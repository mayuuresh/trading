# app.py
import asyncio
import json
import os
import time
from collections import deque
from dataclasses import dataclass
from decimal import Decimal, ROUND_DOWN, getcontext
from typing import Dict, Optional, Tuple, List

from dotenv import load_dotenv
from fastapi import FastAPI, Response
from fastapi.responses import HTMLResponse, JSONResponse
import uvicorn
import websockets

os.system("python3 app.py")
# Optional (LIVE only)
try:
    from binance.client import Client as BinanceClient
    HAVE_BINANCE = True
except Exception:
    HAVE_BINANCE = False

# ========= Precision =========
getcontext().prec = 28  # high-precision decimals for fees/rounding

# ========= CONFIG (taker micro-scalper) =========
PAPER_TRADING = True                  # True = simulate fills; False = send real orders (needs keys)
INR_PER_USD = Decimal("83.5")

# Universe (liquid majors + fast alts)
CANDIDATES = [
    "1000SATSFDUSD",
    "1MBABYDOGEFDUSD",
    "SHIBFDUSD",
    "PEPEFDUSD",
    "DOGEFDUSD",
    "ADAFDUSD"
]

# Fees (taker side, VIP0 typical ~0.1%)
FEE_PCT_PER_SIDE = Decimal("0.0000")  # change if your account differs

# Capital & risk (₹100 ≈ $1.20)
CAPITAL_PER_TRADE_USDT = Decimal("12.0")
TP_PCT = Decimal("0.0025")    # +0.25% take profit
SL_PCT = Decimal("0.0035")    # -0.35% stop loss
MAX_HOLD_SEC = 120            # time stop to avoid stalling

# Entry filters (keep them simple/fast)
SPREAD_MAX_PCT = Decimal("0.0020")        # 0.10% max spread
MOMENTUM_TICKS = 5
MOMENTUM_MIN_SLOPE = Decimal("0.000003")   # min avg mid uptick
VOL_WINDOW = 20
VOL_MIN_ABS = Decimal("0.000015")          # minimum std-dev in mid

# Throttles / protection
ENTRY_COOLDOWN_SEC = 1.0
MAX_TRADES_PER_MIN = 60
MAX_TRADES_PER_DAY = 2000
DAILY_MAX_LOSS_USDT = Decimal("3.0")

# UI & buffers
PRICE_BUFFER = 600
UI_POLL_MS = 500
PRINT_SCORE_EVERY_SEC = 6.0
TOP_N_DEBUG = 5

# ========= ENV / API =========
load_dotenv()
API_KEY = os.getenv("BINANCE_API_KEY", "")
API_SECRET = os.getenv("BINANCE_API_SECRET", "")
binance_client = None
if not PAPER_TRADING and HAVE_BINANCE:
    if not (API_KEY and API_SECRET):
        raise SystemExit("❌ LIVE mode requires BINANCE_API_KEY and BINANCE_API_SECRET.")
    binance_client = BinanceClient(API_KEY, API_SECRET)

# ========= Metadata =========
@dataclass
class SymMeta:
    min_qty: Decimal
    step_qty: Decimal
    tick: Decimal
    min_notional: Decimal

sym_meta: Dict[str, SymMeta] = {}

def round_step(val: Decimal, step: Decimal) -> Decimal:
    if step <= 0:
        return val
    q = (val / step).to_integral_value(rounding=ROUND_DOWN)
    return q * step

def get_symbol_filters(symbol: str) -> SymMeta:
    # Try fetching from Binance; otherwise fall back to sane paper defaults.
    info = None
    if HAVE_BINANCE:
        try:
            tmp = BinanceClient()  # public (no key)
            info = tmp.get_symbol_info(symbol)
        except Exception:
            info = None
    if info is None:
        # Conservative paper defaults (sufficient for rounding)
        if symbol in ("SHIBUSDT", "PEPEUSDT"):
            return SymMeta(Decimal("1"), Decimal("1"), Decimal("0.00000001"), Decimal("0"))
        if symbol.endswith("USDT"):
            return SymMeta(Decimal("0.000001"), Decimal("0.000001"), Decimal("0.000001"), Decimal("0"))
    lot = next(f for f in info["filters"] if f["filterType"] == "LOT_SIZE")
    pricef = next(f for f in info["filters"] if f["filterType"] == "PRICE_FILTER")
    notionalf = next((f for f in info["filters"] if f["filterType"] == "MIN_NOTIONAL"), None)
    return SymMeta(
        min_qty=Decimal(lot["minQty"]),
        step_qty=Decimal(lot["stepSize"]),
        tick=Decimal(pricef["tickSize"]),
        min_notional=Decimal(notionalf["minNotional"]) if notionalf else Decimal("0"),
    )

# ========= State =========
last_ticks: Dict[str, deque] = {s: deque(maxlen=PRICE_BUFFER) for s in CANDIDATES}  # (ts,bid,ask,mid) as Decimal
last_mid: Dict[str, Optional[Decimal]] = {s: None for s in CANDIDATES}

# Position (one position at a time)
in_position: bool = False
pos_symbol: Optional[str] = None
entry_price: Optional[Decimal] = None
position_qty: Decimal = Decimal("0")
entry_time: float = 0.0

# PnL & throttles
daily_pnl: Decimal = Decimal("0")
minute_bucket = int(time.time() // 60)
trades_this_min = 0
trades_today = 0
day_bucket = time.strftime("%Y-%m-%d")
last_entry_ts = 0.0

# Debug/score
last_score_ts = 0.0
last_scores: Dict[str, float] = {}

# Runner + UI log
bot_running = False
event_log: deque = deque(maxlen=400)

def log(msg: str):
    ts = time.strftime("%I:%M:%S %p")
    event_log.append(f"[{ts}] {msg}")
    print(msg)

# ========= Helper math =========
def can_trade_now() -> bool:
    global trades_this_min, minute_bucket, trades_today, day_bucket
    now_bucket = int(time.time() // 60)
    if now_bucket != minute_bucket:
        minute_bucket = now_bucket
        trades_this_min = 0
    today = time.strftime("%Y-%m-%d")
    if today != day_bucket:
        day_bucket = today
        trades_today = 0
    return trades_this_min < MAX_TRADES_PER_MIN and trades_today < MAX_TRADES_PER_DAY

def ensure_notional(symbol: str, qty: Decimal, price: Decimal) -> Decimal:
    meta = sym_meta[symbol]
    if meta.min_notional > 0:
        notional = qty * price
        if notional < meta.min_notional:
            qty = (meta.min_notional / price)
            qty = round_step(qty, meta.step_qty)
    return qty

def spread_pct(symbol: str) -> Optional[Decimal]:
    dq = last_ticks[symbol]
    if not dq:
        return None
    _, bid, ask, mid = dq[-1]
    return (ask - bid) / mid if mid > 0 else None

def momentum_strength(symbol: str) -> Decimal:
    dq = last_ticks[symbol]
    if len(dq) < MOMENTUM_TICKS:
        return Decimal("0")
    mids = [t[3] for t in list(dq)[-MOMENTUM_TICKS:]]
    incs = [mids[i+1] - mids[i] for i in range(len(mids)-1)]
    avg = sum(incs, Decimal("0")) / Decimal(len(incs))
    return max(avg, Decimal("0"))

def volatility_strength(symbol: str) -> Decimal:
    dq = last_ticks[symbol]
    if len(dq) < VOL_WINDOW:
        return Decimal("0")
    mids = [t[3] for t in list(dq)[-VOL_WINDOW:]]
    mean = sum(mids, Decimal("0")) / Decimal(len(mids))
    var = sum((m - mean) * (m - mean) for m in mids) / Decimal(len(mids))
    std = var.sqrt()
    return max(std - VOL_MIN_ABS, Decimal("0"))

def compute_score(symbol: str) -> Tuple[float, Dict[str, float]]:
    spr = spread_pct(symbol)
    if spr is None:
        return -1e9, {"spr": 0.0}
    if spr > SPREAD_MAX_PCT:
        return -1e9, {"spr": float(spr)}
    mom = momentum_strength(symbol)
    vol = volatility_strength(symbol)
    # Normalize by tick to keep scale comparable
    tick = sym_meta.get(symbol, SymMeta(Decimal("0"), Decimal("0"), Decimal("0.000001"), Decimal("0"))).tick
    if tick <= 0:
        tick = Decimal("0.000001")
    mom_n = mom / tick
    vol_n = vol / tick
    spr_n = spr / Decimal("0.0001")  # in 0.01% units
    # weights: aggressive micro scalper
    w_mom = Decimal("1.0")
    w_vol = Decimal("0.5")
    w_spr = Decimal("0.8")
    score_dec = w_mom * mom_n + w_vol * vol_n - w_spr * spr_n
    dbg = {"mom": float(mom_n), "vol": float(vol_n), "spr": float(spr)}
    return float(score_dec), dbg

def pick_best_symbol() -> Optional[str]:
    global last_score_ts
    scores: List[Tuple[str, float, Dict[str, float]]] = []
    for s in CANDIDATES:
        if len(last_ticks[s]) < max(MOMENTUM_TICKS, VOL_WINDOW):
            continue
        sc, dbg = compute_score(s)
        last_scores[s] = sc
        if sc > -1e8:
            scores.append((s, sc, dbg))
    if not scores:
        return None
    scores.sort(key=lambda x: x[1], reverse=True)
    now = time.time()
    if now - last_score_ts >= PRINT_SCORE_EVERY_SEC:
        last_score_ts = now
        snap = ", ".join([f"{s}:{sc:.2f}" for s, sc, _ in scores[:TOP_N_DEBUG]])
        log(f"📊 Top scores → {snap}")
    return scores[0][0]

# ========= Paper execution (TAKER) =========
def paper_buy_taker(symbol: str) -> Tuple[Decimal, Decimal]:
    """Fill at ASK, deduct taker fee in base (reduce qty)."""
    dq = last_ticks[symbol]
    if not dq:
        raise RuntimeError("No market data")
    _, bid, ask, mid = dq[-1]
    px = ask
    meta = sym_meta[symbol]
    qty = CAPITAL_PER_TRADE_USDT / px
    qty = max(qty, meta.min_qty)
    qty = round_step(qty, meta.step_qty)
    qty = ensure_notional(symbol, qty, px)
    # fee reduces base received
    fee_qty = qty * FEE_PCT_PER_SIDE
    filled_qty = qty - fee_qty
    return filled_qty, px

def paper_sell_taker(symbol: str, qty: Decimal) -> Tuple[Decimal, Decimal, Decimal]:
    """Fill at BID, deduct taker fee in quote (reduce proceeds)."""
    dq = last_ticks[symbol]
    if not dq:
        raise RuntimeError("No market data")
    _, bid, ask, mid = dq[-1]
    px = bid
    qty = round_step(qty, sym_meta[symbol].step_qty)
    gross = qty * px
    fee_quote = gross * FEE_PCT_PER_SIDE
    net = gross - fee_quote
    return qty, px, net

# ========= Trade loop =========
async def trade_loop():
    global in_position, pos_symbol, entry_price, position_qty, entry_time
    global daily_pnl, trades_this_min, trades_today, last_entry_ts

    while bot_running:
        try:
            # Kill-switch
            if daily_pnl <= -DAILY_MAX_LOSS_USDT:
                await asyncio.sleep(0.2)
                continue

            # Need market data
            if all(len(last_ticks[s]) < VOL_WINDOW for s in CANDIDATES):
                await asyncio.sleep(0.05)
                continue

            # Flat → look to enter
            if not in_position:
                if not can_trade_now():
                    await asyncio.sleep(0.05)
                    continue
                if time.time() - last_entry_ts < ENTRY_COOLDOWN_SEC:
                    await asyncio.sleep(0.05)
                    continue

                best = pick_best_symbol()
                if not best:
                    await asyncio.sleep(0.02)
                    continue

                # Final sanity filters for the chosen symbol
                mom = momentum_strength(best)
                spr = spread_pct(best)
                vol = volatility_strength(best)
                if spr is None or spr > SPREAD_MAX_PCT:
                    await asyncio.sleep(0.02)
                    continue
                if mom < MOMENTUM_MIN_SLOPE:
                    await asyncio.sleep(0.02)
                    continue
                if vol <= Decimal("0"):
                    await asyncio.sleep(0.02)
                    continue

                try:
                    qty, px = paper_buy_taker(best) if PAPER_TRADING else ...  # live path omitted here
                except Exception as e:
                    log(f"BUY error: {e}")
                    await asyncio.sleep(0.05)
                    continue

                in_position = True
                pos_symbol = best
                entry_price = px
                position_qty = qty
                entry_time = time.time()
                last_entry_ts = entry_time
                trades_this_min += 1
                trades_today += 1
                # INR info
                notional_usdt = qty * px
                notional_inr = (notional_usdt * INR_PER_USD).quantize(Decimal("0.01"))
                entry_price_inr = (px * INR_PER_USD).quantize(Decimal("0.0001"))
                log(f"{best}: ✅ BUY {qty} @ {px} (≈{notional_usdt:.8f} USDT | ₹{notional_inr} | price ₹{entry_price_inr})")
                await asyncio.sleep(0.02)
                continue

            # Manage open position → TP / SL / time stop
            s = pos_symbol
            if not s or entry_price is None or position_qty <= 0:
                await asyncio.sleep(0.02)
                continue

            dq = last_ticks[s]
            if not dq:
                await asyncio.sleep(0.02)
                continue
            _, bid, ask, mid = dq[-1]

            tp_px = entry_price * (Decimal("1") + TP_PCT)
            sl_px = entry_price * (Decimal("1") - SL_PCT)

            # If mid has reached TP (favorable), exit taker at bid
            if mid >= tp_px:
                try:
                    exec_qty, exit_px, proceeds = paper_sell_taker(s, position_qty) if PAPER_TRADING else ...
                except Exception as e:
                    log(f"SELL error: {e}")
                    await asyncio.sleep(0.05)
                    continue
                cost = exec_qty * entry_price
                pnl = proceeds - cost
                daily_pnl += pnl
                log(f"{s}: 🟩 EXIT TP {exec_qty} @ {exit_px} | PnL≈{pnl:.8f} (₹{(pnl*INR_PER_USD):.2f}) | Daily≈{daily_pnl:.4f}")
                in_position = False
                pos_symbol = None
                entry_price = None
                position_qty = Decimal("0")
                entry_time = 0.0
                trades_this_min += 1
                trades_today += 1
                await asyncio.sleep(0.02)
                continue

            # SL (unfavorable), exit at bid
            if mid <= sl_px or (time.time() - entry_time) >= MAX_HOLD_SEC:
                try:
                    exec_qty, exit_px, proceeds = paper_sell_taker(s, position_qty) if PAPER_TRADING else ...
                except Exception as e:
                    log(f"SELL error: {e}")
                    await asyncio.sleep(0.05)
                    continue
                cost = exec_qty * entry_price
                pnl = proceeds - cost
                daily_pnl += pnl
                reason = "SL" if mid <= sl_px else "TIME"
                emoji = "🟥" if reason == "SL" else "🕒"
                log(f"{s}: {emoji} EXIT {reason} {exec_qty} @ {exit_px} | PnL≈{pnl:.8f} (₹{(pnl*INR_PER_USD):.2f}) | Daily≈{daily_pnl:.4f}")
                in_position = False
                pos_symbol = None
                entry_price = None
                position_qty = Decimal("0")
                entry_time = 0.0
                trades_this_min += 1
                trades_today += 1
                await asyncio.sleep(0.02)
                continue

            await asyncio.sleep(0.01)

        except Exception as e:
            log(f"Trade loop error: {e}")
            await asyncio.sleep(0.1)

# ========= WebSocket (merged bookTicker) =========
async def ws_merged_listener():
    streams = [f"{s.lower()}@bookTicker" for s in CANDIDATES]
    url = "wss://stream.binance.com:9443/stream?streams=" + "/".join(streams)
    log("Connecting to Binance WebSocket (merged)…")

    # preload symbol filters (for rounding)
    for s in CANDIDATES:
        try:
            sym_meta[s] = get_symbol_filters(s)
        except Exception as e:
            # fallback already handled in get_symbol_filters
            sym_meta[s] = get_symbol_filters(s)
            log(f"Filters {s} fallback loaded")

    async with websockets.connect(url, ping_interval=15, ping_timeout=20) as ws:
        log("✅ Connected to Binance WebSocket (merged)")
        while bot_running:
            try:
                raw = await ws.recv()
                msg = json.loads(raw)
                data = msg.get("data", {})
                s = data.get("s")
                b = data.get("b")
                a = data.get("a")
                E = data.get("E")
                if not s or b is None or a is None:
                    continue
                try:
                    bid = Decimal(b)
                    ask = Decimal(a)
                    if bid <= 0 or ask <= 0 or ask < bid:
                        continue
                    mid = (bid + ask) / Decimal("2")
                except Exception:
                    continue
                ts = int(E or int(time.time()*1000)) // 1000
                last_ticks[s].append((ts, bid, ask, mid))
                last_mid[s] = mid
            except Exception as e:
                log(f"WS Error: {e}")
                await asyncio.sleep(0.3)
@app.get("/ping")
def ping():
    return {"alive": True}

# ========= Dashboard =========
app = FastAPI()

UI_POLL_MS = 500  # keep your existing value

INDEX_HTML = f"""
<!doctype html>
<html>
<head>
  <meta charset="utf-8"/>
  <title>Micro-Scalper — Dashboard (TAKER)</title>
  <style>
    body {{ font-family: ui-sans-serif, system-ui, -apple-system; background:#0b1220; color:#e6edf6; }}
    .wrap {{ max-width: 1100px; margin: 24px auto; padding: 0 16px; }}
    h1 {{ font-size: 22px; margin: 0 0 12px; }}
    button {{ background:#1f6feb; color:#fff; border:none; padding:10px 16px; border-radius:10px; cursor:pointer; }}
    button.stop {{ background:#8b0000; }}
    .grid {{ display:grid; grid-template-columns: 1fr 1fr; gap:16px; margin-top:16px; }}
    .card {{ background:#111827; border:1px solid #1f2937; border-radius:16px; padding:16px; }}
    .mono {{ font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, "Liberation Mono", monospace; }}
    .small {{ color:#9ca3af; font-size: 12px; }}
    pre {{ white-space: pre-wrap; }}
    .pill {{ font-size:12px; padding:2px 8px; border-radius:999px; background:#0b3d91; }}
    .ok {{ color:#10b981; }} 
    .bad {{ color:#ef4444; }}
  </style>
</head>
<body>
<div class="wrap">
  <h1>Micro-Scalper — Dashboard (TAKER)</h1>
  <div>
    <button onclick="start()">Start</button>
    <button class="stop" onclick="stop()">Stop</button>
  </div>

  <div class="grid">
    <div class="card">
      <h3>Status</h3>
      <div id="status" class="mono"></div>
    </div>
    <div class="card">
      <h3>Live Tickers (last mid)</h3>
      <div id="mids" class="mono small"></div>
    </div>
    <div class="card">
      <h3>Position / PnL</h3>
      <div id="pnl" class="mono"></div>
      <div class="small">
        Paper: <span id="paper"></span> |
        Capital/trade: <span id="cap"></span> |
        Fee/side: <span id="fee"></span> |
        TP: <span id="tp"></span> |
        SL: <span id="sl"></span> |
        Max hold: <span id="hold"></span>s
      </div>
    </div>
    <div class="card">
      <h3>Top Scores</h3>
      <pre id="scores" class="mono small"></pre>
    </div>
    <div class="card" style="grid-column:1/-1;">
      <h3>Event Log</h3>
      <pre id="log" class="mono small"></pre>
    </div>
  </div>
</div>
<script>
async function start(){{ await fetch('/start', {{method:'POST'}}); }}
async function stop(){{ await fetch('/stop', {{method:'POST'}}); }}
async function poll(){{
  const r = await fetch('/status');
  const j = await r.json();
  document.getElementById('status').innerText =
    'Running: ' + j.running + '\\n' +
    'In Position: ' + j.in_position + '\\n' +
    'Symbol: ' + (j.pos_symbol || '-') + '\\n' +
    'Entry: ' + (j.entry_price || '-') + '\\n' +
    'Qty: ' + (j.position_qty || '-');

    let mids = '';
  const lastMid = j.last_mid || {{}};
  const lastMidInr = j.last_mid_inr || {{}};

  for (const k in lastMid) {{
    const usd = lastMid[k];
    if (!usd) continue;
    const inr = lastMidInr[k];
    mids += k + ' : ' + usd + (inr ? '   |   INR: ' + inr : '') + '\\n';
  }}

  document.getElementById('mids').innerText = mids;


  let scores = '';
  const sorted = Object.entries(j.last_scores || {{}}).sort((a,b)=>b[1]-a[1]).slice(0,8);
  for (const [k,v] of sorted) scores += k + '  ' + v.toFixed(2) + '\\n';
  document.getElementById('scores').innerText = scores;

  document.getElementById('pnl').innerText =
    'Daily PnL (USDT): ' + j.daily_pnl + '\\n' +
    'Daily PnL (INR): ' + j.daily_pnl_inr;

  document.getElementById('paper').innerText = j.paper;
  document.getElementById('cap').innerText = '$' + j.capital;
  document.getElementById('fee').innerText = (j.fee_side*100).toFixed(4) + '%';
  document.getElementById('tp').innerText = (j.tp_pct*100).toFixed(2) + '%';
  document.getElementById('sl').innerText = (j.sl_pct*100).toFixed(2) + '%';
  document.getElementById('hold').innerText = j.max_hold_sec;

  document.getElementById('log').innerText = (j.log || []).join('\\n');
}}
setInterval(poll, {UI_POLL_MS});
poll();
</script>
</body>
</html>
"""

@app.get("/", response_class=HTMLResponse)
def index():
    return INDEX_HTML

@app.get("/status")
def status():
    return JSONResponse({
        "running": bot_running,
        "in_position": in_position,
        "pos_symbol": pos_symbol,
        "entry_price": str(entry_price) if entry_price is not None else None,
        "position_qty": str(position_qty) if position_qty else None,
        "daily_pnl": str(daily_pnl),
        "daily_pnl_inr": str((daily_pnl * INR_PER_USD).quantize(Decimal("0.01"))),
        "paper": "ON" if PAPER_TRADING else "OFF",
        "capital": float(CAPITAL_PER_TRADE_USDT),
        "fee_side": float(FEE_PCT_PER_SIDE),
        "tp_pct": float(TP_PCT),
        "sl_pct": float(SL_PCT),
        "max_hold_sec": MAX_HOLD_SEC,

        # ✅ Add INR mid values
        "last_mid": {k: (str(v) if v is not None else None) for k,v in last_mid.items()},
       "last_mid_inr": {
    k: (str((v * INR_PER_USD).quantize(Decimal("0.0001"))) if v is not None else None)
    for k, v in last_mid.items()
},


        "last_scores": last_scores,
        "log": list(event_log),
    })

# Start/Stop orchestration
bot_tasks: List[asyncio.Task] = []

@app.post("/start")
async def start():
    global bot_running, bot_tasks
    if bot_running:
        return Response("already running", 200)
    bot_running = True
    log("UI: Start pressed")
    t1 = asyncio.create_task(ws_merged_listener())
    t2 = asyncio.create_task(trade_loop())
    bot_tasks = [t1, t2]
    return Response("ok", 200)

@app.post("/stop")
async def stop():
    global bot_running, bot_tasks
    if not bot_running:
        return Response("not running", 200)
    bot_running = False
    log("UI: Stop pressed")
    for t in bot_tasks:
        t.cancel()
    bot_tasks.clear()
    return Response("stopped", 200)

def main():
    uvicorn.run(app, host="127.0.0.1", port=8000, log_level="warning")

if __name__ == "__main__":
    import os
    port = int(os.environ.get("PORT", 8000))
    uvicorn.run("app:app", host="0.0.0.0", port=port, reload=True)

