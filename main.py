import requests
import time
import json
import os
import threading
import random
from collections import deque
from datetime import datetime, date
from flask import Flask, render_template_string, jsonify, request as freq

# ========================= CONFIG =========================
TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "")
TELEGRAM_CHAT_ID   = os.environ.get("TELEGRAM_CHAT_ID", "")

_RAW_KEYS = [
    os.environ.get("GROQ_API_KEY",   ""),
    os.environ.get("GROQ_API_KEY_2", ""),
    os.environ.get("GROQ_API_KEY_3", ""),
]
GROQ_KEYS  = [k for k in _RAW_KEYS if k.strip()]
GROQ_MODELS = [
    "llama-3.3-70b-versatile",
    "llama3-70b-8192",
    "mixtral-8x7b-32768",
    "llama-3.1-8b-instant",
    "gemma2-9b-it",
]
GROQ_SLOTS = [(key, model) for key in GROQ_KEYS for model in GROQ_MODELS]

# ---- Balance & Trade ----
INITIAL_BALANCE_USD = 20.0
TARGET_BALANCE_USD  = 50.0
MIN_TRADE_USD       = 5.0
TP_PERCENT          = 6.0    # Take profit at +6%
SL_PERCENT          = 2.5    # Hard stop at -2.5%
CHECK_INTERVAL      = 5      # Check every 5s
MAX_POSITIONS       = 1

# ---- Trading Fees (Solana DEX realistic) ----
DEX_FEE_PCT         = 0.30   # 0.30% per trade (buy + sell = 0.60% round trip)
SLIPPAGE_PCT        = 0.20   # estimated slippage per side

# ---- AI Market Quality Thresholds (no fixed daily cap) ----
MARKET_SCORE_NO_TRADE   = 42   # Below this → AI says skip today, no trades
MARKET_SCORE_CAUTIOUS   = 58   # Below this → only ultra-high confidence entries
MARKET_SCORE_FREE       = 65   # Above this → trade freely, no count limit

# ---- AI/Rules Confidence ----
MIN_AI_CONFIDENCE    = 80    # Raised — only high-conviction entries
MIN_RULES_CONFIDENCE = 68

# ---- Risk Management ----
EARLY_EXIT_PCT    = -0.5   # At -0.5% → ask AI
HARD_FAST_CUT_PCT = -1.2   # At -1.2% → instant exit (covers fee + slippage)

# ---- Trailing Stop ----
TRAIL_TRIGGER_USD   = 0.30  # Activate trail at $0.30 profit
TRAIL_DROP_USD      = 0.18  # Trail drop

# ---- Break-even protection ----
BREAKEVEN_TRIGGER_USD = 0.30

# ---- Filters (strict for real money) ----
MIN_LIQUIDITY        = 15_000
MAX_LIQUIDITY        = 600_000
MIN_5M_VOLUME        = 5_000
MIN_1H_VOLUME        = 15_000
MIN_BUY_RATIO_5M     = 1.4
MIN_BUY_RATIO_1H     = 1.1
MIN_MC               = 30_000
MAX_MC               = 4_000_000
MIN_LP_LOCKED_PCT    = 50
MIN_PRICE_CHANGE_5M  = -2.0
MAX_PRICE_CHANGE_5M  = 60.0
MAX_PRICE_CHANGE_1H  = 100.0
MIN_PRICE_CHANGE_1H  = -15.0
MIN_VOLUME_MCAP_RATIO= 0.005
MIN_BUYS_5M          = 10
MIN_CONFIRMATIONS    = 8     # Stricter: 8/12

NEW_COIN_MAX_AGE_HOURS = 10

PORT = int(os.environ.get("PORT", 5000))
# =========================================================

# ---- Global State ----
balance_usd       = INITIAL_BALANCE_USD
positions         = {}
trade_history     = []
seen_tokens       = set()
traded_coins      = set()
start_time        = datetime.now()
bot_paused        = False
last_update_id    = 0
scan_count        = 0
total_fees_paid   = 0.0    # track all fees paid

# ---- Daily trade tracking ----
daily_trades      = 0
daily_date        = date.today()
daily_fees        = 0.0
_daily_lock       = threading.Lock()

# ---- Continuous market watcher state ----
market_watch      = {
    "last_analysis": "",
    "hot_coins": [],        # coins AI flagged as promising
    "market_score": 50,     # 0-100, AI's current market confidence
    "last_ts": 0,
    "watch_interval": 60,   # seconds between background analyses
}
_watch_lock       = threading.Lock()

# ---- DexScreener Rate Limit State ----
_dex_rate_limited_until = 0.0
_dex_backoff_sec        = 30
_dex_rl_lock            = threading.Lock()

# ---- Market Trend (updated every scan) ----
sol_trend = {
    "price_change_5m": 0.0, "price_change_1h": 0.0,
    "label": "UNKNOWN", "sol_price": 0.0, "ts": 0
}

# ---- Hybrid AI/Rule State ----
ai_mode          = "AI" if GROQ_SLOTS else "RULES"
ai_down_notified = False
_console_lock    = threading.Lock()
_coins_lock      = threading.Lock()

# ---- In-memory logs ----
console_logs  = deque(maxlen=100)
scanned_coins = deque(maxlen=50)


# ==================== DAILY TRADE TRACKER ====================

def _check_daily_reset():
    global daily_trades, daily_date, daily_fees
    with _daily_lock:
        today = date.today()
        if today != daily_date:
            daily_trades = 0
            daily_fees   = 0.0
            daily_date   = today
            log_console(f"Daily reset — new day {today}", "SYSTEM")

def _market_quality() -> str:
    """Return market quality label: BLOCKED / CAUTIOUS / OPEN."""
    label = sol_trend.get("label", "UNKNOWN")
    score = market_watch.get("market_score", 50)
    if "BEARISH" in label or score < MARKET_SCORE_NO_TRADE:
        return "BLOCKED"
    elif score < MARKET_SCORE_CAUTIOUS:
        return "CAUTIOUS"
    else:
        return "OPEN"

def _get_daily_limit() -> str:
    """Informational only — no hard cap, AI decides."""
    q = _market_quality()
    if q == "BLOCKED":  return "0 (market bad)"
    if q == "CAUTIOUS": return "AI-limited (cautious)"
    return "∞ (market open)"

def _can_trade_today() -> bool:
    """AI-driven gate: only block when market quality is BLOCKED."""
    _check_daily_reset()
    q = _market_quality()
    if q == "BLOCKED":
        score = market_watch.get("market_score", 50)
        label = sol_trend.get("label", "?")
        log_console(
            f"🚫 AI says NO trades today — market too weak | Score:{score}% | {label}",
            "WARN"
        )
        return False
    return True

def _record_trade_fees(trade_usd: float) -> float:
    """Calculate and record fees for a trade. Returns total fee amount."""
    global total_fees_paid, daily_fees
    fee = trade_usd * (DEX_FEE_PCT + SLIPPAGE_PCT) / 100.0
    total_fees_paid += fee
    with _daily_lock:
        daily_fees += fee
    return fee


# ==================== DEX HTTP HELPER ====================

_DEX_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/124.0 Safari/537.36",
    "Accept": "application/json",
}

def _dex_get(url: str, timeout: int = 12) -> requests.Response | None:
    global _dex_rate_limited_until, _dex_backoff_sec
    with _dex_rl_lock:
        wait_left = _dex_rate_limited_until - time.time()
        if wait_left > 0:
            return None
    try:
        resp = requests.get(url, headers=_DEX_HEADERS, timeout=timeout)
        if resp.status_code == 429:
            with _dex_rl_lock:
                _dex_rate_limited_until = time.time() + _dex_backoff_sec
                _dex_backoff_sec = min(_dex_backoff_sec * 2, 120)
            return None
        with _dex_rl_lock:
            _dex_backoff_sec = 30
        return resp
    except Exception as e:
        return None


# ==================== LOGGER ====================

def log_console(message: str, level: str = "INFO"):
    ts = datetime.now().strftime("%H:%M:%S")
    entry = {"ts": ts, "level": level, "msg": message}
    with _console_lock:
        console_logs.append(entry)
    print(f"[{ts}][{level}] {message}")


def log_coin(symbol, address, status, price, mc, br5m, vol5m, confirmations, fail_reason=""):
    entry = {
        "symbol":        symbol,
        "address":       address,
        "status":        status,
        "fail_reason":   fail_reason,
        "price":         price,
        "mc":            mc,
        "br5m":          round(br5m, 2),
        "vol5m":         vol5m,
        "confirmations": confirmations,
        "ts":            datetime.now().strftime("%H:%M:%S"),
        "dex_url":       f"https://dexscreener.com/solana/{address}",
    }
    with _coins_lock:
        scanned_coins.appendleft(entry)


# ==================== FLASK APP ====================

app = Flask(__name__)

DASHBOARD_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>AI Trading Bot — Smart Mode</title>
<style>
* { box-sizing: border-box; margin: 0; padding: 0; }
body {
  background: #0d0f14; color: #e2e8f0;
  font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
  min-height: 100vh; padding: 12px;
}
.header {
  text-align: center; padding: 14px 12px 12px;
  background: linear-gradient(135deg, #1a1d2e, #12151f);
  border-radius: 16px; margin-bottom: 12px; border: 1px solid #2d3748;
}
.header h1 {
  font-size: 1.3rem; font-weight: 700;
  background: linear-gradient(90deg, #00d4ff, #7b2ff7);
  -webkit-background-clip: text; -webkit-text-fill-color: transparent;
  margin-bottom: 8px;
}
.header-btns {
  display: flex; justify-content: center; align-items: center;
  gap: 8px; flex-wrap: wrap;
}
.hdr-btn {
  display: inline-flex; align-items: center; gap: 5px;
  padding: 5px 12px; border-radius: 9px; border: none;
  font-size: 0.73rem; font-weight: 700; cursor: pointer;
  transition: opacity .15s, transform .1s; letter-spacing: .4px;
  text-transform: uppercase;
}
.hdr-btn:hover  { opacity: .8; transform: scale(1.03); }
.hdr-btn:active { transform: scale(.97); }
.btn-running { background: rgba(72,187,120,.18); color: #48bb78; border: 1px solid rgba(72,187,120,.45); }
.btn-paused  { background: rgba(246,173,85,.18);  color: #f6ad55; border: 1px solid rgba(246,173,85,.45); }
.btn-scan    { background: rgba(99,179,237,.15);  color: #63b3ed; border: 1px solid rgba(99,179,237,.4); }
.dot { display: inline-block; width:8px; height:8px; border-radius:50%; animation: pulse 1.5s infinite; }
.dot.green  { background:#48bb78; }
.dot.orange { background:#f6ad55; }
.dot.blue   { background:#63b3ed; animation-delay:.3s; }
.dot.purple { background:#b794f4; animation-delay:.6s; }
@keyframes pulse { 0%,100%{opacity:1}50%{opacity:.25} }
.grid { display:grid; grid-template-columns:1fr 1fr; gap:10px; margin-bottom:12px; }
.grid-3 { display:grid; grid-template-columns:1fr 1fr 1fr; gap:10px; margin-bottom:12px; }
.card { background:#1a1d2e; border:1px solid #2d3748; border-radius:14px; padding:14px 12px; }
.card.full { grid-column:1/-1; }
.card-label { font-size:.67rem; text-transform:uppercase; letter-spacing:1px; color:#718096; margin-bottom:4px; }
.card-value { font-size:1.4rem; font-weight:700; color:#fff; }
.card-value.green  { color:#48bb78; }
.card-value.red    { color:#fc8181; }
.card-value.blue   { color:#63b3ed; }
.card-value.orange { color:#f6ad55; }
.card-sub { font-size:.65rem; color:#4a5568; margin-top:3px; }
.progress-bar { background:#2d3748; border-radius:999px; height:8px; margin-top:8px; overflow:hidden; }
.progress-fill { height:100%; background:linear-gradient(90deg,#00d4ff,#7b2ff7); border-radius:999px; transition:width .5s; }
.section-title { font-size:.8rem; font-weight:600; color:#a0aec0; text-transform:uppercase; letter-spacing:1px; margin:14px 0 7px; }
.position-card { background:#1a1d2e; border:1px solid #2d3748; border-radius:14px; padding:14px; margin-bottom:10px; }
.position-header { display:flex; justify-content:space-between; align-items:flex-start; margin-bottom:10px; }
.coin-name { font-size:1.05rem; font-weight:700; color:#fff; }
.contract  { font-size:.6rem; color:#4a5568; word-break:break-all; margin-top:2px; }
.pnl-badge { font-size:.95rem; font-weight:700; padding:4px 10px; border-radius:8px; white-space:nowrap; }
.pnl-badge.pos { background:rgba(72,187,120,.15); color:#48bb78; }
.pnl-badge.neg { background:rgba(252,129,129,.15); color:#fc8181; }
.pos-grid { display:grid; grid-template-columns:1fr 1fr; gap:6px; font-size:.76rem; }
.pos-item { display:flex; flex-direction:column; gap:2px; }
.pos-item .lbl { color:#718096; font-size:.66rem; text-transform:uppercase; }
.pos-item .val { color:#e2e8f0; font-weight:600; }
.tp-sl-bar { display:flex; gap:6px; margin-top:10px; flex-wrap:wrap; }
.tp-box,.sl-box,.trail-box,.fee-box {
  flex:1; padding:5px 8px; border-radius:8px; font-size:.7rem; font-weight:600; text-align:center; min-width:80px;
}
.tp-box    { background:rgba(72,187,120,.12); color:#48bb78; border:1px solid rgba(72,187,120,.3); }
.sl-box    { background:rgba(252,129,129,.12); color:#fc8181; border:1px solid rgba(252,129,129,.3); }
.trail-box { background:rgba(246,173,85,.12);  color:#f6ad55; border:1px solid rgba(246,173,85,.3); }
.fee-box   { background:rgba(99,179,237,.10);  color:#63b3ed; border:1px solid rgba(99,179,237,.25); }
.conf-bar  { margin-top:10px; }
.conf-label { display:flex; justify-content:space-between; font-size:.68rem; color:#718096; margin-bottom:4px; }
.conf-fill { height:6px; border-radius:999px; background:linear-gradient(90deg,#f6ad55,#48bb78); }
.ai-reason { margin-top:8px; font-size:.7rem; color:#a0aec0; background:#12151f; padding:6px 10px; border-radius:8px; border-left:3px solid #7b2ff7; line-height:1.4; }
.peak-info { margin-top:7px; font-size:.7rem; color:#f6ad55; background:rgba(246,173,85,.07); padding:5px 10px; border-radius:8px; border-left:3px solid #f6ad55; }
.trade-row { display:flex; justify-content:space-between; align-items:center; padding:9px 0; border-bottom:1px solid #1e2433; font-size:.78rem; }
.trade-row:last-child { border-bottom:none; }
.trade-symbol { font-weight:700; color:#e2e8f0; }
.trade-detail { color:#718096; font-size:.68rem; margin-top:2px; }
.badge-tp       { background:rgba(72,187,120,.15); color:#48bb78; padding:2px 7px; border-radius:5px; font-size:.68rem; font-weight:700; }
.badge-sl       { background:rgba(252,129,129,.15); color:#fc8181; padding:2px 7px; border-radius:5px; font-size:.68rem; font-weight:700; }
.badge-aiexit   { background:rgba(159,122,234,.15); color:#b794f4; padding:2px 7px; border-radius:5px; font-size:.68rem; font-weight:700; }
.badge-trail    { background:rgba(246,173,85,.15);  color:#f6ad55; padding:2px 7px; border-radius:5px; font-size:.68rem; font-weight:700; }
.badge-recovery { background:rgba(99,179,237,.15);  color:#63b3ed; padding:2px 7px; border-radius:5px; font-size:.68rem; font-weight:700; }
.badge-fastcut  { background:rgba(252,129,129,.25); color:#fc8181; padding:2px 7px; border-radius:5px; font-size:.68rem; font-weight:700; }
.trade-pnl { font-weight:700; }
.trade-pnl.pos { color:#48bb78; }
.trade-pnl.neg { color:#fc8181; }
.no-data { text-align:center; color:#4a5568; padding:22px; font-size:.83rem; }
.btn-stop {
  background: rgba(252,129,129,.2); color: #fc8181;
  border: 1.5px solid rgba(252,129,129,.5);
  animation: stopPulse 2s infinite;
}
.btn-stop:hover { background: rgba(252,129,129,.4) !important; }
.btn-resume { background: rgba(72,187,120,.2); color: #48bb78; border: 1.5px solid rgba(72,187,120,.5); }
@keyframes stopPulse { 0%,100%{box-shadow:0 0 0 0 rgba(252,129,129,.3)} 50%{box-shadow:0 0 8px 3px rgba(252,129,129,.15)} }
.force-close-btn {
  width: 100%; margin-top: 10px; padding: 9px;
  background: rgba(252,129,129,.12); color: #fc8181;
  border: 1px solid rgba(252,129,129,.35); border-radius: 10px;
  font-size: .75rem; font-weight: 700; cursor: pointer;
  transition: background .15s, transform .1s;
}
.force-close-btn:hover  { background: rgba(252,129,129,.28); }
.force-close-btn:active { transform: scale(.97); }
.force-close-btn:disabled { opacity:.4; cursor:not-allowed; }
.modal-overlay {
  display: none; position: fixed; inset: 0;
  background: rgba(0,0,0,.75); z-index: 999;
  align-items: flex-end; justify-content: center;
  backdrop-filter: blur(3px);
}
.modal-overlay.open { display: flex; }
.modal-box {
  background: #13161f; border: 1px solid #2d3748;
  border-radius: 20px 20px 0 0; width: 100%; max-width: 680px;
  max-height: 82vh; display: flex; flex-direction: column;
  animation: slideUp .22s ease;
}
@keyframes slideUp { from{transform:translateY(100%)} to{transform:translateY(0)} }
.modal-header {
  display: flex; justify-content: space-between; align-items: center;
  padding: 14px 16px; border-bottom: 1px solid #2d3748; flex-shrink: 0;
}
.modal-title { font-size: .88rem; font-weight: 700; color: #e2e8f0; }
.modal-close {
  background: #2d3748; border: none; color: #a0aec0; padding: 5px 12px;
  border-radius: 8px; cursor: pointer; font-size: .78rem; font-weight: 600;
  transition: background .15s;
}
.modal-close:hover { background: #fc8181; color: #fff; }
.console-body {
  flex: 1; overflow-y: auto; padding: 10px 12px;
  font-family: 'Courier New', monospace; font-size: .72rem; line-height: 1.65;
}
.console-body::-webkit-scrollbar { width: 4px; }
.console-body::-webkit-scrollbar-thumb { background: #2d3748; border-radius: 4px; }
.log-line { display: flex; gap: 8px; margin-bottom: 1px; }
.log-ts   { color: #4a5568; flex-shrink: 0; }
.log-msg  { flex: 1; word-break: break-word; }
.lvl-INFO   { color: #a0aec0; }
.lvl-TRADE  { color: #48bb78; font-weight: 700; }
.lvl-WARN   { color: #f6ad55; }
.lvl-ERROR  { color: #fc8181; }
.lvl-AI     { color: #b794f4; }
.lvl-RULES  { color: #63b3ed; }
.lvl-SYSTEM { color: #76e4f7; }
.lvl-FEE    { color: #f6ad55; font-style: italic; }
.coins-body { flex: 1; overflow-y: auto; padding: 8px 12px; }
.coins-body::-webkit-scrollbar { width: 4px; }
.coins-body::-webkit-scrollbar-thumb { background: #2d3748; border-radius: 4px; }
.coin-row {
  display: flex; align-items: center; justify-content: space-between;
  padding: 9px 10px; border-radius: 10px; margin-bottom: 6px;
  border: 1px solid #1e2433; gap: 8px;
}
.coin-row.pass { border-color: rgba(72,187,120,.3); background: rgba(72,187,120,.05); }
.coin-row.fail { border-color: rgba(252,129,129,.15); background: rgba(252,129,129,.03); }
.coin-row.buy  { border-color: rgba(159,122,234,.4); background: rgba(159,122,234,.08); }
.coin-sym  { font-weight: 700; font-size: .82rem; color: #fff; min-width: 64px; }
.coin-badge { font-size: .62rem; font-weight: 700; padding: 2px 6px; border-radius: 5px; white-space: nowrap; }
.badge-pass { background:rgba(72,187,120,.15); color:#48bb78; }
.badge-fail { background:rgba(252,129,129,.15); color:#fc8181; }
.badge-buy  { background:rgba(159,122,234,.2);  color:#b794f4; }
.coin-stats { font-size: .67rem; color: #718096; display: flex; flex-wrap: wrap; gap: 5px; flex: 1; }
.coin-stats span { background: #1e2433; padding: 2px 5px; border-radius: 4px; white-space: nowrap; }
.coin-links { display: flex; gap: 6px; flex-shrink: 0; }
.coin-link {
  font-size: .65rem; font-weight: 700; padding: 3px 8px;
  border-radius: 6px; text-decoration: none; white-space: nowrap;
  background: rgba(99,179,237,.15); color: #63b3ed;
  border: 1px solid rgba(99,179,237,.3); transition: opacity .15s;
}
.coin-link:hover { opacity: .75; }
.coin-fail-reason { font-size: .63rem; color: #fc8181; margin-top: 2px; }
.coin-ts { font-size: .6rem; color: #4a5568; white-space: nowrap; }
.refresh-note { text-align:center; color:#4a5568; font-size:.66rem; margin-top:10px; padding-bottom:6px; }
.btn-chat { background:rgba(159,122,234,.18); color:#b794f4; border:1px solid rgba(159,122,234,.4); }
.btn-chat.offline { background:rgba(246,173,85,.12); color:#f6ad55; border:1px solid rgba(246,173,85,.35); }
.btn-watch { background:rgba(0,212,255,.12); color:#00d4ff; border:1px solid rgba(0,212,255,.35); }
.chat-body { flex:1; overflow-y:auto; padding:10px 12px; display:flex; flex-direction:column; gap:10px; }
.chat-body::-webkit-scrollbar { width:4px; }
.chat-body::-webkit-scrollbar-thumb { background:#2d3748; border-radius:4px; }
.chat-msg { max-width:88%; padding:10px 13px; border-radius:14px; font-size:.79rem; line-height:1.55; word-break:break-word; }
.chat-msg.user { align-self:flex-end; background:rgba(99,179,237,.18); color:#e2e8f0; border:1px solid rgba(99,179,237,.3); border-bottom-right-radius:3px; }
.chat-msg.bot  { align-self:flex-start; background:rgba(159,122,234,.14); color:#e2e8f0; border:1px solid rgba(159,122,234,.28); border-bottom-left-radius:3px; }
.chat-typing   { font-size:.72rem; color:#718096; font-style:italic; padding:2px 4px; }
.chat-input-row { display:flex; gap:8px; padding:10px 12px; border-top:1px solid #2d3748; flex-shrink:0; }
.chat-input { flex:1; background:#12151f; border:1px solid #2d3748; border-radius:10px; color:#e2e8f0; padding:9px 12px; font-size:.8rem; outline:none; }
.chat-input:focus { border-color:#7b2ff7; box-shadow:0 0 0 2px rgba(123,47,247,.2); }
.chat-send { background:linear-gradient(135deg,#7b2ff7,#00d4ff); color:#fff; border:none; border-radius:10px; padding:9px 16px; font-size:.8rem; font-weight:700; cursor:pointer; transition:opacity .15s; white-space:nowrap; }
.chat-send:hover { opacity:.85; }
.chat-send:disabled { opacity:.4; cursor:not-allowed; }
.chat-disclaimer { font-size:.63rem; color:#4a5568; text-align:center; padding:4px 12px 6px; flex-shrink:0; }
.market-watch-box {
  background: linear-gradient(135deg,rgba(0,212,255,.07),rgba(123,47,247,.07));
  border: 1px solid rgba(0,212,255,.2); border-radius:14px;
  padding: 10px 14px; margin-bottom:12px; font-size:.75rem; color:#a0aec0;
}
.market-watch-box .mw-title { font-size:.7rem; font-weight:700; color:#00d4ff; text-transform:uppercase; letter-spacing:1px; margin-bottom:5px; }
.market-watch-box .mw-text  { line-height:1.5; color:#cbd5e0; }
.score-bar { display:flex; align-items:center; gap:8px; margin-top:6px; }
.score-track { flex:1; height:5px; background:#1a1d2e; border-radius:999px; overflow:hidden; }
.score-fill  { height:100%; border-radius:999px; transition:width .5s; }
.fee-notice { font-size:.65rem; color:#4a5568; margin-top:4px; }
</style>
</head>
<body>

<div class="header">
  <h1>🤖 AI Trading Bot — Smart Mode</h1>
  <div class="header-btns">
    <button class="hdr-btn btn-running" id="run-btn" onclick="openModal('console-modal')">
      <span class="dot green" id="run-dot"></span>
      <span id="run-label">RUNNING</span>
    </button>
    <button class="hdr-btn btn-scan" onclick="openModal('coins-modal')">
      <span class="dot blue"></span>
      Scan&nbsp;#<span id="scan-num">0</span>
    </button>
    <span style="color:#4a5568;font-size:.7rem;" id="runtime-txt">0h 0m</span>
    <button class="hdr-btn btn-watch" onclick="openModal('watch-modal')">
      <span class="dot purple"></span>
      <span id="watch-score-txt">Market 50%</span>
    </button>
    <button class="hdr-btn btn-chat" id="ai-chat-btn" onclick="openModal('chat-modal')">
      <span class="dot" id="ai-dot" style="background:#b794f4;animation:pulse 1.5s infinite"></span>
      <span id="ai-badge-txt">🤖 AI Chat</span>
    </button>
    <button class="hdr-btn btn-stop" id="pause-btn" onclick="togglePause()">
      🛑 <span id="pause-label">STOP</span>
    </button>
  </div>
  <div style="margin-top:8px;font-size:.72rem;color:#a0aec0;">
    SOL Market: <span id="mkt-label" style="font-weight:700;">scanning...</span>
    &nbsp;|&nbsp; SOL: <span id="mkt-price">$--</span>
    &nbsp;|&nbsp; 5m: <span id="mkt-5m">--</span>
    &nbsp;|&nbsp; 1h: <span id="mkt-1h">--</span>
    &nbsp;|&nbsp; Today: <span id="daily-trades-txt" style="color:#f6ad55;font-weight:700;">0/?</span> trades
  </div>
</div>

<div class="grid">
  <div class="card">
    <div class="card-label">Balance</div>
    <div class="card-value green" id="balance">$--</div>
    <div class="card-sub" id="fees-sub">Fees paid: $0.00</div>
  </div>
  <div class="card">
    <div class="card-label">Total PnL</div>
    <div class="card-value" id="total-pnl">$--</div>
    <div class="card-sub" id="net-pnl-sub">Net after fees: $--</div>
  </div>
  <div class="card">
    <div class="card-label">Win Rate</div>
    <div class="card-value blue" id="win-rate">--%</div>
  </div>
  <div class="card">
    <div class="card-label">Trades (W/L)</div>
    <div class="card-value" id="trades-wl">--</div>
    <div class="card-sub" id="daily-limit-sub">Daily limit: ?</div>
  </div>
  <div class="card full">
    <div class="card-label">Progress to Target ($<span id="target-val">50</span>)</div>
    <div style="display:flex;justify-content:space-between;margin-top:4px;font-size:.73rem;color:#a0aec0;">
      <span>$20 start</span>
      <span id="progress-pct" style="font-weight:700;color:#fff;">0%</span>
    </div>
    <div class="progress-bar"><div class="progress-fill" id="progress-bar" style="width:0%"></div></div>
  </div>
</div>

<div class="section-title">📌 Open Position</div>
<div id="open-positions"><div class="no-data">No open positions</div></div>

<div class="section-title">📜 Trade History</div>
<div class="card full">
  <div id="trade-history"><div class="no-data">No trades yet</div></div>
</div>

<div class="refresh-note" id="last-updated">Auto-refreshing every 10s</div>


<!-- MODAL 1 — CONSOLE -->
<div class="modal-overlay" id="console-modal" onclick="closeModalBg(event,'console-modal')">
  <div class="modal-box">
    <div class="modal-header">
      <span class="modal-title">🖥️ Live Console</span>
      <button class="modal-close" onclick="closeModal('console-modal')">✕ Close</button>
    </div>
    <div class="console-body" id="modal-console-body">
      <div class="log-line"><span class="log-ts">--:--:--</span><span class="log-msg lvl-SYSTEM">Loading...</span></div>
    </div>
  </div>
</div>

<!-- MODAL 2 — LIVE COINS -->
<div class="modal-overlay" id="coins-modal" onclick="closeModalBg(event,'coins-modal')">
  <div class="modal-box">
    <div class="modal-header">
      <span class="modal-title">🔍 Live Scanned Coins</span>
      <button class="modal-close" onclick="closeModal('coins-modal')">✕ Close</button>
    </div>
    <div class="coins-body" id="coins-body">
      <div class="no-data">No coins scanned yet...</div>
    </div>
  </div>
</div>

<!-- MODAL 3 — AI CHAT -->
<div class="modal-overlay" id="chat-modal" onclick="closeModalBg(event,'chat-modal')">
  <div class="modal-box" style="max-height:88vh;">
    <div class="modal-header">
      <span class="modal-title">🤖 AI Market Assistant</span>
      <button class="modal-close" onclick="closeModal('chat-modal')">✕ Close</button>
    </div>
    <div class="chat-body" id="chat-body">
      <div class="chat-msg bot">👋 Assalam o Alaikum! Main AI trading assistant hoon.<br><br>Mujhse pucho:<br>• <b>Market kaisi hai?</b><br>• <b>Kya trade karna chahiye?</b><br>• <b>Meri position kaisi chal rahi hai?</b><br>• <b>Aj ki fees kitni hui?</b><br>• <b>SOL ka trend kya hai?</b></div>
    </div>
    <div class="chat-disclaimer" id="chat-ai-status">⏳ AI status check ho raha hai...</div>
    <div class="chat-input-row">
      <input class="chat-input" id="chat-input" placeholder="Market ke baare mein kuch bhi pucho..." onkeydown="if(event.key==='Enter' && !event.shiftKey){event.preventDefault();sendChat();}">
      <button class="chat-send" id="chat-send-btn" onclick="sendChat()">Send ➤</button>
    </div>
  </div>
</div>

<!-- MODAL 4 — MARKET WATCH -->
<div class="modal-overlay" id="watch-modal" onclick="closeModalBg(event,'watch-modal')">
  <div class="modal-box" style="max-height:75vh;">
    <div class="modal-header">
      <span class="modal-title">📡 AI Market Watch — Live Analysis</span>
      <button class="modal-close" onclick="closeModal('watch-modal')">✕ Close</button>
    </div>
    <div class="chat-body" id="watch-body" style="padding:14px 16px;">
      <div style="color:#4a5568;font-size:.8rem;">AI market analysis load ho rahi hai...</div>
    </div>
  </div>
</div>

<script>
let logTotal    = 0;
let consoleOpen = false;
let coinsOpen   = false;
let chatOpen    = false;
let watchOpen   = false;

function openModal(id) {
  document.getElementById(id).classList.add('open');
  if (id === 'console-modal') { consoleOpen = true; fetchLogs(true); }
  if (id === 'coins-modal')   { coinsOpen   = true; fetchCoins(); }
  if (id === 'chat-modal')    { chatOpen    = true; document.getElementById('chat-input').focus(); }
  if (id === 'watch-modal')   { watchOpen   = true; fetchWatch(); }
}
function closeModal(id) {
  document.getElementById(id).classList.remove('open');
  if (id === 'console-modal') consoleOpen = false;
  if (id === 'coins-modal')   coinsOpen   = false;
  if (id === 'chat-modal')    chatOpen    = false;
  if (id === 'watch-modal')   watchOpen   = false;
}
function closeModalBg(e, id) {
  if (e.target === document.getElementById(id)) closeModal(id);
}

async function togglePause() {
  const btn = document.getElementById('pause-btn');
  btn.disabled = true;
  try {
    const r = await fetch('/api/toggle_pause', { method: 'POST' });
    const d = await r.json();
    updatePauseBtn(d.paused);
  } catch(e) { console.error(e); }
  btn.disabled = false;
}
function updatePauseBtn(paused) {
  const btn = document.getElementById('pause-btn');
  if (paused) {
    btn.className = 'hdr-btn btn-resume';
    btn.innerHTML = '▶️ <span id="pause-label">RESUME</span>';
  } else {
    btn.className = 'hdr-btn btn-stop';
    btn.innerHTML = '🛑 <span id="pause-label">STOP</span>';
  }
}

async function forceClose(addr, btn) {
  if (!confirm('Force close this position NOW at current price?')) return;
  btn.disabled = true; btn.textContent = 'Closing...';
  try {
    const r = await fetch('/api/force_close', {
      method: 'POST', headers: {'Content-Type':'application/json'},
      body: JSON.stringify({ address: addr })
    });
    const d = await r.json();
    if (d.ok) { btn.textContent = '✅ Closed!'; fetchData(); }
    else       { btn.textContent = '❌ Failed'; btn.disabled = false; }
  } catch(e) { btn.textContent = '❌ Error'; btn.disabled = false; }
}

async function fetchData() {
  try {
    const r = await fetch('/api/status');
    const d = await r.json();

    document.getElementById('scan-num').textContent    = d.scan_count;
    document.getElementById('runtime-txt').textContent = d.runtime;

    const runBtn = document.getElementById('run-btn');
    const runDot = document.getElementById('run-dot');
    const runLbl = document.getElementById('run-label');
    if (d.paused) {
      runBtn.className = 'hdr-btn btn-paused';
      runDot.className = 'dot orange';
      runLbl.textContent = 'PAUSED';
    } else {
      runBtn.className = 'hdr-btn btn-running';
      runDot.className = 'dot green';
      runLbl.textContent = 'RUNNING';
    }

    const chatBtn  = document.getElementById('ai-chat-btn');
    const aiDot    = document.getElementById('ai-dot');
    const aiTxt    = document.getElementById('ai-badge-txt');
    const aiStatus = document.getElementById('chat-ai-status');
    if (d.ai_mode === 'AI') {
      chatBtn.className = 'hdr-btn btn-chat';
      aiDot.style.background = '#b794f4';
      aiTxt.textContent = '🤖 AI Chat';
      if (aiStatus) aiStatus.textContent = '✅ AI Online — Groq keys kaam kar rahe hain';
    } else {
      chatBtn.className = 'hdr-btn btn-chat offline';
      aiDot.style.background = '#f6ad55';
      aiTxt.textContent = '📐 Rules Chat';
      if (aiStatus) aiStatus.textContent = '⚠️ AI offline — Rule-Based mode';
    }

    // Market info
    const mkt = d.sol_trend || {};
    document.getElementById('mkt-label').textContent = mkt.label || '--';
    document.getElementById('mkt-price').textContent = mkt.sol_price ? '$'+mkt.sol_price : '$--';
    const p5 = mkt.price_change_5m;
    const p1 = mkt.price_change_1h;
    const el5 = document.getElementById('mkt-5m');
    const el1 = document.getElementById('mkt-1h');
    el5.textContent = p5 !== undefined ? (p5>=0?'+':'')+p5.toFixed(2)+'%' : '--';
    el5.style.color  = p5 > 0 ? '#48bb78' : (p5 < 0 ? '#fc8181' : '#a0aec0');
    el1.textContent = p1 !== undefined ? (p1>=0?'+':'')+p1.toFixed(2)+'%' : '--';
    el1.style.color  = p1 > 0 ? '#48bb78' : (p1 < 0 ? '#fc8181' : '#a0aec0');

    // Daily trades
    const dtEl = document.getElementById('daily-trades-txt');
    if (dtEl) dtEl.textContent = (d.daily_trades||0)+' trades | Market: '+(d.daily_limit||'AI deciding');

    // Market watch score
    const wsEl = document.getElementById('watch-score-txt');
    if (wsEl) wsEl.textContent = 'Market '+(d.market_score||50)+'%';

    // Balance + fees
    document.getElementById('balance').textContent = '$'+d.balance.toFixed(4);
    const feesEl = document.getElementById('fees-sub');
    if (feesEl) feesEl.textContent = 'Fees paid: $'+(d.total_fees||0).toFixed(4);

    // PnL
    const pnl = d.total_pnl;
    const pnlEl = document.getElementById('total-pnl');
    pnlEl.textContent = (pnl >= 0 ? '+' : '') + '$' + Math.abs(pnl).toFixed(4);
    pnlEl.className   = 'card-value ' + (pnl >= 0 ? 'green' : 'red');
    const netEl = document.getElementById('net-pnl-sub');
    if (netEl) {
      const net = pnl - (d.total_fees||0);
      netEl.textContent = 'Net after fees: '+(net>=0?'+':'')+'$'+net.toFixed(4);
      netEl.style.color = net >= 0 ? '#48bb78' : '#fc8181';
    }

    // Win rate
    document.getElementById('win-rate').textContent = d.win_rate.toFixed(1) + '%';
    const wlEl = document.getElementById('trades-wl');
    wlEl.textContent = d.wins + 'W / ' + d.losses + 'L';
    wlEl.className   = 'card-value ' + (d.wins >= d.losses ? 'green' : 'red');
    const dlEl = document.getElementById('daily-limit-sub');
    if (dlEl) dlEl.textContent = 'AI market gate: '+(d.daily_limit||'AI deciding');

    // Progress
    const prog = d.target > 0 ? Math.max(0, Math.min(100, (d.balance - 20) / (d.target - 20) * 100)) : 0;
    document.getElementById('progress-bar').style.width = prog.toFixed(1) + '%';
    document.getElementById('progress-pct').textContent = prog.toFixed(1) + '%';
    document.getElementById('target-val').textContent = d.target;

    // Pause btn sync
    updatePauseBtn(d.paused);

    // Positions
    const posEl = document.getElementById('open-positions');
    if (!d.positions || d.positions.length === 0) {
      posEl.innerHTML = '<div class="no-data">No open positions</div>';
    } else {
      posEl.innerHTML = d.positions.map(pos => {
        const pnlClass = pos.pnl_usd >= 0 ? 'pos' : 'neg';
        const pnlSign  = pos.pnl_usd >= 0 ? '+' : '';
        const confPct  = Math.min(100, pos.ai_confidence || 0);
        const feeEst   = (pos.amount_usd * 0.60 / 100).toFixed(4);
        return `<div class="position-card">
          <div class="position-header">
            <div>
              <div class="coin-name">${esc(pos.symbol)} <span style="font-size:.7rem;color:#718096;">[${esc(pos.entry_mode)}]</span></div>
              <div class="contract">${esc(pos.address)}</div>
            </div>
            <div class="pnl-badge ${pnlClass}">${pnlSign}$${Math.abs(pos.pnl_usd).toFixed(4)} (${pnlSign}${pos.pnl_pct.toFixed(2)}%)</div>
          </div>
          <div class="pos-grid">
            <div class="pos-item"><span class="lbl">Entry</span><span class="val">$${pos.entry_price.toFixed(10)}</span></div>
            <div class="pos-item"><span class="lbl">Current</span><span class="val">$${pos.current_price.toFixed(10)}</span></div>
            <div class="pos-item"><span class="lbl">Amount</span><span class="val">$${pos.amount_usd.toFixed(2)}</span></div>
            <div class="pos-item"><span class="lbl">Peak Profit</span><span class="val" style="color:#f6ad55;">+$${pos.peak_pnl_usd.toFixed(4)}</span></div>
          </div>
          <div class="tp-sl-bar">
            <div class="tp-box">TP: +${d.tp_pct}%</div>
            <div class="sl-box">SL: -${d.sl_pct}%</div>
            <div class="trail-box">Trail: -$${d.trail_drop}</div>
            <div class="fee-box">Fee est: $${feeEst}</div>
          </div>
          ${confPct > 0 ? `<div class="conf-bar">
            <div class="conf-label"><span>AI Confidence</span><span>${confPct}%</span></div>
            <div style="background:#1e2433;border-radius:999px;height:6px;overflow:hidden;">
              <div class="conf-fill" style="width:${confPct}%"></div>
            </div>
          </div>` : ''}
          ${pos.ai_reason ? `<div class="ai-reason">💡 ${esc(pos.ai_reason)}</div>` : ''}
          ${pos.peak_pnl_usd > 0.1 ? `<div class="peak-info">🏔 Peak: +$${pos.peak_pnl_usd.toFixed(4)}</div>` : ''}
          <button class="force-close-btn" onclick="forceClose('${esc(pos.address)}', this)">⚡ Force Close Now</button>
        </div>`;
      }).join('');
    }

    // Trade history
    const histEl = document.getElementById('trade-history');
    if (!d.history || d.history.length === 0) {
      histEl.innerHTML = '<div class="no-data">No trades yet</div>';
    } else {
      const icons = {TP:'✅',SL:'❌','AI-EXIT':'🤖',TRAIL:'📉',FASTCUT:'✂️',RECOVERY:'🔄'};
      histEl.innerHTML = [...d.history].reverse().map(t => {
        const badgeClass = {TP:'badge-tp',SL:'badge-sl','AI-EXIT':'badge-aiexit',TRAIL:'badge-trail',FASTCUT:'badge-fastcut',RECOVERY:'badge-recovery'}[t.result] || 'badge-sl';
        const pnlClass   = t.pnl_usd >= 0 ? 'pos' : 'neg';
        const pnlSign    = t.pnl_usd >= 0 ? '+' : '';
        const feeNote    = t.fee_usd ? ` | Fee: -$${t.fee_usd.toFixed(4)}` : '';
        return `<div class="trade-row">
          <div>
            <div class="trade-symbol">${icons[t.result]||'?'} ${esc(t.symbol)}</div>
            <div class="trade-detail">${esc(t.time)}${feeNote}</div>
          </div>
          <div style="display:flex;align-items:center;gap:8px;">
            <span class="${badgeClass}">${esc(t.result)}</span>
            <span class="trade-pnl ${pnlClass}">${pnlSign}$${Math.abs(t.pnl_usd).toFixed(4)}</span>
          </div>
        </div>`;
      }).join('');
    }

    document.getElementById('last-updated').textContent = 'Updated: ' + new Date().toLocaleTimeString();
  } catch(e) { console.error('fetchData error:', e); }
}

async function fetchLogs(force) {
  if (!consoleOpen && !force) return;
  try {
    const r = await fetch('/api/logs?after=' + logTotal);
    const d = await r.json();
    if (d.logs && d.logs.length > 0) {
      logTotal = d.total;
      const body = document.getElementById('modal-console-body');
      const atBottom = body.scrollHeight - body.clientHeight <= body.scrollTop + 30;
      const colors = {INFO:'#a0aec0',TRADE:'#48bb78',WARN:'#f6ad55',ERROR:'#fc8181',AI:'#b794f4',RULES:'#63b3ed',SYSTEM:'#76e4f7',FEE:'#f6ad55'};
      d.logs.forEach(l => {
        const div = document.createElement('div');
        div.className = 'log-line';
        const c = colors[l.level] || '#a0aec0';
        div.innerHTML = `<span class="log-ts">${esc(l.ts)}</span><span class="log-msg" style="color:${c}">[${esc(l.level)}] ${esc(l.msg)}</span>`;
        body.appendChild(div);
      });
      if (atBottom) body.scrollTop = body.scrollHeight;
    }
  } catch(e) {}
}

async function fetchCoins() {
  if (!coinsOpen) return;
  try {
    const r = await fetch('/api/coins');
    const d = await r.json();
    const body = document.getElementById('coins-body');
    if (!d.coins || d.coins.length === 0) {
      body.innerHTML = '<div class="no-data">No coins scanned yet...</div>'; return;
    }
    body.innerHTML = d.coins.map(c => {
      const cls = {PASS:'pass',FAIL:'fail',BUY:'buy'}[c.status] || 'fail';
      const badge = {PASS:'badge-pass',FAIL:'badge-fail',BUY:'badge-buy'}[c.status] || 'badge-fail';
      const mc  = fmtK(c.mc);
      const vol = fmtK(c.vol5m);
      return `<div class="coin-row ${cls}">
        <div style="flex-shrink:0">
          <div class="coin-sym">${esc(c.symbol)}</div>
          <div class="coin-ts">${c.ts}</div>
        </div>
        <div style="flex:1">
          <div class="coin-stats">
            <span>MC $${mc}</span><span>Vol5m $${vol}</span>
            <span>BR ${c.br5m}x</span><span>${c.confirmations} ✓</span>
          </div>
          ${c.fail_reason ? '<div class="coin-fail-reason">⚠️ '+esc(c.fail_reason)+'</div>' : ''}
        </div>
        <div class="coin-links">
          <a class="coin-link" href="${c.dex_url}" target="_blank" rel="noopener">🔗 DEX</a>
          <a class="coin-link" href="https://solscan.io/token/${c.address}" target="_blank" rel="noopener">🔍 Scan</a>
        </div>
      </div>`;
    }).join('');
  } catch(e) {}
}

async function fetchWatch() {
  if (!watchOpen) return;
  try {
    const r = await fetch('/api/market_watch');
    const d = await r.json();
    const body = document.getElementById('watch-body');
    const score = d.market_score || 50;
    const scoreColor = score >= 70 ? '#48bb78' : (score < 40 ? '#fc8181' : '#f6ad55');
    body.innerHTML = `
      <div style="margin-bottom:12px;">
        <div style="font-size:.7rem;color:#718096;text-transform:uppercase;letter-spacing:1px;margin-bottom:4px;">Market Confidence Score</div>
        <div style="display:flex;align-items:center;gap:10px;">
          <div style="font-size:1.8rem;font-weight:700;color:${scoreColor}">${score}%</div>
          <div class="score-track" style="flex:1;height:8px;background:#1a1d2e;border-radius:999px;overflow:hidden;">
            <div class="score-fill" style="width:${score}%;background:${scoreColor};height:100%;border-radius:999px;"></div>
          </div>
        </div>
      </div>
      ${d.last_analysis ? `<div style="font-size:.78rem;color:#cbd5e0;line-height:1.6;background:#12151f;padding:12px;border-radius:10px;border-left:3px solid #7b2ff7;">${esc(d.last_analysis)}</div>` : '<div style="color:#4a5568;font-size:.8rem;">AI abhi market analyze kar raha hai...</div>'}
      ${d.hot_coins && d.hot_coins.length > 0 ? `<div style="margin-top:12px;font-size:.7rem;color:#00d4ff;font-weight:700;text-transform:uppercase;letter-spacing:1px;">🔥 AI Watched Coins</div><div style="margin-top:6px;">${d.hot_coins.map(c=>`<div style="background:#1a1d2e;border-radius:8px;padding:7px 10px;margin-bottom:6px;font-size:.75rem;color:#e2e8f0;border:1px solid #2d3748;">${esc(c)}</div>`).join('')}</div>` : ''}
      <div style="margin-top:10px;font-size:.65rem;color:#4a5568;">Last update: ${d.last_ts ? new Date(d.last_ts*1000).toLocaleTimeString() : '--'}</div>
    `;
  } catch(e) {}
}

function esc(s) {
  return String(s||'').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
}
function fmt(n) {
  if (!n) return '?';
  if (n >= 1e6) return (n/1e6).toFixed(2)+'M';
  if (n >= 1e3) return (n/1e3).toFixed(1)+'K';
  return String(Math.round(n));
}
function fmtK(n) {
  if (!n) return '?';
  if (n >= 1e6) return (n/1e6).toFixed(1)+'M';
  if (n >= 1e3) return (n/1e3).toFixed(0)+'K';
  return String(Math.round(n));
}

async function sendChat() {
  const inp  = document.getElementById('chat-input');
  const body = document.getElementById('chat-body');
  const btn  = document.getElementById('chat-send-btn');
  const msg  = inp.value.trim();
  if (!msg || btn.disabled) return;

  const uDiv = document.createElement('div');
  uDiv.className = 'chat-msg user';
  uDiv.textContent = msg;
  body.appendChild(uDiv);
  inp.value = '';
  btn.disabled = true;

  const tDiv = document.createElement('div');
  tDiv.className = 'chat-typing';
  tDiv.id = 'chat-typing';
  tDiv.textContent = '⏳ AI soch raha hai...';
  body.appendChild(tDiv);
  body.scrollTop = body.scrollHeight;

  try {
    const r = await fetch('/api/ai_chat', {
      method: 'POST', headers: {'Content-Type':'application/json'},
      body: JSON.stringify({message: msg})
    });
    const d = await r.json();
    document.getElementById('chat-typing')?.remove();
    const bDiv = document.createElement('div');
    bDiv.className = 'chat-msg bot';
    bDiv.textContent = d.reply || '❌ Jawab nahi mila.';
    body.appendChild(bDiv);
  } catch(e) {
    document.getElementById('chat-typing')?.remove();
    const eDiv = document.createElement('div');
    eDiv.className = 'chat-msg bot';
    eDiv.textContent = '❌ Server se jawab nahi mila.';
    body.appendChild(eDiv);
  }

  btn.disabled = false;
  body.scrollTop = body.scrollHeight;
  inp.focus();
}

fetchData();
setInterval(fetchData, 10000);
setInterval(() => { fetchLogs(); fetchCoins(); if(watchOpen) fetchWatch(); }, 5000);
</script>
</body>
</html>"""


@app.route("/")
def dashboard():
    return render_template_string(DASHBOARD_HTML)


@app.route("/api/status")
def api_status():
    wins      = [t for t in trade_history if t["result"] == "TP"]
    losses    = [t for t in trade_history if t["result"] in ("SL","FASTCUT","AI-EXIT","TRAIL")]
    total_pnl = sum(t["pnl_usd"] for t in trade_history)
    win_rate  = (len(wins) / len(trade_history) * 100) if trade_history else 0
    runtime   = datetime.now() - start_time
    hours     = int(runtime.total_seconds() // 3600)
    minutes   = int((runtime.total_seconds() % 3600) // 60)

    positions_data = []
    for addr, pos in positions.items():
        cp      = pos.get("current_price", pos["entry_price"])
        cur_mc  = pos.get("current_mc", pos.get("entry_mc", 0))
        pnl_pct = (cp - pos["entry_price"]) / pos["entry_price"] * 100
        pnl_usd = (cp - pos["entry_price"]) * pos["amount_tokens"]
        positions_data.append({
            "address": addr, "symbol": pos["symbol"],
            "entry_price": pos["entry_price"], "current_price": cp,
            "entry_mc": pos.get("entry_mc", 0), "current_mc": cur_mc,
            "amount_usd": pos["amount_usd"], "amount_tokens": pos["amount_tokens"],
            "tp_price": pos["tp_price"], "sl_price": pos["sl_price"],
            "pnl_pct": pnl_pct, "pnl_usd": pnl_usd,
            "peak_pnl_usd": pos.get("peak_pnl_usd", 0.0),
            "ai_confidence": pos.get("ai_confidence", 0),
            "ai_reason": pos.get("ai_reason", ""),
            "entry_mode": pos.get("entry_mode", "AI"),
            "entry_time": pos["entry_time"].strftime("%H:%M:%S"),
        })

    _check_daily_reset()
    return jsonify({
        "balance": round(balance_usd, 4), "target": TARGET_BALANCE_USD,
        "total_pnl": round(total_pnl, 4), "wins": len(wins), "losses": len(losses),
        "win_rate": round(win_rate, 1), "paused": bot_paused, "scan_count": scan_count,
        "runtime": f"{hours}h {minutes}m", "ai_mode": ai_mode,
        "positions": positions_data,
        "history": [{"symbol":t["symbol"],"result":t["result"],"pnl_usd":t["pnl_usd"],
                     "pnl_pct":t["pnl_pct"],"time":t["time"].strftime("%d %b %H:%M"),
                     "fee_usd":t.get("fee_usd",0)}
                    for t in trade_history],
        "tp_pct": TP_PERCENT, "sl_pct": SL_PERCENT, "trail_drop": TRAIL_DROP_USD,
        "sol_trend": sol_trend,
        "total_fees": round(total_fees_paid, 4),
        "daily_trades": daily_trades,
        "daily_limit": _get_daily_limit(),
        "market_score": market_watch.get("market_score", 50),
    })


@app.route("/api/logs")
def api_logs():
    after = int(freq.args.get("after", 0))
    with _console_lock:
        all_logs = list(console_logs)
    total    = len(all_logs)
    new_logs = all_logs[after:] if after < total else []
    return jsonify({"logs": new_logs, "total": total})


@app.route("/api/coins")
def api_coins():
    with _coins_lock:
        coins = list(scanned_coins)
    return jsonify({"coins": coins, "count": len(coins)})


@app.route("/api/market_watch")
def api_market_watch():
    with _watch_lock:
        data = dict(market_watch)
    return jsonify(data)


@app.route("/api/ai_chat", methods=["POST"])
def api_ai_chat():
    data     = freq.json or {}
    user_msg = data.get("message", "").strip()[:500]
    if not user_msg:
        return jsonify({"ok": False, "reply": "Koi message nahi mila."})

    wins      = [t for t in trade_history if t["result"] == "TP"]
    losses    = [t for t in trade_history if t["result"] in ("SL","FASTCUT","AI-EXIT","TRAIL")]
    total_pnl = sum(t["pnl_usd"] for t in trade_history)
    win_rate  = (len(wins) / len(trade_history) * 100) if trade_history else 0
    mkt       = sol_trend

    open_pos_str = "Koi open position nahi hai."
    for addr, pos in positions.items():
        cp      = pos.get("current_price", pos["entry_price"])
        pnl_pct = (cp - pos["entry_price"]) / pos["entry_price"] * 100
        pnl_usd = (cp - pos["entry_price"]) * pos["amount_tokens"]
        open_pos_str = (
            f"{pos['symbol']} | PnL: {pnl_pct:+.2f}% (${pnl_usd:+.2f}) | "
            f"Entry: ${pos['entry_price']:.8f} | Amount: ${pos['amount_usd']:.2f}"
        )

    recent_trades = ""
    for t in list(reversed(trade_history))[:5]:
        recent_trades += f"\n  {t['symbol']}: {t['result']} {t['pnl_pct']:+.1f}% (${t['pnl_usd']:+.2f})"

    context = f"""Tu ek Solana meme coin trading bot ka AI assistant hai. Seedha, mukhtasar aur helpful jawab de. Urdu ya Roman Urdu mein jawab de.

=== LIVE MARKET DATA ===
SOL Market: {mkt.get('label','UNKNOWN')}
SOL Price: ${mkt.get('sol_price',0):.2f}
5m Change: {mkt.get('price_change_5m',0):+.2f}% | 1h Change: {mkt.get('price_change_1h',0):+.2f}%
Market Confidence Score: {market_watch.get('market_score',50)}%

=== BOT STATUS ===
Balance: ${balance_usd:.2f} | Target: ${TARGET_BALANCE_USD:.2f}
Total PnL: ${total_pnl:+.2f} | Net after fees: ${total_pnl - total_fees_paid:+.2f}
Total Fees Paid: ${total_fees_paid:.4f}
Today's trades: {daily_trades} | Market gate: {_get_daily_limit()} | Today's fees: ${daily_fees:.4f}
Win Rate: {win_rate:.0f}% | Wins: {len(wins)} | Losses: {len(losses)}
AI Mode: {ai_mode}

=== OPEN POSITION ===
{open_pos_str}

=== RECENT TRADES ==={recent_trades if recent_trades else ' Koi trade nahi hua'}

=== AI MARKET WATCH ===
{market_watch.get('last_analysis', 'Abhi analyze ho raha hai...')}"""

    if not GROQ_SLOTS:
        return jsonify({"ok": False, "reply": "AI offline hai. Groq API keys set karo."})

    for api_key, model in GROQ_SLOTS:
        try:
            resp = requests.post(
                "https://api.groq.com/openai/v1/chat/completions",
                headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
                json={"model": model,
                      "messages":[{"role":"system","content":context},
                                  {"role":"user","content":user_msg}],
                      "temperature": 0.7, "max_tokens": 300},
                timeout=20,
            )
            if resp.status_code == 200:
                reply = resp.json()["choices"][0]["message"]["content"].strip()
                return jsonify({"ok": True, "reply": reply})
        except:
            continue

    return jsonify({"ok": False, "reply": "AI abhi busy hai. Thodi der baad koshish karo."})


@app.route("/api/toggle_pause", methods=["POST"])
def api_toggle_pause():
    global bot_paused
    bot_paused = not bot_paused
    log_console(f"{'⏸️ Bot PAUSED' if bot_paused else '▶️ Bot RESUMED'}", "WARN" if bot_paused else "SYSTEM")
    send_telegram(f"{'⏸️ <b>Bot PAUSED</b>' if bot_paused else '▶️ <b>Bot RESUMED</b>'}")
    return jsonify({"paused": bot_paused})


@app.route("/api/force_close", methods=["POST"])
def api_force_close():
    addr = (freq.json or {}).get("address", "")
    if addr not in positions:
        return jsonify({"ok": False, "error": "Position not found"})
    pos = positions[addr]
    try:
        resp  = requests.get(f"https://api.dexscreener.com/latest/dex/tokens/{addr}", timeout=8)
        pairs = resp.json().get("pairs", [])
        cur_price = float(pairs[0]["priceUsd"]) if pairs else pos["entry_price"]
    except:
        cur_price = pos.get("current_price", pos["entry_price"])
    pnl_pct  = (cur_price - pos["entry_price"]) / pos["entry_price"] * 100
    pnl_usd  = (cur_price - pos["entry_price"]) * pos["amount_tokens"]
    exit_val = pos["amount_tokens"] * cur_price
    _close_position(addr, pos, cur_price, pnl_pct, pnl_usd, exit_val, "FASTCUT", "Manual force close")
    return jsonify({"ok": True, "pnl_usd": round(pnl_usd, 4), "pnl_pct": round(pnl_pct, 2)})


def run_web():
    import socket, signal, subprocess
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            s.bind(("0.0.0.0", PORT))
    except OSError:
        try:
            result = subprocess.check_output(["fuser", f"{PORT}/tcp"], stderr=subprocess.DEVNULL)
            for pid in result.split():
                try: os.kill(int(pid), signal.SIGKILL)
                except: pass
        except: pass
        time.sleep(1)
    app.run(host="0.0.0.0", port=PORT, debug=False, use_reloader=False, threaded=True)


# ==================== TELEGRAM ====================

def send_telegram(message, chat_id=None):
    if not TELEGRAM_BOT_TOKEN:
        return
    try:
        url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
        requests.post(url, json={
            "chat_id": chat_id or TELEGRAM_CHAT_ID,
            "text": message, "parse_mode": "HTML"
        }, timeout=10)
    except Exception as e:
        log_console(f"Telegram error: {e}", "ERROR")


def get_updates(offset=0):
    if not TELEGRAM_BOT_TOKEN:
        return []
    try:
        url  = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/getUpdates"
        resp = requests.get(url, params={"offset":offset,"timeout":30,"allowed_updates":["message"]}, timeout=35)
        if resp.status_code == 200:
            return resp.json().get("result", [])
    except:
        pass
    return []


def cmd_status(chat_id):
    wins   = [t for t in trade_history if t["result"] == "TP"]
    losses = [t for t in trade_history if t["result"] in ("SL","FASTCUT","AI-EXIT","TRAIL")]
    pnl    = sum(t["pnl_usd"] for t in trade_history)
    wr     = (len(wins)/len(trade_history)*100) if trade_history else 0
    rt     = datetime.now() - start_time
    h,m    = int(rt.total_seconds()//3600), int((rt.total_seconds()%3600)//60)
    send_telegram(f"""📊 <b>STATUS</b>
⏱ {h}h {m}m | 🧠 {ai_mode}
💼 ${balance_usd:.2f} / ${TARGET_BALANCE_USD:.2f}
💰 PnL: ${pnl:+.2f} | Net: ${pnl-total_fees_paid:+.2f}
💸 Fees: ${total_fees_paid:.4f} | Today: {daily_trades} trades | Gate: {_get_daily_limit()}
✅{len(wins)} ❌{len(losses)} ({wr:.0f}%)
📡 Market: {sol_trend.get('label','?')} | Score: {market_watch.get('market_score',50)}%""", chat_id)


def handle_command(text, chat_id):
    cmd = text.strip().lower().split()[0]
    cmds = {
        "/start":   lambda c: send_telegram(f"🤖 <b>AI SMART TRADING BOT</b>\n${balance_usd:.2f} → ${TARGET_BALANCE_USD:.2f}\n/status /pause /resume /help", c),
        "/status":  cmd_status,
        "/balance": lambda c: send_telegram(f"💼 ${balance_usd:.2f} | Fees: ${total_fees_paid:.4f}", c),
        "/pause":   lambda c: (setattr(__import__('builtins'), '_bp', True), log_console("Paused via Telegram","SYSTEM"), send_telegram("⏸ Paused.", c)),
        "/resume":  lambda c: (setattr(__import__('builtins'), '_bp', False), log_console("Resumed via Telegram","SYSTEM"), send_telegram("▶️ Resumed.", c)),
        "/help":    lambda c: send_telegram("/start /status /balance /pause /resume /help", c),
    }
    fn = cmds.get(cmd)
    if fn:
        fn(chat_id)
    else:
        send_telegram(f"❓ Unknown: {cmd} — /help", chat_id)


def command_listener():
    global last_update_id, bot_paused
    log_console("Telegram command listener started", "SYSTEM")
    while True:
        try:
            for update in get_updates(offset=last_update_id + 1):
                last_update_id = update["update_id"]
                msg  = update.get("message", {})
                text = msg.get("text", "")
                cid  = msg.get("chat", {}).get("id")
                if text and text.startswith("/") and cid:
                    if "/pause" in text:  bot_paused = True
                    if "/resume" in text: bot_paused = False
                    handle_command(text, cid)
        except:
            time.sleep(5)
        time.sleep(2)


# ==============================================================
# ==================== MARKET TREND ANALYSIS ==================
# ==============================================================

def get_sol_market_trend() -> dict:
    global sol_trend
    try:
        resp = _dex_get(
            "https://api.dexscreener.com/latest/dex/tokens/So11111111111111111111111111111111111111112",
            timeout=8
        )
        if resp is None or resp.status_code != 200:
            return sol_trend
        pairs = resp.json().get("pairs", [])
        if not pairs:
            return sol_trend

        sol_pair = None
        for p in pairs:
            qt  = (p.get("quoteToken") or {}).get("symbol", "")
            liq = float((p.get("liquidity") or {}).get("usd", 0) or 0)
            if qt in ("USDC", "USDT") and liq > 50_000:
                sol_pair = p
                break
        if not sol_pair:
            sol_pair = pairs[0]

        pc5m  = float((sol_pair.get("priceChange") or {}).get("m5",  0) or 0)
        pc1h  = float((sol_pair.get("priceChange") or {}).get("h1",  0) or 0)
        price = float(sol_pair.get("priceUsd", 0) or 0)

        if pc1h >= 2.0 and pc5m >= 0:
            label = "🟢 BULLISH"
        elif pc1h >= 0 and pc5m >= -0.5:
            label = "🟡 NEUTRAL"
        elif pc1h < -4.0 or (pc5m < -2.0 and pc1h < -1.0):
            label = "🔴 BEARISH"
        else:
            label = "🟠 CAUTIOUS"

        sol_trend = {
            "price_change_5m": round(pc5m, 2),
            "price_change_1h": round(pc1h, 2),
            "label": label,
            "sol_price": round(price, 2),
            "ts": time.time()
        }
        log_console(
            f"📊 SOL: {label} | ${price:.2f} | 5m:{pc5m:+.2f}% 1h:{pc1h:+.2f}%",
            "SYSTEM"
        )
    except Exception as e:
        log_console(f"SOL trend error: {e}", "WARN")
    return sol_trend


# ==============================================================
# ============= CONTINUOUS MARKET WATCHER THREAD ==============
# ==============================================================

def _build_market_watch_prompt() -> str:
    """Build prompt for background market intelligence."""
    mkt = sol_trend
    open_pos_info = ""
    for addr, pos in positions.items():
        cp      = pos.get("current_price", pos["entry_price"])
        pnl_pct = (cp - pos["entry_price"]) / pos["entry_price"] * 100
        open_pos_info = f"\nACTIVE POSITION: {pos['symbol']} PnL:{pnl_pct:+.2f}%"

    return f"""You are an AI market analyst watching Solana meme coin markets in real time.

CURRENT MARKET STATE:
SOL: {mkt.get('label','UNKNOWN')} | ${mkt.get('sol_price',0):.2f}
5m: {mkt.get('price_change_5m',0):+.2f}% | 1h: {mkt.get('price_change_1h',0):+.2f}%
Bot Balance: ${balance_usd:.2f} | Daily trades: {daily_trades} | Gate: {_get_daily_limit()}
Total fees paid today: ${daily_fees:.4f}{open_pos_info}

Give:
1. Market Score (0-100): How good is NOW to trade meme coins?
2. Brief analysis (2-3 sentences): What is the market doing?
3. Trading advice: Should bot be aggressive/conservative/wait?

Keep it SHORT and actionable. Reply in this JSON format:
{{"score": 0-100, "analysis": "text", "advice": "text", "hot_signals": ["signal1","signal2"]}}"""


def continuous_market_watcher():
    """Background thread — runs every 60s, updates market_watch state."""
    global market_watch
    log_console("📡 Market watcher thread started", "SYSTEM")
    time.sleep(15)  # warm up delay

    while True:
        try:
            if not GROQ_SLOTS:
                time.sleep(60)
                continue

            prompt = _build_market_watch_prompt()
            for api_key, model in GROQ_SLOTS:
                try:
                    resp = requests.post(
                        "https://api.groq.com/openai/v1/chat/completions",
                        headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
                        json={"model": model,
                              "messages":[{"role":"system","content":"You are a crypto market analyst. JSON only."},
                                          {"role":"user","content":prompt}],
                              "temperature": 0.3, "max_tokens": 200},
                        timeout=15,
                    )
                    if resp.status_code == 200:
                        raw = resp.json()["choices"][0]["message"]["content"].strip()
                        raw = raw.replace("```json","").replace("```","").strip()
                        result = json.loads(raw)
                        score    = int(result.get("score", 50))
                        analysis = result.get("analysis","")
                        advice   = result.get("advice","")
                        signals  = result.get("hot_signals", [])

                        full_text = f"{analysis} {advice}".strip()
                        with _watch_lock:
                            market_watch["market_score"]  = score
                            market_watch["last_analysis"] = full_text
                            market_watch["hot_coins"]     = signals[:5]
                            market_watch["last_ts"]       = time.time()

                        log_console(f"📡 Market Watch: Score={score}% | {analysis[:80]}", "SYSTEM")
                        break
                except json.JSONDecodeError:
                    pass
                except Exception as e:
                    log_console(f"Market watcher error: {e}", "WARN")
                    break

        except Exception as e:
            log_console(f"Market watcher outer error: {e}", "ERROR")

        time.sleep(market_watch.get("watch_interval", 60))


# ==============================================================
# ==================== AI BRAIN (PRIMARY) =====================
# ==============================================================

def _build_entry_prompt(td: dict) -> str:
    age      = td.get("pair_age_hours", 999)
    age_str  = f"{age:.1f}h" if age < 999 else "?"
    age_tag  = "🆕 VERY FRESH" if age <= 1 else ("fresh" if age <= 3 else ("new" if age <= 6 else "older"))
    socials  = f"TW={'✅' if td.get('has_twitter') else '❌'} TG={'✅' if td.get('has_telegram_social') else '❌'} Web={'✅' if td.get('has_website') else '❌'}"
    mkt      = sol_trend
    mkt_warn = ""
    if "BEARISH" in mkt.get("label",""):
        mkt_warn = "\n⚠️ BEARISH MARKET — confidence must be 92%+ to BUY."
    elif "CAUTIOUS" in mkt.get("label",""):
        mkt_warn = "\n⚠️ CAUTIOUS market — confidence must be 87%+ to BUY."

    watch_score = market_watch.get("market_score", 50)
    watch_note  = market_watch.get("last_analysis", "")[:120]

    fee_cost = td.get("amount_usd", 20) * (DEX_FEE_PCT + SLIPPAGE_PCT) / 100
    min_profit_needed = fee_cost * 2  # need 2x fees to be worth it

    return f"""You are a Solana meme coin trader making a BUY/SKIP decision with REAL MONEY.

=== COST REALITY ===
Buy fee: ~${fee_cost:.3f} | Min profit needed: ~${min_profit_needed:.3f}
Only enter if expected profit clearly exceeds fees.{mkt_warn}

=== MACRO CONTEXT ===
SOL: {mkt.get('label','UNKNOWN')} | ${mkt.get('sol_price',0):.2f} | 5m:{mkt.get('price_change_5m',0):+.2f}% 1h:{mkt.get('price_change_1h',0):+.2f}%
AI Market Score: {watch_score}/100 | {watch_note}

=== TOKEN DATA ===
Token: {td.get('symbol')} | Age: {age_str} [{age_tag}]
FDV: ${td.get('mc',0):,.0f} | Liq: ${td.get('liquidity',0):,.0f}
Vol5m: ${td.get('vol_5m',0):,.0f} | Vol1h: ${td.get('vol_1h',0):,.0f}
BuyRatio5m: {td.get('buy_ratio_5m',0):.2f}x | BuyRatio1h: {td.get('buy_ratio_1h',0):.2f}x
PriceΔ5m: {td.get('price_change_5m',0):.1f}% | PriceΔ1h: {td.get('price_change_1h',0):.1f}%
LP Locked: {td.get('lp_locked',0):.0f}% | MintRevoked: {td.get('mint_revoked',False)}
Socials: {socials} [{td.get('social_score',0)}/3]
Confirmations: {td.get('confirmations_passed',0)}/12
Momentum: {td.get('momentum_label','?')}
Trend alignment: {td.get('trend_alignment','?')}

=== STRICT RULES ===
- Market Score < 40 → SKIP always
- BEARISH SOL → confidence 92%+ only
- CAUTIOUS SOL → confidence 87%+ only
- Price falling 5m → SKIP unless very strong volume
- Already pumped 40%+ in 1h → likely topped → SKIP
- Low social presence + new coin → higher risk, be conservative
- Only BUY when you see CLEAR momentum: price UP + buy ratio UP + volume UP together

Respond ONLY in JSON (no markdown):
{{"decision":"BUY" or "SKIP","confidence":0-100,"reason":"one sentence","risk_level":"LOW" or "MEDIUM" or "HIGH"}}"""


def _build_exit_prompt(pos, cur_price, cur_mc, pnl_pct, pnl_usd, trigger) -> str:
    peak       = pos.get("peak_pnl_usd", 0.0)
    mins       = int((datetime.now() - pos["entry_time"]).total_seconds() / 60)
    giveback   = peak - pnl_usd if peak > 0 else 0
    fee_paid   = pos.get("entry_fee", 0)
    fee_exit   = pos.get("amount_usd", 20) * (DEX_FEE_PCT + SLIPPAGE_PCT) / 100
    net_if_exit = pnl_usd - fee_paid - fee_exit

    return f"""Solana meme trade — EXIT or HOLD decision with real fees.

{pos['symbol']} | Entry: ${pos['entry_price']:.10f} → Now: ${cur_price:.10f}
PnL: {pnl_pct:+.2f}% (${pnl_usd:+.2f}) | Net after fees: ${net_if_exit:+.2f}
Peak: +${peak:.2f} | Gave back: ${giveback:.2f} | In trade: {mins} min
Trigger: {trigger}
Market: {sol_trend.get('label','?')} | AI Score: {market_watch.get('market_score',50)}%

=== RULES ===
- If net profit after ALL fees is negative → strongly consider EXIT
- If gave back >$0.15 from peak while in profit → EXIT to lock gains
- If coin is showing recovery from brief dip → HOLD if market still bullish
- If market score < 40 → bias EXIT for any open position
- Protect capital — a small loss is better than a big loss

Respond JSON only:
{{"action":"EXIT" or "HOLD","reason":"one sentence","urgency":"HIGH" or "NORMAL","recovery_chance":"LOW" or "MEDIUM" or "HIGH"}}"""


def _build_recovery_prompt(pos, cur_price, pnl_pct, pnl_usd, mins_in_trade) -> str:
    """Dedicated prompt: should we hold a losing position hoping for recovery?"""
    fee_paid  = pos.get("entry_fee", 0)
    fee_exit  = pos.get("amount_usd", 20) * (DEX_FEE_PCT + SLIPPAGE_PCT) / 100
    net_loss_if_exit = pnl_usd - fee_paid - fee_exit  # negative number

    return f"""RECOVERY ANALYSIS: Should we hold or cut this losing trade?

Token: {pos['symbol']}
Current loss: {pnl_pct:.2f}% (${pnl_usd:.2f})
Net loss if exit now: ${net_loss_if_exit:.2f} (includes all fees)
Time in trade: {mins_in_trade} min
Market: {sol_trend.get('label','?')} | AI Score: {market_watch.get('market_score',50)}/100

CONTEXT:
- We chose this coin because AI was {pos.get('ai_confidence',0)}% confident
- Entry reason: {pos.get('ai_reason','N/A')}
- Current momentum unknown — coin may recover or keep falling

RULE: Only hold if recovery chance is genuinely HIGH. When in doubt, CUT.
A smaller certain loss beats a larger uncertain loss.

JSON only:
{{"hold":"yes" or "no","recovery_chance":"LOW" or "MEDIUM" or "HIGH","reason":"one sentence","urgency":"HIGH" or "NORMAL"}}"""


def ask_ai(prompt: str, system: str = "Crypto trader. JSON only.", max_tokens: int = 120, temp: float = 0.15) -> dict | None:
    """Generic AI call. Returns parsed dict or None."""
    for api_key, model in GROQ_SLOTS:
        try:
            resp = requests.post(
                "https://api.groq.com/openai/v1/chat/completions",
                headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
                json={"model": model,
                      "messages":[{"role":"system","content":system},
                                  {"role":"user","content":prompt}],
                      "temperature": temp, "max_tokens": max_tokens},
                timeout=14,
            )
            if resp.status_code == 200:
                raw = resp.json()["choices"][0]["message"]["content"].strip()
                raw = raw.replace("```json","").replace("```","").strip()
                return json.loads(raw)
            elif resp.status_code == 429:
                continue
        except json.JSONDecodeError:
            continue
        except Exception:
            continue
    return None


def ask_ai_entry(token_data: dict) -> dict:
    global ai_mode, ai_down_notified

    if not GROQ_SLOTS:
        return _rule_based_entry(token_data)

    prompt = _build_entry_prompt(token_data)
    result = ask_ai(prompt, system="Crypto trader. JSON only, no markdown.", max_tokens=150, temp=0.1)

    if result:
        result["mode"] = "AI"
        if ai_mode == "RULES":
            ai_mode          = "AI"
            ai_down_notified = False
            log_console("AI back online", "SYSTEM")

        # Extra gate: if AI market score is too low, override to SKIP
        if market_watch.get("market_score", 50) < 35 and result.get("decision") == "BUY":
            result["decision"]   = "SKIP"
            result["reason"]     = f"Market watch score {market_watch.get('market_score',50)}% too low — waiting for better market"
            result["confidence"] = 0

        log_console(
            f"🤖 AI → {result.get('decision')} {result.get('confidence')}% [{result.get('risk_level','?')}] | {token_data.get('symbol')} | {result.get('reason','')}",
            "AI"
        )
        return result

    # All slots failed
    if not ai_down_notified:
        ai_mode          = "RULES"
        ai_down_notified = True
        log_console("All Groq slots failed — switching to RULE-BASED", "WARN")
        send_telegram("⚠️ <b>AI Down</b> — switching to Rule-Based mode.")

    return _rule_based_entry(token_data)


def ask_ai_exit(pos, cur_price, cur_mc, pnl_pct, pnl_usd, trigger) -> dict:
    if not GROQ_SLOTS or ai_mode == "RULES":
        return _rule_based_exit(pnl_pct, pnl_usd, pos.get("peak_pnl_usd", 0))

    prompt = _build_exit_prompt(pos, cur_price, cur_mc, pnl_pct, pnl_usd, trigger)
    result = ask_ai(prompt, system="Risk manager. JSON only. Bias toward protecting capital.", max_tokens=100, temp=0.05)

    if result:
        log_console(f"🤖 AI Exit → {result.get('action')} ({result.get('urgency','?')}) Recovery:{result.get('recovery_chance','?')} | {result.get('reason','')}", "AI")
        return result

    return _rule_based_exit(pnl_pct, pnl_usd, pos.get("peak_pnl_usd", 0))


def ask_ai_recovery(pos, cur_price, pnl_pct, pnl_usd, mins_in_trade) -> dict:
    """Ask AI specifically whether to hold a losing trade for recovery."""
    if not GROQ_SLOTS or ai_mode == "RULES":
        # Rule: if losing more than 1.5% → cut, else hold briefly
        if pnl_pct < -1.5:
            return {"hold": "no", "reason": "Loss too deep to recover", "urgency": "HIGH", "recovery_chance": "LOW"}
        return {"hold": "yes", "reason": "Small loss, may recover", "urgency": "NORMAL", "recovery_chance": "MEDIUM"}

    prompt = _build_recovery_prompt(pos, cur_price, pnl_pct, pnl_usd, mins_in_trade)
    result = ask_ai(prompt, system="Risk analyst. JSON only.", max_tokens=100, temp=0.1)

    if result:
        log_console(f"🧠 Recovery check → Hold:{result.get('hold')} Chance:{result.get('recovery_chance')} | {result.get('reason','')}", "AI")
        return result

    return {"hold": "no", "reason": "AI unavailable — cut loss", "urgency": "NORMAL", "recovery_chance": "LOW"}


# ==============================================================
# ==================== RULE-BASED FALLBACK ====================
# ==============================================================

def _rule_based_entry(token_data: dict) -> dict:
    br5m   = token_data.get("buy_ratio_5m", 0)
    pc5m   = token_data.get("price_change_5m", 0)
    pc1h   = token_data.get("price_change_1h", 0)
    liq    = token_data.get("liquidity", 0)
    vol5m  = token_data.get("vol_5m", 0)
    mc     = token_data.get("mc", 0)
    confs  = token_data.get("confirmations_passed", 0)
    social = token_data.get("social_score", 0)
    sym    = token_data.get("symbol", "?")
    age    = token_data.get("pair_age_hours", 999)

    if br5m < 1.2:
        return {"decision":"SKIP","confidence":0,"reason":f"[Rules] BR too low {br5m:.2f}","mode":"RULES"}
    if liq  < MIN_LIQUIDITY:
        return {"decision":"SKIP","confidence":0,"reason":f"[Rules] Liq too low","mode":"RULES"}
    if mc   < MIN_MC or mc > MAX_MC:
        return {"decision":"SKIP","confidence":0,"reason":f"[Rules] FDV out of range","mode":"RULES"}
    if pc1h > 100:
        return {"decision":"SKIP","confidence":0,"reason":f"[Rules] Already pumped {pc1h:.0f}%","mode":"RULES"}
    if pc5m < -2.0:
        return {"decision":"SKIP","confidence":0,"reason":f"[Rules] Falling {pc5m:.1f}% in 5m","mode":"RULES"}

    score = 0
    if   br5m >= 3.0:  score += 28
    elif br5m >= 2.0:  score += 20
    elif br5m >= 1.5:  score += 12
    elif br5m >= 1.2:  score += 6

    if   0 < pc5m <= 20:  score += 20
    elif pc5m > 0:         score += 10

    if   pc1h < 25:  score += 15
    elif pc1h < 50:  score += 8

    if   20_000 <= liq <= 150_000: score += 15
    elif  8_000 <= liq <= 300_000: score += 7

    if   vol5m >= 20_000: score += 15
    elif vol5m >= 10_000: score += 10
    elif vol5m >= 5_000:  score += 5

    if   confs >= 10: score += 10
    elif confs >= 8:  score += 7

    if   social >= 3: score += 8
    elif social >= 2: score += 5

    if   age <= 2:  score += 7
    elif age <= 6:  score += 4

    confidence = min(int(score), 95)
    log_console(f"[Rules] {sym}: {confidence}% (BR={br5m:.2f} Vol5m=${vol5m:,.0f})", "RULES")

    if confidence >= MIN_RULES_CONFIDENCE:
        return {"decision":"BUY","confidence":confidence,
                "reason":f"[Rules] BR={br5m:.2f}x Vol5m=${vol5m:,.0f} Confs={confs}/12","mode":"RULES"}
    return {"decision":"SKIP","confidence":confidence,
            "reason":f"[Rules] Score {confidence}% < threshold","mode":"RULES"}


def _rule_based_exit(pnl_pct: float, pnl_usd: float, peak_usd: float) -> dict:
    giveback = peak_usd - pnl_usd if peak_usd > 0 else 0
    if pnl_pct < -1.2:
        return {"action":"EXIT","reason":"[Rules] Hard stop","urgency":"HIGH","recovery_chance":"LOW"}
    if giveback >= TRAIL_DROP_USD and peak_usd >= TRAIL_TRIGGER_USD:
        return {"action":"EXIT","reason":f"[Rules] Gave back ${giveback:.2f}","urgency":"HIGH","recovery_chance":"LOW"}
    if pnl_pct < -0.5:
        return {"action":"EXIT","reason":"[Rules] In loss","urgency":"NORMAL","recovery_chance":"MEDIUM"}
    return {"action":"HOLD","reason":"[Rules] Holding","urgency":"NORMAL","recovery_chance":"MEDIUM"}


# ==================== SCANNING ====================

def rugcheck_token(address: str) -> dict:
    try:
        resp = requests.get(f"https://api.rugcheck.xyz/v1/tokens/{address}/report", timeout=8)
        if resp.status_code == 200:
            sec  = resp.json().get("security", {})
            lp   = sec.get("lpLockedPercentage") or 0
            mint = sec.get("mintAuthorityRevoked", False)
            return {"lp_locked_pct": lp, "mint_revoked": mint}
    except:
        pass
    return {"lp_locked_pct": 0, "mint_revoked": False}


def _pair_age_hours(pair: dict) -> float:
    created = pair.get("pairCreatedAt")
    if not created:
        return 999.0
    try:
        return (time.time() - int(created) / 1000) / 3600
    except:
        return 999.0


def _fetch_concurrent(addresses: list, max_workers: int = 4) -> list:
    results, lock = [], threading.Lock()
    def _fetch(addr):
        if not addr: return
        try:
            r = _dex_get(f"https://api.dexscreener.com/latest/dex/tokens/{addr}", timeout=7)
            if r is not None and r.status_code == 200:
                for p in r.json().get("pairs", []):
                    with lock: results.append(p)
        except: pass

    active = []
    for addr in addresses:
        t = threading.Thread(target=_fetch, args=(addr,), daemon=True)
        active.append(t); t.start()
        if len([x for x in active if x.is_alive()]) >= max_workers:
            time.sleep(0.2)
    for t in active: t.join(timeout=12)
    return results


def get_dexscreener_pairs() -> list:
    new_pairs, old_pairs = [], []
    seen_addrs = set()

    def add_pair(p):
        if not isinstance(p, dict): return
        a = p.get("baseToken", {}).get("address")
        if not a or a in seen_addrs: return
        if p.get("chainId") not in ("solana", None): return
        seen_addrs.add(a)
        if _pair_age_hours(p) <= NEW_COIN_MAX_AGE_HOURS:
            new_pairs.append(p)
        else:
            old_pairs.append(p)

    boost_addrs, profile_addrs = [], []

    for ep in ["https://api.dexscreener.com/token-boosts/top/v1",
               "https://api.dexscreener.com/token-boosts/latest/v1"]:
        resp = _dex_get(ep)
        if resp and resp.status_code == 200:
            try:
                data = resp.json()
                if isinstance(data, list):
                    for b in data:
                        if b.get("chainId") == "solana" and b.get("tokenAddress"):
                            boost_addrs.append(b["tokenAddress"])
            except: pass
        time.sleep(0.5)

    resp = _dex_get("https://api.dexscreener.com/token-profiles/latest/v1")
    if resp and resp.status_code == 200:
        try:
            data = resp.json()
            if isinstance(data, list):
                for p in data:
                    if p.get("chainId") == "solana" and p.get("tokenAddress"):
                        profile_addrs.append(p["tokenAddress"])
        except: pass
    time.sleep(0.5)

    all_addrs = list(dict.fromkeys(boost_addrs[:30] + profile_addrs[:30]))
    log_console(f"Addresses to fetch: {len(all_addrs)}", "INFO")
    if all_addrs:
        for p in _fetch_concurrent(all_addrs, max_workers=4):
            add_pair(p)

    for ep in [
        "https://api.dexscreener.com/latest/dex/pairs/solana",
        "https://api.dexscreener.com/latest/dex/tokens/So11111111111111111111111111111111111111112",
    ]:
        resp = _dex_get(ep)
        if resp and resp.status_code == 200:
            try:
                data = resp.json()
                pairs_list = data if isinstance(data, list) else data.get("pairs", [])
                for p in pairs_list:
                    add_pair(p)
            except: pass
        time.sleep(0.5)

    for q in ["solana meme", "raydium"]:
        resp = _dex_get(f"https://api.dexscreener.com/latest/dex/search?q={q}")
        if resp and resp.status_code == 200:
            try:
                pairs_found = resp.json().get("pairs", [])
                for p in pairs_found:
                    add_pair(p)
            except: pass
        time.sleep(0.5)

    all_pairs = new_pairs + old_pairs
    log_console(f"DexScreener: {len(new_pairs)} new + {len(old_pairs)} older = {len(all_pairs)} total", "INFO")
    return all_pairs


def run_12_confirmations(pair: dict, rug_data: dict):
    base  = pair.get("baseToken", {})
    quote = pair.get("quoteToken", {})
    if quote.get("symbol") != "SOL": return False, 0, {}
    token_addr = base.get("address")
    if not token_addr: return False, 0, {}

    try:
        price_usd = float(pair.get("priceUsd") or 0)
        liq       = float(pair.get("liquidity",{}).get("usd") or 0)
        mc        = float(pair.get("fdv") or pair.get("marketCap") or 0)
        vol       = pair.get("volume", {})
        vol_5m    = float(vol.get("m5") or 0)
        vol_1h    = float(vol.get("h1") or 0)
        pc        = pair.get("priceChange", {})
        pc_5m     = float(pc.get("m5") or 0)
        pc_1h     = float(pc.get("h1") or 0)
        pc_24h    = float(pc.get("h24") or 0)
        t5m       = pair.get("txns",{}).get("m5",{})
        buys_5m   = int(t5m.get("buys") or 0)
        sells_5m  = int(t5m.get("sells") or 1)
        t1h       = pair.get("txns",{}).get("h1",{})
        buys_1h   = int(t1h.get("buys") or 0)
        sells_1h  = int(t1h.get("sells") or 1)
        br5m      = buys_5m / sells_5m if sells_5m > 0 else 0
        br1h      = buys_1h / sells_1h if sells_1h > 0 else 0
        vol_mc    = vol_1h / mc if mc > 0 else 0
        lp_locked = rug_data.get("lp_locked_pct", 0)
        mint_rev  = rug_data.get("mint_revoked", False)
        info      = pair.get("info", {})
        socs      = info.get("socials", [])
        webs      = info.get("websites", [])
        has_tw    = any(s.get("type","").lower() in ("twitter","x") for s in socs)
        has_tg    = any(s.get("type","").lower() == "telegram" for s in socs)
        has_web   = len(webs) > 0
        soc_score = sum([has_tw, has_tg, has_web])

        # Trend alignment: is the coin moving WITH the market?
        sol_pc1h = sol_trend.get("price_change_1h", 0)
        if pc_5m > 0 and pc_1h > 0:
            trend_align = "📈 ALIGNED UP"
        elif pc_5m < 0 and sol_pc1h < 0:
            trend_align = "📉 ALIGNED DOWN"
        elif pc_5m > 0 and sol_pc1h < 0:
            trend_align = "💪 COUNTER-TREND UP (strong)"
        else:
            trend_align = "➡️ MIXED"

        checks = [
            (MIN_LIQUIDITY <= liq <= MAX_LIQUIDITY,              f"1. Liq ${liq:,.0f}"),
            (vol_5m  >= MIN_5M_VOLUME,                           f"2. Vol5m ${vol_5m:,.0f}"),
            (vol_1h  >= MIN_1H_VOLUME,                           f"3. Vol1h ${vol_1h:,.0f}"),
            (round(br5m, 2) >= MIN_BUY_RATIO_5M,                 f"4. BR5m {br5m:.2f}x"),
            (round(br1h, 2) >= MIN_BUY_RATIO_1H,                 f"5. BR1h {br1h:.2f}x"),
            (MIN_MC <= mc <= MAX_MC,                              f"6. FDV ${mc:,.0f}"),
            (lp_locked >= MIN_LP_LOCKED_PCT or mint_rev,          f"7. Safety LP={lp_locked:.0f}%"),
            (MIN_PRICE_CHANGE_5M <= pc_5m <= MAX_PRICE_CHANGE_5M, f"8. PC5m {pc_5m:.1f}%"),
            (MIN_PRICE_CHANGE_1H <= pc_1h <= MAX_PRICE_CHANGE_1H, f"9. PC1h {pc_1h:.1f}%"),
            (vol_mc  >= MIN_VOLUME_MCAP_RATIO,                    f"10. VolMC {vol_mc:.4f}"),
            (buys_5m >= MIN_BUYS_5M,                              f"11. Buys5m {buys_5m}"),
            (soc_score >= 1,                                      f"12. Socials {soc_score}/3"),
        ]

        confs, check_results = 0, []
        for passed, label in checks:
            check_results.append(f"{label}: {'✅' if passed else '❌'}")
            if passed: confs += 1

        if pc_5m >= 3.0 and br5m >= 2.0:
            momentum_label = "🚀 STRONG UP"
        elif pc_5m > 0 and br5m >= 1.3:
            momentum_label = "📈 UP"
        elif pc_5m < -2.0:
            momentum_label = "📉 FALLING"
        elif pc_5m < 0:
            momentum_label = "🔻 SLIGHT DOWN"
        else:
            momentum_label = "➡️ FLAT"

        token_data = {
            "address": token_addr, "symbol": base.get("symbol","UNKNOWN"),
            "price": price_usd, "liquidity": liq, "mc": mc,
            "vol_5m": vol_5m, "vol_1h": vol_1h,
            "buy_ratio_5m": br5m, "buy_ratio_1h": br1h,
            "price_change_5m": pc_5m, "price_change_1h": pc_1h, "price_change_24h": pc_24h,
            "lp_locked": lp_locked, "mint_revoked": mint_rev, "vol_mc_ratio": vol_mc,
            "buys_5m": buys_5m, "has_twitter": has_tw, "has_telegram_social": has_tg,
            "has_website": has_web, "social_score": soc_score,
            "confirmations_passed": confs, "check_results": check_results,
            "momentum_label": momentum_label, "trend_alignment": trend_align,
        }
        return confs >= MIN_CONFIRMATIONS, confs, token_data
    except Exception as e:
        log_console(f"Confirmation error: {e}", "ERROR")
        return False, 0, {}


def analyze_pair(pair: dict):
    base       = pair.get("baseToken", {})
    quote      = pair.get("quoteToken", {})
    symbol     = base.get("symbol", "?")

    if quote.get("symbol") != "SOL": return None

    token_addr = base.get("address")
    if not token_addr or token_addr in seen_tokens or token_addr in positions or token_addr in traded_coins:
        return None

    age_hours = _pair_age_hours(pair)
    if age_hours > NEW_COIN_MAX_AGE_HOURS: return None

    try:
        if float(pair.get("priceChange",{}).get("h1") or 0) > MAX_PRICE_CHANGE_1H:
            return None
    except: pass

    # Quick pre-filter
    try:
        liq      = float(pair.get("liquidity",{}).get("usd") or 0)
        vol_5m   = float(pair.get("volume",{}).get("m5") or 0)
        mc       = float(pair.get("fdv") or pair.get("marketCap") or 0)
        t5m      = pair.get("txns",{}).get("m5",{})
        buys_5m  = int(t5m.get("buys") or 0)
        sells_5m = int(t5m.get("sells") or 1)
        br5m     = buys_5m / sells_5m if sells_5m > 0 else 0
        pc_5m_quick = float(pair.get("priceChange", {}).get("m5") or 0)
        pc_1h_quick = float(pair.get("priceChange", {}).get("h1") or 0)

        fails = []
        if liq   < MIN_LIQUIDITY:   fails.append(f"Liq ${liq:,.0f}<${MIN_LIQUIDITY:,}")
        if liq   > MAX_LIQUIDITY:   fails.append(f"Liq too high")
        if vol_5m < MIN_5M_VOLUME:  fails.append(f"Vol5m ${vol_5m:,.0f}<${MIN_5M_VOLUME:,}")
        if mc    < MIN_MC:           fails.append(f"FDV too low")
        if mc    > MAX_MC:           fails.append(f"FDV too high")
        if br5m  < MIN_BUY_RATIO_5M and buys_5m > 3:
            fails.append(f"BR {br5m:.2f}x<{MIN_BUY_RATIO_5M}x")
        if pc_5m_quick < -2.0:
            fails.append(f"Momentum ❌ PC5m {pc_5m_quick:.1f}% falling")
        if pc_1h_quick > 60.0:
            fails.append(f"Already pumped {pc_1h_quick:.0f}% in 1h")

        status_str = "FAIL" if fails else "PASS"
        fail_str   = " | ".join(fails[:2]) if fails else ""
        log_coin(symbol, token_addr or "", status_str,
                 float(pair.get("priceUsd") or 0), mc, br5m, vol_5m, "?/12", fail_str)

        if fails:
            return None
    except:
        return None

    log_console(f"PreFilter ✅ {symbol} — rugcheck...", "INFO")
    rug_data = rugcheck_token(token_addr)
    passed, score, token_data = run_12_confirmations(pair, rug_data)

    log_coin(symbol, token_addr, "PASS" if passed else "FAIL",
             float(pair.get("priceUsd") or 0), token_data.get("mc",0),
             token_data.get("buy_ratio_5m",0), token_data.get("vol_5m",0),
             f"{score}/12",
             "" if passed else f"{score}/{MIN_CONFIRMATIONS} confirms")

    if not passed:
        seen_tokens.add(token_addr)
        return None

    log_console(f"✅ {symbol} {score}/12 — asking {'AI' if ai_mode=='AI' else 'Rules'}...", "INFO")
    token_data["pair_age_hours"] = age_hours
    token_data["amount_usd"]     = balance_usd  # so AI knows trade size for fee calc

    ai_result  = ask_ai_entry(token_data)
    decision   = ai_result.get("decision","SKIP")
    confidence = ai_result.get("confidence",0)
    reason     = ai_result.get("reason","")
    risk_level = ai_result.get("risk_level","?")
    mode       = ai_result.get("mode","AI")
    min_conf   = MIN_AI_CONFIDENCE if mode == "AI" else MIN_RULES_CONFIDENCE

    log_console(
        f"{'🤖' if mode=='AI' else '📐'} → {decision} {confidence}% [Risk:{risk_level}] | {symbol} | {reason}",
        "AI" if mode == "AI" else "RULES"
    )

    # Extra: skip HIGH risk trades if we've already lost today
    if risk_level == "HIGH":
        today_losses = [t for t in trade_history
                        if t["time"].date() == date.today()
                        and t["result"] in ("SL","FASTCUT","AI-EXIT")
                        and t["pnl_usd"] < 0]
        if len(today_losses) >= 2:
            log_console(f"Skip HIGH-risk {symbol} — already {len(today_losses)} losses today", "WARN")
            seen_tokens.add(token_addr)
            return None

    if decision != "BUY" or confidence < min_conf:
        log_console(f"Skip {symbol} ({confidence}% < {min_conf}% min) — {reason}", "INFO")
        seen_tokens.add(token_addr)
        return None

    token_data["ai_confidence"] = confidence
    token_data["ai_reason"]     = reason
    token_data["entry_mode"]    = mode
    token_data["score"]         = score
    token_data["risk_level"]    = risk_level

    log_coin(symbol, token_addr, "BUY",
             token_data.get("price",0), token_data.get("mc",0),
             token_data.get("buy_ratio_5m",0), token_data.get("vol_5m",0),
             f"{score}/12 ✓", f"Conf {confidence}%")
    return token_data


# ==================== TRADING ====================

def simulate_buy(token_data: dict) -> bool:
    global balance_usd, daily_trades

    if balance_usd < MIN_TRADE_USD or len(positions) >= MAX_POSITIONS:
        return False

    addr          = token_data["address"]
    symbol        = token_data["symbol"]
    price         = token_data["price"]
    amount_usd    = balance_usd
    entry_mc      = token_data.get("mc", 0)
    mode          = token_data.get("entry_mode", "AI")

    # Calculate and deduct entry fee
    entry_fee     = _record_trade_fees(amount_usd)
    amount_after_fee = amount_usd - entry_fee  # actual capital at work
    tokens_bought = amount_after_fee / price

    positions[addr] = {
        "symbol": symbol, "entry_price": price,
        "amount_tokens": tokens_bought,
        "amount_usd": amount_usd,
        "amount_after_fee": amount_after_fee,
        "entry_fee": entry_fee,
        "tp_price": price * (1 + TP_PERCENT / 100),
        "sl_price": price * (1 - SL_PERCENT / 100),
        "entry_mc": entry_mc, "current_mc": entry_mc, "current_price": price,
        "entry_time": datetime.now(),
        "ai_confidence": token_data.get("ai_confidence", 0),
        "ai_reason": token_data.get("ai_reason", ""),
        "entry_mode": mode, "score": token_data.get("score", 0),
        "risk_level": token_data.get("risk_level", "?"),
        "peak_pnl_usd": 0.0, "peak_price": price, "last_price": price,
        "last_pnl_usd": 0.0, "last_check_ts": time.time(),
        "low_pnl": 0.0, "was_in_loss": False, "recovery_checks": 0,
    }
    balance_usd -= amount_usd
    with _daily_lock:
        daily_trades += 1
    traded_coins.add(addr)
    seen_tokens.add(addr)

    age_str   = f"{token_data.get('pair_age_hours',999):.1f}h" if token_data.get('pair_age_hours',999) < 999 else "?"
    mode_icon = "🤖" if mode == "AI" else "📐"
    log_console(f"🚀 BUY: {symbol} | ${amount_usd:.2f} @ ${price:.10f} | Fee: ${entry_fee:.4f} | {mode} {token_data.get('ai_confidence')}%", "TRADE")
    log_console(f"💸 Entry fee: ${entry_fee:.4f} | Round-trip est: ${entry_fee*2:.4f} | Daily fees: ${daily_fees:.4f}", "FEE")
    send_telegram(f"""🚀 <b>BUY</b> [{mode}]
🪙 <b>{symbol}</b> ({age_str}) | ${amount_usd:.2f}
Entry: ${price:.10f} | MC: ${entry_mc:,.0f}
{mode_icon} Conf: <b>{token_data.get('ai_confidence',0)}%</b> | Risk: {token_data.get('risk_level','?')} | {token_data.get('score',0)}/12✓
💡 {token_data.get('ai_reason','N/A')}
💸 Fee: ${entry_fee:.4f} | TP:+{TP_PERCENT}% | SL:-{SL_PERCENT}%
📅 Today: {daily_trades} trades | Gate: {_get_daily_limit()}""")
    return True

def score_str(s): return str(s)


def _close_position(addr, pos, cur_price, pnl_pct, pnl_usd, exit_val, label, reason=""):
    global balance_usd

    # Deduct exit fee from received amount
    exit_fee     = _record_trade_fees(exit_val)
    net_received = exit_val - exit_fee
    balance_usd += net_received

    entry_fee    = pos.get("entry_fee", 0)
    net_pnl      = pnl_usd - entry_fee - exit_fee  # true net after all fees

    trade_history.append({
        "symbol":   pos["symbol"],
        "pnl_usd":  pnl_usd,
        "net_pnl":  net_pnl,
        "pnl_pct":  pnl_pct,
        "result":   label,
        "time":     datetime.now(),
        "fee_usd":  round(entry_fee + exit_fee, 4),
    })
    del positions[addr]

    icons  = {"TP":"✅","SL":"❌","AI-EXIT":"🤖","TRAIL":"📉","FASTCUT":"✂️","RECOVERY":"🔄"}
    titles = {"TP":"TAKE PROFIT!","SL":"STOP LOSS","AI-EXIT":"AI EXIT",
              "TRAIL":"TRAIL STOP","FASTCUT":"FAST CUT","RECOVERY":"RECOVERY"}
    sign   = "+" if pnl_usd >= 0 else ""
    peak   = pos.get("peak_pnl_usd", 0)
    net_sign = "+" if net_pnl >= 0 else ""
    log_console(f"CLOSED [{label}]: {pos['symbol']} {pnl_pct:+.2f}% (${pnl_usd:+.2f}) Net:${net_pnl:+.2f} Fees:${entry_fee+exit_fee:.4f} | Bal: ${balance_usd:.2f}", "TRADE")
    send_telegram(f"""{icons.get(label,'⚠️')} <b>{titles.get(label,'CLOSED')}</b>
🪙 {pos['symbol']} | {sign}${abs(pnl_usd):.2f} ({sign}{pnl_pct:.1f}%)
💸 Fees: ${entry_fee+exit_fee:.4f} | Net: {net_sign}${abs(net_pnl):.4f}
{f'🏔 Peak: +${peak:.2f}' if peak > 0.3 else ''}
{f'💡 {reason}' if reason else ''}
💼 Balance: <b>${balance_usd:.2f}</b>""")


# ==================== POSITION MONITORING ====================

def check_positions():
    for addr, pos in list(positions.items()):
        try:
            resp  = requests.get(f"https://api.dexscreener.com/latest/dex/tokens/{addr}", timeout=7)
            pairs = resp.json().get("pairs", [])
            if not pairs: continue

            cur_price    = float(pairs[0]["priceUsd"])
            cur_mc       = float(pairs[0].get("fdv") or pairs[0].get("marketCap") or pos.get("entry_mc",0))
            pnl_pct      = (cur_price - pos["entry_price"]) / pos["entry_price"] * 100
            pnl_usd      = (cur_price - pos["entry_price"]) * pos["amount_tokens"]
            exit_val     = pos["amount_tokens"] * cur_price
            last_price   = pos.get("last_price", pos["entry_price"])
            last_pnl_usd = pos.get("last_pnl_usd", 0.0)
            chg_now      = ((cur_price - last_price) / last_price * 100) if last_price > 0 else 0
            mins_in_trade = int((datetime.now() - pos["entry_time"]).total_seconds() / 60)

            # Fee-adjusted PnL
            entry_fee  = pos.get("entry_fee", 0)
            exit_fee_est = exit_val * (DEX_FEE_PCT + SLIPPAGE_PCT) / 100
            net_pnl_now = pnl_usd - entry_fee - exit_fee_est

            positions[addr]["current_price"] = cur_price
            positions[addr]["current_mc"]    = cur_mc
            positions[addr]["last_price"]    = cur_price
            positions[addr]["last_pnl_usd"]  = pnl_usd
            positions[addr]["last_check_ts"] = time.time()
            if pnl_pct < positions[addr]["low_pnl"]: positions[addr]["low_pnl"] = pnl_pct
            if pnl_pct < -0.3: positions[addr]["was_in_loss"] = True
            if pnl_usd > positions[addr]["peak_pnl_usd"]:
                positions[addr]["peak_pnl_usd"] = pnl_usd
                positions[addr]["peak_price"]   = cur_price

            peak_pnl  = positions[addr]["peak_pnl_usd"]
            drop_peak = peak_pnl - pnl_usd

            log_console(
                f"Monitor {pos['symbol']} | {pnl_pct:+.2f}% (${pnl_usd:+.2f}) Net:${net_pnl_now:+.2f} | Peak:+${peak_pnl:.2f} | Δ:{chg_now:+.2f}%",
                "INFO"
            )

            # ── 0. PROFIT CRASH ──────────────────────────────────────────
            if last_pnl_usd >= 0.25 and pnl_usd < -0.05:
                reason = f"🚨 PROFIT CRASH: was +${last_pnl_usd:.2f}, now ${pnl_usd:.2f}"
                log_console(f"🚨 CRASH: {pos['symbol']} — {reason}", "TRADE")
                _close_position(addr, pos, cur_price, pnl_pct, pnl_usd, exit_val, "FASTCUT", reason); continue

            # ── 1. TRAILING STOP ─────────────────────────────────────────
            if peak_pnl >= TRAIL_TRIGGER_USD and drop_peak >= TRAIL_DROP_USD:
                reason = f"Peak +${peak_pnl:.2f} → now +${pnl_usd:.2f} (dropped ${drop_peak:.2f})"
                log_console(f"📉 TRAIL EXIT: {pos['symbol']}", "TRADE")
                _close_position(addr, pos, cur_price, pnl_pct, pnl_usd, exit_val, "TRAIL", reason); continue

            # ── 2. TAKE PROFIT ───────────────────────────────────────────
            if cur_price >= pos["tp_price"]:
                _close_position(addr, pos, cur_price, pnl_pct, pnl_usd, exit_val, "TP"); continue

            # ── 3. HARD STOP LOSS ────────────────────────────────────────
            if cur_price <= pos["sl_price"]:
                _close_position(addr, pos, cur_price, pnl_pct, pnl_usd, exit_val, "SL"); continue

            # ── 4. INSTANT FAST CUT at hard limit ────────────────────────
            if pnl_pct <= HARD_FAST_CUT_PCT:
                reason = f"Loss {pnl_pct:.2f}% ≤ {HARD_FAST_CUT_PCT}% — instant cut"
                log_console(f"✂️ FAST CUT: {pos['symbol']}", "TRADE")
                _close_position(addr, pos, cur_price, pnl_pct, pnl_usd, exit_val, "FASTCUT", reason); continue

            # ── 5. EARLY EXIT / RECOVERY ANALYSIS ───────────────────────
            if pnl_pct <= EARLY_EXIT_PCT:
                recovery_count = pos.get("recovery_checks", 0)

                # If market has turned bearish while we're in loss → cut fast
                if "BEARISH" in sol_trend.get("label","") and pnl_pct < -0.8:
                    reason = f"Bearish market + loss {pnl_pct:.2f}% — cutting"
                    log_console(f"🐻 BEARISH CUT: {pos['symbol']}", "TRADE")
                    _close_position(addr, pos, cur_price, pnl_pct, pnl_usd, exit_val, "AI-EXIT", reason); continue

                # AI recovery analysis (max 3 chances)
                if recovery_count < 3:
                    positions[addr]["recovery_checks"] = recovery_count + 1
                    rec = ask_ai_recovery(pos, cur_price, pnl_pct, pnl_usd, mins_in_trade)
                    if rec.get("hold") == "no" or rec.get("urgency") == "HIGH" or rec.get("recovery_chance") == "LOW":
                        reason = f"Recovery unlikely ({rec.get('recovery_chance','?')}) — {rec.get('reason','')}"
                        log_console(f"🧠 AI RECOVERY EXIT: {pos['symbol']} — {reason}", "TRADE")
                        _close_position(addr, pos, cur_price, pnl_pct, pnl_usd, exit_val, "AI-EXIT", reason); continue
                    else:
                        log_console(f"🔄 Recovery possible ({rec.get('recovery_chance','?')}) — holding {pos['symbol']} | {rec.get('reason','')}", "INFO")
                        continue
                else:
                    # 3 recovery checks failed to recover → hard cut
                    reason = f"3 recovery checks — no improvement at {pnl_pct:.2f}%"
                    _close_position(addr, pos, cur_price, pnl_pct, pnl_usd, exit_val, "AI-EXIT", reason); continue

            # ── 6. FAST DROP WHILE IN PROFIT ─────────────────────────────
            if pnl_usd > 0.15 and chg_now <= -1.0:
                trigger = f"In profit ${pnl_usd:.2f} but dropped {chg_now:.2f}% this tick"
                ex = ask_ai_exit(pos, cur_price, cur_mc, pnl_pct, pnl_usd, trigger)
                if ex.get("action") == "EXIT":
                    _close_position(addr, pos, cur_price, pnl_pct, pnl_usd, exit_val, "AI-EXIT", ex.get("reason","")); continue

            # ── 7. RECOVERY — was in loss, now green ─────────────────────
            elif pos.get("was_in_loss") and pnl_pct >= 0.3 and net_pnl_now > 0:
                reason = f"Recovered from {pos.get('low_pnl',0):.1f}% → +{pnl_pct:.1f}% — locking net profit"
                log_console(f"🔄 Recovery exit: {pos['symbol']} — Net: ${net_pnl_now:+.2f}", "TRADE")
                _close_position(addr, pos, cur_price, pnl_pct, pnl_usd, exit_val, "RECOVERY", reason); continue

            # ── 8. HOLD ──────────────────────────────────────────────────
            else:
                emoji = "🟢" if net_pnl_now > 0 else "🟡"
                log_console(f"Hold {emoji} {pos['symbol']} | {pnl_pct:+.2f}% Net:${net_pnl_now:+.2f}", "INFO")

        except Exception as e:
            log_console(f"Position check error {addr[:8]}: {e}", "ERROR")


# ==================== MAIN LOOP ====================

def main_loop():
    global scan_count

    log_console("="*55, "SYSTEM")
    log_console(f"BOT START | Balance: ${balance_usd:.2f} → Target: ${TARGET_BALANCE_USD:.2f}", "SYSTEM")
    log_console(f"Filters: Liq≥${MIN_LIQUIDITY:,} | Vol5m≥${MIN_5M_VOLUME:,} | FDV≥${MIN_MC:,} | BR≥{MIN_BUY_RATIO_5M}x | Confs≥{MIN_CONFIRMATIONS}/12", "SYSTEM")
    log_console(f"AI≥{MIN_AI_CONFIDENCE}% | Rules≥{MIN_RULES_CONFIDENCE}% | Age≤{NEW_COIN_MAX_AGE_HOURS}h", "SYSTEM")
    log_console(f"Fee: {DEX_FEE_PCT+SLIPPAGE_PCT:.2f}% round-trip | Trades: AI decides (no fixed limit)", "SYSTEM")
    log_console(f"Groq: {len(GROQ_KEYS)} keys | {len(GROQ_SLOTS)} slots", "SYSTEM")
    log_console("="*55, "SYSTEM")

    threading.Thread(target=command_listener, daemon=True).start()
    threading.Thread(target=continuous_market_watcher, daemon=True).start()

    send_telegram(f"""🤖 <b>AI SMART BOT STARTED</b>
💼 ${INITIAL_BALANCE_USD} → ${TARGET_BALANCE_USD}
TP:+{TP_PERCENT}% | SL:-{SL_PERCENT}% | Trail:-${TRAIL_DROP_USD}
AI:≥{MIN_AI_CONFIDENCE}% | Confs:{MIN_CONFIRMATIONS}/12
Trades: AI decides — good market→unlimited, bad→zero
Fee per round-trip: ~{DEX_FEE_PCT+SLIPPAGE_PCT:.2f}%
Groq: {len(GROQ_SLOTS)} slots | 📡 Market Watcher: ON
/status /balance /pause /help""")

    last_status_ts = time.time()
    last_seen_reset = time.time()

    while True:
        # Reset seen_tokens every 20 min to allow fresh looks
        if time.time() - last_seen_reset >= 1200:
            seen_tokens.clear()
            last_seen_reset = time.time()
            log_console("seen_tokens reset", "SYSTEM")

        if balance_usd >= TARGET_BALANCE_USD:
            log_console(f"🏆 TARGET REACHED! ${balance_usd:.2f}", "SYSTEM")
            send_telegram(f"🏆 <b>TARGET REACHED!</b> ${balance_usd:.2f}")

        if positions:
            check_positions()

        scan_count += 1
        _check_daily_reset()
        market_score = market_watch.get("market_score", 50)
        mq           = _market_quality()

        log_console(
            f"── Scan #{scan_count} | ${balance_usd:.2f} | Pos:{len(positions)}/{MAX_POSITIONS} | "
            f"{ai_mode} | Trades:{daily_trades} | Score:{market_score}% | Gate:{mq} | Paused:{bot_paused}",
            "SYSTEM"
        )

        can_trade = (
            not bot_paused
            and len(positions) < MAX_POSITIONS
            and balance_usd >= MIN_TRADE_USD
            and _can_trade_today()
        )

        if can_trade:
            trend = get_sol_market_trend()
            trend_label = trend.get("label", "UNKNOWN")
            pairs = get_dexscreener_pairs()
            log_console(f"Scanning {len(pairs)} pairs | {trend_label} | Score:{market_score}% | Gate:{mq}", "INFO")
            for pair in pairs:
                if len(positions) >= MAX_POSITIONS or bot_paused or not _can_trade_today():
                    break
                token_data = analyze_pair(pair)
                if token_data and token_data["address"] not in positions:
                    simulate_buy(token_data)
                    break
        else:
            if bot_paused:
                why = "paused"
            elif len(positions) >= MAX_POSITIONS:
                why = "position open"
            elif not _can_trade_today():
                why = f"market BLOCKED (Score:{market_score}%) — AI says no trades today"
            else:
                why = "low balance"
            log_console(f"Skip scan — {why}", "INFO")

        # Auto status every 30 min
        if time.time() - last_status_ts >= 1800:
            wins   = [t for t in trade_history if t["result"] == "TP"]
            losses = [t for t in trade_history if t["result"] in ("SL","FASTCUT","AI-EXIT","TRAIL")]
            pnl    = sum(t["pnl_usd"] for t in trade_history)
            send_telegram(
                f"📊 Auto Status | ${balance_usd:.2f} | PnL:${pnl:+.2f} | "
                f"Net:${pnl-total_fees_paid:+.2f} | Fees:${total_fees_paid:.4f} | "
                f"W:{len(wins)} L:{len(losses)} | {ai_mode}"
            )
            last_status_ts = time.time()

        # Rate limit sleep handling
        rl_wait = _dex_rate_limited_until - time.time()
        if rl_wait > 0:
            sleep_sec = min(rl_wait, 60)
            log_console(f"⏳ Rate-limited — waiting {sleep_sec:.0f}s", "WARN")
            time.sleep(sleep_sec)
        else:
            time.sleep(CHECK_INTERVAL)


if __name__ == "__main__":
    threading.Thread(target=run_web, daemon=True).start()
    log_console(f"Web dashboard on port {PORT}", "SYSTEM")
    main_loop()
