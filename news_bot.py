"""
NEWS + MARKET-MOVER SIGNAL BOT (multi-coin, signals only)

Watches crypto news feeds + live price/volume/derivatives data for a list of
coins. When a news catalyst AND a real price/volume reaction line up, it sends
a LONG/SHORT signal to Telegram with entry, stop loss, TP1, TP2 and a
suggested size. It NEVER places orders.
"""

import os
import re
import json
import time
import hashlib
import traceback
import xml.etree.ElementTree as ET
from datetime import datetime, timezone
from email.utils import parsedate_to_datetime
from urllib.parse import quote_plus

import ccxt
import numpy as np
import pandas as pd
import requests


# ============================================================
# CONFIGURATION
# ============================================================

TOKEN = os.environ.get("TELEGRAM_TOKEN")
CHAT_ID = os.environ.get("TELEGRAM_CHAT_ID")
STATE_FILE = os.environ.get("STATE_FILE", "news_state.json")

# Coins to watch. "names" are matched case-insensitively in headlines,
# the ticker itself is matched only when written in CAPITALS.
COINS = {
    "BTC": {"names": ["bitcoin"], "query": "Bitcoin"},
    "ETH": {"names": ["ethereum", "ether"], "query": "Ethereum"},
    "SOL": {"names": ["solana"], "query": "Solana"},
    "BNB": {"names": ["bnb chain", "binance coin"], "query": "BNB"},
    "XRP": {"names": ["ripple"], "query": "XRP Ripple"},
    "DOGE": {"names": ["dogecoin"], "query": "Dogecoin"},
    "ADA": {"names": ["cardano"], "query": "Cardano"},
    "AVAX": {"names": ["avalanche"], "query": "Avalanche AVAX"},
    "LINK": {"names": ["chainlink"], "query": "Chainlink"},
    "TON": {"names": ["toncoin"], "query": "Toncoin"},
    "SUI": {"names": ["sui network"], "query": "Sui SUI"},
    "PEPE": {"names": ["pepe coin"], "query": "Pepe coin"},
}

TF = "5m"
POLL = 45                          # seconds between market scans
RUN_SECONDS = 345 * 60             # fits inside a 6h GitHub Actions job

GENERAL_NEWS_INTERVAL = 180        # RSS feeds
COIN_NEWS_INTERVAL = 600           # Google News per coin
DERIV_INTERVAL = 300               # funding / open interest
FNG_INTERVAL = 1800                # fear & greed
DAILY_REPORT_INTERVAL = 24 * 3600

NEWS_MAX_AGE_MIN = 90              # ignore older headlines

# ---- Signal rules ----
MIN_SCORE = 6                      # out of ~12
MIN_SCORE_GAP = 2                  # winner must beat other side by this
MAX_ACTIVE_SIGNALS = 3
MAX_SIGNALS_PER_DAY = 12
COOLDOWN_MIN = 90                  # per coin + direction
WATCH_COOLDOWN_MIN = 30
SEND_WATCH_ALERTS = True           # high-impact news with no price reaction yet
SIGNAL_EXPIRY_HOURS = 24

BTC_BLOCK_1H = 1.5                 # % BTC move that blocks opposite alt signals
MAX_EXTENDED_1H = 8.0              # skip if already moved this much in 1h

# ---- Levels ----
MIN_STOP_PCT = 0.006
MAX_STOP_PCT = 0.04
TP1_R = 1.5
TP2_R = 3.0

# ---- Suggested size (information only) ----
ACCOUNT_SIZE = 100.0
RISK_PCT = 0.005                   # 0.5% = 0.50 USDT
LEVERAGE = 3                       # isolated; alts are volatile
MAX_MARGIN_PER_TRADE = 20.0
FEE_RATE = 0.0005

RSS_FEEDS = [
    ("CoinDesk", "https://www.coindesk.com/arc/outboundfeeds/rss/"),
    ("Cointelegraph", "https://cointelegraph.com/rss"),
    ("Decrypt", "https://decrypt.co/feed"),
    ("The Block", "https://www.theblock.co/rss.xml"),
    ("Bitcoin Magazine", "https://bitcoinmagazine.com/.rss/full/"),
]


# ============================================================
# EXCHANGE / HTTP
# ============================================================

exchange = ccxt.okx({"enableRateLimit": True, "timeout": 15000})

session = requests.Session()
session.headers.update({"User-Agent": "Mozilla/5.0 (NewsSignalBot/1.0)"})


# ============================================================
# TELEGRAM
# ============================================================

def send(msg):
    if not TOKEN or not CHAT_ID:
        print("ERROR: TELEGRAM_TOKEN or TELEGRAM_CHAT_ID is missing.")
        return False

    ok = True
    chunks = [msg[i:i + 3900] for i in range(0, len(msg), 3900)] or [""]
    for chunk in chunks:
        try:
            r = session.post(
                f"https://api.telegram.org/bot{TOKEN}/sendMessage",
                data={"chat_id": CHAT_ID, "text": chunk,
                      "disable_web_page_preview": "true"},
                timeout=15,
            )
            print("Telegram:", r.status_code)
            if not r.ok:
                print("Telegram response:", r.text[:300])
                ok = False
        except Exception:
            traceback.print_exc()
            ok = False
    return ok


# ============================================================
# HELPERS
# ============================================================

def safe_float(v, default=None):
    try:
        return float(v)
    except Exception:
        return default


def pct(new, old):
    if new is None or old in (None, 0):
        return None
    return (new - old) / old * 100


def fmt_pct(v, d=2):
    return "N/A" if v is None else f"{v:+.{d}f}%"


def fmt_price(p):
    if p is None:
        return "N/A"
    if p >= 100:
        return f"{p:,.2f}"
    if p >= 1:
        return f"{p:.4f}"
    if p >= 0.01:
        return f"{p:.5f}"
    return f"{p:.8f}"


def fmt_qty(q):
    return f"{q:,.0f}" if q >= 1000 else f"{q:.4f}"


def now_utc():
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")


def today_str():
    return datetime.now(timezone.utc).strftime("%Y-%m-%d")


def side_emoji(side):
    return "🟢" if side == "LONG" else "🔴"


# ============================================================
# STATE
# ============================================================

def default_state():
    return {
        "active": [], "closed": [], "log": [],
        "seen": {}, "cooldown": {}, "watch_cd": {},
        "counter": 0, "last_daily_report": 0,
        "day": {"date": today_str(), "count": 0, "watch": 0},
    }


def load_state():
    state = default_state()
    try:
        if os.path.exists(STATE_FILE):
            with open(STATE_FILE) as f:
                state.update(json.load(f))
            print("State loaded.")
    except Exception:
        traceback.print_exc()
    return state


def save_state(state):
    try:
        state["log"] = state["log"][-3000:]
        state["closed"] = state["closed"][-1500:]
        cutoff = time.time() - 6 * 3600
        state["seen"] = {k: v for k, v in state["seen"].items() if v > cutoff}
        tmp = STATE_FILE + ".tmp"
        with open(tmp, "w") as f:
            json.dump(state, f)
        os.replace(tmp, STATE_FILE)
    except Exception:
        traceback.print_exc()


def ensure_day(state):
    if state["day"]["date"] != today_str():
        state["day"] = {"date": today_str(), "count": 0, "watch": 0}


# ============================================================
# NEWS: SENTIMENT KEYWORDS  (regex, weight)
# ============================================================

BULLISH_RAW = [
    (r"\betf\b.*\bapprov\w+|\bapprov\w+.*\betf\b", 3),
    (r"\b(binance|coinbase|upbit|robinhood|okx|bybit)\b.*\b(list|lists|listing|adds)\b", 2.5),
    (r"\bpartnership\b|\bpartners? with\b", 1.5),
    (r"\bmainnet\b", 1),
    (r"\bupgrade\b", 1),
    (r"\badoption\b", 1),
    (r"\b(surge[sd]?|soar(s|ed)?|skyrocket\w*|jumps?|rall(y|ies|ied))\b", 1.5),
    (r"\b(record high|all-time high|new high)\b", 2),
    (r"\bbreakout\b", 1.5),
    (r"\bbuyback\b", 1.5),
    (r"\binflows?\b", 1.5),
    (r"\bbullish\b", 1),
    (r"\brate cuts?\b", 2),
    (r"\b(acquires?|buys|purchases?)\b", 1),
    (r"\bapproved?\b|\bapproves\b", 1),
]

BEARISH_RAW = [
    (r"\b(hack(ed|s)?|exploit(ed|s)?|drain(ed)?|stolen|breach(ed)?)\b", 3),
    (r"\brug ?pull\b", 3),
    (r"\bdelist(s|ed|ing)?\b", 3),
    (r"\b(sec|cftc|doj)\b.*\b(sues?|charges?|lawsuit|probe|investigat\w+)\b", 3),
    (r"\blawsuit\b|\bsues?\b|\bsued\b", 2),
    (r"\b(ban|bans|banned|banning)\b", 2),
    (r"\b(crash(es|ed)?|plunge[sd]?|plummet\w*|tumbles?|collapse[sd]?)\b", 2),
    (r"\b(dump(s|ed)?|sell-?off)\b", 1.5),
    (r"\bliquidat\w+", 1),
    (r"\boutflows?\b", 1.5),
    (r"\b(fraud|scam|ponzi)\b", 2.5),
    (r"\b(bankrupt\w*|insolven\w*)\b", 3),
    (r"\b(halts?|suspends?|outage|paused)\b", 2),
    (r"\b(token )?unlocks?\b", 1),
    (r"\brate hikes?\b", 2),
    (r"\b(rejects?|rejected|denies|denied)\b", 1.5),
    (r"\barrest\w*", 2),
    (r"\bbearish\b", 1),
    (r"\btariffs?\b", 1),
]

BULLISH = [(re.compile(p, re.I), w) for p, w in BULLISH_RAW]
BEARISH = [(re.compile(p, re.I), w) for p, w in BEARISH_RAW]

MACRO = re.compile(
    r"\b(fed|federal reserve|fomc|cpi|inflation|interest rates?|rate (cut|hike)s?|"
    r"tariffs?|treasury|jobs report|powell|sec|etf|crypto regulation|stablecoin bill)\b",
    re.I,
)

COIN_PATTERNS = {}
for _sym, _info in COINS.items():
    names = "|".join(re.escape(n) for n in _info["names"])
    COIN_PATTERNS[_sym] = (
        re.compile(r"\b(" + names + r")\b", re.I),
        re.compile(r"(?<![A-Za-z])" + _sym + r"(?![A-Za-z])"),
    )


def detect_coins(title):
    found = []
    for sym, (name_re, tick_re) in COIN_PATTERNS.items():
        if name_re.search(title) or tick_re.search(title):
            found.append(sym)
    return found


def score_headline(title):
    score, hits = 0.0, []
    for rx, w in BULLISH:
        if rx.search(title):
            score += w
            hits.append(f"+{rx.pattern[:18]}")
    for rx, w in BEARISH:
        if rx.search(title):
            score -= w
            hits.append(f"-{rx.pattern[:18]}")
    return max(-5.0, min(5.0, score)), hits


# ============================================================
# NEWS: FETCHING
# ============================================================

NEWS_ITEMS = {}          # id -> item (in memory, last ~90 min)
RT = {"first_news": True, "last_general": 0, "last_coin": 0}


def fetch_rss(url, source, hint_coin=None):
    items = []
    try:
        r = session.get(url, timeout=12)
        root = ET.fromstring(r.content)
    except Exception as e:
        print(f"RSS error {source}:", str(e)[:120])
        return items

    for it in root.iter("item"):
        title = (it.findtext("title") or "").strip()
        link = (it.findtext("link") or "").strip()
        pub = it.findtext("pubDate")
        if not title or not pub:
            continue
        try:
            ts = parsedate_to_datetime(pub).timestamp()
        except Exception:
            continue

        src = source
        if source == "Google News" and " - " in title:
            title, src = title.rsplit(" - ", 1)

        coins = detect_coins(title)
        if not coins and hint_coin:
            coins = [hint_coin]
        if not coins and MACRO.search(title):
            coins = ["MARKET"]
        if not coins:
            continue

        score, hits = score_headline(title)
        items.append({
            "id": hashlib.sha1(title.lower().encode()).hexdigest()[:16],
            "title": title, "link": link, "source": src,
            "ts": ts, "coins": coins, "score": score, "hits": hits,
        })
    return items


def update_news(state):
    """Fetch feeds, keep fresh items, return NEW high-impact items."""
    now = time.time()
    fetched = []

    if now - RT["last_general"] >= GENERAL_NEWS_INTERVAL:
        for source, url in RSS_FEEDS:
            fetched += fetch_rss(url, source)
        RT["last_general"] = now

    if now - RT["last_coin"] >= COIN_NEWS_INTERVAL:
        for sym, info in COINS.items():
            q = quote_plus(f"{info['query']} crypto when:1d")
            url = f"https://news.google.com/rss/search?q={q}&hl=en-US&gl=US&ceid=US:en"
            fetched += fetch_rss(url, "Google News", hint_coin=sym)
            time.sleep(0.3)
        RT["last_coin"] = now

    new_high = []
    max_age = NEWS_MAX_AGE_MIN * 60

    for item in fetched:
        if now - item["ts"] > max_age or item["ts"] > now + 300:
            continue
        NEWS_ITEMS[item["id"]] = item

        if item["id"] not in state["seen"]:
            state["seen"][item["id"]] = now
            # first fetch of each run only fills the memory (no spam on start)
            if not RT["first_news"] and abs(item["score"]) >= 3:
                new_high.append(item)

    RT["first_news"] = False

    for k in [k for k, v in NEWS_ITEMS.items() if now - v["ts"] > max_age]:
        del NEWS_ITEMS[k]

    return new_high


def news_for(coin):
    """Time-decayed sentiment for a coin + top headlines."""
    now = time.time()
    total, used = 0.0, []

    for it in NEWS_ITEMS.values():
        if coin not in it["coins"] or it["score"] == 0:
            continue
        age = (now - it["ts"]) / 60
        decay = 1.0 if age < 30 else 0.6 if age < 60 else 0.3
        total += it["score"] * decay
        used.append(it)

    market = 0.0
    for it in NEWS_ITEMS.values():
        if "MARKET" in it["coins"]:
            age = (now - it["ts"]) / 60
            decay = 1.0 if age < 30 else 0.6 if age < 60 else 0.3
            market += it["score"] * decay
    market = max(-4.0, min(4.0, market))

    total = max(-6.0, min(6.0, total + 0.3 * market))
    used.sort(key=lambda x: abs(x["score"]), reverse=True)
    return {"score": total, "items": used[:3], "market": market}


# ============================================================
# MARKET DATA
# ============================================================

def get_df(symbol, timeframe=TF, limit=200):
    raw = exchange.fetch_ohlcv(symbol, timeframe, limit=limit)
    return pd.DataFrame(raw, columns=["time", "open", "high", "low", "close", "volume"])


def add_indicators(df):
    df = df.copy()
    df["ema_fast"] = df["close"].ewm(span=9, adjust=False).mean()
    df["ema_slow"] = df["close"].ewm(span=21, adjust=False).mean()
    df["ema_trend"] = df["close"].ewm(span=50, adjust=False).mean()

    delta = df["close"].diff()
    gain = delta.clip(lower=0).ewm(alpha=1 / 14, adjust=False).mean()
    loss = (-delta.clip(upper=0)).ewm(alpha=1 / 14, adjust=False).mean()
    df["rsi"] = 100 - 100 / (1 + gain / loss.replace(0, np.nan))

    tr = pd.concat([
        df["high"] - df["low"],
        (df["high"] - df["close"].shift()).abs(),
        (df["low"] - df["close"].shift()).abs(),
    ], axis=1).max(axis=1)
    df["atr"] = tr.ewm(alpha=1 / 14, adjust=False).mean()
    return df


def coin_metrics(df):
    if df is None or len(df) < 60:
        return None

    c, live = df.iloc[-2], df.iloc[-1]
    if pd.isna(c["atr"]) or pd.isna(c["rsi"]):
        return None

    vol_avg = df["volume"].iloc[-26:-2].mean()
    vr = float(c["volume"] / vol_avg) if vol_avg and vol_avg > 0 else None
    price = float(live["close"])

    if c["ema_fast"] > c["ema_slow"] > c["ema_trend"] and c["close"] > c["ema_slow"]:
        trend = "UP"
    elif c["ema_fast"] < c["ema_slow"] < c["ema_trend"] and c["close"] < c["ema_slow"]:
        trend = "DOWN"
    else:
        trend = "MIXED"

    return {
        "price": price,
        "ch5": pct(float(c["close"]), float(c["open"])),
        "ch15": pct(price, float(df.iloc[-5]["close"])),
        "ch1h": pct(price, float(df.iloc[-14]["close"])),
        "vr": vr,
        "rsi": float(c["rsi"]),
        "atr": float(c["atr"]),
        "trend": trend,
        "candle_up": c["close"] > c["open"],
    }


DERIV = {}
OI_HIST = {}
FNG = {"value": None, "label": None}


def update_derivs():
    for coin in COINS:
        sym = f"{coin}/USDT:USDT"
        d = {"funding": None, "oi": None, "oi_change": None}

        try:
            fr = exchange.fetch_funding_rate(sym)
            d["funding"] = safe_float(fr.get("fundingRate"))
        except Exception as e:
            print(f"Funding {coin}:", str(e)[:80])

        try:
            oi = exchange.fetch_open_interest(sym)
            val = safe_float(oi.get("openInterestValue")) or safe_float(oi.get("openInterestAmount"))
            if val:
                d["oi"] = val
                hist = OI_HIST.setdefault(coin, [])
                hist.append((time.time(), val))
                OI_HIST[coin] = [x for x in hist if time.time() - x[0] < 4200]
                old = [x for x in OI_HIST[coin] if time.time() - x[0] >= 900]
                if old:
                    d["oi_change"] = pct(val, old[0][1])
        except Exception as e:
            print(f"OI {coin}:", str(e)[:80])

        DERIV[coin] = d


def update_fng():
    try:
        r = session.get("https://api.alternative.me/fng/?limit=1", timeout=10)
        data = r.json()["data"][0]
        FNG["value"] = int(data["value"])
        FNG["label"] = data["value_classification"]
    except Exception as e:
        print("F&G error:", str(e)[:80])


# ============================================================
# SCORING
# ============================================================

def score_side(coin, m, d, news, deriv, btc_1h):
    """Score one direction (d=+1 LONG, d=-1 SHORT). Max about 12."""
    s, why = 0, []
    word = "bullish" if d == 1 else "bearish"

    ns = news["score"] * d
    news_aligned = ns >= 1.5
    if ns >= 3:
        s += 3
        why.append(f"Strong {word} news flow (score {news['score']:+.1f})")
    elif ns >= 1.5:
        s += 2
        why.append(f"{word.capitalize()} news (score {news['score']:+.1f})")

    ch15 = (m["ch15"] or 0) * d
    if ch15 >= 3:
        s += 3
        why.append(f"Explosive 15m move ({m['ch15']:+.2f}%)")
    elif ch15 >= 2:
        s += 2
        why.append(f"Strong 15m move ({m['ch15']:+.2f}%)")
    elif ch15 >= 1:
        s += 1
        why.append(f"15m move ({m['ch15']:+.2f}%)")

    vr = m["vr"] or 0
    candle_ok = (m["candle_up"] and d == 1) or ((not m["candle_up"]) and d == -1)
    if vr >= 3 and candle_ok:
        s += 2
        why.append(f"Volume spike {vr:.1f}x average")
    elif vr >= 2 and candle_ok:
        s += 1
        why.append(f"Above-average volume {vr:.1f}x")

    if (m["ch1h"] or 0) * d >= 1.5:
        s += 1
        why.append(f"1h trend agrees ({m['ch1h']:+.2f}%)")

    if (m["trend"] == "UP" and d == 1) or (m["trend"] == "DOWN" and d == -1):
        s += 1
        why.append("5m EMA structure agrees")

    rsi_side = m["rsi"] if d == 1 else 100 - m["rsi"]
    if rsi_side >= 80:
        s -= 1
        why.append("Penalty: RSI overextended (chasing risk)")

    funding = deriv.get("funding")
    if funding is not None:
        if d == 1 and funding > 0.0005:
            s -= 1
            why.append(f"Penalty: crowded longs (funding {funding * 100:+.3f}%)")
        if d == -1 and funding < -0.0005:
            s -= 1
            why.append(f"Penalty: crowded shorts (funding {funding * 100:+.3f}%)")

    oi_ch = deriv.get("oi_change")
    if oi_ch is not None and oi_ch >= 1.5 and ch15 >= 1:
        s += 1
        why.append(f"Open interest rising with price ({oi_ch:+.1f}%)")

    if coin != "BTC" and btc_1h is not None and btc_1h * d >= 0.5:
        s += 1
        why.append(f"BTC supports direction ({btc_1h:+.2f}% 1h)")

    return s, why, news_aligned


def levels(side, entry, atr, df):
    d = 1 if side == "LONG" else -1
    recent = df.iloc[-8:-1]
    swing = recent["low"].min() if d == 1 else recent["high"].max()

    dist_struct = abs(entry - swing) + 0.2 * atr
    lower = max(1.2 * atr, entry * MIN_STOP_PCT)
    upper = max(lower, min(2.5 * atr, entry * MAX_STOP_PCT))
    dist = min(max(dist_struct, lower), upper)

    return entry - d * dist, entry + d * dist * TP1_R, entry + d * dist * TP2_R


def suggest_size(entry, sl, side):
    risk = ACCOUNT_SIZE * RISK_PCT
    stop_pct = abs(entry - sl) / entry
    notional = risk / (stop_pct + 2 * FEE_RATE)
    margin = notional / LEVERAGE

    capped = margin > MAX_MARGIN_PER_TRADE
    if capped:
        margin = MAX_MARGIN_PER_TRADE
        notional = margin * LEVERAGE

    liq = entry * (1 - 1 / LEVERAGE) if side == "LONG" else entry * (1 + 1 / LEVERAGE)
    return {
        "qty": notional / entry, "notional": notional, "margin": margin,
        "max_loss": notional * (stop_pct + 2 * FEE_RATE),
        "stop_pct": stop_pct * 100, "liq": liq, "capped": capped,
    }


# ============================================================
# SIGNALS
# ============================================================

def log_event(state, coin, side, action):
    state["log"].append({"ts": time.time(), "coin": coin, "side": side, "action": action})


def evaluate_coin(state, coin, m, df, btc_1h):
    news = news_for(coin)
    deriv = DERIV.get(coin, {})

    long_s, long_w, long_news = score_side(coin, m, 1, news, deriv, btc_1h)
    short_s, short_w, short_news = score_side(coin, m, -1, news, deriv, btc_1h)

    if long_s >= MIN_SCORE and long_s >= short_s + MIN_SCORE_GAP:
        side, score, why, news_aligned, d = "LONG", long_s, long_w, long_news, 1
    elif short_s >= MIN_SCORE and short_s >= long_s + MIN_SCORE_GAP:
        side, score, why, news_aligned, d = "SHORT", short_s, short_w, short_news, -1
    else:
        return

    # ---- Gates ----
    ch15, ch1h = (m["ch15"] or 0) * d, (m["ch1h"] or 0) * d

    catalyst = news_aligned or ((m["vr"] or 0) >= 2.5 and ch15 >= 1.5)
    if not catalyst:
        return
    if ch15 < 0.5:                       # price must be reacting
        return
    if ch1h > MAX_EXTENDED_1H:           # already ran too far
        return
    if coin != "BTC" and btc_1h is not None:
        if d == 1 and btc_1h <= -BTC_BLOCK_1H:
            return
        if d == -1 and btc_1h >= BTC_BLOCK_1H:
            return

    ensure_day(state)
    if state["day"]["count"] >= MAX_SIGNALS_PER_DAY:
        return
    if len(state["active"]) >= MAX_ACTIVE_SIGNALS:
        return
    if any(a["coin"] == coin for a in state["active"]):
        return
    if time.time() < state["cooldown"].get(f"{coin}:{side}", 0):
        return

    send_signal(state, coin, side, score, why, m, df, news, deriv, btc_1h)


def send_signal(state, coin, side, score, why, m, df, news, deriv, btc_1h):
    entry = m["price"]
    sl, tp1, tp2 = levels(side, entry, m["atr"], df)
    size = suggest_size(entry, sl, side)

    dist = abs(entry - sl)
    rr1, rr2 = abs(tp1 - entry) / dist, abs(tp2 - entry) / dist

    state["counter"] += 1
    sid = state["counter"]
    state["active"].append({
        "id": sid, "coin": coin, "side": side, "entry": entry,
        "sl": sl, "tp1": tp1, "tp2": tp2, "tp1_hit": False,
        "opened_ts": time.time(), "last_checked": int(df.iloc[-1]["time"]),
    })
    state["cooldown"][f"{coin}:{side}"] = time.time() + COOLDOWN_MIN * 60
    state["day"]["count"] += 1
    log_event(state, coin, side, "SIGNAL")

    headlines = "\n".join(
        f"• {it['title'][:110]} ({it['source']})\n  {it['link']}" for it in news["items"]
    ) or "• No headline - move driven by price/volume"

    warnings = []
    if size["capped"]:
        warnings.append(f"Tight stop: size capped at {MAX_MARGIN_PER_TRADE:.0f} USDT margin (real risk < {RISK_PCT * 100:.1f}%)")
    if FNG["value"] is not None:
        if side == "LONG" and FNG["value"] >= 80:
            warnings.append(f"Extreme Greed ({FNG['value']}) - late-long risk")
        if side == "SHORT" and FNG["value"] <= 20:
            warnings.append(f"Extreme Fear ({FNG['value']}) - short-squeeze risk")
    if m["trend"] == "UP" and side == "SHORT" or m["trend"] == "DOWN" and side == "LONG":
        warnings.append("Against the 5m EMA trend (news-driven reversal attempt)")
    warnings.append("News can reverse fast. Use the stop loss.")

    funding = deriv.get("funding")
    fng_txt = f"{FNG['value']} ({FNG['label']})" if FNG["value"] is not None else "N/A"

    send(
        f"{side_emoji(side)} {side} SIGNAL - {coin}/USDT\n"
        f"News + Market Mover | Score {score}/12\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"Time: {now_utc()}\n"
        f"Signal ID: #{sid}\n\n"
        f"💰 Entry: {fmt_price(entry)}\n"
        f"🛑 Stop Loss: {fmt_price(sl)}  ({size['stop_pct']:.2f}% away)\n"
        f"🎯 TP1: {fmt_price(tp1)}  (R:R 1:{rr1:.1f})\n"
        f"🎯 TP2: {fmt_price(tp2)}  (R:R 1:{rr2:.1f})\n"
        f"↪ At TP1: take partial profit, move SL to entry\n\n"
        f"📰 CATALYST\n{headlines}\n\n"
        f"📈 MARKET\n"
        f"5m {fmt_pct(m['ch5'])} | ~15m {fmt_pct(m['ch15'])} | ~1h {fmt_pct(m['ch1h'])}\n"
        f"Volume {m['vr'] or 0:.1f}x | RSI {m['rsi']:.0f} | Trend {m['trend']}\n"
        f"Funding {fmt_pct(None if funding is None else funding * 100, 4)} | "
        f"OI {fmt_pct(deriv.get('oi_change'), 1)}\n"
        f"BTC 1h {fmt_pct(btc_1h)} | Fear&Greed {fng_txt}\n\n"
        f"📐 SUGGESTED SIZE ({ACCOUNT_SIZE:.0f} USDT account)\n"
        f"ISOLATED | {LEVERAGE}x\n"
        f"Position: {fmt_qty(size['qty'])} {coin} (≈ {size['notional']:.2f} USDT)\n"
        f"Margin: {size['margin']:.2f} USDT | Max loss at SL: {size['max_loss']:.2f} USDT\n"
        f"Approx. liquidation: {fmt_price(size['liq'])}\n\n"
        f"🧠 WHY\n" + "\n".join(f"• {w}" for w in why[:8]) + "\n\n"
        f"⚠️ " + "\n⚠️ ".join(warnings) + "\n\n"
        f"Signal only. The bot places NO orders."
    )


def send_watch_alerts(state, items, metrics):
    if not SEND_WATCH_ALERTS:
        return
    ensure_day(state)

    for it in items:
        for coin in it["coins"]:
            if coin == "MARKET" or coin not in COINS:
                continue
            key = f"{coin}"
            if time.time() < state["watch_cd"].get(key, 0):
                continue
            state["watch_cd"][key] = time.time() + WATCH_COOLDOWN_MIN * 60
            state["day"]["watch"] += 1
            log_event(state, coin, "WATCH", "WATCH")

            m = metrics.get(coin) or {}
            direction = "BULLISH" if it["score"] > 0 else "BEARISH"
            send(
                f"👀 HIGH-IMPACT NEWS - {coin} ({direction})\n"
                f"━━━━━━━━━━━━━━━━━━━━\n"
                f"{it['title'][:200]}\n"
                f"Source: {it['source']}\n{it['link']}\n\n"
                f"Impact score: {it['score']:+.1f}\n"
                f"Price now: {fmt_price(m.get('price'))} | ~15m {fmt_pct(m.get('ch15'))} | "
                f"Volume {m.get('vr') or 0:.1f}x\n\n"
                f"No trade signal yet - waiting for price/volume confirmation.\n"
                f"A signal is sent only if the market reacts."
            )


# ============================================================
# OUTCOME TRACKING (statistics only)
# ============================================================

def close_signal(state, s, reason):
    state["closed"].append({
        "id": s["id"], "coin": s["coin"], "side": s["side"],
        "reason": reason, "tp1_hit": s["tp1_hit"], "closed_ts": time.time(),
    })
    if s in state["active"]:
        state["active"].remove(s)
    if reason == "SL":
        state["cooldown"][f"{s['coin']}:{s['side']}"] = time.time() + 2 * COOLDOWN_MIN * 60

    titles = {
        "SL": "❌ STOP LOSS HIT", "TP2": "✅ TP2 HIT",
        "BE": "🔒 CLOSED AT BREAKEVEN (after TP1)", "EXPIRED": "⌛ SIGNAL EXPIRED",
    }
    send(
        f"{titles[reason]} - {s['coin']}\n"
        f"━━━━━━━━━━━━━━━━━━━━\n"
        f"#{s['id']} {s['side']} | Entry {fmt_price(s['entry'])}\n"
        f"SL {fmt_price(s['sl'])} | TP1 {fmt_price(s['tp1'])} | TP2 {fmt_price(s['tp2'])}\n"
        f"TP1 hit: {'Yes' if s['tp1_hit'] else 'No'}\n"
        f"Tracking only - no real trade."
    )


def check_active(state, dfs):
    for s in state["active"][:]:
        df = dfs.get(s["coin"])
        if df is None:
            continue

        if time.time() - s["opened_ts"] > SIGNAL_EXPIRY_HOURS * 3600:
            close_signal(state, s, "EXPIRED")
            continue

        d = 1 if s["side"] == "LONG" else -1
        closed = df.iloc[:-1]

        for _, cd in closed[closed["time"] > s["last_checked"]].iterrows():
            fav = float(cd["high"]) if d == 1 else float(cd["low"])
            adv = float(cd["low"]) if d == 1 else float(cd["high"])
            s["last_checked"] = int(cd["time"])

            sl_now = s["entry"] if s["tp1_hit"] else s["sl"]

            if adv * d <= sl_now * d:                      # SL first (conservative)
                close_signal(state, s, "BE" if s["tp1_hit"] else "SL")
                break
            if fav * d >= s["tp2"] * d:
                s["tp1_hit"] = True
                close_signal(state, s, "TP2")
                break
            if not s["tp1_hit"] and fav * d >= s["tp1"] * d:
                s["tp1_hit"] = True
                send(
                    f"🎯 TP1 HIT - {s['coin']}\n"
                    f"#{s['id']} {s['side']} | TP1 {fmt_price(s['tp1'])}\n"
                    f"Take partial profit and move SL to entry ({fmt_price(s['entry'])}).\n"
                    f"Next target TP2: {fmt_price(s['tp2'])}\n"
                    f"Tracking only - no real trade."
                )


# ============================================================
# DAILY REPORT
# ============================================================

def send_daily_report(state):
    since = time.time() - 24 * 3600
    log = [x for x in state["log"] if x["ts"] >= since]
    closed = [t for t in state["closed"] if t["closed_ts"] >= since]

    signals = [x for x in log if x["action"] == "SIGNAL"]
    watches = [x for x in log if x["action"] == "WATCH"]

    tp1 = sum(1 for t in closed if t["tp1_hit"]) + sum(1 for a in state["active"] if a["tp1_hit"])
    tp2 = sum(1 for t in closed if t["reason"] == "TP2")
    sl = sum(1 for t in closed if t["reason"] == "SL")
    be = sum(1 for t in closed if t["reason"] == "BE")
    exp = sum(1 for t in closed if t["reason"] == "EXPIRED")
    winners = sum(1 for t in closed if t["tp1_hit"])
    rate = winners / len(closed) * 100 if closed else 0.0

    lines = [
        "📈 24-HOUR NEWS-SIGNAL REPORT", "━━━━━━━━━━━━━━━━━━━━", now_utc(), "",
        f"Signals sent: {len(signals)} (LONG {sum(1 for x in signals if x['side'] == 'LONG')} / "
        f"SHORT {sum(1 for x in signals if x['side'] == 'SHORT')})",
        f"High-impact news alerts: {len(watches)}", "",
        f"TP1 hits: {tp1} | TP2 hits: {tp2}",
        f"SL hits: {sl} | Breakeven: {be} | Expired: {exp}",
        f"Still running: {len(state['active'])}",
        f"Hit rate (TP1+): {rate:.1f}% ({winners}/{len(closed)})", "",
        "By coin:",
    ]
    for coin in COINS:
        n = sum(1 for x in signals if x["coin"] == coin)
        if n:
            w = sum(1 for t in closed if t["coin"] == coin and t["tp1_hit"])
            c = sum(1 for t in closed if t["coin"] == coin)
            lines.append(f"  {coin}: {n} signals | {w}/{c} reached TP1+")
    lines += ["", "Signals only. No orders are placed."]
    send("\n".join(lines))


# ============================================================
# MAIN
# ============================================================

def main():
    state = load_state()

    send(
        "🤖 NEWS + MARKET-MOVER SIGNAL BOT STARTED\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        f"Coins: {', '.join(COINS)}\n"
        "Sources: crypto news RSS + Google News + price/volume + funding/OI\n"
        f"Suggested sizing: {ACCOUNT_SIZE:.0f} USDT, isolated, {LEVERAGE}x, risk {RISK_PCT * 100:.1f}%\n"
        f"Active signals restored: {len(state['active'])}\n"
        "❌ Signals only - no orders placed"
    )

    start = time.time()
    last_deriv = last_fng = 0

    while time.time() - start < RUN_SECONDS:
        try:
            now = time.time()

            new_high = update_news(state)

            if now - last_deriv >= DERIV_INTERVAL:
                update_derivs()
                last_deriv = now
            if now - last_fng >= FNG_INTERVAL:
                update_fng()
                last_fng = now

            metrics, dfs = {}, {}
            for coin in COINS:
                try:
                    df = add_indicators(get_df(f"{coin}/USDT"))
                    m = coin_metrics(df)
                    if m:
                        metrics[coin], dfs[coin] = m, df
                except Exception as e:
                    print(f"Market data {coin}:", str(e)[:100])

            check_active(state, dfs)
            send_watch_alerts(state, new_high, metrics)

            btc_1h = (metrics.get("BTC") or {}).get("ch1h")
            for coin, m in metrics.items():
                evaluate_coin(state, coin, m, dfs[coin], btc_1h)

            if state["last_daily_report"] == 0:
                state["last_daily_report"] = now
            elif now - state["last_daily_report"] >= DAILY_REPORT_INTERVAL:
                send_daily_report(state)
                state["last_daily_report"] = now

            save_state(state)
            print(datetime.now().strftime("%H:%M:%S"),
                  "| coins:", len(metrics),
                  "| news:", len(NEWS_ITEMS),
                  "| active:", len(state["active"]))

        except Exception:
            traceback.print_exc()

        time.sleep(POLL)

    save_state(state)
    send(
        "🛑 BOT SESSION FINISHED\n"
        f"Active signals carried over: {len(state['active'])}\n"
        "State saved. Signals only."
    )


if __name__ == "__main__":
    main()
