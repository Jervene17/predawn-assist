"""
predawn_alay.py - Predawn "Alay" wake-up chain for Telegram (multi-group).

HOW IT WORKS
------------
* Each group runs /pd_setup once. The bot posts a "Join" button; every member taps
  it and presses Start in a private chat with the bot (needed so the bot can DM).
* Monday-Saturday the bot builds a weekly Alay schedule (one Alay per day). With more
  than 6 members it favours whoever served longest ago, so the rotation carries over
  from week to week.
* At the group's wake time the bot DMs that day's Alay. When the Alay taps
  "I'm awake" the group is told, and the Alay is given a random name to call
  on Telegram. The Alay reports "awake" or "no answer" (3 attempts per person).
  A person confirmed awake is then given the next name to call, and so on,
  until everyone is awake or the group's end time passes.
* Everything is stored per chat_id, so one bot can serve many groups.
* State is kept in Google Sheets tabs (PA_*), so a restart mid-morning recovers.

SETUP (standalone)
------------------
    pip install "python-telegram-bot[job-queue]>=21" "gspread>=6" tzdata
    env vars: BOT_TOKEN, SHEET_ID, GOOGLE_CREDS_JSON   (optional: PREDAWN_TZ)
    python predawn_alay.py

SETUP (inside your existing bot)
--------------------------------
    import predawn_alay
    predawn_alay.register(application, spreadsheet)   # spreadsheet = gspread Spreadsheet
    # optional, in your shutdown hook:  predawn_alay.flush_now()

All commands are prefixed pd_ so they don't clash with existing commands.
"""

import asyncio
import html
import json
import logging
import os
import random
from collections import Counter
from datetime import date, datetime, timedelta
from zoneinfo import ZoneInfo

import gspread
from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.constants import ChatMemberStatus, ChatType, ParseMode
from telegram.error import TelegramError
from telegram.ext import (
    Application,
    ApplicationHandlerStop,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    filters,
)

log = logging.getLogger("predawn")

# --------------------------------------------------------------------------------------
# Config / constants
# --------------------------------------------------------------------------------------
DEFAULTS = {
    "wake": "03:30",        # time the Alay is messaged (group-local time)
    "end": "04:30",         # the chain stops at this time
    "tz": os.environ.get("PREDAWN_TZ", "Asia/Manila"),
    "alay_wait": 10,        # minutes the Alay has to tap "I'm awake" before a backup takes over
    "attempt_wait": 5,      # minutes a caller has to report back before an attempt counts as failed
    "max_attempts": 3,      # attempts per person before another person is assigned
    "nag_min": 2,           # minutes between reminder bursts to the Alay
    "burst_count": 10,      # pings sent per reminder burst, ~1.2s apart
    "enabled": True,
}

PRAY_TEXT = "Let's start our day with prayer"

HEADERS = {
    "PA_Groups": ["chat_id", "title", "wake", "end", "tz", "alay_wait", "attempt_wait",
                  "max_attempts", "nag_min", "burst_count", "enabled"],
    "PA_Members": ["chat_id", "user_id", "name", "username", "active", "skip_dates"],
    "PA_Schedule": ["chat_id", "date", "user_id", "name", "status"],
    "PA_State": ["chat_id", "json"],
    "PA_Log": ["timestamp", "chat_id", "event", "user_id", "target_id", "detail"],
}

S = None                      # the Store, set by register()
LOCK = asyncio.Lock()         # serialises tick() and button handlers
HANDLE_PLAIN_START = False    # True when running standalone (bot answers a bare /start)


# --------------------------------------------------------------------------------------
# Small helpers
# --------------------------------------------------------------------------------------
def esc(s):
    return html.escape(str(s))


def truthy(v):
    return str(v).strip().lower() in ("1", "true", "yes", "y")


def tzinfo(g):
    return ZoneInfo(g["tz"])


def now_local(g):
    return datetime.now(tzinfo(g))


def at_local(g, d, hhmm):
    h, m = (int(x) for x in hhmm.split(":"))
    return datetime(d.year, d.month, d.day, h, m, tzinfo=tzinfo(g))


def in_minutes(g, minutes):
    return (now_local(g) + timedelta(minutes=minutes)).isoformat()


def from_iso(s):
    return datetime.fromisoformat(s)


def week_monday(d):
    return d - timedelta(days=d.weekday())


def week_days(monday):
    """Monday..Saturday."""
    return [monday + timedelta(days=i) for i in range(6)]


def fmt_day(d):
    return d.strftime("%a %d %b")


def parse_hhmm(v):
    try:
        h, m = v.strip().split(":")
        h, m = int(h), int(m)
        if 0 <= h < 24 and 0 <= m < 60:
            return f"{h:02d}:{m:02d}"
    except (ValueError, AttributeError):
        pass
    return None


def minutes_of(hhmm):
    h, m = hhmm.split(":")
    return int(h) * 60 + int(m)


# --------------------------------------------------------------------------------------
# Store: in-memory data mirrored to Google Sheets (debounced writes)
# --------------------------------------------------------------------------------------
class Store:
    def __init__(self, spreadsheet):
        self.ss = spreadsheet
        self._ws = {}
        self.groups = {}      # chat_id -> settings dict
        self.members = []     # dicts: chat_id,user_id,name,username,active,skip(list of iso dates)
        self.schedule = []    # dicts: chat_id,date,user_id,name,status
        self.state = {}       # chat_id -> live run state (JSON-serialisable dict)
        self.dirty = set()
        self.log_rows = []

    # ---- sheets plumbing ----
    def _worksheet(self, tab):
        if tab not in self._ws:
            try:
                ws = self.ss.worksheet(tab)
            except gspread.WorksheetNotFound:
                ws = self.ss.add_worksheet(title=tab, rows=200, cols=len(HEADERS[tab]))
                ws.update(range_name="A1", values=[HEADERS[tab]], value_input_option="RAW")
            self._ws[tab] = ws
        return self._ws[tab]

    def _records(self, tab):
        return self._worksheet(tab).get_all_records(numericise_ignore=["all"])

    def load(self):
        for r in self._records("PA_Groups"):
            if not str(r.get("chat_id", "")).strip():
                continue
            g = dict(DEFAULTS)
            g["chat_id"] = int(r["chat_id"])
            g["title"] = r.get("title", "") or str(r["chat_id"])
            for k in ("wake", "end", "tz"):
                if str(r.get(k, "")).strip():
                    g[k] = str(r[k]).strip()
            for k in ("alay_wait", "attempt_wait", "max_attempts", "nag_min", "burst_count"):
                if str(r.get(k, "")).strip():
                    g[k] = int(r[k])
            g["enabled"] = truthy(r.get("enabled", "1"))
            self.groups[g["chat_id"]] = g
        for r in self._records("PA_Members"):
            if not str(r.get("user_id", "")).strip():
                continue
            self.members.append({
                "chat_id": int(r["chat_id"]), "user_id": int(r["user_id"]),
                "name": r.get("name", ""), "username": r.get("username", ""),
                "active": truthy(r.get("active", "1")),
                "skip": [x for x in str(r.get("skip_dates", "")).split(",") if x],
            })
        for r in self._records("PA_Schedule"):
            if not str(r.get("user_id", "")).strip():
                continue
            self.schedule.append({
                "chat_id": int(r["chat_id"]), "date": r["date"], "user_id": int(r["user_id"]),
                "name": r.get("name", ""), "status": r.get("status", "planned"),
            })
        for r in self._records("PA_State"):
            try:
                self.state[int(r["chat_id"])] = json.loads(r["json"])
            except (ValueError, KeyError):
                continue
        self._worksheet("PA_Log")
        log.info("Predawn: loaded %d group(s), %d member(s)", len(self.groups), len(self.members))

    def _rows(self, tab):
        if tab == "PA_Groups":
            return [[g["chat_id"], g["title"], g["wake"], g["end"], g["tz"], g["alay_wait"],
                     g["attempt_wait"], g["max_attempts"], g["nag_min"], g["burst_count"],
                     "1" if g["enabled"] else "0"]
                    for g in self.groups.values()]
        if tab == "PA_Members":
            return [[m["chat_id"], m["user_id"], m["name"], m["username"],
                     "1" if m["active"] else "0", ",".join(m["skip"])] for m in self.members]
        if tab == "PA_Schedule":
            return [[r["chat_id"], r["date"], r["user_id"], r["name"], r["status"]]
                    for r in self.schedule]
        if tab == "PA_State":
            return [[cid, json.dumps(st)] for cid, st in self.state.items()]
        return []

    def snapshot(self):
        """Called on the event loop: copy what needs writing so the slow I/O can run in a thread."""
        snap = {tab: self._rows(tab) for tab in self.dirty}
        self.dirty.clear()
        logs, self.log_rows = self.log_rows, []
        return snap, logs

    def write(self, snap, logs):
        """Blocking Sheets I/O. Returns what failed so the caller can retry it."""
        failed_tabs, failed_logs = [], []
        for tab, rows in snap.items():
            try:
                ws = self._worksheet(tab)
                ws.clear()
                ws.update(range_name="A1", values=[HEADERS[tab]] + rows, value_input_option="RAW")
            except Exception:
                log.exception("Sheets write failed for %s", tab)
                failed_tabs.append(tab)
        if logs:
            try:
                self._worksheet("PA_Log").append_rows(logs, value_input_option="RAW")
            except Exception:
                log.exception("Sheets log append failed")
                failed_logs = logs
        return failed_tabs, failed_logs

    def add_log(self, cid, event, uid="", target="", detail=""):
        self.log_rows.append([datetime.now().isoformat(timespec="seconds"), cid, event, uid, target, detail])


async def flush_job(context=None):
    if S is None:
        return
    snap, logs = S.snapshot()
    if not snap and not logs:
        return
    failed_tabs, failed_logs = await asyncio.to_thread(S.write, snap, logs)
    S.dirty.update(failed_tabs)
    S.log_rows[:0] = failed_logs


def flush_now():
    """Blocking flush - call from a shutdown hook if you like."""
    if S is None:
        return
    snap, logs = S.snapshot()
    failed_tabs, failed_logs = S.write(snap, logs)
    S.dirty.update(failed_tabs)


# --------------------------------------------------------------------------------------
# Data helpers
# --------------------------------------------------------------------------------------
def member(cid, uid):
    for m in S.members:
        if m["chat_id"] == cid and m["user_id"] == uid:
            return m
    return None


def name_of(cid, uid):
    m = member(cid, uid)
    return m["name"] if m else str(uid)


def is_skipping(m, d):
    return d.isoformat() in m["skip"]


def pool(cid, d):
    """Members who should be woken on date d."""
    return [m for m in S.members if m["chat_id"] == cid and m["active"] and not is_skipping(m, d)]


def last_served(cid, uid, before):
    ds = []
    for r in S.schedule:
        if r["chat_id"] == cid and r["user_id"] == uid and r["status"] != "missed":
            d = date.fromisoformat(r["date"])
            if d < before:
                ds.append(d)
    return max(ds) if ds else None


def set_row_status(cid, d, uid, status):
    for r in S.schedule:
        if (r["chat_id"] == cid and r["date"] == d.isoformat() and r["user_id"] == uid
                and r["status"] in ("planned", "backup", "served")):
            r["status"] = status
            S.dirty.add("PA_Schedule")
            return


# --------------------------------------------------------------------------------------
# Weekly Alay rotation
# --------------------------------------------------------------------------------------
def assign_days(cid, days, rng=random):
    """Return new schedule rows for `days` (all inside one Mon-Sat week).

    Priority = whoever served longest ago (looking at previous weeks), ties broken randomly.
    Inside the week nobody repeats until everyone has served (needed when fewer than 6
    members), and the same person is avoided on adjacent days when possible.
    """
    monday = week_monday(days[0])
    week_iso = {d.isoformat() for d in week_days(monday)}
    existing = [r for r in S.schedule
                if r["chat_id"] == cid and r["date"] in week_iso and r["status"] != "missed"]
    counts = Counter(r["user_id"] for r in existing)
    by_date = {r["date"]: r["user_id"] for r in existing}

    members = [m for m in S.members if m["chat_id"] == cid and m["active"]]
    if not members:
        return []
    rng.shuffle(members)
    last = {m["user_id"]: last_served(cid, m["user_id"], monday) for m in members}
    priority = sorted(members, key=lambda m: last[m["user_id"]] or date.min)
    rank = {m["user_id"]: i for i, m in enumerate(priority)}

    order = list(days)
    rng.shuffle(order)
    new = []
    for d in order:
        cands = [m for m in priority if not is_skipping(m, d)]
        if not cands:
            continue
        prev_u = by_date.get((d - timedelta(days=1)).isoformat())
        next_u = by_date.get((d + timedelta(days=1)).isoformat())
        best = min(cands, key=lambda m: (counts[m["user_id"]],
                                         m["user_id"] in (prev_u, next_u),
                                         rank[m["user_id"]]))
        counts[best["user_id"]] += 1
        by_date[d.isoformat()] = best["user_id"]
        new.append({"chat_id": cid, "date": d.isoformat(), "user_id": best["user_id"],
                    "name": best["name"], "status": "planned"})
    new.sort(key=lambda r: r["date"])
    return new


def fmt_schedule(cid, days):
    lines = []
    for d in days:
        rows = [r for r in S.schedule if r["chat_id"] == cid and r["date"] == d.isoformat()
                and r["status"] != "missed"]
        who = ", ".join(esc(r["name"]) for r in rows) or "-"
        lines.append(f"{fmt_day(d)} - {who}")
    return "\n".join(lines)


async def ensure_schedule(bot, cid, g, now):
    """Sunday from 18:00 prepares next week; Mon-Sat creates the current week if missing."""
    today = now.date()
    if today.weekday() == 6:
        if now.hour < 18:
            return
        monday = today + timedelta(days=1)
        days = week_days(monday)
    else:
        monday = week_monday(today)
        days = [d for d in week_days(monday) if d >= today]
    week_iso = {d.isoformat() for d in week_days(monday)}
    if any(r["chat_id"] == cid and r["date"] in week_iso for r in S.schedule):
        return
    rows = assign_days(cid, days)
    if not rows:
        return
    S.schedule.extend(rows)
    S.dirty.add("PA_Schedule")
    S.add_log(cid, "schedule_created", detail=monday.isoformat())
    await say(bot, cid, f"📅 <b>Predawn Alay schedule</b> - week of {fmt_day(monday)}\n\n"
                        f"{fmt_schedule(cid, week_days(monday))}")


def choose_alay(cid, d, exclude):
    """Returns (member, is_backup). Scheduled Alay first, otherwise whoever served longest ago."""
    ex = set(exclude)
    for r in S.schedule:
        if (r["chat_id"] == cid and r["date"] == d.isoformat() and r["status"] == "planned"
                and r["user_id"] not in ex):
            m = member(cid, r["user_id"])
            if m and m["active"] and not is_skipping(m, d):
                return m, False
    cands = [m for m in pool(cid, d) if m["user_id"] not in ex]
    if not cands:
        return None, False
    random.shuffle(cands)
    cands.sort(key=lambda m: last_served(cid, m["user_id"], d) or date.min)
    return cands[0], True


# --------------------------------------------------------------------------------------
# Telegram send helpers
# --------------------------------------------------------------------------------------
async def say(bot, cid, text, markup=None):
    try:
        return await bot.send_message(cid, text, parse_mode=ParseMode.HTML, reply_markup=markup)
    except TelegramError:
        log.exception("Could not post to group %s", cid)
        return None


async def send_dm(bot, uid, text, markup=None):
    try:
        return await bot.send_message(uid, text, parse_mode=ParseMode.HTML, reply_markup=markup)
    except TelegramError as e:
        log.warning("DM to %s failed: %s", uid, e)
        return None


async def strip_kb(bot, uid, msg_id):
    if not msg_id:
        return
    try:
        await bot.edit_message_reply_markup(chat_id=uid, message_id=msg_id, reply_markup=None)
    except TelegramError:
        pass


# --------------------------------------------------------------------------------------
# The morning run (state machine)
# --------------------------------------------------------------------------------------
def unwoken(cid, st):
    awake = {a["uid"] for a in st["awake"]}
    return [m for m in pool(cid, date.fromisoformat(st["date"])) if m["user_id"] not in awake]


def render_list(cid, st):
    g = S.groups[cid]
    d = date.fromisoformat(st["date"])
    lines = [f"🌅 <b>Predawn wake-up</b> - {fmt_day(d)}",
             f"Alay: <b>{esc(name_of(cid, st['alay_id']))}</b>", ""]
    if st["awake"]:
        lines.append("<b>Awake so far:</b>")
        for i, a in enumerate(st["awake"], 1):
            t = from_iso(a["ts"]).astimezone(tzinfo(g)).strftime("%H:%M")
            lines.append(f"{i}. {esc(name_of(cid, a['uid']))} ✅ {t}")
    else:
        lines.append("Nobody has confirmed yet.")
    rem = unwoken(cid, st)
    if rem and st["phase"] != "done":
        lines += ["", "<i>Still sleeping:</i> " + ", ".join(esc(m["name"]) for m in rem)]
    return "\n".join(lines)


async def refresh_list(bot, cid, st):
    if not st.get("list_msg_id"):
        return
    try:
        await bot.edit_message_text(render_list(cid, st), chat_id=cid, message_id=st["list_msg_id"],
                                    parse_mode=ParseMode.HTML)
    except TelegramError as e:
        if "not modified" not in str(e).lower():
            log.warning("Could not edit list message: %s", e)


def new_state(d):
    return {"date": d.isoformat(), "phase": "alay_wait", "alay_id": None, "alay_tried": [],
            "alay_msgs": [], "alay_deadline": "", "next_nag": "", "awake": [], "list_msg_id": None,
            "cur": None, "tried": {}, "stalled": [], "calls": {}, "pray": False}


async def start_run(bot, cid):
    g = S.groups[cid]
    d = now_local(g).date()
    st = new_state(d)
    S.state[cid] = st
    S.dirty.add("PA_State")
    S.add_log(cid, "run_started", detail=d.isoformat())
    if not await activate_alay(bot, cid, st, d):
        return
    msg = await say(bot, cid, render_list(cid, st))
    if msg:
        st["list_msg_id"] = msg.message_id


async def dm_alay(bot, cid, st, m, nag=False):
    g = S.groups[cid]
    if nag:
        text = (f"⏰ <b>{esc(m['name'])}</b>, still sleeping? You're today's Alay for "
                f"<b>{esc(g['title'])}</b>. Tap when you're up.")
    else:
        text = (f"🌅 <b>Good morning, {esc(m['name'])}!</b>\nYou're today's Alay for "
                f"<b>{esc(g['title'])}</b>. Tap the button once you're awake.")
    kb = InlineKeyboardMarkup([[InlineKeyboardButton(
        "✅ I'm awake", callback_data=f"pdaw:{cid}:{st['date']}")]])
    msg = await send_dm(bot, m["user_id"], text, kb)
    if msg:
        st["alay_msgs"].append([m["user_id"], msg.message_id])
    return msg is not None


BURST_GAP_SECONDS = 1.2   # spacing between pings in a reminder burst - stays under Telegram's
                          # per-chat flood limit while still landing as separate notifications


async def run_alay_burst(bot, cid, day, uid):
    """Sends a rapid-fire burst of reminder DMs to `uid` so their phone gets several
    distinct notifications in a row instead of one easy-to-miss message. Runs as its own
    background task (NOT holding the shared LOCK the whole time) so it can't stall the
    rest of the bot for the ~10+ seconds a burst takes; it grabs the lock only briefly
    for each individual send, and re-checks state before every ping so it stops
    immediately if the run has moved on or the person has already confirmed awake."""
    g = S.groups.get(cid)
    if not g:
        return
    count = max(1, g.get("burst_count", DEFAULTS["burst_count"]))
    for i in range(count):
        async with LOCK:
            st = S.state.get(cid)
            if not st or st["date"] != day or st["phase"] != "alay_wait" or st["alay_id"] != uid:
                return
            if uid in {a["uid"] for a in st["awake"]}:
                return
            m = member(cid, uid)
            if not m:
                return
            await dm_alay(bot, cid, st, m, nag=True)
            S.dirty.add("PA_State")
        if i < count - 1:
            await asyncio.sleep(BURST_GAP_SECONDS)


async def activate_alay(bot, cid, st, d, prev_name=None):
    """Pick the Alay (scheduled first, then a backup) and DM them. Loops if a DM can't be delivered.
    Once everyone in the pool has had an untaken turn, cycles back to the very first Alay assigned
    today (if they still haven't confirmed) and keeps nagging them until the run's end time."""
    g = S.groups[cid]
    while True:
        m, backup = choose_alay(cid, d, st["alay_tried"])
        cycling_back = False
        if not m:
            first_uid = st["alay_tried"][0] if st["alay_tried"] else None
            cand = member(cid, first_uid) if first_uid else None
            already_awake = first_uid in {a["uid"] for a in st["awake"]} if first_uid else True
            if not cand or not cand["active"] or is_skipping(cand, d) or already_awake:
                await finish(bot, cid, st)
                return False
            m, backup, cycling_back = cand, False, True
        if backup:
            S.schedule.append({"chat_id": cid, "date": d.isoformat(), "user_id": m["user_id"],
                               "name": m["name"], "status": "backup"})
            S.dirty.add("PA_Schedule")
        st["alay_id"] = m["user_id"]
        if m["user_id"] not in st["alay_tried"]:
            st["alay_tried"].append(m["user_id"])
        st["phase"] = "alay_wait"
        st["alay_deadline"] = in_minutes(g, g["alay_wait"])
        st["next_nag"] = in_minutes(g, g["nag_min"])
        S.dirty.add("PA_State")
        if await dm_alay(bot, cid, st, m):
            if prev_name and cycling_back:
                await say(bot, cid, f"⚠️ {esc(prev_name)} didn't respond. Back to "
                                    f"<b>{esc(m['name'])}</b> - still waiting on them.")
                await refresh_list(bot, cid, st)
            elif prev_name:
                await say(bot, cid, f"⚠️ {esc(prev_name)} didn't respond. "
                                    f"<b>{esc(m['name'])}</b> is now the Alay.")
                await refresh_list(bot, cid, st)
            return True
        set_row_status(cid, d, m["user_id"], "missed")
        S.add_log(cid, "alay_dm_failed", m["user_id"])
        await say(bot, cid, f"⚠️ I couldn't message {esc(m['name'])} privately "
                            f"(they may need to press Start on the bot). Trying someone else.")
        prev_name = None


def choose_pair(cid, st, prefer=None):
    """Return (caller_uid, target_uid) or None. `prefer` is the newly woken person."""
    rem = unwoken(cid, st)
    if not rem:
        return None
    stalled = set(st["stalled"])
    callers = [a["uid"] for a in st["awake"]
               if a["uid"] not in stalled and member(cid, a["uid"]) and member(cid, a["uid"])["active"]]
    if not callers:
        return None
    order = ([prefer] if prefer in callers else []) + sorted(
        [c for c in callers if c != prefer], key=lambda c: st["calls"].get(str(c), 0))

    def candidates(c):
        return [m for m in rem if m["user_id"] not in st["tried"].get(str(c), []) and m["user_id"] != c]

    for c in order:
        cs = candidates(c)
        if cs:
            return c, random.choice(cs)["user_id"]
    # Everybody has tried everybody who is left: start a fresh round.
    st["tried"] = {}
    c = order[0]
    cs = [m for m in rem if m["user_id"] != c]
    return (c, random.choice(cs)["user_id"]) if cs else None


async def dm_caller(bot, cid, st, note=None):
    g = S.groups[cid]
    cur = st["cur"]
    target = name_of(cid, cur["target"])
    text = ((note + "\n\n") if note else "") + (
        f"📞 <b>[{esc(g['title'])}]</b>\nPlease call <b>{esc(target)}</b> on Telegram now to wake them up.\n"
        f"Attempt {cur['attempt']} of {g['max_attempts']}")
    kb = InlineKeyboardMarkup([[
        InlineKeyboardButton(f"✅ {target[:20]} is awake",
                             callback_data=f"pdok:{cid}:{st['date']}:{cur['target']}"),
        InlineKeyboardButton("❌ No answer",
                             callback_data=f"pdno:{cid}:{st['date']}:{cur['target']}"),
    ]])
    msg = await send_dm(bot, cur["caller"], text, kb)
    if msg:
        cur["msg_id"] = msg.message_id
    return msg is not None


async def next_pair(bot, cid, st, prefer=None, note=None):
    g = S.groups[cid]
    while True:
        pair = choose_pair(cid, st, prefer)
        if not pair:
            await finish(bot, cid, st)
            return
        caller, target = pair
        st["cur"] = {"caller": caller, "target": target, "attempt": 1, "silent": 0,
                     "deadline": in_minutes(g, g["attempt_wait"]), "msg_id": None}
        st["calls"][str(caller)] = st["calls"].get(str(caller), 0) + 1
        S.dirty.add("PA_State")
        S.add_log(cid, "assigned", caller, target)
        if await dm_caller(bot, cid, st, note):
            return
        st["stalled"].append(caller)
        S.add_log(cid, "caller_dm_failed", caller)
        prefer, note = None, None


async def fail_attempt(bot, cid, st, silent):
    g = S.groups[cid]
    cur = st["cur"]
    caller, target = cur["caller"], cur["target"]
    await strip_kb(bot, caller, cur.get("msg_id"))
    cur["silent"] = cur["silent"] + 1 if silent else 0
    S.add_log(cid, "attempt_failed", caller, target, f"attempt {cur['attempt']} silent={silent}")
    S.dirty.add("PA_State")

    if silent and cur["silent"] >= g["max_attempts"]:
        st["stalled"].append(caller)
        await say(bot, cid, f"⚠️ {esc(name_of(cid, caller))} isn't responding. "
                            f"I'll hand the wake-up calls to someone else.")
        await next_pair(bot, cid, st)
        return
    if cur["attempt"] >= g["max_attempts"]:
        st["tried"].setdefault(str(caller), []).append(target)
        note = (f"{g['max_attempts']} attempts used for {esc(name_of(cid, target))}. "
                f"Here's someone else:")
        await next_pair(bot, cid, st, prefer=caller, note=note)
        return
    cur["attempt"] += 1
    cur["deadline"] = in_minutes(g, g["attempt_wait"])
    if not await dm_caller(bot, cid, st, note="Let's try again."):
        st["stalled"].append(caller)
        await next_pair(bot, cid, st)


async def finish(bot, cid, st):
    if st["phase"] == "done":
        return
    for uid, mid in st.get("alay_msgs", []):
        await strip_kb(bot, uid, mid)
    if st.get("cur"):
        await strip_kb(bot, st["cur"]["caller"], st["cur"].get("msg_id"))
    st["phase"] = "done"
    st["cur"] = None
    S.dirty.add("PA_State")
    rem = unwoken(cid, st)
    S.add_log(cid, "run_finished", detail=f"awake={len(st['awake'])} remaining={len(rem)}")
    if st.get("alay_id"):
        await refresh_list(bot, cid, st)
    if not st["awake"]:
        text = "⏰ The Predawn wake-up has ended - nobody confirmed this morning."
    elif not rem:
        text = "🎉 Everyone is awake! Have a blessed Predawn."
    else:
        text = ("⏰ Time's up. Not reached yet: " + ", ".join(esc(m["name"]) for m in rem)
                + ".\nPlease pray for them or call them personally 🙏")
    await say(bot, cid, text)


async def advance(bot, cid, st):
    g = S.groups[cid]
    now = now_local(g)
    d = date.fromisoformat(st["date"])
    if now >= at_local(g, d, g["end"]):
        await finish(bot, cid, st)
        return
    if st["phase"] == "alay_wait":
        if now >= from_iso(st["alay_deadline"]):
            prev = st["alay_id"]
            set_row_status(cid, d, prev, "missed")
            S.add_log(cid, "alay_missed", prev)
            # Deliberately NOT stripping/clearing alay_msgs here: someone who missed their
            # turn should still be able to tap their old "I'm awake" button if they wake up
            # late, so it needs to stay live.
            await activate_alay(bot, cid, st, d, prev_name=name_of(cid, prev))
        elif now >= from_iso(st["next_nag"]):
            st["next_nag"] = in_minutes(g, g["nag_min"])
            S.dirty.add("PA_State")
            # Fire the reminder burst in the background rather than awaiting it here -
            # a burst can take 10+ seconds and advance() runs under the shared LOCK
            # (via tick()), so awaiting it inline would stall every other group and
            # every button press for that long.
            asyncio.create_task(run_alay_burst(bot, cid, st["date"], st["alay_id"]))
    elif st["phase"] == "chain":
        if not unwoken(cid, st):
            await finish(bot, cid, st)
        elif st.get("cur") is None:
            await next_pair(bot, cid, st)
        elif now >= from_iso(st["cur"]["deadline"]):
            await fail_attempt(bot, cid, st, silent=True)


async def tick_group(bot, cid):
    g = S.groups[cid]
    now = now_local(g)
    today = now.date()
    await ensure_schedule(bot, cid, g, now)
    st = S.state.get(cid)
    if st and st["phase"] != "done" and st["date"] != today.isoformat():
        st["phase"] = "done"          # left over from an earlier day (e.g. bot was down)
        S.dirty.add("PA_State")
    if st and st["date"] == today.isoformat():
        if st["phase"] != "done":
            await advance(bot, cid, st)
        return
    wake, end = at_local(g, today, g["wake"]), at_local(g, today, g["end"])
    if today.weekday() <= 5 and wake <= now < end:
        await start_run(bot, cid)


async def tick(context: ContextTypes.DEFAULT_TYPE):
    if S is None:
        return
    async with LOCK:
        for cid, g in list(S.groups.items()):
            if not g["enabled"]:
                continue
            try:
                await tick_group(context.bot, cid)
            except Exception:
                log.exception("tick failed for group %s", cid)


# --------------------------------------------------------------------------------------
# Button handlers
# --------------------------------------------------------------------------------------
async def cb_alay(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    try:
        _, cid, day = q.data.split(":")
        cid = int(cid)
    except ValueError:
        await q.answer()
        return
    async with LOCK:
        st = S.state.get(cid)
        uid = q.from_user.id
        # Anyone who was ever assigned Alay duty today can still confirm, even after
        # being superseded (e.g. they were asleep and only just saw the message) - as
        # long as the run hasn't finished for the day.
        if not st or st["date"] != day or st["phase"] == "done" or uid not in st["alay_tried"]:
            await q.answer("This button is no longer active.")
            return
        if uid in {a["uid"] for a in st["awake"]}:
            await q.answer("You're already marked awake. Thank you!")
            return
        await q.answer("Thank you! 🌅")
        g = S.groups[cid]
        d = date.fromisoformat(day)
        starting_now = st["phase"] == "alay_wait"
        st["awake"].append({"uid": uid, "ts": now_local(g).isoformat()})
        set_row_status(cid, d, uid, "served")
        if starting_now:
            st["phase"] = "chain"
        S.dirty.add("PA_State")
        S.add_log(cid, "alay_awake", uid)
        # Strip only this person's own button(s); leave anyone else's alay button live in
        # case they, too, wake up late and want to confirm.
        remaining = []
        for u, mid in st["alay_msgs"]:
            if u == uid:
                await strip_kb(context.bot, u, mid)
            else:
                remaining.append([u, mid])
        st["alay_msgs"] = remaining
        try:
            await q.edit_message_text("✅ Thank you! I'll send you someone to call next.")
        except TelegramError:
            pass
        await refresh_list(context.bot, cid, st)
        if not st["pray"]:
            st["pray"] = True
            await say(context.bot, cid, f"🙏 <b>{esc(name_of(cid, uid))}</b> is up! {PRAY_TEXT}.")
        elif not starting_now:
            await say(context.bot, cid, f"🙌 <b>{esc(name_of(cid, uid))}</b> just confirmed awake too.")
        if starting_now or st.get("cur") is None:
            await next_pair(context.bot, cid, st, prefer=uid)


async def cb_result(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    try:
        tag, cid, day, target = q.data.split(":")
        cid, target = int(cid), int(target)
    except ValueError:
        await q.answer()
        return
    async with LOCK:
        st = S.state.get(cid)
        cur = st.get("cur") if st else None
        if (not st or st["date"] != day or st["phase"] != "chain" or not cur
                or cur["caller"] != q.from_user.id or cur["target"] != target):
            await q.answer("This step has already moved on.")
            return
        g = S.groups[cid]
        tname = esc(name_of(cid, target))
        if tag == "pdok":
            await q.answer("Great!")
            if target not in {a["uid"] for a in st["awake"]}:
                st["awake"].append({"uid": target, "ts": now_local(g).isoformat()})
            st["cur"] = None
            S.dirty.add("PA_State")
            S.add_log(cid, "target_awake", q.from_user.id, target)
            try:
                await q.edit_message_text(f"✅ {tname} is awake. Thank you!", parse_mode=ParseMode.HTML)
            except TelegramError:
                pass
            await refresh_list(context.bot, cid, st)
            await next_pair(context.bot, cid, st, prefer=target)
        else:
            await q.answer("Noted.")
            try:
                await q.edit_message_text(f"❌ No answer from {tname} (attempt {cur['attempt']}).",
                                          parse_mode=ParseMode.HTML)
            except TelegramError:
                pass
            await fail_attempt(context.bot, cid, st, silent=False)


# --------------------------------------------------------------------------------------
# Commands
# --------------------------------------------------------------------------------------
async def is_admin(bot, cid, uid):
    try:
        cm = await bot.get_chat_member(cid, uid)
    except TelegramError:
        return False
    return cm.status in (ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.OWNER)


async def group_only_ctx(update, context, admin=False, need_setup=True):
    """Guard for the two commands that must still be typed inside the group itself
    (/pd_setup and /pd_join). Returns chat_id or None (after replying)."""
    chat = update.effective_chat
    if chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
        await update.effective_message.reply_text("Please use this command inside your group.")
        return None
    if need_setup and chat.id not in S.groups:
        await update.effective_message.reply_text("This group isn't set up yet. An admin needs to run /pd_setup.")
        return None
    if admin and not await is_admin(context.bot, chat.id, update.effective_user.id):
        await update.effective_message.reply_text("Only group admins can do that.")
        return None
    return chat.id


async def priv_ctx(update, context, admin=False, action=None):
    """Guard for every other command, which now only work from a private chat with the
    bot. Figures out which group the command applies to from the user's membership (or
    admin status, if admin=True) and returns that chat_id - or None after replying with
    an explanation, an error, or (if the user is in more than one group) a picker."""
    chat = update.effective_chat
    if chat.type != ChatType.PRIVATE:
        await update.effective_message.reply_text(
            "Let's do that in a private chat - tap my name above, then send the command "
            "(or /pd_menu) there.")
        return None
    forced = getattr(context, "_pd_forced_cid", None)
    if forced is not None:
        return forced
    uid = update.effective_user.id
    if admin:
        cids = [cid for cid in S.groups if await is_admin(context.bot, cid, uid)]
    else:
        cids = sorted({m["chat_id"] for m in S.members if m["user_id"] == uid})
    if not cids:
        await update.effective_message.reply_text(
            "You're not an admin of any group I'm set up in." if admin else
            "You haven't joined a Predawn group yet. Ask your group admin to post the Join button.")
        return None
    if len(cids) == 1:
        return cids[0]
    if not action:
        await update.effective_message.reply_text("You're in more than one group - please use /pd_menu.")
        return None
    kb = InlineKeyboardMarkup([[InlineKeyboardButton(S.groups[c]["title"], callback_data=f"pdm:{action}:{c}")]
                               for c in cids])
    await update.effective_message.reply_text("You're in more than one group - which one?", reply_markup=kb)
    return None


async def send_join_prompt(update, context, cid):
    url = f"https://t.me/{context.bot.username}?start=join_{cid}"
    kb = InlineKeyboardMarkup([[InlineKeyboardButton("🌅 Join Predawn wake-up", url=url)]])
    await update.effective_message.reply_text(
        "Tap the button, then press <b>Start</b> in the private chat with me. "
        "That lets me message you privately in the morning. Please keep notifications on for that chat.",
        parse_mode=ParseMode.HTML, reply_markup=kb)


async def cmd_setup(update, context):
    cid = await group_only_ctx(update, context, admin=True, need_setup=False)
    if cid is None:
        return
    async with LOCK:
        if cid not in S.groups:
            g = dict(DEFAULTS)
            g["chat_id"] = cid
            S.groups[cid] = g
        S.groups[cid]["title"] = update.effective_chat.title or str(cid)
        S.dirty.add("PA_Groups")
    g = S.groups[cid]
    await update.effective_message.reply_text(
        f"✅ Predawn wake-up is set up for this group.\nWake time: {g['wake']}, end time: {g['end']} "
        f"({g['tz']}). DM me privately and use /pd_set wake HH:MM or /pd_set end HH:MM to change them.\n\n"
        f"Everyone must join below (Mon-Sat runs). From here on, manage things by messaging me "
        f"privately - this group will only show the Join button and the weekly schedule.")
    await send_join_prompt(update, context, cid)


async def cmd_join(update, context):
    cid = await group_only_ctx(update, context)
    if cid is not None:
        await send_join_prompt(update, context, cid)


HELP_TEXT = (
    "<b>In the group</b>\n"
    "/pd_setup - admin runs this once to set the group up\n"
    "/pd_join - posts the Join button\n"
    "(the weekly Alay schedule also posts here automatically)\n\n"
    "<b>Everything else - message me privately</b>\n"
    "DM me and send /pd_menu for buttons, or type any of these here:\n"
    "/pd_schedule - this week's Alay schedule\n"
    "/pd_members - who has joined\n"
    "/pd_leave - leave the wake-up rotation\n"
    "/pd_status - what's happening now\n"
    "/pd_settings - show settings\n\n"
    "<b>Admins (also DM me for these)</b>\n"
    "/pd_set wake|end HH:MM  |  tz Area/City  |  alay_wait|attempt_wait|attempts|nag|burst N\n"
    "/pd_regen - reshuffle the remaining days\n"
    "/pd_start - start today's run now (testing)\n"
    "/pd_stop - end today's run\n"
    "/pd_pause /pd_resume - switch the feature off/on"
)


async def cmd_help(update, context):
    await update.effective_message.reply_text(HELP_TEXT, parse_mode=ParseMode.HTML)


async def cmd_start(update, context):
    chat = update.effective_chat
    if chat.type != ChatType.PRIVATE:
        return
    args = context.args or []
    if not (args and args[0].startswith("join_")):
        if HANDLE_PLAIN_START:
            await show_start_menu(update, context)
        return
    try:
        cid = int(args[0][5:])
    except ValueError:
        return
    user = update.effective_user
    if cid not in S.groups:
        await update.message.reply_text("That group isn't set up for Predawn wake-ups yet.")
        raise ApplicationHandlerStop
    try:
        cm = await context.bot.get_chat_member(cid, user.id)
    except TelegramError:
        await update.message.reply_text("I couldn't verify your membership. Is the bot still in the group?")
        raise ApplicationHandlerStop
    if cm.status in (ChatMemberStatus.LEFT, ChatMemberStatus.BANNED) or (
            cm.status == ChatMemberStatus.RESTRICTED and not cm.is_member):
        await update.message.reply_text("You need to be a member of that group first.")
        raise ApplicationHandlerStop
    full = " ".join(x for x in (user.first_name, user.last_name) if x)
    async with LOCK:
        m = member(cid, user.id)
        if m:
            m.update(name=full, username=user.username or "", active=True)
        else:
            S.members.append({"chat_id": cid, "user_id": user.id, "name": full,
                              "username": user.username or "", "active": True, "skip": []})
        S.dirty.add("PA_Members")
        S.add_log(cid, "member_joined", user.id)
    g = S.groups[cid]
    await update.message.reply_text(
        f"✅ You're in the Predawn wake-up for <b>{esc(g['title'])}</b>, {esc(user.first_name)}.\n"
        f"Wake time: {g['wake']} (Mon-Sat). Please keep notifications on for this chat so I can wake you up "
        f"when you're the Alay.", parse_mode=ParseMode.HTML)
    admin = await is_admin(context.bot, cid, user.id)
    await update.message.reply_text(
        f"<b>Predawn wake-up menu</b> - {esc(g['title'])}\nTap a button below.",
        parse_mode=ParseMode.HTML, reply_markup=build_menu(admin, cid))
    raise ApplicationHandlerStop


async def show_start_menu(update, context):
    """Plain /start (no join link): if this person is already tied to a group (as a
    member or an admin), show the menu right away instead of the generic welcome text."""
    uid = update.effective_user.id
    cids = await resolve_menu_group(context.bot, uid)
    if not cids:
        await update.message.reply_text(
            "Hi! I'm the Predawn wake-up bot. Ask your group admin to run /pd_setup in the group, "
            "then tap the Join button there.\n\n" + "Commands are listed with /pd_help.")
        return
    if len(cids) > 1:
        kb = InlineKeyboardMarkup([[InlineKeyboardButton(S.groups[c]["title"], callback_data=f"pdm:menu:{c}")]
                                   for c in cids])
        await update.message.reply_text("Which group?", reply_markup=kb)
        return
    cid = cids[0]
    admin = await is_admin(context.bot, cid, uid)
    await update.message.reply_text(
        f"<b>Predawn wake-up menu</b> - {esc(S.groups[cid]['title'])}\nTap a button below.",
        parse_mode=ParseMode.HTML, reply_markup=build_menu(admin, cid))


def settings_text(g):
    return (f"<b>Predawn settings</b> - {esc(g['title'])}\n"
            f"Status: {'on' if g['enabled'] else 'paused'}\n"
            f"Wake time: {g['wake']}\nEnd time: {g['end']}\nTimezone: {g['tz']}\n"
            f"Alay has {g['alay_wait']} min to respond - a burst of {g['burst_count']} pings "
            f"every {g['nag_min']} min\n"
            f"Callers report within {g['attempt_wait']} min, {g['max_attempts']} attempts per person")


async def cmd_settings(update, context):
    cid = await priv_ctx(update, context, action="settings")
    if cid is not None:
        await update.effective_message.reply_text(settings_text(S.groups[cid]), parse_mode=ParseMode.HTML)


def apply_setting(g, key, value):
    """Returns None on success or an error string."""
    key = key.lower()
    if key in ("wake", "end"):
        v = parse_hhmm(value)
        if not v:
            return "Please use 24-hour HH:MM, e.g. 03:30."
        wake, end = (v, g["end"]) if key == "wake" else (g["wake"], v)
        if minutes_of(end) <= minutes_of(wake):
            return "The end time must be later than the wake time (same morning)."
        g[key] = v
        return None
    if key == "tz":
        try:
            ZoneInfo(value)
        except Exception:
            return "Unknown timezone. Example: Asia/Manila"
        g["tz"] = value
        return None
    fields = {"alay_wait": ("alay_wait", 1, 60), "attempt_wait": ("attempt_wait", 1, 30),
              "attempts": ("max_attempts", 1, 10), "nag": ("nag_min", 1, 10),
              "burst": ("burst_count", 1, 20)}
    if key in fields:
        field, lo, hi = fields[key]
        try:
            n = int(value)
        except ValueError:
            return "Please give a whole number."
        if not lo <= n <= hi:
            return f"Please choose a number from {lo} to {hi}."
        g[field] = n
        return None
    return "Unknown setting. Use: wake, end, tz, alay_wait, attempt_wait, attempts, nag, burst."


async def cmd_set(update, context, forced_key=None):
    cid = await priv_ctx(update, context, admin=True, action="set")
    if cid is None:
        return
    args = context.args or []
    if forced_key:
        args = [forced_key] + args
    if len(args) < 2:
        await update.effective_message.reply_text(
            "Usage: /pd_set wake 03:30  |  end 04:30  |  tz Asia/Manila  |  alay_wait 10  |  "
            "attempt_wait 5  |  attempts 3  |  nag 2  |  burst 10")
        return
    async with LOCK:
        err = apply_setting(S.groups[cid], args[0], args[1])
        if not err:
            S.dirty.add("PA_Groups")
    if err:
        await update.effective_message.reply_text("⚠️ " + err)
    else:
        await update.effective_message.reply_text("✅ Updated.\n\n" + settings_text(S.groups[cid]),
                                                  parse_mode=ParseMode.HTML)


async def cmd_setwake(update, context):
    await cmd_set(update, context, forced_key="wake")


async def cmd_setend(update, context):
    await cmd_set(update, context, forced_key="end")


async def cmd_schedule(update, context):
    cid = await priv_ctx(update, context, action="schedule")
    if cid is None:
        return
    g = S.groups[cid]
    today = now_local(g).date()
    monday = week_monday(today)
    parts = []
    for mon in (monday, monday + timedelta(days=7)):
        days = week_days(mon)
        if any(r["chat_id"] == cid and r["date"] in {d.isoformat() for d in days} for r in S.schedule):
            parts.append(f"<b>Week of {fmt_day(mon)}</b>\n{fmt_schedule(cid, days)}")
    await update.effective_message.reply_text(
        "\n\n".join(parts) or "No schedule yet - it's created automatically once members have joined.",
        parse_mode=ParseMode.HTML)


async def cmd_regen(update, context):
    cid = await priv_ctx(update, context, admin=True, action="regen")
    if cid is None:
        return
    g = S.groups[cid]
    async with LOCK:
        today = now_local(g).date()
        st = S.state.get(cid)
        first = today + timedelta(days=1) if (st and st["date"] == today.isoformat()) else today
        if first.weekday() == 6:
            first += timedelta(days=1)
        monday = week_monday(first)
        days = [d for d in week_days(monday) if d >= first]
        iso = {d.isoformat() for d in days}
        S.schedule[:] = [r for r in S.schedule
                         if not (r["chat_id"] == cid and r["date"] in iso and r["status"] == "planned")]
        rows = assign_days(cid, days)
        S.schedule.extend(rows)
        S.dirty.add("PA_Schedule")
    await update.effective_message.reply_text(
        f"🔀 Reshuffled.\n\n{fmt_schedule(cid, week_days(monday))}", parse_mode=ParseMode.HTML)


async def cmd_members(update, context):
    cid = await priv_ctx(update, context, action="members")
    if cid is None:
        return
    g = S.groups[cid]
    today = now_local(g).date()
    ms = [m for m in S.members if m["chat_id"] == cid]
    if not ms:
        await update.effective_message.reply_text("Nobody has joined yet. Use /pd_join.")
        return
    lines = []
    for m in ms:
        tag = "left" if not m["active"] else ("skipping today" if is_skipping(m, today) else "active")
        lines.append(f"• {esc(m['name'])} - {tag}")
    await update.effective_message.reply_text(
        f"<b>{len(ms)} member(s) joined</b> (only people who pressed Join appear here)\n" + "\n".join(lines),
        parse_mode=ParseMode.HTML)


async def cmd_leave(update, context):
    cid = await priv_ctx(update, context, action="leave")
    if cid is None:
        return
    async with LOCK:
        m = member(cid, update.effective_user.id)
        if m:
            m["active"] = False
            S.dirty.add("PA_Members")
    await update.effective_message.reply_text("You've left the wake-up rotation. Tap /pd_join to come back anytime.")


async def cmd_status(update, context):
    cid = await priv_ctx(update, context, action="status")
    if cid is None:
        return
    g = S.groups[cid]
    st = S.state.get(cid)
    if not g["enabled"]:
        text = "Paused."
    elif not st or st["date"] != now_local(g).date().isoformat():
        text = f"No run today yet. Wake time is {g['wake']}."
    elif st["phase"] == "done":
        text = "Today's run has finished.\n\n" + render_list(cid, st)
    elif st["phase"] == "alay_wait":
        text = f"Waiting for {esc(name_of(cid, st['alay_id']))} (Alay) to confirm."
    else:
        cur = st.get("cur")
        extra = (f"\n{esc(name_of(cid, cur['caller']))} is calling {esc(name_of(cid, cur['target']))} "
                 f"(attempt {cur['attempt']}/{g['max_attempts']})") if cur else ""
        text = render_list(cid, st) + extra
    await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML)


async def cmd_start_now(update, context):
    cid = await priv_ctx(update, context, admin=True, action="start")
    if cid is None:
        return
    async with LOCK:
        g = S.groups[cid]
        st = S.state.get(cid)
        if st and st["date"] == now_local(g).date().isoformat() and st["phase"] != "done":
            await update.effective_message.reply_text("A run is already in progress.")
            return
        if now_local(g) >= at_local(g, now_local(g).date(), g["end"]):
            await update.effective_message.reply_text(
                f"It's past today's end time ({g['end']}). Move it later with /pd_set end HH:MM first.")
            return
        await start_run(context.bot, cid)


async def cmd_stop(update, context):
    cid = await priv_ctx(update, context, admin=True, action="stop")
    if cid is None:
        return
    async with LOCK:
        st = S.state.get(cid)
        if st and st["phase"] != "done":
            await finish(context.bot, cid, st)
        else:
            await update.effective_message.reply_text("Nothing is running.")


async def _set_enabled(update, context, value, action):
    cid = await priv_ctx(update, context, admin=True, action=action)
    if cid is None:
        return
    async with LOCK:
        S.groups[cid]["enabled"] = value
        S.dirty.add("PA_Groups")
    await update.effective_message.reply_text("▶️ Predawn wake-ups are on." if value else "⏸ Predawn wake-ups are paused.")


async def cmd_pause(update, context):
    await _set_enabled(update, context, False, "pause")


async def cmd_resume(update, context):
    await _set_enabled(update, context, True, "resume")


# --------------------------------------------------------------------------------------
# Inline-keyboard menu (buttons that trigger the commands above)
# --------------------------------------------------------------------------------------
MENU_ACTIONS = {
    "menu": None,  # filled in below, once cmd_menu exists
    "schedule": cmd_schedule, "members": cmd_members,
    "leave": cmd_leave,
    "status": cmd_status, "settings": cmd_settings, "set": cmd_set,
    "regen": cmd_regen, "start": cmd_start_now,
    "stop": cmd_stop, "pause": cmd_pause, "resume": cmd_resume,
}


GUIDE_URL = "https://claude.ai/artifact/LedZSXUfVVwRUiBrCbZThg"


def _btn(label, action, cid):
    # Every button carries the resolved group id, so tapping it never has to
    # re-resolve (and possibly re-ask) which group it applies to.
    return InlineKeyboardButton(label, callback_data=f"pdm:{action}:{cid}")


def build_menu(admin, cid):
    rows = [
        [_btn("📅 Schedule", "schedule", cid), _btn("👥 Members", "members", cid)],
        [_btn("📊 Status", "status", cid), _btn("⚙️ Settings", "settings", cid)],
        [_btn("🚪 Leave", "leave", cid)],
    ]
    if admin:
        rows += [
            [_btn("🔀 Regen", "regen", cid), _btn("▶️ Start now", "start", cid)],
            [_btn("⏹ Stop", "stop", cid)],
            [_btn("⏸ Pause", "pause", cid), _btn("▶️ Resume", "resume", cid)],
        ]
    rows.append([InlineKeyboardButton("📖 Guide to the bot", url=GUIDE_URL)])
    return InlineKeyboardMarkup(rows)


async def resolve_menu_group(bot, uid):
    """Every group this person could plausibly want the menu for: groups they've
    joined as a member, plus groups they admin (even if they never personally
    joined the rotation)."""
    member_cids = {m["chat_id"] for m in S.members if m["user_id"] == uid}
    admin_cids = set()
    for cid in S.groups:
        if await is_admin(bot, cid, uid):
            admin_cids.add(cid)
    return sorted(member_cids | admin_cids)


async def cmd_menu(update, context):
    chat = update.effective_chat
    if chat.type != ChatType.PRIVATE:
        await update.effective_message.reply_text(
            "Let's do that in a private chat - tap my name above and send /pd_menu there.")
        return
    uid = update.effective_user.id
    forced = getattr(context, "_pd_forced_cid", None)
    if forced is not None:
        cids = [forced]
    else:
        cids = await resolve_menu_group(context.bot, uid)
        if not cids:
            await update.effective_message.reply_text(
                "I don't see you in any Predawn group yet. Ask your group admin for the Join button.")
            return
        if len(cids) > 1:
            kb = InlineKeyboardMarkup([[InlineKeyboardButton(S.groups[c]["title"], callback_data=f"pdm:menu:{c}")]
                                       for c in cids])
            await update.effective_message.reply_text("Which group?", reply_markup=kb)
            return
    cid = cids[0]
    admin = await is_admin(context.bot, cid, uid)
    await update.effective_message.reply_text(
        f"<b>Predawn wake-up menu</b> - {esc(S.groups[cid]['title'])}\nTap a button below.",
        parse_mode=ParseMode.HTML, reply_markup=build_menu(admin, cid))


MENU_ACTIONS["menu"] = cmd_menu


async def cb_dispatch(update, context):
    """Handles both the main menu's buttons and the 'which group?' picker buttons -
    both are just callback_data of the form pdm:<action>:<chat_id>."""
    q = update.callback_query
    try:
        _, action, cid = q.data.split(":", 2)
        cid = int(cid)
    except ValueError:
        await q.answer()
        return
    fn = MENU_ACTIONS.get(action)
    if not fn:
        await q.answer()
        return
    await q.answer()
    context._pd_forced_cid = cid
    try:
        await fn(update, context)
    finally:
        context._pd_forced_cid = None


# --------------------------------------------------------------------------------------
# Wiring
# --------------------------------------------------------------------------------------
def register(application, spreadsheet, handle_plain_start=False, handler_group=-1):
    """Attach the feature to an existing python-telegram-bot Application."""
    global S, HANDLE_PLAIN_START
    S = Store(spreadsheet)
    S.load()
    HANDLE_PLAIN_START = handle_plain_start
    add = lambda h: application.add_handler(h, group=handler_group)   # noqa: E731
    add(CommandHandler("start", cmd_start, filters=filters.ChatType.PRIVATE))
    for name, fn in [
        ("pd_setup", cmd_setup), ("pd_join", cmd_join), ("pd_help", cmd_help),
        ("pd_settings", cmd_settings), ("pd_set", cmd_set), ("pd_wake", cmd_setwake),
        ("pd_end", cmd_setend), ("pd_schedule", cmd_schedule), ("pd_regen", cmd_regen),
        ("pd_members", cmd_members),
        ("pd_leave", cmd_leave), ("pd_status", cmd_status), ("pd_start", cmd_start_now),
        ("pd_stop", cmd_stop), ("pd_pause", cmd_pause), ("pd_resume", cmd_resume),
        ("pd_menu", cmd_menu),
    ]:
        add(CommandHandler(name, fn))
    add(CallbackQueryHandler(cb_alay, pattern=r"^pdaw:"))
    add(CallbackQueryHandler(cb_result, pattern=r"^pd(ok|no):"))
    add(CallbackQueryHandler(cb_dispatch, pattern=r"^pdm:"))
    application.job_queue.run_repeating(tick, interval=30, first=10, name="predawn_tick")
    application.job_queue.run_repeating(flush_job, interval=20, first=20, name="predawn_flush")


async def _on_shutdown(app):
    flush_now()


def main():
    logging.basicConfig(format="%(asctime)s %(name)s %(levelname)s %(message)s", level=logging.INFO)
    creds = json.loads(os.environ["GOOGLE_CREDS_JSON"])
    spreadsheet = gspread.service_account_from_dict(creds).open_by_key(os.environ["SHEET_ID"])
    app = Application.builder().token(os.environ["BOT_TOKEN"]).post_shutdown(_on_shutdown).build()
    register(app, spreadsheet, handle_plain_start=True)
    app.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()