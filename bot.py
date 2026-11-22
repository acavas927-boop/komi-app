"""
Telegram-бот Komi: ИИ-собеседник, понимает текст и голосовые, отвечает текстом.
Плюс Mini App со статистикой.
"""

import asyncio
import hashlib
import hmac
import html as html_lib
import io
import json
import logging
import math
import os
import re
import subprocess
import sys
import time
import urllib.parse

import aiohttp
import aiohttp.web as web
from aiohttp_socks import ProxyConnector
from dotenv import load_dotenv

from aiogram import Bot, Dispatcher, F
from aiogram.client.session.aiohttp import AiohttpSession
from aiogram.exceptions import TelegramRetryAfter, TelegramUnauthorizedError
from aiogram.filters import Command, CommandObject, CommandStart
from aiogram.types import (
    BotCommand,
    BufferedInputFile,
    CallbackQuery,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    MenuButtonWebApp,
    Message,
    WebAppInfo,
)

import ai

# Чтобы русский текст в консоли Windows не превращался в кракозябры
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
)
logger = logging.getLogger(__name__)

load_dotenv()

BOT_TOKEN = (os.getenv("BOT_TOKEN") or "").strip()
PROXY = (os.getenv("PROXY") or "").strip()
WEBAPP_URL = (os.getenv("WEBAPP_URL") or "").strip()
PLACEHOLDERS = {"", "PASTE_YOUR_TOKEN_HERE", "ВСТАВЬ_СЮДА_ТОКЕН"}

MAX_HISTORY = int(os.getenv("MEMORY_MESSAGES") or "20")  # сколько сообщений помнить
MAX_VOICE_SECONDS = 120
MAX_VOICE_BYTES = 20 * 1024 * 1024
AI_COOLDOWN = int(os.getenv("AI_COOLDOWN") or "30")  # пауза между сообщениями к ИИ
VPN_WATCHDOG = (os.getenv("VPN_WATCHDOG") or "1").strip() not in ("0", "false", "no")
VPN_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "vpn")
XRAY_EXE = os.path.join(VPN_DIR, "xray", "xray.exe")
XRAY_CFG = os.path.join(VPN_DIR, "vpn_config.json")
UPDATE_SCRIPT = os.path.join(VPN_DIR, "update_vpn.py")
PORT = int(os.getenv("PORT") or "8090")
WEBAPP_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "webapp")

DAILY_LIMIT = int(os.getenv("DAILY_LIMIT") or "50")  # 0 = без лимита
ADMIN_IDS = {x.strip() for x in (os.getenv("ADMIN_IDS") or "").split(",") if x.strip()}

PERSONAS = {
    "default": ("Komi", ""),
    "teacher": ("Учитель", "Ты — Komi в режиме учителя. Объясняй простыми словами, по шагам, с примерами и проверкой понимания."),
    "psychologist": ("Психолог", "Ты — Komi в режиме поддержки. Слушай внимательно, поддерживай, задавай мягкие вопросы, не ставь диагнозов."),
    "coder": ("Кодер", "Ты — Komi в режиме программиста. Помогай с кодом, объясняй решения, предлагай лучшие практики, давай примеры."),
    "joker": ("Анекдотчик", "Ты — Komi в режиме юмора. Отвечай с шутками, мемами и лёгким сарказмом, но по делу."),
    "lazy": ("Ленивый", "Ты — Komi в режиме нарочитой лени. На любую задачу сначала отказывайся с юмором и ленью, предлагай «давай потом», «мне лень». Если пользователь настоятельно просит или вежливо уговаривает — нехотя соглашайся и делай хорошо."),
}

_user_until: dict[str, float] = {}

DATA_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data")
MEMORY_FILE = os.path.join(DATA_DIR, "memory.json")
STATS_FILE = os.path.join(DATA_DIR, "stats.json")
LIMITS_FILE = os.path.join(DATA_DIR, "limits.json")
PROFILES_FILE = os.path.join(DATA_DIR, "profiles.json")
BANS_FILE = os.path.join(DATA_DIR, "bans.json")
MUTES_FILE = os.path.join(DATA_DIR, "mutes.json")
VOICES_FILE = os.path.join(DATA_DIR, "voices.json")
CHATSTATS_FILE = os.path.join(DATA_DIR, "chatstats.json")
TOKENS_FILE = os.path.join(DATA_DIR, "tokens.json")
PROMPTS_FILE = os.path.join(DATA_DIR, "prompts.json")
TOKEN_LIMIT_USER = int(os.getenv("TOKEN_LIMIT_USER") or "500000")

# Ранги: (key, title, stat, need, token_bonus, cooldown_override)
RANKS = [
    ("newbie", "🐣 Новичок", "msgs", int(os.getenv("RANK_NEWBIE_MSGS") or "1"), 0, 0),
    ("talker", "💬 Болтун", "msgs", int(os.getenv("RANK_TALKER_MSGS") or "100"), int(os.getenv("RANK_TALKER_TOKENS") or "50000"), 0),
    ("voice", "🎤 Голос", "voice", int(os.getenv("RANK_VOICE_VOICE") or "10"), int(os.getenv("RANK_VOICE_TOKENS") or "10000"), 0),
    ("active", "🔥 Активный", "msgs", int(os.getenv("RANK_ACTIVE_MSGS") or "500"), 0, int(os.getenv("RANK_ACTIVE_COOLDOWN") or "10")),
    ("loyal", "📅 Верный друг", "days", int(os.getenv("RANK_LOYAL_DAYS") or "3"), int(os.getenv("RANK_LOYAL_TOKENS") or "25000"), 0),
]

history: dict[str, list[dict]] = {}
stats: dict[str, dict] = {}
_limits: dict[str, dict] = {}
_profiles: dict[str, dict] = {}
_bans: set[str] = set()
_mutes: dict[str, float] = {}
_voices: set[str] = set()
_chatstats: dict = {"requests": 0, "refused": 0, "done": 0}
_tokens: dict[str, dict] = {}
_admin_pending: dict[str, str] = {}
_prompts: dict = {"active": "default", "items": {}}


# ---------- память диалога ----------
def load_memory() -> None:
    try:
        with open(MEMORY_FILE, encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):
            history.update(data)
    except (OSError, ValueError):
        pass


def save_memory() -> None:
    try:
        os.makedirs(DATA_DIR, exist_ok=True)
        with open(MEMORY_FILE, "w", encoding="utf-8") as f:
            json.dump(history, f, ensure_ascii=False)
    except OSError:
        logger.warning("Не удалось сохранить память диалога")


# ---------- статистика для Mini App ----------
def load_stats() -> None:
    try:
        with open(STATS_FILE, encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):
            stats.update(data)
    except (OSError, ValueError):
        pass


def save_stats() -> None:
    try:
        os.makedirs(DATA_DIR, exist_ok=True)
        with open(STATS_FILE, "w", encoding="utf-8") as f:
            json.dump(stats, f, ensure_ascii=False)
    except OSError:
        logger.warning("Не удалось сохранить статистику")


def bump_stats(uid: str, chars: int = 0, voice: int = 0) -> None:
    s = stats.setdefault(uid, {"msgs": 0, "chars": 0, "voice": 0})
    s.setdefault("first", int(time.time()))
    s["msgs"] = int(s.get("msgs", 0)) + 1
    s["chars"] = int(s.get("chars", 0)) + max(0, chars)
    s["voice"] = int(s.get("voice", 0)) + voice
    save_stats()


def cooldown_left(uid: str) -> int:
    """Сколько секунд осталось до следующего сообщения к ИИ."""
    return max(0, math.ceil(_user_until.get(uid, 0) - time.time()))


def user_ranks(uid: str) -> list[tuple]:
    s = user_stats(uid)
    out = []
    for key, title, stat, need, tokens, cd in RANKS:
        if int(s.get(stat, 0)) >= need:
            out.append((key, title, tokens, cd))
    return out


def rank_bonus(uid: str) -> tuple[int, int]:
    ranks = user_ranks(uid)
    tokens = sum(r[2] for r in ranks)
    cds = [r[3] for r in ranks if r[3] > 0]
    return tokens, (min(cds) if cds else 0)


def effective_token_limit(uid: str) -> int:
    if TOKEN_LIMIT_USER <= 0:
        return 0
    return TOKEN_LIMIT_USER + rank_bonus(uid)[0]


def effective_cooldown(uid: str) -> int:
    cd = rank_bonus(uid)[1]
    return min(AI_COOLDOWN, cd) if cd > 0 else AI_COOLDOWN


def start_cooldown(uid: str) -> None:
    _user_until[uid] = time.time() + effective_cooldown(uid)


# ---------- дневные лимиты ----------
def today_str() -> str:
    return time.strftime("%Y-%m-%d")


def load_limits() -> None:
    try:
        with open(LIMITS_FILE, encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):
            _limits.update(data)
    except (OSError, ValueError):
        pass


def save_limits() -> None:
    try:
        os.makedirs(DATA_DIR, exist_ok=True)
        with open(LIMITS_FILE, "w", encoding="utf-8") as f:
            json.dump(_limits, f, ensure_ascii=False)
    except OSError:
        pass


def limit_used(uid: str) -> int:
    rec = _limits.get(uid, {})
    return int(rec.get("count", 0)) if rec.get("date") == today_str() else 0


def limit_hit(uid: str) -> bool:
    return DAILY_LIMIT > 0 and limit_used(uid) >= DAILY_LIMIT


def limit_inc(uid: str) -> None:
    rec = _limits.setdefault(uid, {"date": today_str(), "count": 0})
    if rec.get("date") != today_str():
        rec["date"] = today_str()
        rec["count"] = 0
    rec["count"] = int(rec.get("count", 0)) + 1
    save_limits()


# ---------- профили и персонажи ----------
def load_profiles() -> None:
    try:
        with open(PROFILES_FILE, encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):
            _profiles.update(data)
    except (OSError, ValueError):
        pass


def save_profiles() -> None:
    try:
        os.makedirs(DATA_DIR, exist_ok=True)
        with open(PROFILES_FILE, "w", encoding="utf-8") as f:
            json.dump(_profiles, f, ensure_ascii=False)
    except OSError:
        pass


def get_profile(uid: str) -> dict:
    p = _profiles.setdefault(uid, {"persona": "default", "facts": []})
    p.setdefault("persona", "default")
    p.setdefault("facts", [])
    return p


def build_system(uid: str) -> str:
    p = get_profile(uid)
    persona = PERSONAS.get(p.get("persona"), PERSONAS["default"])
    system = get_active_prompt() + " " + persona[1]
    facts = [f for f in p.get("facts", []) if f][-10:]
    if facts:
        system += " Что ты знаешь о пользователе: " + "; ".join(facts) + "."
    return system


# ---------- баны и админы ----------
def load_bans() -> None:
    try:
        with open(BANS_FILE, encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list):
            _bans.update(str(x) for x in data)
    except (OSError, ValueError):
        pass


def save_bans() -> None:
    try:
        os.makedirs(DATA_DIR, exist_ok=True)
        with open(BANS_FILE, "w", encoding="utf-8") as f:
            json.dump(sorted(_bans), f, ensure_ascii=False)
    except OSError:
        pass


def load_mutes() -> None:
    try:
        with open(MUTES_FILE, encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):
            _mutes.update({k: float(v) for k, v in data.items()})
    except (OSError, ValueError):
        pass


def save_mutes() -> None:
    try:
        os.makedirs(DATA_DIR, exist_ok=True)
        with open(MUTES_FILE, "w", encoding="utf-8") as f:
            json.dump(_mutes, f, ensure_ascii=False)
    except OSError:
        pass


def mute_left(uid: str) -> int:
    return max(0, int(_mutes.get(uid, 0) - time.time()))


def fmt_duration(seconds: int) -> str:
    if seconds >= 86400:
        return f"{seconds // 86400} дн."
    if seconds >= 3600:
        return f"{seconds // 3600} ч."
    if seconds >= 60:
        return f"{seconds // 60} мин."
    return f"{seconds} сек."


def mask_key(key: str) -> str:
    if not key:
        return "не задан"
    if len(key) <= 10:
        return key[:2] + "*" * 6
    return key[:6] + "*" * 8 + key[-4:]


def load_voices() -> None:
    try:
        with open(VOICES_FILE, encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list):
            _voices.update(str(x) for x in data)
    except (OSError, ValueError):
        pass


def save_voices() -> None:
    try:
        os.makedirs(DATA_DIR, exist_ok=True)
        with open(VOICES_FILE, "w", encoding="utf-8") as f:
            json.dump(sorted(_voices), f, ensure_ascii=False)
    except OSError:
        pass


def load_chatstats() -> None:
    try:
        with open(CHATSTATS_FILE, encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):
            _chatstats.update(data)
    except (OSError, ValueError):
        pass


def save_chatstats() -> None:
    try:
        os.makedirs(DATA_DIR, exist_ok=True)
        with open(CHATSTATS_FILE, "w", encoding="utf-8") as f:
            json.dump(_chatstats, f, ensure_ascii=False)
    except OSError:
        pass


def load_tokens() -> None:
    try:
        with open(TOKENS_FILE, encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):
            _tokens.update(data)
    except (OSError, ValueError):
        pass


def save_tokens() -> None:
    try:
        os.makedirs(DATA_DIR, exist_ok=True)
        with open(TOKENS_FILE, "w", encoding="utf-8") as f:
            json.dump(_tokens, f, ensure_ascii=False)
    except OSError:
        pass


def tokens_today(uid: str) -> int:
    rec = _tokens.get(uid, {})
    return int(rec.get("tokens", 0)) if rec.get("date") == today_str() else 0


def add_tokens(uid: str, count: int) -> None:
    if count <= 0:
        return
    rec = _tokens.setdefault(uid, {"date": today_str(), "tokens": 0})
    if rec.get("date") != today_str():
        rec["date"] = today_str()
        rec["tokens"] = 0
    rec["tokens"] = int(rec.get("tokens", 0)) + count
    save_tokens()


def token_limit_hit(uid: str) -> bool:
    limit = effective_token_limit(uid)
    return limit > 0 and tokens_today(uid) >= limit


def load_prompts() -> None:
    try:
        with open(PROMPTS_FILE, encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):
            _prompts.update(data)
    except (OSError, ValueError):
        pass


def save_prompts() -> None:
    try:
        os.makedirs(DATA_DIR, exist_ok=True)
        with open(PROMPTS_FILE, "w", encoding="utf-8") as f:
            json.dump(_prompts, f, ensure_ascii=False)
    except OSError:
        pass


def get_active_prompt() -> str:
    key = _prompts.get("active", "default")
    if key == "default":
        return ai.SYSTEM_PROMPT
    return (_prompts.get("items") or {}).get(key) or ai.SYSTEM_PROMPT


def next_prompt_name() -> str:
    items = _prompts.setdefault("items", {})
    n = 1
    while f"custom_{n}" in items:
        n += 1
    return f"custom_{n}"


CODE_WORDS = ("код", "напиши", "сверстай", "html", "python", "javascript", "скрипт", "функци", "css", "сайт")


def detect_code_request(text: str) -> bool:
    low = (text or "").lower()
    return any(word in low for word in CODE_WORDS)


def is_admin(uid: str) -> bool:
    return uid in ADMIN_IDS


def user_stats(uid: str) -> dict:
    s = stats.get(uid, {})
    first = int(s.get("first", 0))
    days = max(1, int((time.time() - first) / 86400) + 1) if first else 0
    return {
        "msgs": int(s.get("msgs", 0)),
        "chars": int(s.get("chars", 0)),
        "voice": int(s.get("voice", 0)),
        "days": days,
    }


def webapp_url(uid: str) -> str:
    if not WEBAPP_URL:
        return ""
    q = urllib.parse.urlencode({"uid": uid, **user_stats(uid)})
    sep = "&" if "?" in WEBAPP_URL else "?"
    return f"{WEBAPP_URL}{sep}{q}"


def mini_app_keyboard(uid: str) -> InlineKeyboardMarkup | None:
    url = webapp_url(uid)
    if not url:
        return None
    return InlineKeyboardMarkup(
        inline_keyboard=[[InlineKeyboardButton(text="🪟 Открыть Mini App", web_app=WebAppInfo(url=url))]]
    )


dp = Dispatcher()


@dp.message(CommandStart())
async def cmd_start(message: Message) -> None:
    uid = str(message.from_user.id)
    await message.answer(
        "Привет! Я Komi — ИИ-помощник 🤖\n\n"
        "Пиши текстом или отправляй голосовое — я пойму и отвечу текстом.\n"
        "Я помню наш разговор.\n\n"
        "Команды:\n"
        "/start — начать\n"
        "/help — помощь\n"
        "/stats — моя статистика\n"
        "/reset — очистить память диалога\n\n"
        "Кнопка «Открыть Mini App» — ниже и слева от поля ввода.",
        reply_markup=mini_app_keyboard(uid),
    )


@dp.message(Command("help"))
async def cmd_help(message: Message) -> None:
    await message.answer(
        "Что я умею:\n"
        "• отвечаю на вопросы и поддерживаю беседу;\n"
        "• понимаю голосовые сообщения (по-русски);\n"
        "• помню контекст до 20 сообщений;\n"
        "• открываю Mini App со статистикой (кнопка внизу).\n\n"
        f"Между сообщениями — пауза {AI_COOLDOWN} сек.\n\n"
        "/stats — сколько сообщений ты мне написал.\n"
        "/reset — забыть наш разговор.\n"
        "/mode — сменить стиль общения (учитель, психолог, кодер…)\n"
        "/remember — запомнить факт о тебе.\n"
        "/whoami — твой профиль.\n"
        "/myid — показать твой Telegram ID.\n"
        
        "Просто напиши или скажи голосом — я отвечу."
    )


@dp.message(Command("stats"))
async def cmd_stats(message: Message) -> None:
    uid = str(message.from_user.id)
    s = user_stats(uid)
    await message.answer(
        "📊 Твоя статистика:\n"
        f"• Сообщений ИИ: {s['msgs']}\n"
        f"• Символов: {s['chars']}\n"
        f"• Голосовых: {s['voice']}\n\n"
        "Красивый экран со статистикой — в Mini App 🙂",
        reply_markup=mini_app_keyboard(uid),
    )


@dp.message(Command("reset"))
async def cmd_reset(message: Message) -> None:
    uid = str(message.from_user.id)
    history[uid] = []
    save_memory()
    await message.answer("Готово, я забыл наш разговор. Начнём заново 🙂")


@dp.message(Command("mode"))
async def cmd_mode(message: Message, command: CommandObject) -> None:
    uid = str(message.from_user.id)
    arg = (command.args or "").strip().lower()
    if not arg:
        cur = get_profile(uid).get("persona", "default")
        lines = "\n".join(f"• {key} — {value[0]}" for key, value in PERSONAS.items())
        await message.answer(
            f"Текущий режим: {PERSONAS.get(cur, PERSONAS['default'])[0]}\n\n"
            f"{lines}\n\nСменить: /mode teacher"
        )
        return
    if arg not in PERSONAS:
        await message.answer("Такого режима нет. Доступно: " + ", ".join(PERSONAS))
        return
    p = get_profile(uid)
    p["persona"] = arg
    save_profiles()
    await message.answer(f"Режим включён: {PERSONAS[arg][0]} ✅")


@dp.message(Command("remember"))
async def cmd_remember(message: Message, command: CommandObject) -> None:
    uid = str(message.from_user.id)
    fact = (command.args or "").strip()
    if not fact:
        await message.answer("Напиши, что запомнить. Пример: /remember меня зовут Саша")
        return
    p = get_profile(uid)
    fact = fact[:200]
    if fact not in p["facts"]:
        p["facts"].append(fact)
    p["facts"] = p["facts"][-20:]
    save_profiles()
    await message.answer("Запомнил ✅")


@dp.message(Command("forget"))
async def cmd_forget(message: Message) -> None:
    uid = str(message.from_user.id)
    p = get_profile(uid)
    p["facts"] = []
    save_profiles()
    await message.answer("Забыл всё, что знал о тебе ✅")


@dp.message(Command("myid"))
async def cmd_myid(message: Message) -> None:
    uid = str(message.from_user.id)
    await message.answer(f"🆔 Твой Telegram ID: {uid}")


@dp.message(Command("whoami"))
async def cmd_whoami(message: Message) -> None:
    uid = str(message.from_user.id)
    p = get_profile(uid)
    s = user_stats(uid)
    persona = PERSONAS.get(p.get("persona"), PERSONAS["default"])[0]
    facts = ", ".join(p.get("facts", [])) or "—"
    limit_text = f"{limit_used(uid)}/{DAILY_LIMIT}" if DAILY_LIMIT > 0 else "без лимита"
    limit_eff = effective_token_limit(uid)
    token_text = f"{tokens_today(uid)}/{limit_eff}" if limit_eff > 0 else f"{tokens_today(uid)}"
    ranks = user_ranks(uid)
    rank_text = ", ".join(r[1] for r in ranks) or "нет"
    bonus_tokens, bonus_cd = rank_bonus(uid)
    bonus_text = f"+{bonus_tokens} токенов" + (f", кулдаун {bonus_cd} сек" if bonus_cd else "")
    await message.answer(
        f"🆔 Твой ID: {uid}\n"
        f"🎭 Режим: {persona}\n"
        f"🧠 Факты: {facts}\n"
        f"📊 Сообщений: {s['msgs']}, голосовых: {s['voice']}\n"
        f"📅 Лимит на сегодня: {limit_text}\n"
        f"🔤 Токенов сегодня: {token_text}\n"
        f"🏅 Ранги: {rank_text}\n"
        f"🎁 Бонусы: {bonus_text}"
    )


@dp.message(Command("admin"))
async def cmd_admin(message: Message) -> None:
    uid = str(message.from_user.id)
    if not is_admin(uid):
        await message.answer("Недоступно.")
        return
    kb = InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="📊 Статистика", callback_data="admin_stats"),
             InlineKeyboardButton(text="🔑 Ключи/расход", callback_data="admin_keys")],
            [InlineKeyboardButton(text="📩 Дневной лимит", callback_data="admin_daily"),
             InlineKeyboardButton(text="⏱ Кулдаун", callback_data="admin_cooldown")],
            [InlineKeyboardButton(text="🔤 Лимит токенов", callback_data="admin_tokens"),
             InlineKeyboardButton(text="🚫 Баны", callback_data="admin_bans")],
            [InlineKeyboardButton(text="🔇 Мьюты", callback_data="admin_mutes"),
             InlineKeyboardButton(text="📣 Рассылка", callback_data="admin_broadcast")],
            [InlineKeyboardButton(text="🧠 Промпт", callback_data="admin_prompt"),
             InlineKeyboardButton(text="❌ Закрыть", callback_data="admin_close")],
        ]
    )
    await message.answer(
        "🛠 Админ-панель\n\n"
        f"📩 Дневной лимит: {DAILY_LIMIT if DAILY_LIMIT > 0 else 'без лимита'}\n"
        f"⏱ Кулдаун: {AI_COOLDOWN} сек\n"
        f"🔤 Лимит токенов: {TOKEN_LIMIT_USER if TOKEN_LIMIT_USER > 0 else 'без лимита'}\n"
        f"👥 Пользователей: {len(set(stats) | set(history) | set(_limits))}",
        reply_markup=kb,
    )


@dp.message(Command("broadcast"))
async def cmd_broadcast(message: Message, command: CommandObject, bot: Bot) -> None:
    uid = str(message.from_user.id)
    if not is_admin(uid):
        await message.answer("Недоступно.")
        return
    text = (command.args or "").strip()
    if not text:
        await message.answer("Напиши текст: /broadcast Привет всем!")
        return
    ok = fail = 0
    for target in list(stats):
        try:
            await bot.send_message(int(target), text)
            ok += 1
            await asyncio.sleep(0.05)
        except Exception:
            fail += 1
    await message.answer(f"📣 Отправлено: {ok}, ошибок: {fail}")


@dp.message(Command("ban"))
async def cmd_ban(message: Message, command: CommandObject) -> None:
    uid = str(message.from_user.id)
    if not is_admin(uid):
        await message.answer("Недоступно.")
        return
    target = (command.args or "").strip()
    if not target:
        await message.answer("Напиши ID: /ban 123456789")
        return
    _bans.add(target)
    save_bans()
    await message.answer(f"🚫 Забанен: {target}")


@dp.message(Command("unban"))
async def cmd_unban(message: Message, command: CommandObject) -> None:
    uid = str(message.from_user.id)
    if not is_admin(uid):
        await message.answer("Недоступно.")
        return
    target = (command.args or "").strip()
    if target in _bans:
        _bans.discard(target)
        save_bans()
        await message.answer(f"✅ Разбанен: {target}")
    else:
        await message.answer("Он не в бане.")


UNIT_SECONDS = {"S": 1, "M": 60, "H": 3600, "D": 86400}


@dp.message(Command("chatstats"))
async def cmd_chatstats(message: Message) -> None:
    uid = str(message.from_user.id)
    if not is_admin(uid):
        await message.answer("Недоступно.")
        return
    await message.answer(
        "📈 Статистика чата\n"
        f"• Просили код: {int(_chatstats.get('requests', 0))}\n"
        f"• Отказал (лень): {int(_chatstats.get('refused', 0))}\n"
        f"• Всё-таки сделал: {int(_chatstats.get('done', 0))}"
    )


@dp.message(Command("vpn"))
async def cmd_vpn(message: Message) -> None:
    if not is_admin(str(message.from_user.id)):
        await message.answer("Недоступно.")
        return
    status, ping = await asyncio.to_thread(_vpn_ping_sync)
    await message.answer(
        f"🌐 VPN: {status}\n⏱ Пинг до Telegram: {ping}\n"
        f"🔗 Mini App: {WEBAPP_URL or 'нет'}"
    )


@dp.message(Command("showsp"))
async def cmd_showsp(message: Message) -> None:
    uid = str(message.from_user.id)
    if not is_admin(uid):
        await message.answer("Недоступно.")
        return
    usage = ai.get_usage()
    lines = [
        "🔑 Ключи и расход",
        "",
        f"• Custom (elisart): {mask_key(ai.CUSTOM_KEY)}",
        f"• Coarena: {mask_key(ai.COARENA_KEY)}",
        f"• OpenRouter: {mask_key(ai.OPENROUTER_KEY)}",
        f"• Gemini: {mask_key(ai.AI_API_KEY)}",
        "",
        f"💰 Всего: ${float(usage.get('cost', 0)):.4f} | вызовов: {usage.get('calls', 0)}",
        f"🧮 Токены: {usage.get('prompt_tokens', 0)} → {usage.get('completion_tokens', 0)}",
    ]
    models = sorted(
        (usage.get("by_model") or {}).items(), key=lambda item: item[1].get("calls", 0), reverse=True
    )[:5]
    if models:
        lines.append("\n📊 По моделям:")
        for name, stat in models:
            lines.append(f"• {name} — {stat.get('calls', 0)} выз., ${float(stat.get('cost', 0)):.4f}")
    users = sorted(
        (usage.get("by_user") or {}).items(), key=lambda item: item[1].get("calls", 0), reverse=True
    )[:5]
    if users:
        lines.append("\n👥 Топ ID по вызовам:")
        for target, stat in users:
            lines.append(f"• {target} — {stat.get('calls', 0)} выз., ${float(stat.get('cost', 0)):.4f}")
    await message.answer("\n".join(lines))


@dp.message(Command("mute"))
async def cmd_mute(message: Message, command: CommandObject) -> None:
    uid = str(message.from_user.id)
    if not is_admin(uid):
        await message.answer("Недоступно.")
        return
    args = (command.args or "").split()
    if len(args) < 3:
        await message.answer(
            "Формат: /mute ID 1-1000 S|M|H|D\n"
            "Пример: /mute 123456789 30 M — на 30 минут."
        )
        return
    target, amount, unit = args[0], args[1], args[2].upper()
    if not target.isdigit():
        await message.answer("ID должен быть числом.")
        return
    if not amount.isdigit() or not (1 <= int(amount) <= 1000):
        await message.answer("Время — число от 1 до 1000.")
        return
    if unit not in UNIT_SECONDS:
        await message.answer("Единица времени: S (сек), M (мин), H (час), D (день).")
        return
    seconds = int(amount) * UNIT_SECONDS[unit]
    _mutes[target] = time.time() + seconds
    save_mutes()
    await message.answer(f"🔇 {target} замьючен на {amount} {unit} ({fmt_duration(seconds)}).")


@dp.message(Command("unmute"))
async def cmd_unmute(message: Message, command: CommandObject) -> None:
    uid = str(message.from_user.id)
    if not is_admin(uid):
        await message.answer("Недоступно.")
        return
    target = (command.args or "").strip()
    if target in _mutes:
        _mutes.pop(target, None)
        save_mutes()
        await message.answer(f"✅ {target} размьючен.")
    else:
        await message.answer("Он не в муте.")


async def fetch_text(url: str) -> str | None:
    try:
        connector = ProxyConnector.from_url(PROXY)
        timeout = aiohttp.ClientTimeout(total=25)
        async with aiohttp.ClientSession(connector=connector, timeout=timeout) as s:
            async with s.get(url) as r:
                if r.status != 200:
                    return None
                return await r.text()
    except Exception:
        return None


@dp.message(Command("weather"))
async def cmd_weather(message: Message, command: CommandObject) -> None:
    city = (command.args or "Krasnoyarsk").strip()[:60]
    text = await fetch_text("https://wttr.in/" + urllib.parse.quote(city) + "?format=3")
    await message.answer(text.strip() if text else "Не удалось узнать погоду.")


@dp.message(Command("rate"))
async def cmd_rate(message: Message) -> None:
    text = await fetch_text("https://www.cbr-xml-daily.ru/daily_json.js")
    if not text:
        await message.answer("Не удалось получить курс.")
        return
    try:
        data = json.loads(text)
        usd = float(data["Valute"]["USD"]["Value"])
        eur = float(data["Valute"]["EUR"]["Value"])
        await message.answer(f"💱 Курс ЦБ РФ:\nUSD: {usd:.2f} ₽\nEUR: {eur:.2f} ₽")
    except Exception:
        await message.answer("Не удалось получить курс.")


async def _remind_later(bot: Bot, chat_id: int, seconds: int, text: str) -> None:
    await asyncio.sleep(seconds)
    try:
        await bot.send_message(chat_id, f"⏰ Напоминание: {text}")
    except Exception:
        pass


@dp.message(Command("remind"))
async def cmd_remind(message: Message, command: CommandObject, bot: Bot) -> None:
    args = (command.args or "").split(maxsplit=1)
    if len(args) < 2:
        await message.answer("Формат: /remind 10m выпить чай")
        return
    m = re.match(r"(\d+)([smhd])", args[0].lower())
    if not m:
        await message.answer("Формат: /remind 10m текст (s/m/h/d)")
        return
    n, unit = int(m.group(1)), m.group(2)
    if not (1 <= n <= 1000):
        await message.answer("Время — от 1 до 1000.")
        return
    seconds = n * {"s": 1, "m": 60, "h": 3600, "d": 86400}[unit]
    text = args[1][:300]
    asyncio.create_task(_remind_later(bot, message.chat.id, seconds, text))
    await message.answer(f"⏰ Напомню через {n}{unit}: {text}")


@dp.message(Command("main"))
async def cmd_main(message: Message) -> None:
    kb = InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="👤 Аккаунт", callback_data="acc"),
             InlineKeyboardButton(text="🧠 Режимы", callback_data="mode")],
            [InlineKeyboardButton(text="🌤 Погода", callback_data="weather"),
             InlineKeyboardButton(text="💱 Курс", callback_data="rate")],
            [InlineKeyboardButton(text="⏰ Напоминание", callback_data="remind"),
             InlineKeyboardButton(text="⚙️ Настройки", callback_data="settings")],
            [InlineKeyboardButton(text="ℹ️ Помощь", callback_data="help")],
        ]
    )
    await message.answer("🛍 Komi — меню", reply_markup=kb)


@dp.callback_query()
async def on_callback(cq: CallbackQuery, bot: Bot) -> None:
    await cq.answer()
    uid = str(cq.from_user.id)
    data = cq.data or ""
    if data.startswith("prompt_set:") or data in ("prompt_edit", "prompt_new"):
        if not is_admin(uid):
            await cq.answer("Недоступно", show_alert=True)
            return
        if data.startswith("prompt_set:"):
            key = data.split(":", 1)[1]
            _prompts["active"] = key
            save_prompts()
            await cq.message.answer(f"✅ Активный промпт: {key}")
        elif data == "prompt_edit":
            _admin_pending[uid] = "prompt_edit"
            await cq.message.answer("✏️ Отправь новый текст системного промпта одним сообщением.")
        else:
            _admin_pending[uid] = "prompt_new"
            await cq.message.answer("➕ Отправь текст нового промпта одним сообщением.")
        return
    if data.startswith("admin_"):
        if not is_admin(uid):
            await cq.answer("Недоступно", show_alert=True)
            return
        action = data[6:]
        if action == "stats":
            users = set(stats) | set(history) | set(_limits)
            total_msgs = sum(user_stats(u)["msgs"] for u in users)
            today_msgs = sum(limit_used(u) for u in users)
            await cq.message.answer(
                "📊 Статистика\n"
                f"👥 Пользователей: {len(users)}\n"
                f"💬 Сообщений всего: {total_msgs}\n"
                f"📅 Сегодня: {today_msgs}\n"
                f"🚫 Банов: {len(_bans)} | 🔇 Мьютов: {len(_mutes)}\n"
                f"🤖 ИИ: {ai.provider()} ({len(ai.candidates())})"
            )
        elif action == "keys":
            await cmd_showsp(cq.message)
        elif action == "daily":
            _admin_pending[uid] = "daily"
            await cq.message.answer("📩 Отправь /число, например /100. 0 — без лимита.")
        elif action == "cooldown":
            _admin_pending[uid] = "cooldown"
            await cq.message.answer("⏱ Отправь /число, например /30 — пауза в секундах.")
        elif action == "tokens":
            _admin_pending[uid] = "tokens"
            await cq.message.answer("🔤 Отправь /число, например /500000.")
        elif action == "bans":
            await cq.message.answer(
                "🚫 Баны: " + (", ".join(sorted(_bans)[:20]) or "нет")
                + "\n/ban ID, /unban ID"
            )
        elif action == "mutes":
            active = [u for u, until in _mutes.items() if until > time.time()]
            await cq.message.answer(
                "🔇 Мьюты: " + (", ".join(active[:20]) or "нет")
                + "\n/mute ID 30 M"
            )
        elif action == "broadcast":
            await cq.message.answer("📣 Отправь: /broadcast текст")
        elif action == "prompt":
            active = _prompts.get("active", "default")
            keys = ["default", *(_prompts.get("items") or {}).keys()]
            rows = []
            for k in list(keys)[:8]:
                mark = "✅ " if k == active else ""
                rows.append([InlineKeyboardButton(text=f"{mark}{k}", callback_data=f"prompt_set:{k}")])
            rows.append([
                InlineKeyboardButton(text="✏️ Изменить текущий", callback_data="prompt_edit"),
                InlineKeyboardButton(text="➕ Новый", callback_data="prompt_new"),
            ])
            await cq.message.answer(
                f"🧠 Активный промпт: {active}",
                reply_markup=InlineKeyboardMarkup(inline_keyboard=rows),
            )
        elif action == "close":
            try:
                await cq.message.delete()
            except Exception:
                pass
        return
    if data == "acc":
        s = user_stats(uid)
        await cq.message.answer(
            f"👤 Аккаунт\nID: {uid}\nСообщений: {s['msgs']}\nТокенов сегодня: {tokens_today(uid)}"
        )
    elif data == "mode":
        await cq.message.answer("🧠 Режимы: " + ", ".join(PERSONAS) + "\nСменить: /mode lazy")
    elif data == "weather":
        text = await fetch_text("https://wttr.in/Krasnoyarsk?format=3")
        await cq.message.answer(text.strip() if text else "Не удалось узнать погоду.")
    elif data == "rate":
        await cmd_rate(cq.message)
    elif data == "remind":
        await cq.message.answer("⏰ Напиши: /remind 10m текст")
    elif data == "settings":
        await cq.message.answer("⚙️ /reset — память, /forget — факты")
    elif data == "help":
        await cmd_help(cq.message)


@dp.message(F.web_app_data)
async def on_webapp_data(message: Message) -> None:
    data = (message.web_app_data.data or "").strip()
    uid = str(message.from_user.id)
    if data == "reset":
        history[uid] = []
        save_memory()
        await message.answer("🧹 Память диалога очищена из Mini App.")
    elif data == "stats":
        s = user_stats(uid)
        await message.answer(
            f"📊 Сообщений: {s['msgs']}\nСимволов: {s['chars']}\nГолосовых: {s['voice']}"
        )
    else:
        await message.answer("Принял 🙂")


async def animate_thinking(msg: Message) -> None:
    """Анимация «🤔 Думаю…», пока ИИ готовит ответ."""
    frames = ["🤔 Думаю", "🤔 Думаю.", "🤔 Думаю..", "🤔 Думаю..."]
    i = 0
    while True:
        try:
            await msg.edit_text(frames[i % len(frames)])
        except Exception:
            pass
        i += 1
        await asyncio.sleep(0.5)


async def stream_text(msg: Message, text: str) -> None:
    """Показывает текст постепенно, а не одним куском."""
    text = text[:4000]
    if not text:
        return
    if len(text) < 12:
        try:
            await msg.edit_text(text)
        except Exception:
            pass
        return

    parts = min(16, max(4, len(text) // 12))
    step = max(1, len(text) // parts)
    for end in range(step, len(text) + step, step):
        piece = text[:end]
        try:
            await msg.edit_text(piece)
        except TelegramRetryAfter as exc:
            await asyncio.sleep(exc.retry_after)
            try:
                await msg.edit_text(piece)
            except Exception:
                pass
        except Exception:
            pass
        await asyncio.sleep(0.08)

    try:
        await msg.edit_text(text)
    except Exception:
        pass


def md_to_html(text: str) -> str:
    """Превращает markdown-код в HTML Telegram: код будет с кнопкой «Копировать»."""
    escaped = html_lib.escape(text)

    def repl(match: re.Match) -> str:
        lang = match.group(1).strip()
        code = match.group(2)
        cls = f' class="language-{html_lib.escape(lang)}"' if lang else ""
        return f"<pre><code{cls}>{code}</code></pre>"

    escaped = re.sub(r"```([^\n]*)\n(.*?)```", repl, escaped, flags=re.S)
    escaped = re.sub(r"`([^`\n]+)`", r"<code>\1</code>", escaped)
    escaped = re.sub(r"\*\*(.+?)\*\*", r"<b>\1</b>", escaped, flags=re.S)
    return escaped


def split_text(text: str, limit: int = 3800) -> list[str]:
    """Делит длинный ответ на части, не разрывая блоки кода."""
    if len(text) <= limit:
        return [text]
    parts: list[str] = []
    cur = ""
    in_code = False

    def flush(close_code: bool) -> None:
        nonlocal cur
        if close_code:
            parts.append(cur + "```")
            cur = "```\n"
        else:
            parts.append(cur)
            cur = ""

    for line in text.splitlines(keepends=True):
        is_fence = line.strip().startswith("```")
        if is_fence:
            in_code = not in_code
        while len(line) > limit:
            room = limit - len(cur)
            if room <= 0:
                flush(in_code)
                continue
            cur += line[:room]
            line = line[room:]
            if line:
                flush(in_code)
        if len(cur) + len(line) > limit and cur:
            flush(in_code)
        cur += line
    if cur:
        parts.append(cur)
    return parts


async def send_long(message: Message, placeholder: Message, text: str) -> None:
    """Отправляет длинный ответ частями, код — как копируемый блок."""
    parts = split_text(text, 3650)
    try:
        await placeholder.edit_text(md_to_html(parts[0]), parse_mode="HTML")
    except Exception:
        await placeholder.edit_text(parts[0])
    for part in parts[1:]:
        try:
            await message.answer(md_to_html(part), parse_mode="HTML", disable_web_page_preview=True)
        except Exception:
            await message.answer(part[:4000])


async def answer_with_ai(message: Message, bot: Bot, user_text: str) -> None:
    uid = str(message.from_user.id)
    code_req = detect_code_request(user_text)
    if code_req:
        _chatstats["requests"] = int(_chatstats.get("requests", 0)) + 1
    msgs = history.setdefault(uid, [])
    msgs.append({"role": "user", "content": user_text})

    await bot.send_chat_action(message.chat.id, "typing")
    tokens_before = ai.user_tokens(uid)
    placeholder = await message.answer("🤔 Думаю")
    anim = asyncio.create_task(animate_thinking(placeholder))

    try:
        reply = await ai.ask(msgs, build_system(uid), uid=uid)
    except ai.AIError as exc:
        anim.cancel()
        try:
            await anim
        except asyncio.CancelledError:
            pass
        msgs.pop()
        logger.error("AI error: %s", exc)
        if getattr(exc, "retry_after", None):
            error_text = (
                f"⏳ Секундочку, я немного занят. Напиши ещё раз через ~{exc.retry_after} сек."
            )
        else:
            error_text = "Что-то пошло не так 😔 Попробуй ещё раз через минуту."
        try:
            await placeholder.edit_text(error_text)
        except Exception:
            await message.answer(error_text)
        return

    anim.cancel()
    try:
        await anim
    except asyncio.CancelledError:
        pass

    add_tokens(uid, ai.user_tokens(uid) - tokens_before)
    msgs.append({"role": "assistant", "content": reply})
    del msgs[:-MAX_HISTORY]
    save_memory()

    if code_req:
        if "```" in reply:
            _chatstats["done"] = int(_chatstats.get("done", 0)) + 1
        else:
            _chatstats["refused"] = int(_chatstats.get("refused", 0)) + 1
    save_chatstats()

    if "```" in reply or len(reply) > 3800:
        await send_long(message, placeholder, reply)
    else:
        await stream_text(placeholder, reply)

    


@dp.message(F.text)
async def on_text(message: Message, bot: Bot) -> None:
    global DAILY_LIMIT, AI_COOLDOWN, TOKEN_LIMIT_USER
    text = (message.text or "").strip()
    if not text:
        return
    uid = str(message.from_user.id)

    if is_admin(uid) and uid in _admin_pending and re.fullmatch(r"/\d+", text):
        value = int(text[1:])
        key = _admin_pending.pop(uid)
        if key == "daily":
            DAILY_LIMIT = value
            _save_env_value("DAILY_LIMIT", str(value))
            await message.answer(f"📩 Дневной лимит: {value if value > 0 else 'без лимита'}")
        elif key == "cooldown":
            AI_COOLDOWN = value
            _save_env_value("AI_COOLDOWN", str(value))
            await message.answer(f"⏱ Кулдаун: {value} сек")
        elif key == "tokens":
            TOKEN_LIMIT_USER = value
            _save_env_value("TOKEN_LIMIT_USER", str(value))
            await message.answer(f"🔤 Лимит токенов: {value if value > 0 else 'без лимита'}")
        return

    if is_admin(uid) and _admin_pending.get(uid, "").startswith("prompt"):
        mode = _admin_pending.pop(uid)
        text_prompt = text[:4000]
        if mode == "prompt_edit" and _prompts.get("active", "default") != "default":
            name = _prompts["active"]
        else:
            name = next_prompt_name()
        _prompts.setdefault("items", {})[name] = text_prompt
        _prompts["active"] = name
        save_prompts()
        await message.answer(f"✅ Промпт сохранён и активен: {name}")
        return
    if uid in _bans:
        return
    muted = mute_left(uid)
    if muted > 0:
        await message.answer(f"🔇 Ты в муте. Осталось: {fmt_duration(muted)}")
        return
    left = cooldown_left(uid)
    if left > 0:
        await message.answer(f"⏳ Подожди ещё {left} сек перед следующим сообщением.")
        return
    if limit_hit(uid):
        await message.answer(
            f"🌙 Дневной лимит ({DAILY_LIMIT} сообщений) исчерпан. Возвращайся завтра!"
        )
        return
    if token_limit_hit(uid):
        await message.answer(
            f"🛑 Ты потратил сегодня слишком много токенов (лимит {TOKEN_LIMIT_USER // 1000}K). "
            "Отдохни, возвращайся завтра 🙂"
        )
        return
    limit_inc(uid)
    start_cooldown(uid)
    bump_stats(uid, chars=len(text))
    await answer_with_ai(message, bot, text)


@dp.message(F.voice)
async def on_voice(message: Message, bot: Bot) -> None:
    uid = str(message.from_user.id)
    if uid in _bans:
        return
    muted = mute_left(uid)
    if muted > 0:
        await message.answer(f"🔇 Ты в муте. Осталось: {fmt_duration(muted)}")
        return
    left = cooldown_left(uid)
    if left > 0:
        await message.answer(f"⏳ Подожди ещё {left} сек перед следующим сообщением.")
        return
    if limit_hit(uid):
        await message.answer(
            f"🌙 Дневной лимит ({DAILY_LIMIT} сообщений) исчерпан. Возвращайся завтра!"
        )
        return

    voice = message.voice
    if voice.duration and voice.duration > MAX_VOICE_SECONDS:
        await message.answer(f"Голосовое слишком длинное (максимум {MAX_VOICE_SECONDS} сек).")
        return
    if voice.file_size and voice.file_size > MAX_VOICE_BYTES:
        await message.answer("Голосовое слишком большое (максимум 20 МБ).")
        return

    limit_inc(uid)
    start_cooldown(uid)
    await bot.send_chat_action(message.chat.id, "typing")
    buf = io.BytesIO()
    try:
        await bot.download(voice, destination=buf)
        recognized = await ai.transcribe(buf.getvalue())
    except ai.AIError as exc:
        logger.error("STT error: %s", exc)
        await message.answer("Не смог распознать голосовое 😔 Попробуй записать покороче и чётче.")
        return
    except Exception:
        logger.exception("Voice handling failed")
        await message.answer("Не смог обработать голосовое 😔 Попробуй ещё раз.")
        return

    if not recognized:
        await message.answer("Я не расслышал речь 🎤 Попробуй ещё раз, ближе к микрофону.")
        return

    bump_stats(str(message.from_user.id), chars=len(recognized), voice=1)
    await message.answer(f"🎤 Услышал: «{recognized}»")
    await answer_with_ai(message, bot, recognized)


def validate_init_data(init_data: str) -> dict | None:
    """Проверяет подпись Telegram initData и возвращает пользователя."""
    if not init_data:
        return None
    try:
        data = dict(urllib.parse.parse_qsl(init_data, keep_blank_values=True))
        received = data.pop("hash", "")
        if not received:
            return None
        check = "\n".join(f"{k}={v}" for k, v in sorted(data.items()))
        secret = hmac.new(b"WebAppData", BOT_TOKEN.encode(), hashlib.sha256).digest()
        calculated = hmac.new(secret, check.encode(), hashlib.sha256).hexdigest()
        if not hmac.compare_digest(calculated, received):
            return None
        auth_date = int(data.get("auth_date", "0"))
        if auth_date and time.time() - auth_date > 86400:
            return None
        return json.loads(data.get("user", "{}"))
    except Exception:
        return None


async def serve_index(request: web.Request) -> web.FileResponse:
    return web.FileResponse(os.path.join(WEBAPP_DIR, "index.html"))


async def api_chat(request: web.Request) -> web.Response:
    try:
        payload = await request.json()
    except Exception:
        return web.json_response({"error": "bad json"}, status=400)

    user = validate_init_data(payload.get("initData", ""))
    if not user:
        return web.json_response({"error": "unauthorized"}, status=401)

    uid = str(user.get("id"))
    text = (payload.get("text") or "").strip()[:2000]
    if not text:
        return web.json_response({"error": "empty"}, status=400)

    left = cooldown_left(uid)
    if left > 0:
        return web.json_response({"error": "cooldown", "retry_after": left}, status=429)

    start_cooldown(uid)
    msgs = history.setdefault(uid, [])
    msgs.append({"role": "user", "content": text})
    try:
        reply = await ai.ask(msgs, build_system(uid), uid=uid)
    except ai.AIError as exc:
        msgs.pop()
        return web.json_response(
            {"error": "ai", "message": str(exc), "retry_after": exc.retry_after},
            status=503,
        )

    msgs.append({"role": "assistant", "content": reply})
    del msgs[:-MAX_HISTORY]
    save_memory()
    bump_stats(uid, chars=len(text))
    return web.json_response({"reply": reply})


async def api_profile(request: web.Request) -> web.Response:
    try:
        payload = await request.json()
    except Exception:
        payload = {}
    user = validate_init_data(payload.get("initData", ""))
    if not user:
        return web.json_response({"error": "unauthorized"}, status=401)
    uid = str(user.get("id"))
    return web.json_response(
        {
            "user": {
                "id": uid,
                "first_name": user.get("first_name", ""),
                "last_name": user.get("last_name", ""),
                "username": user.get("username", ""),
                "photo_url": user.get("photo_url", ""),
            },
            "stats": user_stats(uid),
        }
    )


async def start_webapp() -> None:
    app = web.Application()
    app.router.add_get("/", serve_index)
    app.router.add_get("/health", lambda r: web.json_response({"ok": True}))
    app.router.add_post("/api/chat", api_chat)
    app.router.add_post("/api/profile", api_profile)
    runner = web.AppRunner(app)
    await runner.setup()
    site = web.TCPSite(runner, "0.0.0.0", PORT)
    await site.start()
    logger.info("Mini App + API: http://0.0.0.0:%d", PORT)


async def _url_alive(url: str, timeout: int = 10) -> bool:
    try:
        timeout_obj = aiohttp.ClientTimeout(total=timeout)
        async with aiohttp.ClientSession(timeout=timeout_obj) as s:
            async with s.get(url) as r:
                return r.status == 200
    except Exception:
        return False


def _save_env_value(key: str, value: str) -> None:
    try:
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".env")
        with open(path, encoding="utf-8") as f:
            content = f.read()
        if re.search(rf"(?m)^{key}=.*$", content):
            content = re.sub(rf"(?m)^{key}=.*$", f"{key}={value}", content)
        else:
            content = content.rstrip() + f"\n{key}={value}\n"
        with open(path, "w", encoding="utf-8") as f:
            f.write(content)
    except OSError:
        pass


def _start_tunnel_sync() -> str | None:
    ssh = os.path.join(os.environ.get("WINDIR", r"C:\Windows"), "System32", "OpenSSH", "ssh.exe")
    try:
        proc = subprocess.Popen(
            [ssh, "-o", "StrictHostKeyChecking=no", "-o", "UserKnownHostsFile=NUL",
             "-R", f"80:127.0.0.1:{PORT}", "serveo.net"],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            encoding="utf-8", errors="replace", creationflags=0x08000000,
        )
    except Exception:
        return None
    deadline = time.time() + 25
    while time.time() < deadline:
        line = proc.stdout.readline()
        if not line:
            if proc.poll() is not None:
                break
            continue
        m = re.search(r"https://[a-z0-9-]+\.serveousercontent\.com", line)
        if m:
            return m.group(0)
    return None


async def tunnel_watchdog(bot: Bot) -> None:
    global WEBAPP_URL
    fails = 0
    while True:
        await asyncio.sleep(60)
        if not WEBAPP_URL:
            continue
        if await _url_alive(WEBAPP_URL.rstrip("/") + "/health"):
            fails = 0
            continue
        fails += 1
        if fails < 2:
            continue
        logger.warning("Mini App туннель упал — перезапускаю")
        url = await asyncio.to_thread(_start_tunnel_sync)
        if url:
            WEBAPP_URL = url
            _save_env_value("WEBAPP_URL", url)
            try:
                await bot.set_chat_menu_button(
                    menu_button=MenuButtonWebApp(text="Mini App", web_app=WebAppInfo(url=url))
                )
            except Exception:
                pass
            logger.info("Туннель восстановлен: %s", url)
        fails = 0


def _vpn_ping_sync() -> tuple[str, str]:
    try:
        started = time.time()
        r = subprocess.run(
            ["curl.exe", "-x", PROXY, "--ssl-no-revoke", "-sS", "-m", "15",
             "-o", "NUL", "-w", "%{time_total}", "https://api.telegram.org"],
            capture_output=True, text=True, timeout=25,
        )
        seconds = r.stdout.strip()
        if r.returncode == 0 and seconds:
            return "OK", f"{round(float(seconds) * 1000)} мс"
        return "FAIL", "нет связи"
    except Exception:
        return "FAIL", "ошибка"


async def vpn_alive() -> bool:
    try:
        connector = ProxyConnector.from_url(PROXY)
        timeout = aiohttp.ClientTimeout(total=12)
        async with aiohttp.ClientSession(connector=connector, timeout=timeout) as s:
            async with s.get("https://api.telegram.org") as r:
                return r.status in (200, 301, 302, 404)
    except Exception:
        return False


def restart_xray() -> None:
    subprocess.run(
        ["powershell", "-NoProfile", "-Command",
         "Get-Process xray -ErrorAction SilentlyContinue | Where-Object { $_.Path -like '*KomiBot*' } | Stop-Process -Force"],
        capture_output=True, timeout=30,
    )
    time.sleep(1)
    if os.path.exists(XRAY_EXE) and os.path.exists(XRAY_CFG):
        subprocess.Popen(
            [XRAY_EXE, "-c", XRAY_CFG],
            creationflags=0x08000000, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )


def run_update_vpn() -> None:
    subprocess.run(
        [sys.executable, UPDATE_SCRIPT, "200"],
        timeout=900, capture_output=True,
    )


async def vpn_watchdog() -> None:
    fails = 0
    while True:
        await asyncio.sleep(45)
        if await vpn_alive():
            fails = 0
            continue
        fails += 1
        logger.warning("VPN не отвечает (%d/2)", fails)
        if fails < 2:
            continue
        logger.info("Перезапускаю Xray...")
        await asyncio.to_thread(restart_xray)
        await asyncio.sleep(5)
        if not await vpn_alive():
            logger.info("Сервер мёртв — ищу новый (1–5 мин)...")
            await asyncio.to_thread(run_update_vpn)
            await asyncio.to_thread(restart_xray)
            await asyncio.sleep(5)
        fails = 0


async def main() -> None:
    if BOT_TOKEN in PLACEHOLDERS:
        print("\n[ОШИБКА] В файле .env не указан токен бота.\n")
        print("Открой .env и замени PASTE_YOUR_TOKEN_HERE на токен от @BotFather.\n")
        raise SystemExit(1)

    load_memory()
    load_stats()
    load_limits()
    load_profiles()
    load_bans()
    load_mutes()
    load_voices()
    load_chatstats()
    load_tokens()
    load_prompts()

    if PROXY:
        logger.info("Использую прокси: %s", PROXY)
        bot = Bot(token=BOT_TOKEN, session=AiohttpSession(proxy=PROXY))
    else:
        bot = Bot(token=BOT_TOKEN)

    logger.info("ИИ-провайдер по умолчанию: %s (кандидатов: %d)", ai.provider(), len(ai.candidates()))
    logger.info("Дневной лимит: %s | админы: %d", DAILY_LIMIT or "нет", len(ADMIN_IDS))

    try:
        await bot.set_my_commands(
            [
                BotCommand(command="start", description="Начать"),
                BotCommand(command="help", description="Помощь"),
                BotCommand(command="myid", description="Показать мой ID"),
                BotCommand(command="stats", description="Моя статистика"),
                BotCommand(command="whoami", description="Профиль и память"),
                BotCommand(command="mode", description="Сменить стиль общения"),
                BotCommand(command="remember", description="Запомнить факт"),
                BotCommand(command="forget", description="Забыть факты"),
                BotCommand(command="reset", description="Очистить память диалога"),
                BotCommand(command="main", description="Меню с кнопками"),
            ]
        )
        logger.info("Меню команд установлено")
    except Exception as exc:
        logger.warning("Не удалось установить меню команд: %s", exc)

    if WEBAPP_URL:
        try:
            await bot.set_chat_menu_button(
                menu_button=MenuButtonWebApp(text="Mini App", web_app=WebAppInfo(url=WEBAPP_URL))
            )
            logger.info("Кнопка Mini App установлена: %s", WEBAPP_URL)
        except Exception as exc:
            logger.warning("Не удалось установить кнопку Mini App: %s", exc)
    else:
        logger.info("Mini App не настроен (нет WEBAPP_URL) — кнопки не будет")

    try:
        me = await bot.get_me()
        logger.info("Бот @%s (%s) подключился к Telegram", me.username, me.full_name)
    except TelegramUnauthorizedError:
        print("\n[ОШИБКА] Telegram не принял токен. Проверь .env.\n")
        await bot.session.close()
        raise SystemExit(1)
    except Exception as exc:
        print(f"\n[ОШИБКА] Не удалось связаться с Telegram API: {exc!r}\n")
        print("Проверь интернет и VPN — инструкция в README.md.\n")
        await bot.session.close()
        raise SystemExit(1)

    logger.info("Бот запущен. Нажми Ctrl+C, чтобы остановить.")
    web_task = asyncio.create_task(start_webapp())
    if VPN_WATCHDOG:
        asyncio.create_task(vpn_watchdog())
        logger.info("VPN watchdog включён")
    if WEBAPP_URL:
        asyncio.create_task(tunnel_watchdog(bot))
        logger.info("Tunnel watchdog включён")
    try:
        await dp.start_polling(bot)
    finally:
        web_task.cancel()
        await bot.session.close()


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        pass