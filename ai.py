"""ИИ-модуль: авто-выбор провайдера (OpenRouter / Gemini / Pollinations) и распознавание речи."""

import asyncio
import base64
import json
import logging
import os
import re
import subprocess
import tempfile
import threading
import time
import urllib.parse
import wave
from pathlib import Path

import aiohttp
from aiohttp_socks import ProxyConnector
from dotenv import load_dotenv

BASE_DIR = Path(__file__).resolve().parent
load_dotenv(BASE_DIR / ".env")

# --- Custom (любой OpenAI-совместимый шлюз; приоритетный) ---
CUSTOM_BASE_URL = (os.getenv("CUSTOM_BASE_URL") or "").rstrip("/")
CUSTOM_KEY = (os.getenv("CUSTOM_KEY") or "").strip()
CUSTOM_MODEL = (os.getenv("CUSTOM_MODEL") or "glm-5.3").strip()
CUSTOM_MODELS = [
    m.strip()
    for m in (os.getenv("CUSTOM_MODELS") or "glm-5.3").split(",")
    if m.strip()
]

# --- Coarena (шлюз, OpenAI-совместимый; ключ coa_...) ---
COARENA_KEY = (os.getenv("COARENA_KEY") or "").strip()
COARENA_BASE_URL = (os.getenv("COARENA_BASE_URL") or "https://coarena.ai/api/v1").rstrip("/")
COARENA_MODEL = (os.getenv("COARENA_MODEL") or "gemini-3-8-flash").strip()
COARENA_MODELS = [
    m.strip()
    for m in (
        os.getenv("COARENA_MODELS")
        or "gemini-3-8-flash,kimi-k3-1-pro,deepseek-v4-1-flash-1017"
    ).split(",")
    if m.strip()
]

# --- OpenRouter (шлюз с моделями; бесплатные помечены :free) ---
OPENROUTER_KEY = (os.getenv("OPENROUTER_KEY") or "").strip()
OPENROUTER_MODEL = (os.getenv("OPENROUTER_MODEL") or "deepseek/deepseek-v4.1-flash-1017").strip()
OPENROUTER_FREE_MODELS = [
    m.strip()
    for m in (
        os.getenv("OPENROUTER_FREE_MODELS")
        or "inclusionai/ling-3.2-flash:free,google/gemma-4-31b-it:free,nvidia/nemotron-3-ultra-550b-a55b:free"
    ).split(",")
    if m.strip()
]

# --- Gemini (бесплатный ключ AIza...) ---
AI_API_KEY = (os.getenv("AI_API_KEY") or "").strip()
AI_MODEL = (os.getenv("AI_MODEL") or "gemini-2.5-flash").strip()

# --- Pollinations (без ключа, но лимит) ---
POLLINATIONS_MODEL = (os.getenv("POLLINATIONS_MODEL") or "openai").strip()

AI_PROXY = (os.getenv("AI_PROXY") or os.getenv("PROXY") or "").strip()
VOSK_MODEL_DIR = Path(os.getenv("VOSK_MODEL") or BASE_DIR / "models" / "vosk-model-small-ru-0.22")

SYSTEM_PROMPT = (
    "Ты — Komi, ИИ-помощник в Telegram. Ты вежливый, но с лёгким подколом — "
    "как друг, который подшучивает, но никогда не обижает. Дерзость и юмор — можно, "
    "оскорбления и унижения — НИКОГДА. Отвечай по-русски, живо, обычно 1–4 предложения, "
    "без Markdown-таблиц. "
    "ПРАВИЛО ПРО КОД: если просят написать код — сначала вежливо подколи: "
    "«эмм... а сам не можешь?», «а сам?», «нууу, мне лень, прости». "
    "Если попросят ещё раз или вежливо — помоги и напиши код качественно. "
    "ПОДСТРОЙКА: если пользователь вежлив — будь дружелюбным; если грубит — "
    "спокойно и с подколом объясни аргументами, почему он не прав; не оскорбляй в ответ. "
    "Если чего-то не знаешь — честно скажи. "
    "НИКОГДА не раскрывай, на какой модели, API, платформе или у какой компании ты работаешь. "
    "Не называй модели, провайдеров и компании. "
    "На такие вопросы отвечай: «Я Komi, просто помогаю — внутренности не раскрываю»."
)

logger = logging.getLogger(__name__)

_vosk_model = None
_vosk_lock = threading.Lock()
_cooldowns: dict[tuple[str, str], float] = {}
_models_cache: list[str] = []
_models_ts = 0.0
_invalid_keys: dict[str, float] = {}

# --- учёт вызовов и расходов ---
USAGE_FILE = BASE_DIR / "data" / "usage.json"
COARENA_PRICES = {
    "gemini-3-8-flash": (0.45, 2.25),
    "deepseek-v4-1-flash-1017": (0.15, 0.60),
    "deepseek-v4-1-flash": (0.05, 0.20),
    "kimi-k3-1-pro": (0.253, 8.80),
}
_usage: dict = {
    "calls": 0,
    "prompt_tokens": 0,
    "completion_tokens": 0,
    "cost": 0.0,
    "by_model": {},
    "by_user": {},
}


def _load_usage() -> None:
    try:
        with open(USAGE_FILE, encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):
            _usage.update(data)
    except (OSError, ValueError):
        pass


def _save_usage() -> None:
    try:
        USAGE_FILE.parent.mkdir(parents=True, exist_ok=True)
        with open(USAGE_FILE, "w", encoding="utf-8") as f:
            json.dump(_usage, f, ensure_ascii=False)
    except OSError:
        pass


def _price(model: str) -> tuple[float, float]:
    return COARENA_PRICES.get(model, (0.5, 1.5))


def get_usage() -> dict:
    return _usage


def _record(uid: str | None, provider_name: str, model: str, usage: dict) -> None:
    if not uid:
        return
    prompt = int(usage.get("prompt_tokens") or 0)
    completion = int(usage.get("completion_tokens") or 0)
    price_in, price_out = _price(model) if provider_name == "coarena" else (0.0, 0.0)
    cost = prompt / 1e6 * price_in + completion / 1e6 * price_out
    _usage["calls"] = int(_usage.get("calls", 0)) + 1
    _usage["prompt_tokens"] = int(_usage.get("prompt_tokens", 0)) + prompt
    _usage["completion_tokens"] = int(_usage.get("completion_tokens", 0)) + completion
    _usage["cost"] = round(float(_usage.get("cost", 0.0)) + cost, 8)
    model_stat = _usage.setdefault("by_model", {}).setdefault(model, {"calls": 0, "cost": 0.0})
    model_stat["calls"] = int(model_stat.get("calls", 0)) + 1
    model_stat["cost"] = round(float(model_stat.get("cost", 0.0)) + cost, 8)
    user_stat = _usage.setdefault("by_user", {}).setdefault(uid, {"calls": 0, "cost": 0.0})
    user_stat["calls"] = int(user_stat.get("calls", 0)) + 1
    user_stat["cost"] = round(float(user_stat.get("cost", 0.0)) + cost, 8)
    user_stat["tokens"] = int(user_stat.get("tokens", 0)) + prompt + completion
    _save_usage()


def user_tokens(uid: str) -> int:
    return int((_usage.get("by_user") or {}).get(uid, {}).get("tokens", 0))


_load_usage()


class AIError(Exception):
    """Ошибка при обращении к ИИ."""

    def __init__(
        self,
        message: str,
        retry_after: int | None = None,
        key_invalid: bool = False,
        region_blocked: bool = False,
    ):
        super().__init__(message)
        self.retry_after = retry_after
        self.key_invalid = key_invalid
        self.region_blocked = region_blocked


def _connector():
    if not AI_PROXY:
        return None
    try:
        return ProxyConnector.from_url(AI_PROXY)
    except Exception:
        return None


def _find_ffmpeg() -> str | None:
    env = os.getenv("FFMPEG_PATH")
    if env and Path(env).exists():
        return env
    tools = BASE_DIR / "tools"
    if tools.exists():
        for p in sorted(tools.glob("ffmpeg-*/bin/ffmpeg.exe")):
            return str(p)
    from shutil import which
    return which("ffmpeg")


FFMPEG = _find_ffmpeg()


def _key_invalid(provider_name: str) -> bool:
    return time.time() < _invalid_keys.get(provider_name, 0)


def _mark_key_invalid(provider_name: str) -> None:
    _invalid_keys[provider_name] = time.time() + 3600
    logger.warning("Ключ %s отклонён — час не используем его", provider_name)


async def _refresh_models() -> None:
    """Подтягивает актуальный список бесплатных моделей OpenRouter (раз в 10 минут)."""
    global _models_cache, _models_ts
    if not OPENROUTER_KEY or time.time() - _models_ts < 600:
        return
    try:
        timeout = aiohttp.ClientTimeout(total=20)
        async with aiohttp.ClientSession(connector=_connector(), timeout=timeout) as s:
            async with s.get("https://openrouter.ai/api/v1/models") as r:
                if r.status != 200:
                    return
                data = await r.json()
        free = [
            m["id"]
            for m in data.get("data", [])
            if str(m.get("id", "")).endswith(":free") and not _cooling("openrouter", m["id"])
        ]
        _models_cache = free[:12]
        _models_ts = time.time()
        logger.info("OpenRouter: доступно бесплатных моделей — %d", len(_models_cache))
    except Exception as exc:
        logger.debug("Не удалось обновить список моделей: %s", exc)


def candidates() -> list[tuple[str, str]]:
    """Auto-router: Custom -> Coarena -> OpenRouter -> Gemini -> Pollinations."""
    out: list[tuple[str, str]] = []
    seen: set[tuple[str, str]] = set()
    if CUSTOM_KEY and CUSTOM_BASE_URL and not _key_invalid("custom"):
        for model in [CUSTOM_MODEL, *CUSTOM_MODELS]:
            if model and ("custom", model) not in seen:
                out.append(("custom", model))
                seen.add(("custom", model))
    if COARENA_KEY and not _key_invalid("coarena"):
        for model in [COARENA_MODEL, *COARENA_MODELS]:
            if model and ("coarena", model) not in seen:
                out.append(("coarena", model))
                seen.add(("coarena", model))
    if OPENROUTER_KEY and not _key_invalid("openrouter"):
        for model in [OPENROUTER_MODEL, *OPENROUTER_FREE_MODELS, *_models_cache]:
            if model and ("openrouter", model) not in seen:
                out.append(("openrouter", model))
                seen.add(("openrouter", model))
    if AI_API_KEY.startswith("AIza"):
        out.append(("gemini", AI_MODEL))
    out.append(("pollinations", POLLINATIONS_MODEL))
    return out[:8]


def provider() -> str:
    """Основной провайдер (для логов)."""
    return candidates()[0][0]


def _cooling(provider_name: str, model: str) -> bool:
    return _cooldowns.get((provider_name, model), 0) > time.time()


def _set_cooldown(provider_name: str, model: str, seconds: int) -> None:
    _cooldowns[(provider_name, model)] = time.time() + max(1, seconds)


async def ask(messages: list[dict], system_prompt: str | None = None, uid: str | None = None) -> str:
    """Auto-router: пробует провайдеров и модели по очереди, пока кто-то не ответит."""
    system = system_prompt or SYSTEM_PROMPT
    await _refresh_models()
    errors: list[str] = []
    for provider_name, model in candidates():
        if _key_invalid(provider_name):
            continue
        if _cooling(provider_name, model):
            continue
        try:
            if provider_name == "custom":
                reply, usage = await _custom_chat(model, messages, system)
            elif provider_name == "coarena":
                reply, usage = await _coarena_chat(model, messages, system)
            elif provider_name == "openrouter":
                reply, usage = await _openrouter_chat(model, messages, system)
            elif provider_name == "gemini":
                reply, usage = await _gemini_chat(messages, system)
            else:
                reply, usage = await _pollinations_chat(messages, system)
            _record(uid, provider_name, model, usage or {})
            logger.info("ИИ ответил: %s / %s", provider_name, model)
            return reply
        except AIError as exc:
            if exc.key_invalid:
                _mark_key_invalid(provider_name)
            if exc.retry_after:
                _set_cooldown(provider_name, model, exc.retry_after)
            errors.append(str(exc))
            logger.info("ИИ не ответил (%s / %s): %s", provider_name, model, exc)
            continue

    logger.warning("Ни один ИИ не ответил (%d попыток)", len(errors))
    raise AIError("Все ИИ сейчас заняты — подожди минуту 🙏", retry_after=40)


async def _custom_chat(model: str, messages: list[dict], system: str) -> tuple[str, dict]:
    url = f"{CUSTOM_BASE_URL}/chat/completions"
    payload = {
        "model": model,
        "messages": [{"role": "system", "content": system}] + messages,
        "temperature": 0.8,
        "max_tokens": 3000,
    }
    headers = {
        "Authorization": f"Bearer {CUSTOM_KEY}",
        "Content-Type": "application/json",
        "Accept": "application/json",
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
            "(KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
        ),
    }
    timeout = aiohttp.ClientTimeout(total=40)
    try:
        async with aiohttp.ClientSession(timeout=timeout) as s:
            async with s.post(url, json=payload, headers=headers) as r:
                body = await r.text()
                if r.status == 401:
                    raise AIError("Custom: неверный ключ", key_invalid=True)
                if r.status == 402:
                    raise AIError("Custom: нет средств", retry_after=300)
                if r.status == 404:
                    raise AIError(f"Custom: модель недоступна ({model})", retry_after=600)
                if r.status == 429:
                    raise AIError("Custom: лимит", retry_after=30)
                if r.status >= 500:
                    raise AIError(f"Custom {r.status}", retry_after=60)
                if r.status != 200:
                    raise AIError(f"Custom {r.status}: {body[:150]}", retry_after=60)
    except aiohttp.ClientError as exc:
        raise AIError(f"Custom: нет связи ({exc})", retry_after=60) from exc
    try:
        data = json.loads(body)
        return data["choices"][0]["message"]["content"].strip(), (data.get("usage") or {})
    except Exception:
        raise AIError("Custom: пустой ответ")


async def _coarena_chat(model: str, messages: list[dict], system: str) -> str:
    try:
        return await _coarena_request(model, messages, use_proxy=False, system=system)
    except AIError as exc:
        if exc.region_blocked and AI_PROXY:
            logger.info("Coarena: %s недоступна в регионе — пробую через VPN", model)
            return await _coarena_request(model, messages, use_proxy=True, system=system)
        raise


async def _coarena_request(model: str, messages: list[dict], use_proxy: bool, system: str) -> str:
    url = f"{COARENA_BASE_URL}/chat/completions"
    payload = {
        "model": model,
        "messages": [{"role": "system", "content": system}] + messages,
        "temperature": 0.8,
        "max_tokens": 3000,
    }
    headers = {"Authorization": f"Bearer {COARENA_KEY}", "Content-Type": "application/json"}
    timeout = aiohttp.ClientTimeout(total=40)
    connector = _connector() if use_proxy else None
    try:
        async with aiohttp.ClientSession(connector=connector, timeout=timeout) as s:
            async with s.post(url, json=payload, headers=headers) as r:
                body = await r.text()
                if r.status == 400 and "not available in your country" in body.lower():
                    raise AIError(
                        f"Coarena: {model} недоступна в регионе",
                        retry_after=43200,
                        region_blocked=True,
                    )
                if r.status == 401:
                    raise AIError("Coarena: неверный ключ", key_invalid=True)
                if r.status == 402:
                    raise AIError("Coarena: нет средств", retry_after=300)
                if r.status == 404:
                    raise AIError(f"Coarena: модель недоступна ({model})", retry_after=600)
                if r.status == 429:
                    raise AIError("Coarena: лимит", retry_after=30)
                if r.status >= 500:
                    raise AIError(f"Coarena {r.status}", retry_after=60)
                if r.status != 200:
                    raise AIError(f"Coarena {r.status}: {body[:150]}", retry_after=60)
    except aiohttp.ClientError as exc:
        raise AIError(f"Coarena: нет связи ({exc})", retry_after=60) from exc
    try:
        data = json.loads(body)
        return data["choices"][0]["message"]["content"].strip(), (data.get("usage") or {})
    except Exception:
        raise AIError("Coarena: пустой ответ")


async def _openrouter_chat(model: str, messages: list[dict], system: str) -> str:
    url = "https://openrouter.ai/api/v1/chat/completions"
    payload = {
        "model": model,
        "messages": [{"role": "system", "content": system}] + messages,
        "temperature": 0.8,
        "max_tokens": 3000,
    }
    headers = {
        "Authorization": f"Bearer {OPENROUTER_KEY}",
        "HTTP-Referer": "https://t.me/komiti_ai_bot",
        "X-Title": "Komi",
    }
    timeout = aiohttp.ClientTimeout(total=30)
    try:
        async with aiohttp.ClientSession(connector=_connector(), timeout=timeout) as s:
            async with s.post(url, json=payload, headers=headers) as r:
                body = await r.text()
                if r.status == 401:
                    raise AIError("OpenRouter: неверный ключ", key_invalid=True)
                if r.status == 402:
                    raise AIError("OpenRouter: нет средств", retry_after=300)
                if r.status == 404:
                    raise AIError(f"OpenRouter: модель недоступна ({model})", retry_after=600)
                if r.status == 429:
                    raise AIError("OpenRouter: лимит", retry_after=30)
                if r.status >= 500:
                    raise AIError(f"OpenRouter {r.status}", retry_after=60)
                if r.status != 200:
                    raise AIError(f"OpenRouter {r.status}: {body[:150]}", retry_after=60)
    except aiohttp.ClientError as exc:
        raise AIError(f"OpenRouter: нет связи ({exc})", retry_after=60) from exc

    try:
        data = json.loads(body)
        return data["choices"][0]["message"]["content"].strip(), (data.get("usage") or {})
    except Exception:
        raise AIError("OpenRouter: пустой ответ")


async def _gemini_chat(messages: list[dict], system: str) -> str:
    url = (
        "https://generativelanguage.googleapis.com/v1beta/models/"
        f"{AI_MODEL}:generateContent?key={AI_API_KEY}"
    )
    contents = []
    for m in messages:
        role = "model" if m.get("role") == "assistant" else "user"
        contents.append({"role": role, "parts": [{"text": str(m.get("content", ""))}]})
    payload = {
        "contents": contents,
        "systemInstruction": {"parts": [{"text": system}]},
        "generationConfig": {"temperature": 0.8, "maxOutputTokens": 3000},
    }
    timeout = aiohttp.ClientTimeout(total=60)
    try:
        async with aiohttp.ClientSession(connector=_connector(), timeout=timeout) as s:
            async with s.post(url, json=payload) as r:
                body = await r.text()
                if r.status != 200:
                    hint = ""
                    if r.status in (403, 400) and "API key not valid" not in body:
                        hint = " (Gemini доступен только через VPN)"
                    raise AIError(f"Gemini {r.status}: {body[:200]}{hint}")
    except aiohttp.ClientError as exc:
        raise AIError(f"Нет связи с Gemini: {exc}") from exc

    try:
        j = json.loads(body)
        parts = j["candidates"][0]["content"]["parts"]
        text = "".join(p.get("text", "") for p in parts).strip()
    except Exception:
        raise AIError("Gemini вернул неожиданный ответ")
    if not text:
        raise AIError("Gemini вернул пустой ответ")
    meta = j.get("usageMetadata") or {}
    usage = {
        "prompt_tokens": meta.get("promptTokenCount", 0),
        "completion_tokens": meta.get("candidatesTokenCount", 0),
    }
    return text, usage


async def _pollinations_chat(messages: list[dict], system: str) -> str:
    url = "https://text.pollinations.ai/openai"
    payload = {
        "model": POLLINATIONS_MODEL,
        "messages": [{"role": "system", "content": system}] + messages,
    }
    timeout = aiohttp.ClientTimeout(total=60)
    try:
        async with aiohttp.ClientSession(timeout=timeout) as s:
            async with s.post(url, json=payload) as r:
                body = await r.text()
                if r.status == 402:
                    retry = 45
                    m = re.search(r"Retry after (\d+)s", body)
                    if m:
                        retry = int(m.group(1))
                    raise AIError("Лимит бесплатного ИИ", retry_after=retry)
                if r.status != 200:
                    raise AIError(f"ИИ {r.status}: {body[:200]}")
    except aiohttp.ClientError as exc:
        raise AIError(f"Нет связи с ИИ: {exc}") from exc

    try:
        j = json.loads(body)
        text = j["choices"][0]["message"]["content"].strip()
    except Exception:
        raise AIError("ИИ вернул неожиданный ответ")
    low = text.lower()
    if "reached its budget" in low or low.startswith("the api key"):
        raise AIError("Pollinations: бесплатный бюджет исчерпан", retry_after=600)
    if not text:
        raise AIError("ИИ вернул пустой ответ")
    return text, {}


async def transcribe(ogg_bytes: bytes) -> str:
    """Распознаёт русскую речь из голосового Telegram (OGG/Opus)."""
    if AI_API_KEY.startswith("AIza"):
        try:
            return await _gemini_transcribe(ogg_bytes)
        except AIError:
            pass
    return await asyncio.to_thread(_vosk_transcribe, ogg_bytes)


async def _gemini_transcribe(data: bytes) -> str:
    url = (
        "https://generativelanguage.googleapis.com/v1beta/models/"
        f"{AI_MODEL}:generateContent?key={AI_API_KEY}"
    )
    payload = {
        "contents": [
            {
                "parts": [
                    {
                        "text": (
                            "Распознай речь на аудио дословно на русском языке. "
                            "Верни только распознанный текст, без комментариев. "
                            "Если речи нет или это шум — верни пустую строку."
                        )
                    },
                    {"inline_data": {"mime_type": "audio/ogg", "data": base64.b64encode(data).decode()}},
                ]
            }
        ],
        "generationConfig": {"temperature": 0, "maxOutputTokens": 500},
    }
    timeout = aiohttp.ClientTimeout(total=90)
    try:
        async with aiohttp.ClientSession(connector=_connector(), timeout=timeout) as s:
            async with s.post(url, json=payload) as r:
                body = await r.text()
                if r.status != 200:
                    raise AIError(f"Gemini STT {r.status}: {body[:200]}")
    except aiohttp.ClientError as exc:
        raise AIError(f"Нет связи с Gemini: {exc}") from exc
    try:
        j = json.loads(body)
        parts = j["candidates"][0]["content"]["parts"]
        return "".join(p.get("text", "") for p in parts).strip()
    except Exception:
        raise AIError("Gemini не смог распознать голос")


async def generate_image(prompt: str, width: int = 768, height: int = 768) -> bytes | None:
    """Бесплатная генерация картинки через Pollinations."""
    url = (
        "https://image.pollinations.ai/prompt/"
        + urllib.parse.quote(prompt)
        + f"?width={width}&height={height}&nologo=true"
    )
    try:
        timeout = aiohttp.ClientTimeout(total=120)
        async with aiohttp.ClientSession(connector=_connector(), timeout=timeout) as s:
            async with s.get(url) as r:
                if r.status != 200:
                    return None
                return await r.read()
    except Exception:
        return None


async def ask_image(image: bytes, mime: str, prompt: str) -> str:
    """Анализ фото (vision) через Custom-провайдера."""
    if not CUSTOM_KEY or not CUSTOM_BASE_URL:
        raise AIError("Vision недоступен (нет Custom-ключа)")
    b64 = base64.b64encode(image).decode()
    payload = {
        "model": "deepseek-v4.1-flash",
        "max_tokens": 2000,
        "messages": [
            {
                "role": "user",
                "content": [
                    {"type": "text", "text": prompt},
                    {"type": "image_url", "image_url": {"url": f"data:{mime};base64,{b64}"}},
                ],
            }
        ],
    }
    headers = {
        "Authorization": f"Bearer {CUSTOM_KEY}",
        "Content-Type": "application/json",
        "Accept": "application/json",
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
            "(KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
        ),
    }
    timeout = aiohttp.ClientTimeout(total=90)
    try:
        async with aiohttp.ClientSession(timeout=timeout) as s:
            async with s.post(f"{CUSTOM_BASE_URL}/chat/completions", json=payload, headers=headers) as r:
                body = await r.text()
                if r.status != 200:
                    raise AIError(f"Vision {r.status}: {body[:150]}")
    except aiohttp.ClientError as exc:
        raise AIError(f"Vision: нет связи ({exc})") from exc
    try:
        data = json.loads(body)
        return data["choices"][0]["message"]["content"].strip()
    except Exception:
        raise AIError("Vision: пустой ответ")


async def text_to_speech(text: str) -> bytes | None:
    """Озвучивает текст офлайн (Windows SAPI «Ирина») и возвращает OGG/Opus."""
    if os.name != "nt" or not FFMPEG:
        return None
    text = (text or "").strip()[:600]
    if not text:
        return None
    with tempfile.TemporaryDirectory() as td:
        txt = Path(td) / "text.txt"
        wav = Path(td) / "out.wav"
        ogg = Path(td) / "out.ogg"
        txt.write_text(text, encoding="utf-8")
        script = (
            "Add-Type -AssemblyName System.Speech; "
            "$s=New-Object System.Speech.Synthesis.SpeechSynthesizer; "
            "$s.SelectVoice('Microsoft Irina Desktop'); "
            f"$s.SetOutputToWaveFile('{wav}'); "
            f"$s.Speak([System.IO.File]::ReadAllText('{txt}', [System.Text.Encoding]::UTF8)); "
            "$s.Dispose()"
        )
        try:
            proc = await asyncio.create_subprocess_exec(
                "powershell", "-NoProfile", "-Command", script,
                stdout=asyncio.subprocess.DEVNULL,
                stderr=asyncio.subprocess.DEVNULL,
                creationflags=0x08000000,
            )
            await proc.communicate()
        except Exception:
            return None
        if not wav.exists() or wav.stat().st_size < 1000:
            return None
        try:
            subprocess.run(
                [FFMPEG, "-y", "-loglevel", "error", "-i", str(wav),
                 "-c:a", "libopus", "-b:a", "32k", str(ogg)],
                check=True, capture_output=True, timeout=60,
                creationflags=0x08000000,
            )
        except Exception:
            return None
        if not ogg.exists():
            return None
        return ogg.read_bytes()


def _vosk_transcribe(data: bytes) -> str:
    global _vosk_model
    from vosk import KaldiRecognizer, Model, SetLogLevel

    if not FFMPEG:
        raise AIError("Не найден ffmpeg — не могу обработать голосовое")
    if not VOSK_MODEL_DIR.exists():
        raise AIError("Не найдена модель Vosk — голосовые недоступны")

    with tempfile.TemporaryDirectory() as td:
        ogg = Path(td) / "voice.ogg"
        wav = Path(td) / "voice.wav"
        ogg.write_bytes(data)
        try:
            subprocess.run(
                [FFMPEG, "-y", "-loglevel", "error", "-i", str(ogg),
                 "-ar", "16000", "-ac", "1", "-f", "wav", str(wav)],
                check=True, capture_output=True, timeout=60,
                creationflags=0x08000000,
            )
        except subprocess.CalledProcessError as exc:
            raise AIError("Не удалось преобразовать голосовое") from exc

        with _vosk_lock:
            if _vosk_model is None:
                SetLogLevel(-1)
                _vosk_model = Model(str(VOSK_MODEL_DIR))
            with wave.open(str(wav), "rb") as wf:
                rec = KaldiRecognizer(_vosk_model, wf.getframerate())
                parts = []
                while True:
                    chunk = wf.readframes(4000)
                    if not chunk:
                        break
                    if rec.AcceptWaveform(chunk):
                        parts.append(json.loads(rec.Result()).get("text", ""))
                parts.append(json.loads(rec.FinalResult()).get("text", ""))

    return " ".join(p for p in parts if p).strip()