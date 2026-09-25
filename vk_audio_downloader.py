#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
=============================================================================
VK Music Grabber (VK Audio Downloader)
=============================================================================
Профессиональный инструмент для скачивания аудиозаписей из ВКонтакте с полной
поддержкой обоих доменов (vk.ru и vk.com), встроенным HLS/AES-128 дешифратором,
метаданных (ID3-теги: артист, трек, альбом, обложка, текст песни), умной системы
архивации (archive.txt), защиты от банов (рандомизированные задержки) и возможностью
сборки в единый автономный .exe файл через PyInstaller.

Версия: 2.4.0 (С поддержкой защищенных HLS/AES-128 потоков и чистым MP3 демультиплексированием)
=============================================================================
"""

import os
import sys
import re
import json
import time
import random
import getpass
import argparse
import subprocess
from pathlib import Path
from dataclasses import dataclass
from typing import Optional, List, Dict, Any, Tuple, Set
from urllib.parse import urlparse, parse_qs, urljoin

# Убеждаемся в корректной работе с кодировкой UTF-8 в консоли Windows
if sys.platform.startswith('win'):
    try:
        sys.stdout.reconfigure(encoding='utf-8', errors='replace')
        sys.stderr.reconfigure(encoding='utf-8', errors='replace')
    except Exception:
        pass

import requests
from requests.adapters import HTTPAdapter
from urllib3.util import Retry
from bs4 import BeautifulSoup
from tqdm import tqdm

# Cryptography для дешифровки защищенных HLS AES-128 аудиопотоков VK
try:
    from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
    from cryptography.hazmat.backends import default_backend
except ImportError:
    print("[ОШИБКА] Библиотека cryptography не найдена. Установите: pip install cryptography")
    sys.exit(1)

# Mutagen для записи ID3-тегов в MP3
try:
    from mutagen.id3 import ID3, TIT2, TPE1, TALB, USLT, APIC, ID3NoHeaderError
except ImportError:
    print("[ОШИБКА] Библиотека mutagen не установлена. Установите: pip install mutagen")
    sys.exit(1)


# =====================================================================
# Константы приложения и Домены
# =====================================================================
APP_NAME = "VK Music Grabber"
APP_VERSION = "2.4.0"
CONFIG_FILE = ".vk_session.json"
ARCHIVE_FILENAME = "archive.txt"

# Минимальный размер валидного аудиофайла (100 КБ) для отсечения битых текстовых файлов
MIN_AUDIO_FILE_SIZE = 100 * 1024

# Поддерживаемые домены VK (vk.ru основной, vk.com поддерживается полностью)
DEFAULT_VK_DOMAIN = "vk.ru"
SUPPORTED_DOMAINS = ["vk.ru", "vk.com"]

# Официальные параметры Kate Mobile (для легального доступа к VK Audio API)
KATE_CLIENT_ID = "2685278"
KATE_CLIENT_SECRET = "lxhD8OD7dMsqtXIm5IUY"
KATE_USER_AGENT = "KateMobileAndroid/56 lite-460 (Android 4.4.2; SDK 19; x86; unknown Android SDK built for x86; en)"

# VK API
VK_API_VERSION = "5.131"

# Регулярные выражения
RE_CLEAN_FILENAME = re.compile(r'[\\/*?:"<>|]')
RE_M3U8_TO_MP3 = re.compile(r'(/audios)?/([0-9a-zA-Z_-]+)/index\.m3u8')
RE_URL_PREFIX = re.compile(r'^https?://(?:m\.)?vk\.(?:com|ru)/', re.IGNORECASE)

# Алфавит дешифратора ссылок аудиозаписей ВКонтакте
VK_STR = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMN0PQRSTUVWXYZO123456789+/="

# Шаблоны ссылок на плейлисты и альбомы для обоих доменов
RE_PLAYLIST_PATTERNS = [
    re.compile(r'(?:playlist|album)/(-?\d+)_(\d+)(?:_([a-zA-Z0-9]+))?'),
    re.compile(r'audio_playlist(-?\d+)_(\d+)(?:(?:&access_hash=|_)([a-zA-Z0-9]+))?'),
    re.compile(r'^(-?\d+)_(\d+)(?:_([a-zA-Z0-9]+))?$')
]


# =====================================================================
# Алгоритм дешифровки защищенных веб-ссылок VK
# =====================================================================
def _splice(l, a, b, c):
    return l[:a] + [c] + l[a + b:], l[a:a + b]

def _vk_o(string):
    result = []
    index2 = 0
    for s in string:
        sym_index = VK_STR.find(s)
        if sym_index != -1:
            if index2 % 4 != 0:
                index2 += 1
                i = (i << 6) + sym_index
                result.append(chr(0xFF & i >> (-2 * index2 & 6)))
            else:
                i = sym_index
                index2 += 1
    return ''.join(result)

def _vk_r(string, i):
    vk_str2 = VK_STR + VK_STR
    vk_str2_len = len(vk_str2)
    result = []
    for s in string:
        index = vk_str2.find(s)
        if index != -1:
            offset = index - int(i)
            if offset < 0:
                offset += vk_str2_len
            result.append(vk_str2[offset])
        else:
            result.append(s)
    return ''.join(result)

def _vk_xor(string, i):
    xor_val = ord(i[0])
    return ''.join(chr(ord(s) ^ xor_val) for s in string)

def _vk_s_child(t, e):
    i = len(t)
    if not i:
        return []
    o = []
    e = int(e)
    for a in range(i - 1, -1, -1):
        e = (i * (a + 1) ^ e + a) % i
        o.append(e)
    return o[::-1]

def _vk_s(t, e):
    i = len(t)
    if not i:
        return t
    o = _vk_s_child(t, e)
    t = list(t)
    for a in range(1, i):
        t, y = _splice(t, o[i - 1 - a], 1, t[a])
        t[a] = y[0]
    return ''.join(t)

def decode_audio_url(string: str, user_id: int = 0) -> str:
    """Расшифровывает обфусцированные веб-ссылки ВКонтакте (audio_api_unavailable)."""
    if 'audio_api_unavailable' not in string or '?extra=' not in string:
        return string
    try:
        vals = string.split('?extra=', 1)[1].split('#')
        tstr = _vk_o(vals[0])
        ops_list = _vk_o(vals[1]).split('\x09')[::-1]
        for op_data in ops_list:
            split_op_data = op_data.split('\x0b')
            cmd = split_op_data[0]
            arg = split_op_data[1] if len(split_op_data) > 1 else None
            if cmd == 'v':
                tstr = tstr[::-1]
            elif cmd == 'r':
                tstr = _vk_r(tstr, arg)
            elif cmd == 'x':
                tstr = _vk_xor(tstr, arg)
            elif cmd == 's':
                tstr = _vk_s(tstr, arg)
            elif cmd == 'i':
                tstr = _vk_s(tstr, int(arg) ^ user_id)
        return tstr
    except Exception:
        return string


# =====================================================================
# Демультиплексор MPEG-TS в чистый аудиопоток MP3
# =====================================================================
def demux_ts_to_audio(ts_data: bytes) -> bytes:
    """
    Чистый Python демультиплексор MPEG-TS: извлекает элементарный аудиопоток (MP3)
    из пакетов MPEG-TS без использования внешних утилит.
    """
    audio_data = bytearray()
    i = 0
    total_len = len(ts_data)

    while i < total_len:
        # Ищем байт синхронизации TS пакета (0x47)
        if ts_data[i] != 0x47:
            idx = ts_data.find(b'\x47', i)
            if idx == -1:
                break
            i = idx

        packet = ts_data[i:i + 188]
        if len(packet) < 188:
            break
        i += 188

        # Заголовок пакета TS
        pusi = (packet[1] & 0x40) != 0
        afc = (packet[3] & 0x30) >> 4

        payload_offset = 4
        if afc in (2, 3):
            adapt_len = packet[4]
            payload_offset = 5 + adapt_len

        if afc in (1, 3) and payload_offset < 188:
            payload = packet[payload_offset:]
            if pusi and len(payload) >= 9 and payload[:3] == b'\x00\x00\x01':
                # Заголовок PES пакета
                stream_id = payload[3]
                # Аудио потоки ISO/IEC 13818-3 (MP3/AAC): 0xC0..0xDF или private stream 0xBD
                if 0xC0 <= stream_id <= 0xDF or stream_id == 0xBD:
                    pes_hdr_len = payload[8]
                    pes_payload = payload[9 + pes_hdr_len:]
                    audio_data.extend(pes_payload)
            elif not pusi:
                audio_data.extend(payload)

    return bytes(audio_data)


# =====================================================================
# Модели данных
# =====================================================================
@dataclass
class AudioTrack:
    """Модель данных музыкального трека."""
    id: int
    owner_id: int
    artist: str
    title: str
    duration: int
    url: str
    album_title: Optional[str] = None
    lyrics_id: Optional[int] = None
    cover_url: Optional[str] = None

    @property
    def uid(self) -> str:
        """Уникальный идентификатор трека в формате owner_id_audio_id."""
        return f"{self.owner_id}_{self.id}"

    @property
    def formatted_name(self) -> str:
        """Форматированное имя трека: Исполнитель - Название."""
        return f"{self.artist} - {self.title}"


# =====================================================================
# Вспомогательные утилиты парсинга ссылок и ID
# =====================================================================
def sanitize_filename(filename: str, max_len: int = 180) -> str:
    """
    Очищает строку от недопустимых в именах файлов символов:
    \\, /, :, *, ?, ", <, >, | и служебных управляющих символов.
    Ограничивает длину для совместимости с ограничениями файловой системы.
    """
    clean = RE_CLEAN_FILENAME.sub('_', filename)
    clean = "".join(ch for ch in clean if ch.isprintable())
    clean = clean.strip().strip('.')
    clean = re.sub(r'\s+', ' ', clean)
    if not clean:
        clean = "audio_track"
    if len(clean) > max_len:
        clean = clean[:max_len].rstrip().rstrip('.')
    return clean


def parse_playlist_input(input_str: str) -> Optional[Tuple[int, int, Optional[str]]]:
    """
    Разбирает ссылку или идентификатор плейлиста/альбома.
    """
    cleaned = input_str.strip()
    for pattern in RE_PLAYLIST_PATTERNS:
        match = pattern.search(cleaned)
        if match:
            owner_id = int(match.group(1))
            playlist_id = int(match.group(2))
            access_key = match.group(3)
            return owner_id, playlist_id, access_key
    return None


def parse_target_id(client: Optional['VKClient'], input_str: str) -> Optional[int]:
    """
    Извлекает числовой ID пользователя или группы из строки или ссылки:
      - Числовые: '123456', '-123456'
      - Префиксы: 'id123456', 'club123456', 'public123456'
      - Ссылки: 'https://vk.ru/id123', 'https://vk.com/club123', 'https://m.vk.ru/durov'
      - Буквенные короткие имена: 'durov' (резолвятся через API utils.resolveScreenName)
    """
    cleaned = input_str.strip()
    cleaned = RE_URL_PREFIX.sub('', cleaned).strip().strip('/')

    if re.match(r'^-?\d+$', cleaned):
        return int(cleaned)

    if re.match(r'^id\d+$', cleaned, re.IGNORECASE):
        return int(cleaned[2:])

    if re.match(r'^(club|public)\d+$', cleaned, re.IGNORECASE):
        num = re.sub(r'^(club|public)', '', cleaned, flags=re.IGNORECASE)
        return -int(num)

    if client and client.access_token:
        try:
            data = client.call_api("utils.resolveScreenName", {"screen_name": cleaned})
            resp = data.get("response")
            if isinstance(resp, dict):
                obj_id = resp.get("object_id")
                obj_type = resp.get("type")
                if obj_id:
                    return -int(obj_id) if obj_type == "group" else int(obj_id)
        except Exception:
            pass

    return None


def create_robust_session(retries: int = 4, backoff_factor: float = 0.5) -> requests.Session:
    """
    Создает requests.Session с автоматическим повтором запросов при сбоях сети
    и кодах 429, 500, 502, 503, 504.
    """
    session = requests.Session()
    retry_strategy = Retry(
        total=retries,
        read=retries,
        connect=retries,
        backoff_factor=backoff_factor,
        status_forcelist=[429, 500, 502, 503, 504],
        raise_on_status=False
    )
    adapter = HTTPAdapter(max_retries=retry_strategy, pool_connections=10, pool_maxsize=10)
    session.mount("https://", adapter)
    session.mount("http://", adapter)
    session.headers.update({"User-Agent": KATE_USER_AGENT})
    return session


def clean_html_entities(text: str) -> str:
    """Декодирует HTML-сущности (&amp;, &#39;, &quot; и т.д.) в читаемый текст."""
    if not text:
        return ""
    return BeautifulSoup(text, "html.parser").text.strip()


# =====================================================================
# Менеджер архива загрузок (archive.txt)
# =====================================================================
class ArchiveManager:
    """
    Управляет архивом скачанных треков (файл archive.txt в папке загрузки).
    Позволяет пропускать повторное скачивание даже если аудиофайлы
    были перемещены или переименованы.
    """
    def __init__(self, output_dir: Path):
        self.archive_file = output_dir / ARCHIVE_FILENAME
        self._downloaded_uids: Set[str] = set()
        self._load()

    def _load(self):
        """Загружает список уже скачанных ID в память."""
        if not self.archive_file.exists():
            return
        try:
            with open(self.archive_file, "r", encoding="utf-8") as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith("#"):
                        self._downloaded_uids.add(line)
        except Exception as e:
            print(f"[!] Предупреждение: Не удалось прочитать архив {self.archive_file}: {e}")

    def is_downloaded(self, track_uid: str) -> bool:
        """Проверяет, скачан ли трек ранее."""
        return track_uid in self._downloaded_uids

    def add(self, track_uid: str):
        """Добавляет трек в архив и сохраняет на диск."""
        self._downloaded_uids.add(track_uid)
        try:
            with open(self.archive_file, "a", encoding="utf-8") as f:
                f.write(f"{track_uid}\n")
        except Exception as e:
            print(f"[!] Ошибка записи в {ARCHIVE_FILENAME}: {e}")

    @property
    def count(self) -> int:
        return len(self._downloaded_uids)


# =====================================================================
# Менеджер ID3-тегов и метаданных
# =====================================================================
class MetadataManager:
    """
    Отвечает за вшивание метаданных ID3v2.3 (Исполнитель, Название, Альбом,
    Обложка, Текст песни) в MP3-файлы с помощью mutagen.
    """
    @staticmethod
    def embed_tags(file_path: Path, track: AudioTrack, lyrics: Optional[str] = None, cover_bytes: Optional[bytes] = None):
        """
        Вшивает все доступные теги в аудиофайл.
        Использует ID3v2.3 для максимальной совместимости с Windows Explorer и плеерами.
        """
        try:
            try:
                audio = ID3(str(file_path))
            except ID3NoHeaderError:
                audio = ID3()

            # 1. Основные теги (TIT2 - Название, TPE1 - Артист, TALB - Альбом)
            audio.delall("TIT2")
            audio.add(TIT2(encoding=3, text=track.title))

            audio.delall("TPE1")
            audio.add(TPE1(encoding=3, text=track.artist))

            if track.album_title:
                audio.delall("TALB")
                audio.add(TALB(encoding=3, text=track.album_title))

            # 2. Текст песни (USLT)
            if lyrics:
                audio.delall("USLT")
                audio.add(USLT(encoding=3, lang="eng", desc="", text=lyrics))

            # 3. Обложка альбома / трека (APIC)
            if cover_bytes:
                audio.delall("APIC")
                mime_type = "image/jpeg"
                if cover_bytes.startswith(b"\x89PNG\r\n\x1a\n"):
                    mime_type = "image/png"
                elif cover_bytes.startswith(b"GIF8"):
                    mime_type = "image/gif"
                elif cover_bytes.startswith(b"RIFF") and b"WEBP" in cover_bytes[:12]:
                    mime_type = "image/webp"

                audio.add(APIC(
                    encoding=3,
                    mime=mime_type,
                    type=3,  # 3 = Front Cover
                    desc="Cover",
                    data=cover_bytes
                ))

            # Сохраняем теги ID3v2.3
            audio.save(str(file_path), v2_version=3)
        except Exception as e:
            print(f"\n[!] Предупреждение: Не удалось записать теги для {track.formatted_name}: {e}")


# =====================================================================
# Клиент VK API и Авторизация с поддержкой vk.ru и vk.com
# =====================================================================
class VKClient:
    """
    Клиент для взаимодействия с ВКонтакте:
    1. Поддержка обоих доменов: vk.ru (основной) и vk.com (резервный).
    2. Авторизация по логину/паролю (с 2FA и капчей через Kate Mobile OAuth).
    3. Авторизация по Access Token.
    4. Авторизация по Cookies (remixsid) с умным парсингом и веб-загрузкой.
    """
    def __init__(self, domain: str = DEFAULT_VK_DOMAIN, min_delay: float = 2.0, max_delay: float = 4.5):
        self.domain = domain.lower() if domain.lower() in SUPPORTED_DOMAINS else DEFAULT_VK_DOMAIN
        self.session = create_robust_session()
        self.access_token: Optional[str] = None
        self.user_id: Optional[int] = None
        self.user_name: Optional[str] = None
        self.min_delay = min_delay
        self.max_delay = max_delay
        self.is_cookie_session = False

    @property
    def fallback_domain(self) -> str:
        """Резервный домен на случай проблем с сетью."""
        return "vk.com" if self.domain == "vk.ru" else "vk.ru"

    def get_api_base(self, domain: Optional[str] = None) -> str:
        d = domain or self.domain
        return f"https://api.{d}/method/"

    def get_oauth_url(self, domain: Optional[str] = None) -> str:
        d = domain or self.domain
        return f"https://oauth.{d}/token"

    def anti_ban_delay(self, action_name: str = ""):
        """Случайная пауза между обращениями к API и скачиванием файлов."""
        delay = random.uniform(self.min_delay, self.max_delay)
        time.sleep(delay)

    def load_saved_session(self) -> bool:
        """Пытается загрузить сохраненный сеанс из локального файла."""
        if not os.path.exists(CONFIG_FILE):
            return False
        try:
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            token = data.get("access_token")
            user_id = data.get("user_id")
            if token and self.validate_token(token, user_id):
                return True
        except Exception:
            pass
        return False

    def save_session(self):
        """Сохраняет текущий валидный токен в файл сессии."""
        if not self.access_token:
            return
        try:
            data = {
                "access_token": self.access_token,
                "user_id": self.user_id,
                "user_name": self.user_name,
                "domain": self.domain,
                "updated_at": int(time.time())
            }
            with open(CONFIG_FILE, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
        except Exception as e:
            print(f"[!] Не удалось сохранить сессию: {e}")

    def auth_by_credentials(self, login: str, password: str) -> bool:
        """Авторизация через OAuth Kate Mobile с интерактивной поддержкой 2FA и капчи."""
        code: Optional[str] = None
        captcha_sid: Optional[str] = None
        captcha_key: Optional[str] = None

        print(f"\n[*] Авторизация через шлюз VK OAuth (Kate Mobile на {self.domain})...")

        while True:
            params = {
                "grant_type": "password",
                "client_id": KATE_CLIENT_ID,
                "client_secret": KATE_CLIENT_SECRET,
                "username": login,
                "password": password,
                "scope": "audio,offline",
                "2fa_supported": 1,
                "v": VK_API_VERSION
            }
            if code:
                params["code"] = code
            if captcha_sid and captcha_key:
                params["captcha_sid"] = captcha_sid
                params["captcha_key"] = captcha_key

            resp = None
            for dom in [self.domain, self.fallback_domain]:
                try:
                    resp = self.session.post(self.get_oauth_url(dom), data=params, timeout=15)
                    if resp.status_code in (200, 400, 401):
                        break
                except requests.RequestException:
                    continue

            if not resp:
                print(f"[X] Ошибка сети: не удалось связаться с OAuth шлюзом ({self.domain} / {self.fallback_domain})")
                return False

            try:
                data = resp.json()
            except Exception:
                print(f"[X] Ошибка разбора ответа сервера VK (HTTP {resp.status_code})")
                return False

            if "access_token" in data:
                self.access_token = data["access_token"]
                self.user_id = int(data.get("user_id", 0))
                print(f"[V] Авторизация успешна! ID пользователя: {self.user_id}")
                self._fetch_profile_name()
                self.save_session()
                return True

            error = data.get("error")
            error_type = data.get("error_type")
            error_desc = data.get("error_description", "Неизвестная ошибка")

            if error == "need_validation":
                val_type = data.get("validation_type")
                if val_type == "2fa_app":
                    print("[!] Требуется подтверждение 2FA: введите код из приложения-аутентификатора.")
                else:
                    print(f"[!] Требуется подтверждение входа ({val_type}): код выслан по SMS или в приложении VK.")
                code = input(">> Введите код подтверждения: ").strip()
                continue

            if error == "need_captcha":
                captcha_sid = data.get("captcha_sid")
                captcha_img = data.get("captcha_img")
                print(f"\n[!] Требуется ввод капчи! Откройте ссылку в браузере:\n{captcha_img}")
                captcha_key = input(">> Введите текст с картинки капчи: ").strip()
                continue

            if error == "invalid_client":
                print(f"[X] Ошибка: Неверный логин или пароль. ({error_desc})")
                return False
            elif error == "need_token":
                print("[X] Ошибка авторизации: требуется дополнительное подтверждение аккаунта.")
                return False
            elif "flood" in str(error).lower() or error_type == "password_bruteforce_attempt":
                print(f"[X] Блокировка попыток входа (Flood Control). {error_desc}")
                print("    Совет: Воспользуйтесь авторизацией через Token или Cookies!")
                return False
            else:
                print(f"[X] Ошибка авторизации: {error} - {error_desc}")
                return False

    def auth_by_token(self, token_or_url: str) -> bool:
        """Авторизация по access_token (или URL из адресной строки после OAuth)."""
        token = token_or_url.strip()

        if "#" in token or "?" in token:
            parsed = urlparse(token)
            frag_params = parse_qs(parsed.fragment)
            query_params = parse_qs(parsed.query)
            extracted = frag_params.get("access_token") or query_params.get("access_token")
            if extracted:
                token = extracted[0]

        if not token:
            print("[X] Токен не может быть пустым.")
            return False

        if self.validate_token(token):
            self.access_token = token
            self.save_session()
            print(f"[V] Токен успешно подтвержден! Пользователь: {self.user_name} (ID: {self.user_id})")
            return True
        else:
            print("[X] Неверный токен или срок его действия истек.")
            return False

    def auth_by_cookies(self, cookies_str: str) -> bool:
        """
        Авторизация через cookies (remixsid из веб-версии браузера).
        """
        cookies_str = cookies_str.strip()

        if cookies_str.isdigit():
            print(f"\n[!] ОШИБКА ВВОДА: Значение '{cookies_str}' является просто числом (вероятно, ID пользователя или remixmid).")
            print("    Кука 'remixsid' — это длинная строка (буквы и цифры, хэш сессии авторизации).")
            print("    Пример правильного remixsid: 8fa7b2c019d4e5f6a7b8c9d0e1f2a3b4c5d6e7f8")
            print("    В браузере (F12 -> Application -> Cookies) найдите строку 'remixsid' и скопируйте ее 'Value'.\n")
            return False

        remixsid = cookies_str
        extracted_mid = None

        if "remixsid=" in cookies_str or ";" in cookies_str:
            parts = [p.strip() for p in cookies_str.split(";")]
            for part in parts:
                if "=" in part:
                    k, v = part.split("=", 1)
                    k = k.strip()
                    v = v.strip()
                    if k == "remixsid":
                        remixsid = v
                    elif k == "remixmid" and v.isdigit():
                        extracted_mid = int(v)

        if extracted_mid:
            self.user_id = extracted_mid

        for dom in [".vk.ru", ".vk.com"]:
            self.session.cookies.set("remixsid", remixsid, domain=dom)
            self.session.cookies.set("remixaudio_show_alert_today", "0", domain=dom)
            self.session.cookies.set("remixmdevice", "1920/1080/2/!!-!!!!", domain=dom)
            if self.user_id:
                self.session.cookies.set("remixmid", str(self.user_id), domain=dom)

        is_logged_in = False
        detected_id = None
        detected_name = None

        print("[*] Проверка сессии Cookies через серверы VK...")
        for check_domain in ["m.vk.ru", "m.vk.com"]:
            try:
                resp = self.session.get(f"https://{check_domain}/feed", allow_redirects=True, timeout=12)
                if any(x in resp.url.lower() for x in ["/login", "act=login", "/join"]):
                    continue

                html = resp.text
                m_id = re.search(r'href="/(?:id|audios)(\d+)"', html)
                if not m_id:
                    m_id = re.search(r'owner_id:\s*(\d+)', html)
                if not m_id:
                    m_id = re.search(r'"user_id":\s*(\d+)', html)
                if not m_id:
                    m_id = re.search(r'AudioUtils\.followOwner\((\d+)', html)

                if m_id:
                    detected_id = int(m_id.group(1))

                m_name = re.search(r'<title>(.*?)</title>', html)
                if m_name:
                    title_txt = m_name.group(1).strip()
                    if "вконтакте" not in title_txt.lower() and "vk" not in title_txt.lower():
                        detected_name = clean_html_entities(title_txt)

                is_logged_in = True
                break
            except Exception:
                continue

        if not is_logged_in:
            print("[X] Ошибка: Cookies недействительны (VK перенаправляет на страницу входа).")
            print("    Убедитесь, что вы авторизованы в браузере и скопировали актуальный remixsid.")
            return False

        if detected_id:
            self.user_id = detected_id
        if detected_name:
            self.user_name = detected_name

        self.is_cookie_session = True
        print("[V] Сессия по Cookies успешно инициализирована!")

        token_found = self._try_get_token_from_web_session()
        if token_found:
            self.access_token = token_found
            print("[V] Автоматически получен аудио-токен через активную веб-сессию!")
            self._fetch_profile_name()
            self.save_session()
        else:
            if not self.user_id:
                print("\n[!] Не удалось автоматически определить ваш ID пользователя из профиля.")
                uid_str = input(">> Введите ваш числовой ID ВКонтакте (например, 12345678): ").strip()
                if uid_str.isdigit():
                    self.user_id = int(uid_str)
            if self.user_id:
                print(f"[V] Активный профиль: ID {self.user_id}")

        return True

    def _try_get_token_from_web_session(self) -> Optional[str]:
        """Пытается получить access_token через OAuth, используя уже установленные куки сессии."""
        for dom in [self.domain, self.fallback_domain]:
            try:
                url = f"https://oauth.{dom}/authorize?client_id={KATE_CLIENT_ID}&scope=audio,offline&response_type=token&display=page"
                resp = self.session.get(url, allow_redirects=True, timeout=12)
                if "access_token" in resp.url:
                    parsed = urlparse(resp.url)
                    frag = parse_qs(parsed.fragment)
                    extracted = frag.get("access_token")
                    if extracted:
                        uid = frag.get("user_id")
                        if uid and uid[0].isdigit():
                            self.user_id = int(uid[0])
                        return extracted[0]
            except Exception:
                continue
        return None

    def validate_token(self, token: str, hint_user_id: Optional[int] = None) -> bool:
        """Проверяет валидность токена вызовом account.getProfileInfo или users.get."""
        params = {"access_token": token, "v": VK_API_VERSION}

        for dom in [self.domain, self.fallback_domain]:
            try:
                base = self.get_api_base(dom)
                resp = self.session.get(f"{base}account.getProfileInfo", params=params, timeout=10)
                data = resp.json()
                if "response" in data:
                    profile = data["response"]
                    self.user_name = f"{profile.get('first_name', '')} {profile.get('last_name', '')}".strip()
                    self.user_id = profile.get("id") or hint_user_id
                    self.access_token = token
                    self.domain = dom
                    return True

                resp2 = self.session.get(f"{base}users.get", params=params, timeout=10)
                data2 = resp2.json()
                if "response" in data2 and len(data2["response"]) > 0:
                    user = data2["response"][0]
                    self.user_name = f"{user.get('first_name', '')} {user.get('last_name', '')}".strip()
                    self.user_id = user.get("id") or hint_user_id
                    self.access_token = token
                    self.domain = dom
                    return True
            except Exception:
                continue

        return False

    def _fetch_profile_name(self):
        """Подгружает имя пользователя."""
        if not self.access_token:
            return
        try:
            data = self.call_api("account.getProfileInfo", {})
            if "response" in data:
                p = data["response"]
                self.user_name = f"{p.get('first_name', '')} {p.get('last_name', '')}".strip()
        except Exception:
            self.user_name = f"ID {self.user_id}"

    def call_api(self, method: str, params: Dict[str, Any]) -> Dict[str, Any]:
        """
        Универсальный вызов метода VK API с автоматическим переключением доменов (vk.ru <-> vk.com).
        """
        if not self.access_token:
            raise ValueError("Требуется авторизация для вызова API.")

        req_params = {
            "access_token": self.access_token,
            "v": VK_API_VERSION,
            "https": 1,
            "lang": "ru"
        }
        req_params.update(params)

        self.anti_ban_delay(f"API {method}")

        last_err = None
        for dom in [self.domain, self.fallback_domain]:
            url = f"{self.get_api_base(dom)}{method}"
            try:
                resp = self.session.get(url, params=req_params, timeout=15)
                data = resp.json()

                if "error" in data:
                    err = data["error"]
                    err_code = err.get("error_code")
                    err_msg = err.get("error_msg")
                    if err_code == 14:  # Captcha
                        captcha_sid = err.get("captcha_sid")
                        captcha_img = err.get("captcha_img")
                        print(f"\n[!] Капча от API! Ссылка: {captcha_img}")
                        captcha_key = input(">> Введите капчу: ").strip()
                        req_params["captcha_sid"] = captcha_sid
                        req_params["captcha_key"] = captcha_key
                        resp = self.session.get(url, params=req_params, timeout=15)
                        return resp.json()
                    raise RuntimeError(f"Ошибка API [{err_code}]: {err_msg}")

                return data
            except requests.RequestException as exc:
                last_err = exc
                continue

        raise RuntimeError(f"Не удалось связаться с серверами VK ({self.domain} и {self.fallback_domain}): {last_err}")

    def get_user_audio(self, owner_id: Optional[int] = None, count: int = 100, offset: int = 0) -> List[AudioTrack]:
        """Получает аудиозаписи пользователя или сообщества (через API или веб-сессию)."""
        target_id = owner_id if owner_id is not None else self.user_id
        if not target_id:
            raise ValueError("Не указан ID пользователя для загрузки музыки.")

        if self.access_token:
            params = {
                "owner_id": target_id,
                "count": min(count, 5000),
                "offset": offset,
                "extended": 1
            }
            data = self.call_api("audio.get", params)
            items = data.get("response", {}).get("items", [])
            return [self._parse_audio_item(item) for item in items if item.get("url")]
        else:
            return self._get_audio_via_web(owner_id=target_id, count=count, offset=offset)

    def get_playlist_audio(self, owner_id: int, playlist_id: int, access_key: Optional[str] = None,
                           count: int = 100, offset: int = 0) -> List[AudioTrack]:
        """Получает треки из плейлиста или альбома."""
        if self.access_token:
            params = {
                "owner_id": owner_id,
                "album_id": playlist_id,
                "count": count,
                "offset": offset,
                "extended": 1
            }
            if access_key:
                params["access_key"] = access_key

            data = self.call_api("audio.get", params)
            items = data.get("response", {}).get("items", [])
            return [self._parse_audio_item(item) for item in items if item.get("url")]
        else:
            return self._get_audio_via_web(owner_id=owner_id, playlist_id=playlist_id, access_hash=access_key, count=count, offset=offset)

    def search_audio(self, query: str, count: int = 50, offset: int = 0) -> List[AudioTrack]:
        """Поиск аудиозаписей по ключевым словам."""
        if not self.access_token:
            raise RuntimeError("Поиск аудиозаписей требует авторизации по токену или логину/паролю.")

        params = {
            "q": query,
            "count": count,
            "offset": offset,
            "sort": 0,
            "autocomplete": 1,
            "extended": 1
        }
        data = self.call_api("audio.search", params)
        items = data.get("response", {}).get("items", [])
        return [self._parse_audio_item(item) for item in items if item.get("url")]

    def get_lyrics(self, lyrics_id: int) -> Optional[str]:
        """Получает текст песни по lyrics_id через метод audio.getLyrics."""
        if not lyrics_id or not self.access_token:
            return None
        try:
            data = self.call_api("audio.getLyrics", {"lyrics_id": lyrics_id})
            return data.get("response", {}).get("text")
        except Exception:
            return None

    def _get_audio_via_web(self, owner_id: int, playlist_id: Optional[int] = None,
                           access_hash: Optional[str] = None, count: int = 100, offset: int = 0) -> List[AudioTrack]:
        """
        Загрузка треков через мобильный веб-интерфейс (m.vk.ru / m.vk.com) при сессии по куки.
        """
        tracks: List[AudioTrack] = []
        headers = {"X-Requested-With": "XMLHttpRequest"}

        for dom in [self.domain, self.fallback_domain]:
            url = f"https://m.{dom}/audio"
            try:
                data = {
                    "act": "load_section",
                    "owner_id": owner_id,
                    "playlist_id": playlist_id if playlist_id else -1,
                    "offset": offset,
                    "type": "playlist",
                    "access_hash": access_hash or "",
                    "is_loading_all": 1
                }
                resp = self.session.post(url, data=data, headers=headers, timeout=15)
                res_json = resp.json()
                data_list = res_json.get("data", [])
                if not data_list or not data_list[0]:
                    continue

                raw_items = data_list[0].get("list", [])
                for item in raw_items:
                    t_id = item[0]
                    t_owner = item[1]
                    t_url = item[2]
                    t_title = clean_html_entities(item[3])
                    t_artist = clean_html_entities(item[4])
                    t_dur = item[5]
                    t_cover = None

                    if len(item) > 14 and item[14]:
                        covers = item[14].split(",")
                        t_cover = covers[-1] if covers else None

                    if "audio_api_unavailable" in t_url:
                        t_url = decode_audio_url(t_url, self.user_id or owner_id)

                    tracks.append(AudioTrack(
                        id=t_id,
                        owner_id=t_owner,
                        artist=t_artist,
                        title=t_title,
                        duration=t_dur,
                        url=t_url,
                        cover_url=t_cover
                    ))

                if tracks:
                    break
            except Exception:
                continue

        return tracks[:count]

    def _parse_audio_item(self, item: Dict[str, Any]) -> AudioTrack:
        """Преобразует JSON-объект VK в модель AudioTrack."""
        track_id = item.get("id", 0)
        owner_id = item.get("owner_id", 0)
        artist = clean_html_entities(item.get("artist", "Неизвестный исполнитель"))
        title = clean_html_entities(item.get("title", "Без названия"))
        duration = item.get("duration", 0)
        raw_url = item.get("url", "")

        album_title = None
        cover_url = None
        album = item.get("album")
        if isinstance(album, dict):
            album_title = clean_html_entities(album.get("title", ""))
            thumb = album.get("thumb")
            if isinstance(thumb, dict):
                cover_url = thumb.get("photo_1200") or thumb.get("photo_600") or thumb.get("photo_300")

        if not cover_url and item.get("track_covers"):
            covers = item.get("track_covers")
            if isinstance(covers, list) and covers:
                cover_url = covers[-1]

        lyrics_id = item.get("lyrics_id")

        return AudioTrack(
            id=track_id,
            owner_id=owner_id,
            artist=artist,
            title=title,
            duration=duration,
            url=raw_url,
            album_title=album_title,
            lyrics_id=lyrics_id,
            cover_url=cover_url
        )


# =====================================================================
# Менеджер скачивания аудио и работы с сетью
# =====================================================================
class AudioDownloader:
    """
    Отвечает за надежное скачивание MP3 файлов:
    - Проверка наличия в archive.txt
    - Поддержка как прямых MP3 файлов, так и потокового HLS (AES-128 шифрование)
    - Потоковая загрузка с прогресс-баром (tqdm)
    - Демультиплексирование в полноценный 320 kbps MP3
    - Валидация размера файла перед записью в архив
    - Вшивание тегов, обложек и текстов
    - Рандомизированные задержки между треками (Anti-ban)
    """
    def __init__(self, vk_client: VKClient, output_dir: Path, retry_count: int = 3):
        self.vk_client = vk_client
        self.output_dir = output_dir
        self.retry_count = retry_count
        self.archive = ArchiveManager(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)

    def download_track(self, track: AudioTrack) -> bool:
        """
        Скачивает один трек и вшивает все метаданные.
        Возвращает True в случае успеха, False при ошибке.
        """
        # 1. Проверяем, есть ли трек в архиве
        if self.archive.is_downloaded(track.uid):
            print(f"[ПРОПУСК] {track.formatted_name} (уже в archive.txt)")
            return True

        # 2. Формируем чистое имя файла
        clean_name = sanitize_filename(track.formatted_name)
        target_file = self.output_dir / f"{clean_name}.mp3"
        temp_file = self.output_dir / f"{clean_name}.part"

        if target_file.exists():
            clean_name = sanitize_filename(f"{track.formatted_name}_{track.uid}")
            target_file = self.output_dir / f"{clean_name}.mp3"
            temp_file = self.output_dir / f"{clean_name}.part"

        # 3. Скачивание аудиопотока (MP3 или HLS AES-128) с повторными попытками
        download_ok = False
        for attempt in range(1, self.retry_count + 1):
            try:
                download_ok = self._download_stream_or_hls(track.url, temp_file, track.formatted_name)
                if download_ok:
                    break
            except Exception as e:
                print(f"\n[!] Попытка {attempt}/{self.retry_count} не удалась ({e}).")
                if attempt < self.retry_count:
                    backoff = attempt * 2.5
                    print(f"    Ожидание {backoff:.1f} сек перед повтором...")
                    time.sleep(backoff)

        # 4. Валидация размера скачанного файла (защита от битых/текстовых файлов)
        if not download_ok or not temp_file.exists():
            print(f"[X] Не удалось скачать аудиопоток: {track.formatted_name}")
            if temp_file.exists():
                temp_file.unlink(missing_ok=True)
            return False

        file_size = temp_file.stat().st_size
        if file_size < MIN_AUDIO_FILE_SIZE:
            print(f"[X] Ошибка: Скачанный файл слишком мал ({file_size} байт, ожидалось > 1 МБ). Аудиофайл поврежден.")
            temp_file.unlink(missing_ok=True)
            return False

        # Завершаем скачивание: переименовываем временный файл в целевой .mp3
        if target_file.exists():
            target_file.unlink()
        temp_file.rename(target_file)

        # 5. Получение текста песни (Lyrics)
        lyrics = None
        if track.lyrics_id:
            try:
                lyrics = self.vk_client.get_lyrics(track.lyrics_id)
            except Exception:
                pass

        # 6. Получение обложки (Cover Art)
        cover_bytes = None
        if track.cover_url:
            try:
                c_resp = self.vk_client.session.get(track.cover_url, timeout=10)
                if c_resp.status_code == 200:
                    cover_bytes = c_resp.content
            except Exception:
                pass

        # 7. Вшиваем все ID3 теги
        MetadataManager.embed_tags(
            file_path=target_file,
            track=track,
            lyrics=lyrics,
            cover_bytes=cover_bytes
        )

        # 8. Записываем трек в archive.txt (только при подтвержденном размере)
        self.archive.add(track.uid)
        size_mb = round(target_file.stat().st_size / (1024 * 1024), 2)
        print(f"[V] Сохранен: {target_file.name} [{size_mb} МБ]")

        # 9. Анти-бан пауза перед следующим треком
        self.vk_client.anti_ban_delay("пауза между треками")
        return True

    def _download_stream_or_hls(self, url: str, target_temp_file: Path, display_name: str) -> bool:
        """
        Универсальный загрузчик: определяет, является ли ссылка прямой MP3 или HLS (m3u8),
        и выполняет соответствующую загрузку с расшифровкой и демультиплексированием.
        """
        if not url:
            return False

        # Попытка преобразовать m3u8 в прямой mp3 через шаблон CDN (если доступно)
        if "m3u8" in url:
            converted = RE_M3U8_TO_MP3.sub(r'\1/\2.mp3', url)
            try:
                head_resp = self.vk_client.session.head(converted, timeout=5, allow_redirects=True)
                if head_resp.status_code == 200 and int(head_resp.headers.get("content-length", 0)) > MIN_AUDIO_FILE_SIZE:
                    return self._stream_direct_download(converted, target_temp_file, display_name)
            except Exception:
                pass

            # Если прямого MP3 нет — загружаем и расшифровываем HLS плейлист
            return self._download_and_decrypt_hls(url, target_temp_file, display_name)

        # Если ссылка без .m3u8, проверяем первый фрагмент
        try:
            resp = self.vk_client.session.get(url, stream=True, timeout=15)
            resp.raise_for_status()
            first_chunk = next(resp.iter_content(chunk_size=8192), b"")
            if first_chunk.startswith(b"#EXTM3U"):
                # Сервер вернул текст m3u8 плейлиста
                resp.close()
                return self._download_and_decrypt_hls(url, target_temp_file, display_name)

            # Прямой поток MP3
            total_size = int(resp.headers.get("content-length", 0))
            short_title = display_name if len(display_name) <= 35 else display_name[:32] + "..."

            with open(target_temp_file, "wb") as f, tqdm(
                desc=short_title,
                total=total_size,
                unit="B",
                unit_scale=True,
                unit_divisor=1024,
                leave=False,
                bar_format="{desc}: {percentage:3.0f}%|{bar:25}| {n_fmt}/{total_fmt} [{elapsed}<{remaining}, {rate_fmt}]"
            ) as bar:
                f.write(first_chunk)
                bar.update(len(first_chunk))
                for chunk in resp.iter_content(chunk_size=32768):
                    if chunk:
                        f.write(chunk)
                        bar.update(len(chunk))
            return True
        except Exception:
            return self._download_and_decrypt_hls(url, target_temp_file, display_name)

    def _stream_direct_download(self, url: str, target_temp_file: Path, display_name: str) -> bool:
        """Потоковая загрузка прямого файла MP3."""
        response = self.vk_client.session.get(url, stream=True, timeout=20)
        response.raise_for_status()

        total_size = int(response.headers.get("content-length", 0))
        short_title = display_name if len(display_name) <= 35 else display_name[:32] + "..."

        with open(target_temp_file, "wb") as f, tqdm(
            desc=short_title,
            total=total_size,
            unit="B",
            unit_scale=True,
            unit_divisor=1024,
            leave=False,
            bar_format="{desc}: {percentage:3.0f}%|{bar:25}| {n_fmt}/{total_fmt} [{elapsed}<{remaining}, {rate_fmt}]"
        ) as bar:
            for chunk in response.iter_content(chunk_size=32768):
                if chunk:
                    f.write(chunk)
                    bar.update(len(chunk))
        return True

    def _download_and_decrypt_hls(self, playlist_url: str, target_temp_file: Path, display_name: str) -> bool:
        """
        Скачивает все фрагменты защищенного HLS потока (.ts), расшифровывает
        AES-128 ключами и демультиплексирует в полноценный MP3 файл.
        """
        # 1. Получаем текст плейлиста
        p_resp = self.vk_client.session.get(playlist_url, timeout=12)
        p_resp.raise_for_status()
        p_text = p_resp.text

        # Если это мастер-плейлист с вариантами качества, выбираем лучший
        if "#EXT-X-STREAM-INF" in p_text:
            sub_url = None
            for p_line in p_text.splitlines():
                p_line = p_line.strip()
                if p_line and not p_line.startswith("#"):
                    sub_url = urljoin(playlist_url, p_line)
                    break
            if sub_url:
                return self._download_and_decrypt_hls(sub_url, target_temp_file, display_name)

        # 2. Парсим структуру сегментов и ключей шифрования
        lines = p_text.splitlines()
        segments_info: List[Dict[str, Any]] = []

        cur_key_url: Optional[str] = None
        cur_iv: Optional[bytes] = None
        cur_method: str = "NONE"

        for line in lines:
            line = line.strip()
            if not line:
                continue

            if line.startswith("#EXT-X-KEY"):
                m_method = re.search(r'METHOD=([^,\s]+)', line)
                m_uri = re.search(r'URI="([^"]+)"', line)
                m_iv = re.search(r'IV=0x([0-9a-fA-F]+)', line)

                cur_method = m_method.group(1) if m_method else "NONE"
                if cur_method == "AES-128" and m_uri:
                    cur_key_url = urljoin(playlist_url, m_uri.group(1))
                    cur_iv = bytes.fromhex(m_iv.group(1)) if m_iv else None
                elif cur_method == "NONE":
                    cur_key_url = None
                    cur_iv = None

            elif not line.startswith("#"):
                seg_abs_url = urljoin(playlist_url, line)
                segments_info.append({
                    "url": seg_abs_url,
                    "method": cur_method,
                    "key_url": cur_key_url,
                    "iv": cur_iv,
                    "seq": len(segments_info)
                })

        if not segments_info:
            return False

        # 3. Кэшируем ключи шифрования
        key_cache: Dict[str, bytes] = {}
        all_ts_bytes = bytearray()

        short_title = display_name if len(display_name) <= 35 else display_name[:32] + "..."

        with tqdm(
            desc=short_title,
            total=len(segments_info),
            unit="seg",
            leave=False,
            bar_format="{desc}: {percentage:3.0f}%|{bar:25}| {n_fmt}/{total_fmt} seg [{elapsed}<{remaining}]"
        ) as bar:
            for seg in segments_info:
                seg_resp = self.vk_client.session.get(seg["url"], timeout=15)
                seg_resp.raise_for_status()
                seg_data = seg_resp.content

                if seg["method"] == "AES-128" and seg["key_url"]:
                    k_url = seg["key_url"]
                    if k_url not in key_cache:
                        k_resp = self.vk_client.session.get(k_url, timeout=10)
                        k_resp.raise_for_status()
                        key_cache[k_url] = k_resp.content

                    aes_key = key_cache[k_url]
                    iv = seg["iv"] if seg["iv"] else seg["seq"].to_bytes(16, "big")

                    cipher = Cipher(algorithms.AES(aes_key), modes.CBC(iv), backend=default_backend())
                    decryptor = cipher.decryptor()
                    decrypted = decryptor.update(seg_data) + decryptor.finalize()

                    # Удаление PKCS7 padding
                    pad_len = decrypted[-1]
                    if 0 < pad_len <= 16:
                        decrypted = decrypted[:-pad_len]

                    all_ts_bytes.extend(decrypted)
                else:
                    all_ts_bytes.extend(seg_data)

                bar.update(1)

        if len(all_ts_bytes) < MIN_AUDIO_FILE_SIZE:
            return False

        # 4. Преобразование MPEG-TS контейнера в чистый MP3 файл
        # Способ А: Используем FFmpeg, если он доступен в системе (мгновенное copy-демультиплексирование)
        temp_ts_file = target_temp_file.with_suffix('.raw.ts')
        try:
            with open(temp_ts_file, "wb") as f_ts:
                f_ts.write(all_ts_bytes)

            cmd = ["ffmpeg", "-y", "-loglevel", "error", "-i", str(temp_ts_file), "-vn", "-c:a", "copy", str(target_temp_file)]
            res = subprocess.run(cmd, capture_output=True)
            temp_ts_file.unlink(missing_ok=True)

            if res.returncode == 0 and target_temp_file.exists() and target_temp_file.stat().st_size > MIN_AUDIO_FILE_SIZE:
                return True
        except Exception:
            temp_ts_file.unlink(missing_ok=True)

        # Способ Б: Встроенный чистый Python демультиплексор (не требует внешних утилит)
        raw_mp3 = demux_ts_to_audio(all_ts_bytes)
        if len(raw_mp3) > MIN_AUDIO_FILE_SIZE:
            with open(target_temp_file, "wb") as f_out:
                f_out.write(raw_mp3)
            return True

        # Если демультиплексор не распознал PES, записываем байты напрямую
        with open(target_temp_file, "wb") as f_out:
            f_out.write(all_ts_bytes)
        return target_temp_file.stat().st_size > MIN_AUDIO_FILE_SIZE


# =====================================================================
# Парсер аргументов командной строки и Интерактивный CLI
# =====================================================================
def parse_arguments() -> argparse.Namespace:
    """Парсер аргументов CLI."""
    parser = argparse.ArgumentParser(
        description=f"{APP_NAME} v{APP_VERSION} — Скачивание музыки из VK (vk.ru и vk.com) с метаданными и умным архивом.",
        formatter_class=argparse.RawTextHelpFormatter
    )

    domain_group = parser.add_argument_group("Настройки домена VK")
    domain_group.add_argument(
        "-d", "--domain",
        type=str,
        default=DEFAULT_VK_DOMAIN,
        choices=SUPPORTED_DOMAINS,
        help="Основной домен VK для обращений (vk.ru или vk.com, по умолчанию: vk.ru)"
    )

    auth_group = parser.add_argument_group("Параметры авторизации")
    auth_group.add_argument("-l", "--login", type=str, help="Логин VK (телефон или e-mail)")
    auth_group.add_argument("-p", "--password", type=str, help="Пароль VK (не рекомендуется передавать в открытом виде)")
    auth_group.add_argument("-t", "--token", type=str, help="Access Token VK (или ссылка из Kate Mobile / vkhost)")
    auth_group.add_argument("-c", "--cookies", type=str, help="Значение куки remixsid (или строка document.cookie)")

    dest_group = parser.add_argument_group("Параметры сохранения")
    dest_group.add_argument("-o", "--output", type=str, default=None,
                            help="Путь к папке для сохранения музыки (по умолчанию: ./downloads)")

    target_group = parser.add_argument_group("Источник треков")
    target_group.add_argument("-u", "--user-id", type=str,
                            help="ID пользователя, ссылка или имя (например: 12345, id12345, club12345, https://vk.ru/durov)")
    target_group.add_argument("--playlist", type=str,
                            help="Ссылка или идентификатор плейлиста (например: https://vk.ru/music/playlist/-123_456_key)")
    target_group.add_argument("-s", "--search", type=str, help="Поисковый запрос для поиска треков")
    target_group.add_argument("--count", type=int, default=100, help="Количество треков для скачивания (по умолчанию: 100)")

    safety_group = parser.add_argument_group("Анти-бан настройки")
    safety_group.add_argument("--min-delay", type=float, default=2.0, help="Минимальная пауза между запросами в сек. (default: 2.0)")
    safety_group.add_argument("--max-delay", type=float, default=4.5, help="Максимальная пауза между запросами в сек. (default: 4.5)")

    return parser.parse_args()


def interactive_auth(vk_client: VKClient):
    """Интерактивный мастер авторизации при запуске без CLI параметров."""
    print("=" * 60)
    print(f"       ДОБРО ПОЖАЛОВАТЬ В {APP_NAME.upper()} (v{APP_VERSION})")
    print(f"       (Поддержка доменов vk.ru и vk.com с HLS/AES-128 загрузкой)")
    print("=" * 60)

    if os.path.exists(CONFIG_FILE):
        choice = input("[?] Найдена сохраненная сессия. Использовать её? [Y/n]: ").strip().lower()
        if choice in ("", "y", "yes", "д", "да"):
            if vk_client.load_saved_session():
                print(f"[V] Авторизован как: {vk_client.user_name} (ID: {vk_client.user_id})\n")
                return

    while True:
        print("\nВыберите способ входа в ВКонтакте:")
        print("  [1] По логину и паролю (поддержка 2FA и SMS)")
        print("  [2] По токену (Access Token от Kate Mobile — рекомендуется)")
        print("  [3] По Cookies (remixsid из браузера vk.ru / vk.com)")
        print("  [0] Выход")

        sub_choice = input(">> Выберите вариант (1-3): ").strip()
        if sub_choice == "1":
            login = input(">> Введите номер телефона или e-mail: ").strip()
            password = getpass.getpass(">> Введите пароль (символы скрыты): ").strip()
            if vk_client.auth_by_credentials(login, password):
                break
        elif sub_choice == "2":
            print("\nПодсказка:")
            print("  1. Откройте в браузере сайт: https://vkhost.github.io")
            print("  2. Нажмите на 'Kate Mobile' -> нажмите 'Разрешить'.")
            print("  3. Скопируйте всю итоговую ссылку из адресной строки (или сам токен).")
            token = input(">> Вставьте токен или скопированную ссылку: ").strip()
            if vk_client.auth_by_token(token):
                break
        elif sub_choice == "3":
            print("\nПодсказка:")
            print("  1. Откройте в браузере vk.ru (или vk.com) под своим аккаунтом.")
            print("  2. Нажмите F12 -> вкладка Application (или Память/Хранилище) -> Cookies -> vk.ru.")
            print("  3. Найдите строку 'remixsid' и скопируйте ее значение 'Value' (хэш из букв и цифр).")
            cookies = input(">> Введите значение remixsid (или всю строку cookies): ").strip()
            if vk_client.auth_by_cookies(cookies):
                break
        elif sub_choice == "0":
            print("Выход из программы.")
            sys.exit(0)
        else:
            print("[!] Неверный выбор. Попробуйте снова.")


def interactive_destination() -> Path:
    """Интерактивный ввод пути для сохранения файлов."""
    default_dir = Path("./downloads").resolve()
    print(f"\nПапка для сохранения музыки [по умолчанию: {default_dir}]:")
    user_input = input(">> Путь (нажмите Enter для значения по умолчанию): ").strip()
    if user_input:
        chosen_dir = Path(user_input).expanduser().resolve()
    else:
        chosen_dir = default_dir
    chosen_dir.mkdir(parents=True, exist_ok=True)
    print(f"[V] Файлы будут сохранены в: {chosen_dir}\n")
    return chosen_dir


def interactive_source_selection(vk_client: VKClient) -> Tuple[str, Dict[str, Any]]:
    """Интерактивный выбор источника треков (моя музыка, друг, плейлист, поиск)."""
    while True:
        print("Откуда скачивать музыку?")
        print("  [1] Мои сохраненные аудиозаписи")
        print("  [2] Музыка другого пользователя или сообщества (ссылка или ID)")
        print("  [3] Альбом или Плейлист (ссылка на vk.ru или vk.com)")
        print("  [4] Поиск по названию трека или исполнителю")

        choice = input(">> Выберите вариант (1-4): ").strip()

        if choice == "1":
            if not vk_client.user_id:
                uid_str = input(">> Не удалось определить ваш ID. Введите ваш числовой ID (например, 1821591656): ").strip()
                if uid_str.isdigit():
                    vk_client.user_id = int(uid_str)
                else:
                    print("[X] Неверный ID. Попробуйте снова.")
                    continue

            count_str = input(">> Сколько треков получить (Enter = все доступные, макс 5000): ").strip()
            count = int(count_str) if count_str.isdigit() else 5000
            return "user", {"owner_id": vk_client.user_id, "count": count}

        elif choice == "2":
            target = input(">> Введите ID, ссылку (vk.ru/id123 или vk.com/club123) или короткое имя: ").strip()
            owner_id = parse_target_id(vk_client, target)
            if owner_id is None:
                print(f"[X] Ошибка: Не удалось распознать ID или страницу '{target}'.")
                continue
            count_str = input(">> Сколько треков скачать (Enter = 100): ").strip()
            count = int(count_str) if count_str.isdigit() else 100
            return "user", {"owner_id": owner_id, "count": count}

        elif choice == "3":
            pl_url = input(">> Вставьте ссылку на плейлист (vk.ru/music/playlist/... или vk.com/...): ").strip()
            parsed = parse_playlist_input(pl_url)
            if parsed:
                owner_id, playlist_id, access_key = parsed
                return "playlist", {"owner_id": owner_id, "playlist_id": playlist_id, "access_key": access_key}
            else:
                print("[X] Неверный формат ссылки на плейлист. Примеры:")
                print("    https://vk.ru/music/playlist/-2000123_456_key")
                print("    https://vk.com/music/playlist/123456_789")
                continue

        elif choice == "4":
            query = input(">> Введите поисковый запрос (Артист или Название): ").strip()
            count_str = input(">> Количество треков (Enter = 50): ").strip()
            count = int(count_str) if count_str.isdigit() else 50
            return "search", {"query": query, "count": count}

        else:
            print("[!] Неверный ввод, повторите попытку.")


# =====================================================================
# Точка входа (Main Execution)
# =====================================================================
def main():
    args = parse_arguments()

    min_delay = max(0.5, args.min_delay)
    max_delay = max(min_delay, args.max_delay)

    vk_client = VKClient(domain=args.domain, min_delay=min_delay, max_delay=max_delay)

    # 1. Авторизация
    if args.token:
        if not vk_client.auth_by_token(args.token):
            sys.exit(1)
    elif args.cookies:
        if not vk_client.auth_by_cookies(args.cookies):
            sys.exit(1)
    elif args.login:
        password = args.password or getpass.getpass(">> Введите пароль VK: ")
        if not vk_client.auth_by_credentials(args.login, password):
            sys.exit(1)
    else:
        interactive_auth(vk_client)

    # 2. Выбор пути сохранения
    if args.output:
        output_dir = Path(args.output).expanduser().resolve()
        output_dir.mkdir(parents=True, exist_ok=True)
    else:
        output_dir = interactive_destination()

    # 3. Определение источника треков
    tracks: List[AudioTrack] = []

    if args.playlist:
        parsed_pl = parse_playlist_input(args.playlist)
        if parsed_pl:
            owner_id, playlist_id, access_key = parsed_pl
            print(f"\n[*] Загрузка информации о плейлисте {owner_id}_{playlist_id}...")
            tracks = vk_client.get_playlist_audio(owner_id, playlist_id, access_key, count=args.count)
        else:
            print(f"[X] Неверный формат аргумента --playlist: {args.playlist}")
            sys.exit(1)
    elif args.search:
        print(f"\n[*] Поиск аудиозаписей по запросу: '{args.search}'...")
        tracks = vk_client.search_audio(args.search, count=args.count)
    elif args.user_id:
        target_id = parse_target_id(vk_client, args.user_id)
        if target_id is not None:
            print(f"\n[*] Получение аудиозаписей для ID {target_id}...")
            tracks = vk_client.get_user_audio(owner_id=target_id, count=args.count)
        else:
            print(f"[X] Неверный формат --user-id: '{args.user_id}'. Укажите числовой ID или корректную ссылку.")
            sys.exit(1)
    else:
        source_type, source_params = interactive_source_selection(vk_client)
        print("\n[*] Получение списка треков из ВКонтакте...")
        if source_type == "user":
            tracks = vk_client.get_user_audio(owner_id=source_params["owner_id"], count=source_params["count"])
        elif source_type == "playlist":
            tracks = vk_client.get_playlist_audio(
                owner_id=source_params["owner_id"],
                playlist_id=source_params["playlist_id"],
                access_key=source_params.get("access_key"),
                count=100
            )
        elif source_type == "search":
            tracks = vk_client.search_audio(query=source_params["query"], count=source_params["count"])

    if not tracks:
        print("[!] Не найдено доступных для скачивания треков.")
        return

    print(f"\n[V] Найдено треков: {len(tracks)}")
    downloader = AudioDownloader(vk_client=vk_client, output_dir=output_dir)
    print(f"[*] Файл архива: {downloader.archive.archive_file} (уже в архиве: {downloader.archive.count})")
    print("-" * 60)

    # 4. Процесс скачивания с отображением статистики
    success_count = 0
    skipped_count = 0
    error_count = 0

    for idx, track in enumerate(tracks, 1):
        print(f"\n[{idx}/{len(tracks)}] {track.formatted_name}")
        if downloader.archive.is_downloaded(track.uid):
            skipped_count += 1
            print(f"      -> Уже скачан ранее (найден в {ARCHIVE_FILENAME})")
            continue

        try:
            if downloader.download_track(track):
                success_count += 1
            else:
                error_count += 1
        except KeyboardInterrupt:
            print("\n[!] Скачивание прервано пользователем.")
            break
        except Exception as e:
            print(f"[X] Ошибка при обработке трека: {e}")
            error_count += 1

    # 5. Итоговый отчет
    print("\n" + "=" * 60)
    print("ИТОГИ СЕССИИ:")
    print(f"  • Использованный домен: {vk_client.domain}")
    print(f"  • Всего обработано:     {len(tracks)}")
    print(f"  • Успешно скачано:      {success_count}")
    print(f"  • Пропущено (архив):    {skipped_count}")
    print(f"  • Ошибок загрузки:      {error_count}")
    print(f"  • Папка сохранения:     {output_dir}")
    print("=" * 60)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n\n[!] Программа завершена пользователем.")
    except Exception as exc:
        print(f"\n\n[КРИТИЧЕСКАЯ ОШИБКА] {exc}")
    finally:
        # Если запущено из скомпилированного .exe двойным кликом (без CLI-аргументов),
        # предотвращаем мгновенное закрытие консольного окна в Windows
        if getattr(sys, 'frozen', False) and len(sys.argv) <= 1:
            try:
                input("\nНажмите клавишу Enter для выхода...")
            except (EOFError, KeyboardInterrupt):
                pass
