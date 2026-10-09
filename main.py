# -*- coding: utf-8 -*-
"""
============================================================================
 Program: Yalla Team EG - Inline Translator (Arabic <-> English)
============================================================================
How it works:
    1) The program opens a normal window showing its current state and a
       live list of notifications (problems, failed translations, and the
       QUICK FIX for each one: try again / restart / open Settings).
       Pressing "Minimize to tray" - or the window's X button - hides it
       down next to the clock, where it keeps working in the background;
       clicking the tray icon brings the window back.
    2) While you type Arabic anywhere (browser, Telegram, Word, etc.),
       it keeps a small in-memory buffer of the current Arabic SENTENCE
       (letters AND spaces between words, so you can type a full
       sentence normally - nothing is logged or saved to disk/network).
    3) The moment you press the trigger key (F3 by default):
         - it checks whether the buffered text contains Arabic
         - if yes: it simulates exactly len(buffer) Backspace presses
           to erase the whole Arabic sentence, translates it in one
           request via the 'translators' library, and types the
           English result in its place.
         - if no (buffer empty or no Arabic in it): it does nothing
    4) The buffer resets automatically on Ctrl/Alt/Windows combos,
       Enter, arrow keys, Tab, or any character that is neither Arabic
       nor a space, so it never touches unrelated text.
    5) Right-click the tray icon for a menu: Enable/Disable, Settings
       (change the trigger key or translation engine), and Exit.

Required libraries: see the attached requirements.txt file.

WHY 'translators' AND NOT 'googletrans':
    googletrans==4.0.0-rc1 depends on Python's old built-in 'cgi'
    module, which was removed starting with Python 3.13. 'translators'
    has no such dependency and works normally on Python 3.14.

IMPORTANT LIMITATIONS (please read):
    - This relies on the 'keyboard' library reading the character that
      your OS produces for each key, based on the ACTIVE KEYBOARD
      LAYOUT at the moment you type. Make sure your Arabic keyboard
      layout is selected while typing Arabic for this to work reliably.
    - Because translation happens over the network, there is a short
      delay (usually under a second) between pressing the trigger key
      and the sentence being replaced. Avoid typing more characters
      during that brief window, or the Backspace correction can land
      in the wrong place.
    - This program only ever holds the CURRENT sentence in memory to
      decide whether to translate it. It does not log, store, or
      transmit your keystrokes anywhere - it is not a keylogger.
    - Requires running as Administrator on Windows so the 'keyboard'
      library can capture and simulate keys system-wide.
============================================================================
"""

import sys
import os
import json
import re
import time
import queue
import threading
import ctypes
import webbrowser
import traceback
import urllib.request
import urllib.error
from datetime import datetime

try:
    import winreg  # Windows only - used for the "Start with Windows" toggle
except ImportError:
    winreg = None

# ---------------------------------------------------------------------
# Force UTF-8 output on the console whenever possible, and make sure
# printing never crashes the program even if the console still can't
# render a particular character.
# ---------------------------------------------------------------------
try:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")
except Exception:
    pass


def safe_print(message: str):
    """Print a message to the console without ever crashing the program."""
    try:
        print(message)
    except Exception:
        try:
            print(message.encode("ascii", errors="replace").decode("ascii"))
        except Exception:
            pass


# ---------------------------------------------------------------------
# Import third-party libraries.
# 'keyboard', 'pystray' and 'PIL' are genuinely required and are
# wrapped in try/except. 'translators' is imported directly (no custom
# message) so that any real failure shows Python's own error instead
# of a hardcoded one.
# ---------------------------------------------------------------------
try:
    import keyboard  # System-wide key monitoring and key simulation
except ImportError:
    safe_print("ERROR: 'keyboard' library is not installed. Run: pip install -r requirements.txt")
    sys.exit(1)

try:
    import tkinter as tk
    from tkinter import ttk
    import tkinter.messagebox as _tk_messagebox  # Windows' own dialogs: only a fallback
except ImportError:
    safe_print("ERROR: tkinter is not available (it normally ships with Python by default).")
    sys.exit(1)

try:
    import pystray  # System tray icon and right-click menu
except ImportError:
    safe_print("ERROR: 'pystray' library is not installed. Run: pip install -r requirements.txt")
    sys.exit(1)

try:
    from PIL import Image, ImageDraw  # Used to draw the tray icon
except ImportError:
    safe_print("ERROR: 'Pillow' library is not installed. Run: pip install -r requirements.txt")
    sys.exit(1)

import translators as ts  # Arabic -> English translation (no 'cgi' dependency)

# 'anthropic' is OPTIONAL: only needed if the user chooses the "claude"
# engine from Settings. We don't hard-fail the whole program if it's
# missing, since the free 'translators' engines still work without it.
try:
    from anthropic import Anthropic
    _ANTHROPIC_AVAILABLE = True
except ImportError:
    _ANTHROPIC_AVAILABLE = False

# 'google-genai' is also OPTIONAL: only needed if the user chooses the
# "gemini" engine from Settings. We don't hard-fail the whole program
# if it's missing, since the free 'translators' engines still work
# without it.
# NOTE: the older 'google-generativeai' package is deprecated by Google
# and no longer receiving updates - this uses the new unified SDK
# ('pip install google-genai'), imported as 'from google import genai'.
try:
    from google import genai
    _GEMINI_AVAILABLE = True
except ImportError:
    _GEMINI_AVAILABLE = False

# 'deepl' is also OPTIONAL: only needed if the user chooses the
# "deepl" engine from Settings. We don't hard-fail the whole program
# if it's missing, since the free 'translators' engines still work
# without it. DeepL has a free tier (500,000 chars/month) - the same
# API key works whether you're on Free or Pro.
try:
    import deepl
    _DEEPL_AVAILABLE = True
except ImportError:
    _DEEPL_AVAILABLE = False


# ---------------------------------------------------------------------
# Editable settings (can also be changed at runtime from the Settings
# window, opened via the tray icon menu)
# ---------------------------------------------------------------------
# Typing-speed profiles: how long to wait between each simulated
# keypress when typing out the translation. Faster is snappier, but
# some apps/games/emulators (BlueStacks, MSI App Player, etc.) drop or
# scramble keystrokes if they arrive too fast - "safe" trades speed
# for reliability in those cases.
# The display name of the program: used in the window title, the tray
# icon tooltip, every notification and the startup banner. The saved
# settings folder and the "Start with Windows" registry entry keep
# their old internal names on purpose, so renaming the program does
# NOT lose your saved hotkeys/API keys or leave a dead startup entry.
APP_NAME = "Yalla Team EG"

# ---------------------------------------------------------------------
# Auto-update. APP_VERSION is THIS build's version: raise it by hand
# every time you build a new Setup (e.g. "1.0.1"), and put the same
# number in version.json on GitHub when you publish that build.
# At startup (and every few hours) the program reads UPDATE_INFO_URL;
# if the version there is higher than APP_VERSION it ASKS the user,
# and only after a "Yes" downloads and runs the new Setup.
# version.json format:
#   {"version": "1.0.1", "url": "https://github.com/.../YallaTeam_Setup.exe",
#    "notes": "optional: what is new"}
# ---------------------------------------------------------------------
APP_VERSION = "1.0.7"
UPDATE_INFO_URL = "https://raw.githubusercontent.com/hossamadel00-ui/yalla-team-eg/main/version.json"
UPDATE_CHECK_TIMEOUT_SECONDS = 10
UPDATE_DOWNLOAD_TIMEOUT_SECONDS = 60
UPDATE_CHECK_INTERVAL_HOURS = 6

TYPING_SPEED_PRESETS = {
    "turbo": 0.002,   # very fast - regular desktop apps, browsers, editors
    "normal": 0.01,   # default - good balance for general use
    "safe": 0.03,     # slower but reliable - games/emulators that drop fast input
}
DEFAULT_TYPING_SPEED_PROFILE = "normal"

# Set this to True temporarily to print every key the program reads,
# and what it decides to do with it. This is the fastest way to find
# out WHY nothing is happening: it shows you exactly whether Arabic
# letters are being recognized as Arabic at all. Set back to False
# once things are working, to keep the console output clean.
DEBUG_MODE = False

# Preset trigger-key choices shown in the Settings window. You can also
# type a custom one (e.g. "ctrl+alt+space") in the settings window.
# Includes every F-key (F1-F12) and every number-row digit combined
# with Alt (Alt+1 ... Alt+9, Alt+0), as requested, in addition to the
# original presets.
HOTKEY_PRESETS = [
    "scroll lock",
    "f1", "f2", "f3", "f4", "f5", "f6", "f7", "f8", "f9", "f10", "f11", "f12",
    "alt+1", "alt+2", "alt+3", "alt+4", "alt+5", "alt+6", "alt+7", "alt+8", "alt+9", "alt+0",
    "ctrl+alt+space",
]

# Engines supported by the 'translators' library that work well for ar->en,
# plus "claude" (Anthropic API), "gemini" (Google Generative AI), "deepl"
# (DeepL API) and "custom" (any OpenAI-compatible AI provider - OpenAI,
# OpenRouter, Groq, DeepSeek, Mistral, a local Ollama/LM Studio server,
# etc.), which all require your own API key - see CONFIG_FILE_PATH below.
# "claude" and "gemini" are pay-as-you-go; "deepl" has a free tier
# (500,000 characters/month) as well as a paid Pro tier - either key
# works here. "custom" needs no code changes ever - see
# _translate_via_custom_ai() below.
ENGINE_PRESETS = ["google", "bing", "baidu", "argos", "claude", "gemini", "deepl", "custom"]
CLAUDE_MODEL = "claude-haiku-4-5-20251001"  # cheapest current model, plenty for translation
GEMINI_MODEL = "gemini-3.5-flash-lite"  # current GA model, fast & cheap, available to new API keys

# ---------------------------------------------------------------------
# Target language: the "other side" of the Arabic <-> X pair used by
# the trigger key (F3), the popup mode, and the auto-detected
# Select-translate key. Defaults to English (the program's original
# behavior) but can be changed from Settings -> General to translate
# Arabic into any of these instead - no code changes needed.
# Each entry is (language_code, display_name). The codes are plain
# ISO-639-1 codes, understood by every engine below (the free
# 'translators' engines, DeepL, and the AI engines, which are given
# the display name in their prompt instead of the raw code).
# ---------------------------------------------------------------------
TARGET_LANGUAGE_PRESETS = [
    ("en", "English"),
    ("fr", "French"),
    ("de", "German"),
    ("es", "Spanish"),
    ("it", "Italian"),
    ("pt", "Portuguese"),
    ("nl", "Dutch"),
    ("tr", "Turkish"),
    ("ru", "Russian"),
    ("fa", "Persian (Farsi)"),
    ("ur", "Urdu"),
    ("hi", "Hindi"),
    ("zh", "Chinese"),
    ("ja", "Japanese"),
    ("ko", "Korean"),
    ("he", "Hebrew"),
    ("id", "Indonesian"),
    ("sw", "Swahili"),
]
TARGET_LANGUAGE_CODE_TO_NAME = dict(TARGET_LANGUAGE_PRESETS)
TARGET_LANGUAGE_NAME_TO_CODE = {name: code for code, name in TARGET_LANGUAGE_PRESETS}
TARGET_LANGUAGE_NAMES = [name for _code, name in TARGET_LANGUAGE_PRESETS]
DEFAULT_TARGET_LANGUAGE = "en"

# How long (seconds) to wait for a translation before giving up and
# showing an error. WITHOUT this, a stalled network call to a
# translation engine (google/bing/baidu via 'translators', or the
# claude/gemini APIs) has NO timeout at all and can hang for several
# minutes relying on the OS's own TCP timeout - this is what causes
# the "sometimes it takes 5 minutes" symptom. Every translation call
# below is wrapped so it never waits longer than this.
TRANSLATION_TIMEOUT_SECONDS = 20

# Shorter timeout used for the "Test connection" / "Fetch models"
# buttons in the custom-provider editor - these are quick sanity
# checks the user is actively waiting on inside a modal window, so
# they should fail fast rather than hang for the full 8 seconds.
TEST_CONNECTION_TIMEOUT_SECONDS = 6

# ---------------------------------------------------------------------
# Where settings are stored: a small local JSON file OUTSIDE this
# source file, in the user's own AppData folder. This means nothing
# sensitive is hardcoded in main.py, and the trigger key / engine you
# pick in Settings survive closing and reopening the program.
# ---------------------------------------------------------------------
CONFIG_DIR = os.path.join(os.environ.get("APPDATA", os.path.expanduser("~")), "ArEnTranslator")
CONFIG_FILE_PATH = os.path.join(CONFIG_DIR, "config.json")

# ---------------------------------------------------------------------
# A persistent log file, in the same folder as config.json, so that
# problems are still visible after the program (and its in-window
# notification list) has been closed and reopened. Only the last
# LOG_RETENTION_DAYS days are kept - _trim_log_file() below drops
# anything older so the file never grows forever.
# ---------------------------------------------------------------------
LOG_FILE_PATH = os.path.join(CONFIG_DIR, "log.txt")
LOG_RETENTION_DAYS = 7
LOG_TIMESTAMP_FORMAT = "%Y-%m-%d %H:%M:%S"
_log_file_lock = threading.Lock()
_log_file_append_count = 0

# ---------------------------------------------------------------------
# Favorites: translations the user starred with the ⭐ button next to
# a "Translations" notification, stored in their own small JSON file
# (also in CONFIG_DIR) so they survive closing and reopening the
# program. Clicking a favorite later copies it to the clipboard (it is
# never auto-typed - the user pastes it wherever they want).
# ---------------------------------------------------------------------
FAVORITES_FILE_PATH = os.path.join(CONFIG_DIR, "favorites.json")
_favorites_lock = threading.Lock()


def _load_favorites() -> list:
    """Read the saved favorites list from disk. Never raises."""
    try:
        with open(FAVORITES_FILE_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
            if isinstance(data, list):
                return data
    except Exception:
        pass
    return []


def _save_favorites(favorites: list):
    """Overwrite favorites.json with 'favorites'. Never raises."""
    try:
        os.makedirs(CONFIG_DIR, exist_ok=True)
        with _favorites_lock:
            with open(FAVORITES_FILE_PATH, "w", encoding="utf-8") as f:
                json.dump(favorites, f, ensure_ascii=False, indent=2)
    except Exception as e:
        safe_print(f"[ERROR] Could not save favorites.json: {e}")


def _trim_log_file():
    """
    Rewrite log.txt keeping only entries timestamped within the last
    LOG_RETENTION_DAYS days. Safe to call any time - never raises.
    """
    try:
        if not os.path.exists(LOG_FILE_PATH):
            return
        cutoff = time.time() - LOG_RETENTION_DAYS * 86400
        kept_lines = []
        keep_current_entry = False
        with open(LOG_FILE_PATH, "r", encoding="utf-8") as f:
            for line in f:
                if line.startswith("[") and "]" in line:
                    stamp_text = line[1:line.index("]")]
                    try:
                        entry_time = datetime.strptime(stamp_text, LOG_TIMESTAMP_FORMAT).timestamp()
                        keep_current_entry = entry_time >= cutoff
                    except ValueError:
                        keep_current_entry = True  # Unrecognized line - keep it, just in case
                if keep_current_entry:
                    kept_lines.append(line)
        with open(LOG_FILE_PATH, "w", encoding="utf-8") as f:
            f.writelines(kept_lines)
    except Exception as e:
        safe_print(f"[ERROR] Could not trim log.txt: {e}")


def _append_log_to_file(level: str, where: str, cause: str, quick_fix: str):
    """
    Append one notification entry to log.txt (plain text, same shape
    as the in-window log). Thread-safe - can be called from any
    thread. Periodically trims old entries so the file stays small.
    """
    global _log_file_append_count
    try:
        os.makedirs(CONFIG_DIR, exist_ok=True)
        stamp = datetime.now().strftime(LOG_TIMESTAMP_FORMAT)
        with _log_file_lock:
            with open(LOG_FILE_PATH, "a", encoding="utf-8") as f:
                f.write(f"[{stamp}] {level} - {where}\n")
                if cause:
                    f.write(f"    {cause}\n")
                if quick_fix:
                    f.write(f"    -> Fix: {quick_fix}\n")
            _log_file_append_count += 1
        # Trim every 50 entries rather than on every single write, so
        # a busy session isn't re-reading/rewriting the whole file
        # constantly.
        if _log_file_append_count % 50 == 0:
            _trim_log_file()
    except Exception as e:
        safe_print(f"[ERROR] Could not write to log.txt: {e}")


def _load_config() -> dict:
    """Read the saved settings from the local config file, if any."""
    try:
        with open(CONFIG_FILE_PATH, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


def _save_config(**updates):
    """
    Update one or more keys in the local config file, preserving
    whatever else is already saved there (e.g. saving a new hotkey
    doesn't erase the previously saved API key).
    """
    try:
        os.makedirs(CONFIG_DIR, exist_ok=True)
        data = _load_config()
        data.update(updates)
        with open(CONFIG_FILE_PATH, "w", encoding="utf-8") as f:
            json.dump(data, f)
    except Exception as e:
        safe_print(f"[ERROR] Could not save settings: {e}")


_saved_config = _load_config()  # Read once at import time
_favorites = _load_favorites()  # Read once at import time ([{"id", "text", "stamp"}, ...])
_favorites_next_id = (max((f.get("id", 0) for f in _favorites), default=0) + 1)

# ---------------------------------------------------------------------
# "Start with Windows" - adds/removes a value under the current user's
# Run key so the program launches automatically at login. Uses the
# standard library 'winreg' module (no extra dependency). Per-user
# (HKEY_CURRENT_USER), so it does not need Administrator rights.
# ---------------------------------------------------------------------
_STARTUP_REG_PATH = r"Software\Microsoft\Windows\CurrentVersion\Run"
_STARTUP_REG_NAME = "SilentBackgroundTranslator"


def _get_startup_command() -> str:
    """The exact command that would be placed in the Run key: re-launch this same script with this same interpreter."""
    script_path = os.path.abspath(sys.argv[0])
    return f'"{sys.executable}" "{script_path}"'


def _is_startup_enabled() -> bool:
    """True if this program is currently registered to start with Windows."""
    if winreg is None:
        return False
    try:
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, _STARTUP_REG_PATH, 0, winreg.KEY_READ) as key:
            value, _ = winreg.QueryValueEx(key, _STARTUP_REG_NAME)
            return bool(value)
    except FileNotFoundError:
        return False
    except OSError:
        return False


def _set_startup_enabled(enable: bool) -> bool:
    """Add or remove the "start with Windows" registry entry. Returns True on success."""
    if winreg is None:
        safe_print("[ERROR] 'winreg' is unavailable - this feature only works on Windows.")
        return False
    try:
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, _STARTUP_REG_PATH, 0, winreg.KEY_SET_VALUE) as key:
            if enable:
                winreg.SetValueEx(key, _STARTUP_REG_NAME, 0, winreg.REG_SZ, _get_startup_command())
            else:
                try:
                    winreg.DeleteValue(key, _STARTUP_REG_NAME)
                except FileNotFoundError:
                    pass
        safe_print(f"[INFO] Start with Windows: {'ON' if enable else 'OFF'}")
        _notify("Start with Windows", "Turned ON." if enable else "Turned OFF.")
        return True
    except Exception as e:
        safe_print(f"[ERROR] Could not update the Windows startup setting: {e}")
        _notify("Start with Windows", "Could not update this setting - see details in the console/log.")
        return False


# Arabic Unicode ranges: main block + supplement (covers standard Arabic text)
ARABIC_CHAR_PATTERN = re.compile(r"[\u0600-\u06FF\u0750-\u077F]")

# ---------------------------------------------------------------------
# THE ROOT CAUSE OF "buffer was empty" WITH ARABIC TYPING:
#
# Windows attaches a keyboard layout to each THREAD, not globally. The
# 'keyboard' library's background hook runs on this script's own
# thread, so when it turns a raw scan code into event.name it can use
# a DIFFERENT layout than the one actually active in the foreground
# app you're typing into (e.g. it resolves scan codes as if English
# were selected, even though you have Arabic selected in your editor).
# When that happens, Arabic keystrokes come back as event.name values
# like "semicolon" or "bracket left" instead of the Arabic letter, so
# every single keystroke falls into the "unhandled key -> reset
# buffer" branch below - the buffer never has a chance to fill up.
#
# The fix: ask Windows directly what character a scan code produces
# under the layout of the FOREGROUND window (the app that actually
# has focus), instead of trusting event.name's layout guess.
# ---------------------------------------------------------------------
_IS_WINDOWS = sys.platform.startswith("win")
_user32 = ctypes.WinDLL("user32", use_last_error=True) if _IS_WINDOWS else None
_kernel32 = ctypes.WinDLL("kernel32", use_last_error=True) if _IS_WINDOWS else None
_MAPVK_VSC_TO_VK_EX = 3
_VK_SHIFT = 0x10
_CF_UNICODETEXT = 13
_GMEM_MOVEABLE = 0x0002

if _IS_WINDOWS:
    from ctypes import wintypes

    # -------------------------------------------------------------------
    # CRITICAL: ctypes defaults every function's return type to a 32-bit
    # c_int unless told otherwise. HWND, HKL, HANDLE and HGLOBAL are all
    # POINTER-SIZED (64-bit on 64-bit Windows/Python). Without declaring
    # the real restype/argtypes below, these calls silently TRUNCATE
    # 64-bit handle values to 32 bits, which corrupts or zeroes them out
    # on real systems. That is exactly what was breaking every
    # clipboard call above (OpenClipboard/GetClipboardData/GlobalLock/
    # etc. all quietly failing -> "no text selected or copied") and
    # what was silently breaking the foreground-layout key resolver
    # too (it was failing and falling back to the older, less reliable
    # method the whole time). Declaring the correct signatures fixes
    # both.
    # -------------------------------------------------------------------
    _user32.GetForegroundWindow.restype = wintypes.HWND
    _user32.GetForegroundWindow.argtypes = []

    _user32.GetWindowThreadProcessId.restype = wintypes.DWORD
    _user32.GetWindowThreadProcessId.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.DWORD)]

    _user32.GetKeyboardLayout.restype = ctypes.c_void_p
    _user32.GetKeyboardLayout.argtypes = [wintypes.DWORD]

    _user32.MapVirtualKeyExW.restype = wintypes.UINT
    _user32.MapVirtualKeyExW.argtypes = [wintypes.UINT, wintypes.UINT, ctypes.c_void_p]

    _user32.ToUnicodeEx.restype = ctypes.c_int
    _user32.ToUnicodeEx.argtypes = [
        wintypes.UINT, wintypes.UINT, ctypes.POINTER(ctypes.c_byte),
        ctypes.c_wchar_p, ctypes.c_int, wintypes.UINT, ctypes.c_void_p,
    ]

    _user32.OpenClipboard.restype = wintypes.BOOL
    _user32.OpenClipboard.argtypes = [wintypes.HWND]

    _user32.CloseClipboard.restype = wintypes.BOOL
    _user32.CloseClipboard.argtypes = []

    _user32.EmptyClipboard.restype = wintypes.BOOL
    _user32.EmptyClipboard.argtypes = []

    _user32.GetClipboardData.restype = ctypes.c_void_p
    _user32.GetClipboardData.argtypes = [wintypes.UINT]

    _user32.SetClipboardData.restype = ctypes.c_void_p
    _user32.SetClipboardData.argtypes = [wintypes.UINT, ctypes.c_void_p]

    _kernel32.GlobalAlloc.restype = ctypes.c_void_p
    _kernel32.GlobalAlloc.argtypes = [wintypes.UINT, ctypes.c_size_t]

    _kernel32.GlobalLock.restype = ctypes.c_void_p
    _kernel32.GlobalLock.argtypes = [ctypes.c_void_p]

    _kernel32.GlobalUnlock.restype = wintypes.BOOL
    _kernel32.GlobalUnlock.argtypes = [ctypes.c_void_p]

    _user32.GetClipboardSequenceNumber.restype = wintypes.DWORD
    _user32.GetClipboardSequenceNumber.argtypes = []

    # --- extra declarations for the caret position, the no-focus indicator
    # window, the clipboard-content check and the foreground app name ---
    class _GUITHREADINFO(ctypes.Structure):
        _fields_ = [
            ("cbSize", wintypes.DWORD), ("flags", wintypes.DWORD),
            ("hwndActive", wintypes.HWND), ("hwndFocus", wintypes.HWND),
            ("hwndCapture", wintypes.HWND), ("hwndMenuOwner", wintypes.HWND),
            ("hwndMoveSize", wintypes.HWND), ("hwndCaret", wintypes.HWND),
            ("rcCaret", wintypes.RECT),
        ]

    _user32.GetGUIThreadInfo.restype = wintypes.BOOL
    _user32.GetGUIThreadInfo.argtypes = [wintypes.DWORD, ctypes.POINTER(_GUITHREADINFO)]
    _user32.ClientToScreen.restype = wintypes.BOOL
    _user32.ClientToScreen.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.POINT)]
    _user32.GetAncestor.restype = wintypes.HWND
    _user32.GetAncestor.argtypes = [wintypes.HWND, wintypes.UINT]
    _user32.GetWindowLongW.restype = ctypes.c_long
    _user32.GetWindowLongW.argtypes = [wintypes.HWND, ctypes.c_int]
    _user32.SetWindowLongW.restype = ctypes.c_long
    _user32.SetWindowLongW.argtypes = [wintypes.HWND, ctypes.c_int, ctypes.c_long]
    _user32.CountClipboardFormats.restype = ctypes.c_int
    _user32.CountClipboardFormats.argtypes = []
    _kernel32.OpenProcess.restype = wintypes.HANDLE
    _kernel32.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    _kernel32.CloseHandle.restype = wintypes.BOOL
    _kernel32.CloseHandle.argtypes = [wintypes.HANDLE]
    _kernel32.QueryFullProcessImageNameW.restype = wintypes.BOOL
    _kernel32.QueryFullProcessImageNameW.argtypes = [
        wintypes.HANDLE, wintypes.DWORD, wintypes.LPWSTR, ctypes.POINTER(wintypes.DWORD)]


def _get_clipboard_text():
    """
    Return the current clipboard text, or None if it's empty, isn't
    text, or the clipboard couldn't be opened (e.g. another app is
    briefly holding it). Never raises.
    """
    if not _IS_WINDOWS:
        return None
    try:
        if not _user32.OpenClipboard(None):
            return None
        try:
            handle = _user32.GetClipboardData(_CF_UNICODETEXT)
            if not handle:
                return None
            locked = _kernel32.GlobalLock(handle)
            if not locked:
                return None
            try:
                return ctypes.wstring_at(locked)
            finally:
                _kernel32.GlobalUnlock(handle)
        finally:
            _user32.CloseClipboard()
    except Exception:
        return None


def _set_clipboard_text(text: str) -> bool:
    """Set the clipboard to 'text'. Returns True on success. Never raises."""
    if not _IS_WINDOWS:
        return False
    try:
        if not _user32.OpenClipboard(None):
            return False
        try:
            _user32.EmptyClipboard()
            data = text + "\0"
            size = len(data) * ctypes.sizeof(ctypes.c_wchar)
            h_mem = _kernel32.GlobalAlloc(_GMEM_MOVEABLE, size)
            if not h_mem:
                return False
            locked = _kernel32.GlobalLock(h_mem)
            if not locked:
                return False
            ctypes.memmove(locked, data, size)
            _kernel32.GlobalUnlock(h_mem)
            if not _user32.SetClipboardData(_CF_UNICODETEXT, h_mem):
                return False
            return True
        finally:
            _user32.CloseClipboard()
    except Exception:
        return False


def _get_clipboard_sequence():
    """
    Return Windows' clipboard sequence number - a counter that
    increments every time ANYTHING is copied to the clipboard, by any
    method (mouse "Copy", Ctrl+C, another app, etc.). Used to detect
    "something was just copied" without polling/diffing content.
    Returns None if unavailable.
    """
    if not _IS_WINDOWS:
        return None
    try:
        return _user32.GetClipboardSequenceNumber()
    except Exception:
        return None


def _resolve_typed_char(scan_code: int, shift_pressed: bool) -> str:
    """
    Return the Unicode character 'scan_code' actually produces right
    now, resolved against the keyboard layout of the FOREGROUND window
    (see explanation above). Returns "" if this can't be determined
    (not on Windows, no scan code, or any WinAPI failure) - the caller
    then falls back to the 'keyboard' library's own event.name guess.
    """
    if not _IS_WINDOWS or not scan_code:
        return ""
    try:
        hwnd = _user32.GetForegroundWindow()
        if not hwnd:
            return ""
        thread_id = _user32.GetWindowThreadProcessId(hwnd, None)
        layout = _user32.GetKeyboardLayout(thread_id)

        vk = _user32.MapVirtualKeyExW(scan_code, _MAPVK_VSC_TO_VK_EX, layout)
        if not vk:
            return ""

        key_state = (ctypes.c_byte * 256)()
        if shift_pressed:
            key_state[_VK_SHIFT] = 0x80

        buf = ctypes.create_unicode_buffer(8)
        n = _user32.ToUnicodeEx(vk, scan_code, key_state, buf, 8, 0, layout)

        if n < 0:
            # n < 0 means this scan code was resolved as a DEAD KEY
            # (an accent/diacritic key that waits for the next
            # keystroke before producing a character). Windows'
            # ToUnicodeEx has a well-known side effect: after a dead
            # key, it leaves an internal "waiting to compose" state
            # armed. If we don't immediately clear it, THIS state can
            # bleed into the very next real keystroke the user types
            # into the foreground app, silently altering or eating
            # it - which is exactly the kind of "a letter/word gets
            # left behind" symptom this program was seeing. The fix
            # (documented Microsoft workaround) is to immediately call
            # ToUnicodeEx a second time to flush/cancel that pending
            # dead-key state before moving on.
            flush_buf = ctypes.create_unicode_buffer(8)
            _user32.ToUnicodeEx(vk, scan_code, key_state, flush_buf, 8, 0, layout)
            return ""

        if n > 0:
            return buf.value[:n]
    except Exception:
        pass
    return ""

# Keys that should reset the buffer without triggering translation
RESET_KEYS = {
    "tab", "esc", "enter", "up", "down", "left", "right", "home", "end",
    "page up", "page down", "delete", "insert", "caps lock",
}

# Modifier keys are ignored on their own (they don't reset or add to the buffer)
MODIFIER_KEYS = {
    "ctrl", "left ctrl", "right ctrl",
    "alt", "left alt", "right alt",
    "shift", "left shift", "right shift",
    "windows", "left windows", "right windows",
}

# -----------------------------------------------------------------------
# Shared state
# -----------------------------------------------------------------------
_buffer = ""
_buffer_lock = threading.Lock()
_busy = False              # True while a translate/replace operation is running
_enabled = True             # Master on/off switch (toggled from the tray menu)
_translate_engine = _saved_config.get("translate_engine", "google")
_trigger_key = _saved_config.get("trigger_key", "scroll lock")
_trigger_components = {p.strip() for p in _trigger_key.split("+")}
_hotkey_handle = None       # Handle returned by keyboard.add_hotkey, for removal
_tray_icon = None           # pystray.Icon instance, set in main()
_claude_api_key = _saved_config.get("claude_api_key", "")
_gemini_api_key = _saved_config.get("gemini_api_key", "")
_deepl_api_key = _saved_config.get("deepl_api_key", "")

# ---- "custom" engine: any OpenAI-compatible AI provider ----
# _custom_providers maps a name you choose (e.g. "OpenRouter", "Groq")
# to {"base_url": ..., "api_key": ..., "model": ...}. You can save
# several providers and switch between them from Settings without ever
# touching this file - see _translate_via_custom_ai() below.
_custom_providers = _saved_config.get("custom_providers", {})
_custom_provider_selected = _saved_config.get("custom_provider_selected", "")

# Typing speed profile ("turbo" / "normal" / "safe") - see
# TYPING_SPEED_PRESETS above. _key_delay is the actual numeric delay
# in effect right now, kept in sync with _typing_speed_profile.
_typing_speed_profile = _saved_config.get("typing_speed_profile", DEFAULT_TYPING_SPEED_PROFILE)
if _typing_speed_profile not in TYPING_SPEED_PRESETS:
    _typing_speed_profile = DEFAULT_TYPING_SPEED_PROFILE
_key_delay = TYPING_SPEED_PRESETS[_typing_speed_profile]

# ---- English -> Arabic "popup preview" trigger (separate from the
# Arabic -> English in-place replace trigger above) - see
# _on_popup_trigger_pressed(). Copy/select English text, press this
# key, and the Arabic translation shows in a small on-screen popup
# instead of being typed anywhere.
_popup_trigger_key = _saved_config.get("popup_trigger_key", "f10")
_popup_trigger_components = {p.strip() for p in _popup_trigger_key.split("+")}
_popup_hotkey_handle = None

# ---- Select-translate: independent hotkey that translates whatever
# text is currently selected with the MOUSE in any program, in either
# direction (Arabic -> English or English -> Arabic), auto-detected
# from the selected text itself. Completely separate from the typed
# buffer + trigger-key flow above; does not affect it at all.
_select_trigger_key = _saved_config.get("select_trigger_key", "f4")
_select_trigger_components = {p.strip() for p in _select_trigger_key.split("+")}
_select_hotkey_handle = None

# ---- Fallback engine: if the PRIMARY engine (_translate_engine) fails
# for a given translation, we immediately retry that same sentence,
# ONCE, with this engine instead. The saved primary engine never
# changes because of this - next translation still starts with the
# primary engine again. Stored as:
#   "none"                    -> no fallback
#   "<engine>"                -> one of ENGINE_PRESETS (except "custom")
#   "custom:<provider name>"  -> a specific saved custom provider
_fallback_engine = _saved_config.get("fallback_engine", "none")

# ---- Target language: the "other side" of the Arabic <-> X pair (see
# TARGET_LANGUAGE_PRESETS above). Defaults to English, matching the
# program's original behavior; change it from Settings -> General.
_target_language = _saved_config.get("target_language", DEFAULT_TARGET_LANGUAGE)
if _target_language not in TARGET_LANGUAGE_CODE_TO_NAME:
    _target_language = DEFAULT_TARGET_LANGUAGE

# =========================================================================
# EXTRA FEATURES (added): translation tone, in-memory cache, the small
# "translating..." indicator, paste-instead-of-type for long text,
# per-app typing speed, and the API usage meter.
# =========================================================================

# ---- Translation tone (AI engines only) ----
TONE_PRESETS = {
    "formal": "Use a polite, professional, formal register (suitable for a work email).",
    "normal": "Use a natural, everyday register.",
    "casual": "Use a casual, friendly, chatty register, like texting a friend; "
              "contractions and light slang are fine.",
}
TONE_ORDER = ["normal", "formal", "casual"]
DEFAULT_TONE = "normal"
_translation_tone = _saved_config.get("translation_tone", DEFAULT_TONE)
if _translation_tone not in TONE_PRESETS:
    _translation_tone = DEFAULT_TONE
_tone_trigger_key = _saved_config.get("tone_trigger_key", "") or ""
_tone_trigger_components = (
    {p.strip() for p in _tone_trigger_key.split("+")} if _tone_trigger_key else set()
)
_tone_hotkey_handle = None

# ---- Misc. switches ----
_cache_enabled = bool(_saved_config.get("cache_enabled", True))
_indicator_enabled = bool(_saved_config.get("show_working_indicator", True))
_working_sound = bool(_saved_config.get("working_sound", False))

# Translations LONGER than this many characters are pasted (Ctrl+V) instead of
# typed key-by-key. 0 = never paste, always type.
DEFAULT_PASTE_THRESHOLD = 40
try:
    _paste_threshold = max(0, min(5000, int(_saved_config.get("paste_threshold", DEFAULT_PASTE_THRESHOLD))))
except (TypeError, ValueError):
    _paste_threshold = DEFAULT_PASTE_THRESHOLD

# Per-app typing speed: {"process.exe": "turbo"|"normal"|"safe"}
DEFAULT_APP_SPEED_RULES = {"hd-player.exe": "safe"}  # BlueStacks
_raw_app_rules = _saved_config.get("app_speed_rules", DEFAULT_APP_SPEED_RULES)
if isinstance(_raw_app_rules, dict):
    _app_speed_rules = {
        str(k).strip().lower(): v for k, v in _raw_app_rules.items() if v in TYPING_SPEED_PRESETS
    }
else:
    _app_speed_rules = dict(DEFAULT_APP_SPEED_RULES)


def _parse_app_speed_rules(text: str):
    """'name.exe = safe' lines -> ({name: speed}, [unreadable lines])."""
    rules, bad = {}, []
    for raw_line in (text or "").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        sep = "=" if "=" in line else (":" if ":" in line else None)
        if sep is None:
            bad.append(line)
            continue
        name, speed = (part.strip().lower() for part in line.split(sep, 1))
        if not name or speed not in TYPING_SPEED_PRESETS:
            bad.append(line)
            continue
        if not name.endswith(".exe"):
            name += ".exe"
        rules[name] = speed
    return rules, bad


def _effective_speed_profile(app_name: str) -> str:
    """The typing-speed profile to use for the app we are typing into."""
    profile = _app_speed_rules.get((app_name or "").lower())
    return profile if profile in TYPING_SPEED_PRESETS else _typing_speed_profile


def _get_foreground_process_name() -> str:
    """Lowercase exe name of the foreground window's program ('' if unknown)."""
    if not _IS_WINDOWS:
        return ""
    try:
        hwnd = _user32.GetForegroundWindow()
        if not hwnd:
            return ""
        pid = wintypes.DWORD(0)
        _user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
        if not pid.value:
            return ""
        handle = _kernel32.OpenProcess(0x1000, False, pid.value)  # QUERY_LIMITED_INFORMATION
        if not handle:
            return ""
        try:
            buf = ctypes.create_unicode_buffer(1024)
            size = wintypes.DWORD(len(buf))
            if _kernel32.QueryFullProcessImageNameW(handle, 0, buf, ctypes.byref(size)):
                return os.path.basename(buf.value).lower()
        finally:
            _kernel32.CloseHandle(handle)
    except Exception:
        pass
    return ""


def _paste_text_via_clipboard(text: str) -> bool:
    """
    Put 'text' on the clipboard, send Ctrl+V, then restore the old clipboard
    TEXT. Returns False (and does nothing) if the clipboard currently holds
    something that is not text (image/files) - restoring that is impossible,
    so the caller types the text key-by-key instead.
    """
    if not _IS_WINDOWS:
        return False
    previous = _get_clipboard_text()
    try:
        if previous is None and _user32.CountClipboardFormats() > 0:
            return False
    except Exception:
        return False
    if not _set_clipboard_text(text):
        if previous is not None:
            _set_clipboard_text(previous)
        return False
    time.sleep(0.05)
    keyboard.send("ctrl+v")
    time.sleep(0.25)  # let the target app read the clipboard before we restore it
    if previous is not None:
        _set_clipboard_text(previous)
    return True


# ---- In-memory translation cache (never written to disk) ----
TRANSLATION_CACHE_MAX_ENTRIES = 300
_translation_cache = {}  # insertion-ordered: oldest first
_translation_cache_lock = threading.Lock()


def _cache_key(sentence: str, direction: str):
    """Everything that changes the result is part of the key."""
    if _translate_engine == "custom":
        provider = _custom_providers.get(_custom_provider_selected) or {}
        engine_id = f"custom:{_custom_provider_selected}:{provider.get('model', '')}"
    elif _translate_engine == "claude":
        engine_id = f"claude:{CLAUDE_MODEL}"
    elif _translate_engine == "gemini":
        engine_id = f"gemini:{GEMINI_MODEL}"
    else:
        engine_id = _translate_engine
    return (sentence, direction, engine_id, _translation_tone)


def _cache_lookup(key):
    if not _cache_enabled:
        return None
    with _translation_cache_lock:
        value = _translation_cache.get(key)
        if value is not None:  # mark as recently used
            _translation_cache.pop(key, None)
            _translation_cache[key] = value
        return value


def _cache_store(key, value: str):
    if not _cache_enabled or not value:
        return
    with _translation_cache_lock:
        _translation_cache.pop(key, None)
        _translation_cache[key] = value
        while len(_translation_cache) > TRANSLATION_CACHE_MAX_ENTRIES:
            _translation_cache.pop(next(iter(_translation_cache)))


def _clear_translation_cache() -> int:
    with _translation_cache_lock:
        count = len(_translation_cache)
        _translation_cache.clear()
    return count


# ---- Tone hotkey ----
def _cycle_tone():
    global _translation_tone
    try:
        index = TONE_ORDER.index(_translation_tone)
    except ValueError:
        index = -1
    _translation_tone = TONE_ORDER[(index + 1) % len(TONE_ORDER)]
    _save_config(translation_tone=_translation_tone)
    _notify("Translation tone", f"Tone is now: {_translation_tone}", level="info")
    _refresh_ui()


def _on_tone_trigger_pressed():
    if not _enabled:
        return
    _cycle_tone()


def _register_tone_hotkey(key_combo: str) -> bool:
    """Set (or, with an empty string, remove) the optional tone-switch hotkey."""
    global _tone_hotkey_handle, _tone_trigger_key, _tone_trigger_components

    key_combo = (key_combo or "").strip().lower()
    if not key_combo:
        if _tone_hotkey_handle is not None:
            try:
                keyboard.remove_hotkey(_tone_hotkey_handle)
            except Exception:
                pass
        _tone_hotkey_handle = None
        _tone_trigger_key = ""
        _tone_trigger_components = set()
        _save_config(tone_trigger_key="")
        return True

    parts = {p.strip() for p in key_combo.split("+")}
    if parts.issubset({"ctrl", "alt", "shift", "windows"}):
        return False
    if parts in (_trigger_components, _popup_trigger_components, _select_trigger_components):
        return False
    try:
        new_handle = keyboard.add_hotkey(key_combo, _on_tone_trigger_pressed)
    except Exception as e:
        safe_print(f"[ERROR] Could not register tone hotkey '{key_combo}': {e}")
        return False
    if _tone_hotkey_handle is not None:
        try:
            keyboard.remove_hotkey(_tone_hotkey_handle)
        except Exception:
            pass
    _tone_hotkey_handle = new_handle
    _tone_trigger_key = key_combo
    _tone_trigger_components = parts
    _save_config(tone_trigger_key=key_combo)
    return True


# ---- "Translating..." indicator (small capsule above the typing spot) ----
_working_win = None
_working_label = None
_working_failed = False
_working_active = False
_working_token = 0
_working_after_id = None
_working_anim_step = 0
_working_base_text = ""

_WS_EX_LAYERED = 0x00080000
_WS_EX_TRANSPARENT = 0x00000020   # clicks pass straight through
_WS_EX_TOOLWINDOW = 0x00000080
_WS_EX_NOACTIVATE = 0x08000000    # never takes keyboard focus
_GWL_EXSTYLE = -20
_GA_ROOT = 2


def _get_caret_screen_pos():
    """(x, y, height) of the text caret of the foreground app, or None."""
    if not _IS_WINDOWS:
        return None
    try:
        fg = _user32.GetForegroundWindow()
        if not fg:
            return None
        thread_id = _user32.GetWindowThreadProcessId(fg, None)
        info = _GUITHREADINFO()
        info.cbSize = ctypes.sizeof(info)
        if not _user32.GetGUIThreadInfo(thread_id, ctypes.byref(info)):
            return None
        if not info.hwndCaret:
            return None
        point = wintypes.POINT(info.rcCaret.left, info.rcCaret.top)
        if not _user32.ClientToScreen(info.hwndCaret, ctypes.byref(point)):
            return None
        return point.x, point.y, max(info.rcCaret.bottom - info.rcCaret.top, 0)
    except Exception:
        return None


def _init_working_indicator():
    """Create the (hidden) indicator window once. Tk main thread only."""
    global _working_win, _working_label
    if not _IS_WINDOWS or _root is None:
        return
    try:
        win = tk.Toplevel(_root)
        win.withdraw()
        win.overrideredirect(True)
        win.attributes("-topmost", True)
        win.attributes("-alpha", 0.93)
        label = tk.Label(win, text="جاري الترجمة", font=("Segoe UI", 9, "bold"),
                         fg="white", bg="#0f5d8c", padx=10, pady=3)
        label.pack()
        win.geometry("+-3000+-3000")   # show once off-screen to get a real HWND
        win.deiconify()
        win.update_idletasks()
        hwnd = _user32.GetAncestor(win.winfo_id(), _GA_ROOT) or win.winfo_id()
        style = _user32.GetWindowLongW(hwnd, _GWL_EXSTYLE)
        _user32.SetWindowLongW(
            hwnd, _GWL_EXSTYLE,
            style | _WS_EX_LAYERED | _WS_EX_TRANSPARENT | _WS_EX_NOACTIVATE | _WS_EX_TOOLWINDOW,
        )
        win.withdraw()
        _working_win, _working_label = win, label
    except Exception as e:
        safe_print(f"[WARNING] Could not create the 'translating' indicator: {e}")
        _working_win = _working_label = None


def _working_position():
    win = _working_win
    win.update_idletasks()
    w, h = win.winfo_reqwidth(), win.winfo_reqheight()
    screen_w, screen_h = win.winfo_screenwidth(), win.winfo_screenheight()
    caret = _get_caret_screen_pos()
    if caret:
        cx, cy, ch = caret
        x, y = cx, cy - h - 6              # above the caret...
        if y < 0:
            y = cy + max(ch, 16) + 6       # ...or below it if there is no room
    else:
        mx, my = win.winfo_pointerxy()     # app doesn't expose its caret: use the mouse
        x, y = mx + 12, my - h - 14
        if y < 0:
            y = my + 22
    x = min(max(x, 0), max(screen_w - w, 0))
    y = min(max(y, 0), max(screen_h - h, 0))
    win.geometry(f"+{x}+{y}")


def _working_stop_anim():
    global _working_after_id
    if _working_after_id is not None and _working_win is not None:
        try:
            _working_win.after_cancel(_working_after_id)
        except Exception:
            pass
    _working_after_id = None


def _working_anim_tick():
    global _working_anim_step, _working_after_id
    if not _working_active or _working_win is None:
        return
    _working_anim_step = (_working_anim_step + 1) % 4
    _working_label.config(text=_working_base_text + "." * _working_anim_step)
    _working_after_id = _working_win.after(350, _working_anim_tick)


def _working_show_main(text: str):
    global _working_active, _working_base_text, _working_token, _working_anim_step
    if _working_win is None or not _indicator_enabled:
        return
    try:
        _working_token += 1
        _working_stop_anim()
        _working_active = True
        _working_base_text = text
        _working_anim_step = 0
        _working_label.config(text=text, bg="#0f5d8c")
        _working_position()
        _working_win.deiconify()
        _working_win.lift()
        _working_anim_tick()
    except Exception as e:
        safe_print(f"[WARNING] Indicator error: {e}")


def _working_set_text_main(text: str):
    global _working_base_text
    if _working_win is None or not _working_active:
        return
    _working_base_text = text
    _working_label.config(text=text)


def _working_hide_main(failed: bool):
    global _working_active
    if _working_win is None:
        return
    try:
        was_active = _working_active
        _working_stop_anim()
        _working_active = False
        if failed and was_active:
            token = _working_token
            _working_label.config(text="فشلت الترجمة", bg="#c0392b")

            def _finish():
                if token == _working_token and not _working_active:
                    _working_win.withdraw()
            _working_win.after(1200, _finish)
        else:
            _working_win.withdraw()
    except Exception:
        pass


def _play_soft_sound():
    try:
        import winsound
        winsound.Beep(1100, 30)
    except Exception:
        pass


def _working_show(text: str = "جاري الترجمة"):
    """Thread-safe: show the indicator (called when a translation starts)."""
    global _working_failed
    _working_failed = False
    if not _indicator_enabled:
        return
    _ui_call(_working_show_main, text)
    if _working_sound:
        threading.Thread(target=_play_soft_sound, daemon=True).start()


def _working_set_text(text: str):
    if _indicator_enabled:
        _ui_call(_working_set_text_main, text)


def _working_mark_failed():
    global _working_failed
    _working_failed = True


def _working_hide():
    """Thread-safe: hide it (turns red for a moment if the operation failed)."""
    _ui_call(_working_hide_main, _working_failed)


# ---- API usage meter (only for providers that report real numbers) ----
USAGE_MIN_INTERVAL_SECONDS = 60
USAGE_FETCH_TIMEOUT_SECONDS = 8
_usage_snapshot = None          # {"title", "detail", "fraction_left"} or None
_usage_last_fetch = 0.0
_usage_fetch_in_flight = False
_usage_alert_level = 0          # 0 = none sent, 1 = "20% left" sent, 2 = "5% left" sent
_usage_lock = threading.Lock()
_usage_frame = None
_usage_title_var = None
_usage_detail_var = None
_usage_canvas = None


def _fmt_usd(value) -> str:
    if value is None:
        return "?"
    return f"${value:,.4f}" if abs(value) < 1 else f"${value:,.2f}"


def _usage_target():
    """Which provider (if any) can report real usage right now."""
    if _translate_engine == "deepl" and _deepl_api_key:
        return ("deepl", "", _deepl_api_key, "")
    if _translate_engine == "custom":
        provider = _custom_providers.get(_custom_provider_selected) or {}
        base_url = (provider.get("base_url") or "").strip().rstrip("/")
        api_key = (provider.get("api_key") or "").strip()
        if "openrouter.ai" in base_url.lower() and api_key:
            return ("openrouter", base_url, api_key, (provider.get("model") or "").strip())
    return None


def _fetch_openrouter_usage(base_url: str, api_key: str, model: str):
    request = urllib.request.Request(
        f"{base_url}/key", headers={"Authorization": f"Bearer {api_key}"}, method="GET")
    with urllib.request.urlopen(request, timeout=USAGE_FETCH_TIMEOUT_SECONDS) as resp:
        payload = json.loads(resp.read().decode("utf-8"))
    data = payload.get("data") or {}

    def num(name):
        value = data.get(name)
        return float(value) if isinstance(value, (int, float)) and not isinstance(value, bool) else None

    limit, remaining = num("limit"), num("limit_remaining")
    used_total, used_today = num("usage"), num("usage_daily")
    if remaining is None and limit is not None and used_total is not None:
        remaining = limit - used_total

    if model.endswith(":free"):
        status = "Free model (:free) - no cost, daily request limits apply"
    elif data.get("is_free_tier"):
        status = "Free tier - no credits purchased yet"
    else:
        status = "Paid"

    parts = []
    if used_today is not None:
        parts.append(f"Used today {_fmt_usd(used_today)}")
    if used_total is not None:
        parts.append(f"Total {_fmt_usd(used_total)}")

    fraction_left = None
    if limit and limit > 0 and remaining is not None:
        fraction_left = max(0.0, min(1.0, remaining / limit))
        parts.append(f"Left {_fmt_usd(remaining)} of {_fmt_usd(limit)} ({fraction_left * 100:.0f}%)")
    else:
        parts.append("no spending limit is set on this key")
    return {"title": f"OpenRouter · {status}", "detail": "  ·  ".join(parts),
            "fraction_left": fraction_left}


def _fetch_deepl_usage(api_key: str):
    if not _DEEPL_AVAILABLE:
        return None
    usage = deepl.Translator(api_key).get_usage()
    chars = usage.character
    if not getattr(chars, "valid", False) or not chars.limit:
        return None
    fraction_left = max(0.0, min(1.0, 1 - chars.count / chars.limit))
    return {
        "title": "DeepL · characters",
        "detail": f"Used {chars.count:,} of {chars.limit:,}  ·  Left {fraction_left * 100:.0f}%",
        "fraction_left": fraction_left,
    }


def _check_usage_alerts(snapshot):
    global _usage_alert_level
    if not snapshot or snapshot.get("fraction_left") is None:
        return
    left = snapshot["fraction_left"]
    if left > 0.2:
        _usage_alert_level = 0   # topped up again: re-arm the warnings
        return
    if left <= 0.05 and _usage_alert_level < 2:
        _usage_alert_level = 2
        message = f"Only {left * 100:.0f}% is left. Top up soon or switch engine."
    elif _usage_alert_level < 1:
        _usage_alert_level = 1
        message = f"{left * 100:.0f}% is left."
    else:
        return
    title = snapshot["title"].split("·")[0].strip() + " - usage warning"
    _notify(title, message, level="warning")
    _log_event("WARN", title, message, "Add credits / raise the limit, or switch engine in Settings.")


def _draw_usage_bar():
    canvas = _usage_canvas
    if canvas is None:
        return
    canvas.delete("all")
    snapshot = _usage_snapshot
    if not snapshot or snapshot.get("fraction_left") is None:
        return
    width, height = canvas.winfo_width(), canvas.winfo_height()
    left = snapshot["fraction_left"]
    color = "#2e8b57" if left >= 0.4 else ("#e0a000" if left >= 0.2 else "#c0392b")
    canvas.create_rectangle(0, 0, int(width * left), height, fill=color, outline="")


def _apply_usage_to_ui():
    """Show/hide/update the usage block. Tk main thread only."""
    if _usage_frame is None:
        return
    snapshot = _usage_snapshot
    if not snapshot:
        _usage_frame.pack_forget()
        return
    _usage_title_var.set(snapshot["title"])
    _usage_detail_var.set(snapshot["detail"])
    if snapshot.get("fraction_left") is None:
        _usage_canvas.pack_forget()
    else:
        _usage_canvas.pack(fill="x", pady=(3, 0))
    if _quick_fix_button is not None and _quick_fix_button.winfo_manager():
        _usage_frame.pack(fill="x", padx=14, pady=(0, 6), before=_quick_fix_button)
    else:
        _usage_frame.pack(fill="x", padx=14, pady=(0, 6))
    _usage_frame.update_idletasks()
    _draw_usage_bar()


def _usage_worker():
    global _usage_snapshot, _usage_fetch_in_flight
    snapshot = None
    try:
        target = _usage_target()
        if target is not None:
            kind, base_url, api_key, model = target
            if kind == "openrouter":
                snapshot = _fetch_openrouter_usage(base_url, api_key, model)
            elif kind == "deepl":
                snapshot = _fetch_deepl_usage(api_key)
    except Exception as e:
        safe_print(f"[INFO] Could not read the usage numbers: {e}")
        snapshot = None
    finally:
        with _usage_lock:
            _usage_fetch_in_flight = False
    _usage_snapshot = snapshot
    _ui_call(_apply_usage_to_ui)
    _check_usage_alerts(snapshot)


def _refresh_usage(force: bool = False):
    """Fetch the usage numbers in the background (at most once a minute)."""
    global _usage_last_fetch, _usage_fetch_in_flight
    now = time.time()
    with _usage_lock:
        if _usage_fetch_in_flight:
            return
        if not force and now - _usage_last_fetch < USAGE_MIN_INTERVAL_SECONDS:
            return
        _usage_fetch_in_flight = True
        _usage_last_fetch = now
    threading.Thread(target=_usage_worker, daemon=True).start()



def _is_arabic_char(ch: str) -> bool:
    return bool(ARABIC_CHAR_PATTERN.match(ch))


# =========================================================================
# UI BRIDGE
# -------------------------------------------------------------------------
# Everything visual (main window, settings window, translation popup) now
# lives on ONE Tk root that runs on the MAIN thread. Translations, the
# clipboard watcher and the keyboard hooks all run on background threads,
# and Tk is NOT thread-safe, so background threads never touch widgets
# directly: they push a callable onto _ui_queue and the main thread picks
# it up in _pump_ui_queue() a few times per second.
# =========================================================================
_ui_queue = queue.Queue()
_root = None            # The single tk.Tk() root (created in main())
_main_window = None     # The visible main window (a Toplevel of _root)
_settings_window = None # The settings Toplevel, while it is open
_status_var = None      # StringVar shown as the big status line
_translations_log_widget = None  # Text widget: successful translation results
_errors_log_widget = None        # Text widget: errors/warnings/info notices
_favorites_list_frame = None     # Scrollable frame holding the favorites rows
_window_visible = False


def _ui_call(func, *args, **kwargs):
    """Run 'func' on the Tk main thread. Safe to call from any thread."""
    _ui_queue.put((func, args, kwargs))


def _pump_ui_queue():
    """Drain queued UI tasks. Re-schedules itself on the Tk main loop."""
    while True:
        try:
            func, args, kwargs = _ui_queue.get_nowait()
        except queue.Empty:
            break
        try:
            func(*args, **kwargs)
        except Exception as e:
            safe_print(f"[ERROR] A UI task failed: {e}")
    if _root is not None:
        _root.after(100, _pump_ui_queue)


# =========================================================================
# PROBLEM DIAGNOSIS + NOTIFICATIONS
# -------------------------------------------------------------------------
# Instead of a single generic "Translation failed" message, every failure
# is classified into a known cause, and each cause carries a concrete
# QUICK FIX: retry, restart the program, open Settings, install a
# package, etc. The same text is shown in three places: the Windows
# toast, the status line of the main window, and the scrolling
# notification history inside that window.
# =========================================================================

# Quick-fix action ids understood by the main window's action button.
ACTION_RETRY = "retry"       # re-run the last translation
ACTION_RESTART = "restart"   # relaunch the whole program
ACTION_SETTINGS = "settings"  # open the Settings window
ACTION_NONE = None

# How many failures in a row before we stop suggesting "try again" and
# start suggesting a full restart (a hook or engine session that keeps
# failing usually only recovers on a restart).
_FAILURES_BEFORE_RESTART = 3

_consecutive_failures = 0
_last_job = None            # dict describing the last translation attempt
_last_job_lock = threading.Lock()


def _diagnose(exc: Exception):
    """
    Turn an exception into (cause, quick_fix, action).
      cause     - short human explanation of WHAT went wrong
      quick_fix - what the user should do about it, right now
      action    - one of the ACTION_* ids, used by the "Quick fix" button
    Matching is done on the lowercased type+message, which covers
    'translators', requests/urllib3, the Anthropic SDK and the Gemini SDK
    without importing any of their exception classes.
    """
    text = f"{type(exc).__name__}: {exc}".lower()

    def has(*needles):
        return any(n in text for n in needles)

    if isinstance(exc, TimeoutError) or has("timeout", "timed out"):
        return ("The translation engine did not answer in time "
                "(انتهت مهلة انتظار محرك الترجمة).",
                f"Press 'Quick fix' to translate again, or pick a faster engine "
                f"in Settings (current: {_translate_engine}).",
                ACTION_RETRY)

    if has("http 402", "payment required", "insufficient credits", "insufficient_quota",
           "out of credits", "more credits", "requires more credits"):
        return ("The AI account is out of credits (الرصيد خلص).",
                "Add credits to your AI provider account (for OpenRouter: "
                "openrouter.ai/credits), then press 'Quick fix' to try again.",
                ACTION_RETRY)

    if has("api key", "x-api-key", "unauthorized", "401", "403",
           "authentication", "permission_denied", "invalid_api_key"):
        return ("The API key for the selected engine is missing, wrong or expired "
                "(مفتاح الـ API غير صالح).",
                "Open Settings and paste a valid key, or switch back to the free "
                "'google' engine.",
                ACTION_SETTINGS)

    if has("429", "rate limit", "rate_limit", "quota", "resource_exhausted",
           "too many requests", "insufficient", "billing", "credit"):
        return ("The engine refused the request: rate limit or quota reached "
                "(تجاوزت حد الاستخدام).",
                "Wait a few seconds and press 'Quick fix', or switch to another "
                "engine in Settings.",
                ACTION_RETRY)

    if isinstance(exc, (ImportError, ModuleNotFoundError)) or has("not installed", "no module named"):
        return ("A library needed by the selected engine is not installed "
                "(مكتبة ناقصة).",
                "Close the program and run:  pip install -r requirements.txt",
                ACTION_NONE)

    if has("connection", "getaddrinfo", "max retries", "network", "ssl",
           "name or service", "temporary failure", "proxy", "unreachable",
           "refused", "reset by peer", "dns"):
        return ("Could not reach the translation service - the network call failed "
                "(مشكلة في الاتصال بالإنترنت).",
                "Check your internet / VPN, then press 'Quick fix' to try again.",
                ACTION_RETRY)

    if has("access is denied", "administrator", "winerror 5", "permission denied"):
        return ("Windows blocked the program from simulating or reading keys "
                "(صلاحيات ناقصة).",
                "Close it and run it again as Administrator - press 'Quick fix' "
                "to restart now.",
                ACTION_RESTART)

    if has("translatorerror", "region", "not supported", "unsupported",
           "expecting value", "jsondecode", "html", "captcha", "blocked"):
        return (f"The '{_translate_engine}' engine returned something unusable - it is "
                f"often region-blocked or temporarily down (المحرك رفض الطلب).",
                "Switch the engine in Settings (google / bing / baidu), then try again.",
                ACTION_SETTINGS)

    return (f"Unexpected error: {type(exc).__name__}: {exc}",
            "Press 'Quick fix' to try the same translation again. If it keeps "
            "failing, restart the program.",
            ACTION_RETRY)


def _report_problem(where: str, exc: Exception = None, cause: str = None,
                    quick_fix: str = None, action=ACTION_RETRY, counts_as_failure=True):
    """
    The single place every failure goes through. Classifies the problem,
    remembers how many failures happened in a row, and shows the result
    as a toast + a line in the main window.
    """
    global _consecutive_failures

    _working_mark_failed()  # turns the "translating..." capsule red for a moment

    if exc is not None:
        cause, quick_fix, action = _diagnose(exc)
        if DEBUG_MODE:
            safe_print(traceback.format_exc())

    if counts_as_failure:
        _consecutive_failures += 1
        if _consecutive_failures >= _FAILURES_BEFORE_RESTART:
            quick_fix = (f"This is failure #{_consecutive_failures} in a row - a restart "
                         f"usually clears it. Press 'Quick fix' to restart the program.")
            action = ACTION_RESTART

    _set_quick_fix(action, cause, quick_fix)
    _notify(where, f"{cause}\n\nFix: {quick_fix}", level="error")
    _log_event("ERROR", where, cause, quick_fix)


def _report_warning(where: str, cause: str, quick_fix: str, action=ACTION_NONE):
    """A non-fatal notice (e.g. nothing was selected to translate)."""
    _set_quick_fix(action, cause, quick_fix)
    _notify(where, f"{cause}\n\n{quick_fix}", level="warning")
    _log_event("WARN", where, cause, quick_fix)


def _report_success(where: str, detail: str = ""):
    """Clears the failure streak and reports a successful operation."""
    global _consecutive_failures
    _consecutive_failures = 0
    _set_quick_fix(ACTION_NONE)  # something just worked -> nothing left to fix
    _log_event("OK", where, detail, "")
    _refresh_usage()  # at most once a minute


def _report_fallback_if_used(where: str, fallback_info):
    """
    If 'fallback_info' is set (primary_exc, fallback_display_name),
    show a clear notice that the PRIMARY engine failed for this
    translation and the FALLBACK engine produced the result instead.
    Called right before _report_success() for a translation that
    succeeded via fallback. Does nothing if fallback_info is None.
    """
    if not fallback_info:
        return
    primary_exc, fallback_name = fallback_info
    cause, _quick_fix, _action = _diagnose(primary_exc)
    _notify(
        f"{where} (via fallback engine)",
        f"The primary engine ('{_translate_engine}') failed: {cause}\n\n"
        f"Result came from the fallback engine ('{fallback_name}') instead.",
        level="warning",
    )
    _log_event(
        "WARN", f"{where} — fallback engine used",
        f"Primary engine '{_translate_engine}' failed: {cause}",
        f"Used fallback engine '{fallback_name}' for this translation instead.",
    )


def _remember_job(kind: str, text: str, direction: str = "ar-en"):
    """Store the last translation attempt so 'Quick fix -> retry' can repeat it."""
    global _last_job
    with _last_job_lock:
        _last_job = {"kind": kind, "text": text, "direction": direction}


def _retry_last_job():
    """
    Re-run the last translation that was attempted.

    IMPORTANT: the retry never types into whatever window happens to be
    focused now (you may have clicked somewhere else since the failure,
    and blind backspaces there would destroy unrelated text). Instead the
    result is copied to the clipboard and shown in a popup, so you paste
    it wherever you actually want it.
    """
    with _last_job_lock:
        job = dict(_last_job) if _last_job else None

    if not job:
        _report_warning("Nothing to retry",
                        "No failed translation is stored yet.",
                        "Type or select a sentence and press the trigger key first.")
        return

    def _worker():
        try:
            result = _run_translation(job["text"], direction=job["direction"])
        except Exception as e:
            _report_problem("Retry failed", exc=e)
            return
        if not result:
            _report_problem("Retry failed", cause="The engine returned an empty result.",
                            quick_fix="Try a different engine in Settings.",
                            action=ACTION_SETTINGS)
            return
        _set_clipboard_text(result)
        _cache_store(_cache_key(job["text"], job["direction"]), result)  # replace an older cached answer
        _report_success("Retry succeeded", result)
        _show_translation_popup(f"{result}\n\n(copied to clipboard - Ctrl+V to paste)")

    threading.Thread(target=_worker, daemon=True).start()


def _restart_program():
    """
    Relaunch this program from scratch (same interpreter, same arguments)
    and quit the current instance. Used by the 'Quick fix' button when a
    problem is the kind that only a clean restart clears - a dead
    keyboard hook, a wedged engine session, a lost network stack.
    """
    safe_print("[INFO] Restarting the program...")
    try:
        _popup_watcher_stop_event.set()
    except Exception:
        pass
    try:
        keyboard.unhook_all()
    except Exception:
        pass
    try:
        if _tray_icon is not None:
            _tray_icon.visible = False
            _tray_icon.stop()
    except Exception:
        pass
    try:
        if _root is not None:
            _root.destroy()
    except Exception:
        pass
    os.environ["YALLA_RESTARTING"] = "1"  # tells the new copy to wait for this one to finish closing
    try:
        if getattr(sys, "frozen", False):
            # Packaged .exe: re-run the exe itself
            os.execl(sys.executable, sys.executable, *sys.argv[1:])
        else:
            os.execl(sys.executable, sys.executable, *sys.argv)
    except Exception as e:
        safe_print(f"[ERROR] Could not restart automatically: {e}")
        _fatal_error_dialog(f"Could not restart automatically:\n{e}\n\n"
                            "Please close and open the program manually.")
        os._exit(1)


# =========================================================================
# Keystroke tracking (builds the Arabic sentence buffer)
# =========================================================================
NUMBER_PREFIX_EXTRA_CHARS = set(",.%/:-+$")


def _buffer_is_number_prefix(text: str) -> bool:
    """True if the buffer holds only digits/number punctuation/spaces so far
    (i.e. a number typed before any Arabic word)."""
    return all(c.isdigit() or c.isspace() or c in NUMBER_PREFIX_EXTRA_CHARS for c in text)


PASTE_BUFFER_MAX_CHARS = 200


def _append_clipboard_to_buffer():
    """
    Called when Ctrl+V / Shift+Insert is pressed. Instead of wiping the
    tracked sentence (the old behaviour - which is why pasting an English
    word like 'city' in the middle of an Arabic sentence broke the next
    translation), add the pasted text to it so the sentence stays whole
    and the right number of characters gets erased later.
    Only short single-line text is added; anything else resets the buffer.
    """
    global _buffer
    text = _get_clipboard_text()
    usable = (
        bool(text) and len(text) <= PASTE_BUFFER_MAX_CHARS
        and not any(c in text for c in "\r\n\t")
    )
    with _buffer_lock:
        buffer_has_arabic = bool(ARABIC_CHAR_PATTERN.search(_buffer))
        starts_ok = buffer_has_arabic or (
            usable and ARABIC_CHAR_PATTERN.search(text)
            and (not _buffer or _buffer_is_number_prefix(_buffer))
        )
        if usable and starts_ok:
            _buffer += text
        else:
            _buffer = ""
        if DEBUG_MODE:
            safe_print(f"[DEBUG] paste -> buffer={_buffer!r}")


def _on_key_event(event):
    """
    Raw keyboard hook callback. Runs on every key press system-wide.
    Keeps '_buffer' in sync with the Arabic sentence currently being
    typed. The actual translation trigger is handled separately by
    keyboard.add_hotkey() (see _register_hotkey), so this function
    explicitly ignores whatever key(s) make up the current trigger.
    """
    global _buffer

    if not _enabled:
        return  # Master switch is off: don't track anything

    if event.event_type != "down":
        return

    if _busy:
        # A translate/replace operation is currently running and is
        # generating its own synthetic key events (backspace presses,
        # then the translated English letters). Ignore all key
        # tracking while that happens to avoid corrupting the buffer.
        return

    name = (event.name or "").lower()

    # Ignore any key that is part of any of the three hotkey combos
    # (translate / popup / select) - the dedicated hotkey handlers
    # take care of those.
    if (name in _trigger_components or name in _popup_trigger_components
            or name in _select_trigger_components or name in _tone_trigger_components):
        return

    # Other modifier keys alone: ignore, don't touch the buffer
    if name in MODIFIER_KEYS:
        return

    # Paste (Ctrl+V or Shift+Insert): keep the pasted text in the buffer instead
    # of treating it like any other shortcut. The V key's scan code is 47 on every
    # layout (so this also works while the Arabic layout is active).
    scan_code = getattr(event, "scan_code", None)
    if (
        (keyboard.is_pressed("ctrl") and not keyboard.is_pressed("alt")
         and (name == "v" or scan_code == 47))
        or (keyboard.is_pressed("shift") and name == "insert")
    ):
        _append_clipboard_to_buffer()
        return

    # If Ctrl/Alt/Windows is held down, this is very likely a shortcut
    # (Ctrl+C, Alt+Tab, Win+D, etc.), not normal typing - reset and skip
    if keyboard.is_pressed("ctrl") or keyboard.is_pressed("alt") or keyboard.is_pressed("windows"):
        with _buffer_lock:
            _buffer = ""
        return

    # Backspace: keep the buffer in sync if the user manually edits the text
    if name == "backspace":
        with _buffer_lock:
            if _buffer:
                _buffer = _buffer[:-1]
        if DEBUG_MODE:
            safe_print(f"[DEBUG] key='backspace' -> buffer={_buffer!r}")
        return

    # Any of the reset keys: clear the buffer, nothing to translate
    if name in RESET_KEYS:
        with _buffer_lock:
            _buffer = ""
        if DEBUG_MODE:
            safe_print(f"[DEBUG] key='{name}' is a reset key -> buffer cleared")
        return

    # Space: allowed inside the buffer so full sentences can be typed
    if name == "space":
        with _buffer_lock:
            if _buffer:
                _buffer += " "
        if DEBUG_MODE:
            safe_print(f"[DEBUG] key='space' -> buffer={_buffer!r}")
        return

    # ---- Resolve the ACTUAL character this key produces right now ----
    # Try the foreground-layout scan-code lookup first (see
    # _resolve_typed_char above for why this matters for Arabic). Fall
    # back to the 'keyboard' library's own event.name if that lookup
    # is unavailable (non-Windows) or fails for any reason.
    scan_code = getattr(event, "scan_code", 0) or 0
    shift_pressed = keyboard.is_pressed("shift")
    resolved_char = _resolve_typed_char(scan_code, shift_pressed)
    typed_char = resolved_char if len(resolved_char) == 1 else (name if len(name) == 1 else "")

    if DEBUG_MODE:
        safe_print(
            f"[DEBUG] name={name!r} scan_code={scan_code} "
            f"resolved={resolved_char!r} typed_char={typed_char!r} "
            f"(arabic={_is_arabic_char(typed_char) if typed_char else False})"
        )

    # A single printable character: add it to the buffer if it's
    # Arabic, or if we're already mid-sentence, allow ANY printable
    # character (English words, digits, punctuation) to keep being
    # appended too - so a sentence that mixes Arabic and English no
    # longer wipes the buffer the moment an English word shows up. A
    # non-Arabic character only resets the buffer if it arrives BEFORE
    # any Arabic has been typed (i.e. this clearly isn't an Arabic
    # sentence at all).
    if typed_char:
        with _buffer_lock:
            if _is_arabic_char(typed_char):
                _buffer += typed_char
            elif typed_char.isdigit() and (not _buffer or _buffer_is_number_prefix(_buffer)):
                # FIX: a number typed BEFORE the Arabic words (e.g. "20 مليون")
                # used to wipe the buffer, so the digits were never erased
                # and never translated. Now digits can START the buffer.
                _buffer += typed_char
            elif _buffer and _buffer_is_number_prefix(_buffer) and typed_char in NUMBER_PREFIX_EXTRA_CHARS:
                _buffer += typed_char  # e.g. "1,500" or "2.5" or "20%"
            elif _buffer and ARABIC_CHAR_PATTERN.search(_buffer) and typed_char.isprintable():
                _buffer += typed_char
            else:
                _buffer = ""
        return

    # ---- THE MAIN FIX FOR "translation leaves an Arabic word/letter
    # behind" ----
    # We reach here when this keystroke could NOT be resolved to a
    # printable character. That happens for two very different
    # reasons, which used to be treated the same way (wiping the
    # whole buffer) - but shouldn't be:
    #   1) A genuine special/functional key (Print Screen, media
    #      keys, an F-key that isn't the trigger, etc.) - this really
    #      is a context change, so the buffer SHOULD reset.
    #   2) A transient failure to resolve an ordinary character key
    #      (e.g. the foreground-layout lookup above briefly failed,
    #      or hit the dead-key case) while you were still in the
    #      middle of typing an Arabic sentence. This used to silently
    #      wipe everything already buffered, so only the LATER part
    #      of your sentence stayed in the buffer. When you then
    #      pressed the trigger key, only that later part got
    #      translated and erased, leaving the earlier word(s)
    #      untouched on screen next to the English result - exactly
    #      the bug being reported.
    # 'keyboard' names ordinary character keys with a single-character
    # name (e.g. "a", "1", ";"), while real special keys get
    # multi-character names (e.g. "f5", "print screen", "volume up").
    # So: if this looks like an ordinary character key and we already
    # have text buffered, just skip this one keystroke and keep the
    # buffer intact, instead of discarding the whole sentence.
    if len(name) <= 1 and _buffer:
        if DEBUG_MODE:
            safe_print(f"[DEBUG] key='{name}' could not be resolved to a character "
                       f"- ignoring this keystroke, buffer kept as {_buffer!r}")
        return

    with _buffer_lock:
        _buffer = ""
    if DEBUG_MODE:
        safe_print(f"[DEBUG] key='{name}' (unhandled/special) -> buffer cleared")


# =========================================================================
# Translation trigger and replacement
# =========================================================================
def _on_trigger_pressed():
    """Called by keyboard.add_hotkey() when the trigger key is pressed."""
    if not _enabled:
        return
    global _buffer
    with _buffer_lock:
        typed_sentence = _buffer
        _buffer = ""
    threading.Thread(target=_handle_trigger, args=(typed_sentence,), daemon=True).start()


def _try_get_selection():
    """
    Detect whether text is currently SELECTED (with the mouse or the
    keyboard) in the foreground app, using a quick Ctrl+C snapshot:
    remember the clipboard, send Ctrl+C, then check whether the
    clipboard actually changed. If it did, something real was just
    copied - that's our selected sentence. If it didn't, nothing was
    selected (Ctrl+C with no selection normally leaves the clipboard
    untouched).

    Returns (selected_text_or_None, previous_clipboard_text_or_None,
    clipboard_was_changed). Never raises - any failure here just means
    "nothing selected", and the caller falls back to the typed buffer.

    Known limitation: if the clipboard already happened to contain the
    EXACT same text as what's currently selected, this can't tell the
    two apart and will treat it as "nothing selected".
    """
    previous = _get_clipboard_text()
    try:
        keyboard.send("ctrl+c")
        time.sleep(0.15)  # give the foreground app time to write the clipboard
        current = _get_clipboard_text()
    except Exception:
        return None, previous, False

    changed = current != previous
    if changed and current and current.strip():
        return current, previous, True
    return None, previous, changed


def _restore_clipboard(previous_text):
    if previous_text is not None:
        _set_clipboard_text(previous_text)


def _run_translation_inner(sentence: str, direction: str = "ar-en",
                            engine: str = None, custom_provider: str = None) -> str:
    """
    Dispatch to the configured engine. 'direction' is "<from>-<to>",
    e.g. "ar-en" (Arabic -> the chosen target language, used by the
    replace-in-place trigger) or "en-ar" (target language -> Arabic,
    used by the popup-preview trigger) - the target language defaults
    to English but can be any of TARGET_LANGUAGE_PRESETS.
    'engine'/'custom_provider' let a caller override which engine is
    actually used for THIS ONE call (used by the fallback-engine
    feature) without touching the globally saved settings; when
    omitted, the currently selected engine/provider is used as usual.
    Raises on failure. This is the actual (possibly slow/blocking)
    network call - see _run_translation() below for the timeout
    wrapper around it.
    """
    engine = (engine or _translate_engine)
    # 'direction' is always "<from_lang>-<to_lang>" (e.g. "ar-en",
    # "en-ar", "ar-fr", "fr-ar", ...) so any language pair works here,
    # not just Arabic <-> English - see TARGET_LANGUAGE_PRESETS above.
    from_lang, to_lang = direction.split("-", 1)
    if engine == "claude":
        return _translate_via_claude(sentence, from_lang, to_lang)
    elif engine == "gemini":
        return _translate_via_gemini(sentence, from_lang, to_lang)
    elif engine == "deepl":
        return _translate_via_deepl(sentence, from_lang, to_lang)
    elif engine == "custom":
        return _translate_via_custom_ai(sentence, from_lang, to_lang, provider_name=custom_provider)
    else:
        # 'timeout' here bounds the actual socket/connect/read time
        # inside the 'translators' library itself (it defaults to
        # None = no timeout, i.e. it can hang for minutes on a dead
        # or blocked connection). This is the main fix for engines
        # like google/bing/baidu.
        return ts.translate_text(
            sentence, translator=engine, from_language=from_lang, to_language=to_lang,
            timeout=TRANSLATION_TIMEOUT_SECONDS,
        )


def _run_translation(sentence: str, direction: str = "ar-en",
                      engine: str = None, custom_provider: str = None) -> str:
    """
    Same as _run_translation_inner(), but additionally guarantees the
    call can NEVER block the caller for longer than
    TRANSLATION_TIMEOUT_SECONDS, no matter what the underlying engine
    or library does. This belt-and-suspenders wrapper matters because:
      - the 'timeout' kwarg passed to ts.translate_text() only bounds
        each individual HTTP request; some engines internally retry
        several times on failure, so the total time can still add up
        to multiple timeouts back-to-back.
      - the claude/gemini SDKs are called without their own explicit
        timeout below in some setups, so this wrapper is what actually
        enforces a hard ceiling for them too.
    Raises TimeoutError if the deadline is hit, or whatever exception
    the engine itself raised otherwise.
    """
    result_holder = {}

    def _worker():
        try:
            result_holder["value"] = _run_translation_inner(
                sentence, direction, engine=engine, custom_provider=custom_provider)
        except Exception as e:
            result_holder["error"] = e

    worker_thread = threading.Thread(target=_worker, daemon=True)
    worker_thread.start()
    worker_thread.join(timeout=TRANSLATION_TIMEOUT_SECONDS)

    used_engine = engine or _translate_engine
    if worker_thread.is_alive():
        # The worker thread is left running in the background (daemon
        # thread, harmless) since Python cannot forcibly kill a thread,
        # but the caller is freed immediately instead of waiting on it.
        raise TimeoutError(
            f"Translation engine '{used_engine}' did not respond within "
            f"{TRANSLATION_TIMEOUT_SECONDS} seconds. Check your internet connection, "
            f"or try a different engine from Settings."
        )
    if "error" in result_holder:
        raise result_holder["error"]
    return result_holder.get("value", "")


# -------------------------------------------------------------------
# Fallback engine (see _fallback_engine above): if the primary engine
# fails for a given sentence, we retry that SAME sentence once with
# the chosen fallback engine, without ever changing the saved primary
# engine setting.
# -------------------------------------------------------------------
def _parse_fallback_engine(value: str):
    """
    '_fallback_engine' -> (engine_id, custom_provider_name_or_None).
    "none"/""            -> (None, None)
    "custom:ProviderName" -> ("custom", "ProviderName")
    "google" (etc.)       -> ("google", None)
    """
    value = (value or "none").strip()
    if not value or value == "none":
        return None, None
    if value.startswith("custom:"):
        return "custom", value.split(":", 1)[1]
    return value, None


def _fallback_engine_display_name(value: str = None) -> str:
    """Human-friendly label for a stored fallback-engine value."""
    engine, provider = _parse_fallback_engine(value if value is not None else _fallback_engine)
    if engine is None:
        return "None"
    if engine == "custom":
        return f"custom ({provider})" if provider else "custom"
    return engine


def _translate_with_fallback(sentence: str, direction: str = "ar-en"):
    """
    Try the primary engine first. If it fails AND a fallback engine is
    configured (and is actually different from the primary), retry the
    SAME sentence once with the fallback engine.

    Returns (translated_text, fallback_info) where fallback_info is
    None if the primary engine succeeded, or (primary_exc,
    fallback_display_name) if the fallback engine had to be used.

    Raises the primary exception if the primary engine fails and there
    is no usable fallback, or if the fallback ALSO fails (so the
    reported problem still reflects the primary/saved engine).
    """
    cache_key = _cache_key(sentence, direction)
    cached = _cache_lookup(cache_key)
    if cached is not None:
        safe_print("[INFO] Using the remembered (cached) translation - no engine call made.")
        return cached, None
    try:
        result = _run_translation(sentence, direction)
        _cache_store(cache_key, result)
        return result, None
    except Exception as primary_exc:
        fb_engine, fb_provider = _parse_fallback_engine(_fallback_engine)
        if fb_engine is None:
            raise
        is_same_as_primary = (
            fb_engine == _translate_engine and
            (fb_engine != "custom" or fb_provider == _custom_provider_selected)
        )
        if is_same_as_primary:
            raise
        try:
            result = _run_translation(sentence, direction, engine=fb_engine, custom_provider=fb_provider)
        except Exception:
            # Fallback failed too - report the ORIGINAL (primary) failure,
            # since the primary engine is what's saved in Settings.
            raise primary_exc
        return result, (primary_exc, _fallback_engine_display_name())


def _translate_selection(sentence: str, previous_clipboard):
    """
    Translate a MOUSE-SELECTED sentence and replace it. The text is
    still selected in the target app, so pasting over it replaces it
    in one shot - no backspacing needed. This also means that if the
    translation call FAILS, nothing on screen is touched at all (the
    original selection is left exactly as it was), so you never lose
    what you selected just because a translation glitched.
    """
    direction = f"ar-{_target_language}"
    _remember_job("selection", sentence, direction)
    _working_show()
    try:
        translated_text, fallback_info = _translate_with_fallback(sentence, direction)
    except Exception as e:
        safe_print(f"[ERROR] Translation failed: {e}")
        _report_problem("Translation failed (selected text)", exc=e)
        _restore_clipboard(previous_clipboard)
        return

    if not translated_text:
        safe_print("[WARNING] No translated text was returned.")
        _report_problem(
            "Empty translation",
            cause=f"The '{_translate_engine}' engine answered, but returned no text - "
                  f"your selection was left untouched.",
            quick_fix="Press 'Quick fix' to try again, or switch engine in Settings.",
            action=ACTION_RETRY,
        )
        _restore_clipboard(previous_clipboard)
        return

    _set_clipboard_text(translated_text)
    time.sleep(0.05)
    keyboard.send("ctrl+v")
    time.sleep(0.05)
    _restore_clipboard(previous_clipboard)

    safe_print(f"[OK] Replaced selection with: {translated_text}")
    _report_fallback_if_used("Selection translated", fallback_info)
    _report_success("Selection translated", translated_text)


def _translate_selection_auto_direction(sentence: str, previous_clipboard):
    """
    Used by the independent "Select-translate" hotkey (_select_trigger_key,
    default F4): translate a MOUSE-SELECTED sentence in WHICHEVER
    direction fits its content - Arabic -> English if the selection
    contains Arabic, English -> Arabic otherwise - and paste the result
    back over the selection. Does not touch, and is not affected by,
    the older typed-buffer + trigger-key (F3) flow at all.
    """
    direction = f"ar-{_target_language}" if ARABIC_CHAR_PATTERN.search(sentence) else f"{_target_language}-ar"
    _remember_job("select", sentence, direction)
    _working_show()
    try:
        translated_text, fallback_info = _translate_with_fallback(sentence, direction)
    except Exception as e:
        safe_print(f"[ERROR] Select-translate failed: {e}")
        _report_problem("Select-translate failed", exc=e)
        _restore_clipboard(previous_clipboard)
        return

    if not translated_text:
        safe_print("[WARNING] No translated text was returned.")
        _report_problem(
            "Empty translation",
            cause=f"The '{_translate_engine}' engine answered, but returned no text - "
                  f"your selection was left untouched.",
            quick_fix="Press 'Quick fix' to try again, or switch engine in Settings.",
            action=ACTION_RETRY,
        )
        _restore_clipboard(previous_clipboard)
        return

    _set_clipboard_text(translated_text)
    time.sleep(0.05)
    keyboard.send("ctrl+v")
    time.sleep(0.05)
    _restore_clipboard(previous_clipboard)

    safe_print(f"[OK] Select-translate replaced selection with: {translated_text}")
    _report_fallback_if_used("Select-translate", fallback_info)
    _report_success("Select-translate", translated_text)


def _on_select_trigger_pressed():
    """Called by keyboard.add_hotkey() when the Select-translate key is pressed."""
    if not _enabled:
        return
    threading.Thread(target=_handle_select_trigger, daemon=True).start()


def _handle_select_trigger():
    """
    Runs on the Select-translate hotkey. Grabs whatever is currently
    selected with the mouse (or keyboard) in the foreground app via a
    Ctrl+C snapshot, and - if anything was actually selected -
    translates it with the direction auto-detected from its content.
    Completely independent from the typed-buffer trigger (F3): it
    never reads or clears '_buffer'.
    """
    global _busy
    _busy = True
    try:
        selected_sentence, previous_clipboard, clipboard_changed = _try_get_selection()

        if selected_sentence and selected_sentence.strip():
            _translate_selection_auto_direction(selected_sentence, previous_clipboard)
            return

        if clipboard_changed:
            _restore_clipboard(previous_clipboard)

        safe_print("[INFO] Select-translate pressed, but nothing appears to be selected.")
        _report_warning(
            "Nothing to translate",
            "No text seems to be selected right now.",
            f"Select a sentence with the mouse (Arabic or English), then press "
            f"{_select_trigger_key.upper()}.",
            action=ACTION_NONE,
        )
    finally:
        time.sleep(0.05)
        _working_hide()
        _busy = False


def _translate_typed_buffer(arabic_sentence: str, app_name: str = ""):
    """
    Translate the sentence tracked from your own typing, and replace
    it in-place at the current cursor position using the original
    backspace-then-retype approach (there's no "selection" to paste
    over here, since this text was typed, not selected).

    The delay between each simulated keypress comes from the current
    typing-speed profile (_key_delay - see TYPING_SPEED_PRESETS and
    the Settings window): faster profiles feel snappier in normal
    apps, but games/emulators that drop fast synthetic input need the
    slower "safe" profile to avoid dropped or scrambled characters.
    """
    direction = f"ar-{_target_language}"
    _remember_job("typed", arabic_sentence, direction)
    _working_show()
    try:
        translated_text, fallback_info = _translate_with_fallback(arabic_sentence, direction)
    except Exception as e:
        safe_print(f"[ERROR] Translation failed: {e}")
        _report_problem("Translation failed (typed text)", exc=e)
        return

    if not translated_text:
        safe_print("[WARNING] No translated text was returned.")
        _report_problem(
            "Empty translation",
            cause=f"The '{_translate_engine}' engine answered, but returned no text - "
                  f"what you typed was left untouched.",
            quick_fix="Press 'Quick fix' to try again, or switch engine in Settings.",
            action=ACTION_RETRY,
        )
        return

    _working_set_text("جاري الكتابة")  # translation is ready - now erasing/typing

    # Typing speed can differ per program (e.g. 'safe' in BlueStacks).
    speed_profile = _effective_speed_profile(app_name)
    key_delay = TYPING_SPEED_PRESETS[speed_profile]
    if DEBUG_MODE:
        safe_print(f"[DEBUG] target app={app_name!r} speed={speed_profile} delay={key_delay}")

    delete_count = len(arabic_sentence)
    for _ in range(delete_count):
        keyboard.send("backspace")
        time.sleep(key_delay)

    # Long translations are pasted in one go (faster and safer than typing
    # every key) - except in 'safe' mode, which exists for apps that dislike
    # fast synthetic input, and when the clipboard holds a non-text item.
    pasted = False
    if speed_profile != "safe" and _paste_threshold > 0 and len(translated_text) > _paste_threshold:
        pasted = _paste_text_via_clipboard(translated_text)
    if not pasted:
        keyboard.write(translated_text, delay=key_delay)

    safe_print(f"[OK] Replaced with: {translated_text}")
    _report_fallback_if_used("Typed text translated", fallback_info)
    _report_success("Typed text translated", translated_text)


def _handle_trigger(typed_sentence: str):
    """
    Runs on trigger key press. Prefers a MOUSE-SELECTED sentence over
    the typed buffer (see _try_get_selection); falls back to whatever
    was typed if nothing is currently selected.
    """
    global _busy
    _busy = True
    try:
        target_app = _get_foreground_process_name()  # who we are typing into
        selected_sentence, previous_clipboard, clipboard_changed = _try_get_selection()

        if selected_sentence and ARABIC_CHAR_PATTERN.search(selected_sentence):
            _translate_selection(selected_sentence, previous_clipboard)
            return

        if clipboard_changed:
            # We copied something via Ctrl+C but it had no Arabic in
            # it - put the user's original clipboard back untouched.
            _restore_clipboard(previous_clipboard)

        if typed_sentence and ARABIC_CHAR_PATTERN.search(typed_sentence):
            _translate_typed_buffer(typed_sentence, target_app)
        else:
            # Diagnostic message: this tells us WHY nothing happened.
            if not typed_sentence and not selected_sentence:
                safe_print("[INFO] Trigger pressed, but nothing is selected and the "
                           "buffer was empty - nothing was captured as Arabic text. "
                           "Select a sentence with the mouse, or type one, then press "
                           "the trigger key. Set DEBUG_MODE = True at the top of the "
                           "settings section to see exactly what each keypress is read as.")
                _report_warning(
                    "Nothing to translate",
                    "Nothing was selected and the typed buffer was empty.",
                    "Select a sentence with the mouse, or type one, then press "
                    f"{_trigger_key.upper()}. If typing never fills the buffer, make sure "
                    "the Arabic keyboard layout is active and that the program runs as "
                    "Administrator.",
                    action=ACTION_NONE,
                )
            else:
                safe_print("[INFO] Trigger pressed, but no Arabic text was detected "
                           "in the selection or the typed buffer.")
                _report_warning(
                    "Nothing to translate",
                    "Text was captured, but it contained no Arabic characters.",
                    "Only Arabic text is translated by this key. For "
                    f"{TARGET_LANGUAGE_CODE_TO_NAME.get(_target_language, _target_language)} -> Arabic, "
                    f"turn on auto-popup mode with {_popup_trigger_key.upper()}.",
                    action=ACTION_NONE,
                )
    finally:
        time.sleep(0.05)
        _working_hide()
        _busy = False


# =========================================================================
# English -> Arabic "auto popup" mode (toggled on/off by a hotkey,
# e.g. F10) - while ON, ANY copy (Ctrl+C, right-click Copy, long-press
# "Copy" on touch devices, etc.) automatically shows a popup with the
# Arabic translation. No need to press anything after copying.
# =========================================================================
_popup_auto_mode = False
_popup_watcher_thread = None
_popup_watcher_stop_event = threading.Event()


def _on_popup_trigger_pressed():
    """Called by keyboard.add_hotkey() when the popup-trigger key is pressed - TOGGLES auto EN->AR popup mode on/off."""
    if not _enabled:
        return
    _toggle_popup_auto_mode()


def _toggle_popup_auto_mode():
    global _popup_auto_mode, _popup_watcher_thread, _popup_watcher_stop_event
    _popup_auto_mode = not _popup_auto_mode
    if _popup_auto_mode:
        _popup_watcher_stop_event = threading.Event()
        _popup_watcher_thread = threading.Thread(target=_popup_watcher_loop, daemon=True)
        _popup_watcher_thread.start()
        safe_print("[INFO] Auto EN -> AR popup mode: ON - copy any English text "
                   "(mouse or Ctrl+C) and its Arabic translation will pop up automatically.")
        _notify("Auto popup translation", "Turned ON - copy English text to see its Arabic translation.")
        _log_event("INFO", "Auto EN → AR popup mode ON", "", "")
    else:
        _popup_watcher_stop_event.set()
        safe_print("[INFO] Auto EN -> AR popup mode: OFF.")
        _notify("Auto popup translation", "Turned OFF.")
        _log_event("INFO", "Auto EN → AR popup mode OFF", "", "")
    _refresh_ui()


def _popup_watcher_loop():
    """
    Runs in its own thread while auto-popup mode is ON. Polls
    GetClipboardSequenceNumber (a counter Windows bumps every time
    ANYTHING is copied, by any method - mouse "Copy", Ctrl+C, etc.) so
    we catch every copy, not just Ctrl+C. When it changes, we read the
    new clipboard text and, if it looks like non-Arabic text, translate
    it to Arabic and show the popup.
    """
    last_seq = _get_clipboard_sequence()
    while not _popup_watcher_stop_event.is_set():
        time.sleep(0.15)
        if _busy or not _enabled:
            continue  # our own clipboard use (e.g. the F9 replace flow) - ignore
        seq = _get_clipboard_sequence()
        if seq is None or seq == last_seq:
            continue
        last_seq = seq

        text = _get_clipboard_text()
        if not text or not text.strip():
            continue
        if ARABIC_CHAR_PATTERN.search(text):
            continue  # already Arabic - nothing to do here
        threading.Thread(target=_auto_translate_and_popup, args=(text,), daemon=True).start()


def _auto_translate_and_popup(english_text: str):
    """Translate 'english_text' to Arabic and show it in the popup. Never touches the clipboard."""
    global _busy
    _busy = True
    try:
        direction = f"{_target_language}-ar"
        _remember_job("popup", english_text, direction)
        try:
            translated_text, fallback_info = _translate_with_fallback(english_text, direction=direction)
        except Exception as e:
            safe_print(f"[ERROR] Translation failed: {e}")
            _report_problem("Auto-popup translation failed", exc=e)
            return
        if not translated_text:
            _report_problem(
                "Empty translation",
                cause=f"The '{_translate_engine}' engine returned no text for the copied English.",
                quick_fix="Press 'Quick fix' to try again, or switch engine in Settings.",
                action=ACTION_RETRY,
            )
            return
        safe_print(f"[OK] Auto popup translation: {translated_text}")
        _report_fallback_if_used("Auto-popup translation", fallback_info)
        _report_success("Auto-popup translation", translated_text)
        _show_translation_popup(translated_text)
    finally:
        time.sleep(0.05)
        _busy = False


def _show_translation_popup(arabic_text: str, duration_ms: int = 9000):
    """
    Show a small, borderless, always-on-top popup near the mouse
    cursor with the Arabic translation, and auto-close it after
    'duration_ms' (or on click).

    This used to create its own throwaway tk.Tk() inside a background
    thread. Now that the program owns a real main window, there is
    exactly ONE Tk root and it lives on the main thread, so this call
    is forwarded there through the UI queue (Tk is not thread-safe).
    """
    _ui_call(_show_translation_popup_on_main_thread, arabic_text, duration_ms)


def _show_translation_popup_on_main_thread(arabic_text: str, duration_ms: int = 9000):
    """Actual popup construction - only ever runs on the Tk main thread."""
    try:
        win = tk.Toplevel(_root)
        win.overrideredirect(True)   # no title bar / window borders
        win.attributes("-topmost", True)
        try:
            win.attributes("-alpha", 0.96)
        except Exception:
            pass

        frame = tk.Frame(win, bg="#1f1f1f", highlightbackground="#444", highlightthickness=1)
        frame.pack()

        tk.Label(
            frame, text=arabic_text, font=("Segoe UI", 12), fg="white", bg="#1f1f1f",
            justify="right", anchor="e", wraplength=360, padx=14, pady=10,
        ).pack()
        tk.Label(
            frame, text="(click to dismiss)", font=("Arial", 7), fg="#888", bg="#1f1f1f",
        ).pack(pady=(0, 6))

        win.update_idletasks()

        # Position near the current mouse cursor, kept on-screen
        mouse_x, mouse_y = win.winfo_pointerx(), win.winfo_pointery()
        w, h = win.winfo_reqwidth(), win.winfo_reqheight()
        x = min(max(mouse_x - w // 2, 0), max(win.winfo_screenwidth() - w, 0))
        y = min(mouse_y + 20, max(win.winfo_screenheight() - h, 0))
        win.geometry(f"{w}x{h}+{x}+{y}")

        win.after(duration_ms, win.destroy)
        for widget in (win, frame):
            widget.bind("<Button-1>", lambda e: win.destroy())
    except Exception as e:
        safe_print(f"[ERROR] Could not show translation popup: {e}")


_LANG_NAMES = {"ar": "Arabic", **TARGET_LANGUAGE_CODE_TO_NAME}


def _estimate_max_tokens(text: str) -> int:
    """
    A token budget for the translation reply, sized to the INPUT
    length instead of a flat number - a flat 300 is plenty for a
    short sentence but silently cuts a long paragraph off mid-word.
    ~4 characters per token is a rough but common rule of thumb, and
    a translation can run longer than the original, so the estimate
    is padded up and then clamped to a sane range.
    """
    estimate = int(len(text) / 4 * 3) + 120
    return max(300, min(estimate, 4096))


def _build_ai_prompt(sentence: str, from_name: str, to_name: str) -> str:
    """One shared, context-aware prompt for every AI engine."""
    return (
        f"You are a professional human translator. Translate the {from_name} text "
        f"below into natural, fluent {to_name}, the way a native speaker would "
        f"actually say it.\n"
        f"Rules:\n"
        f"- Translate the MEANING, not word-by-word. Never translate literally "
        f"if it sounds unnatural; use the idiom a native speaker would use.\n"
        f"- The text may be in a dialect (e.g. Egyptian Arabic) or informal chat "
        f"style: understand the intent and keep the same tone/register.\n"
        f"- Keep every number exactly as written (e.g. '20 مليون' -> '20 million'). "
        f"Never drop, change, or move numbers, names, or symbols.\n"
        f"- Keep any English words, brand names, URLs, and emojis as they are.\n"
        f"- {TONE_PRESETS.get(_translation_tone, TONE_PRESETS[DEFAULT_TONE])}\n"
        f"- Reply with ONLY the translated text: no quotes, no notes, no explanation.\n\n"
        f"Text:\n" + sentence
    )


def _translate_via_claude(sentence: str, from_lang: str = "ar", to_lang: str = "en") -> str:
    """
    Translate 'sentence' from 'from_lang' to 'to_lang' using the
    Anthropic Claude API. Requires a valid API key saved via Settings.
    Raises on any failure - the caller (_run_translation) handles
    errors.
    """
    if not _ANTHROPIC_AVAILABLE:
        raise RuntimeError("The 'anthropic' library is not installed. Run: pip install anthropic")
    if not _claude_api_key:
        raise RuntimeError("No Claude API key is set. Open Settings and paste your key first.")

    from_name = _LANG_NAMES.get(from_lang, from_lang)
    to_name = _LANG_NAMES.get(to_lang, to_lang)

    client = Anthropic(api_key=_claude_api_key, timeout=TRANSLATION_TIMEOUT_SECONDS)
    response = client.messages.create(
        model=CLAUDE_MODEL,
        max_tokens=_estimate_max_tokens(sentence),
        messages=[{
            "role": "user",
            "content": _build_ai_prompt(sentence, from_name, to_name),
        }],
    )
    return response.content[0].text.strip()


def _translate_via_gemini(sentence: str, from_lang: str = "ar", to_lang: str = "en") -> str:
    """
    Translate 'sentence' from 'from_lang' to 'to_lang' using the Google
    Gemini API (model: gemini-3.5-flash-lite) via the 'google-genai'
    SDK. Requires a valid API key saved via Settings. Raises on any
    failure - the caller (_run_translation) handles errors.
    """
    if not _GEMINI_AVAILABLE:
        raise RuntimeError("The 'google-genai' library is not installed. Run: pip install google-genai")
    if not _gemini_api_key:
        raise RuntimeError("No Gemini API key is set. Open Settings and paste your key first.")

    from_name = _LANG_NAMES.get(from_lang, from_lang)
    to_name = _LANG_NAMES.get(to_lang, to_lang)

    client = genai.Client(api_key=_gemini_api_key)
    response = client.models.generate_content(
        model=GEMINI_MODEL,
        contents=_build_ai_prompt(sentence, from_name, to_name),
    )
    return (response.text or "").strip()


# DeepL's TARGET-language codes need a regional variant for English
# ("EN-US"/"EN-GB") and Portuguese ("PT-PT"/"PT-BR"); the SOURCE
# language is always the plain base code (just "EN", never "EN-US").
# Everything else (AR, DE, ES, FR, IT, NL, TR, RU, ZH, JA, KO, ID, ...)
# uses the same base code on both sides, so falling back to
# from_lang.upper()/to_lang.upper() is correct for those without
# needing an entry here at all. Languages DeepL does not support at
# all (e.g. Persian/Farsi, Urdu, Hindi, Swahili, Hebrew, as of this
# writing) simply raise a clear error from DeepL itself if selected -
# pick a different engine (google/claude/gemini/custom) for those.
_DEEPL_SOURCE_LANG_CODES = {"en": "EN"}
_DEEPL_TARGET_LANG_CODES = {"en": "EN-US", "pt": "PT-PT"}


def _translate_via_deepl(sentence: str, from_lang: str = "ar", to_lang: str = "en") -> str:
    """
    Translate 'sentence' from 'from_lang' to 'to_lang' using the DeepL
    API. Requires a valid API key saved via Settings (either a Free or
    Pro DeepL account key both work the same way). Raises on any
    failure - the caller (_run_translation) handles errors.
    """
    if not _DEEPL_AVAILABLE:
        raise RuntimeError("The 'deepl' library is not installed. Run: pip install deepl")
    if not _deepl_api_key:
        raise RuntimeError("No DeepL API key is set. Open Settings and paste your key first.")

    source_code = _DEEPL_SOURCE_LANG_CODES.get(from_lang, from_lang.upper())
    target_code = _DEEPL_TARGET_LANG_CODES.get(to_lang, to_lang.upper())

    translator = deepl.Translator(_deepl_api_key)
    result = translator.translate_text(sentence, source_lang=source_code, target_lang=target_code)
    return (result.text or "").strip()


def _translate_via_custom_ai(sentence: str, from_lang: str = "ar", to_lang: str = "en",
                             provider_name: str = None) -> str:
    """
    Translate 'sentence' using a "custom" AI provider (see
    _custom_providers above). By default uses whichever provider is
    currently selected in Settings (_custom_provider_selected); pass
    'provider_name' to use a specific saved provider instead (used by
    the fallback-engine feature, so the fallback can point at a
    DIFFERENT custom provider than the primary one). Works with ANY
    provider that speaks the OpenAI-compatible chat-completions API -
    this covers OpenAI itself, OpenRouter (which alone re-exposes
    hundreds of models, including Claude/Gemini/Llama/DeepSeek/Grok),
    Groq, DeepSeek, Mistral, Together, Fireworks, and local servers
    like Ollama or LM Studio. Adding a new provider is done entirely
    from Settings - this function never needs to change.
    Raises on any failure - the caller (_run_translation) handles
    errors.
    """
    provider_name = provider_name or _custom_provider_selected
    if not provider_name or provider_name not in _custom_providers:
        raise RuntimeError(
            "No custom AI provider is selected. Open Settings, pick the "
            "'custom' engine, and add/select a provider first."
        )

    provider = _custom_providers[provider_name]
    base_url = (provider.get("base_url") or "").strip().rstrip("/")
    api_key = (provider.get("api_key") or "").strip()
    model = (provider.get("model") or "").strip()

    if not base_url or not model:
        raise RuntimeError(
            f"The custom provider '{provider_name}' is missing its "
            "Base URL or Model name. Open Settings and edit it."
        )

    from_name = _LANG_NAMES.get(from_lang, from_lang)
    to_name = _LANG_NAMES.get(to_lang, to_lang)
    prompt = _build_ai_prompt(sentence, from_name, to_name)

    body = json.dumps({
        "model": model,
        "messages": [{"role": "user", "content": prompt}],
        "max_tokens": _estimate_max_tokens(sentence),
    }).encode("utf-8")

    headers = {"Content-Type": "application/json"}
    if api_key:
        headers["Authorization"] = f"Bearer {api_key}"

    request = urllib.request.Request(
        f"{base_url}/chat/completions", data=body, headers=headers, method="POST"
    )
    try:
        with urllib.request.urlopen(request, timeout=TRANSLATION_TIMEOUT_SECONDS) as resp:
            payload = json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        # Surface the provider's own error body (often has a clear
        # message like "invalid_api_key" or "rate_limit_exceeded") so
        # _diagnose() above can classify it correctly.
        detail = ""
        try:
            detail = e.read().decode("utf-8", errors="replace")
        except Exception:
            pass
        raise RuntimeError(f"HTTP {e.code} {e.reason} from '{provider_name}': {detail}") from e
    except urllib.error.URLError as e:
        raise RuntimeError(f"Could not reach '{base_url}': {e.reason}") from e

    try:
        return (payload["choices"][0]["message"]["content"] or "").strip()
    except (KeyError, IndexError, TypeError):
        raise RuntimeError(
            f"The '{provider_name}' provider returned an unexpected "
            f"response shape: {payload}"
        )


def _test_custom_provider_connection(base_url: str, api_key: str, model: str):
    """
    Send ONE tiny chat-completion request to check that 'base_url' +
    'model' + 'api_key' actually work together, without saving
    anything. Used by the "Test connection" button in the
    add/edit-provider window, before the user commits to Apply.
    Never raises - returns (ok: bool, message: str) so it can be
    called directly from a background thread.
    """
    base_url = base_url.strip().rstrip("/")
    if not base_url or not model:
        return False, "Base URL و Model لازم يتملوا الأول."

    body = json.dumps({
        "model": model,
        "messages": [{"role": "user", "content": "Reply with only the word: OK"}],
        "max_tokens": 5,
    }).encode("utf-8")
    headers = {"Content-Type": "application/json"}
    if api_key:
        headers["Authorization"] = f"Bearer {api_key}"
    request = urllib.request.Request(
        f"{base_url}/chat/completions", data=body, headers=headers, method="POST"
    )
    try:
        with urllib.request.urlopen(request, timeout=TEST_CONNECTION_TIMEOUT_SECONDS) as resp:
            payload = json.loads(resp.read().decode("utf-8"))
        payload["choices"][0]["message"]["content"]  # confirms the response shape is right
        return True, "شغال - الاتصال والرد تمام."
    except urllib.error.HTTPError as e:
        detail = ""
        try:
            detail = e.read().decode("utf-8", errors="replace")[:1500]
        except Exception:
            pass
        return False, f"HTTP {e.code} {e.reason} - {detail}"
    except urllib.error.URLError as e:
        return False, f"تعذر الوصول لـ {base_url}: {e.reason}"
    except (KeyError, IndexError, TypeError):
        return False, "الرد وصل لكن شكله مش OpenAI-compatible."
    except Exception as e:
        return False, str(e)


def _fetch_custom_provider_models(base_url: str, api_key: str):
    """
    GET {base_url}/models (the OpenAI-compatible model-listing
    endpoint, supported by OpenAI/OpenRouter/Groq/Ollama/etc.) and
    return the available model IDs. Used by the "Fetch models"
    button in the add/edit-provider window. Never raises - returns
    (ok: bool, list_of_ids_or_error_message).
    """
    base_url = base_url.strip().rstrip("/")
    if not base_url:
        return False, "اكتب الـ Base URL الأول."

    headers = {}
    if api_key:
        headers["Authorization"] = f"Bearer {api_key}"
    request = urllib.request.Request(f"{base_url}/models", headers=headers, method="GET")
    try:
        with urllib.request.urlopen(request, timeout=TEST_CONNECTION_TIMEOUT_SECONDS) as resp:
            payload = json.loads(resp.read().decode("utf-8"))
        ids = sorted({item.get("id", "") for item in payload.get("data", []) if item.get("id")})
        if not ids:
            return False, "السيرفر رد، لكن مفيهوش موديلات في الرد."
        return True, ids
    except urllib.error.HTTPError as e:
        detail = ""
        try:
            detail = e.read().decode("utf-8", errors="replace")[:1500]
        except Exception:
            pass
        return False, f"HTTP {e.code} {e.reason} - {detail}"
    except urllib.error.URLError as e:
        return False, f"تعذر الوصول لـ {base_url}: {e.reason}"
    except Exception as e:
        return False, str(e)


# ---------------------------------------------------------------------
# Estimated translation quality (%) per model - shown in the model list
# ---------------------------------------------------------------------
# IMPORTANT: this is an ESTIMATE from the model's family / tier / size
# (e.g. "pro" > "flash" > "lite", 70B > 8B). It is NOT a live benchmark.
# To force your own number for a model, add a part of its name below,
# e.g. "gemini-3.5-flash": 94. The first matching key wins.
MODEL_QUALITY_OVERRIDES = {
    # "gemini-3.5-flash": 94,
}

_NOT_FOR_TRANSLATION = (
    "embed", "tts", "whisper", "audio", "image", "imagen", "dall-e", "moderation",
    "rerank", "guard", "transcribe", "speech", "realtime", "video", "veo", "sora",
)


def _estimate_model_quality(model_id: str):
    """Return an estimated Arabic<->English translation quality 0-99, or None if not a text model."""
    m = (model_id or "").lower()
    for key, value in MODEL_QUALITY_OVERRIDES.items():
        if key.lower() in m:
            return int(value)
    if any(word in m for word in _NOT_FOR_TRANSLATION):
        return None

    # parameter size in billions (e.g. "70b", "8b", "235b-a22b")
    sizes = [float(x) for x in re.findall(r"(\d+(?:\.\d+)?)b\b", m)]
    size = max(sizes) if sizes else None

    if "opus" in m:            score = 95
    elif "sonnet" in m:        score = 92
    elif "haiku" in m:         score = 82
    elif "claude" in m:        score = 88
    elif "gemini" in m:
        if "flash-lite" in m or "flash_lite" in m: score = 78
        elif "flash" in m:     score = 87
        elif "pro" in m:       score = 94
        else:                  score = 85
    elif "gpt-5" in m:         score = 92
    elif "gpt-4.1" in m:       score = 88
    elif "gpt-4o" in m:        score = 86
    elif "gpt-4" in m:         score = 84
    elif "gpt-3.5" in m:       score = 70
    elif re.search(r"(^|[/\-])o[134](-|$)", m): score = 86
    elif "deepseek" in m:      score = 85
    elif "qwen" in m:
        score = 86 if (size and size >= 70) or "max" in m or "plus" in m else 76
    elif "llama" in m:
        score = 82 if (size and size >= 65) else 66
    elif "mixtral" in m:       score = 74
    elif "mistral" in m:
        score = 84 if "large" in m else (80 if "medium" in m else 70)
    elif "command" in m:       score = 80
    elif "gemma" in m:
        score = 78 if (size and size >= 20) else (72 if (size and size >= 9) else 62)
    elif "glm" in m or "kimi" in m or "grok" in m:
        score = 86
    elif size:
        score = 55 + min(28, int(size ** 0.5 * 2.2))
    else:
        score = 62

    # tier modifiers
    if re.search(r"(?<![a-z])(nano|tiny)(?![a-z])", m):   score -= 15
    elif re.search(r"(?<![a-z])(mini|lite)(?![a-z])", m): score -= 8   # not the 'mini' inside 'gemini'
    elif re.search(r"(?<![a-z])small(?![a-z])", m):       score -= 5
    if "preview" in m or "-exp" in m: score -= 2

    # newer version number in the name = a small bonus
    cleaned = re.sub(r"\d+(?:\.\d+)?b\b", "", m)
    cleaned = re.sub(r"\d{4}-?\d{2}-?\d{2}|\b\d{4}\b", "", cleaned)
    versions = [float(x) for x in re.findall(r"(?<![\d.])(\d{1,2}(?:\.\d{1,2})?)", cleaned) if float(x) < 20]
    if versions:
        score += max(0, min(3, int(round((max(versions) - 2) * 1.0))))

    return max(20, min(99, score))


_MODEL_SUFFIX_RE = re.compile(r"\s+\[(?:\d{1,3}%|n/a)\]\s*$")


def _strip_model_suffix(text: str) -> str:
    """'google/gemini-3.5-flash   [87%]' -> 'google/gemini-3.5-flash'."""
    return _MODEL_SUFFIX_RE.sub("", text or "").strip()


def _models_with_quality(ids):
    """Sort model ids best-first and tag each with its estimated quality."""
    scored = [(mid, _estimate_model_quality(mid)) for mid in ids]
    scored.sort(key=lambda t: (t[1] is None, -(t[1] or 0), t[0]))
    return [f"{mid}   [{q}%]" if q is not None else f"{mid}   [n/a]" for mid, q in scored]


def _register_hotkey(key_combo: str) -> bool:
    """
    Register 'key_combo' (e.g. "f3" or "ctrl+alt+space") as the new
    trigger, replacing any previously registered one, and save it so
    it's remembered next time the program starts. Returns True on
    success, False if the combo could not be registered.
    """
    global _hotkey_handle, _trigger_key, _trigger_components

    key_combo = key_combo.strip().lower()
    if not key_combo:
        return False

    parts = {p.strip() for p in key_combo.split("+")}

    # Reject combos made ONLY of modifier keys (ctrl/alt/shift/windows)
    # with nothing else - these overlap with reserved OS shortcuts like
    # Ctrl+Shift (keyboard layout switch) or Alt+Shift, and are
    # unreliable to detect as a result. Require at least one real key.
    ONLY_MODIFIER_NAMES = {"ctrl", "alt", "shift", "windows"}
    if parts and parts.issubset(ONLY_MODIFIER_NAMES):
        safe_print(
            f"[ERROR] '{key_combo}' is made only of modifier keys "
            f"(Ctrl/Alt/Shift/Win) - Windows reserves combos like this "
            f"for things such as switching keyboard language, so it "
            f"won't reach this program reliably. Add a regular key to "
            f"it, e.g. '{key_combo}+z'."
        )
        return False

    try:
        new_handle = keyboard.add_hotkey(key_combo, _on_trigger_pressed)
    except Exception as e:
        safe_print(f"[ERROR] Could not register hotkey '{key_combo}': {e}")
        return False

    # Only remove the old hotkey after the new one registered successfully
    if _hotkey_handle is not None:
        try:
            keyboard.remove_hotkey(_hotkey_handle)
        except Exception:
            pass

    _hotkey_handle = new_handle
    _trigger_key = key_combo
    _trigger_components = parts
    _save_config(trigger_key=key_combo)  # Remember it for next launch
    safe_print(f"[INFO] Trigger key set to: {key_combo.upper()} (saved as default)")
    return True


def _register_popup_hotkey(key_combo: str) -> bool:
    """
    Same as _register_hotkey(), but for the separate English -> Arabic
    popup-preview trigger (_on_popup_trigger_pressed). Kept as its own
    function/state so the two hotkeys can be changed independently.
    """
    global _popup_hotkey_handle, _popup_trigger_key, _popup_trigger_components

    key_combo = key_combo.strip().lower()
    if not key_combo:
        return False

    parts = {p.strip() for p in key_combo.split("+")}

    ONLY_MODIFIER_NAMES = {"ctrl", "alt", "shift", "windows"}
    if parts and parts.issubset(ONLY_MODIFIER_NAMES):
        safe_print(
            f"[ERROR] '{key_combo}' is made only of modifier keys "
            f"(Ctrl/Alt/Shift/Win) - Windows reserves combos like this "
            f"for things such as switching keyboard language, so it "
            f"won't reach this program reliably. Add a regular key to "
            f"it, e.g. '{key_combo}+z'."
        )
        return False

    if parts == _trigger_components:
        safe_print(f"[ERROR] '{key_combo}' is already used as the Arabic -> English "
                   f"trigger key - pick a different key for the popup trigger.")
        return False

    try:
        new_handle = keyboard.add_hotkey(key_combo, _on_popup_trigger_pressed)
    except Exception as e:
        safe_print(f"[ERROR] Could not register popup hotkey '{key_combo}': {e}")
        return False

    if _popup_hotkey_handle is not None:
        try:
            keyboard.remove_hotkey(_popup_hotkey_handle)
        except Exception:
            pass

    _popup_hotkey_handle = new_handle
    _popup_trigger_key = key_combo
    _popup_trigger_components = parts
    _save_config(popup_trigger_key=key_combo)
    safe_print(f"[INFO] Popup (English -> Arabic) trigger key set to: {key_combo.upper()} (saved as default)")
    return True


def _register_select_hotkey(key_combo: str) -> bool:
    """
    Same idea as _register_hotkey()/_register_popup_hotkey(), but for
    the independent "Select-translate" hotkey (_on_select_trigger_pressed):
    translates whatever is currently mouse-selected, in either
    direction (auto-detected). Kept as its own state so it can be
    changed independently of the other two hotkeys.
    """
    global _select_hotkey_handle, _select_trigger_key, _select_trigger_components

    key_combo = key_combo.strip().lower()
    if not key_combo:
        return False

    parts = {p.strip() for p in key_combo.split("+")}

    ONLY_MODIFIER_NAMES = {"ctrl", "alt", "shift", "windows"}
    if parts and parts.issubset(ONLY_MODIFIER_NAMES):
        safe_print(
            f"[ERROR] '{key_combo}' is made only of modifier keys "
            f"(Ctrl/Alt/Shift/Win) - Windows reserves combos like this "
            f"for things such as switching keyboard language, so it "
            f"won't reach this program reliably. Add a regular key to "
            f"it, e.g. '{key_combo}+z'."
        )
        return False

    if parts == _trigger_components or parts == _popup_trigger_components:
        safe_print(f"[ERROR] '{key_combo}' is already used by another hotkey in this "
                   f"program - pick a different key for Select-translate.")
        return False

    try:
        new_handle = keyboard.add_hotkey(key_combo, _on_select_trigger_pressed)
    except Exception as e:
        safe_print(f"[ERROR] Could not register select hotkey '{key_combo}': {e}")
        return False

    if _select_hotkey_handle is not None:
        try:
            keyboard.remove_hotkey(_select_hotkey_handle)
        except Exception:
            pass

    _select_hotkey_handle = new_handle
    _select_trigger_key = key_combo
    _select_trigger_components = parts
    _save_config(select_trigger_key=key_combo)
    safe_print(f"[INFO] Select-translate trigger key set to: {key_combo.upper()} (saved as default)")
    return True


# =========================================================================
# Settings window (tkinter) - opened from the tray icon menu
# =========================================================================
# Every setting below gets a small "؟" button next to it. Clicking it
# opens a plain-Arabic explanation of what that setting does and how to
# use it - nothing else in the program is affected, the button only ever
# shows a message box.
SETTINGS_HELP = {
    "enabled": (
        "Enabled - تشغيل / إيقاف",
        "لما تكون متفعّلة، البرنامج بيراقب الكيبورد ومستني مفتاح الترجمة.\n\n"
        "لو قفلتها، البرنامج بيفضل شغال بس مش هيترجم ولا هيتابع أي كتابة — "
        "مفيدة لو بتلعب لعبة أو بتكتب حاجة مش عايز البرنامج يتدخل فيها.\n\n"
        "تقدر تفتحها وتقفلها كمان من الزرار اللي في النافذة الرئيسية أو من "
        "الأيقونة اللي جنب الساعة."
    ),
    "startup": (
        "Start with Windows - يفتح مع الويندوز",
        "لو علّمت عليها، البرنامج هيفتح لوحده كل مرة تدخل على الويندوز، "
        "من غير ما تشغّله بإيدك.\n\n"
        "بيتسجل باسم المستخدم بتاعك بس (HKEY_CURRENT_USER) فمش محتاج صلاحيات "
        "مدير، ولو شِلت العلامة بيتمسح فورًا.\n\n"
        "ملحوظة: لو البرنامج محتاج يشتغل كـ Administrator عشان يقرا الكيبورد، "
        "الفتح التلقائي ده هيفتحه بصلاحيات عادية."
    ),
    "trigger": (
        "Trigger key - مفتاح الترجمة (عربي ← إنجليزي)",
        "ده المفتاح اللي بتدوس عليه بعد ما تكتب أو تظلّل جملة عربية، فيمسحها "
        "ويكتب مكانها الترجمة الإنجليزية.\n\n"
        "طريقة الاستخدام:\n"
        "١) اكتب الجملة العربية عادي في أي برنامج، أو ظلّلها بالماوس.\n"
        "٢) دوس المفتاح ده.\n"
        "٣) استنى أقل من ثانية وهتلاقي الترجمة اتكتبت مكانها.\n\n"
        "تقدر تختار من القايمة (F1 لحد F12، Alt+رقم، Scroll Lock) أو تكتب "
        "تركيبة بنفسك زي ctrl+alt+space.\n\n"
        "اختار مفتاح مش مستخدم في برامج تانية، ومتستخدمش Ctrl/Alt/Shift "
        "لوحدهم لأن الويندوز حاجزهم لنفسه."
    ),
    "popup": (
        "Auto-popup key - مفتاح البوب-أب (إنجليزي ← عربي)",
        "المفتاح ده شغّال كمفتاح تبديل (on/off) مش ترجمة مرة واحدة.\n\n"
        "لما تدوس عليه مرة، الوضع بيتفعّل: أي نص إنجليزي تنسخه بعد كده "
        "(Ctrl+C أو كليك يمين ← Copy) هتظهر ترجمته العربية في نافذة صغيرة "
        "جنب الماوس، من غير ما تدوس أي حاجة تانية.\n\n"
        "دوس عليه تاني عشان توقّف الوضع ده.\n\n"
        "لازم يكون مفتاح مختلف عن مفتاح الترجمة اللي فوق."
    ),
    "select": (
        "Select-translate key - ترجمة النص المحدد بالماوس",
        "مفتاح مستقل تمامًا عن مفتاح الترجمة العادي (F3) ومفتاح البوب-أب.\n\n"
        "طريقة الاستخدام:\n"
        "١) ظلّل أي نص بالماوس في أي برنامج - عربي أو إنجليزي.\n"
        "٢) دوس المفتاح ده.\n"
        "٣) النص هيتبدل فورًا بترجمته في نفس المكان.\n\n"
        "الاتجاه (عربي←إنجليزي أو العكس) بيتحدد تلقائيًا من محتوى النص "
        "نفسه - مش محتاج تختاره.\n\n"
        "ده منفصل تمامًا عن الطريقة القديمة (تكتب ثم تدوس F3) - الاتنين "
        "شغالين جنب بعض من غير ما يأثروا على بعض."
    ),
    "fallback": (
        "Fallback engine - محرك احتياطي",
        "لو المحرك الأساسي فشل في ترجمة معينة، البرنامج بيجرب فورًا نفس "
        "الجملة بالمحرك الاحتياطي ده، مرة واحدة بس.\n\n"
        "المحرك الأساسي المحفوظ فوق (Translation engine) مبيتغيّرش أبدًا "
        "بسبب ده - الترجمة الجاية هتفضل تبدأ بيه هو تاني.\n\n"
        "لو الاتنين فشلوا، هتوصلك رسالة توضح سبب فشل المحرك الأساسي "
        "عادي. ولو الاحتياطي نجح، هتوصلك رسالة توضح إن المحرك الأساسي "
        "فشل وليه، وإن النتيجة جت من الاحتياطي.\n\n"
        "اختار 'None' لو مش عايز أي محرك احتياطي."
    ),
    "speed": (
        "Typing speed - سرعة كتابة الترجمة",
        "بتحدد المدة بين كل حرف والتاني وهو بيكتب الترجمة:\n\n"
        "• turbo — أسرع حاجة، مناسب للمتصفحات وبرامج الكتابة العادية.\n"
        "• normal — الوضع الافتراضي، متوازن ومناسب لمعظم الحالات.\n"
        "• safe — أبطأ بس أضمن، استخدمه مع الألعاب والمحاكيات زي BlueStacks "
        "أو MSI App Player لأنها بتبلع الحروف السريعة وتطلع الكلام ناقص أو "
        "مبعثر.\n\n"
        "لو لاحظت إن في حروف بتضيع من الترجمة، نزّل السرعة خطوة."
    ),
    "target_language": (
        "Target language - لغة الترجمة",
        "الأصل: البرنامج بيترجم من وإلى الإنجليزي بس. الإعداد ده بيخليك "
        "تختار أي لغة تانية بدل الإنجليزي، وكل حاجة في البرنامج بتتظبط "
        "عليها تلقائيًا:\n\n"
        "• مفتاح الترجمة (F3) هيترجم العربي اللي بتكتبه/تظلّله للغة "
        "اللي اخترتها هنا بدل الإنجليزي.\n"
        "• مفتاح البوب-أب هيترجم أي نص تنسخه من اللغة دي للعربي.\n"
        "• مفتاح Select-translate هيكتشف الاتجاه تلقائيًا برضه، عربي "
        "↔ اللغة اللي اخترتها.\n\n"
        "ملحوظة: مش كل محرك بيدعم كل اللغات - لو محرك 'deepl' مثلًا "
        "مبيدعمش اللغة اللي اخترتها، هتوصلك رسالة خطأ واضحة؛ جرّب "
        "'google' أو 'claude' أو 'gemini' بدالها."
    ),
    "engine": (
        "Translation engine - محرك الترجمة",
        "المحرك اللي بيترجم فعليًا:\n\n"
        "• google / bing / baidu — مجانية ومن غير أي مفتاح، والأسرع عمومًا. "
        "google هو الافتراضي والأنسب لمعظم الناس.\n"
        "• argos — بيشتغل أوفلاين بعد التحميل، جودته أقل.\n"
        "• claude / gemini — أدق وأفهم للسياق والعامية، بس بتحتاج مفتاح API "
        "بتاعك وبتتحاسب على كل ترجمة (مبلغ صغير جدًا).\n"
        "• deepl — دقة عالية ومفيها باقة مجانية، بتحتاج مفتاح API بتاعك.\n"
        "• custom — أي مزوّد AI تاني تحبه (OpenAI, OpenRouter, Groq...)، "
        "بتضيفه بنفسك من غير ما نغيّر الكود.\n\n"
        "لو محرك وقع أو اتحجب في بلدك، جرّب غيره من هنا — ده أول حل تجربه لما "
        "تيجي رسالة إن المحرك رفض الطلب."
    ),
    "claude_key": (
        "Claude API key",
        "مطلوب بس لو اخترت المحرك 'claude'، وسايبه فاضي لو بتستخدم "
        "google أو bing.\n\n"
        "طريقة الحصول عليه:\n"
        "١) دوس زرار 'Get API key' جنب الخانة — هيفتحلك موقع Anthropic.\n"
        "٢) سجّل دخول واعمل مفتاح جديد وانسخه.\n"
        "٣) الزقه هنا ودوس Apply.\n\n"
        "المفتاح بيتخزن على جهازك بس في الملف:\n" + CONFIG_FILE_PATH + "\n\n"
        "متشاركوش مع حد، وأي حد معاه المفتاح يقدر يستهلك رصيدك."
    ),
    "gemini_key": (
        "Gemini API key",
        "نفس فكرة مفتاح Claude، بس للمحرك 'gemini' من جوجل.\n\n"
        "دوس 'Get API key' عشان يفتحلك aistudio.google.com، اعمل مفتاح، "
        "والزقه هنا ودوس Apply.\n\n"
        "بيتخزن على جهازك بس في:\n" + CONFIG_FILE_PATH
    ),
    "deepl_key": (
        "DeepL API key",
        "مطلوب بس لو اخترت المحرك 'deepl'.\n\n"
        "دوس 'Get API key' عشان يفتحلك deepl.com، سجّل دخول وانسخ المفتاح "
        "من صفحة 'API Keys & Limits'، والزقه هنا ودوس Apply.\n\n"
        "مفتاح الباقة المجانية (Free) بيشتغل بنفس الطريقة بالظبط.\n\n"
        "بيتخزن على جهازك بس في:\n" + CONFIG_FILE_PATH
    ),
    "custom_engine": (
        "Custom AI provider - أي ذكاء اصطناعي",
        "المحرك ده بيخليك تضيف أي مزوّد AI بيتكلم بنفس شكل API بتاع "
        "OpenAI (وأغلبهم كده: OpenAI نفسها، OpenRouter، Groq، DeepSeek، "
        "Mistral، وحتى موديل شغال على جهازك زي Ollama)، من غير ما تلمس "
        "الكود خالص.\n\n"
        "لكل مزوّد محتاج تحفظله 3 حاجات:\n"
        "١) Base URL - عنوان السيرفر بتاع المزوّد.\n"
        "٢) API key - مفتاحك عندهم.\n"
        "٣) Model - اسم الموديل اللي عايز تستخدمه.\n\n"
        "دوس '+ Add' عشان تضيف مزوّد جديد، أو اختار واحد محفوظ من القايمة. "
        "تقدر تحفظ أكتر من مزوّد وتبدّل بينهم وقت ما تحب.\n\n"
        "كل البيانات دي بتتخزن على جهازك بس في:\n" + CONFIG_FILE_PATH
    ),
}


SETTINGS_HELP.update({
    "tone": (
        "Tone - نبرة الترجمة",
        "بتحدد أسلوب الترجمة اللي الذكاء الاصطناعي هيستخدمه:\n\n"
        "• normal: عادي وطبيعي.\n"
        "• formal: رسمي ومحترم (للإيميلات والشغل).\n"
        "• casual: عامية وودّية (للشات مع الأصحاب).\n\n"
        "بتأثر على Claude وGemini والـ custom بس. جوجل وDeepL مش بياخدوا "
        "تعليمات فمش هيتأثروا.\n\n"
        "تقدر كمان تحط مفتاح سريع (مثلاً ctrl+alt+t) تبدّل بيه بين النبرات "
        "من غير ما تفتح الإعدادات. سيبه فاضي لو مش عايزه."
    ),
    "cache": (
        "Cache - ذاكرة الترجمات",
        "الجملة اللي اتترجمت قبل كده (بنفس المحرك والنبرة واللغة) بتيجي "
        "فوراً من غير ما تصرف رصيد.\n\n"
        "بتتحفظ في ذاكرة البرنامج بس وبتتمسح لما تقفله، ومفيش حاجة بتتكتب "
        "في أي ملف.\n\n"
        "لو ترجمة طلعت مش حلوة، دوس Quick fix / Retry وهو بيجيب ترجمة جديدة "
        "ويحدّث الذاكرة."
    ),
    "indicator": (
        "Indicator - أيقونة جاري الترجمة",
        "كبسولة صغيرة بتظهر فوق مكان الكتابة وقت الترجمة والكتابة، معناها: "
        "استنى ومتكتبش لسه.\n\n"
        "في البرامج اللي بتبيّن مكان المؤشر (زي Notepad) بتظهر فوقه. في "
        "المتصفحات وتيليجرام وأغلب البرامج الحديثة مش بتبيّنه، فبتظهر جنب "
        "الماوس.\n\n"
        "بتختفي لوحدها، وبتحمرّ لثانية لو الترجمة فشلت، ومش بتاخد الفوكس "
        "ولا بتمنع الضغط من تحتها.\n\n"
        "الصوت اختياري ومقفول من الأول."
    ),
    "paste_threshold": (
        "Paste for long text - لصق الجمل الطويلة",
        "الترجمة اللي أطول من الرقم ده بتتلصق مرة واحدة (Ctrl+V) بدل ما "
        "تتكتب حرف حرف: أسرع وأضمن.\n\n"
        "الـ clipboard بتاعك بيرجع زي ما كان بعدها (النص بس). الجمل الأقصر "
        "بتتكتب حرف حرف زي الأول.\n\n"
        "0 = دايماً كتابة حرف حرف.\n\n"
        "اللصق مش بيشتغل في السرعة safe (زي BlueStacks)، ولا لو الـ clipboard "
        "فيه صورة أو ملفات، وفي الحالتين البرنامج بيكتب حرف حرف."
    ),
    "app_speed": (
        "Per-app speed - سرعة الكتابة لكل برنامج",
        "اكتب اسم البرنامج وسرعته، سطر لكل برنامج، مثال:\n\n"
        "hd-player.exe = safe\n"
        "chrome.exe = turbo\n\n"
        "السرعات: turbo / normal / safe.\n\n"
        "اسم البرنامج هتلاقيه في Task Manager > Details. أي برنامج مش في "
        "القايمة بيستخدم السرعة العامة اللي في الشاشة الرئيسية (Typing speed)."
    ),
})


def _show_setting_help(key: str):
    """Show the plain-Arabic explanation of one setting."""
    title, body = SETTINGS_HELP.get(key, (key, "مفيش شرح متاح للإعداد ده."))
    try:
        messagebox.showinfo(title, body, parent=_settings_window)
    except Exception:
        # A missing/closed parent should never stop the help from showing
        messagebox.showinfo(title, body)


def _help_button(parent, key: str):
    """The small '؟' button that opens the explanation for 'key'."""
    return tk.Button(
        parent, text="؟", width=2, font=("Segoe UI", 9, "bold"),
        fg="#0f5d8c", relief="groove", cursor="hand2",
        command=lambda: _show_setting_help(key),
    )


def _setting_row(win, key: str, padding: dict):
    """
    A horizontal row that holds one setting's label (or checkbox) on the
    left and its '؟' help button on the right. Returns the frame so the
    caller packs the actual widget into it.
    """
    row = tk.Frame(win)
    row.pack(fill="x", **padding)
    _help_button(row, key).pack(side="right")
    return row


def _make_scrollable_tab(notebook, window, text: str):
    """
    Add a tab to 'notebook' whose content scrolls vertically (mouse wheel
    works while that tab is open). Returns the inner frame to pack into.
    """
    outer = tk.Frame(notebook)
    canvas = tk.Canvas(outer, highlightthickness=0, borderwidth=0)
    canvas._theme_role = "plain"
    scrollbar = tk.Scrollbar(outer, orient="vertical", command=canvas.yview)
    inner = tk.Frame(canvas)
    inner_id = canvas.create_window((0, 0), window=inner, anchor="nw")
    inner.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
    canvas.bind("<Configure>", lambda e: canvas.itemconfigure(inner_id, width=e.width))
    canvas.configure(yscrollcommand=scrollbar.set)
    scrollbar.pack(side="right", fill="y")
    canvas.pack(side="left", fill="both", expand=True)

    def _on_wheel(event):
        try:
            if notebook.select() == str(outer):
                canvas.yview_scroll(int(-event.delta / 120), "units")
        except tk.TclError:
            pass

    window.bind("<MouseWheel>", _on_wheel, add="+")
    notebook.add(outer, text=text)
    return inner


def _open_settings_window():
    """
    Build and show the settings window. MUST run on the Tk main thread
    (call it through _ui_call from anywhere else). If it is already
    open, the existing window is just brought back to the front instead
    of opening a second copy.
    """
    global _settings_window

    if _settings_window is not None and _settings_window.winfo_exists():
        _settings_window.deiconify()
        _settings_window.lift()
        _settings_window.focus_force()
        return

    win = tk.Toplevel(_root)
    _settings_window = win
    win.title(f"{APP_NAME} - Settings")
    win.attributes("-topmost", True)
    # Vertical resizing stays allowed: the help hint below adds a line, and
    # on short screens (1366x768 laptops) the window must be shrinkable.
    win.resizable(False, True)

    width, height = 460, 720
    screen_w = win.winfo_screenwidth()
    screen_h = win.winfo_screenheight()
    x = (screen_w // 2) - (width // 2)
    y = (screen_h // 2) - (height // 2)
    win.geometry(f"{width}x{height}+{x}+{y}")

    padding = {"padx": 15, "pady": 6}

    # ---- Hint: every setting has a "؟" button next to it ----
    tk.Label(
        win,
        text="دوس على ؟ جنب أي إعداد عشان تعرف بيعمل إيه وإزاي تستخدمه",
        font=("Segoe UI", 9), fg="#0f5d8c", justify="right", anchor="e",
    ).pack(fill="x", padx=15, pady=(10, 0))

    # ---- Tabs: General / Engine / Advanced (tone, language, speed and engine
    # quick-switches live on the main window) ----
    notebook = ttk.Notebook(win)
    notebook.pack(fill="both", expand=True, padx=8, pady=(8, 0))

    general_tab = tk.Frame(notebook)
    engine_tab = tk.Frame(notebook)
    notebook.add(general_tab, text="General")
    notebook.add(engine_tab, text="Engine")
    # Everything that is rarely changed lives in one scrollable tab.
    advanced_tab = _make_scrollable_tab(notebook, win, "Advanced")
    extras_tab = advanced_tab

    # ======================= GENERAL TAB =======================
    # ---- Enabled checkbox ----
    enabled_var = tk.BooleanVar(value=_enabled)

    def on_toggle_enabled():
        global _enabled
        _enabled = enabled_var.get()
        with _buffer_lock:
            globals()["_buffer"] = ""

    enabled_row = _setting_row(general_tab, "enabled", padding)
    tk.Checkbutton(
        enabled_row, text="Enabled", variable=enabled_var, command=on_toggle_enabled,
        font=("Arial", 11)
    ).pack(side="left", anchor="w")

    # ---- Start with Windows checkbox ----
    startup_var = tk.BooleanVar(value=_is_startup_enabled())

    def on_toggle_startup():
        if not _set_startup_enabled(startup_var.get()):
            # Revert the checkbox visually if the registry update failed
            startup_var.set(_is_startup_enabled())
            messagebox.showerror(
                "Could not update startup setting",
                "Failed to update the Windows startup entry. See the console "
                "window for details."
            )

    startup_row = _setting_row(general_tab, "startup", padding)
    tk.Checkbutton(
        startup_row, text="Start with Windows", variable=startup_var, command=on_toggle_startup,
        font=("Arial", 11)
    ).pack(side="left", anchor="w")

    # ---- Trigger key ----
    trigger_row = _setting_row(general_tab, "trigger", padding)
    tk.Label(
        trigger_row, text="Trigger key (Arabic -> target language, replaces the typed/selected text):",
        font=("Arial", 11), wraplength=350, justify="left"
    ).pack(side="left", anchor="w")
    hotkey_var = tk.StringVar(value=_trigger_key)
    hotkey_combo = ttk.Combobox(
        general_tab, textvariable=hotkey_var, values=HOTKEY_PRESETS, font=("Arial", 11)
    )
    hotkey_combo.pack(fill="x", padx=15)
    tk.Label(
        general_tab, text="(pick a preset above, or type your own, e.g. ctrl+alt+space)",
        font=("Arial", 8), fg="gray"
    ).pack(anchor="w", padx=15, pady=(2, 6))

    # ---- Popup trigger key ----
    popup_row = _setting_row(general_tab, "popup", padding)
    tk.Label(
        popup_row, text="Auto-popup toggle key (target language -> Arabic):",
        font=("Arial", 11), wraplength=350, justify="left"
    ).pack(side="left", anchor="w")
    popup_hotkey_var = tk.StringVar(value=_popup_trigger_key)
    popup_hotkey_combo = ttk.Combobox(
        general_tab, textvariable=popup_hotkey_var, values=HOTKEY_PRESETS, font=("Arial", 11)
    )
    popup_hotkey_combo.pack(fill="x", padx=15)
    tk.Label(
        general_tab, text="(press once to turn ON: any copy afterward auto-shows its Arabic\n"
                  "translation in a popup, until you press it again to turn OFF)",
        font=("Arial", 8), fg="gray", justify="left"
    ).pack(anchor="w", padx=15, pady=(2, 6))

    # ---- Select-translate trigger key ----
    select_row = _setting_row(general_tab, "select", padding)
    tk.Label(
        select_row, text="Select-translate key (translate mouse-selected text, either direction):",
        font=("Arial", 11), wraplength=350, justify="left"
    ).pack(side="left", anchor="w")
    select_hotkey_var = tk.StringVar(value=_select_trigger_key)
    select_hotkey_combo = ttk.Combobox(
        general_tab, textvariable=select_hotkey_var, values=HOTKEY_PRESETS, font=("Arial", 11)
    )
    select_hotkey_combo.pack(fill="x", padx=15)
    tk.Label(
        general_tab, text="(select any text with the mouse in any program, press this key, and\n"
                  "it's replaced in place with its translation - direction auto-detected)",
        font=("Arial", 8), fg="gray", justify="left"
    ).pack(anchor="w", padx=15, pady=(2, 6))

    # ======================= ENGINE TAB =======================
    # ---- Translation engine ----
    engine_row = _setting_row(engine_tab, "engine", padding)
    tk.Label(engine_row, text="Translation engine:", font=("Arial", 11)).pack(side="left", anchor="w")
    engine_var = tk.StringVar(value=_translate_engine)
    engine_combo = ttk.Combobox(
        engine_tab, textvariable=engine_var, values=ENGINE_PRESETS, font=("Arial", 11)
    )
    engine_combo.pack(fill="x", padx=15)
    tk.Label(
        engine_tab,
        text="('claude', 'gemini', 'deepl' and 'custom' need your own API key below)",
        font=("Arial", 8), fg="gray"
    ).pack(anchor="w", padx=15, pady=(2, 6))

    # ---- Engine-specific key panel: ONE area that swaps its contents
    # depending on the selected engine, instead of showing every
    # engine's API key box at once (that used to make the window very
    # crowded). Built by _render_engine_key_panel() below, which is
    # re-run every time engine_var changes. ----
    claude_api_key_var = tk.StringVar(value=_claude_api_key)
    gemini_api_key_var = tk.StringVar(value=_gemini_api_key)
    deepl_api_key_var = tk.StringVar(value=_deepl_api_key)
    custom_provider_var = tk.StringVar(value=_custom_provider_selected)
    # Local working copy - only written back to _custom_providers on Apply,
    # so closing the window with Close (not Apply) discards unsaved edits.
    local_custom_providers = dict(_custom_providers)

    engine_key_container = tk.Frame(engine_tab)
    engine_key_container.pack(fill="x")

    def _provider_summary_text():
        name = custom_provider_var.get().strip()
        p = local_custom_providers.get(name)
        if not p:
            return "No provider selected yet - press '+ Add' below."
        return f"Base URL: {p.get('base_url', '')}\nModel: {p.get('model', '')}"

    def _refresh_provider_combo(select: str = None):
        names = list(local_custom_providers.keys())
        provider_combo["values"] = names
        if select is not None:
            custom_provider_var.set(select)
        elif custom_provider_var.get() not in local_custom_providers and names:
            custom_provider_var.set(names[0])
        elif not names:
            custom_provider_var.set("")
        provider_summary_label.config(text=_provider_summary_text())
        try:
            _refresh_fallback_combo()
        except NameError:
            pass  # not built yet on the very first call

    def _open_provider_editor(mode: str):
        original_name = custom_provider_var.get().strip() if mode == "edit" else ""
        existing = local_custom_providers.get(original_name, {}) if mode == "edit" else {}

        modal = tk.Toplevel(win)
        modal.title("Add provider" if mode == "add" else f"Edit '{original_name}'")
        modal.attributes("-topmost", True)
        modal.resizable(False, False)
        mpad = {"padx": 15, "pady": 4}

        tk.Label(modal, text="Provider name (e.g. OpenRouter, Groq):", font=("Arial", 10)).pack(anchor="w", **mpad)
        name_var = tk.StringVar(value=original_name)
        tk.Entry(modal, textvariable=name_var, font=("Arial", 10), width=42).pack(padx=15)

        tk.Label(modal, text="Base URL (e.g. https://openrouter.ai/api/v1):", font=("Arial", 10)).pack(anchor="w", **mpad)
        base_url_var = tk.StringVar(value=existing.get("base_url", ""))
        tk.Entry(modal, textvariable=base_url_var, font=("Arial", 10), width=42).pack(padx=15)

        tk.Label(modal, text="API key:", font=("Arial", 10)).pack(anchor="w", **mpad)
        modal_key_var = tk.StringVar(value=existing.get("api_key", ""))
        tk.Entry(modal, textvariable=modal_key_var, font=("Arial", 10), width=42, show="*").pack(padx=15)

        tk.Label(modal, text="Model name (e.g. gpt-4o-mini):", font=("Arial", 10)).pack(anchor="w", **mpad)
        model_row = tk.Frame(modal)
        model_row.pack(fill="x", padx=15)
        model_var = tk.StringVar(value=existing.get("model", ""))
        model_combo = ttk.Combobox(model_row, textvariable=model_var, font=("Arial", 10), width=30)
        model_combo.pack(side="left", fill="x", expand=True)
        fetch_models_btn = tk.Button(model_row, text="Fetch models", font=("Arial", 9))
        fetch_models_btn.pack(side="left", padx=(6, 0))

        tk.Label(
            modal,
            text="Works with any OpenAI-compatible provider (OpenAI, OpenRouter,\n"
                 "Groq, DeepSeek, Mistral, a local Ollama/LM Studio server, ...).",
            font=("Arial", 8), fg="gray", justify="left"
        ).pack(anchor="w", padx=15, pady=(4, 4))

        # ---- "Test connection" / "Fetch models" status line ----
        # Shared by both buttons below - only one of them runs at a
        # time in practice, so one status label is enough.
        conn_status_var = tk.StringVar(value="")
        test_row = tk.Frame(modal)
        test_row.pack(fill="x", padx=15, pady=(0, 4))
        test_btn = tk.Button(test_row, text="Test connection", font=("Arial", 9))
        test_btn.pack(side="left")
        def _copy_status():
            try:
                modal.clipboard_clear()
                modal.clipboard_append(conn_status_var.get())
            except Exception:
                pass
        tk.Button(test_row, text="Copy message", font=("Arial", 9),
                  command=_copy_status).pack(side="left", padx=(6, 0))

        # Read-only text box (you can select / copy / scroll the FULL message)
        status_box_frame = tk.Frame(modal)
        status_box_frame.pack(fill="x", padx=15, pady=(0, 6))
        status_box = tk.Text(status_box_frame, height=7, width=46, font=("Arial", 9),
                             wrap="word", relief="flat", state="disabled")
        status_scroll = ttk.Scrollbar(status_box_frame, orient="vertical", command=status_box.yview)
        status_box.configure(yscrollcommand=status_scroll.set)
        status_box.pack(side="left", fill="x", expand=True)
        status_scroll.pack(side="right", fill="y")

        def _sync_status_box(*_a):
            status_box.config(state="normal")
            status_box.delete("1.0", "end")
            status_box.insert("1.0", conn_status_var.get())
            status_box.config(state="disabled")
        conn_status_var.trace_add("write", _sync_status_box)

        def on_test_connection():
            base_url = base_url_var.get().strip()
            model = _strip_model_suffix(model_var.get())
            api_key = modal_key_var.get().strip()
            if not base_url or not model:
                conn_status_var.set("❌ املأ Base URL والـ Model الأول.")
                return
            test_btn.config(state="disabled")
            conn_status_var.set("⏳ بيتم الاختبار...")

            def worker():
                ok, message = _test_custom_provider_connection(base_url, api_key, model)

                if not ok:
                    _log_event("WARN", "Provider test failed", message, "")  # full text goes to log.txt

                def update_ui():
                    conn_status_var.set(("✅ " if ok else "❌ ") + message)
                    test_btn.config(state="normal")

                _ui_call(update_ui)

            threading.Thread(target=worker, daemon=True).start()

        def on_fetch_models():
            base_url = base_url_var.get().strip()
            api_key = modal_key_var.get().strip()
            if not base_url:
                conn_status_var.set("❌ اكتب الـ Base URL الأول.")
                return
            fetch_models_btn.config(state="disabled")
            conn_status_var.set("⏳ بيتم جلب قايمة الموديلات...")

            def worker():
                ok, result = _fetch_custom_provider_models(base_url, api_key)

                def update_ui():
                    fetch_models_btn.config(state="normal")
                    if ok:
                        model_combo["values"] = _models_with_quality(result)
                        best = _models_with_quality(result)[0]
                        conn_status_var.set(f"✅ لقيت {len(result)} موديل مرتبين من الأفضل للأقل (النسبة تقديرية لجودة الترجمة عربي↔إنجليزي). الأعلى: {best}")
                    else:
                        conn_status_var.set(f"❌ {result}")

                _ui_call(update_ui)

            threading.Thread(target=worker, daemon=True).start()

        test_btn.config(command=on_test_connection)
        fetch_models_btn.config(command=on_fetch_models)

        def on_model_selected(_event=None):
            clean = _strip_model_suffix(model_var.get())
            model_var.set(clean)
            q = _estimate_model_quality(clean)
            if q is None:
                conn_status_var.set("⚠ الموديل ده مش موديل نصوص/ترجمة (صوت/صور/embedding) - اختار غيره.")
            else:
                conn_status_var.set(f"⭐ جودة الترجمة التقديرية: {q}% (تقدير حسب نوع وحجم الموديل - مش اختبار فعلي)")
        model_combo.bind("<<ComboboxSelected>>", on_model_selected)

        def on_modal_save():
            name = name_var.get().strip()
            base_url = base_url_var.get().strip()
            model = _strip_model_suffix(model_var.get())
            if not name or not base_url or not model:
                messagebox.showerror(
                    "Missing info", "Provider name, Base URL and Model are all required.",
                    parent=modal
                )
                return
            if mode == "edit" and original_name and original_name != name:
                local_custom_providers.pop(original_name, None)
            local_custom_providers[name] = {
                "base_url": base_url, "api_key": modal_key_var.get().strip(), "model": model,
            }
            _refresh_provider_combo(select=name)
            modal.destroy()

        def on_modal_delete():
            if original_name and messagebox.askyesno(
                "Delete provider", f"Remove '{original_name}'?", parent=modal
            ):
                local_custom_providers.pop(original_name, None)
                _refresh_provider_combo()
                modal.destroy()

        modal_btn_row = tk.Frame(modal)
        modal_btn_row.pack(pady=10)
        tk.Button(modal_btn_row, text="Save", width=10, command=on_modal_save).pack(side="left", padx=4)
        if mode == "edit":
            tk.Button(modal_btn_row, text="Delete", width=10, command=on_modal_delete).pack(side="left", padx=4)
        tk.Button(modal_btn_row, text="Cancel", width=10, command=modal.destroy).pack(side="left", padx=4)
        _theme_apply_to(modal)

    def _render_engine_key_panel(*_args):
        for child in engine_key_container.winfo_children():
            child.destroy()

        engine = engine_var.get().strip().lower()
        nonlocal provider_combo, provider_summary_label

        if engine == "claude":
            row = _setting_row(engine_key_container, "claude_key", padding)
            tk.Label(row, text="Claude API key:", font=("Arial", 11)).pack(side="left", anchor="w")
            key_row = tk.Frame(engine_key_container)
            key_row.pack(fill="x", padx=15)
            tk.Entry(key_row, textvariable=claude_api_key_var, font=("Arial", 10), show="*").pack(
                side="left", fill="x", expand=True)
            tk.Button(key_row, text="Get API key", font=("Arial", 9),
                      command=lambda: webbrowser.open("https://console.anthropic.com/settings/keys")
                      ).pack(side="left", padx=(6, 0))

        elif engine == "gemini":
            row = _setting_row(engine_key_container, "gemini_key", padding)
            tk.Label(row, text="Gemini API key:", font=("Arial", 11)).pack(side="left", anchor="w")
            key_row = tk.Frame(engine_key_container)
            key_row.pack(fill="x", padx=15)
            tk.Entry(key_row, textvariable=gemini_api_key_var, font=("Arial", 10), show="*").pack(
                side="left", fill="x", expand=True)
            tk.Button(key_row, text="Get API key", font=("Arial", 9),
                      command=lambda: webbrowser.open("https://aistudio.google.com/apikey")
                      ).pack(side="left", padx=(6, 0))

        elif engine == "deepl":
            row = _setting_row(engine_key_container, "deepl_key", padding)
            tk.Label(row, text="DeepL API key:", font=("Arial", 11)).pack(side="left", anchor="w")
            key_row = tk.Frame(engine_key_container)
            key_row.pack(fill="x", padx=15)
            tk.Entry(key_row, textvariable=deepl_api_key_var, font=("Arial", 10), show="*").pack(
                side="left", fill="x", expand=True)
            tk.Button(key_row, text="Get API key", font=("Arial", 9),
                      command=lambda: webbrowser.open("https://www.deepl.com/en/your-account/keys")
                      ).pack(side="left", padx=(6, 0))

        elif engine == "custom":
            row = _setting_row(engine_key_container, "custom_engine", padding)
            tk.Label(row, text="AI provider:", font=("Arial", 11)).pack(side="left", anchor="w")
            provider_row = tk.Frame(engine_key_container)
            provider_row.pack(fill="x", padx=15)
            provider_combo = ttk.Combobox(
                provider_row, textvariable=custom_provider_var,
                values=list(local_custom_providers.keys()), state="readonly", font=("Arial", 10)
            )
            provider_combo.pack(side="left", fill="x", expand=True)
            tk.Button(provider_row, text="+ Add", font=("Arial", 9),
                      command=lambda: _open_provider_editor("add")).pack(side="left", padx=(6, 0))

            action_row = tk.Frame(engine_key_container)
            action_row.pack(fill="x", padx=15, pady=(4, 0))
            tk.Button(action_row, text="Edit", font=("Arial", 9),
                      command=lambda: _open_provider_editor("edit")).pack(side="left")

            provider_summary_label = tk.Label(
                engine_key_container, text="", font=("Arial", 8), fg="gray", justify="left"
            )
            provider_summary_label.pack(anchor="w", padx=15, pady=(4, 6))
            provider_combo.bind("<<ComboboxSelected>>",
                                 lambda e: provider_summary_label.config(text=_provider_summary_text()))
            provider_summary_label.config(text=_provider_summary_text())

        else:
            # google / bing / baidu / argos - free, no key needed
            tk.Label(
                engine_key_container, text="This engine is free - no API key needed.",
                font=("Arial", 9), fg="gray"
            ).pack(anchor="w", padx=15, pady=(2, 6))

        _theme_apply_to(engine_key_container)

    provider_combo = None
    provider_summary_label = None
    engine_var.trace_add("write", _render_engine_key_panel)
    _render_engine_key_panel()

    # ---- Fallback engine ----
    # Lists every built-in engine PLUS every saved custom provider by
    # its own name (not just generic "custom"), so the fallback can
    # point at one specific provider even when several are saved.
    tk.Frame(engine_tab, height=1, bg="#ddd").pack(fill="x", padx=15, pady=(6, 4))
    fallback_row = _setting_row(engine_tab, "fallback", padding)
    tk.Label(
        fallback_row, text="Fallback engine (tried once if the primary engine fails):",
        font=("Arial", 11), wraplength=350, justify="left"
    ).pack(side="left", anchor="w")
    fallback_var = tk.StringVar(value=_fallback_engine_display_name(_fallback_engine))
    fallback_combo = ttk.Combobox(
        engine_tab, textvariable=fallback_var, state="readonly", font=("Arial", 11)
    )
    fallback_combo.pack(fill="x", padx=15)
    tk.Label(
        engine_tab,
        text="(the saved PRIMARY engine above never changes because of this - the "
             "next translation still starts with it. The failure reason and which "
             "engine actually answered are shown in the notification.)",
        font=("Arial", 8), fg="gray", wraplength=390, justify="left"
    ).pack(anchor="w", padx=15, pady=(2, 6))

    def _fallback_choices():
        choices = ["None"] + [e for e in ENGINE_PRESETS if e != "custom"]
        choices += [f"custom ({name})" for name in local_custom_providers.keys()]
        return choices

    def _fallback_value_to_stored(display: str) -> str:
        """Reverse of _fallback_engine_display_name(): UI label -> stored value."""
        display = (display or "None").strip()
        if display == "None":
            return "none"
        if display.startswith("custom (") and display.endswith(")"):
            return f"custom:{display[len('custom ('):-1]}"
        return display

    def _refresh_fallback_combo():
        current_display = fallback_var.get()
        choices = _fallback_choices()
        fallback_combo["values"] = choices
        if current_display not in choices:
            fallback_var.set("None")

    _refresh_fallback_combo()

    # ======================= EXTRAS TAB =======================
    _note = {"font": ("Arial", 8), "fg": "gray", "justify": "left", "wraplength": 390}

    # ---- Tone quick key (the tone itself is picked on the main window) ----
    tone_row = _setting_row(extras_tab, "tone", padding)
    tk.Label(tone_row, text="Quick key to switch tone (optional, e.g. ctrl+alt+t):",
             font=("Arial", 10)).pack(side="left", anchor="w")
    tone_hotkey_var = tk.StringVar(value=_tone_trigger_key)
    tk.Entry(extras_tab, textvariable=tone_hotkey_var, font=("Arial", 10)).pack(fill="x", padx=15, pady=(0, 2))
    tk.Label(extras_tab, text="(the tone itself - formal / normal / casual - is picked on the "
                              "main window; AI engines only)", **_note).pack(anchor="w", padx=15, pady=(0, 4))

    # ---- Cache ----
    cache_row = _setting_row(extras_tab, "cache", padding)
    cache_var = tk.BooleanVar(value=_cache_enabled)
    tk.Checkbutton(cache_row, text="Remember translations (memory only)", variable=cache_var,
                   font=("Arial", 10)).pack(side="left", anchor="w")
    tk.Button(extras_tab, text="Clear remembered translations", font=("Arial", 8),
              command=lambda: messagebox.showinfo(
                  "Cache", f"Cleared {_clear_translation_cache()} remembered translation(s).",
                  parent=win)).pack(anchor="w", padx=15)

    # ---- Indicator ----
    indicator_row = _setting_row(extras_tab, "indicator", padding)
    indicator_var = tk.BooleanVar(value=_indicator_enabled)
    tk.Checkbutton(indicator_row, text="Show the 'translating...' capsule", variable=indicator_var,
                   font=("Arial", 10)).pack(side="left", anchor="w")
    sound_var = tk.BooleanVar(value=_working_sound)
    tk.Checkbutton(extras_tab, text="Play a soft sound when a translation starts", variable=sound_var,
                   font=("Arial", 10)).pack(anchor="w", padx=15)

    # ---- Paste threshold ----
    paste_row = _setting_row(extras_tab, "paste_threshold", padding)
    tk.Label(paste_row, text="Paste instead of typing when longer than:",
             font=("Arial", 10)).pack(side="left", anchor="w")
    paste_var = tk.StringVar(value=str(_paste_threshold))
    tk.Spinbox(extras_tab, from_=0, to=5000, textvariable=paste_var, width=8,
               font=("Arial", 10)).pack(anchor="w", padx=15)
    tk.Label(extras_tab, text="(characters; 0 = always type key-by-key; never used in 'safe' speed)",
             **_note).pack(anchor="w", padx=15, pady=(2, 2))

    # ---- Per-app typing speed ----
    app_speed_row = _setting_row(extras_tab, "app_speed", padding)
    tk.Label(app_speed_row, text="Typing speed per program:", font=("Arial", 10)).pack(side="left", anchor="w")
    app_rules_text = tk.Text(extras_tab, height=4, width=40, font=("Consolas", 9))
    app_rules_text.pack(fill="x", padx=15)
    app_rules_text.insert("1.0", "\n".join(f"{k} = {v}" for k, v in sorted(_app_speed_rules.items())))
    tk.Label(extras_tab, text="(one per line, e.g.  hd-player.exe = safe   - speeds: turbo / normal / "
                              "safe. Program names: Task Manager > Details)", **_note).pack(anchor="w", padx=15, pady=(2, 2))

    # ---- Where the data lives (bottom of the Advanced tab) ----
    tk.Frame(advanced_tab, height=1, bg="#ddd").pack(fill="x", padx=15, pady=(12, 0))
    def _open_config_folder():
        try:
            os.makedirs(CONFIG_DIR, exist_ok=True)
            if _IS_WINDOWS:
                os.startfile(CONFIG_DIR)  # noqa: S606 - Windows-only helper
            else:
                webbrowser.open(f"file:///{CONFIG_DIR}")
        except Exception as e:
            messagebox.showerror("Could not open folder", str(e), parent=win)

    tk.Label(
        advanced_tab, text="Where this program keeps your data on this machine:",
        font=("Arial", 11), wraplength=390, justify="left"
    ).pack(anchor="w", padx=15, pady=(14, 6))

    for label_text, path in (
        ("Settings (config.json):", CONFIG_FILE_PATH),
        ("Log (log.txt):", LOG_FILE_PATH),
        ("Favorites (favorites.json):", FAVORITES_FILE_PATH),
    ):
        tk.Label(advanced_tab, text=label_text, font=("Arial", 10, "bold")).pack(
            anchor="w", padx=15, pady=(6, 0))
        path_row = tk.Frame(advanced_tab)
        path_row.pack(fill="x", padx=15)
        path_entry = tk.Entry(path_row, font=("Consolas", 9))
        path_entry.insert(0, path)
        path_entry.config(state="readonly")
        path_entry.pack(side="left", fill="x", expand=True)

    tk.Button(
        advanced_tab, text="Open folder", font=("Arial", 10), command=_open_config_folder
    ).pack(anchor="w", padx=15, pady=(14, 6))

    tk.Label(
        advanced_tab, text=f"Version: {APP_VERSION}", font=("Arial", 10, "bold")
    ).pack(anchor="w", padx=15, pady=(10, 2))
    tk.Button(
        advanced_tab, text="Check for updates", font=("Arial", 10), command=_check_for_update_manual
    ).pack(anchor="w", padx=15, pady=(0, 6))

    tk.Label(
        advanced_tab,
        text=f"Log entries older than {LOG_RETENTION_DAYS} days are trimmed automatically.",
        font=("Arial", 8), fg="gray", wraplength=390, justify="left"
    ).pack(anchor="w", padx=15, pady=(2, 6))


    # ---- Apply / Close buttons ----
    def on_apply():
        global _translate_engine, _claude_api_key, _gemini_api_key, _deepl_api_key
        global _custom_providers, _custom_provider_selected, _typing_speed_profile, _key_delay
        global _fallback_engine, _target_language
        global _translation_tone, _cache_enabled, _indicator_enabled, _working_sound
        global _paste_threshold, _app_speed_rules, _usage_alert_level
        new_hotkey = hotkey_var.get().strip().lower()
        if new_hotkey and new_hotkey != _trigger_key:
            if not _register_hotkey(new_hotkey):
                messagebox.showerror(
                    "Invalid hotkey",
                    f"Could not register '{new_hotkey}'.\n\n"
                    "If it's made only of Ctrl/Alt/Shift/Win with nothing "
                    "else, Windows reserves that combo for itself (e.g. "
                    "Ctrl+Shift switches keyboard language). Add a normal "
                    "key to it, e.g. 'ctrl+shift+z'.\n\n"
                    "Keeping the previous hotkey."
                )
                hotkey_var.set(_trigger_key)

        new_popup_hotkey = popup_hotkey_var.get().strip().lower()
        if new_popup_hotkey and new_popup_hotkey != _popup_trigger_key:
            if not _register_popup_hotkey(new_popup_hotkey):
                messagebox.showerror(
                    "Invalid popup hotkey",
                    f"Could not register '{new_popup_hotkey}' as the popup "
                    "trigger key (it may be invalid, reserved, or already "
                    "used as the other trigger key).\n\n"
                    "Keeping the previous popup hotkey."
                )
                popup_hotkey_var.set(_popup_trigger_key)

        new_select_hotkey = select_hotkey_var.get().strip().lower()
        if new_select_hotkey and new_select_hotkey != _select_trigger_key:
            if not _register_select_hotkey(new_select_hotkey):
                messagebox.showerror(
                    "Invalid Select-translate hotkey",
                    f"Could not register '{new_select_hotkey}' as the "
                    "Select-translate key (it may be invalid, reserved, or "
                    "already used as another hotkey in this program).\n\n"
                    "Keeping the previous key."
                )
                select_hotkey_var.set(_select_trigger_key)

        new_tone_hotkey = tone_hotkey_var.get().strip().lower()
        if new_tone_hotkey != _tone_trigger_key:
            if not _register_tone_hotkey(new_tone_hotkey):
                messagebox.showerror(
                    "Invalid tone key",
                    f"Could not register '{new_tone_hotkey}' as the tone-switch key (invalid, "
                    "only modifier keys, or already used by another key of this program).\n\n"
                    "Keeping the previous one.")
                tone_hotkey_var.set(_tone_trigger_key)

        if cache_var.get() != _cache_enabled:
            _cache_enabled = cache_var.get()
            _save_config(cache_enabled=_cache_enabled)
            if not _cache_enabled:
                _clear_translation_cache()

        if indicator_var.get() != _indicator_enabled:
            _indicator_enabled = indicator_var.get()
            _save_config(show_working_indicator=_indicator_enabled)
        if sound_var.get() != _working_sound:
            _working_sound = sound_var.get()
            _save_config(working_sound=_working_sound)

        try:
            new_paste_threshold = max(0, min(5000, int(paste_var.get().strip())))
        except ValueError:
            messagebox.showerror("Paste threshold", "Please enter a whole number (0 or more).")
            paste_var.set(str(_paste_threshold))
        else:
            if new_paste_threshold != _paste_threshold:
                _paste_threshold = new_paste_threshold
                _save_config(paste_threshold=_paste_threshold)

        new_rules, bad_rule_lines = _parse_app_speed_rules(app_rules_text.get("1.0", "end"))
        if bad_rule_lines:
            messagebox.showerror(
                "Typing speed per program",
                "These lines were not understood, so the list was NOT changed:\n\n"
                + "\n".join(bad_rule_lines)
                + "\n\nUse:  program.exe = safe   (speeds: turbo / normal / safe)")
        elif new_rules != _app_speed_rules:
            _app_speed_rules = new_rules
            _save_config(app_speed_rules=_app_speed_rules)

        new_engine = engine_var.get().strip().lower() or _translate_engine
        if new_engine != _translate_engine:
            _translate_engine = new_engine
            _save_config(translate_engine=new_engine)

        new_api_key = claude_api_key_var.get().strip()
        if new_api_key != _claude_api_key:
            _claude_api_key = new_api_key
            _save_config(claude_api_key=new_api_key)

        new_gemini_api_key = gemini_api_key_var.get().strip()
        if new_gemini_api_key != _gemini_api_key:
            _gemini_api_key = new_gemini_api_key
            _save_config(gemini_api_key=new_gemini_api_key)

        new_deepl_api_key = deepl_api_key_var.get().strip()
        if new_deepl_api_key != _deepl_api_key:
            _deepl_api_key = new_deepl_api_key
            _save_config(deepl_api_key=new_deepl_api_key)

        new_custom_provider_selected = custom_provider_var.get().strip()
        if local_custom_providers != _custom_providers:
            _custom_providers = dict(local_custom_providers)
            _save_config(custom_providers=_custom_providers)
        if new_custom_provider_selected != _custom_provider_selected:
            _custom_provider_selected = new_custom_provider_selected
            _save_config(custom_provider_selected=new_custom_provider_selected)

        new_fallback_engine = _fallback_value_to_stored(fallback_var.get())
        if new_fallback_engine != _fallback_engine:
            _fallback_engine = new_fallback_engine
            _save_config(fallback_engine=new_fallback_engine)

        if _translate_engine == "claude" and not _claude_api_key:
            messagebox.showwarning(
                "Missing API key",
                "You selected the 'claude' engine but no API key is set. "
                "Paste your key above, or pick a different engine."
            )
        elif _translate_engine == "gemini" and not _gemini_api_key:
            messagebox.showwarning(
                "Missing API key",
                "You selected the 'gemini' engine but no API key is set. "
                "Paste your key above, or pick a different engine."
            )
        elif _translate_engine == "deepl" and not _deepl_api_key:
            messagebox.showwarning(
                "Missing API key",
                "You selected the 'deepl' engine but no API key is set. "
                "Paste your key above, or pick a different engine."
            )
        elif _translate_engine == "custom" and (
            not _custom_provider_selected or _custom_provider_selected not in _custom_providers
        ):
            messagebox.showwarning(
                "Missing provider",
                "You selected the 'custom' engine but no AI provider is set up. "
                "Press '+ Add' above to add one, or pick a different engine."
            )
        else:
            messagebox.showinfo("Settings", "Settings applied and saved as default.")

        # Re-check: hide the Quick fix button if the engine is OK now,
        # otherwise show what is still missing.
        _still = _engine_setup_problem()
        if _still:
            _set_quick_fix(ACTION_SETTINGS, _still, "Open Settings > Engine and add the API key / provider.")
        else:
            _set_quick_fix(ACTION_NONE)
        # Keep the main window's info block in sync with what was just saved
        _refresh_main_window()
        _usage_alert_level = 0
        _refresh_usage(force=True)  # engine/key may have changed: re-read usage
        _log_event("INFO", "Settings applied",
                   f"Engine: {_engine_display_name()}, fallback: {_fallback_engine_display_name()}, "
                   f"trigger: {_trigger_key.upper()}, popup: {_popup_trigger_key.upper()}, "
                   f"select: {_select_trigger_key.upper()}, speed: {_typing_speed_profile}, "
                   f"target language: {TARGET_LANGUAGE_CODE_TO_NAME.get(_target_language, _target_language)}", "")

    button_row = tk.Frame(win)
    button_row.pack(pady=15)
    def on_close():
        global _settings_window
        _settings_window = None
        win.destroy()

    tk.Button(button_row, text="Apply", width=12, command=on_apply).pack(side="left", padx=5)
    tk.Button(button_row, text="Close", width=12, command=on_close).pack(side="left", padx=5)
    win.protocol("WM_DELETE_WINDOW", on_close)
    _theme_apply_to(win)


# =========================================================================
# MAIN WINDOW
# -------------------------------------------------------------------------
# The program is no longer tray-only: it opens a normal, visible window
# that shows its current state and a live list of notifications. The
# "Minimize to tray" button is what hides it down next to the clock; the
# window's X button does the same thing (so the program is never closed
# by accident - use Exit for that). Left-clicking or double-clicking the
# tray icon brings the window back.
# =========================================================================
_info_var = None
_quick_fix_var = None
_quick_fix_button = None
_quick_fix_action = ACTION_NONE
_enable_button = None
_tray_hint_shown = False
_header_subtitle_label = None
_state_label = None
_theme_button = None
_dyn_frame = None        # holds the usage block + the Quick fix button
_actions_row = None
_quick_vars = {}         # "engine"/"tone"/"language"/"speed" -> StringVar
_quick_combos = {}       # same keys -> ttk.Combobox

_LEVEL_COLORS = {
    "OK": "#1b8a3a",
    "INFO": "#1f4e79",
    "WARN": "#b06a00",
    "ERROR": "#b3261e",
}


# =========================================================================
# DARK / LIGHT MODE
# -------------------------------------------------------------------------
# One palette per mode. _apply_theme() walks every widget of the program
# (main window, Settings, provider editor) and recolors it, so switching
# is instant and needs no restart. The choice is saved in config.json.
# The blue header and the 'translating...' capsule keep their own colors.
# =========================================================================
_THEMES = {
    "light": {
        "bg": "#f0f0f0", "fg": "#000000", "muted": "#666666", "field": "#ffffff",
        "readonly": "#f0f0f0", "log": "#fbfbfb", "button": "#f0f0f0",
        "button_active": "#e3e3e3", "accent": "#0f5d8c", "danger": "#b3261e",
        "select": "#cce4f7", "select_fg": "#000000", "border": "#cccccc", "bar_bg": "#e6e6e6",
        "ok": "#1b8a3a", "info": "#1f4e79", "warn": "#b06a00", "error": "#b3261e",
    },
    "dark": {
        "bg": "#1f2023", "fg": "#e8e8e8", "muted": "#a0a4aa", "field": "#2b2d31",
        "readonly": "#2b2d31", "log": "#17181a", "button": "#3a3d43",
        "button_active": "#4a4e55", "accent": "#6cb6e8", "danger": "#ff7b72",
        "select": "#0f5d8c", "select_fg": "#ffffff", "border": "#44474d", "bar_bg": "#3a3d43",
        "ok": "#4cc27a", "info": "#6cb6e8", "warn": "#e0a64a", "error": "#ff7b72",
    },
}
_LEVEL_PALETTE_KEYS = {"OK": "ok", "INFO": "info", "WARN": "warn", "ERROR": "error"}

_theme_name = _saved_config.get("theme", "light")
if _theme_name not in _THEMES:
    _theme_name = "light"
_orig_ttk_theme = None
_theme_skip = set()   # widget paths that keep their own colors (header, capsule, quick fix)

# Colors a widget may currently have -> which palette slot they mean.
_MUTED_COLORS = {"gray", "grey", "#444", "#444444", "#666666", "#a0a4aa"}
_ACCENT_COLORS = {"#0f5d8c", "#6cb6e8"}
_DANGER_COLORS = {"#b3261e", "#ff7b72"}
_PLAIN_FG_COLORS = {"", "black", "#000000", "#000", "systemwindowtext", "systembuttontext", "#e8e8e8"}


def _theme_fg_for(current, pal):
    """Map a widget's current text color to the matching palette color (None = leave it)."""
    cur = str(current).strip().lower()
    if cur in _MUTED_COLORS:
        return pal["muted"]
    if cur in _ACCENT_COLORS:
        return pal["accent"]
    if cur in _DANGER_COLORS:
        return pal["danger"]
    if cur in _PLAIN_FG_COLORS:
        return pal["fg"]
    return None


def _cfg(widget, **options):
    """widget.configure() that silently skips options this widget type doesn't have."""
    for key, value in options.items():
        try:
            widget.configure(**{key: value})
        except tk.TclError:
            pass


def _set_dark_titlebar(window, dark: bool):
    """Windows 10/11: dark title bar for the window (ignored elsewhere)."""
    if not _IS_WINDOWS:
        return
    try:
        window.update_idletasks()
        hwnd = ctypes.windll.user32.GetParent(window.winfo_id()) or window.winfo_id()
        value = ctypes.c_int(1 if dark else 0)
        ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, 20, ctypes.byref(value), ctypes.sizeof(value))
    except Exception:
        pass


def _configure_ttk(pal):
    """Style the ttk widgets (tabs + dropdowns) for the current mode."""
    global _orig_ttk_theme
    try:
        style = ttk.Style()
        if _orig_ttk_theme is None:
            _orig_ttk_theme = style.theme_use()
        if _theme_name == "dark":
            style.theme_use("clam")
            style.configure(".", background=pal["bg"], foreground=pal["fg"],
                            fieldbackground=pal["field"], bordercolor=pal["border"])
            style.configure("TNotebook", background=pal["bg"], bordercolor=pal["border"],
                            lightcolor=pal["bg"], darkcolor=pal["bg"])
            style.configure("TNotebook.Tab", background=pal["button"], foreground=pal["fg"],
                            padding=(8, 3), bordercolor=pal["border"],
                            lightcolor=pal["button"], darkcolor=pal["button"])
            style.map("TNotebook.Tab",
                      background=[("selected", pal["field"]), ("active", pal["button_active"])],
                      foreground=[("selected", pal["fg"])])
            style.configure("TCombobox", fieldbackground=pal["field"], background=pal["button"],
                            foreground=pal["fg"], arrowcolor=pal["fg"], bordercolor=pal["border"],
                            lightcolor=pal["field"], darkcolor=pal["field"],
                            selectbackground=pal["field"], selectforeground=pal["fg"])
            style.map("TCombobox",
                      fieldbackground=[("readonly", pal["field"]), ("disabled", pal["bg"])],
                      foreground=[("readonly", pal["fg"])],
                      selectbackground=[("readonly", pal["field"])],
                      selectforeground=[("readonly", pal["fg"])],
                      background=[("active", pal["button_active"])])
        else:
            style.theme_use(_orig_ttk_theme)
    except Exception as e:
        safe_print(f"[WARNING] Could not style the tabs/dropdowns: {e}")


def _theme_combo_popdown(combo, pal):
    """Recolor the list that drops down from a ttk Combobox."""
    try:
        popdown = str(combo.tk.call("ttk::combobox::PopdownWindow", str(combo)))
        combo.tk.call(popdown + ".f.l", "configure",
                      "-background", pal["field"], "-foreground", pal["fg"],
                      "-selectbackground", pal["select"], "-selectforeground", pal["select_fg"],
                      "-highlightbackground", pal["border"])
    except tk.TclError:
        pass


def _theme_walk(widget, pal):
    try:
        if str(widget) in _theme_skip:
            return
        cls = widget.winfo_class()
    except tk.TclError:
        return

    role = getattr(widget, "_theme_role", None)
    if cls in ("Tk", "Toplevel"):
        _cfg(widget, bg=pal["bg"])
        try:
            if cls == "Tk" or not widget.overrideredirect():
                _set_dark_titlebar(widget, _theme_name == "dark")
        except tk.TclError:
            pass
    elif cls == "Frame":
        try:
            is_line = int(widget.cget("height")) == 1
        except (tk.TclError, ValueError):
            is_line = False
        if is_line:
            _cfg(widget, bg=pal["border"])
        else:
            _cfg(widget, bg=pal["log"] if role == "log" else pal["bg"])
    elif cls == "Label":
        _cfg(widget, bg=pal["bg"])
        fg = _theme_fg_for(widget.cget("fg"), pal)
        if fg:
            _cfg(widget, fg=fg)
    elif cls == "Button":
        _cfg(widget, bg=pal["button"], activebackground=pal["button_active"],
             highlightbackground=pal["bg"])
        fg = _theme_fg_for(widget.cget("fg"), pal)
        if fg:
            _cfg(widget, fg=fg, activeforeground=fg)
    elif cls in ("Checkbutton", "Radiobutton"):
        _cfg(widget, bg=pal["bg"], activebackground=pal["bg"], selectcolor=pal["field"],
             highlightbackground=pal["bg"])
        fg = _theme_fg_for(widget.cget("fg"), pal)
        if fg:
            _cfg(widget, fg=fg, activeforeground=fg)
    elif cls in ("Entry", "Spinbox"):
        _cfg(widget, bg=pal["field"], fg=pal["fg"], insertbackground=pal["fg"],
             readonlybackground=pal["readonly"], disabledbackground=pal["readonly"],
             disabledforeground=pal["muted"], buttonbackground=pal["button"],
             highlightbackground=pal["border"], selectbackground=pal["select"],
             selectforeground=pal["select_fg"])
    elif cls == "Text":
        _cfg(widget, bg=pal["log"] if role == "log" else pal["field"], fg=pal["fg"],
             insertbackground=pal["fg"], selectbackground=pal["select"],
             selectforeground=pal["select_fg"], highlightbackground=pal["border"])
    elif cls == "Canvas":
        if role == "bar":
            color = pal["bar_bg"]
        elif role == "log":
            color = pal["log"]
        else:
            color = pal["bg"]
        _cfg(widget, bg=color, highlightbackground=color)
    elif cls == "Listbox":
        _cfg(widget, bg=pal["field"], fg=pal["fg"], selectbackground=pal["select"],
             selectforeground=pal["select_fg"])
    elif cls == "Menu":
        _cfg(widget, bg=pal["field"], fg=pal["fg"], activebackground=pal["select"],
             activeforeground=pal["select_fg"])
    elif cls == "Scrollbar":
        _cfg(widget, bg=pal["button"], troughcolor=pal["bg"], activebackground=pal["button_active"])
    elif cls == "TCombobox":
        _theme_combo_popdown(widget, pal)

    for child in widget.winfo_children():
        _theme_walk(child, pal)


def _theme_apply_to(widget):
    """Recolor one widget (and everything inside it) for the current mode. Tk main thread only."""
    if _root is None or widget is None:
        return
    try:
        _theme_walk(widget, _THEMES[_theme_name])
    except Exception as e:
        safe_print(f"[WARNING] Could not apply the {_theme_name} theme: {e}")


def _apply_theme():
    """Recolor the whole program for the current mode. Tk main thread only."""
    pal = _THEMES[_theme_name]
    _configure_ttk(pal)
    if _root is None:
        return
    try:
        _root.option_add("*TCombobox*Listbox.background", pal["field"])
        _root.option_add("*TCombobox*Listbox.foreground", pal["fg"])
        _root.option_add("*TCombobox*Listbox.selectBackground", pal["select"])
        _root.option_add("*TCombobox*Listbox.selectForeground", pal["select_fg"])
    except tk.TclError:
        pass
    if _working_win is not None:
        _theme_skip.add(str(_working_win))   # the capsule keeps its own colors
    _theme_walk(_root, pal)

    for widget in (_translations_log_widget, _errors_log_widget):
        if widget is not None and widget.winfo_exists():
            for level, key in _LEVEL_PALETTE_KEYS.items():
                try:
                    widget.tag_config(level, foreground=pal[key])
                except tk.TclError:
                    pass
    if _theme_button is not None and _theme_button.winfo_exists():
        _theme_button.config(text="☀  Light" if _theme_name == "dark" else "☾  Dark")
    _draw_usage_bar()


def _toggle_theme():
    """Header button / tray item: switch between dark and light mode and remember it."""
    global _theme_name
    _theme_name = "light" if _theme_name == "dark" else "dark"
    _save_config(theme=_theme_name)
    _apply_theme()


def _engine_display_name() -> str:
    """
    Human-friendly engine label for the main window. For the 'custom'
    engine, appends the selected provider's name (e.g. 'custom (GPT)')
    so it's clear at a glance which AI you're actually talking to,
    since 'custom' alone doesn't say that.
    """
    if _translate_engine == "custom":
        if _custom_provider_selected:
            return f"custom ({_custom_provider_selected})"
        return "custom (no provider selected)"
    return _translate_engine


def _header_subtitle_text() -> str:
    lang_name = TARGET_LANGUAGE_CODE_TO_NAME.get(_target_language, _target_language)
    return f"Arabic ↔ {lang_name}, anywhere you type  ·  v{APP_VERSION}"


def _current_info_text() -> str:
    """One compact line with the hotkeys (the dropdowns above show engine/tone/language/speed)."""
    lang_name = TARGET_LANGUAGE_CODE_TO_NAME.get(_target_language, _target_language)
    return (
        f"Arabic → {lang_name}: {_trigger_key.upper()}   ·   "
        f"Popup: {_popup_trigger_key.upper()} ({'ON' if _popup_auto_mode else 'OFF'})   ·   "
        f"Selected text: {_select_trigger_key.upper()}"
    )


# ---- Quick controls (the 4 dropdowns on the main window) ----
def _engine_choices() -> list:
    """Every built-in engine, plus each saved custom provider by its own name."""
    choices = [e for e in ENGINE_PRESETS if e != "custom"]
    if _custom_providers:
        choices += [f"custom ({name})" for name in _custom_providers]
    else:
        choices.append("custom")
    return choices


def _engine_current_choice() -> str:
    if _translate_engine == "custom":
        if _custom_provider_selected in _custom_providers:
            return f"custom ({_custom_provider_selected})"
        return "custom"
    return _translate_engine


def _engine_setup_problem() -> str:
    """Why the current engine can't work yet (missing key / provider), or ''."""
    if _translate_engine == "claude" and not _claude_api_key:
        return "The 'claude' engine has no API key yet."
    if _translate_engine == "gemini" and not _gemini_api_key:
        return "The 'gemini' engine has no API key yet."
    if _translate_engine == "deepl" and not _deepl_api_key:
        return "The 'deepl' engine has no API key yet."
    if _translate_engine == "custom" and (
        not _custom_provider_selected or _custom_provider_selected not in _custom_providers
    ):
        return "The 'custom' engine has no AI provider set up yet."
    return ""


def _sync_quick_controls():
    """Put the live settings into the 4 dropdowns. Tk main thread only."""
    if not _quick_combos:
        return
    try:
        _quick_combos["engine"]["values"] = _engine_choices()
        _quick_vars["engine"].set(_engine_current_choice())
        _quick_combos["tone"]["values"] = TONE_ORDER
        _quick_vars["tone"].set(_translation_tone)
        _quick_combos["language"]["values"] = TARGET_LANGUAGE_NAMES
        _quick_vars["language"].set(TARGET_LANGUAGE_CODE_TO_NAME.get(_target_language, _target_language))
        _quick_combos["speed"]["values"] = list(TYPING_SPEED_PRESETS.keys())
        _quick_vars["speed"].set(_typing_speed_profile)
    except tk.TclError:
        pass


def _apply_engine_choice(choice: str):
    """Switch engine (and custom provider) right away and save it. Tk main thread only."""
    global _translate_engine, _custom_provider_selected, _usage_alert_level
    choice = (choice or "").strip()
    if not choice:
        return
    if choice.startswith("custom (") and choice.endswith(")"):
        new_engine, new_provider = "custom", choice[len("custom ("):-1]
    else:
        new_engine, new_provider = choice, _custom_provider_selected
    if new_engine == _translate_engine and new_provider == _custom_provider_selected:
        return
    _translate_engine = new_engine
    _custom_provider_selected = new_provider
    _save_config(translate_engine=new_engine, custom_provider_selected=new_provider)
    _usage_alert_level = 0
    _refresh_usage(force=True)  # the usage meter belongs to the engine/provider
    problem = _engine_setup_problem()
    if problem:
        _report_warning("Engine needs setup", problem,
                        "Open Settings > Engine and add the API key / provider.", ACTION_SETTINGS)
    else:
        _set_quick_fix(ACTION_NONE)  # the new engine is fully set up
    _log_event("INFO", "Engine changed", f"Engine: {_engine_display_name()}", "")
    _refresh_main_window()
    try:
        if _tray_icon is not None:
            _tray_icon.update_menu()
    except Exception:
        pass


def _apply_tone_choice(tone: str):
    global _translation_tone
    tone = (tone or "").strip().lower()
    if tone in TONE_PRESETS and tone != _translation_tone:
        _translation_tone = tone
        _save_config(translation_tone=tone)
        _log_event("INFO", "Tone changed", f"Tone is now: {tone}", "")
    _refresh_main_window()
    try:
        if _tray_icon is not None:
            _tray_icon.update_menu()
    except Exception:
        pass


def _apply_language_choice(language_name: str):
    global _target_language
    code = TARGET_LANGUAGE_NAME_TO_CODE.get((language_name or "").strip())
    if code and code != _target_language:
        _target_language = code
        _save_config(target_language=code)
        _log_event("INFO", "Target language changed", f"Now: Arabic ↔ {language_name}", "")
    _refresh_main_window()


def _apply_speed_choice(profile: str):
    global _typing_speed_profile, _key_delay
    profile = (profile or "").strip().lower()
    if profile in TYPING_SPEED_PRESETS and profile != _typing_speed_profile:
        _typing_speed_profile = profile
        _key_delay = TYPING_SPEED_PRESETS[profile]
        _save_config(typing_speed_profile=profile)
        _log_event("INFO", "Typing speed changed", f"Typing speed is now: {profile}", "")
    _refresh_main_window()


def _on_quick_control_changed(name: str):
    """A dropdown on the main window changed - apply it immediately (no Apply button)."""
    value = _quick_vars[name].get()
    try:
        _quick_combos[name].selection_clear()
    except tk.TclError:
        pass
    if name == "engine":
        _apply_engine_choice(value)
    elif name == "tone":
        _apply_tone_choice(value)
    elif name == "language":
        _apply_language_choice(value)
    elif name == "speed":
        _apply_speed_choice(value)


def _refresh_main_window():
    """Re-read the live settings into the window. Tk main thread only."""
    if _info_var is not None:
        _info_var.set(_current_info_text())
    if _enable_button is not None:
        _enable_button.config(text="Disable" if _enabled else "Enable")
    if _state_label is not None:
        _state_label.config(text="●  Enabled" if _enabled else "●  Disabled",
                            fg="#7ee2a8" if _enabled else "#ffb4a8")
    if _header_subtitle_label is not None:
        _header_subtitle_label.config(text=_header_subtitle_text())
    _sync_quick_controls()


def _refresh_ui():
    """Thread-safe version of _refresh_main_window()."""
    _ui_call(_refresh_main_window)


def _log_event(level: str, where: str, cause: str, quick_fix: str):
    """
    Append one entry to the notification history inside the window,
    AND to the persistent log.txt file (so it survives closing the
    program). Safe to call from any thread.
    """
    _append_log_to_file(level, where, cause, quick_fix)
    _ui_call(_log_event_on_main_thread, level, where, cause, quick_fix)


# "where" labels that represent an actual successful translation result
# (as opposed to a status message like "Translator enabled" or "Settings
# applied") - these go in the "Translations" tab, with a ⭐ favorite
# button, instead of "Errors/Notices".
_TRANSLATION_EVENT_NAMES = {
    "Selection translated", "Typed text translated", "Auto-popup translation",
    "Retry succeeded", "Select-translate",
}


def _log_event_on_main_thread(level: str, where: str, cause: str, quick_fix: str):
    stamp = datetime.now().strftime("%H:%M:%S")
    is_translation = level == "OK" and where in _TRANSLATION_EVENT_NAMES and bool(cause)

    if is_translation:
        if _translations_log_widget is not None and _translations_log_widget.winfo_exists():
            widget = _translations_log_widget
            widget.config(state="normal")
            widget.insert("end", f"[{stamp}] {where}\n", level)

            star_btn = tk.Button(
                widget, text="⭐", font=("Segoe UI", 9), relief="flat", cursor="hand2",
                command=lambda text=cause: _add_favorite(text),
            )
            widget.window_create("end", window=star_btn)
            _theme_apply_to(star_btn)
            widget.insert("end", f"  {cause}\n\n")
            widget.see("end")
            widget.config(state="disabled")
    else:
        if _errors_log_widget is not None and _errors_log_widget.winfo_exists():
            widget = _errors_log_widget
            widget.config(state="normal")
            widget.insert("end", f"[{stamp}] {level} - {where}\n", level)
            if cause:
                widget.insert("end", f"    {cause}\n")
            if quick_fix:
                widget.insert("end", f"    → Fix: {quick_fix}\n")
            widget.insert("end", "\n")
            widget.see("end")
            widget.config(state="disabled")

    if _status_var is not None:
        _status_var.set(f"{level}: {where}" if level != "OK" else f"OK - {where}")


def _add_favorite(text: str):
    """Add 'text' to the favorites list, persist it, and refresh the Favorites tab."""
    global _favorites, _favorites_next_id
    if not text:
        return
    entry = {"id": _favorites_next_id, "text": text, "stamp": datetime.now().strftime(LOG_TIMESTAMP_FORMAT)}
    _favorites_next_id += 1
    _favorites.append(entry)
    _save_favorites(_favorites)
    _refresh_favorites_widget()
    _notify("Added to favorites", "You can find it under the Favorites tab - click it any time to copy.")


def _remove_favorite(favorite_id: int):
    """Remove one favorite by id, persist it, and refresh the Favorites tab."""
    global _favorites
    _favorites = [f for f in _favorites if f.get("id") != favorite_id]
    _save_favorites(_favorites)
    _refresh_favorites_widget()


def _copy_favorite_to_clipboard(text: str):
    """Clicking a favorite copies it to the clipboard (never auto-typed)."""
    if _set_clipboard_text(text):
        _notify("Copied", "The favorite was copied to the clipboard - paste it with Ctrl+V.")
    else:
        messagebox.showinfo("Favorite", text)


def _refresh_favorites_widget():
    """Rebuild the Favorites tab's list of rows from '_favorites'. Tk main thread only."""
    if _favorites_list_frame is None or not _favorites_list_frame.winfo_exists():
        return
    for child in _favorites_list_frame.winfo_children():
        child.destroy()

    if not _favorites:
        tk.Label(
            _favorites_list_frame, text="No favorites yet - press ⭐ next to a\ntranslation in the "
            "Translations tab to add one.",
            font=("Segoe UI", 9), fg="gray", justify="left", anchor="w",
        ).pack(anchor="w", padx=8, pady=8)
        _theme_apply_to(_favorites_list_frame)
        return

    for entry in reversed(_favorites):  # newest first
        fav_id = entry.get("id")
        text = entry.get("text", "")
        row = tk.Frame(_favorites_list_frame, relief="groove", borderwidth=1)
        row.pack(fill="x", padx=6, pady=3)

        label = tk.Label(
            row, text=text, font=("Segoe UI", 9), justify="left", anchor="w",
            wraplength=440, cursor="hand2",
        )
        label.pack(side="left", fill="x", expand=True, padx=(8, 4), pady=6)
        label.bind("<Button-1>", lambda e, t=text: _copy_favorite_to_clipboard(t))

        tk.Button(
            row, text="✕", font=("Segoe UI", 9), fg="#b3261e", relief="flat", cursor="hand2",
            command=lambda fid=fav_id: _remove_favorite(fid),
        ).pack(side="right", padx=(0, 6))

    _theme_apply_to(_favorites_list_frame)


def _set_quick_fix(action, cause: str = "", fix: str = ""):
    """
    Point the 'Quick fix' button at whatever would solve the last problem.
    The button now SHOWS the problem and its solution (not just an action
    name). Pass action=ACTION_NONE to hide it. Right-click it to dismiss.
    """
    _ui_call(_set_quick_fix_on_main_thread, action, cause, fix)


def _set_quick_fix_on_main_thread(action, cause: str = "", fix: str = ""):
    """Show the Quick fix button (orange / red) only while there is something to fix."""
    global _quick_fix_action
    _quick_fix_action = action
    if _quick_fix_button is None or not _quick_fix_button.winfo_exists():
        return
    labels = {
        ACTION_RETRY: "Click here: translate again",
        ACTION_RESTART: "Click here: restart the program",
        ACTION_SETTINGS: "Click here: open Settings",
    }
    colors = {ACTION_RETRY: "#d9822b", ACTION_RESTART: "#c0392b", ACTION_SETTINGS: "#d9822b"}
    if action in labels:
        def _short(text, limit):
            text = " ".join(str(text or "").split())
            return text if len(text) <= limit else text[:limit - 1] + "…"
        lines = []
        if cause:
            lines.append("⚠ Problem: " + _short(cause, 220))
        if fix:
            lines.append("✔ Solution: " + _short(fix, 260))
        lines.append("👉 " + labels[action] + "   (right-click to dismiss)")
        _quick_fix_button.config(text="\n".join(lines), bg=colors[action],
                                 activebackground=colors[action], fg="white",
                                 activeforeground="white", state="normal",
                                 wraplength=560, justify="left", anchor="w",
                                 font=("Segoe UI", 9, "bold"))
        if not _quick_fix_button.winfo_manager():
            _quick_fix_button.pack(side="top", fill="x", padx=14, pady=(0, 8), ipady=3)
    else:
        _quick_fix_button.pack_forget()


def _on_quick_fix_clicked():
    if _quick_fix_action == ACTION_RETRY:
        _retry_last_job()
    elif _quick_fix_action == ACTION_RESTART:
        if messagebox.askyesno("Restart", "Restart the program now?"):
            _restart_program()
    elif _quick_fix_action == ACTION_SETTINGS:
        _open_settings_window()


def _hide_to_tray():
    """The Minimize button: hide the window down next to the clock."""
    global _window_visible, _tray_hint_shown
    _window_visible = False
    if _root is not None:
        _root.withdraw()
    if not _tray_hint_shown:
        _tray_hint_shown = True
        _notify("Still running",
                "The window is hidden next to the clock. Click the tray icon to "
                "bring it back - translation keeps working meanwhile.")


def _show_main_window():
    """Bring the window back from the tray. Safe from any thread."""
    _ui_call(_show_main_window_on_main_thread)


def _show_main_window_on_main_thread():
    global _window_visible
    if _root is None:
        return
    _window_visible = True
    _root.deiconify()
    _root.lift()
    try:
        _root.attributes("-topmost", True)
        _root.after(400, lambda: _root.attributes("-topmost", False))
    except Exception:
        pass
    _refresh_main_window()


def _toggle_enabled_from_window():
    global _enabled
    _enabled = not _enabled
    with _buffer_lock:
        globals()["_buffer"] = ""
    _notify("Translator", "Enabled" if _enabled else "Disabled")
    _log_event("INFO", "Translator " + ("enabled" if _enabled else "disabled"), "", "")
    _refresh_main_window()


def _exit_program():
    """Fully quit: stop the tray icon, the hooks and the window."""
    if not messagebox.askyesno("Exit", "Close the translator completely?\n\n"
                                       "(Use 'Minimize to tray' if you only want to hide it.)"):
        return
    safe_print("[INFO] Exiting...")
    _popup_watcher_stop_event.set()
    try:
        keyboard.unhook_all()
    except Exception:
        pass
    try:
        if _tray_icon is not None:
            _tray_icon.visible = False
            _tray_icon.stop()
    except Exception:
        pass
    if _root is not None:
        _root.quit()
        _root.destroy()


def _confirm_restart():
    if messagebox.askyesno("Restart", "Restart the program now?"):
        _restart_program()


def _popup_more_menu(button, menu):
    """Open the '⋯ More' menu right under its button."""
    try:
        menu.tk_popup(button.winfo_rootx(), button.winfo_rooty() + button.winfo_height())
    finally:
        menu.grab_release()


def _build_main_window(root):
    """Fill the Tk root with the main window's contents."""
    global _status_var, _info_var, _translations_log_widget, _errors_log_widget
    global _favorites_list_frame, _quick_fix_button, _enable_button, _window_visible
    global _header_subtitle_label, _state_label, _theme_button, _dyn_frame, _actions_row
    global _usage_frame, _usage_title_var, _usage_detail_var, _usage_canvas

    root.title(APP_NAME)
    root.geometry("620x600")
    root.minsize(560, 520)

    # ---- Header (keeps its blue in both modes) ----
    header = tk.Frame(root, bg="#0f5d8c")
    header.pack(fill="x")
    _theme_skip.add(str(header))
    header_left = tk.Frame(header, bg="#0f5d8c")
    header_left.pack(side="left", fill="x", expand=True)
    tk.Label(header_left, text=APP_NAME, font=("Segoe UI", 14, "bold"),
             fg="white", bg="#0f5d8c").pack(anchor="w", padx=14, pady=(10, 0))
    _header_subtitle_label = tk.Label(header_left, text=_header_subtitle_text(),
                                      font=("Segoe UI", 9), fg="#cde6f5", bg="#0f5d8c")
    _header_subtitle_label.pack(anchor="w", padx=14, pady=(0, 10))
    header_right = tk.Frame(header, bg="#0f5d8c")
    header_right.pack(side="right", padx=12)
    _state_label = tk.Label(header_right, text="", font=("Segoe UI", 9, "bold"),
                            fg="white", bg="#0f5d8c")
    _state_label.pack(side="top", anchor="e", pady=(10, 3))
    _theme_button = tk.Button(header_right, text="", font=("Segoe UI", 9), fg="white",
                              bg="#1b78ad", activebackground="#2a8bc4", activeforeground="white",
                              relief="flat", cursor="hand2", padx=8, command=_toggle_theme)
    _theme_button.pack(side="top", anchor="e")

    # ---- Live status line ----
    _status_var = tk.StringVar(value="Running - no problems so far.")
    tk.Label(root, textvariable=_status_var, font=("Segoe UI", 10, "bold"),
             anchor="w", justify="left", wraplength=580).pack(fill="x", padx=14, pady=(10, 6))

    # ---- Quick controls: the things you change often, applied instantly ----
    quick = tk.Frame(root)
    quick.pack(fill="x", padx=14, pady=(0, 4))
    quick.columnconfigure(0, weight=1, uniform="quick")
    quick.columnconfigure(1, weight=1, uniform="quick")
    specs = [
        ("engine", "Engine", "engine"),
        ("tone", "Tone", "tone"),
        ("language", "Target language", "target_language"),
        ("speed", "Typing speed", "speed"),
    ]
    for index, (name, label_text, help_key) in enumerate(specs):
        column = index % 2
        cell = tk.Frame(quick)
        cell.grid(row=index // 2, column=column, sticky="ew", pady=(0, 6),
                  padx=(0, 6) if column == 0 else (6, 0))
        top = tk.Frame(cell)
        top.pack(fill="x")
        tk.Label(top, text=label_text, font=("Segoe UI", 8), fg="gray").pack(side="left")
        _help_button(top, help_key).pack(side="right")
        var = tk.StringVar()
        combo = ttk.Combobox(cell, textvariable=var, state="readonly", font=("Segoe UI", 9))
        combo.pack(fill="x")
        combo.bind("<<ComboboxSelected>>", lambda e, n=name: _on_quick_control_changed(n))
        _quick_vars[name] = var
        _quick_combos[name] = combo

    # ---- Hotkeys, one compact line ----
    _info_var = tk.StringVar(value=_current_info_text())
    tk.Label(root, textvariable=_info_var, font=("Segoe UI", 9), fg="gray",
             anchor="w", justify="left").pack(fill="x", padx=14, pady=(0, 6))

    # ---- Dynamic area: usage block (only when the provider reports real numbers)
    # and the Quick fix button (only while there is a problem to fix) ----
    _dyn_frame = tk.Frame(root)
    _dyn_frame.pack(fill="x")

    _usage_frame = tk.Frame(_dyn_frame)
    _usage_title_var = tk.StringVar()
    _usage_detail_var = tk.StringVar()
    _usage_top = tk.Frame(_usage_frame)
    _usage_top.pack(fill="x")
    tk.Label(_usage_top, textvariable=_usage_title_var, font=("Segoe UI", 9, "bold"),
             anchor="w").pack(side="left")
    tk.Button(_usage_top, text="Refresh", font=("Segoe UI", 8),
              command=lambda: _refresh_usage(force=True)).pack(side="right")
    tk.Label(_usage_frame, textvariable=_usage_detail_var, font=("Segoe UI", 9), fg="gray",
             anchor="w", justify="left", wraplength=580).pack(fill="x")
    _usage_canvas = tk.Canvas(_usage_frame, height=6, highlightthickness=0, bg="#e6e6e6")
    _usage_canvas._theme_role = "bar"
    _usage_canvas.bind("<Configure>", lambda e: _draw_usage_bar())

    _quick_fix_button = tk.Button(_dyn_frame, text="", font=("Segoe UI", 10, "bold"),
                                  relief="flat", cursor="hand2", fg="white",
                                  command=_on_quick_fix_clicked)
    _theme_skip.add(str(_quick_fix_button))   # it has its own orange / red colors
    _quick_fix_button.bind("<Button-3>", lambda e: _set_quick_fix(ACTION_NONE))  # right-click = dismiss

    # ---- Main buttons + '⋯ More' ----
    _actions_row = tk.Frame(root)
    _actions_row.pack(fill="x", padx=14, pady=(2, 8))
    for column in range(3):
        _actions_row.columnconfigure(column, weight=1, uniform="actions")
    _enable_button = tk.Button(_actions_row, text="Disable" if _enabled else "Enable",
                               command=_toggle_enabled_from_window)
    _enable_button.grid(row=0, column=0, sticky="ew", padx=(0, 6), ipady=3)
    tk.Button(_actions_row, text="Retry last", command=_retry_last_job).grid(
        row=0, column=1, sticky="ew", padx=6, ipady=3)
    tk.Button(_actions_row, text="Settings...", command=_open_settings_window).grid(
        row=0, column=2, sticky="ew", padx=6, ipady=3)
    more_button = tk.Button(_actions_row, text="⋯", width=4, font=("Segoe UI", 11, "bold"))
    more_button.grid(row=0, column=3, padx=(6, 0))
    more_menu = tk.Menu(root, tearoff=0)
    more_menu.add_command(label="Minimize to tray", command=_hide_to_tray)
    more_menu.add_command(label="Check for updates", command=_check_for_update_manual)
    more_menu.add_command(label="Restart program", command=_confirm_restart)
    more_menu.add_separator()
    more_menu.add_command(label="Exit", command=_exit_program)
    more_button.config(command=lambda: _popup_more_menu(more_button, more_menu))

    # ---- Notifications: three tabs - Translations / Errors&Notices / Favorites ----
    notif_notebook = ttk.Notebook(root)
    notif_notebook.pack(fill="both", expand=True, padx=14, pady=(2, 14))

    # -- Translations tab --
    translations_tab = tk.Frame(notif_notebook)
    notif_notebook.add(translations_tab, text="Translations")
    tr_scrollbar = tk.Scrollbar(translations_tab)
    tr_scrollbar.pack(side="right", fill="y")
    _translations_log_widget = tk.Text(
        translations_tab, height=10, wrap="word", font=("Segoe UI", 9),
        yscrollcommand=tr_scrollbar.set, state="disabled",
        background="#fbfbfb", relief="solid", borderwidth=1,
    )
    _translations_log_widget._theme_role = "log"
    _translations_log_widget.pack(side="left", fill="both", expand=True)
    tr_scrollbar.config(command=_translations_log_widget.yview)
    _translations_log_widget.tag_config("OK", foreground=_LEVEL_COLORS["OK"], font=("Segoe UI", 9, "bold"))

    # -- Errors/Notices tab --
    errors_tab = tk.Frame(notif_notebook)
    notif_notebook.add(errors_tab, text="Errors/Notices")
    err_scrollbar = tk.Scrollbar(errors_tab)
    err_scrollbar.pack(side="right", fill="y")
    _errors_log_widget = tk.Text(
        errors_tab, height=10, wrap="word", font=("Segoe UI", 9),
        yscrollcommand=err_scrollbar.set, state="disabled",
        background="#fbfbfb", relief="solid", borderwidth=1,
    )
    _errors_log_widget._theme_role = "log"
    _errors_log_widget.pack(side="left", fill="both", expand=True)
    err_scrollbar.config(command=_errors_log_widget.yview)
    for level, color in _LEVEL_COLORS.items():
        _errors_log_widget.tag_config(level, foreground=color, font=("Segoe UI", 9, "bold"))

    # -- Favorites tab -- (starred translations; click a row to copy it) --
    favorites_tab = tk.Frame(notif_notebook)
    notif_notebook.add(favorites_tab, text="Favorites")
    fav_canvas = tk.Canvas(favorites_tab, highlightthickness=0, background="#fbfbfb")
    fav_canvas._theme_role = "log"
    fav_scrollbar = tk.Scrollbar(favorites_tab, orient="vertical", command=fav_canvas.yview)
    _favorites_list_frame = tk.Frame(fav_canvas, background="#fbfbfb")
    _favorites_list_frame._theme_role = "log"
    _favorites_list_frame.bind(
        "<Configure>", lambda e: fav_canvas.configure(scrollregion=fav_canvas.bbox("all"))
    )
    fav_canvas.create_window((0, 0), window=_favorites_list_frame, anchor="nw", width=560)
    fav_canvas.configure(yscrollcommand=fav_scrollbar.set)
    fav_canvas.pack(side="left", fill="both", expand=True)
    fav_scrollbar.pack(side="right", fill="y")
    _refresh_favorites_widget()

    # The X button hides to the tray instead of killing the program,
    # so a stray click never silently stops translation.
    root.protocol("WM_DELETE_WINDOW", _hide_to_tray)
    _window_visible = True
    _init_working_indicator()

    _refresh_main_window()   # fills the dropdowns, the state label and the hotkeys line
    _apply_theme()           # dark / light, as saved last time


# =========================================================================
# System tray icon and menu (pystray)
# =========================================================================
def _make_tray_image():
    """
    Draw the tray icon in memory - no external image file needed, and
    no font file needed either (the glyph is pure geometry: a globe
    made of arcs/ellipses), so this renders identically on any machine
    the program runs on, including after being packaged into an .exe.
    Drawn at 4x size and downsampled with LANCZOS for smooth,
    anti-aliased edges instead of the old jagged low-res circle.
    """
    S = 256  # draw large, then shrink - this is what smooths the edges
    img = Image.new("RGBA", (S, S), (0, 0, 0, 0))

    # ---- Background: diagonal blue -> teal gradient, rounded-square mask ----
    grad = Image.new("RGB", (S, S), 0)
    top_color, bottom_color = (0, 122, 204), (0, 191, 165)
    gdraw = ImageDraw.Draw(grad)
    for y in range(S):
        t = y / (S - 1)
        r = int(top_color[0] + (bottom_color[0] - top_color[0]) * t)
        g = int(top_color[1] + (bottom_color[1] - top_color[1]) * t)
        b = int(top_color[2] + (bottom_color[2] - top_color[2]) * t)
        gdraw.line([(0, y), (S, y)], fill=(r, g, b))

    mask = Image.new("L", (S, S), 0)
    margin, radius = int(S * 0.03), int(S * 0.22)
    ImageDraw.Draw(mask).rounded_rectangle(
        [margin, margin, S - margin, S - margin], radius=radius, fill=255
    )
    img.paste(grad, (0, 0), mask)

    border = Image.new("RGBA", (S, S), (0, 0, 0, 0))
    ImageDraw.Draw(border).rounded_rectangle(
        [margin, margin, S - margin, S - margin], radius=radius,
        outline=(0, 70, 120, 160), width=max(2, S // 128)
    )
    img = Image.alpha_composite(img, border)

    # ---- Foreground: a simple globe glyph (universally read as "language") ----
    fdraw = ImageDraw.Draw(img)
    cx, cy = S // 2, S // 2
    r = int(S * 0.30)
    stroke = max(3, S // 60)
    white = (255, 255, 255, 235)
    fdraw.ellipse([cx - r, cy - r, cx + r, cy + r], outline=white, width=stroke)
    fdraw.ellipse([cx - r * 0.42, cy - r, cx + r * 0.42, cy + r], outline=white, width=stroke)
    fdraw.arc([cx - r, cy - r * 0.98, cx + r, cy + r * 1.9], start=200, end=340, fill=white, width=stroke)
    fdraw.arc([cx - r, cy - r * 1.9, cx + r, cy + r * 0.98], start=20, end=160, fill=white, width=stroke)

    return img.resize((64, 64), Image.LANCZOS)


def _notify(title: str, message: str, level: str = "info"):
    """
    Show a native system notification (Windows toast/balloon via
    pystray) with 'title'/'message'. This is the ONLY channel visible
    once the program is packaged as a windowed .exe with no console -
    so this is used for anything the user genuinely needs to notice
    (a toggle changed, an error happened), not routine chatter (that
    stays as safe_print(), which still shows up when run from a
    console during development). Never raises - notifications are a
    nice-to-have, never something that should crash the program.
    """
    safe_print(f"[NOTIFY] {title}: {message}")

    # Toast next to the clock (only exists once the tray icon is up)
    if _tray_icon is not None:
        try:
            _tray_icon.notify(message, title)
        except Exception:
            pass

    # Same text inside the main window, so nothing is missed if the
    # Windows toast was suppressed (Focus assist, notifications off...)
    def _update_status():
        if _status_var is not None:
            prefix = {"error": "PROBLEM", "warning": "NOTICE"}.get(level, "")
            _status_var.set(f"{prefix + ': ' if prefix else ''}{title}")
    _ui_call(_update_status)


def _tray_show_window(icon=None, item=None):
    """Left-click / double-click the tray icon, or 'Show window' in the menu."""
    _show_main_window()


def _tray_retry(icon, item):
    _retry_last_job()


def _tray_restart(icon, item):
    _ui_call(_restart_program)


def _tray_toggle_enabled(icon, item):
    global _enabled
    _enabled = not _enabled
    with _buffer_lock:
        globals()["_buffer"] = ""
    state = "Enabled" if _enabled else "Disabled"
    safe_print(f"[INFO] Translator {state.lower()}.")
    _notify("Translator", state)
    _log_event("INFO", f"Translator {state.lower()}", "", "")
    _refresh_ui()


def _tray_is_enabled(item):
    return _enabled


def _tray_toggle_popup_auto_mode(icon, item):
    _toggle_popup_auto_mode()


def _tray_is_popup_auto_mode(item):
    return _popup_auto_mode


def _tray_toggle_startup(icon, item):
    _set_startup_enabled(not _is_startup_enabled())


def _tray_is_startup_enabled(item):
    return _is_startup_enabled()


def _tray_open_settings(icon, item):
    # All Tk work happens on the single main thread - never in this
    # pystray callback thread.
    _ui_call(_open_settings_window)


def _tray_exit(icon, item):
    safe_print("[INFO] Exiting...")
    _popup_watcher_stop_event.set()
    try:
        keyboard.unhook_all()
    except Exception:
        pass
    icon.stop()
    if _root is not None:
        _ui_call(_root.quit)


def _tray_engine_action(choice):
    def _action(icon, item):
        _ui_call(_apply_engine_choice, choice)
    return _action


def _tray_engine_items():
    return [
        pystray.MenuItem(choice, _tray_engine_action(choice),
                         checked=(lambda item, c=choice: _engine_current_choice() == c),
                         radio=True)
        for choice in _engine_choices()
    ]


def _tray_tone_action(tone):
    def _action(icon, item):
        _ui_call(_apply_tone_choice, tone)
    return _action


def _tray_tone_items():
    return [
        pystray.MenuItem(tone, _tray_tone_action(tone),
                         checked=(lambda item, t=tone: _translation_tone == t),
                         radio=True)
        for tone in TONE_ORDER
    ]


def _tray_toggle_theme(icon, item):
    _ui_call(_toggle_theme)


def _tray_is_dark(item):
    return _theme_name == "dark"


def _build_tray_icon():
    menu = pystray.Menu(
        # default=True -> this is what a left-click/double-click on the
        # tray icon runs, so the window comes back the way people expect.
        pystray.MenuItem("Show window", _tray_show_window, default=True),
        pystray.MenuItem("Retry last translation", _tray_retry),
        pystray.MenuItem("Restart program", _tray_restart),
        pystray.Menu.SEPARATOR,
        pystray.MenuItem("Enabled", _tray_toggle_enabled, checked=_tray_is_enabled),
        pystray.MenuItem("Engine", pystray.Menu(_tray_engine_items)),
        pystray.MenuItem("Tone", pystray.Menu(_tray_tone_items)),
        pystray.MenuItem("Dark mode", _tray_toggle_theme, checked=_tray_is_dark),
        pystray.MenuItem("Auto EN -> AR popup (on copy)", _tray_toggle_popup_auto_mode, checked=_tray_is_popup_auto_mode),
        pystray.MenuItem("Start with Windows", _tray_toggle_startup, checked=_tray_is_startup_enabled),
        pystray.MenuItem("Settings...", _tray_open_settings),
        pystray.MenuItem("Check for updates", lambda icon, item: _check_for_update_manual()),
        pystray.MenuItem("Exit", _tray_exit),
    )
    return pystray.Icon("yalla_team_eg", _make_tray_image(), APP_NAME, menu)


# =========================================================================
# Entry point
# =========================================================================
# =========================================================================
# THEMED MESSAGE BOXES
# -------------------------------------------------------------------------
# Replaces tkinter's built-in 'messagebox' (the plain white Windows dialogs)
# with dialogs that use the program's own light/dark colors, and that always
# open IN FRONT: on top of the Settings window when it is open (the old
# dialogs opened behind it because Settings is an always-on-top window).
# It keeps the same function names, so every messagebox.showinfo(...),
# showwarning(...), showerror(...) and askyesno(...) call in the program
# works unchanged.
# =========================================================================
class _ThemedMessageBox:
    def _pick_owner(self, parent):
        """The visible window the dialog should sit on top of (or None)."""
        for window in (parent, _settings_window, _root):
            try:
                if window is not None and window.winfo_exists() and window.winfo_viewable():
                    return window
            except Exception:
                pass
        return None

    def _show(self, kind: str, title, message, parent=None, ask: bool = False):
        title, message = str(title), str(message)

        # Before the main window exists (startup errors) fall back to Windows' own dialog.
        if _root is None:
            if ask:
                return _tk_messagebox.askyesno(title, message)
            native = {"info": _tk_messagebox.showinfo, "warning": _tk_messagebox.showwarning,
                      "error": _tk_messagebox.showerror}.get(kind, _tk_messagebox.showinfo)
            return native(title, message)

        pal = _THEMES[_theme_name]
        glyph, color = {
            "info": ("i", pal["info"]), "warning": ("!", pal["warn"]),
            "error": ("✕", pal["error"]), "question": ("?", pal["info"]),
        }.get(kind, ("i", pal["info"]))
        result = {"value": False if ask else "ok"}

        owner = self._pick_owner(parent)
        win = tk.Toplevel(_root)
        win.withdraw()
        win.title(title)
        win.configure(bg=pal["bg"])
        win.resizable(False, False)
        win.attributes("-topmost", True)
        if owner is not None:
            try:
                win.transient(owner)
            except tk.TclError:
                pass

        def finish(value):
            result["value"] = value
            try:
                win.destroy()
            except tk.TclError:
                pass

        body = tk.Frame(win, bg=pal["bg"])
        body.pack(fill="both", expand=True, padx=22, pady=(20, 14))
        icon = tk.Canvas(body, width=40, height=40, bg=pal["bg"], highlightthickness=0)
        icon.create_oval(2, 2, 38, 38, fill=color, outline="")
        icon.create_text(20, 20, text=glyph, fill="white", font=("Segoe UI", 15, "bold"))
        icon.pack(side="left", anchor="n", padx=(0, 14))
        tk.Label(body, text=message, bg=pal["bg"], fg=pal["fg"], font=("Segoe UI", 10),
                 justify="left", anchor="w", wraplength=400).pack(side="left", fill="both", expand=True)

        tk.Frame(win, height=1, bg=pal["border"]).pack(fill="x")
        buttons = tk.Frame(win, bg=pal["bg"])
        buttons.pack(fill="x", padx=18, pady=12)

        def make_button(text, value, primary):
            return tk.Button(
                buttons, text=text, width=10, relief="flat", bd=0, cursor="hand2", padx=8, pady=5,
                font=("Segoe UI", 9, "bold" if primary else "normal"),
                bg=pal["select"] if primary else pal["button"],
                fg=pal["select_fg"] if primary else pal["fg"],
                activebackground=pal["button_active"], activeforeground=pal["fg"],
                command=lambda: finish(value))

        if ask:
            no_button = make_button("No", False, False)
            no_button.pack(side="right")
            yes_button = make_button("Yes", True, True)
            yes_button.pack(side="right", padx=(0, 8))
            default_button, cancel_value = yes_button, False
        else:
            ok_button = make_button("OK", "ok", True)
            ok_button.pack(side="right")
            default_button, cancel_value = ok_button, "ok"

        win.bind("<Return>", lambda e: default_button.invoke())
        win.bind("<Escape>", lambda e: finish(cancel_value))
        win.protocol("WM_DELETE_WINDOW", lambda: finish(cancel_value))

        # Center over the owner window (or the screen) and show in front.
        win.update_idletasks()
        w, h = win.winfo_reqwidth(), win.winfo_reqheight()
        try:
            if owner is not None:
                x = owner.winfo_rootx() + (owner.winfo_width() - w) // 2
                y = owner.winfo_rooty() + (owner.winfo_height() - h) // 2
            else:
                x = (win.winfo_screenwidth() - w) // 2
                y = (win.winfo_screenheight() - h) // 2
        except tk.TclError:
            x = y = 100
        x = min(max(x, 0), max(win.winfo_screenwidth() - w, 0))
        y = min(max(y, 0), max(win.winfo_screenheight() - h, 0))
        win.geometry(f"+{x}+{y}")
        win.deiconify()
        _set_dark_titlebar(win, _theme_name == "dark")
        win.lift()
        win.focus_force()
        default_button.focus_set()
        try:
            win.wait_visibility()
            win.grab_set()
        except tk.TclError:
            pass
        win.wait_window()
        return result["value"]

    def showinfo(self, title, message, **kwargs):
        return self._show("info", title, message, kwargs.get("parent"))

    def showwarning(self, title, message, **kwargs):
        return self._show("warning", title, message, kwargs.get("parent"))

    def showerror(self, title, message, **kwargs):
        return self._show("error", title, message, kwargs.get("parent"))

    def askyesno(self, title, message, **kwargs):
        return self._show("question", title, message, kwargs.get("parent"), ask=True)


messagebox = _ThemedMessageBox()


# =========================================================================
# AUTO-UPDATE (checks version.json on GitHub, asks the user, then
# downloads and runs the new Setup)
# =========================================================================
_update_check_in_flight = False
_update_declined_version = ""     # the version the user said "No" to (until next launch)
_update_download_in_flight = False


def _version_tuple(version_text) -> tuple:
    """'1.0.10' -> (1, 0, 10) so versions compare as numbers, not as text."""
    parts = re.findall(r"\d+", str(version_text))
    return tuple(int(p) for p in parts) if parts else (0,)


def _check_for_update(manual: bool = False):
    """
    Runs on a background thread. Downloads version.json and, if it
    holds a higher version than APP_VERSION, asks the user whether to
    install it. 'manual' = the user pressed "Check for updates", so we
    also tell them when they are already up to date or the check failed
    (an automatic check stays silent in those cases).
    """
    global _update_check_in_flight
    if _update_check_in_flight:
        return
    _update_check_in_flight = True
    try:
        request = urllib.request.Request(
            UPDATE_INFO_URL,
            headers={"Cache-Control": "no-cache", "User-Agent": f"{APP_NAME}/{APP_VERSION}"},
        )
        with urllib.request.urlopen(request, timeout=UPDATE_CHECK_TIMEOUT_SECONDS) as resp:
            info = json.loads(resp.read().decode("utf-8"))

        latest = str(info.get("version", "")).strip()
        url = str(info.get("url", "")).strip()
        notes = str(info.get("notes", "")).strip()
        if not latest:
            raise ValueError("version.json has no 'version' value.")

        if _version_tuple(latest) > _version_tuple(APP_VERSION):
            if not url.lower().startswith("https://"):
                # A new version exists but its download link is missing/unsafe.
                safe_print(f"[INFO] Version {latest} is published but has no valid https download link yet.")
                if manual:
                    _ui_call(messagebox.showinfo, "Update",
                             f"Version {latest} is announced, but its download link is not ready yet. "
                             "Try again a bit later.")
                return
            if not manual and latest == _update_declined_version:
                return  # the user already said "No" to this one in this session
            _ui_call(_offer_update, latest, url, notes)
        elif manual:
            _ui_call(messagebox.showinfo, "Update",
                     f"You already have the latest version ({APP_VERSION}).")
    except Exception as e:
        safe_print(f"[INFO] Update check failed: {e}")
        if manual:
            _ui_call(messagebox.showwarning, "Update",
                     "Could not check for updates. Check your internet connection and try again.\n\n"
                     f"({type(e).__name__}: {e})")
    finally:
        _update_check_in_flight = False


def _offer_update(latest: str, url: str, notes: str):
    """Ask the user whether to install the new version. Tk main thread only."""
    global _update_declined_version
    message = f"A new version is available: {latest}\n(you have {APP_VERSION})\n"
    if notes:
        message += f"\nWhat's new:\n{notes}\n"
    message += ("\nDownload and install it now?\n"
                "The program will close and the installer will open.\n\n"
                "فيه نسخة جديدة، تحمّلها وتثبّتها دلوقتي؟")
    if messagebox.askyesno("Update available", message):
        threading.Thread(target=_download_and_install_update, args=(url, latest), daemon=True).start()
    else:
        _update_declined_version = latest


_update_cancel_event = threading.Event()
_update_progress_win = None
_update_progress_bar = None
_update_progress_label = None


class _UpdateCancelled(Exception):
    """The user pressed Cancel while the update was downloading."""


def _show_update_progress(latest: str):
    """Small 'Downloading update' window with a progress bar. Tk main thread only."""
    global _update_progress_win, _update_progress_bar, _update_progress_label
    try:
        win = tk.Toplevel(_root)
        win.title("Updating")
        win.geometry("380x140")
        win.resizable(False, False)
        win.transient(_root)
        win.protocol("WM_DELETE_WINDOW", _update_cancel_event.set)
        tk.Label(win, text=f"Downloading version {latest}...", font=("Arial", 11, "bold")).pack(pady=(14, 4))
        bar = ttk.Progressbar(win, orient="horizontal", length=330, mode="determinate", maximum=100)
        bar.pack(pady=4)
        label = tk.Label(win, text="Starting...", font=("Arial", 9))
        label.pack()
        ttk.Button(win, text="Cancel", command=_update_cancel_event.set).pack(pady=8)
        _update_progress_win, _update_progress_bar, _update_progress_label = win, bar, label
    except Exception as e:
        safe_print(f"[INFO] Could not show the update window: {e}")


def _set_update_progress(done: int, total: int):
    """Move the bar. Tk main thread only."""
    try:
        if _update_progress_bar is None:
            return
        if total > 0:
            _update_progress_bar["value"] = done * 100 / total
            _update_progress_label.config(text=f"{done / 1048576:.1f} / {total / 1048576:.1f} MB  ({done * 100 // total}%)")
        else:
            _update_progress_label.config(text=f"{done / 1048576:.1f} MB")
    except Exception:
        pass


def _set_update_progress_text(text: str):
    """Change the line under the bar. Tk main thread only."""
    try:
        if _update_progress_label is not None:
            _update_progress_label.config(text=text)
    except Exception:
        pass


def _close_update_progress():
    """Close the progress window. Tk main thread only."""
    global _update_progress_win, _update_progress_bar, _update_progress_label
    try:
        if _update_progress_win is not None:
            _update_progress_win.destroy()
    except Exception:
        pass
    _update_progress_win = _update_progress_bar = _update_progress_label = None


def _launch_silent_installer(setup_path: str):
    """
    Run the Setup silently AFTER this program has closed, then start the
    new version again. Done through a small detached 'cmd' so it keeps
    running after we exit: wait ~3s -> run Setup and wait for it to
    finish -> launch the program.
    """
    import subprocess
    flags = "/VERYSILENT /SUPPRESSMSGBOXES /NORESTART /CLOSEAPPLICATIONS /FORCECLOSEAPPLICATIONS"
    cmd = f'ping -n 4 127.0.0.1 >nul & start /wait "" "{setup_path}" {flags}'
    if getattr(sys, "frozen", False):  # built exe: start the program again afterwards
        cmd += f' & start "" "{sys.executable}"'
    DETACHED_PROCESS = 0x00000008
    CREATE_NEW_PROCESS_GROUP = 0x00000200
    CREATE_NO_WINDOW = 0x08000000
    subprocess.Popen(f'cmd.exe /s /c "{cmd}"',
                     creationflags=DETACHED_PROCESS | CREATE_NEW_PROCESS_GROUP | CREATE_NO_WINDOW,
                     close_fds=True)


def _download_and_install_update(url: str, latest: str):
    """Download the Setup with a progress bar, close this program, install silently, relaunch."""
    global _update_download_in_flight
    if _update_download_in_flight:
        return
    _update_download_in_flight = True
    _update_cancel_event.clear()
    target = os.path.join(os.environ.get("TEMP", os.path.expanduser("~")),
                          f"YallaTeamEG_Setup_{latest}.exe")
    try:
        _log_event("INFO", "Downloading update", f"Version {latest}", "")
        _ui_call(_show_update_progress, latest)
        request = urllib.request.Request(url, headers={"User-Agent": f"{APP_NAME}/{APP_VERSION}"})
        with urllib.request.urlopen(request, timeout=UPDATE_DOWNLOAD_TIMEOUT_SECONDS) as resp, \
                open(target + ".part", "wb") as out:
            try:
                total = int(resp.headers.get("Content-Length") or 0)
            except ValueError:
                total = 0
            done = 0
            last_ui = 0.0
            while True:
                if _update_cancel_event.is_set():
                    raise _UpdateCancelled()
                chunk = resp.read(1024 * 128)
                if not chunk:
                    break
                out.write(chunk)
                done += len(chunk)
                now = time.time()
                if now - last_ui >= 0.1:
                    last_ui = now
                    _ui_call(_set_update_progress, done, total)
        if os.path.getsize(target + ".part") < 100 * 1024:
            raise RuntimeError("The downloaded file is too small to be the installer.")
        os.replace(target + ".part", target)

        _ui_call(_set_update_progress, done, done or 1)
        _ui_call(_set_update_progress_text, "Installing... the program will restart by itself.")
        _log_event("OK", "Update downloaded", f"Installing {latest} silently", "")
        _launch_silent_installer(target)
        time.sleep(1.0)
        _ui_call(_quit_for_update)
        time.sleep(4.0)
        os._exit(0)  # safety net: make sure we are really closed so the Setup can replace the files
    except _UpdateCancelled:
        _ui_call(_close_update_progress)
        try:
            os.remove(target + ".part")
        except OSError:
            pass
        _notify("Update", "Update cancelled.")
    except Exception as e:
        _ui_call(_close_update_progress)
        _report_problem("Update failed", exc=e, counts_as_failure=False)
        # Fallback: let the browser download it instead (the browser often
        # works where the program's own download is blocked by the network).
        _ui_call(_offer_browser_download, url)
    finally:
        _update_download_in_flight = False


def _offer_browser_download(url: str):
    """Ask the user to open the installer link in the browser. Tk main thread only."""
    try:
        if messagebox.askyesno(
                "Update",
                "Automatic download failed.\n"
                "Open the download link in your browser instead?\n\n"
                "فشل التحميل التلقائي، تفتح رابط التحميل في المتصفح؟"):
            webbrowser.open(url)
    except Exception as e:
        safe_print(f"[INFO] Could not open the browser fallback: {e}")


def _quit_for_update():
    """Close the program without a confirmation so the installer can replace it."""
    safe_print("[INFO] Closing for the update...")
    _popup_watcher_stop_event.set()
    try:
        keyboard.unhook_all()
    except Exception:
        pass
    try:
        if _tray_icon is not None:
            _tray_icon.visible = False
            _tray_icon.stop()
    except Exception:
        pass
    if _root is not None:
        _root.quit()
        _root.destroy()


def _check_for_update_manual():
    """The 'Check for updates' buttons/menu items."""
    threading.Thread(target=_check_for_update, kwargs={"manual": True}, daemon=True).start()


def _schedule_update_checks():
    """Check shortly after startup, then every UPDATE_CHECK_INTERVAL_HOURS. Tk main thread only."""
    threading.Thread(target=_check_for_update, daemon=True).start()
    if _root is not None:
        _root.after(UPDATE_CHECK_INTERVAL_HOURS * 3600 * 1000, _schedule_update_checks)


def _fatal_error_dialog(message: str):
    """
    Show a blocking native error dialog. Used ONLY for startup failures
    that happen before the tray icon exists (so _notify() has nothing
    to show a toast through yet) - without this, a packaged windowed
    .exe with no console would fail completely silently and just
    vanish, leaving no clue why.
    """
    safe_print(f"[FATAL ERROR DIALOG] {message}")
    try:
        root = tk.Tk()
        root.withdraw()
        messagebox.showerror(f"{APP_NAME} - Startup Error", message)
        root.destroy()
    except Exception:
        pass


# =========================================================================
# SINGLE INSTANCE (only one copy of the program may run at a time)
# =========================================================================
_SINGLE_INSTANCE_MUTEX_NAME = "Local\\YallaTeamEG_SingleInstance_Mutex"
_SINGLE_INSTANCE_EVENT_NAME = "Local\\YallaTeamEG_SingleInstance_ShowEvent"
_single_instance_handles = []   # kept alive for the whole run so Windows holds the lock


def _acquire_single_instance() -> bool:
    """
    Returns True if this is the only copy running (and locks it), or
    False if another copy already runs - in which case that copy is
    told to bring its window to the front.
    After an automatic restart the old copy may still be closing, so
    then we wait up to 10 seconds for it to let go.
    """
    if not _IS_WINDOWS:
        return True
    try:
        from ctypes import wintypes
        k32 = ctypes.WinDLL("kernel32", use_last_error=True)
        k32.CreateMutexW.restype = wintypes.HANDLE
        k32.CreateMutexW.argtypes = [wintypes.LPVOID, wintypes.BOOL, wintypes.LPCWSTR]
        k32.OpenEventW.restype = wintypes.HANDLE
        k32.OpenEventW.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.LPCWSTR]
        k32.SetEvent.argtypes = [wintypes.HANDLE]
        k32.CloseHandle.argtypes = [wintypes.HANDLE]

        ERROR_ALREADY_EXISTS = 183
        EVENT_MODIFY_STATE = 0x0002
        restarting = bool(os.environ.pop("YALLA_RESTARTING", ""))
        deadline = time.time() + (10 if restarting else 0)
        while True:
            handle = k32.CreateMutexW(None, False, _SINGLE_INSTANCE_MUTEX_NAME)
            err = ctypes.get_last_error()
            if not handle:
                return True  # could not create the lock at all - do not block the user
            if err != ERROR_ALREADY_EXISTS:
                _single_instance_handles.append(handle)
                return True
            k32.CloseHandle(handle)
            if time.time() >= deadline:
                break
            time.sleep(0.2)

        # Another copy is running: ask it to show its window, then give up.
        ev = k32.OpenEventW(EVENT_MODIFY_STATE, False, _SINGLE_INSTANCE_EVENT_NAME)
        if ev:
            k32.SetEvent(ev)
            k32.CloseHandle(ev)
        return False
    except Exception as e:
        safe_print(f"[WARNING] Single-instance check failed: {e}")
        return True


def _start_single_instance_listener():
    """
    Background thread: when a second copy is launched it signals an event,
    and this brings our window back (even if it is hidden in the tray).
    """
    if not _IS_WINDOWS:
        return
    try:
        from ctypes import wintypes
        k32 = ctypes.WinDLL("kernel32", use_last_error=True)
        k32.CreateEventW.restype = wintypes.HANDLE
        k32.CreateEventW.argtypes = [wintypes.LPVOID, wintypes.BOOL, wintypes.BOOL, wintypes.LPCWSTR]
        k32.WaitForSingleObject.restype = wintypes.DWORD
        k32.WaitForSingleObject.argtypes = [wintypes.HANDLE, wintypes.DWORD]
        event = k32.CreateEventW(None, False, False, _SINGLE_INSTANCE_EVENT_NAME)  # auto-reset
        if not event:
            return
        _single_instance_handles.append(event)

        def _listen():
            while True:
                result = k32.WaitForSingleObject(event, 0xFFFFFFFF)  # INFINITE
                if result == 0:  # WAIT_OBJECT_0 = signaled
                    try:
                        _show_main_window()
                    except Exception:
                        pass
                else:
                    time.sleep(1)

        threading.Thread(target=_listen, daemon=True).start()
    except Exception as e:
        safe_print(f"[WARNING] Could not start the single-instance listener: {e}")


def main():
    global _tray_icon, _root

    if not _acquire_single_instance():
        sys.exit(0)  # already running - the existing window was brought to the front

    _trim_log_file()  # Drop log.txt entries older than LOG_RETENTION_DAYS

    _lang_name = TARGET_LANGUAGE_CODE_TO_NAME.get(_target_language, _target_language)
    safe_print("=" * 60)
    safe_print(f" {APP_NAME} is now running")
    safe_print(f" Type an Arabic sentence anywhere, then press {_trigger_key.upper()} to auto-translate"
               f" (target language: {_lang_name})")
    safe_print(f" Press {_popup_trigger_key.upper()} to toggle auto {_lang_name} -> AR popup mode "
               f"(then just copy {_lang_name} text - no extra key needed)")
    safe_print(f" Select text with the mouse anywhere and press {_select_trigger_key.upper()} "
               f"to translate it in place (direction auto-detected)")
    safe_print(" The main window shows the status, any problems, and the quick fix "
               "for each one")
    safe_print(" 'Minimize to tray' hides it near the clock - click the tray icon to "
               "bring it back")
    safe_print("=" * 60)

    try:
        keyboard.hook(_on_key_event)
        if not _register_hotkey(_trigger_key):
            _fatal_error_dialog(
                f"Could not register the trigger key ({_trigger_key.upper()}).\n\n"
                "It may already be in use by another program.\n\nThe program will now close."
            )
            sys.exit(1)
    except Exception as e:
        _fatal_error_dialog(
            f"Could not start the keyboard listener:\n{e}\n\n"
            "Try running this program as Administrator.\n\nThe program will now close."
        )
        sys.exit(1)

    # ---- The single Tk root == the visible main window ----
    # Tk must own the MAIN thread, so the tray icon is what moves to a
    # background thread now (the Windows pystray backend supports this).
    _root = tk.Tk()
    _build_main_window(_root)
    _pump_ui_queue()  # starts the background -> UI task pump
    _start_single_instance_listener()  # a second launch brings this window to the front
    _refresh_usage(force=True)
    _root.after(5000, _schedule_update_checks)  # first update check ~5s after launch

    _tray_icon = _build_tray_icon()
    threading.Thread(target=_tray_icon.run, daemon=True).start()

    _log_event("OK", "Translator started",
               f"{_trigger_key.upper()} = Arabic → {_lang_name}, "
               f"{_popup_trigger_key.upper()} = toggle the {_lang_name} → Arabic auto-popup.",
               "Press 'Minimize to tray' to hide this window next to the clock.")

    # Registered after the tray icon exists, so a failure here can show
    # a proper toast notification instead of vanishing silently.
    if not _register_popup_hotkey(_popup_trigger_key):
        safe_print("[WARNING] Could not register the popup trigger key - the "
                   "English -> Arabic popup feature will be unavailable until "
                   "you set a working key in Settings.")
        _report_problem(
            "Popup trigger key unavailable",
            cause=f"'{_popup_trigger_key.upper()}' could not be registered - another "
                  f"program is probably already using it.",
            quick_fix="Open Settings and choose a different auto-popup key.",
            action=ACTION_SETTINGS,
            counts_as_failure=False,
        )

    if not _register_select_hotkey(_select_trigger_key):
        safe_print("[WARNING] Could not register the Select-translate trigger key - "
                   "the mouse-selection translate feature will be unavailable until "
                   "you set a working key in Settings.")
        _report_problem(
            "Select-translate trigger key unavailable",
            cause=f"'{_select_trigger_key.upper()}' could not be registered - another "
                  f"program is probably already using it.",
            quick_fix="Open Settings and choose a different Select-translate key.",
            action=ACTION_SETTINGS,
            counts_as_failure=False,
        )

    if _tone_trigger_key:
        saved_tone_key = _tone_trigger_key
        if not _register_tone_hotkey(saved_tone_key):
            _report_problem(
                "Tone key unavailable",
                cause=f"'{saved_tone_key.upper()}' could not be registered as the tone-switch key.",
                quick_fix="Open Settings > Advanced and choose a different key (or leave it empty).",
                action=ACTION_SETTINGS,
                counts_as_failure=False,
            )

    try:
        _root.mainloop()  # Blocks here until Exit (or the tray's Exit item)
    except KeyboardInterrupt:
        safe_print("Program stopped by user.")
    finally:
        try:
            _popup_watcher_stop_event.set()
            keyboard.unhook_all()
        except Exception:
            pass
        try:
            if _tray_icon is not None:
                _tray_icon.visible = False
                _tray_icon.stop()
        except Exception:
            pass


if __name__ == "__main__":
    main()
