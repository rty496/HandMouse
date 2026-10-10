"""
Hand Mouse — керування комп'ютером рукою через веб-камеру.

Запуск: подвійний клік по цьому файлу (HandMouse.pyw) або по ярлику «Hand Mouse».
Консоль не відкривається; усе керування — у вікні програми.

Жести (одна рука, долонею до камери):
  Відкрита рука ................ рух курсора
  Великий + вказівний, коротко .. лівий клік (двічі = подвійний клік)
  Великий + вказівний, тримати .. затиснути ліву кнопку (перетягування / стрільба)
  Великий + середній ............ правий клік
  «Peace» ✌ + рух вгору/вниз .... прокрутка
  Кулак ✊ ...................... пауза («підняти мишу», щоб переставити руку)

Глобальні клавіші: F8 — ігровий режим, F9 — пауза.
"""

import base64
import json
import math
import queue
import os
import struct
import subprocess
import sys
import threading
import time
import traceback
import urllib.request

import tkinter as tk
from tkinter import messagebox, ttk

APP_NAME = "Hand Mouse"
FROZEN = getattr(sys, "frozen", False)            # True, коли запущено як HandMouse.exe
APP_FILE = sys.executable if FROZEN else os.path.abspath(__file__)
APP_DIR = os.path.dirname(APP_FILE)
DATA_DIR = os.path.join(os.environ.get("APPDATA") or os.path.expanduser("~"), "HandMouse")
os.makedirs(DATA_DIR, exist_ok=True)
SETTINGS_PATH = os.path.join(DATA_DIR, "settings.json")
MODEL_PATH = os.path.join(DATA_DIR, "hand_landmarker.task")
ICON_PATH = os.path.join(DATA_DIR, "hand_mouse.ico")
LOG_PATH = os.path.join(DATA_DIR, "hand_mouse.log")
MODEL_URL = ("https://storage.googleapis.com/mediapipe-models/hand_landmarker/"
             "hand_landmarker/float16/1/hand_landmarker.task")

IS_WIN = sys.platform.startswith("win")
NO_WINDOW = 0x08000000 if IS_WIN else 0   # CREATE_NO_WINDOW

REQUIRED = {"cv2": "opencv-python", "mediapipe": "mediapipe", "pyautogui": "pyautogui"}

DEFAULTS = {
    "camera": 0,
    "autostart": True,
    "game_mode": False,
    "desktop_style": "relative",   # relative = «як миша» (точніше), absolute = пряме наведення
    "sensitivity": 1.0,            # чутливість курсора
    "smoothing": 0.5,              # 0 = швидко/тремтить, 1 = плавно/повільніше
    "freeze_click": True,          # не зсувати курсор під час кліку
    "zone": 0.15,                  # рамка для прямого наведення та центру джойстика
    "game_style": "hybrid",        # hybrid = джойстик + приціл, mouse = як миша (кулак — перехопити)
    "game_vertical": False,        # повертати вгору/вниз джойстиком (вимкнено: камера не «пливе» в небо)
    "game_cx": 0.5, "game_cy": 0.5,  # центр джойстика (F7 — поставити туди, де зараз рука)
    "game_overlay": True,          # міні-камера поверх гри
    "game_turn": 18.0,             # швидкість безперервного повороту в грі
    "game_aim": 1.0,               # точне доведення прицілу в грі
    "game_deadzone": 0.22,         # мертва зона джойстика
    "show_camera": True,
    "fast_camera": False,          # ручна витримка: більше кадрів/с, але темніше зображення
    "topmost": False,
    "voice": False,                # голосові команди
    "voice_device": "",            # назва мікрофона ("" = стандартний)
    "voice_gain": 1.0,             # програмне підсилення мікрофона
    "voice_engine": "mine",        # mine = «Мій голос» (власні зразки), model = модель Vosk
    "voice_model": "small",        # small = точніша (133 МБ), nano = швидша (73 МБ)
    "voice_strict": 0.5,           # суворість розпізнавання (0..1): вище — менше хибних спрацювань
    "voice_off": [],               # вимкнені команди
    "pinch_on": None, "pinch_off": None,   # пороги з калібрування (None = стандартні)
    "mid_on": None, "mid_off": None,
    "freeze_ratio": None,
    "calibrated": False,
    "_shortcut_offered": False,
    "overlay_pos": None,
}

# --- Константи жестів і точності (з досліджень, див. README) ---
PINCH_ON, PINCH_OFF = 0.28, 0.40      # поріг щипка відносно розміру долоні (гістерезис)
PINCH_FRAMES = 2                      # скільки кадрів поспіль має триматися стан (антидребезг)
FREEZE_RATIO = 0.50                   # пальці почали зводитися — запам'ятати позицію курсора
ROLLBACK_WINDOW = 0.40                # сек: якщо щипок стався так швидко — повернути курсор назад
HOLD_TO_DRAG = 0.35                   # сек утримання щипка до початку перетягування
G_MIN, G_MAX = 0.7, 4.0               # підсилення: повільна рука -> точно, швидка -> далеко
V_SLOW, V_FAST = 0.08, 1.0            # швидкості руки (частка кадру за секунду)
GAME_AIM_PX = 1800                    # пікселів миші на всю ширину кадру для точного прицілу
SCROLL_SPEED = 250
JUMP_LIMIT = 0.12                     # макс. правдоподібний зсув долоні за кадр (частка кадру)

PALM = (0, 5, 9, 13, 17)              # точки долоні: середнє з них тремтить менше за одну точку
WRIST, THUMB_TIP, INDEX_PIP, INDEX_TIP = 0, 4, 6, 8
MIDDLE_MCP, MIDDLE_PIP, MIDDLE_TIP = 9, 10, 12
RING_PIP, RING_TIP, PINKY_PIP, PINKY_TIP = 14, 16, 18, 20
HAND_CONNECTIONS = [(0, 1), (1, 2), (2, 3), (3, 4), (0, 5), (5, 6), (6, 7), (7, 8), (5, 9), (9, 10),
                    (10, 11), (11, 12), (9, 13), (13, 14), (14, 15), (15, 16), (13, 17), (17, 18),
                    (18, 19), (19, 20), (0, 17)]


def log(msg):
    try:
        with open(LOG_PATH, "a", encoding="utf-8") as f:
            f.write(time.strftime("%Y-%m-%d %H:%M:%S ") + msg + "\n")
    except OSError:
        pass


def load_settings():
    s = dict(DEFAULTS)
    try:
        with open(SETTINGS_PATH, encoding="utf-8") as f:
            s.update({k: v for k, v in json.load(f).items() if k in DEFAULTS})
    except (OSError, ValueError):
        pass
    return s


def save_settings(s):
    try:
        with open(SETTINGS_PATH, "w", encoding="utf-8") as f:
            json.dump(s, f, ensure_ascii=False, indent=2)
    except OSError:
        pass


# ============================== Windows: ввід, клавіші, ярлики ==============================
if IS_WIN:
    import ctypes
    from ctypes import wintypes

    class _MOUSEINPUT(ctypes.Structure):
        _fields_ = [("dx", wintypes.LONG), ("dy", wintypes.LONG), ("mouseData", wintypes.DWORD),
                    ("dwFlags", wintypes.DWORD), ("time", wintypes.DWORD), ("dwExtraInfo", ctypes.c_size_t)]

    class _KEYBDINPUT(ctypes.Structure):
        _fields_ = [("wVk", wintypes.WORD), ("wScan", wintypes.WORD), ("dwFlags", wintypes.DWORD),
                    ("time", wintypes.DWORD), ("dwExtraInfo", ctypes.c_size_t)]

    class _INPUTUNION(ctypes.Union):
        _fields_ = [("mi", _MOUSEINPUT), ("ki", _KEYBDINPUT)]

    class _INPUT(ctypes.Structure):
        _fields_ = [("type", wintypes.DWORD), ("u", _INPUTUNION)]

    _user32 = ctypes.WinDLL("user32", use_last_error=True)
    _user32.SendInput.argtypes = (wintypes.UINT, ctypes.POINTER(_INPUT), ctypes.c_int)
    _user32.GetAsyncKeyState.argtypes = (ctypes.c_int,)
    _user32.GetAsyncKeyState.restype = ctypes.c_short
    _user32.MapVirtualKeyW.argtypes = (wintypes.UINT, wintypes.UINT)
    _user32.MapVirtualKeyW.restype = wintypes.UINT
    try:  # чіткі координати на екранах з масштабуванням 125–150%
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass

MOUSE_MOVE, LEFT_DOWN, LEFT_UP, RIGHT_DOWN, RIGHT_UP, WHEEL = 0x1, 0x2, 0x4, 0x8, 0x10, 0x800
VK_F7, VK_F8, VK_F9 = 0x76, 0x77, 0x78


def send_mouse(flags, dx=0, dy=0, data=0):
    inp = _INPUT(type=0)
    inp.u.mi = _MOUSEINPUT(int(dx), int(dy), data & 0xFFFFFFFF, flags, 0, 0)
    _user32.SendInput(1, ctypes.byref(inp), ctypes.sizeof(_INPUT))


KEY_UP, KEY_SCANCODE, KEY_EXTENDED = 0x2, 0x8, 0x1
VK = {"ctrl": 0x11, "alt": 0x12, "shift": 0x10, "enter": 0x0D, "space": 0x20, "left": 0x25,
      "c": 0x43, "v": 0x56, "z": 0x5A, "r": 0x52, "tab": 0x09, "esc": 0x1B}
EXTENDED_KEYS = {0x25, 0x26, 0x27, 0x28}


def press_keys(*names):
    """Натиснути комбінацію клавіш (скан-коди — їх «бачать» і ігри)."""
    if not IS_WIN:
        import pyautogui
        pyautogui.hotkey(*names)
        return
    vks = [VK[n] for n in names]

    def one(vk, up):
        scan = _user32.MapVirtualKeyW(vk, 0)
        flags = KEY_SCANCODE | (KEY_UP if up else 0) | (KEY_EXTENDED if vk in EXTENDED_KEYS else 0)
        inp = _INPUT(type=1)
        inp.u.ki = _KEYBDINPUT(0, scan, flags, 0, 0)
        _user32.SendInput(1, ctypes.byref(inp), ctypes.sizeof(_INPUT))
    for vk in vks:
        one(vk, False)
        time.sleep(0.02)
    for vk in reversed(vks):
        one(vk, True)


def mouse_now(kind, arg=None):
    """Дія миші без рушія (для голосових команд)."""
    if IS_WIN:
        flags = {"click": [LEFT_DOWN, LEFT_UP], "double": [LEFT_DOWN, LEFT_UP, LEFT_DOWN, LEFT_UP],
                 "right": [RIGHT_DOWN, RIGHT_UP], "down": [LEFT_DOWN], "up": [LEFT_UP]}.get(kind)
        if kind == "scroll":
            send_mouse(WHEEL, data=arg)
        for f in flags or []:
            send_mouse(f)
            time.sleep(0.01)
    else:
        import pyautogui
        {"click": pyautogui.click, "double": pyautogui.doubleClick, "right": pyautogui.rightClick,
         "down": pyautogui.mouseDown, "up": pyautogui.mouseUp}.get(kind, lambda: pyautogui.scroll(arg // 40))()


class HotKey:
    def __init__(self, vk):
        self.vk, self.was = vk, False

    def pressed(self):
        if not IS_WIN:
            return False
        down = bool(_user32.GetAsyncKeyState(self.vk) & 0x8000)
        hit = down and not self.was
        self.was = down
        return hit


def special_folder(csidl):
    buf = ctypes.create_unicode_buffer(520)
    ctypes.windll.shell32.SHGetFolderPathW(None, csidl, None, 0, buf)
    return buf.value


def pythonw_exe():
    d = os.path.dirname(sys.executable)
    for name in ("pythonw.exe", "python.exe"):
        p = os.path.join(d, name)
        if os.path.exists(p):
            return p
    return sys.executable


def python_console_exe():
    d = os.path.dirname(sys.executable)
    p = os.path.join(d, "python.exe")
    return p if os.path.exists(p) else sys.executable


def make_shortcut(lnk_path, target_exe=None):
    """Створює .lnk на програму (HandMouse.pyw або HandMouse.exe) з іконкою."""
    def q(s):
        return s.replace("'", "''")
    if target_exe or FROZEN:
        exe, args = target_exe or APP_FILE, ""
        workdir = os.path.dirname(exe)
    else:
        exe, args, workdir = pythonw_exe(), f'"{APP_FILE}"', APP_DIR
    ps = (f"$s=(New-Object -ComObject WScript.Shell).CreateShortcut('{q(lnk_path)}');"
          f"$s.TargetPath='{q(exe)}';$s.Arguments='{q(args)}';"
          f"$s.WorkingDirectory='{q(workdir)}';$s.IconLocation='{q(ICON_PATH)}';"
          f"$s.Description='{APP_NAME}';$s.Save()")
    try:
        subprocess.run(["powershell", "-NoProfile", "-NonInteractive", "-Command", ps],
                       creationflags=NO_WINDOW, capture_output=True, timeout=30)
    except Exception as e:
        log(f"shortcut powershell failed: {e}")
    if os.path.exists(lnk_path):
        return True
    # Запасний варіант: інтернет-ярлик на файл (працює без PowerShell)
    try:
        url_path = os.path.splitext(lnk_path)[0] + ".url"
        with open(url_path, "w", encoding="utf-8") as f:
            f.write("[InternetShortcut]\nURL=file:///" + (target_exe or APP_FILE).replace("\\", "/") +
                    f"\nIconFile={ICON_PATH}\nIconIndex=0\n")
        return True
    except OSError as e:
        log(f"shortcut .url failed: {e}")
        return False


def startup_link():
    return os.path.join(special_folder(0x07), APP_NAME + ".lnk")   # CSIDL_STARTUP


def remove_startup():
    for ext in (".lnk", ".url"):
        p = os.path.splitext(startup_link())[0] + ext
        if os.path.exists(p):
            os.remove(p)


def startup_enabled():
    base = os.path.splitext(startup_link())[0]
    return os.path.exists(base + ".lnk") or os.path.exists(base + ".url")


# ============================== Іконка (малюється кодом) ==============================
def build_icon():
    """Малює іконку 256x256 і зберігає PNG-байти + .ico. Повертає PNG-байти або None."""
    try:
        import cv2
        import numpy as np
    except ImportError:
        return None
    n = 256
    img = np.zeros((n, n, 4), np.uint8)
    cv2.circle(img, (128, 128), 120, (90, 50, 20, 255), -1, cv2.LINE_AA)       # темно-синє коло
    cv2.circle(img, (128, 128), 104, (255, 200, 0, 255), 8, cv2.LINE_AA)        # блакитне кільце
    arrow = np.array([[96, 62], [96, 186], [126, 158], [146, 202], [166, 193], [146, 150], [186, 150]], np.int32)
    cv2.fillPoly(img, [arrow], (255, 255, 255, 255), cv2.LINE_AA)
    ok, png = cv2.imencode(".png", img)
    if not ok:
        return None
    png = png.tobytes()
    try:
        ico = struct.pack("<HHH", 0, 1, 1) + struct.pack("<BBBBHHII", 0, 0, 0, 0, 1, 32, len(png), 22) + png
        with open(ICON_PATH, "wb") as f:
            f.write(ico)
    except OSError:
        pass
    return png


# ============================== Фільтр і жести ==============================
class OneEuro:
    """1€-фільтр (Casiez та ін.): прибирає тремтіння на повільних рухах, не гальмує швидкі."""

    def __init__(self, min_cutoff=1.0, beta=10.0, d_cutoff=1.0):
        self.min_cutoff, self.beta, self.d_cutoff = min_cutoff, beta, d_cutoff
        self.reset()

    def reset(self):
        self.x = self.dx = self.t = None

    @staticmethod
    def _a(cutoff, dt):
        return 1.0 / (1.0 + 1.0 / (2 * math.pi * cutoff * dt))

    def __call__(self, x, t):
        if self.t is None:
            self.x, self.dx, self.t = x, 0.0, t
            return x
        dt = max(t - self.t, 1e-3)
        dx = (x - self.x) / dt
        self.dx = self._a(self.d_cutoff, dt) * dx + (1 - self._a(self.d_cutoff, dt)) * self.dx
        cutoff = self.min_cutoff + self.beta * abs(self.dx)
        a = self._a(cutoff, dt)
        self.x, self.t = a * x + (1 - a) * self.x, t
        return self.x


def _d(a, b):
    return math.hypot(a.x - b.x, a.y - b.y)


class Gestures:
    """21 точка руки -> режим і дії миші. Має антидребезг щипка (кілька кадрів поспіль)."""

    def __init__(self, settings=None):
        self.s = settings if settings is not None else {}
        self.reset()

    def thresholds(self):
        """Пороги щипка: з калібрування (якщо є) або стандартні."""
        s = self.s
        on, off = s.get("pinch_on") or PINCH_ON, s.get("pinch_off") or PINCH_OFF
        mon, moff = s.get("mid_on") or on, s.get("mid_off") or off
        return on, off, mon, moff

    def measure(self, lm):
        """Сирі виміри руки (для жестів і калібрування)."""
        palm = _d(lm[WRIST], lm[MIDDLE_MCP]) or 1e-6
        self.p_idx = _d(lm[THUMB_TIP], lm[INDEX_TIP]) / palm
        self.p_mid = _d(lm[THUMB_TIP], lm[MIDDLE_TIP]) / palm
        self.ups = (self._up(lm, INDEX_TIP, INDEX_PIP), self._up(lm, MIDDLE_TIP, MIDDLE_PIP),
                    self._up(lm, RING_TIP, RING_PIP), self._up(lm, PINKY_TIP, PINKY_PIP))
        return palm

    def reset(self):
        self.left_since = None
        self.dragging = False
        self.right = False
        self.scroll_y = None
        self.cnt_l_on = self.cnt_l_off = self.cnt_r_on = self.cnt_r_off = 0
        self.p_idx = self.p_mid = 1.0

    @property
    def pinched(self):
        return (self.left_since is not None and not self.dragging) or self.right

    @staticmethod
    def _up(lm, tip, pip):
        return _d(lm[tip], lm[WRIST]) > _d(lm[pip], lm[WRIST]) * 1.08

    def release_all(self):
        out = [("up",)] if self.dragging else []
        self.reset()
        return out

    def _release_left(self, allow_click):
        out = []
        if self.dragging:
            out.append(("up",))
        elif self.left_since is not None and allow_click:
            out.append(("click",))
        self.left_since, self.dragging = None, False
        return out

    def update(self, lm, now):
        palm = self.measure(lm)
        p_idx, p_mid = self.p_idx, self.p_mid
        up_i, up_m, up_r, up_p = self.ups
        on, off, mon, moff = self.thresholds()
        acts = []

        if not (up_i or up_m or up_r or up_p) and p_idx > on and p_mid > mon:
            acts += self._release_left(False)
            self.right, self.scroll_y = False, None
            return "pause", acts

        if up_i and up_m and not up_r and not up_p and p_idx > off and p_mid > moff \
                and self.left_since is None:
            y = lm[MIDDLE_MCP].y
            if self.scroll_y is not None:
                dy = (self.scroll_y - y) / palm
                if abs(dy) > 0.02:
                    acts.append(("scroll", int(dy * SCROLL_SPEED)))
            self.scroll_y = y
            return "scroll", acts
        self.scroll_y = None

        # правий клік (великий + середній) з антидребезгом
        self.cnt_r_on = self.cnt_r_on + 1 if (p_mid < mon and p_idx > off) else 0
        self.cnt_r_off = self.cnt_r_off + 1 if p_mid > moff else 0
        if not self.right and self.cnt_r_on >= PINCH_FRAMES and self.left_since is None:
            self.right = True
            acts.append(("right",))
        elif self.right and self.cnt_r_off >= PINCH_FRAMES:
            self.right = False

        # лівий клік / перетягування (великий + вказівний) з антидребезгом
        self.cnt_l_on = self.cnt_l_on + 1 if p_idx < on else 0
        self.cnt_l_off = self.cnt_l_off + 1 if p_idx > off else 0
        if self.left_since is None:
            if self.cnt_l_on >= PINCH_FRAMES and not self.right:
                self.left_since = now
        elif self.cnt_l_off >= PINCH_FRAMES:
            acts += self._release_left(True)
        elif not self.dragging and now - self.left_since > HOLD_TO_DRAG:
            self.dragging = True
            acts.append(("down",))

        if self.dragging:
            return "drag", acts
        return ("pinch" if self.pinched else "move"), acts


def smoothstep(e0, e1, x):
    t = min(max((x - e0) / (e1 - e0), 0.0), 1.0)
    return t * t * (3 - 2 * t)


def joystick(v, dead):
    a = abs(v)
    if a < dead:
        return 0.0
    k = min((a - dead) / (1 - dead), 1.0) ** 1.6
    return k if v > 0 else -k


# ============================== Вивід миші ==============================
class Mouse:
    def __init__(self, pg):
        self.pg = pg
        self.sw, self.sh = pg.size()
        self.pos = None
        self.last_set = None
        self.acc = [0.0, 0.0]
        self.lock = threading.Lock()

    def _sync(self):
        x, y = self.pg.position()
        if self.pos is None or self.last_set is None or \
                abs(x - self.last_set[0]) > 3 or abs(y - self.last_set[1]) > 3:
            self.pos = [float(x), float(y)]   # користувач зрушив справжню мишу/тачпад

    def get(self):
        self._sync()
        return tuple(self.pos)

    def move_to(self, x, y):
        x = min(max(x, 0.0), self.sw - 1.0)
        y = min(max(y, 0.0), self.sh - 1.0)
        self.pos = [x, y]
        self.last_set = (int(round(x)), int(round(y)))
        self.pg.moveTo(*self.last_set)

    def move_by(self, dx, dy):
        self._sync()
        self.move_to(self.pos[0] + dx, self.pos[1] + dy)

    def raw_by(self, dx, dy):
        """Відносний рух для ігор (Roblox, шутери): ігри читають саме його."""
        with self.lock:
            self.acc[0] += dx
            self.acc[1] += dy
            mx, my = int(self.acc[0]), int(self.acc[1])
            self.acc[0] -= mx
            self.acc[1] -= my
        if mx or my:
            if IS_WIN:
                send_mouse(MOUSE_MOVE, mx, my)
            else:
                self.pg.moveRel(mx, my)
        return mx, my

    def action(self, kind, arg=None):
        if IS_WIN:
            if kind == "click":
                send_mouse(LEFT_DOWN); send_mouse(LEFT_UP)
            elif kind == "down":
                send_mouse(LEFT_DOWN)
            elif kind == "up":
                send_mouse(LEFT_UP)
            elif kind == "right":
                send_mouse(RIGHT_DOWN); send_mouse(RIGHT_UP)
            elif kind == "scroll":
                send_mouse(WHEEL, data=arg)
        else:
            {"click": self.pg.click, "down": self.pg.mouseDown, "up": self.pg.mouseUp,
             "right": self.pg.rightClick}.get(kind, lambda: self.pg.scroll(arg // 40))()


class MotionSender(threading.Thread):
    """Розподіляє рух прицілу дрібними кроками ~250 разів/с, як справжня миша.

    Камера дає 25–30 кадрів/с, а гра малює 60+. Якщо надсилати рух раз на кадр камери,
    поворот у грі йде «сходинками» — особливо помітно, коли персонаж біжить.
    """
    TICK = 0.004

    def __init__(self, mouse):
        super().__init__(daemon=True)
        self.mouse = mouse
        self.lock = threading.Lock()
        self.rem = [0.0, 0.0]       # ще не надісланий рух від точного прицілу
        self.step = [0.0, 0.0]      # скільки надсилати за один такт
        self.vel = [0.0, 0.0]       # безперервний поворот (джойстик), пікселів/с
        self.stopped = False
        self.sent_ticks = 0

    def push(self, dx, dy, span):
        """Додати рух, рівномірно розподіливши його на span секунд (≈ інтервал між кадрами)."""
        with self.lock:
            self.rem[0] += dx
            self.rem[1] += dy
            n = max(1.0, span / self.TICK)
            self.step = [abs(self.rem[0]) / n, abs(self.rem[1]) / n]

    def set_velocity(self, vx, vy):
        with self.lock:
            self.vel = [vx, vy]

    def clear(self):
        """Зупинити все; повертає рух, який так і не надіслали."""
        with self.lock:
            left = tuple(self.rem)
            self.rem, self.step, self.vel = [0.0, 0.0], [0.0, 0.0], [0.0, 0.0]
        return left

    def run(self):
        nxt = time.perf_counter()
        while not self.stopped:
            with self.lock:
                out = []
                for i in (0, 1):
                    r = self.rem[i]
                    d = math.copysign(min(self.step[i], abs(r)), r) if r else 0.0
                    self.rem[i] -= d
                    out.append(d + self.vel[i] * self.TICK)
                idle = not (self.rem[0] or self.rem[1] or self.vel[0] or self.vel[1])
            if out[0] or out[1]:
                self.mouse.raw_by(out[0], out[1])
                self.sent_ticks += 1
            if idle:
                time.sleep(0.01)
                nxt = time.perf_counter()
                continue
            nxt += self.TICK
            delay = nxt - time.perf_counter()
            if delay > 0:
                time.sleep(delay)
            else:
                nxt = time.perf_counter()


# ============================== Камера в окремому потоці ==============================
def open_camera(cv2, index, fast):
    cap = cv2.VideoCapture(index, cv2.CAP_DSHOW if IS_WIN else cv2.CAP_ANY)
    if not cap.isOpened():
        return cap
    # MJPG: більшість веб-камер дають 30 кадр/с лише в цьому форматі (у «сирому» — 5–15)
    cap.set(cv2.CAP_PROP_FOURCC, cv2.VideoWriter_fourcc(*"MJPG"))
    cap.set(cv2.CAP_PROP_FRAME_WIDTH, 640)
    cap.set(cv2.CAP_PROP_FRAME_HEIGHT, 480)
    cap.set(cv2.CAP_PROP_FPS, 60 if fast else 30)
    cap.set(cv2.CAP_PROP_BUFFERSIZE, 1)
    if fast:   # коротка витримка: камера не «гальмує» в темряві, але картинка темніша
        cap.set(cv2.CAP_PROP_AUTO_EXPOSURE, 0.25)
        cap.set(cv2.CAP_PROP_EXPOSURE, -6)
    else:
        cap.set(cv2.CAP_PROP_AUTO_EXPOSURE, 0.75)
    return cap


class CameraReader(threading.Thread):
    """Безперервно читає камеру; рушій завжди бере найсвіжіший кадр і не чекає на камеру."""

    def __init__(self, cap):
        super().__init__(daemon=True)
        self.cap = cap
        self.frame, self.n, self.fps = None, 0, 0.0
        self.cond = threading.Condition()
        self.stopped = False
        self.want_settings = False

    def run(self):
        t, k = time.monotonic(), 0
        while not self.stopped:
            if self.want_settings:          # вікно драйвера камери (тільки Windows)
                self.want_settings = False
                try:
                    self.cap.set(37, 1)     # CAP_PROP_SETTINGS
                except Exception:
                    pass
            ok, f = self.cap.read()
            if not ok:
                time.sleep(0.01)
                continue
            with self.cond:
                self.frame, self.n = f, self.n + 1
                self.cond.notify_all()
            k += 1
            now = time.monotonic()
            if now - t >= 1.0:
                self.fps, t, k = k / (now - t), now, 0

    def latest(self, last_n, timeout=0.5):
        with self.cond:
            if self.n == last_n:
                self.cond.wait(timeout)
            return self.n, self.frame


# ============================== Рушій (окремий потік) ==============================
class Engine(threading.Thread):
    def __init__(self, settings, source=None, pg=None):
        super().__init__(daemon=True)
        self.s = settings
        self.source = source            # None = камера з налаштувань; рядок = відеофайл (для тесту)
        self.pg = pg
        self.stop_event = threading.Event()
        self.paused = False
        self.status = "Запуск…"
        self.mode = ""
        self.preview = None             # PNG-байти для вікна
        self.error = None
        self.fps = 0.0
        self.cam_fps = 0.0
        self.proc_ms = 0.0
        self.reader = None
        self.stats = {}
        self.hand_pt = None          # згладжена точка долоні (0..1) для малювання
        self.want_center = False     # кнопка «Центр тут» у вікні
        self.calibrating = False     # майстер калібрування: лише вимірюємо, мишу не чіпаємо
        self.raw = None
        self.turning = False

    def stop(self):
        self.stop_event.set()

    def run(self):
        try:
            self._loop()
        except Exception:
            self.error = traceback.format_exc()
            log(self.error)
        finally:
            if self.error is None:
                self.status = "Зупинено"

    def _ensure_model(self):
        old = os.path.join(APP_DIR, "hand_landmarker.task")   # модель від попередньої версії
        if not os.path.exists(MODEL_PATH) and os.path.exists(old):
            import shutil
            shutil.copyfile(old, MODEL_PATH)
        if not os.path.exists(MODEL_PATH):
            self.status = "Завантажую модель руки (~8 МБ)…"
            tmp = MODEL_PATH + ".part"
            urllib.request.urlretrieve(MODEL_URL, tmp)
            os.replace(tmp, MODEL_PATH)

    def _loop(self):
        import cv2
        import mediapipe as mp
        from mediapipe.tasks import python as mp_python
        from mediapipe.tasks.python import vision
        pg = self.pg
        if pg is None:
            import pyautogui as pg
            pg.PAUSE = 0
            pg.FAILSAFE = False
        mouse = Mouse(pg)
        sender = MotionSender(mouse)
        sender.start()
        if IS_WIN:
            try:   # точніший системний таймер для рівних кроків миші
                ctypes.windll.winmm.timeBeginPeriod(1)
            except Exception:
                pass
        self._ensure_model()

        self.status = "Відкриваю камеру…"
        landmarker = vision.HandLandmarker.create_from_options(vision.HandLandmarkerOptions(
            base_options=mp_python.BaseOptions(model_asset_path=MODEL_PATH),
            running_mode=vision.RunningMode.VIDEO, num_hands=1,
            min_hand_detection_confidence=0.6, min_hand_presence_confidence=0.6,
            min_tracking_confidence=0.5))
        if self.source is not None:
            cap = cv2.VideoCapture(self.source)
        else:
            cap = open_camera(cv2, int(self.s["camera"]), bool(self.s["fast_camera"]))
        if not cap.isOpened():
            raise RuntimeError(f"Не вдалося відкрити камеру №{self.s['camera']}. "
                               "Спробуйте інший номер камери або закрийте програми, які її використовують.")

        g = Gestures(self.s)
        fx, fy = OneEuro(), OneEuro()
        prev = None
        was_pinched = False
        approach = None          # (час, позиція курсора, сума ігрових рухів) коли пальці почали зводитися
        game_since = [0.0, 0.0]
        hk_game, hk_pause, hk_center = HotKey(VK_F8), HotKey(VK_F9), HotKey(VK_F7)
        rate = [0.0, 0.0]            # поточна швидкість повороту (плавно розганяється/гальмує)
        raw_prev, glitch = None, 0
        t0 = time.monotonic()
        last_ts, frame_i, fps_t, fps_n = -1, 0, time.monotonic(), 0
        stats = self.stats
        reader, last_n, last_proc = None, 0, 0.0
        frame_dt = 1 / 30            # згладжений інтервал між обробленими кадрами
        if self.source is None:
            reader = self.reader = CameraReader(cap)
            reader.start()

        try:
            while not self.stop_event.is_set():
                if reader is not None:
                    n, frame = reader.latest(last_n)
                    self.cam_fps = reader.fps
                    if n == last_n or frame is None:
                        continue
                    last_n = n
                    # У грі не більше 30 обробок/с: менше навантаження на процесор — гра не «гальмує»
                    if self.s["game_mode"] and time.perf_counter() - last_proc < 1 / 31:
                        continue
                    last_proc = time.perf_counter()
                else:
                    ok, frame = cap.read()
                    if not ok:
                        break
                t_proc = time.perf_counter()
                if self.source is None:
                    frame = cv2.flip(frame, 1)
                now = time.monotonic() if self.source is None else frame_i / 30.0
                frame_i += 1
                ts = int((now - (t0 if self.source is None else 0)) * 1000)
                ts = max(ts, last_ts + 1)
                last_ts = ts

                if hk_pause.pressed():
                    self.paused = not self.paused
                if hk_game.pressed():
                    for a in g.release_all():
                        mouse.action(a[0])
                    sender.clear()
                    self.s["game_mode"] = not self.s["game_mode"]

                if hk_center.pressed():
                    self.want_center = True
                game = self.s["game_mode"]
                sm = float(self.s["smoothing"])
                fx.min_cutoff = fy.min_cutoff = 3.0 * (0.1 ** sm)   # 3 Гц … 0.3 Гц

                lm = None
                if not self.paused:      # на паузі не витрачаємо процесор на розпізнавання
                    res = landmarker.detect_for_video(
                        mp.Image(image_format=mp.ImageFormat.SRGB, data=cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)), ts)
                    lm = res.hand_landmarks[0] if res.hand_landmarks else None
                mode = "немає руки"
                if lm is not None and self.calibrating:
                    for a in g.release_all():
                        mouse.action(a[0])
                    sender.clear()
                    g.measure(lm)
                    self.raw = {"p_idx": g.p_idx, "p_mid": g.p_mid, "ups": g.ups, "t": now,
                                "u": sum(lm[i].x for i in PALM) / len(PALM),
                                "v": sum(lm[i].y for i in PALM) / len(PALM)}
                    prev = None
                    mode = "калібрування"
                elif lm is not None and not self.paused:
                    mode, acts = g.update(lm, now)
                    u = sum(lm[i].x for i in PALM) / len(PALM)
                    v = sum(lm[i].y for i in PALM) / len(PALM)
                    # Стрибок понад 12% кадру за 1/30 с — це збій розпізнавання (перескочило на іншу
                    # руку тощо), а не справжній рух. Такий кадр ігноруємо; якщо рука справді там
                    # (3 кадри поспіль) — приймаємо нове місце без ривка прицілу.
                    if raw_prev is not None:
                        lim = JUMP_LIMIT * max(now - raw_prev[2], 1 / 60) * 30
                        if math.hypot(u - raw_prev[0], v - raw_prev[1]) > lim:
                            glitch += 1
                            stats["jump"] = stats.get("jump", 0) + 1
                            if glitch < 3:
                                u, v = raw_prev[0], raw_prev[1]
                            else:
                                fx.reset(); fy.reset()
                                prev, glitch = None, 0
                        else:
                            glitch = 0
                    raw_prev = (u, v, now)
                    fu, fv = fx(u, now), fy(v, now)
                    du, dv, dt = 0.0, 0.0, 1 / 30
                    if prev is not None:
                        du, dv, dt = fu - prev[0], fv - prev[1], max(now - prev[2], 1e-3)
                    prev = (fu, fv, now)
                    self.hand_pt = (fu, fv)
                    if self.want_center:      # F7 / кнопка: центр джойстика там, де зараз рука
                        self.want_center = False
                        self.s["game_cx"], self.s["game_cy"] = round(fu, 3), round(fv, 3)
                        rate = [0.0, 0.0]

                    freeze = bool(self.s["freeze_click"])
                    pinched = g.pinched
                    # 1) Пальці почали зводитися — запам'ятовуємо, де був курсор
                    if min(g.p_idx, g.p_mid) < (self.s.get("freeze_ratio") or FREEZE_RATIO):
                        if approach is None:
                            approach = (now, None if game else mouse.get())
                            game_since = [0.0, 0.0]
                    else:
                        approach = None
                    # 2) Щойно стався щипок — повертаємо курсор туди, де він був до зведення пальців
                    if freeze and pinched and not was_pinched and approach and now - approach[0] < ROLLBACK_WINDOW:
                        if game:
                            left = sender.clear()      # ненадіслане просто скасовуємо
                            mouse.raw_by(-(game_since[0] - left[0]), -(game_since[1] - left[1]))
                        elif approach[1] is not None:
                            mouse.move_to(*approach[1])
                        stats["rollback"] = stats.get("rollback", 0) + 1
                    was_pinched = pinched
                    frozen = freeze and pinched
                    active = mode in ("move", "pinch", "drag")

                    if game:
                        mx = my = 0.0
                        if active and not frozen:
                            # точне доведення: рух руки = рух прицілу; повільно — точніше, швидко — далі
                            speed = math.hypot(du, dv) / dt
                            aim = GAME_AIM_PX * float(self.s["game_aim"]) * \
                                (0.5 + 1.5 * smoothstep(V_SLOW, V_FAST, speed))
                            mx, my = du * aim, dv * aim
                            game_since[0] += mx
                            game_since[1] += my
                        target = [0.0, 0.0]
                        if active and self.s["game_style"] == "hybrid":
                            # джойстик: рука далеко від центру = безперервний поворот
                            half = 0.5 - float(self.s["zone"])
                            dz = float(self.s["game_deadzone"])
                            turn = float(self.s["game_turn"]) * 30      # пікселів миші за секунду
                            target[0] = joystick((fu - float(self.s["game_cx"])) / half, dz) * turn
                            if self.s["game_vertical"]:
                                target[1] = joystick((fv - float(self.s["game_cy"])) / half, dz) * turn * 0.6
                        # плавний розгін (~0.15 с) і швидке гальмування (~0.06 с)
                        for i in (0, 1):
                            k = dt / (0.15 if abs(target[i]) > abs(rate[i]) else 0.06)
                            rate[i] += (target[i] - rate[i]) * min(k, 1.0)
                        self.turning = abs(rate[0]) + abs(rate[1]) > 1
                        frame_dt = 0.8 * frame_dt + 0.2 * min(dt, 0.1)
                        sender.push(mx, my, frame_dt)      # приціл — рівними кроками до наступного кадру
                        sender.set_velocity(rate[0], rate[1])   # поворот — безперервно
                    elif active and not frozen:
                        sender.clear()
                        if self.s["desktop_style"] == "absolute":
                            z = float(self.s["zone"])
                            ax = min(max((fu - z) / (1 - 2 * z), 0.0), 1.0) * (mouse.sw - 1)
                            ay = min(max((fv - z) / (1 - 2 * z), 0.0), 1.0) * (mouse.sh - 1)
                            mouse.move_to(ax, ay)
                        else:                              # «як миша» з адаптивним підсиленням
                            speed = math.hypot(du, dv) / dt
                            gain = mouse.sw * float(self.s["sensitivity"]) * \
                                (G_MIN + (G_MAX - G_MIN) * smoothstep(V_SLOW, V_FAST, speed))
                            mouse.move_by(du * gain, dv * gain)

                    for a in acts:
                        mouse.action(a[0], a[1] if len(a) > 1 else None)
                        stats[a[0]] = stats.get(a[0], 0) + 1
                    if frozen:
                        mode = "клік (курсор зафіксовано)" if mode == "pinch" else mode
                else:
                    for a in g.release_all():
                        mouse.action(a[0])
                    fx.reset(); fy.reset()
                    prev, approach, was_pinched = None, None, False
                    rate = [0.0, 0.0]          # руки немає — камера одразу зупиняється
                    sender.clear()
                    self.raw = None
                    raw_prev, glitch = None, 0
                    self.hand_pt, self.turning = None, False
                    if self.paused:
                        mode = "ПАУЗА (F9)"
                stats["frames"] = stats.get("frames", 0) + 1
                if lm is not None:
                    stats["hand"] = stats.get("hand", 0) + 1

                self.mode = {"move": "рух", "pinch": "щипок", "drag": "перетягування",
                             "scroll": "прокрутка", "pause": "кулак — пауза"}.get(mode, mode)
                fps_n += 1
                if time.monotonic() - fps_t >= 1.0:
                    self.fps = fps_n / (time.monotonic() - fps_t)
                    fps_t, fps_n = time.monotonic(), 0
                self.status = "Працює" + (" · ігровий режим" if game else "")

                # перегляд ~15 разів/с і лише коли вікно вже показало попередній кадр
                want_view = self.s["show_camera"] or (game and self.s["game_overlay"])
                if want_view and frame_i % 2 == 0 and self.preview is None:
                    self.preview = self._render(cv2, frame, lm, game, mode)
                self.proc_ms = 0.8 * self.proc_ms + 0.2 * (time.perf_counter() - t_proc) * 1000
        finally:
            for a in g.release_all():
                try:
                    mouse.action(a[0])
                except Exception:
                    pass
            sender.stopped = True
            sender.clear()
            if IS_WIN:
                try:
                    ctypes.windll.winmm.timeEndPeriod(1)
                except Exception:
                    pass
            if reader is not None:
                reader.stopped = True
                reader.join(timeout=1)
            cap.release()
            landmarker.close()

    def _render(self, cv2, frame, lm, game, mode):
        h, w = frame.shape[:2]
        if lm is not None:
            pts = [(int(p.x * w), int(p.y * h)) for p in lm]
            for a, b in HAND_CONNECTIONS:
                cv2.line(frame, pts[a], pts[b], (255, 200, 0), 2, cv2.LINE_AA)
            for p in pts:
                cv2.circle(frame, p, 3, (255, 255, 255), -1, cv2.LINE_AA)
        z = float(self.s["zone"])
        if (game and self.s["game_style"] == "hybrid") or (not game and self.s["desktop_style"] == "absolute"):
            cv2.rectangle(frame, (int(w * z), int(h * z)), (int(w * (1 - z)), int(h * (1 - z))), (0, 255, 0), 2)
        if game and self.s["game_style"] == "hybrid":
            # центр джойстика, мертва зона і де зараз рука
            cx, cy = int(float(self.s["game_cx"]) * w), int(float(self.s["game_cy"]) * h)
            dz = float(self.s["game_deadzone"])
            rx, ry = int(w * (0.5 - z) * dz), int(h * (0.5 - z) * dz)
            if self.s["game_vertical"]:
                cv2.rectangle(frame, (cx - rx, cy - ry), (cx + rx, cy + ry), (0, 0, 255), 2)
            else:
                cv2.line(frame, (cx - rx, 0), (cx - rx, h), (0, 0, 255), 2)
                cv2.line(frame, (cx + rx, 0), (cx + rx, h), (0, 0, 255), 2)
            cv2.drawMarker(frame, (cx, cy), (0, 0, 255), cv2.MARKER_CROSS, 18, 2)
            if self.hand_pt is not None:
                hx, hy = int(self.hand_pt[0] * w), int(self.hand_pt[1] * h)
                col = (0, 165, 255) if self.turning else (0, 220, 0)
                cv2.line(frame, (cx, cy), (hx, hy), col, 2, cv2.LINE_AA)
                cv2.circle(frame, (hx, hy), 9, col, -1, cv2.LINE_AA)
        small = cv2.resize(frame, (320, 240), interpolation=cv2.INTER_AREA)
        ok, img = cv2.imencode(".ppm", small)     # PPM без стиснення — найшвидше для Tk
        return img.tobytes() if ok else None


# ============================== Голосові команди ==============================
VOICE_MODELS = {   # назва: (адреса, папка, розмір МБ)
    "small": ("https://alphacephei.com/vosk/models/vosk-model-small-uk-v3-small.zip",
              os.path.join(DATA_DIR, "vosk-uk-small"), 133),
    "nano": ("https://alphacephei.com/vosk/models/vosk-model-small-uk-v3-nano.zip",
             os.path.join(DATA_DIR, "vosk-uk"), 73),
}
VOICE_PACKAGES = {"vosk": "vosk", "sounddevice": "sounddevice"}

# (дія, опис, варіанти фраз). Розпізнаються лише ці фрази — звичайна розмова не спрацює.
VOICE_COMMANDS = [   # лише 5 команд — так розпізнавання найнадійніше
    ("click", "один клік лівою кнопкою", ["клік", "клац"]),
    ("jump", "стрибок (пробіл)", ["стрибок", "стрибай"]),
    ("fire", "стріляти безперервно — до «стоп»", ["стріляй", "вогонь"]),
    ("hold", "затиснути ліву кнопку — до «стоп»", ["задерж", "затримай", "тримай"]),
    ("stop", "зупинити стрільбу / відпустити кнопку", ["стоп"]),
]


def voice_missing():
    import importlib.util
    return [pip for mod, pip in VOICE_PACKAGES.items() if importlib.util.find_spec(mod) is None]


def ensure_voice_model(progress, which="small"):
    VOICE_MODEL_URL, VOICE_MODEL_DIR, size = VOICE_MODELS.get(which, VOICE_MODELS["small"])
    if os.path.exists(os.path.join(VOICE_MODEL_DIR, "am")) or os.path.exists(os.path.join(VOICE_MODEL_DIR, "conf")):
        return VOICE_MODEL_DIR
    import shutil
    import zipfile
    tmp_zip = VOICE_MODEL_DIR + ".zip.part"

    def hook(blocks, bs, total):
        if total > 0:
            progress(f"Завантажую голосову модель ({size} МБ)… {min(100, blocks * bs * 100 // total)}%")
    urllib.request.urlretrieve(VOICE_MODEL_URL, tmp_zip, hook)
    progress("Розпаковую голосову модель…")
    tmp_dir = VOICE_MODEL_DIR + ".tmp"
    shutil.rmtree(tmp_dir, ignore_errors=True)
    with zipfile.ZipFile(tmp_zip) as z:
        z.extractall(tmp_dir)
    inner = [os.path.join(tmp_dir, d) for d in os.listdir(tmp_dir)]
    src = inner[0] if len(inner) == 1 and os.path.isdir(inner[0]) else tmp_dir
    shutil.rmtree(VOICE_MODEL_DIR, ignore_errors=True)
    shutil.move(src, VOICE_MODEL_DIR)
    shutil.rmtree(tmp_dir, ignore_errors=True)
    os.remove(tmp_zip)
    return VOICE_MODEL_DIR


def match_command(text, phrases):
    """Текст від розпізнавача -> дія. Спочатку точний збіг, потім найдовша фраза всередині тексту."""
    text = " ".join(w for w in text.split() if w != "[unk]")
    if not text:
        return None, ""
    if text in phrases:
        return phrases[text], text
    best = None
    padded = f" {text} "
    for ph, act in phrases.items():
        if f" {ph} " in padded and (best is None or len(ph) > len(best[0])):
            best = (ph, act)
    return (best[1], text) if best else (None, text)


# ---------- «Мій голос»: розпізнавання за власними зразками (MFCC + DTW) ----------
# Не залежить від мови й акценту: користувач сам записує кожну команду 3 рази.
VOICE_SAMPLES = os.path.join(DATA_DIR, "voice_samples.npz")
VOICE_SAMPLES_META = os.path.join(DATA_DIR, "voice_samples.json")
VOICE_LABEL = {act: variants[0] for act, _d, variants in VOICE_COMMANDS}
VOICE_DESC = {act: d for act, d, _v in VOICE_COMMANDS}

try:
    import numpy as _np
except ImportError:      # numpy приходить разом з opencv; без нього «Мій голос» недоступний
    _np = None


VSR = 16000
FRAME, HOP, NFFT = 400, 160, 512


def _mel_filters(n=26, fmin=80, fmax=7600):
    def hz2mel(h): return 2595 * _np.log10(1 + h / 700)
    def mel2hz(m): return 700 * (10 ** (m / 2595) - 1)
    mels = _np.linspace(hz2mel(fmin), hz2mel(fmax), n + 2)
    bins = _np.floor((NFFT + 1) * mel2hz(mels) / VSR).astype(int)
    fb = _np.zeros((n, NFFT // 2 + 1))
    for i in range(1, n + 1):
        l, c, r = bins[i - 1], bins[i], bins[i + 1]
        for k in range(l, c):
            fb[i - 1, k] = (k - l) / max(c - l, 1)
        for k in range(c, r):
            fb[i - 1, k] = (r - k) / max(r - c, 1)
    return fb


_FB = _mel_filters()
_N = 26
_DCT = _np.array([[math.cos(math.pi * k * (2 * n + 1) / (2 * _N)) for n in range(_N)] for k in range(13)])
_WIN = _np.hamming(FRAME)


VOICE_TRIM = False    # обрізання країв слова (тести показали: без нього точніше)
VOICE_TRIM_DB = 5     # що тихіше за шум + 5 дБ на краях слова — обрізаємо
VOICE_FLOOR = 1e-2   # «підлога» спектра: на 20 дБ нижче найгучнішого (пригашує фоновий шум)


def voice_features(x):
    """int16/float mono 16 kHz -> (frames, 26) MFCC+delta, per-utterance CMVN."""
    x = _np.asarray(x, dtype=_np.float64)
    x = _np.append(x[0], x[1:] - 0.97 * x[:-1])
    if len(x) < FRAME:
        x = _np.pad(x, (0, FRAME - len(x)))
    n = 1 + (len(x) - FRAME) // HOP
    idx = _np.arange(FRAME)[None, :] + HOP * _np.arange(n)[:, None]
    frames = x[idx] * _WIN
    spec = _np.abs(_np.fft.rfft(frames, NFFT)) ** 2
    melp = spec @ _FB.T
    # «підлога» на 30 дБ нижче найгучнішого: тихі частини (де живе шум) вирівнюються,
    # тож зразок, записаний у тиші, і команда в шумі стають схожішими
    floor = _np.percentile(melp, 99) * VOICE_FLOOR
    mel = _np.log(_np.maximum(melp, floor) + 1e-6)
    c = mel @ _DCT.T                                      # (n, 13)
    d = _np.zeros_like(c)
    d[1:-1] = (c[2:] - c[:-2]) / 2
    f = _np.hstack([c, d])
    f = (f - f.mean(0)) / (f.std(0) + 1e-6)
    return f.astype(_np.float32)


def dtw_dist(a, b):
    """DTW з обмеженням нахилу (кроки (1,1), (1,2), (2,1) з проміжними точками).
    Векторизовано по рядках. Повертає відстань, нормовану на довжину шляху."""
    n, m = len(a), len(b)
    if n < 2 or m < 2 or n > 2 * m + 2 or m > 2 * n + 2:
        return float("inf")
    cost = _np.sqrt(((a[:, None, :] - b[None, :, :]) ** 2).sum(-1))
    INF = 1e18
    D = _np.full((n, m), INF)
    D[0, 0] = cost[0, 0]
    for i in range(1, n):
        best = _np.full(m, INF)
        best[1:] = D[i - 1, :-1]                                   # (i-1, j-1)
        b2 = _np.full(m, INF)
        b2[2:] = D[i - 1, :-2] + cost[i, 1:-1]                     # (i-1, j-2) через (i, j-1)
        best = _np.minimum(best, b2)
        if i >= 2:
            b3 = _np.full(m, INF)
            b3[1:] = D[i - 2, :-1] + cost[i - 1, 1:]               # (i-2, j-1) через (i-1, j)
            best = _np.minimum(best, b3)
        D[i] = cost[i] + best
    return float(D[-1, -1] / (n + m))


class VoiceSegmenter:
    """Енергетичний VAD: ріже потік на окремі слова/фрази."""
    FR = 320  # 20 мс

    def __init__(self, on_utt, min_len=0.18, max_len=2.0):
        self.on_utt = on_utt
        self.buf = _np.zeros(0, dtype=_np.float32)
        self.noise = -50.0
        self.hist = []
        self.speech = []
        self.active = False
        self.loud = 0
        self.quiet = 0
        self.pre = []
        self.min_len, self.max_len = min_len, max_len
        self.level = -90.0

    def push(self, x):
        self.buf = _np.concatenate([self.buf, _np.asarray(x, dtype=_np.float32)])
        while len(self.buf) >= self.FR:
            fr, self.buf = self.buf[:self.FR], self.buf[self.FR:]
            self._frame(fr)

    def _frame(self, fr):
        db = 20 * math.log10(math.sqrt(float(_np.mean(fr * fr))) / 32768 + 1e-9)
        self.level = db
        self.smooth = db if not hasattr(self, "smooth") else 0.6 * self.smooth + 0.4 * db
        self.hist.append(db)
        if len(self.hist) > 150:                           # 3 с історії
            self.hist.pop(0)
        if not self.active:
            self.noise = float(_np.percentile(self.hist, 20))
        on, off = self.noise + 10, self.noise + 5
        if not self.active:
            self.pre = (self.pre + [fr])[-6:]              # 120 мс до початку слова
            self.loud = self.loud + 1 if db > on else 0
            if self.loud >= 3:
                self.active, self.quiet = True, 0
                self.speech = list(self.pre)
        else:
            self.speech.append(fr)
            # тиша накопичується; короткі сплески шуму лише трохи її зменшують
            self.quiet = self.quiet + 1 if self.smooth < off else max(0, self.quiet - 2)
            dur = len(self.speech) * self.FR / VSR
            if self.quiet >= 14 or dur > self.max_len + 0.5:   # ~280 мс тиші — кінець
                seg = _np.concatenate(self.speech[:len(self.speech) - max(0, self.quiet - 4)])
                self.active, self.loud, self.pre = False, 0, []
                if VOICE_TRIM:
                    seg = self._trim(seg)
                d = len(seg) / VSR
                if self.min_len <= d <= self.max_len:
                    self.on_utt(seg)

    def _trim(self, seg):
        """Обрізати тишу/шум на краях: лишити саме слово + 40 мс запасу."""
        hop = 160
        n = len(seg) // hop
        if n < 3:
            return seg
        e = _np.array([20 * math.log10(math.sqrt(float(_np.mean(seg[i * hop:(i + 1) * hop] ** 2))) / 32768 + 1e-9)
                      for i in range(n)])
        loud = _np.nonzero(e > max(self.noise + VOICE_TRIM_DB, e.max() - 40))[0]
        if not len(loud):
            return seg
        a, b = max(0, loud[0] - 6), min(n, loud[-1] + 8)
        return seg[a * hop:b * hop]


class VoiceTemplates:
    def __init__(self):
        self.data = {}   # дія -> [features]

    def add(self, act, feat):
        self.data.setdefault(act, []).append(feat)

    def count(self, act):
        return len(self.data.get(act, []))

    def scores(self, feat, acts=None):
        out = {}
        for act, lst in self.data.items():
            if acts is not None and act not in acts:
                continue
            ds = sorted(dtw_dist(feat, t) for t in lst)
            ds = [d for d in ds if math.isfinite(d)] or [float("inf")]
            out[act] = ds[0] if len(ds) == 1 else (ds[0] + ds[1]) / 2
        return out

    def threshold(self):
        """Поріг «це взагалі команда?» з розкиду власних зразків (leave-one-out)."""
        within = []
        for act, lst in self.data.items():
            for i, t in enumerate(lst):
                others = [dtw_dist(t, u) for j, u in enumerate(lst) if j != i]
                if others and math.isfinite(min(others)):
                    within.append(min(others))
        return float(_np.percentile(within, 90)) if within else 1.0

    def classify(self, feat, strict=0.5, acts=None, thr=None, noise_delta=0.0):
        """-> (дія або None, відстані, впевненість 0..1).

        Головна ознака — відрив найкращої команди від другої: для справжньої команди він
        великий, для стороннього слова майже нульовий. Допустима відстань росте з шумом
        (noise_delta — на скільки дБ зараз шумніше, ніж під час запису зразків).
        """
        sc = self.scores(feat, acts)
        if not sc:
            return None, sc, 0.0
        ranked = sorted(sc.items(), key=lambda kv: kv[1])
        best, d1 = ranked[0]
        d2 = ranked[1][1] if len(ranked) > 1 else d1 * 3
        if not math.isfinite(d1):
            return None, sc, 0.0
        thr = thr if thr is not None else self.threshold()
        margin = 1.0 if not math.isfinite(d2) else (d2 - d1) / max(d2, 1e-9)
        # підібрано на тестах із реальним шумом: 0 хибних спрацювань при ~80–90% розпізнаних команд
        cap = (1.5 + 0.15 * max(0.0, noise_delta)) * (1.15 - 0.3 * strict)  # strict .5 -> ×1.0
        need = 0.05 + 0.25 * strict                                          # strict .5 -> 0.175
        ok = d1 <= thr * cap and margin >= need
        conf = max(0.0, min(1.0, margin / (2 * need))) * (1.0 if d1 <= thr * cap else 0.5)
        return (best if ok else None), sc, conf


def load_voice_samples():
    """-> ({дія: [аудіо int16]}, рівень шуму під час запису дБ)."""
    out, noise = {}, -50.0
    try:
        with open(VOICE_SAMPLES_META, encoding="utf-8") as f:
            meta = json.load(f)
        noise = float(meta.get("noise", -50.0))
        with _np.load(VOICE_SAMPLES) as z:
            for key in z.files:
                act = key.rsplit("__", 1)[0]
                out.setdefault(act, []).append(z[key])
    except (OSError, ValueError, KeyError):
        pass
    return out, noise


def save_voice_samples(samples, noise):
    arrays = {f"{act}__{i}": _np.asarray(a, dtype=_np.int16) for act, lst in samples.items() for i, a in enumerate(lst)}
    _np.savez_compressed(VOICE_SAMPLES, **arrays)
    with open(VOICE_SAMPLES_META, "w", encoding="utf-8") as f:
        json.dump({"noise": noise}, f)


def build_templates(samples):
    t = VoiceTemplates()
    for act, lst in samples.items():
        for a in lst:
            t.add(act, voice_features(a))
    return t


def find_phrase(text, phrases):
    """Як match_command, але повертає ще й саму фразу-команду."""
    text = " ".join(w for w in text.split() if w != "[unk]")
    if text in phrases:
        return phrases[text], text
    best = None
    padded = f" {text} "
    for ph in phrases:
        if f" {ph} " in padded and (best is None or len(ph) > len(best)):
            best = ph
    return (phrases[best], best) if best else (None, None)


def ambiguous_phrases(phrases):
    """Фрази, з яких починається довша команда («правий» -> «правий клік»): для них чекаємо кінця."""
    return {a for a in phrases for b in phrases if b != a and b.startswith(a + " ")}


def mic_devices():
    """Список мікрофонів: [(індекс, назва)]."""
    import sounddevice as sd
    out, seen = [], set()
    try:
        default_api = sd.query_devices(kind="input")["hostapi"]
    except Exception:
        default_api = None
    for i, d in enumerate(sd.query_devices()):
        if d["max_input_channels"] > 0 and (default_api is None or d["hostapi"] == default_api):
            if d["name"] not in seen:
                seen.add(d["name"])
                out.append((i, d["name"]))
    return out


class VoiceListener(threading.Thread):
    """Слухає мікрофон офлайн (Vosk) і викликає on_command(дія).

    Команда спрацьовує, щойно її розпізнано в проміжному результаті — без очікування тиші
    (у грі чи з музикою фоном тиші може не бути взагалі).
    """
    COOLDOWN = 0.7   # сек: та сама команда не повториться двічі від одного слова

    def __init__(self, on_command, settings=None):
        super().__init__(daemon=True)
        self.on_command = on_command
        self.s = settings if settings is not None else {}
        self.status = "Запуск…"
        self.heard = ""
        self.error = None
        self.stopped = False
        self.phrases = {}
        self.levels = [0.0] * 60        # «хвиля» гучності для вікна (0..1)
        self.history = []               # [(час, текст, дія або None)]
        self.devices = []
        self.fired_at = 0.0
        self._last = (None, 0.0)
        self.partial = ""               # що модель чує прямо зараз
        self.recorder = None            # навчання: функція, що отримає наступне сказане слово
        self.seg = None
        self.templates = None
        self.train_noise = -50.0
        self.thr = 1.0
        self.engine_kind = self.s.get("voice_engine") or "mine"
        self.fallback = False

    def _fire(self, act, phrase):
        now = time.monotonic()
        if self._last[0] == act and now - self._last[1] < self.COOLDOWN:
            return
        self._last = (act, now)
        self.fired_at = now
        self.heard = phrase
        self.history = (self.history + [(now, phrase, act)])[-4:]
        try:
            self.on_command(act)
        except Exception:
            log(traceback.format_exc())

    def _judge(self, res):
        """Остаточний результат -> виконати команду, якщо модель достатньо впевнена."""
        text = res.get("text", "")
        act, ph = find_phrase(text, self.phrases)
        clean = " ".join(w for w in text.split() if w != "[unk]")
        if not act:
            if clean:
                self._note(clean)
            return
        words = ph.split()
        confs = [w.get("conf", 1.0) for w in res.get("result", []) if w.get("word") in words]
        conf = min(confs) if confs else 1.0
        if conf >= 0.1 + 0.5 * float(self.s.get("voice_strict") or 0.5) or act == "stop":   # strict 0.5 -> 35 %
            self._fire(act, ph)
        else:
            self._note(f"{ph}? не впевнено {int(conf * 100)}%")

    def _note(self, text):
        now = time.monotonic()
        self.heard = text + "  (не команда)"
        self.history = (self.history + [(now, text, None)])[-4:]

    def _progress(self, msg):
        self.status = msg

    def run(self):
        try:
            import sounddevice as sd
            if self.engine_kind == "mine":
                self.reload_templates()
                if self.templates is None and not self.s.get("_voice_training"):
                    # зразків ще немає — щоб команди працювали одразу, слухаємо готовою моделлю
                    try:
                        import vosk  # noqa: F401
                        self.engine_kind = "model"
                        self.fallback = True
                    except ImportError:
                        pass
                if self.engine_kind == "mine":
                    self._listen(sd, None, None)
                    return
            path = ensure_voice_model(self._progress, self.s.get("voice_model") or "small")
            self.status = "Завантажую модель у пам'ять…"
            from vosk import KaldiRecognizer, Model, SetLogLevel
            SetLogLevel(-1)
            model = Model(path)
            # лишаємо тільки фрази, всі слова яких модель знає
            off = set(self.s.get("voice_off") or [])
            for act, _desc, variants in VOICE_COMMANDS:
                if act in off:
                    continue
                for ph in variants:
                    if all(model.vosk_model_find_word(w) >= 0 for w in ph.split()):
                        self.phrases[ph] = act
            if not self.phrases:
                raise RuntimeError("Голосова модель не знає жодної команди.")
            grammar = json.dumps(list(self.phrases) + ["[unk]"], ensure_ascii=False)
            self._listen(sd, KaldiRecognizer, (model, grammar))
        except Exception as e:
            msg = str(e) or e.__class__.__name__
            if isinstance(e, OSError) and "urlopen" in msg or "URLError" in e.__class__.__name__:
                msg = "не вдалося завантажити модель — перевірте інтернет"
            elif "PortAudio" in msg or "device" in msg.lower():
                msg = "мікрофон недоступний — перевірте, чи дозволено доступ до мікрофона"
            self.error = msg
            log(traceback.format_exc())
            self.status = "Помилка"
        else:
            self.status = "Вимкнено"

    def reload_templates(self):
        samples, self.train_noise = load_voice_samples()
        off = set(self.s.get("voice_off") or [])
        samples = {a: l for a, l in samples.items() if a not in off and a in VOICE_LABEL}
        self.templates = build_templates(samples) if samples else None
        self.thr = self.templates.threshold() if self.templates else 1.0
        self.trained = sorted(samples)

    def _on_utt(self, audio):
        """«Мій голос»: щойно закінчилось слово."""
        if self.recorder is not None:
            cb, self.recorder = self.recorder, None
            cb(audio, self.seg.noise)
            return
        if self.templates is None:
            self._note("немає зразків — натисніть «Навчити мій голос»")
            return
        act, sc, conf = self.templates.classify(
            voice_features(audio), float(self.s.get("voice_strict") or 0.6), thr=self.thr,
            noise_delta=self.seg.noise - self.train_noise)
        if act:
            self._fire(act, VOICE_LABEL.get(act, act))
        elif sc:
            near = min(sc, key=sc.get)
            # «стоп» — безпечна команда (лише зупиняє стрільбу), тож для неї вистачає того,
            # що це найближче слово: краще зайва зупинка, ніж стрільба, що не зупиняється
            if near == "stop" and math.isfinite(sc[near]) and sc[near] <= self.thr * 3:
                self._fire("stop", VOICE_LABEL["stop"])
            else:
                self._note(f"? схоже на «{VOICE_LABEL.get(near, near)}»")

    def _listen(self, sd, KaldiRecognizer, model_grammar):
        """Відкрити мікрофон і слухати (обидва режими)."""
        np = _np
        q = queue.Queue(maxsize=64)

        def callback(indata, frames, t, status):
            try:
                q.put_nowait(bytes(indata))
            except queue.Full:
                pass

        self.devices = mic_devices()
        want = self.s.get("voice_device") or ""
        device = next((i for i, n in self.devices if n == want), None)
        stream = None
        for rate in (16000, None):
            try:
                if rate is None:
                    rate = int(sd.query_devices(device if device is not None else sd.default.device[0],
                                                "input")["default_samplerate"])
                stream = sd.RawInputStream(samplerate=rate, blocksize=rate // 10, dtype="int16",
                                           channels=1, callback=callback, device=device)
                break
            except Exception:
                stream = None
        if stream is None:
            raise RuntimeError("мікрофон недоступний — перевірте, чи дозволено доступ до мікрофона")
        rec = None
        if self.engine_kind == "model":
            model, grammar = model_grammar
            ambiguous = ambiguous_phrases(self.phrases)
            rec = KaldiRecognizer(model, rate, grammar)
            rec.SetWords(True)            # впевненість кожного слова
        else:
            self.seg = VoiceSegmenter(self._on_utt)
        last_partial, stable = "", 0
        with stream:
            self.status = "Слухаю"
            while not self.stopped:
                try:
                    data = q.get(timeout=0.3)
                except queue.Empty:
                    continue
                # підсилення + рівень гучності для «хвилі»
                a = np.frombuffer(data, dtype=np.int16).astype(np.float32)
                gain = float(self.s.get("voice_gain") or 1.0)
                if gain != 1.0:
                    a = np.clip(a * gain, -32768, 32767)
                    data = a.astype(np.int16).tobytes()
                rms = float(np.sqrt(np.mean(a * a))) / 32768 if a.size else 0.0
                db = 20 * math.log10(rms + 1e-9)
                self.levels = self.levels[1:] + [_clamp((db + 55) / 50, 0.0, 1.0)]

                if rec is None:                  # «Мій голос»
                    x = a if rate == VSR else np.interp(
                        np.arange(0, len(a) * VSR / rate) * rate / VSR, np.arange(len(a)), a)
                    self.seg.push(x)
                    self.partial = "🗣 говорите…" if self.seg.active else ""
                    continue
                if rec.AcceptWaveform(data):
                    self._judge(json.loads(rec.Result()))
                    last_partial, stable, self.partial = "", 0, ""
                    continue
                part = json.loads(rec.PartialResult()).get("partial", "")
                self.partial = part.replace("[unk]", "…").strip()
                stable = stable + 1 if (part and part == last_partial) else 0
                last_partial = part
                act, ph = find_phrase(part, self.phrases)
                # Здогад тримається ~0.2 с (довгі/неоднозначні — 0.3 с) -> просимо в моделі
                # остаточний результат з упевненістю і лише тоді виконуємо
                if act and stable >= (2 if ph in ambiguous else 1):
                    self._judge(json.loads(rec.FinalResult()))
                    last_partial, stable, self.partial = "", 0, ""


# ============================== Калібрування ==============================
CALIB_STEPS = [
    ("open", "✋  Відкрита долоня",
     "Покажіть камері відкриту долоню (як зазвичай керуєте) і тримайте її нерухомо.", 2.5),
    ("pinch", "👌  Великий + вказівний",
     "Зведіть великий і вказівний пальці разом — як для кліку — і тримайте.", 2.0),
    ("mid", "🤌  Великий + середній",
     "Зведіть великий і середній пальці разом — як для правого кліку — і тримайте.", 2.0),
    ("fist", "✊  Кулак", "Стисніть кулак і тримайте.", 1.5),
    ("range", "↔  Зручні межі",
     "Повільно поводьте відкритою рукою вліво, вправо, вгору і вниз — так далеко, як вам ЗРУЧНО "
     "(не тягніться). Центр цих рухів стане центром джойстика.", 5.0),
]
CALIB_SETTLE = 0.7   # сек на те, щоб скласти жест, перед початком вимірювання


def _median(xs):
    xs = sorted(xs)
    n = len(xs)
    return (xs[n // 2] + xs[(n - 1) // 2]) / 2 if n else 0.0


def _pct(xs, q):
    xs = sorted(xs)
    return xs[min(len(xs) - 1, max(0, int(q * (len(xs) - 1))))] if xs else 0.0


def _clamp(x, lo, hi):
    return min(max(x, lo), hi)


def compute_calibration(samples):
    """samples: {крок: [виміри]} -> (нові налаштування, попередження)."""
    warn = []
    o, pi, pm, fi, rg = (samples[k] for k in ("open", "pinch", "mid", "fist", "range"))
    open_i, open_m = _median([x["p_idx"] for x in o]), _median([x["p_mid"] for x in o])
    close_i, close_m = _median([x["p_idx"] for x in pi]), _median([x["p_mid"] for x in pm])
    res = {"calibrated": True}

    def thresholds(op, cl, name):
        """Пороги між «зведено» і «відкрито». None, якщо жест нечіткий (лишаємо стандартні)."""
        gap = op - cl
        if gap < 0.25 or cl > 0.45:
            warn.append(f"Щипок «{name}» нечіткий — для нього лишаю стандартні пороги. "
                        "Зводьте пальці щільніше, долонею до камери, і пройдіть ще раз.")
            return None
        on = _clamp(cl + 0.25 * gap, 0.12, 0.55)
        off = _clamp(cl + 0.45 * gap, on + 0.06, 0.8)
        return round(on, 3), round(off, 3), cl + 0.6 * gap

    ti = thresholds(open_i, close_i, "великий + вказівний")
    if ti:
        res["pinch_on"], res["pinch_off"] = ti[0], ti[1]
        res["freeze_ratio"] = round(_clamp(ti[2], ti[1] + 0.03, max(ti[1] + 0.03, open_i - 0.05)), 3)
    else:
        res["pinch_on"] = res["pinch_off"] = res["freeze_ratio"] = None
    tm = thresholds(open_m, close_m, "великий + середній")
    res["mid_on"], res["mid_off"] = (tm[0], tm[1]) if tm else (None, None)

    # тремтіння руки в спокої -> плавність
    us, vs = [x["u"] for x in o], [x["v"] for x in o]
    mu, mv = sum(us) / len(us), sum(vs) / len(vs)
    jitter = math.sqrt(sum((u - mu) ** 2 + (v - mv) ** 2 for u, v in zip(us, vs)) / (2 * len(us)))
    res["_jitter"] = jitter
    if jitter > 0.012:
        warn.append("На першому кроці рука рухалась — плавність не змінюю.")
    else:
        lo, hi = math.log10(0.0006), math.log10(0.005)
        t = _clamp((math.log10(max(jitter, 1e-5)) - lo) / (hi - lo), 0.0, 1.0)
        res["smoothing"] = round(0.15 + 0.6 * t, 2)

    fist_ok = sum(1 for x in fi if not any(x["ups"])) / max(len(fi), 1)
    if fist_ok < 0.6:
        warn.append("Кулак розпізнається ненадійно — стискайте пальці щільніше.")

    ru, rv = [x["u"] for x in rg], [x["v"] for x in rg]
    u5, u95, v5, v95 = _pct(ru, 0.05), _pct(ru, 0.95), _pct(rv, 0.05), _pct(rv, 0.95)
    half = max((u95 - u5) / 2, (v95 - v5) / 2)
    if half < 0.08:
        warn.append("Рука рухалась зовсім мало — межі руху лишаю стандартними.")
    else:
        res["game_cx"], res["game_cy"] = round((u5 + u95) / 2, 3), round((v5 + v95) / 2, 3)
        res["zone"] = round(_clamp(0.5 - half, 0.05, 0.35), 3)
    return res, warn


class CalibrationWizard:
    def __init__(self, app):
        self.app = app
        self.samples = {k: [] for k, *_ in CALIB_STEPS}
        self.step = 0
        self.held = 0.0
        self.last_t = None
        self.last_tick = time.monotonic()
        w = self.win = tk.Toplevel(app.root)
        w.title(APP_NAME + " — калібрування")
        w.resizable(False, False)
        w.transient(app.root)
        w.attributes("-topmost", True)
        w.protocol("WM_DELETE_WINDOW", self.cancel)
        f = ttk.Frame(w, padding=16)
        f.grid()
        self.img = tk.Label(f, image=app.blank, bg="#1e1e1e", bd=0)
        self.img.grid(row=0, column=0, rowspan=5, padx=(0, 16))
        self.count_var = tk.StringVar()
        self.title_var = tk.StringVar()
        self.text_var = tk.StringVar()
        self.hint_var = tk.StringVar()
        ttk.Label(f, textvariable=self.count_var, foreground="#666").grid(row=0, column=1, sticky="w")
        ttk.Label(f, textvariable=self.title_var, font=("Segoe UI", 16, "bold")).grid(row=1, column=1, sticky="w")
        ttk.Label(f, textvariable=self.text_var, wraplength=300, justify="left").grid(row=2, column=1, sticky="nw")
        self.bar = ttk.Progressbar(f, length=300, maximum=100)
        self.bar.grid(row=3, column=1, sticky="ew", pady=(8, 0))
        ttk.Label(f, textvariable=self.hint_var, foreground="#b35c00").grid(row=4, column=1, sticky="w")
        self.btns = ttk.Frame(f)
        self.btns.grid(row=5, column=0, columnspan=2, sticky="e", pady=(12, 0))
        ttk.Button(self.btns, text="Скасувати", command=self.cancel).pack(side="right")
        app.start()
        self._show_step()
        self._tick()

    def _engine(self):
        e = self.app.engine
        return e if (e and e.is_alive()) else None

    def _show_step(self):
        key, title, text, dur = CALIB_STEPS[self.step]
        self.count_var.set(f"Крок {self.step + 1} з {len(CALIB_STEPS)}")
        self.title_var.set(title)
        self.text_var.set(text)
        self.held, self.last_t = 0.0, None
        self.bar["value"] = 0

    def _tick(self):
        if not self.win.winfo_exists():
            return
        if self.app.photo is not None:
            self.img.config(image=self.app.photo)
        e = self._engine()
        now = time.monotonic()
        if self.step < len(CALIB_STEPS):
            if e is None:
                self.hint_var.set("Запускаю камеру…")
            else:
                e.calibrating, e.paused = True, False
                raw = e.raw
                if raw is None:
                    self.hint_var.set("Покажіть руку камері")
                    self.held = min(self.held, CALIB_SETTLE)
                    self.last_tick = now
                elif raw["t"] != self.last_t:
                    self.last_t = raw["t"]
                    self.hint_var.set("")
                    self.held += min(now - self.last_tick, 0.2)   # час між новими кадрами з рукою
                    self.last_tick = now
                    key, _, _, dur = CALIB_STEPS[self.step]
                    if self.held > CALIB_SETTLE:
                        self.samples[key].append(raw)
                    self.bar["value"] = 100 * _clamp((self.held - CALIB_SETTLE) / dur, 0, 1)
                    if self.held >= CALIB_SETTLE + dur and len(self.samples[key]) >= 8:
                        self.step += 1
                        if self.step < len(CALIB_STEPS):
                            self._show_step()
                        else:
                            self._finish()
        self.win.after(40, self._tick)

    def _finish(self):
        e = self._engine()
        if e:
            e.calibrating = False
        self.result, warn = compute_calibration(self.samples)
        r = self.result
        self.count_var.set("Готово")
        self.title_var.set("✅  Калібрування завершено")
        def thr(a, b):
            return f"спрацьовує при {r[a]:.2f}, відпускається при {r[b]:.2f}" if r.get(a) else "стандартні пороги"
        j = r["_jitter"]
        shake = "мале" if j < 0.0015 else "середнє" if j < 0.004 else "помітне"
        lines = [f"Клік (великий + вказівний): {thr('pinch_on', 'pinch_off')}",
                 f"Правий клік (великий + середній): {thr('mid_on', 'mid_off')}"]
        if "smoothing" in r:
            lines.append(f"Плавність: {r['smoothing']:.2f} (тремтіння руки {shake})")
        if "game_cx" in r:
            lines.append(f"Центр джойстика: ({r['game_cx']:.2f}, {r['game_cy']:.2f})")
        if warn:
            lines.append("")
            lines += ["⚠ " + w for w in warn]
        self.text_var.set("\n".join(lines))
        self.hint_var.set("")
        self.bar["value"] = 100
        for b in self.btns.winfo_children():
            b.destroy()
        ttk.Button(self.btns, text="Зберегти", command=self.save).pack(side="right")
        ttk.Button(self.btns, text="Пройти ще раз", command=self.restart).pack(side="right", padx=(0, 6))
        ttk.Button(self.btns, text="Скасувати", command=self.cancel).pack(side="right", padx=(0, 6))

    def restart(self):
        self.win.destroy()
        self.app.calibrate()

    def save(self):
        for k, v in self.result.items():
            if not k.startswith("_"):
                self.app.s[k] = v
        save_settings(self.app.s)
        for k, var in self.app.vars.items():
            var.set(self.app.s[k])
        for f in self.app.updaters:
            f()
        self.win.destroy()
        messagebox.showinfo(APP_NAME, "Налаштування під вашу руку збережено.")

    def cancel(self):
        e = self._engine()
        if e:
            e.calibrating = False
        self.win.destroy()


# ============================== Встановлення бібліотек ==============================
def missing_packages():
    if FROZEN:
        return []
    import importlib.util
    return [pip for mod, pip in REQUIRED.items() if importlib.util.find_spec(mod) is None]


def run_pip(root, packages, done):
    """Встановити пакети у фоні; done(ok) викликається у вікні програми."""
    result = {}

    def work():
        try:
            p = subprocess.run([python_console_exe(), "-m", "pip", "install", "--upgrade", *packages],
                               capture_output=True, text=True, creationflags=NO_WINDOW)
            result["ok"] = p.returncode == 0
            log((p.stdout or "") + (p.stderr or ""))
        except Exception as e:
            result["ok"] = False
            log(str(e))

    t = threading.Thread(target=work, daemon=True)
    t.start()

    def poll():
        if t.is_alive():
            root.after(300, poll)
        else:
            done(result.get("ok", False))
    poll()


def install_and_restart(root, packages):
    win = tk.Toplevel(root)
    win.title(APP_NAME)
    win.resizable(False, False)
    ttk.Label(win, text="Встановлюю потрібні бібліотеки…\nЦе займе 1–3 хвилини, потрібен інтернет.",
              padding=16, justify="center").pack()
    bar = ttk.Progressbar(win, mode="indeterminate", length=320)
    bar.pack(padx=16, pady=(0, 16))
    bar.start(12)
    result = {}

    def work():
        try:
            p = subprocess.run([python_console_exe(), "-m", "pip", "install", "--upgrade", *packages],
                               capture_output=True, text=True, creationflags=NO_WINDOW)
            result["ok"] = p.returncode == 0
            result["out"] = (p.stdout or "") + (p.stderr or "")
        except Exception as e:
            result["ok"], result["out"] = False, str(e)

    def poll():
        if t.is_alive():
            root.after(300, poll)
            return
        log(result.get("out", ""))
        if result.get("ok"):
            subprocess.Popen([pythonw_exe(), APP_FILE], cwd=APP_DIR)
        else:
            messagebox.showerror(APP_NAME, "Не вдалося встановити бібліотеки.\n\n"
                                 + result.get("out", "")[-800:] + f"\n\nЖурнал: {LOG_PATH}")
        root.destroy()

    t = threading.Thread(target=work, daemon=True)
    t.start()
    poll()


# ============================== Збирання HandMouse.exe ==============================
def build_dirs():
    base = os.path.join(special_folder(0x05) if IS_WIN else os.path.expanduser("~"), "HandMouse_exe")
    return base, os.path.join(base, "dist"), os.path.join(base, "build")


def build_exe_worker(state):
    """Фоновий потік: pip -> PyInstaller -> перевірка запуску. Пише прогрес у state."""
    import importlib.util
    import shutil
    base, dist, work = build_dirs()
    os.makedirs(base, exist_ok=True)
    blog = os.path.join(DATA_DIR, "build.log")
    py = python_console_exe()

    def run(cmd, step):
        state["step"] = step
        with open(blog, "a", encoding="utf-8") as f:
            f.write("\n$ " + " ".join(cmd) + "\n")
            f.flush()
            p = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, creationflags=NO_WINDOW, cwd=base)
        if p.returncode != 0:
            raise RuntimeError(f"{step} — помилка (код {p.returncode}). Журнал: {blog}")

    try:
        open(blog, "w").close()
        build_icon()
        run([py, "-m", "pip", "install", "--upgrade", "pyinstaller", "vosk", "sounddevice"],
            "Встановлюю PyInstaller і голосові бібліотеки…")
        cmd = [py, "-m", "PyInstaller", "--noconfirm", "--clean", "--windowed", "--name", "HandMouse",
               "--distpath", dist, "--workpath", work, "--specpath", work,
               "--collect-all", "mediapipe", "--collect-all", "vosk", "--hidden-import", "sounddevice"]
        if os.path.exists(ICON_PATH):
            cmd += ["--icon", ICON_PATH]
        if importlib.util.find_spec("_sounddevice_data") is not None:
            cmd += ["--collect-all", "_sounddevice_data"]
        run(cmd + [os.path.abspath(__file__)], "Збираю HandMouse.exe (3–10 хвилин)…")
        exe = os.path.join(dist, "HandMouse", "HandMouse.exe" if IS_WIN else "HandMouse")
        state["exe"] = exe
        state["step"] = "Перевіряю, чи Windows дозволяє запуск…"
        try:
            p = subprocess.run([exe, "--selftest"], timeout=180, creationflags=NO_WINDOW,
                               capture_output=True, text=True)
            state["runs"] = p.returncode == 0
            if p.returncode != 0:
                state["why"] = f"код виходу {p.returncode}: {(p.stdout + p.stderr)[-300:]}"
        except OSError as e:          # Smart App Control / політика блокує непідписаний .exe
            state["runs"], state["why"] = False, str(e)
        state["step"] = "Пакую архів для інших комп'ютерів…"
        state["zip"] = shutil.make_archive(os.path.join(base, "HandMouse_для_друзів"), "zip",
                                           os.path.join(dist), "HandMouse")
        state["ok"] = True
    except Exception as e:
        state["ok"], state["error"] = False, str(e)
        log(traceback.format_exc())
    state["done"] = True


# ============================== Навчання «Мій голос» ==============================
class VoiceTrainer:
    """Записує кожну увімкнену команду 3 рази. Потім перевіряє, чи команди не схожі між собою."""
    PER = 3

    def __init__(self, app):
        self.app = app
        off = set(app.s.get("voice_off") or [])
        self.acts = [a for a, _d, _v in VOICE_COMMANDS if a not in off]
        self.samples, self.noise = load_voice_samples()
        self.noises = []
        self.queue = []          # (дія, номер зразка) — що записувати далі
        self.cur = None
        self.rec_q = queue.Queue()
        app.s["_voice_training"] = True        # під час навчання слухаємо в режимі «мій голос»
        v = app.voice
        if v is None or not v.is_alive() or v.engine_kind != "mine" or v.error:
            app._restart_voice()
        w = self.win = tk.Toplevel(app.root)
        w.title(APP_NAME + " — навчити мій голос")
        w.resizable(False, False)
        w.transient(app.root)
        w.protocol("WM_DELETE_WINDOW", self.close)
        f = ttk.Frame(w, padding=14)
        f.grid()
        ttk.Label(f, wraplength=520, justify="left", foreground="#444",
                  text="Скажіть кожну команду 3 рази — так, як говоритимете під час гри (у тій самій кімнаті, "
                       "з тим самим мікрофоном). Можна будь-яке слово будь-якою мовою: програма запам'ятає "
                       "саме ваш голос. Вимкнені команди (кнопка «Команди…») тут не показуються.").grid(
            row=0, column=0, columnspan=3, sticky="w")
        self.prompt = tk.StringVar(value="Натисніть «Записати всі» або виберіть команду в списку.")
        ttk.Label(f, textvariable=self.prompt, font=("Segoe UI", 15, "bold"), wraplength=520).grid(
            row=1, column=0, columnspan=3, sticky="w", pady=(10, 4))
        self.meter = tk.Canvas(f, width=520, height=44, bg="#1e1e1e", highlightthickness=0)
        self.meter.grid(row=2, column=0, columnspan=3, sticky="w")
        self.info = tk.StringVar()
        ttk.Label(f, textvariable=self.info, foreground="#b35c00", wraplength=520).grid(
            row=3, column=0, columnspan=3, sticky="w", pady=(2, 6))
        self.tree = ttk.Treeview(f, columns=("word", "n"), show="headings", height=9, selectmode="browse")
        self.tree.heading("word", text="Команда")
        self.tree.heading("n", text="Зразків")
        self.tree.column("word", width=400)
        self.tree.column("n", width=100, anchor="center")
        self.tree.grid(row=4, column=0, columnspan=3, sticky="ew")
        b = ttk.Frame(f)
        b.grid(row=5, column=0, columnspan=3, sticky="ew", pady=(8, 0))
        ttk.Button(b, text="🎙  Записати всі (по 3 рази)", command=self.record_all).pack(side="left")
        ttk.Button(b, text="Перезаписати вибрану", command=self.record_selected).pack(side="left", padx=6)
        ttk.Button(b, text="+1 зразок вибраній", command=self.add_selected).pack(side="left")
        ttk.Button(b, text="Готово", command=self.close).pack(side="right")
        self.refresh()
        self._tick()

    def refresh(self):
        self.tree.delete(*self.tree.get_children())
        for a in self.acts:
            n = len(self.samples.get(a, []))
            self.tree.insert("", "end", iid=a, values=(f"«{VOICE_LABEL[a]}» — {VOICE_DESC[a]}",
                                                       f"{n}" + (" ✓" if n >= self.PER else "")))

    def _listener(self):
        v = self.app.voice
        return v if (v and v.is_alive() and v.engine_kind == "mine" and v.status == "Слухаю") else None

    def record_all(self):
        self.queue = [(a, i) for a in self.acts for i in range(self.PER)]
        for a in self.acts:
            self.samples[a] = []
        self._next()

    def record_selected(self):
        sel = self.tree.selection()
        if sel:
            self.samples[sel[0]] = []
            self.queue = [(sel[0], i) for i in range(self.PER)]
            self._next()

    def add_selected(self):
        sel = self.tree.selection()
        if sel:
            self.queue = [(sel[0], len(self.samples.get(sel[0], [])))]
            self._next()

    def _next(self):
        self.refresh()
        if not self.queue:
            self.cur = None
            self._finish()
            return
        self.cur = self.queue.pop(0)
        a, i = self.cur
        done = sum(len(self.samples.get(x, [])) for x in self.acts)
        self.prompt.set(f"Скажіть: «{VOICE_LABEL[a]}»   ({i + 1}-й раз)")
        self.info.set(f"{VOICE_DESC[a]}. Можна інше слово — але щоразу однакове.   Записано зразків: {done}")
        self._arm()

    def _arm(self):
        v = self._listener()
        if v is None:
            self.info.set("Запускаю мікрофон…")
            self.win.after(400, self._arm)
            return
        v.recorder = lambda audio, noise: self.rec_q.put((audio, noise))

    def _got(self, audio, noise):
        if self.cur is None or not self.win.winfo_exists():
            return
        a, i = self.cur
        peak = 20 * math.log10(float(_np.sqrt(_np.mean(_np.asarray(audio, dtype=_np.float64) ** 2))) / 32768 + 1e-9)
        if peak < noise + 8:
            self.info.set("Занадто тихо — скажіть голосніше або ближче до мікрофона.")
            self._arm()
            return
        self.samples.setdefault(a, []).append(_np.asarray(audio, dtype=_np.int16))
        self.noises.append(noise)
        self._next()

    def _finish(self):
        good = {a: l for a, l in self.samples.items() if l}
        if self.noises:
            self.noise = float(_np.median(self.noises))
        save_voice_samples(good, self.noise)
        self.prompt.set("Перевіряю, чи команди не схожі між собою…")
        self.win.update()
        # кожен зразок розпізнаємо за рештою — так видно, які слова плутаються
        t = build_templates(good)
        thr = t.threshold()
        confused = {}
        for a, lst in good.items():
            for k, audio in enumerate(lst):
                rest = VoiceTemplates()
                for b, l2 in good.items():
                    for j, aud2 in enumerate(l2):
                        if not (b == a and j == k):
                            rest.add(b, t.data[b][j])
                sc = rest.scores(t.data[a][k])
                if sc:
                    best = min(sc, key=sc.get)
                    if best != a:
                        confused[(a, best)] = confused.get((a, best), 0) + 1
        v = self.app.voice
        if v:
            v.reload_templates()
        if confused:
            pairs = "; ".join(f"«{VOICE_LABEL[a]}» ↔ «{VOICE_LABEL[b]}»" for a, b in confused)
            self.prompt.set("⚠ Деякі команди звучать схоже")
            self.info.set(f"{pairs}. Перезапишіть одну з них чіткіше або оберіть для неї інше слово.")
        else:
            self.prompt.set("✅ Готово! Команди добре розрізняються.")
            self.info.set("Спробуйте сказати будь-яку команду — у рядку «Почуто» з'явиться ✓.")
        self.refresh()

    def _tick(self):
        if not self.win.winfo_exists():
            return
        while not self.rec_q.empty():
            self._got(*self.rec_q.get_nowait())
        self.app._draw_meter(self.app.voice, self.meter)
        self.win.after(50, self._tick)

    def close(self):
        if self.noises:          # закрили посередині — зберігаємо все, що встигли записати
            good = {a: l for a, l in self.samples.items() if l}
            if good:
                save_voice_samples(good, float(_np.median(self.noises)))
        self.app.s.pop("_voice_training", None)
        v = self.app.voice
        if v:
            v.recorder = None
        self.win.destroy()
        self.app._restart_voice()      # тепер зі зразками — режим «мій голос»


# ============================== Вікно програми ==============================
class App:
    def __init__(self, root, icon_png):
        self.root = root
        self.s = load_settings()
        self.engine = None
        self.photo = None
        self.overlay = self.overlay_label = self.overlay_photo = None
        self._firing = None
        self.voice_cmds = queue.Queue()
        self.shown_error = None
        root.title(APP_NAME)
        root.resizable(False, False)
        if icon_png:
            self._icon = tk.PhotoImage(data=base64.b64encode(icon_png).decode())
            root.iconphoto(True, self._icon)
        style = ttk.Style()
        try:
            style.theme_use("vista" if IS_WIN else "clam")
        except tk.TclError:
            pass
        style.configure("Big.TButton", font=("Segoe UI", 11, "bold"), padding=8)
        style.configure("Status.TLabel", font=("Segoe UI", 10, "bold"))

        main = ttk.Frame(root, padding=12)
        main.grid()
        left = ttk.Frame(main)
        left.grid(row=0, column=0, sticky="n", padx=(0, 12))
        right = ttk.Frame(main)
        right.grid(row=0, column=1, sticky="n")

        # --- ліва колонка: камера, статус, кнопки ---
        self.blank = tk.PhotoImage(width=320, height=240)   # розмір у пікселях
        self.preview = tk.Label(left, bg="#1e1e1e", fg="#bbbbbb", bd=0,
                                text="Камера вимкнена", image=self.blank, compound="center")
        self.preview.grid(row=0, column=0, columnspan=2)
        self.status_var = tk.StringVar(value="Зупинено")
        self.mode_var = tk.StringVar(value="")
        ttk.Label(left, textvariable=self.status_var, style="Status.TLabel").grid(
            row=1, column=0, columnspan=2, sticky="w", pady=(8, 0))
        ttk.Label(left, textvariable=self.mode_var, foreground="#555").grid(
            row=2, column=0, columnspan=2, sticky="w")
        self.start_btn = ttk.Button(left, text="▶  Старт", style="Big.TButton", command=self.toggle)
        self.start_btn.grid(row=3, column=0, sticky="ew", pady=(8, 0), padx=(0, 4))
        self.pause_btn = ttk.Button(left, text="⏸  Пауза (F9)", style="Big.TButton", command=self.toggle_pause)
        self.pause_btn.grid(row=3, column=1, sticky="ew", pady=(8, 0))
        help_text = ("✋ рука — курсор     👌 щипок — клік\n"
                     "👌 тримати — перетягнути / стріляти\n"
                     "великий+середній — правий клік\n"
                     "✌ вгору/вниз — прокрутка     ✊ кулак — пауза\n"
                     "F7 — центр джойстика   F8 — гра   F9 — пауза")
        ttk.Button(left, text="🎯  Калібрування під мою руку", command=self.calibrate).grid(
            row=4, column=0, columnspan=2, sticky="ew", pady=(6, 0))
        ttk.Label(left, text=help_text, foreground="#444", justify="left").grid(
            row=5, column=0, columnspan=2, sticky="w", pady=(10, 0))

        # --- права колонка: налаштування ---
        self.vars = {}
        self.updaters = []
        mode_box = ttk.LabelFrame(right, text=" Режим ", padding=8)
        mode_box.grid(row=0, column=0, sticky="ew")
        self.game_var = tk.BooleanVar(value=self.s["game_mode"])
        ttk.Radiobutton(mode_box, text="Робочий стіл", variable=self.game_var, value=False,
                        command=self._on_mode).grid(row=0, column=0, sticky="w")
        ttk.Radiobutton(mode_box, text="Гра (F8)", variable=self.game_var, value=True,
                        command=self._on_mode).grid(row=0, column=1, sticky="w", padx=(16, 0))

        nb = ttk.Notebook(right)
        nb.grid(row=1, column=0, sticky="nsew", pady=(8, 0))
        desk = ttk.Frame(nb, padding=10)
        nb.add(desk, text=" Курсор ")
        self.style_var = tk.StringVar(value=self.s["desktop_style"])
        ttk.Radiobutton(desk, text="Як миша — точніше", variable=self.style_var, value="relative",
                        command=lambda: self._set("desktop_style", self.style_var.get())).grid(row=0, column=0, sticky="w")
        ttk.Radiobutton(desk, text="Пряме наведення", variable=self.style_var, value="absolute",
                        command=lambda: self._set("desktop_style", self.style_var.get())).grid(row=0, column=1, sticky="w")
        self._slider(desk, 1, "Чутливість", "sensitivity", 0.3, 3.0)
        self._slider(desk, 2, "Плавність", "smoothing", 0.0, 1.0)
        self._check(desk, 3, "Не зсувати курсор під час кліку", "freeze_click")

        game = ttk.Frame(nb, padding=10)
        nb.add(game, text=" Гра ")
        self.gstyle_var = tk.StringVar(value=self.s["game_style"])
        ttk.Radiobutton(game, text="Джойстик + приціл", variable=self.gstyle_var, value="hybrid",
                        command=lambda: self._set("game_style", self.gstyle_var.get())).grid(row=0, column=0, sticky="w")
        ttk.Radiobutton(game, text="Як миша (✊ — перехопити)", variable=self.gstyle_var, value="mouse",
                        command=lambda: self._set("game_style", self.gstyle_var.get())).grid(
                            row=0, column=1, columnspan=2, sticky="w")
        self._slider(game, 1, "Швидкість повороту", "game_turn", 5, 60)
        self._slider(game, 2, "Точне наведення", "game_aim", 0.0, 3.0)
        self._slider(game, 3, "Мертва зона (центр)", "game_deadzone", 0.05, 0.45)
        self._check(game, 4, "Повертати вгору/вниз джойстиком", "game_vertical")
        self._check(game, 5, "Міні-камера поверх гри", "game_overlay")
        ttk.Button(game, text="✛  Центр джойстика — де зараз рука (F7)", command=self.set_center).grid(
            row=6, column=0, columnspan=3, sticky="ew", pady=(6, 0))

        voice = ttk.Frame(nb, padding=10)
        nb.add(voice, text=" Голос ")
        self._check(voice, 0, "Голосові команди (мікрофон)", "voice", self._on_voice)
        self.voice_status = tk.StringVar(value="Вимкнено")
        self.voice_heard = tk.StringVar(value="")
        ttk.Label(voice, textvariable=self.voice_status, style="Status.TLabel").grid(
            row=1, column=0, columnspan=3, sticky="w", pady=(6, 0))
        # «хвиля» гучності мікрофона
        self.meter = tk.Canvas(voice, width=340, height=48, bg="#1e1e1e", highlightthickness=0)
        self.meter.grid(row=2, column=0, columnspan=3, sticky="w", pady=(4, 2))
        ttk.Label(voice, textvariable=self.voice_heard, foreground="#555", justify="left").grid(
            row=3, column=0, columnspan=3, sticky="w")
        ttk.Label(voice, text="Мікрофон").grid(row=4, column=0, sticky="w", pady=(6, 0))
        self.mic_var = tk.StringVar(value=self.s.get("voice_device") or "Стандартний")
        self.mic_box = ttk.Combobox(voice, textvariable=self.mic_var, state="readonly", width=30,
                                    values=["Стандартний"])
        self.mic_box.grid(row=4, column=1, columnspan=2, sticky="w", padx=6, pady=(6, 0))
        self.mic_box.bind("<<ComboboxSelected>>", self._on_mic)
        ef = ttk.Frame(voice)
        ef.grid(row=10, column=0, columnspan=3, sticky="ew", pady=(8, 0))
        self.vengine_var = tk.StringVar(value=self.s.get("voice_engine") or "mine")
        ttk.Radiobutton(ef, text="Мій голос (навчання) — точніше", variable=self.vengine_var, value="mine",
                        command=self._on_vengine).pack(side="left")
        ttk.Radiobutton(ef, text="Модель (без навчання)", variable=self.vengine_var, value="model",
                        command=self._on_vengine).pack(side="left", padx=(8, 0))
        ttk.Button(voice, text="🎓  Навчити мій голос…", command=self.train_voice).grid(
            row=11, column=0, columnspan=3, sticky="ew", pady=(4, 0))
        self._slider(voice, 5, "Підсилення", "voice_gain", 1.0, 3.0)
        self._slider(voice, 6, "Суворість", "voice_strict", 0.3, 0.95)
        ttk.Label(voice, text="Модель").grid(row=7, column=0, sticky="w", pady=(4, 0))
        self.vmodel_row = []
        self.vmodel_var = tk.StringVar(value=self.s.get("voice_model") or "small")
        mf = ttk.Frame(voice)
        mf.grid(row=7, column=1, columnspan=2, sticky="w", padx=6, pady=(4, 0))
        ttk.Radiobutton(mf, text="Точна (133 МБ)", variable=self.vmodel_var, value="small",
                        command=self._on_vmodel).pack(side="left")
        ttk.Radiobutton(mf, text="Швидка (73 МБ)", variable=self.vmodel_var, value="nano",
                        command=self._on_vmodel).pack(side="left", padx=(8, 0))
        ttk.Label(voice, foreground="#444", justify="left", wraplength=340,
                  text="Хвиля має підстрибувати, коли говорите. Плутає — підніміть «Суворість» "
                       "або вимкніть зайві команди. Не реагує — зменште «Суворість». "
                       "«Мій голос» розуміє будь-яку мову й акцент — запишіть зразки там, де граєте.").grid(
            row=8, column=0, columnspan=3, sticky="w", pady=(6, 0))
        ttk.Button(voice, text="Команди: увімкнути / вимкнути…", command=self.show_voice_commands).grid(
            row=9, column=0, columnspan=3, sticky="ew", pady=(6, 0))
        self.voice = None
        self._mics_filled = False

        other = ttk.Frame(nb, padding=10)
        nb.add(other, text=" Інше ")
        ttk.Label(other, text="Камера №").grid(row=0, column=0, sticky="w")
        self.cam_var = tk.StringVar(value=str(self.s["camera"]))
        cam = ttk.Spinbox(other, from_=0, to=5, width=4, textvariable=self.cam_var, command=self._on_camera)
        cam.grid(row=0, column=1, sticky="w")
        if IS_WIN:
            ttk.Button(other, text="Налаштування камери…", command=self.camera_settings).grid(
                row=0, column=2, sticky="e", padx=(8, 0))
        self._check(other, 1, "Показувати камеру", "show_camera")
        self._check(other, 2, "Вікно поверх усіх вікон", "topmost", self._apply_topmost)
        self._check(other, 3, "Вмикати стеження одразу при запуску", "autostart")
        self._check(other, 4, "Більше кадрів/с (ручна витримка, потрібне світло)", "fast_camera",
                    self._restart_engine)
        if IS_WIN:
            self.startup_var = tk.BooleanVar(value=startup_enabled())
            ttk.Checkbutton(other, text="Запускати разом з Windows", variable=self.startup_var,
                            command=self._on_startup).grid(row=5, column=0, columnspan=2, sticky="w")
            ttk.Button(other, text="Створити ярлик на робочому столі", command=self.make_shortcuts).grid(
                row=6, column=0, columnspan=3, sticky="ew", pady=(6, 0))
        ttk.Button(other, text="Скинути налаштування", command=self.reset).grid(
            row=7, column=0, columnspan=3, sticky="ew", pady=(4, 0))
        if IS_WIN and not FROZEN:
            ttk.Button(other, text="Зібрати HandMouse.exe…", command=self.build_exe).grid(
                row=8, column=0, columnspan=3, sticky="ew", pady=(4, 0))

        self._apply_topmost()
        root.protocol("WM_DELETE_WINDOW", self.quit)
        if self.s["autostart"]:
            self.start()
        if self.s["voice"]:
            root.after(500, self._on_voice)
        if IS_WIN and not self.s.get("_shortcut_offered"):
            root.after(800, self._offer_shortcut)
        self._poll()

    # --- елементи налаштувань ---
    def _slider(self, parent, row, label, key, lo, hi):
        ttk.Label(parent, text=label).grid(row=row, column=0, sticky="w")
        var = tk.DoubleVar(value=float(self.s[key]))
        val = ttk.Label(parent, width=5)
        val.grid(row=row, column=2, sticky="e")

        def changed(_=None):
            self.s[key] = round(var.get(), 3)
            val.config(text=f"{var.get():.2f}" if hi <= 3 else f"{var.get():.0f}")
            self._save_later()
        ttk.Scale(parent, from_=lo, to=hi, variable=var, length=170, command=changed).grid(
            row=row, column=1, padx=6, pady=2)
        changed()
        self.vars[key] = var
        self.updaters.append(changed)

    def _check(self, parent, row, label, key, extra=None):
        var = tk.BooleanVar(value=bool(self.s[key]))

        def changed():
            self.s[key] = var.get()
            self._save_later()
            if extra:
                extra()
        ttk.Checkbutton(parent, text=label, variable=var, command=changed).grid(
            row=row, column=0, columnspan=3, sticky="w")
        self.vars[key] = var

    def _set(self, key, value):
        self.s[key] = value
        self._save_later()

    def _save_later(self):
        if getattr(self, "_save_job", None):
            self.root.after_cancel(self._save_job)
        self._save_job = self.root.after(500, lambda: save_settings(self.s))

    def _on_mode(self):
        self._set("game_mode", self.game_var.get())

    def _on_camera(self):
        try:
            self.s["camera"] = int(self.cam_var.get())
        except ValueError:
            return
        self._save_later()
        if self.engine and self.engine.is_alive():
            self.stop()
            self.root.after(300, self.start)

    def build_exe(self):
        base, dist, _ = build_dirs()
        if not messagebox.askyesno(APP_NAME, "Зібрати HandMouse.exe з іконкою?\n\n"
                                   "• Потрібен інтернет, 3–10 хвилин і ~1 ГБ місця на диску.\n"
                                   f"• Результат буде в папці:\n{base}\n"
                                   "• Увага: «Інтелектуальне керування програмами» Windows часто блокує "
                                   ".exe без цифрового підпису. Програма перевірить це сама. Якщо заблокує — "
                                   ".exe все одно знадобиться для інших комп'ютерів, а тут лишиться ярлик."):
            return
        win = tk.Toplevel(self.root)
        win.title(APP_NAME + " — збирання .exe")
        win.resizable(False, False)
        win.transient(self.root)
        step = tk.StringVar(value="Починаю…")
        ttk.Label(win, textvariable=step, padding=16, wraplength=380).pack()
        bar = ttk.Progressbar(win, mode="indeterminate", length=380)
        bar.pack(padx=16, pady=(0, 16))
        bar.start(12)
        state = {}
        threading.Thread(target=build_exe_worker, args=(state,), daemon=True).start()

        def poll():
            if not state.get("done"):
                step.set(state.get("step", "Починаю…"))
                win.after(300, poll)
                return
            win.destroy()
            if not state.get("ok"):
                messagebox.showerror(APP_NAME, "Не вдалося зібрати .exe:\n" + state.get("error", ""))
                return
            folder = os.path.dirname(state["exe"])
            if state.get("runs"):
                if messagebox.askyesno(APP_NAME, "✅ HandMouse.exe зібрано і він запускається!\n\n"
                                       f"{state['exe']}\n\nАрхів для друзів:\n{state['zip']}\n\n"
                                       "Перенаправити ярлики (робочий стіл і Пуск) на HandMouse.exe?"):
                    for folder_id in (0x10, 0x02):
                        make_shortcut(os.path.join(special_folder(folder_id), APP_NAME + ".lnk"), state["exe"])
                    messagebox.showinfo(APP_NAME, "Готово! Тепер ярлик запускає HandMouse.exe.")
            else:
                messagebox.showwarning(APP_NAME, "HandMouse.exe зібрано, але Windows на цьому комп'ютері "
                                       "не дає його запустити (найімовірніше, «Інтелектуальне керування "
                                       "програмами» блокує .exe без цифрового підпису).\n\n"
                                       "Тут продовжуйте користуватися ярликом «Hand Mouse» — він працює так само.\n\n"
                                       f"Архів .exe для інших комп'ютерів:\n{state['zip']}\n\n"
                                       f"Деталі: {state.get('why', '')[:200]}")
            try:
                os.startfile(os.path.dirname(state["zip"]))
            except Exception:
                pass
        poll()

    def calibrate(self):
        CalibrationWizard(self)

    # --- голос ---
    def _on_voice(self):
        if self.s["voice"]:
            if self.voice and self.voice.is_alive():
                return
            missing = voice_missing()
            if (self.s.get("voice_engine") or "mine") == "mine" and load_voice_samples()[0]:
                missing = [m for m in missing if m != "vosk"]
            if missing:
                if getattr(sys, "frozen", False):
                    messagebox.showerror(APP_NAME, "У цій збірці немає голосових бібліотек.")
                    self.vars["voice"].set(False); self.s["voice"] = False
                    return
                if not messagebox.askyesno(APP_NAME, "Для голосових команд потрібні бібліотеки: "
                                           + ", ".join(missing) + ".\nВстановити зараз (потрібен інтернет)?"):
                    self.vars["voice"].set(False); self.s["voice"] = False
                    return
                self.voice_status.set("Встановлюю бібліотеки…")
                run_pip(self.root, missing, lambda ok: self._voice_installed(ok))
                return
            self.voice = VoiceListener(self.voice_cmds.put, self.s)   # дії виконує _poll (потокобезпечно)
            self.voice.start()
        else:
            if self.voice:
                self.voice.stopped = True
            self.voice = None
            self.voice_status.set("Вимкнено")
            self.voice_heard.set("")

    def _restart_voice(self):
        """Перезапустити голос (навіть якщо попередній потік завершився з помилкою)."""
        if not self.s.get("voice"):
            return
        if self.voice:
            self.voice.stopped = True
        self.voice = None
        self._mics_filled = False
        self.root.after(400, self._on_voice)

    def _on_vengine(self):
        self.s["voice_engine"] = self.vengine_var.get()
        self._save_later()
        if self.voice and self.voice.is_alive():
            self._restart_voice()
        if self.s["voice_engine"] == "mine" and not load_voice_samples()[0]:
            self.root.after(300, self.train_voice)

    def train_voice(self):
        if self.s.get("voice_engine") != "mine":
            self.vengine_var.set("mine")
            self.s["voice_engine"] = "mine"
            self._save_later()
            self._restart_voice()
        if not self.s.get("voice"):
            self.vars["voice"].set(True)
            self.s["voice"] = True
            self._on_voice()
        VoiceTrainer(self)

    def _on_vmodel(self):
        self.s["voice_model"] = self.vmodel_var.get()
        self._save_later()
        self._restart_voice()

    def _on_mic(self, _=None):
        name = self.mic_var.get()
        self.s["voice_device"] = "" if name == "Стандартний" else name
        self._save_later()
        if self.voice and self.voice.is_alive():      # перезапуск з новим мікрофоном
            self.voice.stopped = True
            self.voice = None
            self._mics_filled = False
            self.root.after(400, self._on_voice)

    def _draw_meter(self, v, c=None):
        c = c or self.meter
        c.delete("all")
        w, h = int(c["width"]), int(c["height"])
        levels = v.levels if v else [0.0] * 60
        n = len(levels)
        bw = w / n
        flash = v is not None and time.monotonic() - v.fired_at < 0.5
        listening = v is not None and v.status == "Слухаю" and not v.error
        color = "#4aa3ff" if flash else ("#3ecf6e" if listening else "#555555")
        mid = h / 2
        for i, lv in enumerate(levels):
            amp = max(1.0, lv * (h / 2 - 2))
            x = i * bw
            c.create_rectangle(x + 1, mid - amp, x + bw - 1, mid + amp, fill=color, outline="")
        if flash:
            c.create_text(w - 6, 10, text="✓ " + v.heard, anchor="e", fill="#ffffff", font=("Segoe UI", 9, "bold"))

    def _voice_installed(self, ok):
        if ok:
            import importlib
            importlib.invalidate_caches()
            self._on_voice()
        else:
            self.vars["voice"].set(False); self.s["voice"] = False
            self.voice_status.set("Не вдалося встановити бібліотеки")

    AUTOFIRE_MS = 90         # «стріляй»: клік кожні 90 мс
    AUTOFIRE_LIMIT = 20.0    # безпека: сама зупиниться через 20 с, якщо «стоп» не почуто

    def _autofire(self):
        if self._firing is None:
            return
        if time.monotonic() - self._firing > self.AUTOFIRE_LIMIT:
            self._firing = None
            return
        mouse_now("click")
        self.root.after(self.AUTOFIRE_MS, self._autofire)

    def voice_action(self, act):
        if act == "click":
            mouse_now("click")
        elif act == "jump":
            press_keys("space")
        elif act == "fire":
            if self._firing is None:
                self._firing = time.monotonic()
                self._autofire()
        elif act == "hold":
            self._firing = None
            mouse_now("down")
        elif act == "stop":
            self._firing = None
            mouse_now("up")

    def _voice_action_old(self, act):
        e = self.engine if (self.engine and self.engine.is_alive()) else None
        if act in ("click", "double", "right", "down", "up"):
            mouse_now(act)
        elif act == "scroll_down":
            mouse_now("scroll", -600)
        elif act == "scroll_up":
            mouse_now("scroll", 600)
        elif act == "pause" and e:
            e.paused = True
        elif act == "resume":
            if e:
                e.paused = False
            else:
                self.start()
        elif act in ("game_on", "game_off"):
            self.s["game_mode"] = act == "game_on"
            self.game_var.set(self.s["game_mode"])
        elif act == "center" and e:
            e.want_center = True
        elif act in ("copy", "paste", "undo"):
            press_keys("ctrl", {"copy": "c", "paste": "v", "undo": "z"}[act])
        elif act == "enter":
            press_keys("enter")
        elif act == "back":
            press_keys("alt", "left")
        elif act == "jump":
            press_keys("space")
        elif act == "reload":
            press_keys("r")
        elif act == "keyboard" and IS_WIN:
            try:
                os.startfile("osk.exe")
            except OSError:
                subprocess.Popen(["osk.exe"], shell=True)
        elif act == "browser":
            import webbrowser
            webbrowser.open("https://www.google.com")

    def show_voice_commands(self):
        """Список команд із галочками: менше команд — менше плутанини."""
        win = tk.Toplevel(self.root)
        win.title(APP_NAME + " — голосові команди")
        win.resizable(False, False)
        win.transient(self.root)
        f = ttk.Frame(win, padding=14)
        f.grid()
        ttk.Label(f, text="Залиште лише потрібні команди — так модель менше плутає.",
                  foreground="#444").grid(row=0, column=0, columnspan=2, sticky="w", pady=(0, 8))
        off = set(self.s.get("voice_off") or [])
        known = set(self.voice.phrases) if (self.voice and self.voice.phrases) else None
        vars_ = {}
        for i, (act, desc, variants) in enumerate(VOICE_COMMANDS, 1):
            v = tk.BooleanVar(value=act not in off)
            vars_[act] = v
            words = " / ".join(f"«{p}»" for p in variants)
            if known is not None and not any(p in known for p in variants):
                words += "  (модель не знає слова)"
            ttk.Checkbutton(f, text=words, variable=v).grid(row=i, column=0, sticky="w")
            ttk.Label(f, text=desc, foreground="#666").grid(row=i, column=1, sticky="w", padx=(12, 0))

        def save():
            self.s["voice_off"] = [a for a, v in vars_.items() if not v.get()]
            save_settings(self.s)
            win.destroy()
            self._restart_voice()
        b = ttk.Frame(f)
        b.grid(row=len(VOICE_COMMANDS) + 1, column=0, columnspan=2, sticky="e", pady=(10, 0))
        ttk.Button(b, text="Зберегти", command=save).pack(side="right")
        ttk.Button(b, text="Скасувати", command=win.destroy).pack(side="right", padx=(0, 6))

    def set_center(self):
        if self.engine and self.engine.is_alive():
            self.engine.want_center = True
        else:
            messagebox.showinfo(APP_NAME, "Спершу натисніть «Старт» і покажіть руку камері.")

    # --- міні-камера поверх гри ---
    def _overlay_show(self, show):
        if show and self.overlay is None:
            ov = tk.Toplevel(self.root)
            ov.overrideredirect(True)
            ov.attributes("-topmost", True)
            try:
                ov.attributes("-alpha", 0.85)
            except tk.TclError:
                pass
            x, y = self.s.get("overlay_pos") or (12, ov.winfo_screenheight() - 200)
            ov.geometry(f"+{x}+{y}")
            lbl = tk.Label(ov, bd=0, bg="black")
            lbl.pack()
            drag = {}

            def press(ev):
                drag["x"], drag["y"] = ev.x_root - ov.winfo_x(), ev.y_root - ov.winfo_y()

            def move(ev):
                nx, ny = ev.x_root - drag["x"], ev.y_root - drag["y"]
                ov.geometry(f"+{nx}+{ny}")
                self.s["overlay_pos"] = [nx, ny]
                self._save_later()
            lbl.bind("<ButtonPress-1>", press)
            lbl.bind("<B1-Motion>", move)
            self.overlay, self.overlay_label = ov, lbl
        elif not show and self.overlay is not None:
            self.overlay.destroy()
            self.overlay = self.overlay_label = self.overlay_photo = None

    def _restart_engine(self):
        if self.engine and self.engine.is_alive():
            self.stop()
            self.root.after(500, self.start)

    def camera_settings(self):
        if self.engine and self.engine.is_alive() and self.engine.reader:
            self.engine.reader.want_settings = True
        else:
            messagebox.showinfo(APP_NAME, "Спершу натисніть «Старт», щоб увімкнути камеру.")

    def _apply_topmost(self):
        self.root.attributes("-topmost", bool(self.s["topmost"]))

    def _on_startup(self):
        try:
            if self.startup_var.get():
                build_icon()
                if not make_shortcut(startup_link()):
                    raise OSError("не вдалося створити ярлик")
            else:
                remove_startup()
        except OSError as e:
            messagebox.showerror(APP_NAME, f"Не вдалося змінити автозапуск: {e}")
        self.startup_var.set(startup_enabled())

    def _offer_shortcut(self):
        self.s["_shortcut_offered"] = True
        save_settings(self.s)
        if messagebox.askyesno(APP_NAME, "Створити ярлик «Hand Mouse» на робочому столі та в меню Пуск?\n"
                                         "Тоді програму можна буде запускати як звичайну."):
            self.make_shortcuts()

    def make_shortcuts(self):
        build_icon()
        ok1 = make_shortcut(os.path.join(special_folder(0x10), APP_NAME + ".lnk"))   # робочий стіл
        ok2 = make_shortcut(os.path.join(special_folder(0x02), APP_NAME + ".lnk"))   # меню Пуск
        if ok1 or ok2:
            messagebox.showinfo(APP_NAME, "Готово! Ярлик «Hand Mouse» є на робочому столі та в меню Пуск.")
        else:
            messagebox.showwarning(APP_NAME, "Не вдалося створити ярлик автоматично.\n"
                                             "Клацніть правою кнопкою по HandMouse.pyw → Показати додаткові "
                                             "параметри → Надіслати → Робочий стіл (створити ярлик).")

    def reset(self):
        keep = {"_shortcut_offered": True}
        for k in ("pinch_on", "pinch_off", "mid_on", "mid_off", "freeze_ratio", "calibrated"):
            keep[k] = self.s.get(k)
        self.s.clear()
        self.s.update(DEFAULTS)
        self.s.update(keep)
        save_settings(self.s)
        for k, var in self.vars.items():
            var.set(self.s[k])
        for f in self.updaters:
            f()
        self._on_voice()
        self.game_var.set(self.s["game_mode"])
        self.style_var.set(self.s["desktop_style"])
        self.gstyle_var.set(self.s["game_style"])
        self.cam_var.set(str(self.s["camera"]))
        self._apply_topmost()
        if self.engine:
            self.engine.s = self.s

    # --- керування рушієм ---
    def start(self):
        if self.engine and self.engine.is_alive():
            return
        self.shown_error = None
        self.engine = Engine(self.s)
        self.engine.start()
        self.start_btn.config(text="■  Стоп")

    def stop(self):
        if self.engine:
            self.engine.stop()
        self.start_btn.config(text="▶  Старт")

    def toggle(self):
        if self.engine and self.engine.is_alive():
            self.stop()
        else:
            self.start()

    def toggle_pause(self):
        if self.engine and self.engine.is_alive():
            self.engine.paused = not self.engine.paused

    def _poll(self):
        e = self.engine
        if e is not None:
            alive = e.is_alive()
            if e.error and self.shown_error is not e:
                self.shown_error = e
                first = e.error.strip().splitlines()[-1]
                self.status_var.set("Помилка — див. повідомлення")
                messagebox.showerror(APP_NAME, f"{first}\n\nДеталі в журналі:\n{LOG_PATH}")
            elif alive:
                extra = ""
                if e.fps:
                    extra = f"   ·  {e.fps:.0f} кадр/с"
                    if e.cam_fps:
                        extra += f"  (камера {e.cam_fps:.0f}, обробка {e.proc_ms:.0f} мс)"
                self.status_var.set(("⏸ " if e.paused else "● ") + e.status + extra)
                self.mode_var.set("Жест: " + e.mode if e.mode else "")
            elif not e.error:
                self.status_var.set("Зупинено")
                self.mode_var.set("")
            if not alive:
                self.start_btn.config(text="▶  Старт")
            if self.game_var.get() != bool(self.s["game_mode"]):   # перемкнули через F8
                self.game_var.set(bool(self.s["game_mode"]))
            png = e.preview if alive else None
            want_overlay = alive and bool(self.s["game_mode"]) and bool(self.s["game_overlay"])
            self._overlay_show(want_overlay)
            if png is not None:
                e.preview = None
                photo = tk.PhotoImage(data=png)   # «сирі» байти PPM — без base64
                if self.s["show_camera"]:
                    self.photo = photo
                    self.preview.config(image=self.photo, text="")
                if self.overlay is not None:
                    self.overlay_photo = photo.subsample(2)   # 160x120
                    self.overlay_label.config(image=self.overlay_photo)
            if not alive or not self.s["show_camera"]:
                self.photo = None
                self.preview.config(image=self.blank,
                                    text="Камера вимкнена" if not alive else "Перегляд вимкнено")
        while not self.voice_cmds.empty():                  # команди від голосу
            try:
                self.voice_action(self.voice_cmds.get_nowait())
            except Exception:
                log(traceback.format_exc())
        v = self.voice
        if v is not None:
            if v.error:
                self.voice_status.set("Помилка: " + v.error[:60])
            elif v.status == "Слухаю":
                mode = "мій голос" if v.engine_kind == "mine" else (
                    "модель — навчіть свій голос для кращої точності" if v.fallback else "модель")
                self.voice_status.set(f"🎤 Слухаю ({mode})")
            else:
                self.voice_status.set(v.status)
            now = time.monotonic()
            hist = "   ".join(f"«{t}» {'✓' if a else '✗'}" for ts, t, a in reversed(v.history) if now - ts < 30)
            self.voice_heard.set("Чую: " + (v.partial or "—") + "\nПочуто: " + (hist or "—"))
            if v.devices and not self._mics_filled:
                self._mics_filled = True
                self.mic_box["values"] = ["Стандартний"] + [n for _, n in v.devices]
        self._draw_meter(v)
        self.root.after(40, self._poll)

    def quit(self):
        self._firing = None
        self.stop()
        if self.voice:
            self.voice.stopped = True
        save_settings(self.s)
        if self.engine:
            self.engine.join(timeout=2)
        self.root.destroy()


def selftest():
    """HandMouse.exe --selftest: перевірка, що всі частини програми на місці."""
    import cv2  # noqa: F401
    import mediapipe  # noqa: F401
    from mediapipe.tasks.python import vision  # noqa: F401
    import pyautogui  # noqa: F401
    sys.exit(0)


def main():
    if IS_WIN:
        try:   # власна іконка в панелі завдань (а не значок Python)
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("HandMouse.App")
        except Exception:
            pass
    root = tk.Tk()
    root.withdraw()

    def report(exc, val, tb):
        text = "".join(traceback.format_exception(exc, val, tb))
        log(text)
        messagebox.showerror(APP_NAME, f"{val}\n\nЖурнал: {LOG_PATH}")
    root.report_callback_exception = report

    missing = missing_packages()
    if missing:
        if messagebox.askyesno(APP_NAME, "Для роботи потрібні бібліотеки: " + ", ".join(missing) +
                               ".\nВстановити їх зараз автоматично?"):
            install_and_restart(root, missing)
            root.mainloop()
        else:
            root.destroy()
        return
    icon = build_icon()
    root.deiconify()
    App(root, icon)
    root.mainloop()


if __name__ == "__main__":
    if "--selftest" in sys.argv:
        selftest()
    try:
        main()
    except Exception:
        log(traceback.format_exc())
        raise
