import collections
import copy
import ctypes
import json
import math
import queue
import statistics
import sys
import threading
import time
import tkinter as tk
from pathlib import Path
from tkinter import messagebox

import numpy as np

try:
    import customtkinter as ctk
except ImportError:
    ctk = None

try:
    import sounddevice as sd
except Exception:
    sd = None

APP_NAME = "guitar2key"
IS_WIN = sys.platform == "win32"
if getattr(sys, "frozen", False):
    BASE = Path(sys._MEIPASS)
    EXE_DIR = Path(sys.executable).parent
else:
    BASE = Path(__file__).resolve().parent
    EXE_DIR = BASE
CONFIG_PATH = EXE_DIR / "guitar2key_config.json"

MAX_SLOTS = 10
DEFAULT_NAME = "Default"  
DEADZONE_MAX = 100
CALIB_N = 8
GATE_OFF_DB = -70         
GATE_HOLD = 0.08        
MIN_HOLD = 0.012           
UNREC = ["ignore", "as previous button"]
BLOCKS = ["64", "128", "256", "512"]
API_ORDER = ["ASIO", "WDM-KS", "WASAPI", "DirectSound", "MME"]
EXT_VK = {0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x2D, 0x2E, 0x6F}

SC_NAMES = {}
for _c, _s in zip("QWERTYUIOP", range(0x10, 0x1A)):
    SC_NAMES[_s] = _c
for _c, _s in zip("ASDFGHJKL", range(0x1E, 0x27)):
    SC_NAMES[_s] = _c
for _c, _s in zip("ZXCVBNM", range(0x2C, 0x33)):
    SC_NAMES[_s] = _c
for _c, _s in zip("1234567890", range(0x02, 0x0C)):
    SC_NAMES[_s] = _c
for _i, _s in enumerate(range(0x3B, 0x45)):
    SC_NAMES[_s] = f"F{_i + 1}"
SC_NAMES.update({
    0x57: "F11", 0x58: "F12", 0x01: "Esc", 0x0C: "-", 0x0D: "=", 0x0E: "Backspace",
    0x0F: "Tab", 0x1A: "[", 0x1B: "]", 0x1C: "Enter", 0x1D: "Ctrl", 0x27: ";",
    0x28: "'", 0x29: "`", 0x2A: "Shift", 0x2B: "\\", 0x33: ",", 0x34: ".",
    0x35: "/", 0x36: "Shift", 0x38: "Alt", 0x39: "Space", 0x3A: "CapsLock",
    0x47: "Num7", 0x48: "Num8", 0x49: "Num9", 0x4B: "Num4", 0x4C: "Num5",
    0x4D: "Num6", 0x4F: "Num1", 0x50: "Num2", 0x51: "Num3", 0x52: "Num0", 0x53: "Num.",
})
EXT_NAMES = {0x48: "Up", 0x50: "Down", 0x4B: "Left", 0x4D: "Right", 0x47: "Home",
             0x4F: "End", 0x49: "PageUp", 0x51: "PageDown", 0x52: "Insert",
             0x53: "Delete", 0x35: "Num/"}


def key_name(sc, ext=False):
    if ext and sc in EXT_NAMES:
        return EXT_NAMES[sc]
    return SC_NAMES.get(sc, f"Key {sc}")


def vk_to_scan(vk):
    if IS_WIN:
        return int(ctypes.windll.user32.MapVirtualKeyW(vk, 0))
    return 0


def estimate_pitch(x, sr, fmax=1200.0):
    x = x - x.mean()
    n = len(x)
    r = np.correlate(x, x, "full")[n - 1:]
    if r[0] <= 1e-12:
        return None
    r = r / r[0]
    lo = max(2, int(sr / fmax))
    hi = n // 2 
    neg = np.where(r[1:hi] < 0)[0]
    if len(neg) == 0:
        return None
    start = max(lo, int(neg[0]) + 1)
    if hi <= start + 2:
        return None
    seg = r[start:hi]
    m = seg.max()
    if m < 0.3:
        return None
    idx = int(np.argmax(seg > 0.9 * m)) + start
    while idx + 1 < hi and r[idx + 1] > r[idx]:
        idx += 1
    shift = 0.0
    if 0 < idx < n - 1:
        a, b, c = r[idx - 1], r[idx], r[idx + 1]
        den = a - 2 * b + c
        if den < -1e-6:
            shift = max(-1.0, min(1.0, 0.5 * (a - c) / den))
    freq = sr / (idx + shift)
    return float(freq) if freq > 0 else None


def classify(freq, slots):
    if not freq or freq <= 0 or not slots:
        return None
    best, best_d = None, 1e9
    for idx, f, _keys in slots:
        d = abs(math.log(freq / f))
        if d < best_d:
            best, best_d = idx, d
    return best

class KeySender:
    def __init__(self, hold_ms=12):
        self.hold = hold_ms / 1000.0
        self.q = queue.Queue()
        self.down_t = {}
        self._setup()
        threading.Thread(target=self._run, daemon=True).start()

    def _setup(self):
        from ctypes import wintypes

        PUL = ctypes.POINTER(ctypes.c_ulong)

        class KEYBDINPUT(ctypes.Structure):
            _fields_ = [("wVk", wintypes.WORD), ("wScan", wintypes.WORD),
                        ("dwFlags", wintypes.DWORD), ("time", wintypes.DWORD),
                        ("dwExtraInfo", PUL)]

        class MOUSEINPUT(ctypes.Structure):
            _fields_ = [("dx", wintypes.LONG), ("dy", wintypes.LONG),
                        ("mouseData", wintypes.DWORD), ("dwFlags", wintypes.DWORD),
                        ("time", wintypes.DWORD), ("dwExtraInfo", PUL)]

        class _I(ctypes.Union):
            _fields_ = [("ki", KEYBDINPUT), ("mi", MOUSEINPUT)]

        class INPUT(ctypes.Structure):
            _fields_ = [("type", wintypes.DWORD), ("i", _I)]

        user32 = ctypes.windll.user32
        extra = ctypes.c_ulong(0)

        def send(scan, up, ext):
            flags = 0x0008 | (0x0002 if up else 0) | (0x0001 if ext else 0)
            ii = _I()
            ii.ki = KEYBDINPUT(0, scan, flags, 0, ctypes.pointer(extra))
            inp = INPUT(1, ii)
            user32.SendInput(1, ctypes.byref(inp), ctypes.sizeof(inp))

        self._send = send

    def tap(self, sc, ext=False):
        self.q.put(("tap", sc, ext))

    def down(self, sc, ext=False):
        self.q.put(("down", sc, ext))

    def up(self, sc, ext=False):
        self.q.put(("up", sc, ext))

    def _run(self):
        while True:
            op, sc, ext = self.q.get()
            key = (sc, ext)
            if op == "tap":
                self._send(sc, False, ext)
                time.sleep(self.hold)
                self._send(sc, True, ext)
            elif op == "down":
                self._send(sc, False, ext)
                self.down_t[key] = time.perf_counter()
            elif op == "up":
                t0 = self.down_t.pop(key, None)
                if t0 is not None:
                    wait = self.hold - (time.perf_counter() - t0)
                    if wait > 0:
                        time.sleep(wait)
                self._send(sc, True, ext)
                time.sleep(0.004)


def sens_to_thr(s):
    return 0.1 * (0.02 ** (s / 100.0))


class Params:
    sensitivity = 41
    deadzone_ms = 40
    window_ms = 30
    ratio = 1.8
    gate_db = GATE_OFF_DB
    release_pct = 60

    @property
    def threshold(self):
        return sens_to_thr(self.sensitivity)

    @property
    def gate_thr(self):
        return 0.0 if self.gate_db <= GATE_OFF_DB else 10 ** (self.gate_db / 20.0)


class Detector:
    def __init__(self, sr, params, on_hit, on_release=None):
        self.sr = sr
        self.p = params
        self.on_hit = on_hit
        self.on_release = on_release
        self.hist = collections.deque([0.0] * 64, maxlen=64)
        self.collecting = False
        self.buf = []
        self.have = 0
        self.need = 0
        self.t = 0.0
        self.last = -1e9
        self.gate_until = -1.0
        self.note_active = False

    def _env(self, block_len):
        k = max(4, int(0.02 * self.sr / max(1, block_len)))
        return max(list(self.hist)[-k:])

    def process(self, block):
        p = self.p
        self.t += len(block) / self.sr
        raw = float(np.sqrt(np.mean(block * block)))
        rms = raw
        gt = p.gate_thr
        if gt > 0:  
            if raw >= gt:
                self.gate_until = self.t + GATE_HOLD
            if self.t > self.gate_until:
                block = np.zeros_like(block)
                rms = 0.0

        if self.collecting:
            self.buf.append(block.copy())
            self.have += len(block)
            if self.have >= self.need:
                x = np.concatenate(self.buf)[: self.need]
                self.collecting = False
                self.on_hit(estimate_pitch(x, self.sr))
        else:
            base = self._env(len(block))
            if (rms > p.threshold and rms > p.ratio * base
                    and (self.t - self.last) * 1000.0 >= p.deadzone_ms):
                self.last = self.t
                self.collecting = True
                self.buf = []
                self.have = 0
                self.need = max(64, int(self.sr * p.window_ms / 1000.0))
        self.hist.append(rms)

        if self.note_active and not self.collecting:
            if self._env(len(block)) < p.threshold * p.release_pct / 100.0:
                self.note_active = False
                if self.on_release:
                    self.on_release()
        return raw


class Engine:
    def __init__(self, ui_queue):
        self.q = ui_queue
        self.params = Params()
        self.sender = None
        self.slots = [] 
        self.enabled = True
        self.calibrating = False
        self.unrec_last = False
        self.long_notes = False
        self.held = None
        self.lock = threading.RLock()
        self.last_slot = None
        self.alt = {}
        self.level = 0.0
        self.stream = None
        self.det = None
        self.col = 0
        self.asio = False
        self.sr = 48000
        self.block = 64

    def ensure_sender(self):
        if self.sender is None and IS_WIN:
            self.sender = KeySender()
            try:
                ctypes.windll.winmm.timeBeginPeriod(1)
            except Exception:
                pass

    def press(self, keys, slot_index=None):
        if not keys or self.sender is None:
            return
        n = self.alt.get(slot_index, 0)
        sc, ext = keys[n % len(keys)]
        self.alt[slot_index] = n + 1
        if self.long_notes and not isinstance(slot_index, tuple):
            with self.lock:
                self._release_locked()
                self.sender.down(sc, ext)
                self.held = (sc, ext)
            if self.det is not None:
                self.det.note_active = True
        else:
            self.sender.tap(sc, ext)

    def _release_locked(self):
        if self.held is not None and self.sender is not None:
            self.sender.up(*self.held)
        self.held = None
        if self.det is not None:
            self.det.note_active = False

    def release(self):
        with self.lock:
            self._release_locked()

    def set_long_notes(self, flag):
        flag = bool(flag)
        if self.long_notes and not flag:
            self.release()
        self.long_notes = flag

    # --- hit
    def handle_hit(self, freq):
        if self.calibrating:
            self.q.put(("calib", freq))
            return
        slots = self.slots
        if freq is None:
            if self.unrec_last and self.last_slot is not None:
                idx = self.last_slot
            else:
                self.q.put(("hit", None, None))
                return
        else:
            idx = classify(freq, slots)
            if idx is None:
                self.q.put(("hit", None, freq))
                return
            self.last_slot = idx
        if self.enabled:
            for i, _f, keys in slots:
                if i == idx:
                    self.press(keys, idx)
                    break
        self.q.put(("hit", idx, freq))

    def _cb(self, indata, frames, t, status):
        try:
            col = min(self.col, indata.shape[1] - 1)
            self.level = self.det.process(indata[:, col])
        except Exception:
            pass

    def start(self, dev_index, channel, block):
        if sd is None:
            raise RuntimeError("Sounddevice library is not installed (pip install sounddevice)")
        dev = sd.query_devices(dev_index, "input")
        api = sd.query_hostapis(dev["hostapi"])["name"]
        self.sr = int(dev["default_samplerate"])
        self.block = block
        channels = max(int(dev["max_input_channels"]), channel + 1)
        extra = None
        self.col = channel
        self.asio = "ASIO" in api
        if self.asio:
            extra = sd.AsioSettings(channel_selectors=[channel])
            channels, self.col = 1, 0
        self.ensure_sender()
        self.det = Detector(self.sr, self.params, self.handle_hit, self.release)
        self.stream = sd.InputStream(
            device=dev_index, channels=channels, samplerate=self.sr,
            blocksize=block, dtype="float32", latency="low",
            extra_settings=extra, callback=self._cb)
        self.stream.start()
        return f"{self.sr} Hz, {channels} ch., buffer {block}"

    def stop(self):
        self.release()
        if self.stream is not None:
            try:
                self.stream.stop()
                self.stream.close()
            except Exception:
                pass
            self.stream = None
        self.level = 0.0


def make_key(sc, ext=False):
    return {"sc": sc, "ext": ext, "name": key_name(sc, ext)}


def new_slot(freq=None, key=None):
    return {"freq": freq, "spread": None, "key": key}


def default_profile():
    return {
        "device": "", "channel": 0, "block": 64,
        "sensitivity": 41, "deadzone_ms": 40, "window_ms": 30, "ratio": 1.8,
        "gate_db": GATE_OFF_DB, "long_notes": False, "release_pct": 60,
        "unrecognized": "ignore",
        "slots": [new_slot(84.0, make_key(0x21)),
                  new_slot(112.0, make_key(0x20))],
    }


def normalize_profile(p):
    for k, v in default_profile().items():
        p.setdefault(k, copy.deepcopy(v))
    for s in p["slots"]:
        for k, v in new_slot().items():
            s.setdefault(k, v)
        s.pop("key2", None)
        for kk in ("key",):
            if s[kk]:
                s[kk]["ext"] = bool(s[kk].get("ext", False))
                s[kk]["name"] = key_name(s[kk]["sc"], s[kk]["ext"])
    while len(p["slots"]) < 1:
        p["slots"].append(new_slot())
    p["deadzone_ms"] = max(0, min(DEADZONE_MAX, int(p["deadzone_ms"])))
    return p


def load_config():
    cfg = {}
    for path in (CONFIG_PATH,):
        try:
            cfg = json.loads(path.read_text(encoding="utf-8"))
            break
        except Exception:
            continue
    if not isinstance(cfg.get("profiles"), dict) or not cfg["profiles"]:
        cfg["profiles"] = {DEFAULT_NAME: default_profile()}
    for name in list(cfg["profiles"]):
        cfg["profiles"][name] = normalize_profile(cfg["profiles"][name])
    if DEFAULT_NAME not in cfg["profiles"]:
        cfg["profiles"] = {DEFAULT_NAME: default_profile(), **cfg["profiles"]}
    if cfg.get("current") not in cfg["profiles"]:
        cfg["current"] = next(iter(cfg["profiles"]))
    cfg.setdefault("pause_key", "F9")
    if cfg.get("theme") not in ("dark", "light"):
        cfg["theme"] = "dark"
    return cfg


BG = ("#f5f2fb", "#110e1a")
CARD = ("#ffffff", "#1a1626")
CARD2 = ("#efe9f9", "#251f36")
BORDER = ("#dcd3ee", "#342c4b")
TEXT = ("#1c1730", "#ece8f7")
MUTED = ("#6f6890", "#9d95b8")
ACCENT = ("#7c3aed", "#8b5cf6")
ACCENT_H = ("#6d28d9", "#7c3aed")
BTN = ("#e7e0f5", "#2c2542")
BTN_H = ("#d9cff0", "#3a3158")
OKC = ("#1f9d57", "#34c56f")
DANGER = ("#d64545", "#e5534b")
DANGER_H = ("#b83a3a", "#c9453d")
AMBER = ("#d98e04", "#f0a500")
DIM = ("#a39cb8", "#6b6385")
INACTIVE = ("#c4bbdb", "#4b4368")
FONT = "Segoe UI"

DEVICE_HELP = (
    "The list shows the driver type in brackets after the device name.\n\n"
    "WDM-KS — the fastest available. Works directly with the device driver, bypassing the "
    "Windows mixer, so latency is minimal. Usually takes over the device entirely (other programs "
    "cannot use it at the same time) and is sensitive to buffer size. The best choice for gaming.\n\n"
    "WASAPI — modern Windows audio layer. Low latency, works stably and coexists peacefully "
    "with other programs. A good fallback option if WDM-KS fails to open.\n\n"
    "DirectSound — legacy layer. Noticeably higher latency (tens of milliseconds). Only choose this "
    "if the two options above don't work.\n\n"
    "MME — the oldest and slowest, latency is usually 50–100 ms and higher. Not suitable for gaming.\n\n"
    "Order from best to worst: WDM-KS → WASAPI → DirectSound → MME."
)

_Base = ctk.CTk if ctk else object
_TopBase = ctk.CTkToplevel if ctk else object
_FrameBase = ctk.CTkFrame if ctk else object


def center_window(win):
    win.update_idletasks()
    w, h = win.winfo_reqwidth(), win.winfo_reqheight()
    x = max(0, (win.winfo_screenwidth() - w) // 2)
    y = max(0, (win.winfo_screenheight() - h) // 2)
    tk.Wm.wm_geometry(win, f"+{x}+{y}")


class RoundCombo(_FrameBase):
    ROW_H = 32
    MAX_ROWS = 8

    def __init__(self, parent, app, variable, values, width, command=None):
        super().__init__(parent, fg_color="transparent")
        self.app = app
        self.var = variable
        self.values = list(values)
        self.command = command
        self.width = width
        self.enabled = True
        self.popup = None
        self.btn = ctk.CTkButton(
            self, text="", width=width, height=32, corner_radius=8, fg_color=CARD2, hover_color=BTN,
            border_width=1, border_color=BORDER, text_color=TEXT, anchor="w", font=app.font(13),
            command=self.toggle)
        self.btn.grid(row=0, column=0)
        self.arrow = ctk.CTkLabel(self, text="▾", width=16, height=16, fg_color="transparent",
                                  text_color=MUTED, font=app.font(14))
        self.arrow.place(relx=1.0, x=-14, rely=0.5, anchor="e")
        self.arrow.bind("<Button-1>", lambda e: self.toggle())
        self.var.trace_add("write", lambda *a: self._refresh())
        self.winfo_toplevel().bind("<Button-1>", self._on_root_click, add="+")
        self._refresh()

    def _fit(self, text, px):
        limit = max(8, int(px / 7.6) - 4)
        return text if len(text) <= limit else text[: limit - 1] + "…"

    def _refresh(self):
        try:
            self.btn.configure(text=self._fit(str(self.var.get()), self.width))
        except Exception:
            pass

    def configure(self, require_redraw=False, **kw):
        if "values" in kw:
            self.values = list(kw.pop("values"))
        if "state" in kw:
            self.enabled = kw.pop("state") != "disabled"
            self.btn.configure(state="normal" if self.enabled else "disabled")
            self.arrow.configure(text_color=MUTED if self.enabled else DIM)
        if kw or require_redraw:
            super().configure(require_redraw=require_redraw, **kw)

    def toggle(self):
        if not self.enabled:
            return
        if self.popup is not None:
            self.close()
        else:
            self.open()

    def _on_root_click(self, event):
        if self.popup is None:
            return
        w, me = str(event.widget), str(self)
        if w == me or w.startswith(me + "."):
            return
        self.close()

    def close(self):
        pop, self.popup = self.popup, None
        if pop is None:
            return
        try:
            pop.withdraw()
        except Exception:
            pass

        def kill():
            try:
                pop.destroy()
            except Exception:
                pass
        self.after(160, kill)

    def pick(self, value):
        self.var.set(value)
        self.close()
        if self.command:
            self.command(value)

    def open(self):
        dark = ctk.get_appearance_mode() == "Dark"
        magic = "#110e1a" if dark else "#f5f2fb"
        top = self.winfo_toplevel()
        pop = tk.Toplevel(top)
        pop.withdraw()
        pop.overrideredirect(True)
        pop.configure(bg=magic)
        try:
            pop.attributes("-transparentcolor", magic)
        except Exception:
            pass
        pop.transient(top)
        self.popup = pop
        longest = max([len(str(v)) for v in self.values] + [1])
        pw = int(min(max(self.width, longest * 7.6 + 48), 560))
        frame = ctk.CTkFrame(pop, fg_color=CARD2, border_color=BORDER, border_width=1,
                             corner_radius=12, bg_color=magic)
        frame.pack(padx=2, pady=2)
        if len(self.values) > self.MAX_ROWS:
            kw = dict(width=pw - 28, height=self.ROW_H * self.MAX_ROWS, fg_color="transparent")
            try:
                holder = ctk.CTkScrollableFrame(
                    frame, scrollbar_button_color=BTN_H, scrollbar_button_hover_color=ACCENT, **kw)
            except TypeError:
                holder = ctk.CTkScrollableFrame(frame, **kw)
        else:
            holder = ctk.CTkFrame(frame, fg_color="transparent")
        holder.pack(padx=6, pady=6)
        cur = self.var.get()
        for v in self.values:
            sel = v == cur
            ctk.CTkButton(
                holder, text=self._fit(str(v), pw - 28), anchor="w", width=pw - 28, height=30,
                corner_radius=8, fg_color=ACCENT if sel else "transparent",
                hover_color=ACCENT_H if sel else BTN_H, text_color="white" if sel else TEXT,
                font=self.app.font(13), command=lambda v=v: self.pick(v)).pack(pady=1)
        pop.update_idletasks()
        x = self.winfo_rootx()
        y = self.winfo_rooty() + self.winfo_height() + 4
        ph = pop.winfo_reqheight()
        if y + ph > pop.winfo_screenheight() - 40:
            y = max(0, self.winfo_rooty() - ph - 4)
        pop.geometry(f"+{x}+{y}")
        pop.deiconify()
        pop.bind("<Escape>", lambda e: self.close())


class Dialog(_TopBase):
    
    def __init__(self, app, title, text, buttons, entry=False, wrap=420):
        super().__init__(app, fg_color=BG)
        self.title(title)
        self.resizable(False, False)
        self.transient(app)
        self.result = None
        self._entry = None
        self._default = buttons[-1][1]
        body = ctk.CTkFrame(self, fg_color=CARD, corner_radius=14, border_width=1, border_color=BORDER)
        body.grid(row=0, column=0, padx=14, pady=14)
        app.label(body, title, 15, True).grid(row=0, column=0, sticky="w", padx=20, pady=(16, 4))
        app.label(body, text, 13, False, MUTED, wraplength=wrap, justify="left", anchor="w").grid(
            row=1, column=0, sticky="w", padx=20, pady=(0, 10))
        row = 2
        if entry:
            self._entry = ctk.CTkEntry(body, width=wrap, height=34, corner_radius=8, fg_color=CARD2,
                                       border_color=BORDER, text_color=TEXT, font=app.font(13))
            self._entry.grid(row=2, column=0, padx=20, pady=(0, 10))
            row = 3
        bar = ctk.CTkFrame(body, fg_color="transparent")
        bar.grid(row=row, column=0, sticky="e", padx=16, pady=(4, 16))
        for col, (label, value, kind) in enumerate(buttons):
            app.button(bar, label, lambda v=value: self.finish(v), kind, 120, 34).grid(row=0, column=col, padx=4)
        self.bind("<Escape>", lambda e: self.finish(None if entry else False))
        self.bind("<Return>", lambda e: self.finish(self._default))
        self.protocol("WM_DELETE_WINDOW", lambda: self.finish(None if entry else False))
        center_window(self)
        self.after(80, self._grab)

    def _grab(self):
        try:
            self.lift()
            self.grab_set()
            self.focus_force()
            if self._entry is not None:
                self._entry.focus()
        except Exception:
            pass

    def finish(self, value):
        if self._entry is not None:
            self.result = self._entry.get() if value else None
        else:
            self.result = value
        try:
            self.grab_release()
        except Exception:
            pass
        self.destroy()

    def show(self):
        self.master.wait_window(self)
        return self.result


class App(_Base):
    def __init__(self):
        self.cfg = load_config()
        ctk.set_appearance_mode(self.cfg["theme"])
        ctk.set_default_color_theme("blue")
        super().__init__(fg_color=BG)
        self.title(APP_NAME)
        self.resizable(False, False)
        if IS_WIN:
            try:
                ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("phrq.guitar2key.app.1")
            except Exception:
                pass
        if IS_WIN:
            try:
                ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("phrq.guitar2key.app.1")
            except Exception:
                pass

        icon_ico = BASE / "assets" / "icon.ico"
        if icon_ico.exists():
            try:
                self.iconbitmap(str(icon_ico))
            except Exception as e:
                print(f"Не удалось загрузить иконку: {e}")
        self.q = queue.Queue()
        self.engine = Engine(self.q)
        self.prof = self.cfg["profiles"][self.cfg["current"]]
        self.running = False
        self.paused = False
        self.capture = None
        self.calib_slot = None
        self.calib_vals = []
        self.hits = 0
        self.dirty = False
        self.pause_prev = False
        self.disp = 0.0
        self.status_text = ""
        self._loading = True
        self.dev_map = {}
        self.num_labels, self.freq_labels = [], []
        self.key_btns, self.key2_btns, self.calib_btns = [], [], []
        self.val_labels = []
        self.meter_w = 470

        self.v_prof = tk.StringVar()
        self.v_device = tk.StringVar()
        self.v_channel = tk.StringVar(value="1")
        self.v_block = tk.StringVar(value="64")
        self.v_sens = tk.DoubleVar()
        self.v_gate = tk.DoubleVar()
        self.v_dead = tk.DoubleVar()
        self.v_win = tk.DoubleVar()
        self.v_ratio = tk.DoubleVar()
        self.v_rel = tk.DoubleVar()
        self.v_long = tk.BooleanVar(value=False)
        self.v_unrec = tk.StringVar(value=UNREC[0])
        self.v_pause = tk.StringVar(value=self.cfg["pause_key"])

        self._build()
        self.refresh_devices()
        self.load_profile_to_ui()
        self.bind("<KeyPress>", self.on_key)
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        center_window(self)
        self.after(30, self.tick)
        self.after(3000, self.autosave)

    def font(self, size=13, bold=False):
        return ctk.CTkFont(family=FONT, size=size, weight="bold" if bold else "normal")

    def label(self, parent, text="", size=13, bold=False, color=TEXT, **kw):
        return ctk.CTkLabel(parent, text=text, text_color=color, font=self.font(size, bold), **kw)

    def button(self, parent, text, command, kind="secondary", width=100, height=32, **kw):
        if kind == "accent":
            fg, hv, tc = ACCENT, ACCENT_H, "white"
        elif kind == "danger":
            fg, hv, tc = DANGER, DANGER_H, "white"
        else:
            fg, hv, tc = BTN, BTN_H, TEXT
        return ctk.CTkButton(parent, text=text, command=command, width=width, height=height,
                             corner_radius=8, fg_color=fg, hover_color=hv, text_color=tc,
                             font=self.font(13, kind != "secondary"), **kw)

    def combo(self, parent, variable, values, width, command=None):
        return RoundCombo(parent, self, variable, values, width, command)

    def card(self, parent, title):
        f = ctk.CTkFrame(parent, fg_color=CARD, corner_radius=14, border_width=1, border_color=BORDER)
        self.label(f, title, 14, True).grid(row=0, column=0, columnspan=6, sticky="w", padx=16, pady=(12, 6))
        return f

    def add_slider(self, parent, row, text, var, lo, hi, fmt):
        name = self.label(parent, text, 13, False)
        name.grid(row=row, column=0, sticky="w", padx=(16, 8), pady=5)
        slider = ctk.CTkSlider(parent, from_=lo, to=hi, variable=var, width=230, height=16,
                               command=lambda _v: self.on_param(), progress_color=ACCENT,
                               button_color=ACCENT, button_hover_color=ACCENT_H, fg_color=BTN)
        slider.grid(row=row, column=1, sticky="w", pady=5)
        lbl = self.label(parent, "", 13, True, width=70, anchor="e")
        lbl.grid(row=row, column=2, sticky="e", padx=(6, 16))
        self.val_labels.append((lbl, var, fmt))
        return name, slider, lbl

    def ask(self, title, text, buttons, entry=False, wrap=420):
        return Dialog(self, title, text, buttons, entry, wrap).show()

    def info(self, title, text, wrap=420):
        self.ask(title, text, [("OK", True, "accent")], wrap=wrap)

    def confirm(self, title, text, yes="Yes", danger=True):
        return bool(self.ask(title, text, [("No", False, "secondary"),
                                           (yes, True, "danger" if danger else "accent")]))

    def ask_text(self, title, text, ok="Create"):
        return self.ask(title, text, [("Cancel", None, "secondary"), (ok, True, "accent")], entry=True)


    def _build(self):
        self.grid_columnconfigure(0, weight=1)

        hdr = ctk.CTkFrame(self, fg_color="transparent")
        hdr.grid(row=0, column=0, sticky="ew", padx=18, pady=(16, 10))
        hdr.grid_columnconfigure(2, weight=1)
        self.label(hdr, APP_NAME, 24, True).grid(row=0, column=0, sticky="w")
        self.label(hdr, "v1.0 by Phrq", 13, False, MUTED).grid(row=0, column=1, sticky="w", padx=12)
        self.lbl_status = self.label(hdr, "Stopped", 13, True, MUTED, width=330, height=30,
                                     corner_radius=15, fg_color=BTN)
        self.lbl_status.grid(row=0, column=3, padx=8)
        self.btn_start = self.button(hdr, "▶  Start", self.toggle_run, "accent", 120, 36)
        self.btn_start.grid(row=0, column=4, padx=4)
        self.btn_pause = self.button(hdr, "⏸  Pause", self.toggle_pause, "secondary", 120, 36)
        self.btn_pause.grid(row=0, column=5, padx=4)
        self.seg_theme = ctk.CTkSegmentedButton(
            hdr, values=["Dark", "Light"], command=self.on_theme, height=32,
            fg_color=CARD2, selected_color=ACCENT, selected_hover_color=ACCENT_H,
            unselected_color=CARD2, unselected_hover_color=BTN_H, text_color=TEXT,
            font=self.font(12))
        self.seg_theme.grid(row=0, column=6, padx=(10, 0))
        self.seg_theme.set("Light" if self.cfg["theme"] == "light" else "Dark")

        body = ctk.CTkFrame(self, fg_color="transparent")
        body.grid(row=1, column=0, sticky="nsew", padx=18, pady=(0, 18))
        body.grid_columnconfigure(0, weight=1, uniform="cols")
        body.grid_columnconfigure(1, weight=1, uniform="cols")

        c = self.card(body, "Audio")
        c.grid(row=0, column=0, sticky="nsew", padx=(0, 6), pady=(0, 6))
        self.label(c, "Device", 13, False, MUTED).grid(row=1, column=0, sticky="w", padx=(16, 8), pady=4)
        self.cb_dev = self.combo(c, self.v_device, [], 290, lambda v: self.on_param())
        self.cb_dev.grid(row=1, column=1, sticky="w", pady=4)
        self.btn_refresh = self.button(c, "⟳", self.refresh_devices, "secondary", 34, 32)
        self.btn_refresh.grid(row=1, column=2, padx=(6, 0))
        self.button(c, "i", self.show_device_help, "secondary", 34, 32).grid(row=1, column=3, padx=(6, 16))
        r = ctk.CTkFrame(c, fg_color="transparent")
        r.grid(row=2, column=0, columnspan=4, sticky="w", padx=16, pady=(4, 14))
        self.label(r, "Channel", 13, False, MUTED).grid(row=0, column=0, padx=(0, 6))
        self.cb_ch = self.combo(r, self.v_channel, ["1", "2"], 66, lambda v: self.on_param())
        self.cb_ch.grid(row=0, column=1)
        self.label(r, "Buffer", 13, False, MUTED).grid(row=0, column=2, padx=(16, 6))
        self.cb_blk = self.combo(r, self.v_block, BLOCKS, 84, lambda v: self.on_param())
        self.cb_blk.grid(row=0, column=3)
        self.label(r, "Pause key", 13, False, MUTED).grid(row=0, column=4, padx=(16, 6))
        self.combo(r, self.v_pause, [f"F{i}" for i in range(6, 13)], 76,
                   lambda v: self.on_param()).grid(row=0, column=5)

        c = self.card(body, "Settings")
        c.grid(row=1, column=0, rowspan=2, sticky="nsew", padx=(0, 6), pady=(6, 0))
        self.meter = tk.Canvas(c, width=self.meter_w, height=26, highlightthickness=0, bd=0)
        self.meter.grid(row=1, column=0, columnspan=3, padx=16, pady=(2, 2), sticky="w")
        self.label(c, "red line: hit threshold · purple line: noise gate threshold", 12, False, MUTED).grid(
            row=2, column=0, columnspan=3, sticky="w", padx=16, pady=(0, 6))
        self.add_slider(c, 3, "Sensitivity", self.v_sens, 0, 100, lambda v: f"{v:.0f}")
        self.add_slider(c, 4, "Noise gate", self.v_gate, GATE_OFF_DB, -20,
                        lambda v: "off" if v <= GATE_OFF_DB + 0.5 else f"{v:.0f} dB")
        self.add_slider(c, 5, "Deadzone", self.v_dead, 0, DEADZONE_MAX, lambda v: f"{v:.0f} ms")
        self.add_slider(c, 6, "Note analysis window", self.v_win, 5, 40, lambda v: f"{v:.0f} ms")
        self.add_slider(c, 7, "Rise threshold", self.v_ratio, 1.1, 4.0, lambda v: f"×{v:.1f}")
        self.label(c, "Unrecognized hit", 13, False).grid(row=8, column=0, sticky="w", padx=(16, 8), pady=5)
        self.combo(c, self.v_unrec, UNREC, 230, lambda v: self.on_param()).grid(row=8, column=1, sticky="w")
        self.sw_long = ctk.CTkSwitch(
            c, text="Long notes (hold key while sounding)", variable=self.v_long,
            command=self.on_param, progress_color=ACCENT, button_color="white",
            button_hover_color="#e8e8e8", fg_color=BTN, text_color=TEXT, font=self.font(13))
        self.sw_long.grid(row=9, column=0, columnspan=3, sticky="w", padx=16, pady=(8, 2))
        self.rel_widgets = self.add_slider(c, 10, "Note release", self.v_rel, 20, 100,
                                           lambda v: f"{v:.0f}%")
        self.lbl_lat = self.label(c, "", 12, False, MUTED, wraplength=470, justify="left", anchor="nw",
                                  height=52)
        self.lbl_lat.grid(row=11, column=0, columnspan=3, sticky="nw", padx=16, pady=(4, 14))

        c = self.card(body, "Profile")
        c.grid(row=0, column=1, sticky="nsew", padx=(6, 0), pady=(0, 6))
        self.cb_prof = self.combo(c, self.v_prof, [], 200, lambda v: self.switch_profile(v))
        self.cb_prof.grid(row=1, column=0, padx=(16, 6), pady=(0, 6), sticky="w")
        self.btn_pnew = self.button(c, "New profile", self.new_profile, "secondary", 140)
        self.btn_pnew.grid(row=1, column=1, padx=4, pady=(0, 6))
        self.btn_pdel = self.button(c, "Delete profile", self.delete_profile, "secondary", 150)
        self.btn_pdel.grid(row=1, column=2, padx=(4, 16), pady=(0, 6))
        self.label(c, "changes are saved to the profile automatically", 12, False, MUTED).grid(
            row=2, column=0, columnspan=3, sticky="w", padx=16, pady=(0, 14))

        c = self.card(body, "Buttons")
        c.grid(row=1, column=1, sticky="nsew", padx=(6, 0), pady=6)
        c.grid_columnconfigure(0, weight=1)
        c.grid_rowconfigure(1, weight=1)
        kw = dict(width=520, height=236, fg_color="transparent")
        try:
            self.slots_frame = ctk.CTkScrollableFrame(
                c, scrollbar_button_color=BTN_H, scrollbar_button_hover_color=ACCENT, **kw)
        except TypeError: 
            self.slots_frame = ctk.CTkScrollableFrame(c, **kw)
        self.slots_frame.grid(row=1, column=0, columnspan=2, sticky="nsew", padx=(10, 6))
        self.slots_frame.grid_columnconfigure(1, weight=1)
        self.btn_add = None
        self.lbl_warn = self.label(c, "", 12, False, DANGER, wraplength=520, justify="left",
                                   anchor="nw", height=36)
        self.lbl_warn.grid(row=2, column=0, columnspan=2, sticky="nw", padx=16, pady=(6, 12))

        c = self.card(body, "Monitor")
        c.grid(row=2, column=1, sticky="nsew", padx=(6, 0), pady=(6, 0))
        self.lbl_last = self.label(c, "—", 40, True, ACCENT, width=90)
        self.lbl_last.grid(row=1, column=0, padx=(16, 8), pady=(0, 12))
        self.lbl_hit_info = self.label(c, "hits: 0", 13, False, MUTED, anchor="w")
        self.lbl_hit_info.grid(row=1, column=1, sticky="w", pady=(0, 12))

    def show_device_help(self):
        self.info("Which driver to choose", DEVICE_HELP, wrap=540)

    def refresh_devices(self):
        items = []
        if sd is not None:
            try:
                apis = sd.query_hostapis()
                for i, d in enumerate(sd.query_devices()):
                    if d["max_input_channels"] > 0:
                        api = apis[d["hostapi"]]["name"].replace("Windows ", "")
                        order = API_ORDER.index(api) if api in API_ORDER else 9
                        items.append((order, f"{d['name']} [{api}]", i))
            except Exception:
                pass
        items.sort(key=lambda t: (t[0], t[2]))
        self.dev_map = {label: i for _o, label, i in items}
        self.cb_dev.configure(values=list(self.dev_map))
        if self.v_device.get() not in self.dev_map and self.dev_map:
            self.v_device.set(self.pick_default_device())

    def pick_default_device(self):
        labels = list(self.dev_map)
        for needle in ("GP-5 Audio", "GP-5"):
            for lb in labels:
                if needle in lb and "WDM-KS" in lb:
                    return lb
        for lb in labels:
            if "GP-5" in lb:
                return lb
        return labels[0]

    def load_profile_to_ui(self):
        self._loading = True
        p = self.prof
        self.cb_prof.configure(values=list(self.cfg["profiles"]))
        self.v_prof.set(self.cfg["current"])
        if p["device"] in self.dev_map:
            self.v_device.set(p["device"])
        elif self.dev_map:
            self.v_device.set(self.pick_default_device())
        self.v_channel.set(str(p["channel"] + 1))
        self.v_block.set(str(p["block"]))
        self.v_sens.set(p["sensitivity"])
        self.v_gate.set(p["gate_db"])
        self.v_dead.set(p["deadzone_ms"])
        self.v_win.set(p["window_ms"])
        self.v_ratio.set(p["ratio"])
        self.v_rel.set(p["release_pct"])
        self.v_long.set(bool(p["long_notes"]))
        self.v_unrec.set(UNREC[1] if p["unrecognized"] == "last" else UNREC[0])
        self.rebuild_slots()
        self.update_profile_buttons()
        self._loading = False
        self.on_param()

    def update_profile_buttons(self):
        if self.cfg["current"] == DEFAULT_NAME:
            self.btn_pdel.configure(text="Reset profile", command=self.reset_profile)
        else:
            self.btn_pdel.configure(text="Delete profile", command=self.delete_profile)

    def with_restart(self, action):
        self.cancel_calib()
        was_running = self.running
        if was_running:
            self.stop()
        action()
        if was_running:
            self.start()

    def switch_profile(self, name):
        if name not in self.cfg["profiles"] or name == self.cfg["current"]:
            return
        self.save_config()

        def go():
            self.cfg["current"] = name
            self.prof = self.cfg["profiles"][name]
            self.load_profile_to_ui()
        self.with_restart(go)
        self.save_config()

    def new_profile(self):
        name = self.ask_text("New profile", "Profile name:")
        if name is None:
            return
        name = name.strip()[:30]
        if not name:
            self.info("New profile", "Name cannot be empty.")
            return
        if name in self.cfg["profiles"]:
            self.info("New profile", f"Profile '{name}' already exists. Choose another name.")
            return
        cur = self.prof
        p = default_profile()
        p["device"], p["channel"], p["block"] = cur["device"], cur["channel"], cur["block"]
        p["slots"] = [new_slot(None, make_key(0x21)), new_slot(None, make_key(0x20))]
        self.cfg["profiles"][name] = p
        self.switch_profile(name)

    def reset_profile(self):
        if not self.confirm("Reset profile",
                            f"Reset profile '{DEFAULT_NAME}' to factory settings?\n"
                            f"Recorded notes, keys, and all sliders will revert to defaults.",
                            "Yes, reset"):
            return
        if not self.confirm("Reset profile", "Are you sure you want to reset? This action cannot be undone.",
                            "Reset"):
            return

        def go():
            self.cfg["profiles"][DEFAULT_NAME] = normalize_profile(default_profile())
            self.prof = self.cfg["profiles"][DEFAULT_NAME]
            self.load_profile_to_ui()
        self.with_restart(go)
        self.save_config()

    def delete_profile(self):
        name = self.cfg["current"]
        if name == DEFAULT_NAME:
            return
        if not self.confirm("Delete profile", f"Delete profile '{name}'?", "Yes, delete"):
            return
        if not self.confirm("Delete profile",
                            f"Are you sure you want to delete '{name}'? This action cannot be undone.", "Delete"):
            return

        def go():
            del self.cfg["profiles"][name]
            self.cfg["current"] = DEFAULT_NAME
            self.prof = self.cfg["profiles"][DEFAULT_NAME]
            self.load_profile_to_ui()
        self.with_restart(go)
        self.save_config()

    def on_param(self, *_):
        if self._loading:
            return
        p = self.prof
        p["device"] = self.v_device.get()
        p["channel"] = int(self.v_channel.get()) - 1
        p["block"] = int(self.v_block.get())
        p["sensitivity"] = int(round(self.v_sens.get()))
        p["gate_db"] = int(round(self.v_gate.get()))
        p["deadzone_ms"] = int(round(self.v_dead.get()))
        p["window_ms"] = int(round(self.v_win.get()))
        p["ratio"] = round(self.v_ratio.get(), 1)
        p["release_pct"] = int(round(self.v_rel.get()))
        p["long_notes"] = bool(self.v_long.get())
        p["unrecognized"] = "last" if self.v_unrec.get() == UNREC[1] else "ignore"
        self.cfg["pause_key"] = self.v_pause.get()
        self.dirty = True
        self.push_params()

    def set_release_enabled(self, enabled):
        name, slider, val = self.rel_widgets
        if enabled:
            slider.configure(state="normal", progress_color=ACCENT, button_color=ACCENT,
                             button_hover_color=ACCENT_H)
            name.configure(text_color=TEXT)
            val.configure(text_color=TEXT)
        else:
            slider.configure(state="disabled", progress_color=INACTIVE, button_color=INACTIVE,
                             button_hover_color=INACTIVE)
            name.configure(text_color=DIM)
            val.configure(text_color=DIM)

    def push_params(self):
        p = self.prof
        e = self.engine
        e.params.sensitivity = p["sensitivity"]
        e.params.gate_db = p["gate_db"]
        e.params.deadzone_ms = p["deadzone_ms"]
        e.params.window_ms = p["window_ms"]
        e.params.ratio = p["ratio"]
        e.params.release_pct = p["release_pct"]
        e.col = 0 if e.asio else p["channel"]
        e.unrec_last = p["unrecognized"] == "last"
        e.set_long_notes(p["long_notes"])
        self.set_release_enabled(p["long_notes"])
        for lbl, var, fmt in self.val_labels:
            lbl.configure(text=fmt(var.get()))
        sr = e.sr if self.running else 48000
        total = p["window_ms"] + p["block"] / sr * 1000.0
        eff = max(p["deadzone_ms"], p["window_ms"])
        self.lbl_lat.configure(
            text=f"Latency ≈ {total:.0f} ms (+ driver). Real minimum between "
                 f"hits ≈ {eff:.0f} ms.")
        self.sync_slots_to_engine()

    def on_theme(self, value):
        mode = "light" if value == "Light" else "dark"
        ctk.set_appearance_mode(mode)
        self.cfg["theme"] = mode
        self.dirty = True

    def rebuild_slots(self):
        sf = self.slots_frame
        for w in sf.winfo_children():
            w.destroy()
        self.num_labels, self.freq_labels = [], []
        self.key_btns, self.calib_btns = [], []
        self.btn_add = None
        self.label(sf, "Note", 12, False, MUTED).grid(row=0, column=1, padx=4, sticky="w")
        self.label(sf, "Key", 12, False, MUTED, width=96, anchor="center").grid(row=0, column=3, padx=4)
        n = len(self.prof["slots"])
        for i, s in enumerate(self.prof["slots"]):
            row = i + 1
            nl = self.label(sf, str(i + 1), 15, True, width=32, height=32, corner_radius=16, fg_color=CARD2)
            nl.grid(row=row, column=0, padx=4, pady=4)
            fl = self.label(sf, "", 13, False, width=170, anchor="w")
            fl.grid(row=row, column=1, padx=4, sticky="w")
            cb = self.button(sf, "Record", lambda i=i: self.calib_toggle(i), "secondary", 96, 30)
            cb.grid(row=row, column=2, padx=4)
            kb = self.button(sf, "", lambda i=i: self.start_capture(i, "key"), "secondary", 96, 30)
            kb.grid(row=row, column=3, padx=4)
            if i >= 1:
                self.button(sf, "Delete", lambda i=i: self.remove_slot(i), "secondary", 80, 30).grid(
                    row=row, column=4, padx=4)
            else: 
                ctk.CTkFrame(sf, fg_color="transparent", width=80, height=30).grid(row=row, column=4, padx=4)
            self.num_labels.append(nl)
            self.freq_labels.append(fl)
            self.key_btns.append(kb)
            self.calib_btns.append(cb)
            self.refresh_slot(i)
        if n < MAX_SLOTS:  
            self.btn_add = self.button(sf, "＋  Add button", self.add_slot, "secondary", 100, 34)
            self.btn_add.grid(row=n + 1, column=0, columnspan=5, sticky="ew", padx=4, pady=(8, 4))
        self.update_warning()

    def refresh_slot(self, i):
        s = self.prof["slots"][i]
        if self.calib_slot == i:
            self.freq_labels[i].configure(text=f"play… {len(self.calib_vals)}/{CALIB_N}")
            self.calib_btns[i].configure(text="Cancel", fg_color=DANGER, hover_color=DANGER_H, text_color="white")
        else:
            if s["freq"]:
                sp = f"  ±{s['spread'] * 100:.0f}%" if s.get("spread") is not None else ""
                self.freq_labels[i].configure(text=f"{s['freq']:.0f} Hz{sp}")
            else:
                self.freq_labels[i].configure(text="not recorded")
            self.calib_btns[i].configure(text="Record", fg_color=BTN, hover_color=BTN_H, text_color=TEXT)
        cap = self.capture == (i, "key")
        self.key_btns[i].configure(
            text="press…" if cap else (s["key"]["name"] if s["key"] else "not set"),
            fg_color=ACCENT if cap else BTN, text_color="white" if cap else TEXT)

    def sync_slots_to_engine(self):
        snap = []
        for i, s in enumerate(self.prof["slots"]):
            if s["freq"]:
                keys = [(s["key"]["sc"], s["key"].get("ext", False))] if s["key"] else []
                snap.append((i, float(s["freq"]), keys))
        self.engine.slots = snap
        self.engine.alt = {}

    def add_slot(self):
        if len(self.prof["slots"]) >= MAX_SLOTS:
            return
        self.prof["slots"].append(new_slot())
        self.rebuild_slots()
        self.dirty = True
        self.sync_slots_to_engine()

    def remove_slot(self, i):
        if i < 1 or i >= len(self.prof["slots"]): 
            return
        self.cancel_calib()
        del self.prof["slots"][i]
        self.rebuild_slots()
        self.dirty = True
        self.sync_slots_to_engine()

    def flash(self, i):
        if i is None or i >= len(self.num_labels):
            return
        lbl = self.num_labels[i]
        lbl.configure(fg_color=OKC, text_color="white")

        def reset():
            try:
                lbl.configure(fg_color=CARD2, text_color=TEXT)
            except Exception:
                pass
        self.after(130, reset)

    def update_warning(self):
        sl = [(i, s) for i, s in enumerate(self.prof["slots"]) if s["freq"]]
        sl.sort(key=lambda t: t[1]["freq"])
        msgs = []
        for (i, a), (j, b) in zip(sl, sl[1:]):
            gap = b["freq"] / a["freq"] - 1.0
            need = max(0.08, 1.5 * ((a.get("spread") or 0.03) + (b.get("spread") or 0.03)))
            if gap < need:
                msgs.append(f"⚠ Buttons {i + 1} and {j + 1} are too close in pitch — notes will get mixed up. "
                            f"Choose notes further apart.")
        for i, s in enumerate(self.prof["slots"]):
            if s["freq"] and (s.get("spread") or 0) > 0.10:
                msgs.append(f"⚠ Button {i + 1}: note is detected unreliably (±{s['spread'] * 100:.0f}%). "
                            f"Play cleaner, mute strings, or increase the analysis window.")
        self.lbl_warn.configure(text="\n".join(msgs))

    def start_capture(self, i, which):
        old = self.capture
        self.capture = (i, which)
        if old and old[0] < len(self.key_btns):
            self.refresh_slot(old[0])
        self.refresh_slot(i)
        self.focus_force()

    def on_key(self, e):
        if not self.capture:
            return
        i, which = self.capture
        self.capture = None
        if e.keysym != "Escape":
            sc = vk_to_scan(e.keycode)
            if sc:
                self.prof["slots"][i][which] = make_key(sc, e.keycode in EXT_VK)
                self.dirty = True
                self.sync_slots_to_engine()
        if i < len(self.key_btns):
            self.refresh_slot(i)
        return "break"

    def calib_toggle(self, i):
        if self.calib_slot == i:
            self.cancel_calib()
            return
        if not self.running:
            self.info("Calibration", "Click 'Start' first so the program listens to the guitar.")
            return
        self.cancel_calib()
        self.calib_slot = i
        self.calib_vals = []
        self.engine.calibrating = True
        self.refresh_slot(i)

    def cancel_calib(self):
        i = self.calib_slot
        self.calib_slot = None
        self.calib_vals = []
        self.engine.calibrating = False
        if i is not None and i < len(self.freq_labels):
            self.refresh_slot(i)

    def on_calib(self, freq):
        i = self.calib_slot
        if i is None:
            return
        if freq is None:
            self.freq_labels[i].configure(text="not recognized, try again")
            return
        self.calib_vals.append(freq)
        self.refresh_slot(i)
        self.freq_labels[i].configure(text=f"{len(self.calib_vals)}/{CALIB_N} · {freq:.0f} Hz")
        if len(self.calib_vals) >= CALIB_N:
            vals = self.calib_vals
            med = statistics.median(vals)
            good = [v for v in vals if 0.8 * med <= v <= 1.25 * med] or vals
            med = statistics.median(good)
            spread = (max(good) - min(good)) / 2.0 / med
            s = self.prof["slots"][i]
            s["freq"], s["spread"] = med, spread
            self.calib_slot = None
            self.calib_vals = []
            self.engine.calibrating = False
            self.dirty = True
            self.refresh_slot(i)
            self.update_warning()
            self.sync_slots_to_engine()

    def toggle_run(self):
        if self.running:
            self.stop()
        else:
            self.start()

    def start(self):
        label = self.v_device.get()
        if label not in self.dev_map:
            self.info("Device", "Select an input device from the list.")
            return
        try:
            info = self.engine.start(self.dev_map[label], self.prof["channel"], self.prof["block"])
        except Exception as ex:
            self.info(
                "Failed to open device",
                f"{ex}\n\nTry: buffer 128/256, another device option "
                f"(WASAPI instead of WDM-KS), close programs using the sound card.", wrap=480)
            return
        self.running = True
        self.btn_start.configure(text="■  Stop", fg_color=DANGER, hover_color=DANGER_H)
        self.cb_dev.configure(state="disabled")
        self.cb_blk.configure(state="disabled")
        self.btn_refresh.configure(state="disabled")
        self.status_text = info
        self.push_params()
        self.update_status()

    def stop(self):
        self.cancel_calib()
        self.engine.stop()
        self.running = False
        self.btn_start.configure(text="▶  Start", fg_color=ACCENT, hover_color=ACCENT_H)
        self.cb_dev.configure(state="readonly")
        self.cb_blk.configure(state="readonly")
        self.btn_refresh.configure(state="normal")
        self.update_status()

    def toggle_pause(self):
        self.paused = not self.paused
        self.engine.enabled = not self.paused
        if self.paused:
            self.engine.release()
        self.btn_pause.configure(text="▶  Resume" if self.paused else "⏸  Pause")
        self.update_status()

    def update_status(self):
        if not self.running:
            self.lbl_status.configure(text="Stopped", fg_color=BTN, text_color=MUTED)
        elif self.paused:
            self.lbl_status.configure(text=f"⏸ Paused — keys are not sent ({self.v_pause.get()})",
                                      fg_color=AMBER, text_color="white")
        else:
            self.lbl_status.configure(text=f"● Listening · {self.status_text}", fg_color=OKC, text_color="white")

    def tick(self):
        try:
            for _ in range(80):
                ev = self.q.get_nowait()
                if ev[0] == "hit":
                    _, idx, freq = ev
                    if idx is None:
                        self.lbl_last.configure(text="?")
                    else:
                        self.lbl_last.configure(text=str(idx + 1))
                        self.flash(idx)
                        self.hits += 1
                    self.lbl_hit_info.configure(
                        text=f"hits: {self.hits}" + (f"   ·   note: {freq:.0f} Hz" if freq else ""))
                elif ev[0] == "calib":
                    self.on_calib(ev[1])
        except queue.Empty:
            pass
        except Exception:
            pass
        try:
            lvl = self.engine.level if self.running else 0.0
            self.disp = max(lvl, self.disp * 0.88)
            self.draw_meter()
            self.poll_hotkey()
        except Exception:
            pass
        self.after(30, self.tick)

    def lvl_x(self, v):
        v = max(v, 1e-4)
        return int(max(0.0, min(1.0, (math.log10(v) + 4.0) / 4.0)) * self.meter_w)

    def draw_meter(self):
        dark = ctk.get_appearance_mode() == "Dark"
        c = self.meter
        c.configure(bg="#1a1626" if dark else "#ffffff")
        c.delete("all")
        c.create_rectangle(0, 0, self.meter_w, 26, fill="#251f36" if dark else "#e7e0f5", width=0)
        pr = self.engine.params
        x = self.lvl_x(self.disp)
        hot = self.disp > pr.threshold
        c.create_rectangle(0, 0, x, 26, width=0,
                           fill=("#f0a500" if hot else "#34c56f") if dark else ("#d98e04" if hot else "#1f9d57"))
        if pr.gate_thr > 0:
            gx = self.lvl_x(pr.gate_thr)
            c.create_line(gx, 0, gx, 26, fill="#b794ff" if dark else "#7c3aed", width=2)
        tx = self.lvl_x(pr.threshold)
        c.create_line(tx, 0, tx, 26, fill="#ff4d4f", width=3)

    def poll_hotkey(self):
        if not IS_WIN:
            return
        try:
            vk = 0x70 + int(self.v_pause.get()[1:]) - 1
        except Exception:
            return
        down = bool(ctypes.windll.user32.GetAsyncKeyState(vk) & 0x8000)
        if down and not self.pause_prev:
            self.toggle_pause()
        self.pause_prev = down

    def save_config(self):
        try:
            CONFIG_PATH.write_text(json.dumps(self.cfg, ensure_ascii=False, indent=2), encoding="utf-8")
            self.dirty = False
        except Exception:
            pass

    def autosave(self):
        if self.dirty:
            self.save_config()
        self.after(3000, self.autosave)

    def on_close(self):
        self.save_config()
        self.engine.stop()
        self.destroy()


def main():
    if ctk is None:
        msg = "Customtkinter library is not installed.\n\nRun in the console:\npip install customtkinter"
        print(msg)
        try:
            root = tk.Tk()
            root.withdraw()
            messagebox.showerror(APP_NAME, msg)
        except Exception:
            pass
        return
    App().mainloop()


if __name__ == "__main__":
    main()