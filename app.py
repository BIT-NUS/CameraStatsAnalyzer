"""
カメラ撮影統計アナライザー
フォルダ内の画像EXIFデータを解析し、ズーム域・ISO・絞り・
シャッタースピード・撮影時刻・カメラ機種などの統計グラフを表示する。
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import threading
from pathlib import Path
from collections import Counter
from datetime import datetime
import statistics
import math
import csv
import unicodedata

import exifread

import matplotlib
matplotlib.use("TkAgg")
matplotlib.rcParams["font.family"] = ["Yu Gothic", "MS Gothic", "Meiryo", "sans-serif"]
matplotlib.rcParams["axes.unicode_minus"] = False
import matplotlib.patches as mpatches
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk
from matplotlib.figure import Figure

from PIL import Image
from PIL.ExifTags import TAGS

# ─────────────────────────────────────────────
# 定数
# ─────────────────────────────────────────────
IMAGE_EXTENSIONS = {
    ".jpg", ".jpeg", ".png", ".tif", ".tiff",
    ".nef", ".cr2", ".cr3", ".arw", ".rw2",
    ".orf", ".dng", ".raf", ".heic", ".heif",
}

RAW_EXTENSIONS = {
    ".nef", ".cr2", ".cr3", ".arw", ".rw2", ".orf", ".dng", ".raf",
}

NON_RAW_EXTENSIONS = IMAGE_EXTENSIONS - RAW_EXTENSIONS


def _extensions_for_raw_filter(mode: str) -> set:
    if mode == "raw_only":
        return RAW_EXTENSIONS
    if mode == "exclude_raw":
        return NON_RAW_EXTENSIONS
    return IMAGE_EXTENSIONS

ZOOM_CATEGORIES = [
    ("超広角\n(~17mm)",      0,    17),
    ("広角\n(18-24mm)",     18,    24),
    ("準広角\n(25-35mm)",   25,    35),
    ("標準\n(36-70mm)",     36,    70),
    ("中望遠\n(71-135mm)",  71,   135),
    ("望遠\n(136-300mm)",  136,   300),
    ("超望遠\n(301mm~)",   301, 99999),
]

SHUTTER_STOPS = [
    (30,     '30"'),  (15,     '15"'),  (8,      '8"'),
    (4,      '4"'),   (2,      '2"'),   (1,      '1"'),
    (1/2,    "1/2"),  (1/4,    "1/4"),  (1/8,    "1/8"),
    (1/15,   "1/15"), (1/30,   "1/30"), (1/60,   "1/60"),
    (1/125,  "1/125"),(1/250,  "1/250"),(1/500,  "1/500"),
    (1/1000, "1/1000"),(1/2000,"1/2000"),(1/4000,"1/4000"),
    (1/8000, "1/8000"),
]


def shutter_group_log2(sec: float) -> str:
    if sec is None or sec <= 0:
        return "?"
    if sec >= 30:
        return '30"'
    lo = 1 / 8000
    if sec <= lo / (2 ** 0.5):
        return "1/8000"
    best_lbl = None
    best_d = math.inf
    for val, lbl in SHUTTER_STOPS:
        d = abs(math.log2(sec) - math.log2(val))
        if d < best_d:
            best_d = d
            best_lbl = lbl
    return best_lbl or "?"

PALETTE = [
    "#7c6ff7", "#f38ba8", "#a6e3a1", "#fab387",
    "#89dceb", "#f9e2af", "#cba6f7", "#74c7ec",
]

BG       = "#1e1e2e"
PANEL_BG = "#2a2a3e"
DARK_BG  = "#181825"
ACCENT   = "#7c6ff7"
TEXT     = "#cdd6f4"
SUBTEXT  = "#bac2de"
MUTED    = "#585b70"
SURFACE  = "#313244"
OVERLAY  = "#45475a"

# 機材名の欠損表示（集計・フィルター・グラフで統一）
UNKNOWN_EQUIPMENT = "Unknown (不明)"

# 左パネル：Listbox とスクロールバーで文字が潰れないよう幅と余白を確保
LEFT_PANEL_WIDTH = 322
LISTBOX_PADX = (10, 8)  # (左端からの余白, スクロールバーとの隙間)


# ─────────────────────────────────────────────
# EXIF 読み取り
# ─────────────────────────────────────────────
def normalize_equipment_field(val) -> str:
    """None / 空を UNKNOWN に統一。RAW・JPEG 間の表記ゆれ（空白・全角・Null文字）を吸収する。"""
    if val is None:
        return UNKNOWN_EQUIPMENT
    # EXIF特有の終端Null文字(\x00)を除去
    s = str(val).replace("\0", "").strip()
    if not s:
        return UNKNOWN_EQUIPMENT
    s = unicodedata.normalize("NFKC", s)
    for zw in ("\u00ad", "\u200b", "\u200c", "\u200d", "\u2060", "\ufeff"):
        s = s.replace(zw, "")
    s = " ".join(s.split())
    return s if s else UNKNOWN_EQUIPMENT


def _ratio_to_float(val):
    try:
        if hasattr(val, "numerator"):
            return val.numerator / val.denominator if val.denominator else None
        return float(val)
    except Exception:
        return None


def _empty_exif_dict() -> dict:
    return {
        "focal_length": None,
        "focal_length_35mm": None,
        "iso": None,
        "aperture": None,
        "shutter_speed": None,
        "datetime": None,
        "camera_make": None,
        "camera_model": None,
        "lens_model": None,
        "img_width": None,
        "img_height": None,
        "orientation": None,
    }


def _logical_dimensions(img: Image.Image) -> tuple[int, int]:
    w, h = img.size
    try:
        ex = img.getexif()
        if ex is None:
            return w, h
        ori = ex.get(274)
        if ori in (5, 6, 7, 8):
            return h, w
    except Exception:
        pass
    return w, h


def _normalize_iso(val):
    if val is None:
        return None
    try:
        if hasattr(val, "values") and val.values:
            v = val.values[0]
        elif isinstance(val, (list, tuple)):
            v = val[0]
        else:
            v = val

        if hasattr(v, "numerator"):
            return int(v.numerator / v.denominator) if v.denominator else None
        return int(float(str(v)))
    except Exception:
        return None


def _parse_focal_length_35mm(val):
    if val is None:
        return None
    try:
        v = int(float(str(val).split()[0]))
        return v if v > 0 else None
    except Exception:
        return None


def _exifread_to_float(tag):
    if tag is None:
        return None
    try:
        if hasattr(tag, "num") and hasattr(tag, "den"):
            return tag.num / tag.den if tag.den else None
        if hasattr(tag, "numerator") and hasattr(tag, "denominator"):
            return tag.numerator / tag.denominator if tag.denominator else None
        s = str(tag).strip()
        if "/" in s:
            a, b = s.split("/", 1)
            return float(a) / float(b)
        return float(s)
    except Exception:
        return None


def _exifread_first_tag(tags: dict, *names):
    for n in names:
        if n in tags:
            return tags[n]
    return None


def _exifread_datetime(tags) -> datetime | None:
    raw = _exifread_first_tag(
        tags,
        "EXIF DateTimeOriginal",
        "EXIF DateTimeDigitized",
        "Image DateTime",
        "EXIF DateTime",
    )
    if raw is None:
        return None
    s = str(raw).strip()
    for fmt in ("%Y:%m:%d %H:%M:%S", "%Y-%m-%d %H:%M:%S"):
        try:
            return datetime.strptime(s, fmt)
        except Exception:
            pass
    return None


def _from_pillow_exif(raw: dict) -> dict:
    exif = {TAGS.get(k, k): v for k, v in raw.items()}
    data = _empty_exif_dict()
    data["focal_length"]      = _ratio_to_float(exif.get("FocalLength"))
    data["focal_length_35mm"] = _parse_focal_length_35mm(exif.get("FocalLengthIn35mmFilm"))
    data["iso"] = _normalize_iso(exif.get("ISOSpeedRatings") or exif.get("PhotographicSensitivity"))
    data["aperture"]      = _ratio_to_float(exif.get("FNumber"))
    data["shutter_speed"] = _ratio_to_float(exif.get("ExposureTime"))
    for tag in ("DateTimeOriginal", "DateTime", "DateTimeDigitized"):
        raw_dt = exif.get(tag)
        if raw_dt:
            try:
                data["datetime"] = datetime.strptime(raw_dt, "%Y:%m:%d %H:%M:%S")
                break
            except Exception:
                pass
    data["camera_make"]  = (exif.get("Make") or "").strip() or None
    data["camera_model"] = (exif.get("Model") or "").strip() or None
    data["lens_model"]   = (exif.get("LensModel") or "").strip() or None
    return data


def _from_exifread(filepath: str) -> dict:
    data = _empty_exif_dict()
    try:
        with open(filepath, "rb") as f:
            tags = exifread.process_file(f, details=False)
    except Exception:
        return data

    fl = _exifread_to_float(_exifread_first_tag(tags, "EXIF FocalLength"))
    fl35 = _exifread_first_tag(tags, "EXIF FocalLengthIn35mmFilm")
    data["focal_length"] = fl
    data["focal_length_35mm"] = _parse_focal_length_35mm(fl35) if fl35 is not None else None

    iso_tag = _exifread_first_tag(
        tags, "EXIF ISOSpeedRatings", "Image ISOSpeedRatings", "EXIF PhotographicSensitivity",
    )
    data["iso"] = _normalize_iso(iso_tag)

    data["aperture"] = _exifread_to_float(_exifread_first_tag(tags, "EXIF FNumber"))
    data["shutter_speed"] = _exifread_to_float(_exifread_first_tag(tags, "EXIF ExposureTime"))

    data["datetime"] = _exifread_datetime(tags)

    make = _exifread_first_tag(tags, "Image Make", "EXIF Make")
    model = _exifread_first_tag(tags, "Image Model", "EXIF Model")
    lens = _exifread_first_tag(tags, "EXIF LensModel", "EXIF Lens", "EXIF LensSpecification")
    if make is not None:
        data["camera_make"] = str(make).strip() or None
    if model is not None:
        data["camera_model"] = str(model).strip() or None
    if lens is not None:
        data["lens_model"] = str(lens).strip() or None

    try:
        # RAW特有の幅・高さタグも検索対象に追加
        w_tag = _exifread_first_tag(tags, "EXIF ExifImageWidth", "Image ImageWidth", "Image DefaultCropSize", "MakerNote ImageWidth")
        h_tag = _exifread_first_tag(tags, "EXIF ExifImageLength", "Image ImageLength", "Image ImageHeight", "Image DefaultCropLength", "MakerNote ImageLength")
        ori_tag = _exifread_first_tag(tags, "Image Orientation")

        w, h = None, None
        if w_tag and hasattr(w_tag, "values") and w_tag.values:
            w = int(w_tag.values[0])
        elif w_tag:
            w = int(str(w_tag).strip("[]").split(",")[0]) # リスト文字列対策

        if h_tag and hasattr(h_tag, "values") and h_tag.values:
            h = int(h_tag.values[0])
        elif h_tag:
            h = int(str(h_tag).strip("[]").split(",")[0])

        ori = 1
        if ori_tag and hasattr(ori_tag, "values") and ori_tag.values:
            try:
                ori = int(ori_tag.values[0])
            except ValueError:
                pass

        if ori == 1 and ori_tag:
            s = str(ori_tag)
            if any(k in s for k in ("90", "270", "Portrait", "CW", "Left", "Right")):
                ori = 6

        if w and h:
            if ori in (5, 6, 7, 8):
                w, h = h, w

            data["img_width"] = w
            data["img_height"] = h
            if w > h:
                data["orientation"] = "landscape"
            elif h > w:
                data["orientation"] = "portrait"
            else:
                data["orientation"] = "square"
        elif ori_tag is not None:
            # 幅・高さが取得できなくても Orientation があれば構図だけ推定（RAW 向け）
            if ori in (5, 6, 7, 8):
                data["orientation"] = "portrait"
            elif ori in (1, 2, 3, 4):
                data["orientation"] = "landscape"
    except Exception:
        pass

    return data


def _merge_exif(dst: dict, src: dict) -> None:
    for k in dst:
        if dst[k] is None and src.get(k) is not None:
            dst[k] = src[k]


def _exif_has_core(d: dict) -> bool:
    return bool(
        d.get("focal_length")
        or d.get("focal_length_35mm")
        or d.get("iso")
        or d.get("aperture")
        or d.get("camera_model")
    )


def get_exif_data(filepath: str) -> dict:
    data = _empty_exif_dict()
    path = Path(filepath)
    ext = path.suffix.lower()

    try:
        with Image.open(filepath) as img:
            w, h = _logical_dimensions(img)
            data["img_width"] = w
            data["img_height"] = h
            if w > h:
                data["orientation"] = "landscape"
            elif h > w:
                data["orientation"] = "portrait"
            else:
                data["orientation"] = "square"

            raw = img._getexif()
            if raw:
                for k, v in _from_pillow_exif(raw).items():
                    data[k] = v
    except Exception:
        pass

    need_exifread = ext in RAW_EXTENSIONS or not _exif_has_core(data) or data["img_width"] is None
    if need_exifread:
        extra = _from_exifread(filepath)
        _merge_exif(data, extra)

    return data


def effective_focal_length(d: dict):
    return d.get("focal_length_35mm") or d.get("focal_length")


def zoom_category_label_for_data(d: dict) -> str:
    """ズーム域グラフと同じ区分。CSV用にラベル内の改行を空白に置き換える。"""
    fl = effective_focal_length(d)
    if fl is None:
        return ""
    try:
        fl_f = float(fl)
    except (TypeError, ValueError):
        return ""
    for name, lo, hi in ZOOM_CATEGORIES:
        if lo <= fl_f <= hi:
            return name.replace("\n", " ")
    return ""


# ─────────────────────────────────────────────
# メインアプリ
# ─────────────────────────────────────────────
class CameraStatsApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("カメラ撮影統計アナライザー")
        self.root.geometry("1440x900")
        self.root.configure(bg=BG)
        self.root.minsize(1000, 700)

        self.folders: list[str] = []
        self.exif_data: list[dict] = []
        self.filtered_data: list[dict] = []
        self.is_loading = False
        self._filter_ui_busy = False
        self.equipment_filter_enabled_var = tk.BooleanVar(value=True)
        self._chart_figs: dict[str, Figure] = {}
        self._chart_canvases: dict[str, FigureCanvasTkAgg] = {}
        self.tab_keys: list[str] = []
        self._charts_drawn: set[str] = set()

        # 描画の遅延実行（デバウンス）用タイマーを追加
        self._redraw_timer = None
        self._left_panel_outer: ttk.Frame | None = None
        self._left_scroll_canvas: tk.Canvas | None = None

        self._setup_style()
        self._build_ui()

    def _setup_style(self):
        s = ttk.Style()
        s.theme_use("clam")

        s.configure("TFrame",       background=BG)
        s.configure("Panel.TFrame", background=PANEL_BG)

        s.configure("TLabel",       background=BG,       foreground=TEXT,   font=("Yu Gothic UI", 10))
        s.configure("Panel.TLabel", background=PANEL_BG, foreground=TEXT,   font=("Yu Gothic UI", 10))
        s.configure("Title.TLabel", background=PANEL_BG, foreground=TEXT,   font=("Yu Gothic UI", 11, "bold"))
        s.configure("Head.TLabel",  background=BG,       foreground=ACCENT, font=("Yu Gothic UI", 14, "bold"))
        s.configure("Val.TLabel",   background=PANEL_BG, foreground="#a6e3a1", font=("Yu Gothic UI", 11, "bold"))

        s.configure("TButton", background=OVERLAY, foreground=TEXT, font=("Yu Gothic UI", 10), padding=(10, 4))
        s.map("TButton", background=[("active", ACCENT)])

        s.configure("Go.TButton", background=ACCENT, foreground="white",
                    font=("Yu Gothic UI", 11, "bold"), padding=(14, 7))
        s.map("Go.TButton", background=[("active", "#9c8fff")])

        s.configure("TNotebook",     background=BG, tabmargins=[2, 5, 2, 0])
        s.configure("TNotebook.Tab", background=PANEL_BG, foreground=TEXT,
                    font=("Yu Gothic UI", 10), padding=[14, 6])
        s.map("TNotebook.Tab",
              background=[("selected", ACCENT)],
              foreground=[("selected", "white")])

        s.configure("TProgressbar", background=ACCENT, troughcolor=PANEL_BG)
        s.configure("TSeparator",   background=OVERLAY)

    def _build_ui(self):
        main = ttk.Frame(self.root)
        main.pack(fill=tk.BOTH, expand=True, padx=10, pady=(10, 4))

        left = ttk.Frame(main, style="Panel.TFrame", width=LEFT_PANEL_WIDTH)
        left.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 10))
        left.pack_propagate(False)
        self._build_left_panel(left)

        right = ttk.Frame(main)
        right.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self._build_right_panel(right)

        self.progress = ttk.Progressbar(self.root, mode="determinate")
        self.progress.pack(fill=tk.X, side=tk.BOTTOM, padx=10, pady=(0, 2))

        self.status_var = tk.StringVar(value="フォルダーを追加して「解析開始」をクリックしてください")
        tk.Label(self.root, textvariable=self.status_var,
                 bg=SURFACE, fg=SUBTEXT, font=("Yu Gothic UI", 9),
                 anchor="w", padx=10).pack(fill=tk.X, side=tk.BOTTOM)

    def _listbox_can_scroll_internally(self, lb: tk.Listbox, direction_up: bool) -> bool:
        """Listbox 内でまだホイール分スクロールできるなら True（外側パネルには回さない）。"""
        try:
            first, last = lb.yview()
        except tk.TclError:
            return False
        if last - first >= 0.999:
            return False
        if direction_up:
            return first > 0.001
        return last < 0.999

    def _on_mousewheel_left_panel(self, event):
        """左カラム内なら（Listbox を除く／Listbox は端まで来たら）外側 Canvas をスクロール。"""
        p = self._left_panel_outer
        c = self._left_scroll_canvas
        if p is None or c is None:
            return
        try:
            if not p.winfo_exists() or not c.winfo_exists():
                return
        except tk.TclError:
            return
        px, py = p.winfo_rootx(), p.winfo_rooty()
        pw, ph = p.winfo_width(), p.winfo_height()
        xr, yr = event.x_root, event.y_root
        if not (px <= xr < px + pw and py <= yr < py + ph):
            return
        w = event.widget
        direction_up = event.delta > 0
        if isinstance(w, tk.Listbox) and self._listbox_can_scroll_internally(w, direction_up):
            return
        c.yview_scroll(int(-event.delta / 120), "units")

    def _on_button_scroll_left_panel(self, event, direction_up: bool):
        p = self._left_panel_outer
        c = self._left_scroll_canvas
        if p is None or c is None:
            return
        try:
            if not p.winfo_exists() or not c.winfo_exists():
                return
        except tk.TclError:
            return
        px, py = p.winfo_rootx(), p.winfo_rooty()
        pw, ph = p.winfo_width(), p.winfo_height()
        xr, yr = event.x_root, event.y_root
        if not (px <= xr < px + pw and py <= yr < py + ph):
            return
        w = event.widget
        if isinstance(w, tk.Listbox) and self._listbox_can_scroll_internally(w, direction_up):
            return
        c.yview_scroll(-1 if direction_up else 1, "units")

    def _build_left_panel(self, parent):
        self._left_panel_outer = parent
        sb = ttk.Scrollbar(parent, orient=tk.VERTICAL)
        sb.pack(side=tk.RIGHT, fill=tk.Y)
        canvas = tk.Canvas(
            parent,
            highlightthickness=0,
            bg=PANEL_BG,
            bd=0,
        )
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        sb.config(command=canvas.yview)
        canvas.config(yscrollcommand=sb.set)

        inner = ttk.Frame(canvas, style="Panel.TFrame")
        inner_win = canvas.create_window((0, 0), window=inner, anchor="nw")

        def _on_inner_configure(_event=None):
            bbox = canvas.bbox("all")
            if bbox:
                canvas.configure(scrollregion=bbox)

        def _on_canvas_configure(event):
            canvas.itemconfig(inner_win, width=event.width)

        inner.bind("<Configure>", _on_inner_configure)
        canvas.bind("<Configure>", _on_canvas_configure)

        self._left_scroll_canvas = canvas
        self.root.bind_all("<MouseWheel>", self._on_mousewheel_left_panel, add="+")
        self.root.bind_all("<Button-4>", lambda e: self._on_button_scroll_left_panel(e, True), add="+")
        self.root.bind_all("<Button-5>", lambda e: self._on_button_scroll_left_panel(e, False), add="+")

        ttk.Label(inner, text="カメラ撮影統計アナライザー",
                  style="Title.TLabel", padding=(12, 14, 12, 4)).pack(fill=tk.X)
        ttk.Separator(inner).pack(fill=tk.X, padx=10, pady=4)

        ttk.Label(inner, text="対象フォルダー", style="Title.TLabel",
                  padding=(12, 4)).pack(fill=tk.X)

        list_frame = tk.Frame(inner, bg=PANEL_BG)
        list_frame.pack(fill=tk.X, expand=False, padx=8, pady=(0, 4))
        folder_sb = tk.Scrollbar(list_frame)
        folder_sb.pack(side=tk.RIGHT, fill=tk.Y)
        self.folder_listbox = tk.Listbox(
            list_frame, yscrollcommand=folder_sb.set,
            bg=DARK_BG, fg=TEXT, selectbackground=ACCENT,
            font=("Yu Gothic UI", 9), borderwidth=0, height=7,
            activestyle="none", highlightthickness=0,
        )
        self.folder_listbox.pack(
            side=tk.LEFT, fill=tk.BOTH, expand=True, padx=LISTBOX_PADX,
        )
        folder_sb.config(command=self.folder_listbox.yview)

        btn_row = ttk.Frame(inner, style="Panel.TFrame")
        btn_row.pack(fill=tk.X, padx=10, pady=(0, 6))
        btn_row.columnconfigure(2, weight=1)
        ttk.Button(btn_row, text="＋ 追加", command=self._add_folder).grid(
            row=0, column=0, padx=(0, 4), sticky="w",
        )
        ttk.Button(btn_row, text="－ 削除", command=self._remove_folder).grid(
            row=0, column=1, padx=(0, 4), sticky="w",
        )
        ttk.Button(btn_row, text="クリア", command=self._clear_folders).grid(
            row=0, column=2, sticky="e",
        )

        ttk.Separator(inner).pack(fill=tk.X, padx=10, pady=6)

        ttk.Label(inner, text="オプション", style="Title.TLabel",
                  padding=(12, 0, 12, 4)).pack(fill=tk.X)
        self.recursive_var = tk.BooleanVar(value=True)
        tk.Checkbutton(
            inner, text="サブフォルダーも含める",
            variable=self.recursive_var,
            bg=PANEL_BG, fg=TEXT, selectcolor=ACCENT,
            activebackground=PANEL_BG, activeforeground=TEXT,
            font=("Yu Gothic UI", 10),
        ).pack(anchor="w", padx=16, pady=2)

        ttk.Label(
            inner, text="読み込むファイル",
            style="Title.TLabel",
            padding=(12, 8, 12, 2),
        ).pack(fill=tk.X)
        self.raw_filter_var = tk.StringVar(value="all")
        for text, val in (
            ("すべて（JPEG / RAW など）", "all"),
            ("RAW のみ", "raw_only"),
            ("RAW を除く", "exclude_raw"),
        ):
            tk.Radiobutton(
                inner,
                text=text,
                variable=self.raw_filter_var,
                value=val,
                bg=PANEL_BG,
                fg=TEXT,
                selectcolor=ACCENT,
                activebackground=PANEL_BG,
                activeforeground=TEXT,
                font=("Yu Gothic UI", 9),
                anchor="w",
            ).pack(anchor="w", padx=24, pady=1)

        ttk.Separator(inner).pack(fill=tk.X, padx=10, pady=8)

        ttk.Label(
            inner,
            text="機材フィルター\n（クリックで選択／解除・複数可）",
            style="Title.TLabel",
            padding=(12, 0, 12, 4),
        ).pack(fill=tk.X)

        tk.Checkbutton(
            inner,
            text="クリックで機材フィルターを適用（ON/OFF）",
            variable=self.equipment_filter_enabled_var,
            command=self._on_equipment_filter_toggle,
            bg=PANEL_BG,
            fg=TEXT,
            selectcolor=ACCENT,
            activebackground=PANEL_BG,
            activeforeground=TEXT,
            font=("Yu Gothic UI", 9),
            anchor="w",
        ).pack(anchor="w", padx=16, pady=(0, 6))

        filter_outer = tk.Frame(inner, bg=PANEL_BG)
        filter_outer.pack(fill=tk.X, expand=False, padx=8, pady=(0, 4))

        def _labeled_listbox(row_parent, title: str):
            tk.Label(
                row_parent,
                text=title,
                bg=PANEL_BG,
                fg=SUBTEXT,
                font=("Yu Gothic UI", 9),
                anchor="w",
            ).pack(fill=tk.X, padx=2, pady=(0, 2))
            wrap = tk.Frame(row_parent, bg=PANEL_BG, height=88)
            wrap.pack(fill=tk.BOTH, expand=True, pady=(0, 6))
            wrap.pack_propagate(False)
            sb = tk.Scrollbar(wrap)
            sb.pack(side=tk.RIGHT, fill=tk.Y)
            lb = tk.Listbox(
                wrap,
                yscrollcommand=sb.set,
                bg=DARK_BG,
                fg=TEXT,
                selectbackground=ACCENT,
                font=("Yu Gothic UI", 9),
                borderwidth=0,
                height=5,
                activestyle="none",
                highlightthickness=0,
                selectmode=tk.MULTIPLE,
                exportselection=False,
            )
            lb.pack(
                side=tk.LEFT, fill=tk.BOTH, expand=True, padx=LISTBOX_PADX,
            )
            sb.config(command=lb.yview)
            return lb

        self.camera_filter_listbox = _labeled_listbox(filter_outer, "カメラ本体")
        self.lens_filter_listbox = _labeled_listbox(filter_outer, "レンズ")

        self.camera_filter_listbox.bind("<<ListboxSelect>>", self._on_camera_filter_select)
        self.lens_filter_listbox.bind("<<ListboxSelect>>", self._on_lens_filter_select)

        self.filter_count_var = tk.StringVar(value="絞り込み後: — / — 枚")
        tk.Label(
            filter_outer,
            textvariable=self.filter_count_var,
            bg=PANEL_BG,
            fg="#a6e3a1",
            font=("Yu Gothic UI", 9),
            anchor="w",
        ).pack(fill=tk.X, pady=(2, 0))

        ttk.Separator(inner).pack(fill=tk.X, padx=10, pady=8)

        self.csv_filtered_only_var = tk.BooleanVar(value=False)
        tk.Checkbutton(
            inner,
            text="CSVは絞り込み後のデータのみ出力",
            variable=self.csv_filtered_only_var,
            bg=PANEL_BG,
            fg=TEXT,
            selectcolor=ACCENT,
            activebackground=PANEL_BG,
            activeforeground=TEXT,
            font=("Yu Gothic UI", 9),
            anchor="w",
        ).pack(anchor="w", padx=16, pady=(0, 6))

        # 解析・CSVボタン行
        btn_row_go = ttk.Frame(inner, style="Panel.TFrame")
        btn_row_go.pack(fill=tk.X, padx=10, pady=4)
        
        self.btn_analyze = ttk.Button(btn_row_go, text="　解析開始　", style="Go.TButton",
                                      command=self._start_analysis)
        self.btn_analyze.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 4))

        self.btn_csv = ttk.Button(btn_row_go, text="CSV出力",
                                  command=self._export_csv, state=tk.DISABLED)
        self.btn_csv.pack(side=tk.RIGHT, fill=tk.Y)

        ttk.Separator(inner).pack(fill=tk.X, padx=10, pady=8)

        ttk.Label(inner, text="サマリー", style="Title.TLabel",
                  padding=(12, 0, 12, 4)).pack(fill=tk.X)
        sf = ttk.Frame(inner, style="Panel.TFrame")
        sf.pack(fill=tk.X, padx=10, pady=4)

        self.stat_vars: dict[str, tk.StringVar] = {}
        for key, label in [
            ("total",      "総画像数"),
            ("with_exif",  "EXIF取得"),
            ("with_focal", "焦点距離あり"),
            ("cameras",    "カメラ機種数"),
        ]:
            row = ttk.Frame(sf, style="Panel.TFrame")
            row.pack(fill=tk.X, pady=2)
            ttk.Label(row, text=label, style="Panel.TLabel").pack(side=tk.LEFT, padx=6)
            var = tk.StringVar(value="—")
            self.stat_vars[key] = var
            ttk.Label(row, textvariable=var, style="Val.TLabel").pack(side=tk.RIGHT, padx=6)

        self.root.after_idle(_on_inner_configure)

    def _build_right_panel(self, parent):
        header = ttk.Frame(parent)
        header.pack(fill=tk.X, pady=(0, 8))
        ttk.Label(header, text="撮影データ統計グラフ", style="Head.TLabel").pack(side=tk.LEFT)
        
        self.btn_save_graph = ttk.Button(header, text="表示中のグラフを画像保存",
                                         command=self._save_current_graph, state=tk.DISABLED)
        self.btn_save_graph.pack(side=tk.RIGHT)

        self.notebook = ttk.Notebook(parent)
        self.notebook.pack(fill=tk.BOTH, expand=True)

        tab_defs = [
            ("zoom",        "ズーム域分布"),
            ("zoom_detail", "ズーム域詳細"),
            ("orientation", "横縦構図"),
            ("focal_hist", "焦点距離ヒストグラム"),
            ("iso",        "ISO感度"),
            ("aperture",   "絞り値 (F値)"),
            ("shutter",    "シャッタースピード"),
            ("time",       "撮影時刻"),
            ("camera",     "カメラ / レンズ"),
        ]
        self.tab_keys = [key for key, _ in tab_defs]
        self.tab_frames: dict[str, ttk.Frame] = {}
        for key, label in tab_defs:
            frame = ttk.Frame(self.notebook)
            self.notebook.add(frame, text=label)
            self.tab_frames[key] = frame

        self.notebook.bind("<<NotebookTabChanged>>", self._on_notebook_tab_changed)

        self._show_placeholders()

    # ── 追加機能：CSV出力 ─────────────────────
    def _export_csv(self):
        if not self.exif_data:
            return
        filtered_only = self.csv_filtered_only_var.get()
        rows = list(self.filtered_data) if filtered_only else list(self.exif_data)
        if filtered_only and not rows:
            messagebox.showwarning(
                "警告",
                "絞り込み後のデータがありません。\nチェックを外すか、機材の選択を見直してください。",
            )
            return
        filepath = filedialog.asksaveasfilename(
            defaultextension=".csv",
            filetypes=[("CSV Files", "*.csv")],
            title="EXIFデータをCSVとして保存",
            initialfile="camera_stats_export.csv"
        )
        if not filepath:
            return

        keys = ["filepath", "datetime", "camera_make", "camera_model", "lens_model",
                "focal_length", "focal_length_35mm", "zoom_category",
                "iso", "aperture", "shutter_speed", "shutter_speed_str",
                "img_width", "img_height", "orientation"]
        
        try:
            with open(filepath, mode="w", newline="", encoding="utf-8-sig") as f:
                # escapecharを設定し、安全に処理を行う
                writer = csv.DictWriter(f, fieldnames=keys, extrasaction="ignore", escapechar='\\')
                writer.writeheader()
                for d in rows:
                    row = {}
                    for k in keys:
                        if k == "shutter_speed_str":
                            ss = d.get("shutter_speed")
                            row[k] = "" if ss is None else shutter_group_log2(ss)
                            continue
                        if k == "zoom_category":
                            row[k] = zoom_category_label_for_data(d)
                            continue
                        val = d.get(k)
                        if val is None:
                            row[k] = ""
                        elif k == "datetime" and isinstance(val, datetime):
                            row[k] = val.strftime("%Y-%m-%d %H:%M:%S")
                        else:
                            # 値を文字列化し、改行やNull文字などの制御文字を取り除く
                            s = str(val).replace('\0', '').replace('\n', ' ').replace('\r', '')
                            row[k] = s
                    writer.writerow(row)
            scope = "（絞り込み後）" if filtered_only else "（全件）"
            messagebox.showinfo("完了", f"CSVを出力しました{scope}\n{len(rows):,} 件")
        except Exception as e:
            messagebox.showerror("エラー", f"CSVの保存に失敗しました:\n{e}")

    # ── 追加機能：グラフ保存 ────────────────────
    def _save_current_graph(self):
        if not self.exif_data:
            messagebox.showwarning("警告", "先に解析を完了してください。")
            return
        current_tab_idx = self.notebook.index(self.notebook.select())
        if current_tab_idx < 0 or current_tab_idx >= len(self.tab_keys):
            return
        tab_key = self.tab_keys[current_tab_idx]

        if tab_key not in self._charts_drawn:
            self._draw_chart_for_tab(tab_key)
            self._charts_drawn.add(tab_key)

        fig = self._chart_figs.get(tab_key)
        if not fig:
            messagebox.showwarning("警告", "保存できるグラフがありません。")
            return

        filepath = filedialog.asksaveasfilename(
            defaultextension=".png",
            filetypes=[("PNG Image", "*.png"), ("JPEG Image", "*.jpg")],
            title="グラフを画像として保存",
            initialfile=f"chart_{tab_key}.png"
        )
        if filepath:
            try:
                fig.savefig(filepath, dpi=150, bbox_inches="tight", facecolor=BG)
                messagebox.showinfo("完了", "グラフを画像として保存しました。")
            except Exception as e:
                messagebox.showerror("エラー", f"画像の保存に失敗しました:\n{e}")

    def _add_folder(self):
        folder = filedialog.askdirectory(title="フォルダーを選択")
        if folder and folder not in self.folders:
            self.folders.append(folder)
            self.folder_listbox.insert(tk.END, Path(folder).name or folder)

    def _remove_folder(self):
        sel = self.folder_listbox.curselection()
        if sel:
            idx = sel[0]
            self.folders.pop(idx)
            self.folder_listbox.delete(idx)

    def _clear_folders(self):
        self.folders.clear()
        self.folder_listbox.delete(0, tk.END)

    def _start_analysis(self):
        if not self.folders:
            messagebox.showwarning("警告", "フォルダーを追加してください")
            return
        if self.is_loading:
            return
        self.is_loading = True
        self.btn_csv.config(state=tk.DISABLED)
        self.btn_save_graph.config(state=tk.DISABLED)
        self.exif_data = []
        self.filtered_data = []
        self.equipment_filter_enabled_var.set(True)
        self._clear_equipment_filter_lists()
        self._sync_filter_listbox_interactive_state()
        self.filter_count_var.set("絞り込み後: — / — 枚")
        recursive = self.recursive_var.get()
        raw_mode = self.raw_filter_var.get()
        if raw_mode not in ("all", "raw_only", "exclude_raw"):
            raw_mode = "all"
        threading.Thread(
            target=self._load_thread,
            args=(recursive, raw_mode),
            daemon=True,
        ).start()

    def _load_thread(self, recursive: bool, raw_filter_mode: str):
        exts = _extensions_for_raw_filter(raw_filter_mode)
        files: list[Path] = []
        for folder in self.folders:
            base = Path(folder)
            for ext in exts:
                pattern = f"**/*{ext}" if recursive else f"*{ext}"
                files.extend(base.glob(pattern))
                files.extend(base.glob(pattern.replace(ext, ext.upper())))

        files = list(set(files))
        total = len(files)

        if total == 0:
            msg = "条件に合う画像ファイルが見つかりませんでした"
            self.root.after(0, lambda m=msg: messagebox.showinfo("情報", m))
            self.is_loading = False
            return

        self.root.after(0, lambda: self.progress.configure(maximum=total, value=0))
        self.root.after(0, lambda: self.status_var.set(f"読み込み中... 0 / {total}"))

        result = []
        for i, fp in enumerate(files):
            d = get_exif_data(str(fp))
            d["filepath"] = str(fp)
            result.append(d)
            if (i + 1) % 20 == 0 or (i + 1) == total:
                n = i + 1
                self.root.after(0, lambda n=n, t=total: (
                    self.progress.configure(value=n),
                    self.status_var.set(f"読み込み中... {n} / {t}"),
                ))

        for d in result:
            d["camera_model"] = normalize_equipment_field(d.get("camera_model"))
            d["lens_model"] = normalize_equipment_field(d.get("lens_model"))

        self.exif_data = result
        self.root.after(0, self._on_analysis_complete)

    def _on_analysis_complete(self):
        self.is_loading = False
        data = self.exif_data
        total = len(data)
        with_exif = sum(
            1
            for d in data
            if d.get("iso")
            or d.get("aperture")
            or d.get("focal_length")
            or d.get("focal_length_35mm")
            or d.get("camera_model")
        )
        with_focal = sum(1 for d in data if effective_focal_length(d))
        cameras    = len({d["camera_model"] for d in data})

        self.stat_vars["total"].set(f"{total:,} 枚")
        self.stat_vars["with_exif"].set(f"{with_exif:,} 枚")
        self.stat_vars["with_focal"].set(f"{with_focal:,} 枚")
        self.stat_vars["cameras"].set(f"{cameras} 種")
        self.status_var.set(f"解析完了 — {total:,} 枚を処理しました")
        self.progress.configure(value=total)

        self._populate_equipment_filter_lists()
        self._apply_equipment_filter_and_redraw()

        # 解析完了時にボタンを有効化
        self.btn_csv.config(state=tk.NORMAL)
        self.btn_save_graph.config(state=tk.NORMAL)

    def _on_notebook_tab_changed(self, _event=None) -> None:
        if self.is_loading or not self.exif_data:
            return
        idx = self.notebook.index(self.notebook.select())
        if idx < 0 or idx >= len(self.tab_keys):
            return
        key = self.tab_keys[idx]
        if key in self._charts_drawn:
            return
        self._draw_chart_for_tab(key)
        self._charts_drawn.add(key)

    def _show_placeholders(self):
        for frame in self.tab_frames.values():
            self._clear_frame(frame)
            tk.Label(frame,
                     text="フォルダーを選択して「解析開始」をクリックしてください",
                     bg=BG, fg=MUTED, font=("Yu Gothic UI", 13),
                     ).pack(expand=True)

    @staticmethod
    def _clear_frame(frame: ttk.Frame):
        for w in frame.winfo_children():
            w.destroy()

    def _clear_equipment_filter_lists(self) -> None:
        for lb in (self.camera_filter_listbox, self.lens_filter_listbox):
            lb.config(state=tk.NORMAL)
        self.camera_filter_listbox.delete(0, tk.END)
        self.lens_filter_listbox.delete(0, tk.END)

    def _sync_filter_listbox_interactive_state(self) -> None:
        """フィルターOFF時はリスト操作を無効化し、誤操作と再描画ループを防ぐ。"""
        if not self.exif_data:
            for lb in (self.camera_filter_listbox, self.lens_filter_listbox):
                lb.config(state=tk.DISABLED)
            return
        if self.equipment_filter_enabled_var.get():
            self.camera_filter_listbox.config(state=tk.NORMAL)
            self.lens_filter_listbox.config(state=tk.NORMAL)
        else:
            self.camera_filter_listbox.config(state=tk.DISABLED)
            self.lens_filter_listbox.config(state=tk.DISABLED)

    def _schedule_filter_update(self):
        """連続クリック時の二重描画（表示崩れ）を防ぐための遅延実行（デバウンス処理）"""
        if self._redraw_timer is not None:
            self.root.after_cancel(self._redraw_timer)
        self._redraw_timer = self.root.after(150, self._on_debounced_filter_redraw)

    def _on_debounced_filter_redraw(self) -> None:
        self._redraw_timer = None
        self._apply_equipment_filter_and_redraw()

    def _on_equipment_filter_toggle(self) -> None:
        if self._filter_ui_busy or self.is_loading:
            return
        self._sync_filter_listbox_interactive_state()
        if self.equipment_filter_enabled_var.get() and self.exif_data:
            self._filter_ui_busy = True
            try:
                self._refill_lens_filter_listbox()
            finally:
                self._filter_ui_busy = False
        if self.exif_data:
            self._schedule_filter_update()

    @staticmethod
    def _listbox_selected_strings(lb: tk.Listbox) -> set[str]:
        return {lb.get(i) for i in lb.curselection()}

    @staticmethod
    def _listbox_select_strings(lb: tk.Listbox, wanted: set[str]) -> None:
        lb.selection_clear(0, tk.END)
        for i in range(lb.size()):
            if lb.get(i) in wanted:
                lb.selection_set(i)

    def _populate_equipment_filter_lists(self) -> None:
        self._filter_ui_busy = True
        try:
            self._clear_equipment_filter_lists()
            if not self.exif_data:
                return
            for c in sorted({d["camera_model"] for d in self.exif_data}):
                self.camera_filter_listbox.insert(tk.END, c)
            for L in sorted({d["lens_model"] for d in self.exif_data}):
                self.lens_filter_listbox.insert(tk.END, L)
        finally:
            self._filter_ui_busy = False
            self._sync_filter_listbox_interactive_state()

    def _refill_lens_filter_listbox(self) -> None:
        if not self.exif_data:
            self.lens_filter_listbox.delete(0, tk.END)
            return
        prev_lenses = self._listbox_selected_strings(self.lens_filter_listbox)
        sel_cams = self._listbox_selected_strings(self.camera_filter_listbox)
        if sel_cams:
            subset = [d for d in self.exif_data if d["camera_model"] in sel_cams]
        else:
            subset = self.exif_data
        lenses = sorted({d["lens_model"] for d in subset})
        self.lens_filter_listbox.delete(0, tk.END)
        for L in lenses:
            self.lens_filter_listbox.insert(tk.END, L)
        self._listbox_select_strings(self.lens_filter_listbox, prev_lenses & set(lenses))

    def _recompute_filtered_data(self) -> None:
        if not self.exif_data:
            self.filtered_data = []
            return
        if not self.equipment_filter_enabled_var.get():
            self.filtered_data = list(self.exif_data)
            return
        sc = self._listbox_selected_strings(self.camera_filter_listbox)
        sl = self._listbox_selected_strings(self.lens_filter_listbox)
        self.filtered_data = [
            d
            for d in self.exif_data
            if (not sc or d["camera_model"] in sc) and (not sl or d["lens_model"] in sl)
        ]

    def _update_filter_count_label(self) -> None:
        if not self.exif_data:
            self.filter_count_var.set("絞り込み後: — / — 枚")
            return
        t = len(self.exif_data)
        if not self.equipment_filter_enabled_var.get():
            self.filter_count_var.set(f"フィルターOFF — 全 {t:,} 枚表示")
            return
        n = len(self.filtered_data)
        self.filter_count_var.set(f"絞り込み後: {n:,} / {t:,} 枚")

    def _apply_equipment_filter_and_redraw(self) -> None:
        self._recompute_filtered_data()
        self._update_filter_count_label()
        if self.is_loading or not self.exif_data:
            return
        self._charts_drawn.clear()
        cur_idx = self.notebook.index(self.notebook.select())
        if cur_idx < 0 or cur_idx >= len(self.tab_keys):
            cur_idx = 0
        cur_key = self.tab_keys[cur_idx]
        for key in self.tab_keys:
            if key != cur_key and key in self._chart_figs:
                self._chart_figs[key].clear()
        self._draw_chart_for_tab(cur_key)
        self._charts_drawn.add(cur_key)

    def _on_camera_filter_select(self, _event=None) -> None:
        if (
            self._filter_ui_busy
            or self.is_loading
            or not self.exif_data
            or not self.equipment_filter_enabled_var.get()
        ):
            return
        self._filter_ui_busy = True
        try:
            self._refill_lens_filter_listbox()
        finally:
            self._filter_ui_busy = False
        self._schedule_filter_update()

    def _on_lens_filter_select(self, _event=None) -> None:
        if (
            self._filter_ui_busy
            or self.is_loading
            or not self.exif_data
            or not self.equipment_filter_enabled_var.get()
        ):
            return
        self._schedule_filter_update()

    def _ensure_canvas(self, tab_key: str, frame: ttk.Frame, figsize=(11, 6)):
        if tab_key not in self._chart_figs:
            self._clear_frame(frame)
            fig = Figure(figsize=figsize, facecolor=BG)
            canvas = FigureCanvasTkAgg(fig, master=frame)
            canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
            toolbar = NavigationToolbar2Tk(canvas, frame)
            toolbar.update()
            toolbar.config(bg=SURFACE)
            self._chart_figs[tab_key] = fig
            self._chart_canvases[tab_key] = canvas
        else:
            fig = self._chart_figs[tab_key]
            canvas = self._chart_canvases[tab_key]
            fig.clf()
            fig.set_facecolor(BG)
        return fig, canvas

    def _style_ax(self, ax, title, xlabel=None, ylabel=None):
        ax.set_facecolor(DARK_BG)
        ax.set_title(title, color=TEXT, fontsize=13, fontweight="bold", pad=10)
        if xlabel:
            ax.set_xlabel(xlabel, color=SUBTEXT, fontsize=10)
        if ylabel:
            ax.set_ylabel(ylabel, color=SUBTEXT, fontsize=10)
        ax.tick_params(colors=SUBTEXT, labelsize=9)
        for spine in ax.spines.values():
            spine.set_color(OVERLAY)
        ax.grid(axis="y", color=SURFACE, linestyle="--", alpha=0.8)

    def _no_data(self, ax, canvas):
        ax.text(0.5, 0.5, "データなし", transform=ax.transAxes,
                ha="center", va="center", color=MUTED, fontsize=14)
        canvas.draw()

    def _draw_chart_for_tab(self, tab_key: str) -> None:
        drawers = {
            "zoom": self._draw_zoom_chart,
            "zoom_detail": self._draw_zoom_detail_chart,
            "orientation": self._draw_orientation_chart,
            "focal_hist": self._draw_focal_histogram,
            "iso": self._draw_iso_chart,
            "aperture": self._draw_aperture_chart,
            "shutter": self._draw_shutter_chart,
            "time": self._draw_time_chart,
            "camera": self._draw_camera_chart,
        }
        fn = drawers.get(tab_key)
        if fn is not None:
            fn()

    def _draw_zoom_chart(self):
        frame = self.tab_frames["zoom"]
        fig, canvas = self._ensure_canvas("zoom", frame, figsize=(12, 6))

        fls = [effective_focal_length(d) for d in self.filtered_data if effective_focal_length(d)]
        if not fls:
            ax = fig.add_subplot(111)
            self._style_ax(ax, "ズーム域別使用枚数", "ズーム域", "枚数")
            self._no_data(ax, canvas)
            return

        ax = fig.add_subplot(111)
        self._style_ax(ax, "ズーム域別使用枚数（比率は各バー上）", "ズーム域", "枚数")

        counts = Counter()
        for fl in fls:
            for name, lo, hi in ZOOM_CATEGORIES:
                if lo <= fl <= hi:
                    counts[name] += 1
                    break

        names  = [c[0] for c in ZOOM_CATEGORIES if counts.get(c[0])]
        values = [counts[c[0]] for c in ZOOM_CATEGORIES if counts.get(c[0])]
        total  = sum(values)
        pcts   = [v / total * 100 for v in values]
        clrs   = PALETTE[:len(names)]

        bars = ax.bar(range(len(names)), values, color=clrs,
                      edgecolor=BG, linewidth=0.8)
        ax.set_xticks(range(len(names)))
        ax.set_xticklabels(names, fontsize=8)
        for bar, val, pct in zip(bars, values, pcts):
            ax.text(bar.get_x() + bar.get_width() / 2,
                    bar.get_height() + max(values) * 0.01,
                    f"{val:,}\n({pct:.1f}%)",
                    ha="center", va="bottom", color=TEXT, fontsize=8)

        fig.tight_layout(pad=2.0)
        canvas.draw()

    def _draw_zoom_detail_chart(self):
        """ズームレンズの癖（端のmm付近に寄る等）を 2mm 刻みで見る。"""
        frame = self.tab_frames["zoom_detail"]
        fig, canvas = self._ensure_canvas("zoom_detail", frame, figsize=(13, 6))
        ax = fig.add_subplot(111)
        self._style_ax(ax, "焦点距離の細かい分布（2mm 刻み・35mm換算）", "焦点距離 (mm)", "枚数")

        fls = [effective_focal_length(d) for d in self.filtered_data if effective_focal_length(d)]
        if not fls:
            self._no_data(ax, canvas)
            return

        clipped = [min(f, 600) for f in fls]
        lo = max(8, int(math.floor(min(clipped) / 2) * 2) - 2)
        hi = int(math.ceil(max(clipped) / 2) * 2) + 4
        hi = min(hi, 602)
        if hi - lo < 24:
            lo = max(8, lo - 12)
            hi = min(602, hi + 12)
        bins = list(range(lo, hi + 2, 2))

        ax.hist(
            clipped,
            bins=bins,
            edgecolor=BG,
            linewidth=0.35,
            color=ACCENT,
            rwidth=0.9,
        )
        if len(bins) > 35:
            ax.tick_params(axis="x", labelsize=7)
            for lbl in ax.get_xticklabels():
                lbl.set_rotation(45)
                lbl.set_ha("right")

        fig.tight_layout(pad=2.0)
        canvas.draw()

    def _draw_orientation_chart(self):
        frame = self.tab_frames["orientation"]
        fig, canvas = self._ensure_canvas("orientation", frame, figsize=(14, 6))

        orient_counts = Counter()
        for d in self.filtered_data:
            o = d.get("orientation")
            if o in ("landscape", "portrait", "square"):
                orient_counts[o] += 1

        if not orient_counts:
            ax = fig.add_subplot(111)
            self._style_ax(ax, "横構図 vs 縦構図", "", "")
            self._no_data(ax, canvas)
            return

        ax_pie = fig.add_subplot(121)
        ax_st = fig.add_subplot(122)

        order = ("landscape", "portrait", "square")
        label_map = {"landscape": "横構図", "portrait": "縦構図", "square": "スクエア"}
        pie_labels = [label_map[k] for k in order if orient_counts.get(k)]
        pie_vals = [orient_counts[k] for k in order if orient_counts.get(k)]
        pie_colors = ["#fab387", "#89dceb", "#f9e2af"]
        pie_colors = pie_colors[: len(pie_vals)]

        ax_pie.set_facecolor(DARK_BG)
        ax_pie.set_title("横 / 縦 / スクエアの比率", color=TEXT, fontsize=13, fontweight="bold")
        _, _, autotexts = ax_pie.pie(
            pie_vals,
            labels=pie_labels,
            autopct="%1.1f%%",
            colors=pie_colors,
            startangle=90,
            textprops={"color": TEXT, "fontsize": 10},
            wedgeprops={"edgecolor": BG, "linewidth": 1.5},
        )
        for at in autotexts:
            at.set_color(DARK_BG)
            at.set_fontweight("bold")

        self._style_ax(ax_st, "ズーム域ごとの構図（割合）", "ズーム域", "割合 (%)")
        ax_st.set_ylim(0, 100)

        zoom_orient: dict[str, Counter] = {}
        for d in self.filtered_data:
            fl = effective_focal_length(d)
            o = d.get("orientation")
            if fl is None or o not in ("landscape", "portrait", "square"):
                continue
            zname = None
            for name, lo, hi in ZOOM_CATEGORIES:
                if lo <= fl <= hi:
                    zname = name
                    break
            if zname:
                zoom_orient.setdefault(zname, Counter())[o] += 1

        zorder = [
            c[0]
            for c in ZOOM_CATEGORIES
            if zoom_orient.get(c[0]) and sum(zoom_orient[c[0]].values()) > 0
        ]
        if not zorder:
            ax_st.text(
                0.5,
                0.5,
                "焦点距離が取得できないため\nズーム域別の内訳は表示できません",
                transform=ax_st.transAxes,
                ha="center",
                va="center",
                color=MUTED,
                fontsize=11,
            )
            ax_st.set_xticks([])
            ax_st.set_yticks([])
            for s in ax_st.spines.values():
                s.set_visible(False)
            ax_st.grid(False)
        else:
            n = len(zorder)
            x = range(n)
            p_pct, l_pct, s_pct = [], [], []
            for zn in zorder:
                c = zoom_orient[zn]
                tot = sum(c.values())
                if tot <= 0:
                    p_pct.append(0.0)
                    l_pct.append(0.0)
                    s_pct.append(0.0)
                else:
                    p_pct.append(c.get("portrait", 0) / tot * 100)
                    l_pct.append(c.get("landscape", 0) / tot * 100)
                    s_pct.append(c.get("square", 0) / tot * 100)

            ax_st.bar(
                x,
                p_pct,
                color="#89dceb",
                edgecolor=BG,
                linewidth=0.5,
            )
            ax_st.bar(
                x,
                l_pct,
                bottom=p_pct,
                color="#fab387",
                edgecolor=BG,
                linewidth=0.5,
            )
            bottom2 = [a + b for a, b in zip(p_pct, l_pct)]
            ax_st.bar(
                x,
                s_pct,
                bottom=bottom2,
                color="#f9e2af",
                edgecolor=BG,
                linewidth=0.5,
            )
            ax_st.set_xticks(list(x))
            ax_st.set_xticklabels(zorder, fontsize=7)
            # 枚数 0 の系列だけ凡例に出すと紛らわしいので、合計が正のものだけ表示
            leg_handles = []
            if sum(p_pct) > 1e-6:
                leg_handles.append(mpatches.Patch(color="#89dceb", label="縦構図"))
            if sum(l_pct) > 1e-6:
                leg_handles.append(mpatches.Patch(color="#fab387", label="横構図"))
            if sum(s_pct) > 1e-6:
                leg_handles.append(mpatches.Patch(color="#f9e2af", label="スクエア"))
            if leg_handles:
                ax_st.legend(
                    handles=leg_handles,
                    facecolor=SURFACE,
                    edgecolor=OVERLAY,
                    labelcolor=TEXT,
                    fontsize=9,
                    loc="upper right",
                )
            ax_st.yaxis.set_major_formatter(
                matplotlib.ticker.FuncFormatter(lambda v, _: f"{v:.0f}%")
            )

        fig.tight_layout(pad=2.0)
        canvas.draw()

    def _draw_focal_histogram(self):
        frame = self.tab_frames["focal_hist"]
        fig, canvas = self._ensure_canvas("focal_hist", frame, figsize=(12, 6))

        fls = [effective_focal_length(d) for d in self.filtered_data if effective_focal_length(d)]
        if not fls:
            ax = fig.add_subplot(111)
            self._style_ax(ax, "焦点距離分布ヒストグラム (35mm換算)", "焦点距離 (mm)", "枚数")
            self._no_data(ax, canvas)
            return

        # 単一 Axes + 軸下に凡例1つ（2段 subplot + tight_layout は Tk 埋め込みで二重表示の原因になりやすい）
        ax = fig.add_subplot(111)
        self._style_ax(ax, "焦点距離分布ヒストグラム (35mm換算)", "焦点距離 (mm)", "枚数")

        clipped = [min(fl, 600) for fl in fls]
        bins = [0, 14, 18, 24, 28, 35, 50, 70, 85, 105, 135, 200, 300, 400, 600]
        bin_colors = [
            "#89dceb", "#89dceb", "#a6e3a1", "#a6e3a1",
            "#f9e2af", "#f9e2af", "#f9e2af", "#fab387",
            "#fab387", "#fab387", "#f38ba8", "#f38ba8",
            "#cba6f7", "#cba6f7",
        ]
        _, _, patches = ax.hist(clipped, bins=bins, edgecolor=BG, linewidth=0.6, rwidth=0.88)
        for patch, color in zip(patches, bin_colors):
            patch.set_facecolor(color)

        for b in [18, 25, 36, 71, 136, 301]:
            if b <= max(clipped):
                ax.axvline(b, color=OVERLAY, linestyle="--", alpha=0.6, linewidth=1)

        legend_items = [
            mpatches.Patch(color="#89dceb", label="超広角/広角 (~24mm)"),
            mpatches.Patch(color="#a6e3a1", label="準広角 (25-35mm)"),
            mpatches.Patch(color="#f9e2af", label="標準 (36-70mm)"),
            mpatches.Patch(color="#fab387", label="中望遠 (71-135mm)"),
            mpatches.Patch(color="#f38ba8", label="望遠 (136-300mm)"),
            mpatches.Patch(color="#cba6f7", label="超望遠 (300mm~)"),
        ]
        # 軸の legend は Tk 再描画で重ね塗りされやすいので Figure 座標で1回だけ付与
        while fig.legends:
            fig.legends[-1].remove()
        fig.legend(
            handles=legend_items,
            loc="lower center",
            bbox_to_anchor=(0.5, 0.02),
            bbox_transform=fig.transFigure,
            ncol=3,
            fontsize=8,
            framealpha=0.95,
            facecolor=SURFACE,
            edgecolor=OVERLAY,
            labelcolor=TEXT,
            columnspacing=0.85,
            handlelength=1.1,
        )

        median_fl = statistics.median(fls)
        mean_fl   = sum(fls) / len(fls)
        nshots = len(fls)
        ax.text(
            0.97,
            0.97,
            f"中央値: {median_fl:.0f} mm\n平均値: {mean_fl:.1f} mm\n枚数: {nshots:,} 枚",
            transform=ax.transAxes,
            ha="right",
            va="top",
            color=TEXT,
            fontsize=10,
            clip_on=False,
            bbox=dict(boxstyle="round,pad=0.4", facecolor=SURFACE, alpha=0.95, edgecolor=OVERLAY),
        )

        fig.subplots_adjust(left=0.09, right=0.98, top=0.90, bottom=0.20)
        canvas.draw()

    def _draw_iso_chart(self):
        frame = self.tab_frames["iso"]
        fig, canvas = self._ensure_canvas("iso", frame, figsize=(12, 6))
        ax = fig.add_subplot(111)
        self._style_ax(ax, "ISO感度分布", "ISO値", "枚数")

        iso_vals = [d["iso"] for d in self.filtered_data if d.get("iso")]
        if not iso_vals:
            self._no_data(ax, canvas)
            return

        stops = [50, 100, 200, 400, 800, 1600, 3200, 6400, 12800, 25600, 51200, 102400]

        def iso_group(v):
            for s in stops:
                if v <= s * 1.41:
                    return s
            return stops[-1]

        grouped = Counter(iso_group(v) for v in iso_vals)
        labels = [f"ISO {s:,}" for s in stops if s in grouped]
        values = [grouped[s] for s in stops if s in grouped]

        bars = ax.bar(range(len(labels)), values,
                      color=PALETTE[:len(labels)], edgecolor=BG, linewidth=0.6)
        ax.set_xticks(range(len(labels)))
        ax.set_xticklabels(labels, rotation=30, ha="right")
        for bar, val in zip(bars, values):
            pct = val / len(iso_vals) * 100
            ax.text(bar.get_x() + bar.get_width() / 2,
                    bar.get_height() + max(values) * 0.01,
                    f"{val:,}\n({pct:.1f}%)",
                    ha="center", va="bottom", color=TEXT, fontsize=8)

        fig.tight_layout(pad=2.0)
        canvas.draw()

    def _draw_aperture_chart(self):
        frame = self.tab_frames["aperture"]
        fig, canvas = self._ensure_canvas("aperture", frame, figsize=(12, 6))
        ax = fig.add_subplot(111)
        self._style_ax(ax, "絞り値 (F値) 分布", "F値", "枚数")

        apts = [d["aperture"] for d in self.filtered_data if d.get("aperture")]
        if not apts:
            self._no_data(ax, canvas)
            return

        f_stops = [1.0, 1.2, 1.4, 1.8, 2.0, 2.4, 2.8, 3.5, 4.0,
                   4.5, 5.0, 5.6, 6.3, 7.1, 8.0, 9.0, 10, 11, 13, 16, 22]

        def f_group(v):
            for s in f_stops:
                if v <= s * 1.06:
                    return s
            return f_stops[-1]

        grouped  = Counter(f_group(v) for v in apts)
        s_sorted = sorted(grouped)
        labels   = [f"f/{s}" for s in s_sorted]
        values   = [grouped[s] for s in s_sorted]

        bars = ax.bar(range(len(labels)), values,
                      color=[PALETTE[i % len(PALETTE)] for i in range(len(labels))],
                      edgecolor=BG, linewidth=0.6)
        ax.set_xticks(range(len(labels)))
        ax.set_xticklabels(labels, rotation=45, ha="right", fontsize=9)
        threshold = max(values) * 0.04
        for bar, val in zip(bars, values):
            if val > threshold:
                ax.text(bar.get_x() + bar.get_width() / 2,
                        bar.get_height() + max(values) * 0.01,
                        f"{val:,}", ha="center", va="bottom", color=TEXT, fontsize=8)

        fig.tight_layout(pad=2.0)
        canvas.draw()

    def _draw_shutter_chart(self):
        frame = self.tab_frames["shutter"]
        fig, canvas = self._ensure_canvas("shutter", frame, figsize=(12, 6))
        ax = fig.add_subplot(111)
        self._style_ax(ax, "シャッタースピード分布 (log2 最近傍)", "シャッタースピード", "枚数")

        shutters = [d["shutter_speed"] for d in self.filtered_data if d.get("shutter_speed")]
        if not shutters:
            self._no_data(ax, canvas)
            return

        grouped   = Counter(shutter_group_log2(s) for s in shutters)
        order     = [lbl for _, lbl in SHUTTER_STOPS]
        s_labels  = [l for l in order if l in grouped]
        values    = [grouped[l] for l in s_labels]

        bars = ax.bar(range(len(s_labels)), values,
                      color=[PALETTE[i % len(PALETTE)] for i in range(len(s_labels))],
                      edgecolor=BG, linewidth=0.6)
        ax.set_xticks(range(len(s_labels)))
        ax.set_xticklabels(s_labels, rotation=45, ha="right", fontsize=9)
        threshold = max(values) * 0.03
        for bar, val in zip(bars, values):
            if val > threshold:
                ax.text(bar.get_x() + bar.get_width() / 2,
                        bar.get_height() + max(values) * 0.01,
                        f"{val:,}", ha="center", va="bottom", color=TEXT, fontsize=8)

        fig.tight_layout(pad=2.0)
        canvas.draw()

    def _draw_time_chart(self):
        frame = self.tab_frames["time"]
        fig, canvas = self._ensure_canvas("time", frame, figsize=(12, 6))
        ax = fig.add_subplot(111)
        self._style_ax(ax, "撮影時刻分布（時間帯別）", "時刻（時）", "枚数")

        hours = [d["datetime"].hour for d in self.filtered_data if d.get("datetime")]
        if not hours:
            self._no_data(ax, canvas)
            return

        hour_count = Counter(hours)
        all_hours  = list(range(24))
        values     = [hour_count.get(h, 0) for h in all_hours]

        def hour_color(h):
            if 5  <= h < 8:  return "#f9e2af"
            if 8  <= h < 12: return "#a6e3a1"
            if 12 <= h < 17: return "#89dceb"
            if 17 <= h < 20: return "#fab387"
            return "#7c6ff7"

        bars = ax.bar(all_hours, values,
                      color=[hour_color(h) for h in all_hours],
                      edgecolor=BG, linewidth=0.6)
        ax.set_xticks(all_hours)
        ax.set_xticklabels([f"{h}時" for h in all_hours], rotation=45, ha="right", fontsize=8)

        legend_items = [
            mpatches.Patch(color="#f9e2af", label="早朝 (5-8時)"),
            mpatches.Patch(color="#a6e3a1", label="午前 (8-12時)"),
            mpatches.Patch(color="#89dceb", label="午後 (12-17時)"),
            mpatches.Patch(color="#fab387", label="夕方 (17-20時)"),
            mpatches.Patch(color="#7c6ff7", label="夜間 (20-5時)"),
        ]
        ax.legend(handles=legend_items, facecolor=SURFACE, edgecolor=OVERLAY,
                  labelcolor=TEXT, fontsize=9, loc="upper right")

        fig.tight_layout(pad=2.0)
        canvas.draw()

    def _draw_camera_chart(self):
        frame = self.tab_frames["camera"]
        fig, canvas = self._ensure_canvas("camera", frame, figsize=(13, 6))
        ax1 = fig.add_subplot(121)
        ax2 = fig.add_subplot(122)
        self._style_ax(ax1, "カメラ機種別枚数 (上位10)", "枚数", "")
        self._style_ax(ax2, "レンズ別枚数 (上位10)",     "枚数", "")

        def draw_horizontal(ax, counter_data, palette):
            if not counter_data:
                ax.text(0.5, 0.5, "データなし", transform=ax.transAxes,
                        ha="center", va="center", color=MUTED, fontsize=12)
                return
            top = counter_data.most_common(10)
            names  = [n[:24] for n, _ in top]
            values = [v      for _, v in top]
            bars = ax.barh(range(len(names)), values,
                           color=palette[:len(names)], edgecolor=BG, linewidth=0.6)
            ax.set_yticks(range(len(names)))
            ax.set_yticklabels(names, fontsize=9)
            ax.invert_yaxis()
            ax.grid(axis="x", color=SURFACE, linestyle="--", alpha=0.8)
            ax.grid(axis="y", visible=False)
            for bar, val in zip(bars, values):
                ax.text(bar.get_width() + max(values) * 0.01,
                        bar.get_y() + bar.get_height() / 2,
                        f"{val:,}", va="center", color=TEXT, fontsize=8)

        cams  = Counter(d["camera_model"] for d in self.filtered_data)
        lens  = Counter(d["lens_model"] for d in self.filtered_data)
        draw_horizontal(ax1, cams,  PALETTE)
        draw_horizontal(ax2, lens,  PALETTE)

        fig.tight_layout(pad=2.0)
        canvas.draw()


# ─────────────────────────────────────────────
# エントリーポイント
# ─────────────────────────────────────────────
def main():
    root = tk.Tk()
    app = CameraStatsApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()