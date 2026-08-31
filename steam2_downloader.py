#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
steam2 downloader - a GUI browser/downloader/extractor for an archive of the
old steam2 content server, served as an open directory of blobs and dats.
Set the server address in the top bar on first run; it is remembered after that.

Stdlib only (tkinter + http.client + threading). Python 3.8+.

Features
  * browse the remote nginx index, listings are cached on disk
  * substring / regex / depot filtering over the huge blobs+dats listings
  * depot picker: pick a depot id, see every version, queue blob+dat pairs,
    warns when a depot had a "reset" (duplicate versions) and shows the CRC
    you must pass to the extractor as --blobcrc
  * parallel downloads, pause/resume (HTTP Range), retry, skip existing
  * SHA-256 verification straight from the filename (4th name component)
"""
from __future__ import annotations

import hashlib
import http.client
import json
import os
import queue
import re
import shlex
import shutil
import struct
import subprocess
import sys
import threading
import time
import zlib
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
import http.cookiejar
from urllib.error import HTTPError
from urllib.parse import quote, unquote, urlencode, urljoin, urlsplit
from urllib.request import HTTPCookieProcessor, Request, build_opener, urlopen
from concurrent.futures import ThreadPoolExecutor

import tkinter as tk
from tkinter import filedialog, messagebox, ttk

APP_NAME = "steam2 downloader"
DEFAULT_BASE = ""        # set it in the Server field; remembered after that
# Mirrors have been seen rejecting "name-with-hyphen/version" user agents with
# a 403, while serving curl, browsers and this plainer wording perfectly well.
# It still says exactly what the client is - change it if your mirror prefers
# something else.
UA = "steam2 depot downloader (python, stdlib)"
TIMEOUT = 90          # the server can take 25s+ to answer a cold request
CHUNK = 1 << 18          # 256 KiB
MAX_ROWS = 3000          # max rows rendered in the browse list at once

HERE = Path(__file__).resolve().parent
CACHE_DIR = HERE / ".s2cache"
SETTINGS_PATH = HERE / "s2downloader.json"
QUEUE_PATH = HERE / "s2queue.json"
NAMES_PATH = HERE / "depot_names.json"   # optional {"852": "Half-Life 2 content"} map
NAMES_CACHE = CACHE_DIR / "steam_names.json"   # names fetched from Steam, cached forever
HISTORY_PATH = HERE / "s2extracted.json"       # what has been extracted, and where
# Optional, yours, and not shipped: ["http://mirror.one/", "http://mirror.two/"]
# or {"label": "http://mirror.one/"}. Whatever is here fills the Server dropdown,
# along with the servers you have actually used.
MIRRORS_PATH = HERE / "mirrors.json"
LOG_PATH = HERE / "s2downloader.log"           # the log panes, kept after you close

# depot_version_crc_sha256.ext
NAME_RE = re.compile(r"^(\d+)_(\d+)_([0-9A-Fa-f]{8})_([0-9A-Fa-f]{64})\.(blob|dat)$")
# Mirrors do not all run the same index. Plain nginx autoindex writes one <a>
# per line followed by the date and the byte count; nginx fancyindex, Apache and
# Caddy write an HTML table instead, with human sizes like "3.5 KiB". Both are
# understood, because a mirror whose index does not parse looks exactly like an
# empty archive.
ENTRY_RE = re.compile(
    r'<a href="([^"?]+)">[^<]*</a>\s+'
    r'(\d{2}-[A-Za-z]{3}-\d{4}\s+\d{2}:\d{2})\s+'
    r'([0-9-]+)'
)
# a table row: the link cell, then the remaining cells of that row
ROW_RE = re.compile(r'<a href="([^"?]+)"[^>]*>.*?</a>\s*</t[dh]>(.*?)</tr>',
                    re.I | re.S)
CELL_RE = re.compile(r'<t[dh][^>]*>(.*?)</t[dh]>', re.I | re.S)
TAG_RE = re.compile(r'<[^>]+>')
# "1234", "3.5 KiB", "1.2K", "-"
SIZE_RE = re.compile(r'^([\d.,]+)\s*([KMGTP])?i?B?$', re.I)

# What "Process" pulls out of an extracted build. Source 1 depots keep media
# both loose on disk and inside .vpk archives; the loose half needs no tools.
MEDIA_KINDS = {
    "images": (".vtf", ".tga", ".png", ".jpg", ".jpeg", ".bmp", ".gif", ".psd",
               ".ico", ".pcx", ".dds"),
    "audio": (".wav", ".mp3", ".ogg", ".flac", ".aiff", ".mid"),
    "videos": (".bik", ".avi", ".mov", ".mp4", ".mpg", ".mpeg", ".wmv", ".roq",
               ".webm", ".ogv"),
}
# multi-part archives are opened through their _dir file, not one part at a time
VPK_PART_RE = re.compile(r"_\d{3}\.vpk$", re.I)
# The GUI and the CLI ship in the same release and look alike. Handed a flag,
# the GUI treats it as a filename and says so, then sits there with a window
# open - so its own complaint is what tells us the wrong one was picked.
S2V_GUI_SIGNS = ("[mainform]", "'-i' does not exist", "'-o' does not exist",
                 "'-e' does not exist", "'-d' does not exist")
# Flags differ between Source2Viewer releases, so this is only a starting point:
# it is editable on the tab, and "Tool help" prints what your build accepts.
S2V_ARGS = '-i "{input}" -o "{output}" -e "{ext}" -d'
BUILD_RE = re.compile(r"^(\d+)\s*-\s*(.*?)_v(\d+)$")

STATUS_QUEUED = "queued"
STATUS_ACTIVE = "downloading"
STATUS_DONE = "done"
STATUS_SKIP = "already have"
STATUS_ERR = "error"
STATUS_STOP = "stopped"
STATUS_BAD = "hash mismatch"


# --------------------------------------------------------------------------- helpers
def human(n) -> str:
    if n is None:
        return "-"
    n = float(n)
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if abs(n) < 1024.0:
            return f"{n:,.0f} {unit}" if unit == "B" else f"{n:,.1f} {unit}"
        n /= 1024.0
    return f"{n:,.1f} PB"


def parse_size(text: str):
    """A size cell -> (bytes, rounded?).

    Byte counts are exact. "3.5 KiB" is not: it stands for anything between
    3.45 and 3.55 KiB, and callers have to know that before they compare it
    with a file on disk."""
    t = text.strip().replace(" ", " ")
    if not t or t == "-":
        return 0, False
    m = SIZE_RE.match(t)
    if not m:
        return 0, False
    try:
        n = float(m.group(1).replace(",", ""))
    except ValueError:
        return 0, False
    unit = (m.group(2) or "").upper()
    if not unit:
        return int(n), False
    return int(n * (1024 ** ("KMGTP".index(unit) + 1))), True


def size_match(actual: int, listed: int, approx: bool = False) -> bool:
    """Is the file on disk the size the listing said it would be?

    When the index only publishes rounded sizes, an exact comparison calls
    every finished file unfinished - and the download path answers that by
    deleting it and fetching it again. So a rounded size is matched to the
    precision it was given in; the sha256 in the filename stays the real
    check either way."""
    if not listed:
        return True
    if actual == listed:
        return True
    return approx and abs(actual - listed) <= listed * 0.06


def mirror_eta(sizes, agg_bps: float, conn_bps: float):
    """Seconds a mirror run should take, or None if nothing has been measured.

    Speeds differ by orders of magnitude between mirrors, so nothing here is
    assumed - these rates come from downloads this session has actually done.
    One file only ever gets one connection, so a single huge file sets the floor
    however many threads are running."""
    if not sizes or agg_bps <= 0:
        return None
    floor = max(sizes) / conn_bps if conn_bps > 0 else 0.0
    return max(sum(sizes) / agg_bps, floor)


def duration(secs: float) -> str:
    if secs < 90:
        return f"{int(secs)} seconds"
    if secs < 5400:
        return f"about {round(secs / 60)} minutes"
    return f"about {secs / 3600:.1f} hours"


def bar(fraction, width: int = 10) -> str:
    """A progress bar for a table cell - Treeview holds text, not widgets."""
    f = max(0.0, min(1.0, float(fraction or 0)))
    filled = int(round(f * width))
    return "█" * filled + "░" * (width - filled) + f" {f * 100:5.1f}%"


def human_speed(bps: float) -> str:
    return human(bps) + "/s" if bps else ""


def eta(remaining: float, bps: float) -> str:
    if not bps or remaining <= 0:
        return "-"
    s = int(remaining / bps)
    h, s = divmod(s, 3600)
    m, s = divmod(s, 60)
    return f"{h}:{m:02d}:{s:02d}" if h else f"{m}:{s:02d}"


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def safe_name(name: str) -> str:
    return re.sub(r'[<>:"|?*\\]', "_", name).strip()


def parse_stamp(s: str):
    """'2003-09-10+13:11:59.0156250000' -> POSIX seconds. The lists are UTC."""
    s = s.strip().replace("+", " ").split(".")[0]
    try:
        return datetime.strptime(s, "%Y-%m-%d %H:%M:%S").replace(
            tzinfo=timezone.utc).timestamp()
    except ValueError:
        return None


def log_to_disk(msg: str, tag: str = ""):
    """Keep the log panes after the window closes - they're the only record of
    what a long run did."""
    try:
        with open(LOG_PATH, "a", encoding="utf-8") as fh:
            fh.write(f"{time.strftime('%Y-%m-%d %H:%M:%S')} {tag}{msg}\n")
    except Exception:                                               # noqa: BLE001
        pass


def out_folder_name(dep: str, name: str, ver: str) -> str:
    """`220 - Half-Life 2_v10`, or plain `220_v10` when the depot has no name.

    The extractor *removes* the characters Windows forbids rather than
    replacing them, so this removes them too - otherwise the app would look for
    the output in a folder the extractor never created."""
    # shared depots list every game that used them; a folder wants one name,
    # and never the "(+3 more)" marker that belongs in the table
    first = (name or "").split(" / ")[0]
    nm = re.sub(r'[<>:"|?*\\/]', "", first).strip(" .")[:48].strip(" .")
    return f"{dep} - {nm}_v{ver}" if nm else f"{dep}_v{ver}"


def short_name(name: str, keep: int = 2) -> str:
    """Shared depots are used by a dozen games; show a couple and count the rest."""
    parts = [p.strip() for p in (name or "").split(" / ") if p.strip()]
    if len(parts) <= keep:
        return name or ""
    return " / ".join(parts[:keep]) + f"  (+{len(parts) - keep} more)"


# --------------------------------------------------------------------------- listings
@dataclass
class Entry:
    name: str
    is_dir: bool
    size: int
    date: str
    approx: bool = False        # the index only gave a rounded size ("3.5 KiB")


class Listing:
    """Fetches + caches nginx autoindex directory listings."""

    def __init__(self):
        self.mem = {}
        CACHE_DIR.mkdir(parents=True, exist_ok=True)

    @staticmethod
    def _cache_file(url: str) -> Path:
        return CACHE_DIR / (hashlib.sha1(url.encode()).hexdigest()[:16] + ".json")

    def age(self, url: str):
        """Seconds since this listing was cached, or None if it never was."""
        cf = self._cache_file(url)
        try:
            return time.time() - json.loads(cf.read_text("utf-8"))["at"]
        except Exception:
            return None

    def _read_cache(self, url: str):
        try:
            raw = json.loads(self._cache_file(url).read_text("utf-8"))
            entries = [Entry(*e) for e in raw["entries"]]
        except Exception:
            return None
        # An empty listing means the index was not understood, not that the
        # archive is empty - and once cached it would keep the depot list empty
        # forever. Throw it away and ask again.
        return entries or None

    def get(self, url: str, refresh: bool = False):
        if not refresh and url in self.mem:
            return self.mem[url]
        cf = self._cache_file(url)
        if not refresh:
            cached = self._read_cache(url)
            if cached is not None:
                self.mem[url] = cached
                return cached
        try:
            entries = self._fetch(url)
        except Exception:
            # this server times out often - a failed refresh must not lose the
            # copy we already have. Callers show the cache age, so a fallback
            # is visible as "cached 2h ago" instead of "fetched just now".
            cached = self._read_cache(url)
            if cached is not None:
                self.mem[url] = cached
                return cached
            raise
        self.mem[url] = entries
        try:
            cf.write_text(json.dumps(
                {"url": url, "at": time.time(),
                 "entries": [[e.name, e.is_dir, e.size, e.date, e.approx]
                             for e in entries]}), "utf-8")
        except Exception:
            pass
        return entries

    @staticmethod
    def _fetch(url: str):
        parts = urlsplit(url)
        if not parts.hostname:
            # a typo in the Server field, otherwise this surfaces deep inside
            # http.client as an unreadable AttributeError
            raise ValueError(f'"{url}" is not a valid address - check the '
                             f'"Server" field at the top')
        cls = http.client.HTTPSConnection if parts.scheme == "https" else http.client.HTTPConnection
        conn = cls(parts.hostname, parts.port, timeout=TIMEOUT)
        try:
            path = quote(parts.path or "/", safe="/%")
            conn.request("GET", path, headers={"User-Agent": UA, "Accept-Encoding": "identity"})
            resp = conn.getresponse()
            if resp.status != 200:
                raise IOError(f"HTTP {resp.status} {resp.reason} for {url}")
            html = resp.read().decode("utf-8", "replace")
        finally:
            conn.close()

        out = []
        for href, size, date in Listing._rows(html):
            if href.startswith("../") or href in ("../", "/"):
                continue
            is_dir = href.endswith("/")
            name = unquote(href[:-1] if is_dir else href)
            n, approx = parse_size(size)
            out.append(Entry(name, is_dir, n, date.strip(), approx))
        if not out:
            raise IOError(f"nothing readable in the index at {url} - the server "
                          f"answered, but its file list is in a format this "
                          f"version does not understand")
        out.sort(key=lambda e: (not e.is_dir, e.name.lower()))
        return out

    @staticmethod
    def _rows(html: str):
        """(href, size text, date text) for every row, whichever index this is."""
        rows = [(href, size, date)
                for href, date, size in ENTRY_RE.findall(html)]
        if rows:
            return rows
        for href, rest in ROW_RE.findall(html):
            cells = [TAG_RE.sub("", c).replace("&nbsp;", " ").strip()
                     for c in CELL_RE.findall(rest)]
            # the two remaining columns are a size and a date, but their order
            # differs between servers, so they are told apart by shape
            size = next((c for c in cells if SIZE_RE.match(c) or c == "-"), "-")
            date = next((c for c in cells if c is not size and c != "-"), "")
            rows.append((href, size, date))
        return rows


# --------------------------------------------------------------------------- download
@dataclass
class Job:
    url: str
    rel: str                    # path relative to the save folder
    size: int = 0
    sha256: str = ""
    status: str = STATUS_QUEUED
    done: int = 0
    speed: float = 0.0
    error: str = ""
    iid: str = ""               # treeview row id
    dest: str = ""              # absolute override: mirror files are written
                                # into the torrent's own layout, not the save folder
    overwrite: bool = False     # the file already exists but is half-downloaded
                                # by qBittorrent: fetch it anyway, replace at the end
    approx: bool = False        # size came rounded from the index, so it is only
                                # good to the precision it was printed at


class Conn:
    """Keep-alive HTTP connection with one automatic reconnect."""

    def __init__(self, base_url: str):
        p = urlsplit(base_url)
        self.https = p.scheme == "https"
        self.host, self.port = p.hostname, p.port
        self.c = None

    def _open(self):
        cls = http.client.HTTPSConnection if self.https else http.client.HTTPConnection
        self.c = cls(self.host, self.port, timeout=TIMEOUT)

    def get(self, path: str, headers: dict):
        for attempt in (0, 1):
            if self.c is None:
                self._open()
            try:
                self.c.request("GET", path, headers=headers)
                return self.c.getresponse()
            except Exception:
                self.close()
                if attempt:
                    raise
        raise IOError("unreachable")

    def close(self):
        try:
            if self.c:
                self.c.close()
        except Exception:
            pass
        self.c = None


class Downloader:
    def __init__(self):
        self.jobs = []
        self.q = queue.Queue()
        # mirror downloads jump the line: they hold a torrent paused while they
        # run, so they must not wait behind a restored queue of 500 files
        self.urgent = queue.Queue()
        self.lock = threading.Lock()
        self.dirty = set()                    # indices of jobs whose row changed
        self.running = False
        self.stop_flag = False
        self.pause = threading.Event()
        self.pause.set()                      # set == not paused
        self.workers = []
        self.save_dir = Path.home() / "steam2"
        self.n_workers = 4
        self.verify = True
        self.retries = 4

    # ---- queue management
    def add(self, jobs, urgent: bool = False):
        with self.lock:
            base = len(self.jobs)
            self.jobs.extend(jobs)
            for i in range(len(jobs)):
                self.dirty.add(base + i)
        lane = self.urgent if urgent else self.q
        for j in jobs:
            lane.put(j)
        if self.running:
            self._ensure_workers()

    def clear_finished(self):
        with self.lock:
            self.jobs = [j for j in self.jobs
                         if j.status not in (STATUS_DONE, STATUS_SKIP)]
            self.dirty = set(range(len(self.jobs)))

    def requeue_failed(self):
        again = []
        with self.lock:
            for i, j in enumerate(self.jobs):
                if j.status in (STATUS_ERR, STATUS_STOP, STATUS_BAD):
                    j.status, j.error, j.speed = STATUS_QUEUED, "", 0.0
                    self.dirty.add(i)
                    again.append(j)
        for j in again:
            self.q.put(j)
        if self.running:
            self._ensure_workers()
        return len(again)

    def mark(self, job: Job):
        with self.lock:
            try:
                self.dirty.add(self.jobs.index(job))
            except ValueError:
                pass

    def stats(self):
        with self.lock:
            total = sum(j.size for j in self.jobs)
            done = sum(j.size if j.status in (STATUS_DONE, STATUS_SKIP) else j.done
                       for j in self.jobs)
            speed = sum(j.speed for j in self.jobs if j.status == STATUS_ACTIVE)
            counts = {}
            for j in self.jobs:
                counts[j.status] = counts.get(j.status, 0) + 1
        return total, done, speed, counts

    # ---- run control
    def start(self):
        self.stop_flag = False
        self.running = True
        self.pause.set()
        self._ensure_workers()

    def _ensure_workers(self):
        self.workers = [t for t in self.workers if t.is_alive()]
        while len(self.workers) < self.n_workers:
            t = threading.Thread(target=self._worker, daemon=True)
            t.start()
            self.workers.append(t)

    def stop(self):
        self.stop_flag = True
        self.running = False
        self.pause.set()
        try:
            while True:
                self.q.get_nowait()
        except queue.Empty:
            pass

    def _wait_if_paused(self):
        while not self.pause.is_set() and not self.stop_flag:
            time.sleep(0.15)

    # ---- worker
    def _worker(self):
        conn = None
        while not self.stop_flag:
            self._wait_if_paused()
            try:
                job = self.urgent.get_nowait()          # line-jumpers first
            except queue.Empty:
                try:
                    job = self.q.get(timeout=0.5)
                except queue.Empty:
                    break
            if self.stop_flag:
                job.status = STATUS_STOP
                self.mark(job)
                break
            if conn is None:
                conn = Conn(job.url)
            job.status = STATUS_ACTIVE
            job.error = ""
            self.mark(job)
            for attempt in range(self.retries):
                try:
                    self._download(job, conn)
                    break
                except Exception as exc:                       # noqa: BLE001
                    conn.close()
                    if self.stop_flag:
                        job.status = STATUS_STOP
                        break
                    job.error = f"{type(exc).__name__}: {exc}"
                    if attempt == self.retries - 1:
                        job.status = STATUS_ERR
                    else:
                        time.sleep(1.5 * (attempt + 1))
                finally:
                    self.mark(job)
            job.speed = 0.0
            self.mark(job)
        if conn:
            conn.close()

    def _download(self, job: Job, conn: Conn):
        dest = Path(job.dest) if job.dest else self.save_dir / job.rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        part = dest.with_name(dest.name + ".part")

        # already on disk? (size check only - re-hashing terabytes on every restart
        # would be unusable; use "Verify on disk" for a full check)
        # A mirror job points at a file qBittorrent is midway through. It may
        # already be full size (preallocated) while being full of holes, so the
        # size check must not skip it - and its partial data must not be thrown
        # away up front. Download beside it and replace it only once verified.
        if dest.exists() and not job.overwrite:
            if size_match(dest.stat().st_size, job.size, job.approx):
                job.done = job.size or dest.stat().st_size
                job.status = STATUS_SKIP
                return
            dest.unlink()

        start = part.stat().st_size if part.exists() else 0
        # a .part bigger than the whole file is junk and gets restarted - but a
        # rounded size is not the whole file, so leave room before throwing away
        # a nearly-finished download
        limit = job.size * 1.06 if job.approx else job.size
        if job.size and start >= limit:
            start = 0
            if part.exists():
                part.unlink()

        h = hashlib.sha256()
        if start:
            with open(part, "rb") as f:
                for b in iter(lambda: f.read(1 << 20), b""):
                    h.update(b)

        path = quote(urlsplit(job.url).path, safe="/%")
        headers = {"User-Agent": UA, "Accept-Encoding": "identity",
                   "Connection": "keep-alive"}
        if start:
            headers["Range"] = f"bytes={start}-"

        resp = conn.get(path, headers)
        if resp.status == 416:                       # part is already the whole file
            resp.read()
            resp = None
        elif resp.status == 200 and start:           # server ignored Range
            start, h = 0, hashlib.sha256()
        elif resp.status not in (200, 206):
            body = resp.read(512)
            raise IOError(f"HTTP {resp.status} {resp.reason} {body[:80]!r}")

        if resp is not None:
            length = resp.getheader("Content-Length")
            total = start + int(length) if length else job.size
            if total:
                job.size = total
            job.done = start
            mode = "ab" if start else "wb"
            t0, b0 = time.time(), start
            with open(part, mode) as f:
                while True:
                    self._wait_if_paused()
                    if self.stop_flag:
                        resp.close()
                        job.status = STATUS_STOP
                        return
                    block = resp.read(CHUNK)
                    if not block:
                        break
                    f.write(block)
                    h.update(block)
                    job.done += len(block)
                    now = time.time()
                    if now - t0 >= 0.5:
                        inst = (job.done - b0) / (now - t0)
                        job.speed = inst if not job.speed else job.speed * 0.6 + inst * 0.4
                        t0, b0 = now, job.done
                        self.mark(job)
            resp.close()

        if not size_match(part.stat().st_size, job.size, job.approx):
            raise IOError(f"short read {part.stat().st_size}/{job.size}")

        if self.verify and job.sha256 and h.hexdigest().lower() != job.sha256.lower():
            job.status = STATUS_BAD
            job.error = "sha256 mismatch (kept as .bad)"
            part.replace(part.with_name(part.name + ".bad"))
            return

        part.replace(dest)
        job.done = job.size or dest.stat().st_size
        job.status = STATUS_DONE


# --------------------------------------------------------------------------- blob reading
BLOB_PLAIN, BLOB_COMPRESSED = 0x5001, 0x4301
NO_NODE = 0xFFFFFFFF


class ManifestError(Exception):
    pass


def _inflate(data: bytes) -> bytes:
    """Decompress a compressed blob. The header size varies between dumps, so
    the zlib stream is located rather than assumed."""
    for off in range(0, 32):        # 0 covers a bare zlib stream, e.g. key 3
        if data[off:off + 1] != b"\x78":
            continue
        try:
            out = zlib.decompressobj().decompress(data[off:])
        except zlib.error:
            continue
        if out:
            return out
    raise ManifestError("could not decompress this blob")


def blob_records(data: bytes) -> dict:
    """{integer key: value bytes} from a steam2 blob container.

    Layout: u16 magic, u32 total size, u32 slack, then records of
    u16 key size, u32 value size, key, value. Everything little-endian."""
    magic = int.from_bytes(data[:2], "little")
    if magic == BLOB_COMPRESSED:
        data = _inflate(data)
        magic = int.from_bytes(data[:2], "little")
    if magic != BLOB_PLAIN:
        raise ManifestError(f"not a blob container (magic {magic:#06x})")
    total = int.from_bytes(data[2:6], "little")
    slack = int.from_bytes(data[6:10], "little")
    stop = len(data)
    if 10 < total <= len(data) and slack < total:
        stop = total - slack
    out, pos = {}, 10
    while pos + 6 <= stop:
        ksz = int.from_bytes(data[pos:pos + 2], "little")
        vsz = int.from_bytes(data[pos + 2:pos + 6], "little")
        pos += 6
        if ksz > 64 or pos + ksz + vsz > len(data):
            break
        key = data[pos:pos + ksz]
        val = data[pos + ksz:pos + ksz + vsz]
        pos += ksz + vsz
        if ksz == 4:
            out[int.from_bytes(key, "little")] = val
    return out


def parse_manifest(raw: bytes, depot=None, version=None):
    """[(path, size), ...] from a manifest.

    56-byte header of 14 u32s, then one 28-byte node per entry, then a table of
    NUL-terminated names. A node is 7 u32s: name offset, size, file id, flags,
    parent, next sibling, first child.

    Raises ManifestError unless the bytes really are a manifest: the version
    field, the self-declared byte length, and - when the caller knows them -
    the depot and version ids recorded in the header must all agree. A wrong
    guess is refused rather than shown as a file list."""
    if len(raw) < 56:
        raise ManifestError("too short to be a manifest")
    ver, app, vid, nodes, nfiles, _r, binsize, _strsize = struct.unpack_from(
        "<8I", raw, 0)
    names_at = 56 + nodes * 28
    if ver not in (3, 4) or not nodes or nodes > 4_000_000 or names_at > len(raw):
        raise ManifestError("this doesn't look like a manifest")
    if binsize != len(raw):
        raise ManifestError("the manifest's own length field disagrees")
    if depot is not None and str(app) != str(depot):
        raise ManifestError(f"that manifest belongs to depot {app}, not {depot}")
    if version is not None and vid != version:
        raise ManifestError(f"that manifest is version {vid}, not {version}")

    ents = []
    for i in range(nodes):
        off, size, fid, flags, parent = struct.unpack_from("<5I", raw, 56 + i * 28)
        end = raw.find(b"\0", names_at + off)
        if off > len(raw) - names_at or end < 0:
            raise ManifestError("the name table is out of range")
        ents.append((raw[names_at + off:end].decode("utf-8", "replace"),
                     size, fid, flags, parent))

    # "is a file" is recorded differently across manifest versions; pick the
    # rule that reproduces the file count the header itself states
    by_flag = [i for i, e in enumerate(ents) if e[3]]
    by_id = [i for i, e in enumerate(ents) if e[2] != NO_NODE]
    idx = by_flag if len(by_flag) == nfiles else (
        by_id if len(by_id) == nfiles else by_flag)

    def path_of(i):
        parts = []
        while i != NO_NODE and i < len(ents) and len(parts) < 256:
            if ents[i][0]:                  # the root node is unnamed - skip it,
                parts.append(ents[i][0])    # or every path starts with a slash
            i = ents[i][4]
        return "/".join(reversed(parts))

    return [(path_of(i), ents[i][1]) for i in idx]


def manifest_of(blob_path: Path):
    """The file list recorded in one .blob.

    Key 3 of the blob holds a compressed container of its own, and key 0 of
    *that* is the manifest. Older dumps vary, so every plausible payload is
    tried and the one that validates as this depot's manifest wins."""
    p = Path(blob_path)
    m = NAME_RE.match(p.name)
    depot = m.group(1) if m else None
    version = int(m.group(2)) if m else None

    body = blob_records(p.read_bytes()).get(3)
    if body is None:
        raise ManifestError("this blob has no manifest record")
    tries = []
    if body[:2] in (b"\x01\x50", b"\x01\x43"):      # a container of its own
        try:
            tries += list(blob_records(body).values())
        except ManifestError:
            pass
    try:
        tries.append(_inflate(body))
    except ManifestError:
        pass
    tries.append(body)
    # Two passes. First insist the manifest names this depot and version, which
    # makes picking the wrong payload impossible. Then fall back to the purely
    # structural check, because a handful of depots are mislabelled upstream -
    # blob 55420_0 carries a valid manifest that says depot 55421.
    why = ""
    for expect in ((depot, version), (None, None)):
        for cand in tries:
            try:
                return parse_manifest(cand, expect[0], expect[1])
            except (ManifestError, struct.error, IndexError) as exc:
                why = str(exc)
                continue
    raise ManifestError(f"could not read the manifest out of this blob ({why})")


# --------------------------------------------------------------------------- depot names
class SteamNames:
    """depot id -> game name, fetched once and cached on disk.

    The dump itself carries no names anywhere, so they have to come from
    outside. Two sources, in order:

    1. `depot_labels.tsv` from the steam2-winfsp project - a ready-made list
       covering all 10,876 depots in this exact dump, one request.
    2. api.steamcmd.net, for anything the list misses. It serves the public
       appinfo record for an app id, which names that app's depots. steam2-era
       depots sit right next to the app that owns them (app 10000 owns depots
       10001-10007), so an unknown depot is looked up by its own id and then a
       few ids below it, and each answer names all of that app's depots at once.

    Every answer is cached - including "no such app" - so a second run costs
    nothing and a stopped fetch resumes where it left off.
    """

    API = "https://api.steamcmd.net/v1/info/{}"
    # a ready-made depot -> game label list for exactly this dump (10,876 rows)
    LABELS = ("https://raw.githubusercontent.com/dr3murr/steam2-winfsp/"
              "main/data/depot_labels.tsv")
    LOOKBACK = 12            # how far below a depot id its owner app may sit
    WORKERS = 4              # polite concurrency against a free third-party API

    def __init__(self, path: Path):
        self.path = path
        self.apps = {}       # "10000" -> "Enemy Territory: Quake Wars"  ("" = no such app)
        self.depots = {}     # "10002" -> {"name": ..., "app": "10000"}
        self.lock = threading.Lock()
        self.dirty = False
        self.load()

    def load(self):
        try:
            d = json.loads(self.path.read_text("utf-8"))
            self.apps = {str(k): (v or "") for k, v in d.get("apps", {}).items()}
            self.depots = {str(k): v for k, v in d.get("depots", {}).items()
                           if isinstance(v, dict)}
        except Exception:
            pass

    def save(self):
        with self.lock:
            if not self.dirty:
                return
            data = json.dumps({"apps": self.apps, "depots": self.depots})
            self.dirty = False
        try:
            self.path.parent.mkdir(parents=True, exist_ok=True)
            tmp = self.path.with_suffix(".tmp")
            tmp.write_text(data, "utf-8")
            tmp.replace(self.path)
        except Exception:
            pass

    def names(self) -> dict:
        with self.lock:
            return {d: v["name"] for d, v in self.depots.items() if v.get("name")}

    @staticmethod
    def _score(depot: int, appid: int):
        """How likely is this app to be the depot's real owner? Bigger is better.

        The app id itself always wins; otherwise the owner is nearly always the
        closest app id *below* the depot (app 2505 owns depot 2507)."""
        if appid == depot:
            return (2, 0)
        if appid < depot:
            return (1, appid - depot)         # closer below = less negative = better
        return (0, -appid)                    # above: last resort, prefer the nearest

    def _record(self, depot, appid, name, src="api"):
        depot, appid = str(depot), str(appid)
        cur = self.depots.get(depot)
        if cur:
            if cur.get("src") == "labels" and src != "labels":
                return                            # the label list is authoritative
            if src != "labels" and cur.get("app", "").isdigit():
                if (self._score(int(depot), int(cur["app"]))
                        >= self._score(int(depot), int(appid))):
                    return
        self.depots[depot] = {"name": name, "app": appid, "src": src}
        self.dirty = True

    def fetch_labels(self) -> int:
        """Pull the ready-made depot -> game list. One request, names everything.

        Falls back to the per-app Steam lookups below for anything it misses."""
        req = Request(self.LABELS, headers={"User-Agent": UA})
        with urlopen(req, timeout=60) as r:
            text = r.read().decode("utf-8", "replace")
        n = 0
        with self.lock:
            for line in text.splitlines():
                dep, _, name = line.partition("\t")
                dep, name = dep.strip(), name.strip()
                if dep.isdigit() and name:
                    self._record(dep, dep, name, src="labels")
                    n += 1
        self.save()
        return n

    def fetch_app(self, appid: str):
        """appinfo for one app id. Returns the name, or None if there is no app."""
        appid = str(appid)
        with self.lock:
            if appid in self.apps:
                return self.apps[appid] or None
        req = Request(self.API.format(appid), headers={"User-Agent": UA})
        with urlopen(req, timeout=25) as r:
            data = json.loads(r.read().decode("utf-8", "replace"))
        app = (data.get("data") or {}).get(appid) or {}
        name = ((app.get("common") or {}).get("name") or "").strip()
        depots = [d for d in (app.get("depots") or {}) if str(d).isdigit()]
        with self.lock:
            self.apps[appid] = name
            self.dirty = True
            if name:
                self._record(appid, appid, name)     # depot id == app id is common
                for d in depots:
                    self._record(d, appid, name)
        return name or None

    def known(self, depot) -> bool:
        with self.lock:
            return str(depot) in self.depots

    def resolve(self, depot_ids, on_progress=None, should_stop=None):
        """Name every depot we don't know yet. Returns (named, asked, errors)."""
        want = sorted({int(d) for d in depot_ids if str(d).isdigit()
                       and not self.known(d)})
        if not want:
            return 0, 0, 0
        pending = set(want)
        # every app id worth asking about, lowest first: owners sit below depots
        cands = sorted({c for d in want
                        for c in range(max(1, d - self.LOOKBACK), d + 1)})
        stats = {"asked": 0, "errors": 0}
        stop = threading.Event()

        def worth(c):
            return any(d in pending for d in range(c, c + self.LOOKBACK + 1))

        def job(c):
            if stop.is_set():
                return
            with self.lock:
                if str(c) in self.apps:              # already known, no request
                    return
            if not worth(c):
                return
            try:
                self.fetch_app(str(c))
                stats["asked"] += 1
            except Exception:
                stats["errors"] += 1
                time.sleep(1.5)                      # back off, then carry on
                return
            time.sleep(0.05)

        with ThreadPoolExecutor(max_workers=self.WORKERS) as pool:
            futs = []
            for i, c in enumerate(cands):
                if should_stop and should_stop():
                    stop.set()
                    break
                futs.append(pool.submit(job, c))
                if len(futs) >= self.WORKERS * 4:    # keep the window small so
                    for f in futs:                   # "worth()" stays accurate
                        f.result()
                    futs = []
                    pending = {d for d in pending if not self.known(d)}
                    if on_progress:
                        on_progress(i + 1, len(cands), len(want) - len(pending),
                                    stats["errors"])
                    if i % 400 < self.WORKERS * 4:
                        self.save()
            for f in futs:
                f.result()
        self.save()
        named = sum(1 for d in want if self.known(d))
        return named, stats["asked"], stats["errors"]


# --------------------------------------------------------------------------- qbittorrent
class QBitError(Exception):
    pass


class QBit:
    """Minimal qBittorrent WebUI (api/v2) client - stdlib only.

    Used to grab depot files from an already-added torrent instead of pulling
    them over HTTP from the (slow) origin server.
    """

    PRIO_SKIP, PRIO_NORMAL, PRIO_HIGH, PRIO_MAX = 0, 1, 6, 7

    def __init__(self, base_url: str, user: str = "", pw: str = ""):
        self.base = (base_url or "").strip().rstrip("/")
        if self.base and "://" not in self.base:
            self.base = "http://" + self.base
        self.user, self.pw = user, pw
        self.jar = http.cookiejar.CookieJar()
        self.opener = build_opener(HTTPCookieProcessor(self.jar))
        # The session cookie is tracked by hand as well as by the jar, so the
        # client can tell whether it is actually authenticated - and so a jar
        # that declines to store it isn't fatal.
        self.sid = ""
        self.sid_name = "SID"
        self.lock = threading.RLock()      # polling and the UI share one client

    LOGIN = "/api/v2/auth/login"
    # 4.x calls it SID; 5.x calls it QBT_SID_<port>, e.g. QBT_SID_8080
    SESSION_RE = re.compile(r"\s*((?:QBT_)?SID[0-9A-Za-z_]*)=([^;]+)")

    @staticmethod
    def _is_session(name: str) -> bool:
        return name == "SID" or name.startswith("QBT_SID")

    def _grab_sid(self, headers):
        for raw in (headers.get_all("Set-Cookie") or []):
            m = self.SESSION_RE.match(raw)
            if m:
                self.sid_name, self.sid = m.group(1), m.group(2).strip()
        if not self.sid:                   # whatever the jar did manage to keep
            for c in self.jar:
                if self._is_session(c.name):
                    self.sid_name, self.sid = c.name, c.value
                    break

    def _req(self, path: str, data=None, timeout: int = 20, retry: bool = True):
        """Returns (status, body, headers). 4xx/5xx come back as a status,
        not an exception, so callers can explain them properly."""
        with self.lock:
            url = self.base + path
            body = urlencode(data).encode() if data is not None else None
            req = Request(url, data=body, method="POST" if body is not None else "GET")
            req.add_header("Referer", self.base)      # qB rejects cross-site posts
            req.add_header("Origin", self.base)
            if self.sid:
                req.add_header("Cookie", f"{self.sid_name}={self.sid}")
            try:
                with self.opener.open(req, timeout=timeout) as r:
                    st, txt, hdrs = (r.status, r.read().decode("utf-8", "replace"),
                                     r.headers)
            except HTTPError as e:
                st, txt, hdrs = e.code, e.read().decode("utf-8", "replace"), e.headers
            except Exception as exc:                                # noqa: BLE001
                raise QBitError(f"{type(exc).__name__}: {exc}") from exc
            self._grab_sid(hdrs)
            # sessions expire (an hour by default) - a queue running overnight
            # would otherwise die on a 403 halfway through
            if st == 403 and retry and path != self.LOGIN and (self.user or self.pw):
                self.sid = ""
                self.login(verify=False)
                return self._req(path, data, timeout, retry=False)
            return st, txt, hdrs

    def login(self, verify: bool = True):
        """Authenticate, then prove the session actually works."""
        if not self.base:
            raise QBitError("no qBittorrent URL set")
        self.sid = ""                      # never carry a dead session into a login
        st, body, _ = self._req(self.LOGIN,
                                {"username": self.user, "password": self.pw},
                                retry=False)
        low = body.strip().lower()
        # A rejected login looks different across versions: qBittorrent 4.x
        # answers 200 with "Fails.", 5.x answers 401 Unauthorized. Both mean the
        # same thing, and neither may be waved through - treating 401 as "fine"
        # is how a wrong password ends up reported as a session problem.
        if low.startswith("fails") or st == 401:
            raise QBitError(
                "qBittorrent rejected the username or password. Check them in "
                "Tools > Preferences > Web UI. It locks an IP out for a while "
                "after a few wrong tries, so fix them before retrying.")
        if st == 403:
            if "ban" in low:
                raise QBitError(
                    "your IP is temporarily banned by qBittorrent after too many "
                    "failed logins. Restart qBittorrent, or wait it out (an hour "
                    "by default), then try again with the right password.")
            raise QBitError(f"403 on login - qBittorrent refused the request "
                            f"({body[:60]!r})")
        if st == 404:
            raise QBitError("no Web UI at that address (404) - check the port")
        # 2xx: "Ok." with a session cookie normally, or 204 No Content when
        # "bypass authentication for localhost" is on and no login is needed
        if not (200 <= st < 300):
            raise QBitError(f"unexpected login reply: HTTP {st} {body[:80]!r}")
        if low.startswith("ok") and not self.sid:
            raise QBitError(
                "qBittorrent accepted the login but sent no session cookie - "
                "the address may be going through a proxy that strips it.")
        if not verify:
            return "logged in"

        # verify the session rather than assuming it stuck
        st2, _body2, _ = self._req("/api/v2/torrents/info", retry=False)
        if st2 == 403:
            raise QBitError(
                "logged in, but qBittorrent refused the session (403). In "
                "Preferences > Web UI, try turning off 'Enable Host header "
                "validation' / CSRF protection, or use the exact address "
                "qBittorrent lists there.")
        if st2 == 401:
            raise QBitError("qBittorrent wants credentials - fill in the user "
                            "and password above and press Connect")
        if st2 != 200:
            raise QBitError(f"torrents/info returned HTTP {st2}")
        if self.sid:
            return "logged in"
        # no session cookie: either the Web UI wants no login at all, or it is
        # bypassing authentication for this client
        return ("connected (no login required)" if not (self.user or self.pw)
                else "connected (authentication bypassed for this client)")

    def torrents(self):
        st, body, _ = self._req("/api/v2/torrents/info")
        if st in (401, 403):
            raise QBitError("session refused - press Connect again")
        if st != 200:
            raise QBitError(f"torrents/info returned HTTP {st}")
        try:
            return json.loads(body)
        except Exception:
            raise QBitError(f"unexpected reply from qBittorrent: {body[:120]!r}")

    # states qBittorrent reports for a torrent that is NOT running. 4.x says
    # "paused", 5.x says "stopped"; queued and errored ones are not running
    # either, and starting one of those is not "putting it back as we found it"
    STOPPED = ("pauseddl", "pausedup", "stoppeddl", "stoppedup", "queueddl",
               "queuedup", "error", "missingfiles", "unknown")

    def state(self, thash: str) -> str:
        """The torrent's current state, or "" if it cannot be read."""
        st, body, _ = self._req(f"/api/v2/torrents/info?hashes={quote(thash)}")
        if st != 200:
            raise QBitError(f"torrents/info returned HTTP {st}")
        try:
            rows = json.loads(body)
        except Exception:
            raise QBitError("could not read the torrent's state")
        return (rows[0].get("state", "") if rows else "")

    @staticmethod
    def is_running(state: str) -> bool:
        """Was it actually going? An unreadable state counts as running, so we
        err towards putting it back rather than leaving it stopped."""
        return state.lower() not in QBit.STOPPED

    def files(self, thash: str):
        st, body, _ = self._req(f"/api/v2/torrents/files?hash={quote(thash)}")
        if st != 200:
            raise QBitError(f"torrents/files returned HTTP {st}")
        try:
            data = json.loads(body)
        except Exception:
            raise QBitError(f"could not read the file list: {body[:120]!r}")
        # older builds omit "index"; positional order is the id there
        for i, f in enumerate(data):
            f.setdefault("index", i)
        return data

    def set_priority(self, thash: str, ids, priority: int):
        if not ids:
            return
        st, body, _ = self._req("/api/v2/torrents/filePrio",
                                {"hash": thash, "id": "|".join(str(i) for i in ids),
                                 "priority": priority})
        if st != 200:
            raise QBitError(f"filePrio returned HTTP {st} {body[:80]!r}")

    def web_seeds(self, thash: str):
        """Web seeds already on the torrent. [] on builds too old to know."""
        st, body, _ = self._req(f"/api/v2/torrents/webseeds?hash={quote(thash)}")
        if st == 404:
            raise QBitError("this qBittorrent is too old to manage web seeds "
                            "over the Web UI - add it from the torrent's "
                            "properties instead")
        if st != 200:
            raise QBitError(f"webseeds returned HTTP {st}")
        try:
            return [w.get("url", "") for w in json.loads(body)]
        except Exception:
            return []

    def add_web_seeds(self, thash: str, urls):
        st, body, _ = self._req("/api/v2/torrents/addWebSeeds",
                                {"hash": thash, "urls": "|".join(urls)})
        if st == 404:
            raise QBitError("this qBittorrent is too old to add web seeds over "
                            "the Web UI - add it from the torrent's properties")
        if st == 400:
            raise QBitError(f"qBittorrent rejected the URL ({body[:60]!r})")
        if st not in (200, 204):
            raise QBitError(f"addWebSeeds returned HTTP {st}")

    def recheck(self, thash: str):
        st, body, _ = self._req("/api/v2/torrents/recheck", {"hashes": thash})
        if st != 200:
            raise QBitError(f"recheck returned HTTP {st} {body[:60]!r}")

    def pause(self, thash: str):
        # qBittorrent 5.x renamed pause -> stop; try both
        for path in ("/api/v2/torrents/pause", "/api/v2/torrents/stop"):
            try:
                st, _, _ = self._req(path, {"hashes": thash})
                if st == 200:
                    return True
            except QBitError:
                continue
        return False

    def resume(self, thash: str):
        # qBittorrent 5.x renamed resume -> start; try both
        for path in ("/api/v2/torrents/resume", "/api/v2/torrents/start"):
            try:
                st, _, _ = self._req(path, {"hashes": thash})
                if st == 200:
                    return
            except QBitError:
                continue


# --------------------------------------------------------------------------- extractor
class ExtractRunner:
    """Runs extract.exe in the background and streams its output line by line."""

    def __init__(self):
        self.proc = None
        self.thread = None

    @property
    def busy(self) -> bool:
        return self.thread is not None and self.thread.is_alive()

    def run(self, exe: Path, args, cwd: Path, log, done):
        cmd = [str(exe)] + [str(a) for a in args]
        if os.name != "nt":                      # win64 build, needs wine elsewhere
            cmd = ["wine"] + cmd

        def work():
            rc = -1
            try:
                self.proc = subprocess.Popen(
                    cmd, cwd=str(cwd), stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                    text=True, bufsize=1, errors="replace",
                    creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
                for line in self.proc.stdout:
                    log(line.rstrip())
                rc = self.proc.wait()
            except FileNotFoundError:
                log("could not start the extractor - "
                    + ("extract.exe is missing" if os.name == "nt"
                       else "install wine, or build src.zip for your platform"))
            except Exception as exc:                                # noqa: BLE001
                log(f"error running the extractor: {exc}")
            finally:
                self.proc = None
                done(rc)

        self.thread = threading.Thread(target=work, daemon=True)
        self.thread.start()

    def kill(self):
        if self.proc:
            try:
                self.proc.terminate()
            except Exception:
                pass


# --------------------------------------------------------------------------- GUI
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(APP_NAME)
        self.geometry("1180x760")
        self.minsize(940, 600)

        self.listing = Listing()
        self.dl = Downloader()
        self.cur_path = ""                    # remote path relative to base, "" = root
        self.cur_entries = []
        self.filtered = []
        self.depot_rows = []
        self.busy = False

        self.base_var = tk.StringVar(value=DEFAULT_BASE)
        self.dir_var = tk.StringVar(value=str(self.dl.save_dir))
        self.filter_var = tk.StringVar()
        self.regex_var = tk.BooleanVar(value=False)
        self.verify_var = tk.BooleanVar(value=True)
        self.group_var = tk.BooleanVar(value=True)
        self.workers_var = tk.IntVar(value=4)
        self.depot_var = tk.StringVar()
        self.maxver_var = tk.StringVar()
        self.cmd_var = tk.StringVar()
        self.depot_id = ""

        self.ext = ExtractRunner()
        self.edepot_var = tk.StringVar()
        self.ever_var = tk.StringVar()
        self.ecrc_var = tk.StringVar()
        self.efilter_var = tk.StringVar()
        self.out_var = tk.StringVar()
        self.pipe = None                      # active download->extract pipeline
        self.last_out = None                  # folder the last extraction wrote to
        self.stage_dir = None                 # temporary link farm, cleaned up after
        self.tasks = []                       # extractions + processing runs, waiting
        self.task_total = 0                   # how many this run started with
        self.task_pending = False
        self.current_task = None              # the one actually running
        self.unatt_var = tk.BooleanVar(value=False)
        self.history = {}                     # depot -> what was extracted, and where
        try:
            self.history = json.loads(HISTORY_PATH.read_text("utf-8"))
        except Exception:
            pass

        self.qb = None                        # QBit client once connected
        self.qb_torrents = []
        self.qb_hash = ""
        self.qb_save_path = ""
        self.qb_index = {}                    # basename -> file dict from qB
        self.qb_url_var = tk.StringVar(value="http://localhost:8080")
        self.qb_user_var = tk.StringVar()
        self.qb_pass_var = tk.StringVar()
        self.qb_savepw_var = tk.BooleanVar(value=False)
        self.qb_use_var = tk.BooleanVar(value=True)
        self.qb_auto_var = tk.BooleanVar(value=True)
        self.qb_tor_var = tk.StringVar()
        self.qb_status_var = tk.StringVar(value="not connected")
        self.mirror_rows = []                 # incomplete files the torrent wants
        self.msort = ("name", False)          # mirror list: sort column, reversed?
        self.qsort = (None, False)            # queue: None = the order you added
        self.servers = []                     # mirrors you have used, newest first
        self.mirrors = []                     # from mirrors.json, if you have one
        try:
            raw = json.loads(MIRRORS_PATH.read_text("utf-8"))
            self.mirrors = ([str(v) for v in raw.values()]
                            if isinstance(raw, dict) else [str(v) for v in raw])
        except Exception:
            pass
        self.mirror_job = None                # an HTTP mirror run in progress
        self.mirror_recheck_var = tk.BooleanVar(value=False)
        self.qb_webseed_var = tk.StringVar()
        # observed download rates, this session only - they belong to whichever
        # mirror is in use, so they are never persisted or assumed
        self.rate_agg = 0.0                   # bytes/s across all workers
        self.rate_conn = 0.0                  # best bytes/s seen on one file
        self.mirror_status_var = tk.StringVar(value="not connected to qBittorrent")
        # remembered from the last session so the depot list knows where the
        # torrent lives before qBittorrent is connected. Never written to.
        self.torrent_dir_var = tk.StringVar()

        # ---- Process tab: turning an extracted build into plain media files
        self.s2v_var = tk.StringVar()         # Source2Viewer CLI, only needed for vpk
        self.media_var = tk.StringVar()       # where the pulled-out media goes
        self.s2v_args_var = tk.StringVar(value=S2V_ARGS)
        self.kind_vars = {k: tk.BooleanVar(value=True) for k in MEDIA_KINDS}
        self.vpk_var = tk.BooleanVar(value=True)
        self.proc_rows = []                   # extracted builds you can process
        self.proc_busy = False
        self.proc_stop = threading.Event()
        self.proc_proc = None                 # Source2Viewer, while it runs

        self.dfilter_var = tk.StringVar()
        self.depot_stats = []                 # aggregated depot index
        self.dsort = ("depot", False)
        self.snames = SteamNames(NAMES_CACHE)   # fetched from Steam, cached on disk
        self.depot_names = {}
        self.names_stop = threading.Event()
        self.names_busy = False
        self._reload_names()
        self._local_cache = None               # {depot: files you have}, recounted lazily
        self._local_busy = False               # a background recount is running
        self.status_var = tk.StringVar(value="ready")
        self.path_var = tk.StringVar(value="/")
        self.sel_var = tk.StringVar(value="")

        self.first_run = not SETTINGS_PATH.exists()
        self._load_settings()
        self._build()
        self._load_queue()
        self.after(200, self._tick)
        self.protocol("WM_DELETE_WINDOW", self._on_close)
        self.after(300, lambda: self.navigate(""))
        self.after(600, self._autoload_depots)
        self.after(900, self._qb_autoconnect)
        if self.first_run:
            self.nb.select(self.settings_tab)
            self.status_var.set(
                "first run - set the server and the folders here, then press Save. "
                "The depot list builds itself from there.")
        self.after(60000, self._unattended_tick)
        try:                                   # keep the disk log from growing forever
            if LOG_PATH.exists() and LOG_PATH.stat().st_size > 5 << 20:
                LOG_PATH.replace(LOG_PATH.with_suffix(".log.1"))
        except Exception:                                           # noqa: BLE001
            pass

    def after(self, ms, func=None, *args):
        """Background threads hand their results back through after().

        If the window has already been destroyed - you closed the app while a
        scan or a poll was still running - Tk raises instead, and the thread
        dies with a traceback on the console. There is nothing to deliver at
        that point, so drop it quietly."""
        try:
            return super().after(ms, func, *args)
        except (RuntimeError, tk.TclError):
            return None

    # ---- settings
    def _load_settings(self):
        try:
            s = json.loads(SETTINGS_PATH.read_text("utf-8"))
            self.base_var.set(s.get("base", DEFAULT_BASE))
            self.dir_var.set(s.get("save_dir", self.dir_var.get()))
            self.workers_var.set(int(s.get("workers", 4)))
            self.verify_var.set(bool(s.get("verify", True)))
            self.group_var.set(bool(s.get("group_by_depot", True)))
            self.out_var.set(s.get("out_dir", ""))
            self.qb_url_var.set(s.get("qb_url", "http://localhost:8080"))
            self.qb_user_var.set(s.get("qb_user", ""))
            self.qb_pass_var.set(s.get("qb_pass", ""))
            self.qb_savepw_var.set(bool(s.get("qb_save_pw", False)))
            self.qb_use_var.set(bool(s.get("qb_use", True)))
            self.qb_auto_var.set(bool(s.get("qb_autoconnect", True)))
            self.qb_hash = s.get("qb_hash", "")
            self.torrent_dir_var.set(s.get("torrent_dir", ""))
            self.servers = [str(x) for x in s.get("servers", []) if x]
            self.qb_webseed_var.set(s.get("webseed", ""))
            self.s2v_var.set(s.get("s2v_path", ""))
            self.media_var.set(s.get("media_dir", ""))
            self.s2v_args_var.set(s.get("s2v_args", S2V_ARGS))
            if s.get("geometry"):
                self.geometry(s["geometry"])
        except Exception:
            pass

    def _save_settings(self):
        try:
            SETTINGS_PATH.write_text(json.dumps({
                "base": self.base_var.get(),
                "save_dir": self.dir_var.get(),
                "workers": int(self.workers_var.get()),
                "verify": bool(self.verify_var.get()),
                "group_by_depot": bool(self.group_var.get()),
                "out_dir": self.out_var.get(),
                "qb_url": self.qb_url_var.get(),
                "qb_user": self.qb_user_var.get(),
                "qb_pass": self.qb_pass_var.get() if self.qb_savepw_var.get() else "",
                "qb_save_pw": bool(self.qb_savepw_var.get()),
                "qb_use": bool(self.qb_use_var.get()),
                "qb_autoconnect": bool(self.qb_auto_var.get()),
                "qb_hash": self.qb_hash,
                "torrent_dir": self.torrent_dir_var.get(),
                "servers": self.servers,
                "webseed": self.qb_webseed_var.get(),
                "s2v_path": self.s2v_var.get(),
                "media_dir": self.media_var.get(),
                "s2v_args": self.s2v_args_var.get(),
                "geometry": self.geometry(),
            }, indent=2), "utf-8")
        except Exception:
            pass

    # ---- layout
    def _build(self):
        try:
            ttk.Style().theme_use("vista")
        except tk.TclError:
            pass

        top = ttk.Frame(self, padding=(8, 6))
        top.pack(fill="x")
        ttk.Label(top, text="Server:").pack(side="left")
        # editable: pick a known mirror, or just type one
        self.base_combo = ttk.Combobox(top, textvariable=self.base_var, width=28)
        self.base_combo.pack(side="left", padx=(4, 10))
        self._refresh_servers()
        ttk.Label(top, text="Save to:").pack(side="left")
        ttk.Entry(top, textvariable=self.dir_var, width=34).pack(side="left", padx=4)
        ttk.Button(top, text="Browse...", command=self._pick_dir).pack(side="left")
        ttk.Button(top, text="Open folder", command=self._open_dir).pack(side="left", padx=(4, 12))
        ttk.Checkbutton(top, text="verify sha256", variable=self.verify_var).pack(side="left")
        ttk.Checkbutton(top, text="group by depot", variable=self.group_var,
                        command=self._update_cmd).pack(side="left")
        ttk.Label(top, text="  threads:").pack(side="left")
        ttk.Spinbox(top, from_=1, to=16, width=3, textvariable=self.workers_var).pack(side="left")
        ttk.Button(top, text="Refresh listing",
                   command=lambda: self.navigate(self.cur_path, True)).pack(side="right")

        main = ttk.PanedWindow(self, orient="vertical")
        main.pack(fill="both", expand=True, padx=8, pady=(0, 6))

        nb = ttk.Notebook(main)
        self.nb = nb
        main.add(nb, weight=3)
        self._build_depots(nb)
        self._build_browse(nb)
        self._build_depot(nb)
        self._build_extract(nb)
        self._build_qbit(nb)
        self._build_mirror(nb)
        self._build_process(nb)
        self._build_settings(nb)
        nb.bind("<<NotebookTabChanged>>", self._on_tab_changed)
        self._build_queue(main)

        bar = ttk.Frame(self, padding=(8, 4))
        bar.pack(fill="x")
        ttk.Label(bar, textvariable=self.status_var).pack(side="left")
        ttk.Label(bar, textvariable=self.sel_var, foreground="#555").pack(side="right")

    def _build_depots(self, nb):
        f = ttk.Frame(nb, padding=6)
        nb.add(f, text="Depots")
        self.depots_tab = f

        row = ttk.Frame(f)
        row.pack(fill="x", pady=(0, 6))
        ttk.Button(row, text="Load depot list", command=self._load_depots).pack(side="left")
        ttk.Button(row, text="Refresh from server",
                   command=lambda: self._load_depots(True)).pack(side="left", padx=4)
        self.btn_names = ttk.Button(row, text="Fetch names from Steam",
                                    command=self._fetch_names)
        self.btn_names.pack(side="left", padx=(0, 4))
        ttk.Button(row, text="Rescan my files",
                   command=self._rescan_local).pack(side="left")
        ttk.Label(row, text="  Find:").pack(side="left")
        e = ttk.Entry(row, textvariable=self.dfilter_var, width=26)
        e.pack(side="left", padx=4)
        e.bind("<KeyRelease>", lambda _e: self._show_depots())
        ttk.Label(row, text="right-click for actions  |  Find also takes "
                            "have:complete / partial / none / extracted",
                  foreground="#777").pack(side="left", padx=10)
        ttk.Button(row, text="Export CSV", command=self._export_depots).pack(side="right")

        body = ttk.Frame(f)
        body.pack(fill="both", expand=True)
        cols = ("depot", "name", "versions", "blobs", "dats", "total", "local")
        heads = {"depot": "Depot", "name": "Name",
                 "versions": "Versions", "blobs": "Blobs", "dats": "Dats",
                 "total": "Total size", "local": "You have"}
        widths = {"depot": 80, "name": 300, "versions": 80, "blobs": 100,
                  "dats": 110, "total": 110, "local": 120}
        self.dep_tv = ttk.Treeview(body, columns=cols, show="headings",
                                   selectmode="extended")
        for c in cols:
            self.dep_tv.heading(c, text=heads[c], command=lambda x=c: self._sort_depots(x))
            self.dep_tv.column(c, width=widths[c], anchor=("w" if c == "name" else "e"),
                               stretch=(c == "name"))
        sb = ttk.Scrollbar(body, orient="vertical", command=self.dep_tv.yview)
        self.dep_tv.configure(yscrollcommand=sb.set)
        self.dep_tv.pack(side="left", fill="both", expand=True)
        sb.pack(side="left", fill="y")
        self.dep_tv.tag_configure("extracted", background="#e8f5e9")
        self.dep_tv.bind("<Double-1>", self._open_depot_from_list)
        self.dep_tv.bind("<Button-3>", self._depot_menu)
        self.dmenu = tk.Menu(self, tearoff=0)
        self.dmenu.add_command(label="Open in depot picker",
                               command=lambda: self._open_depot_from_list(None))
        self.dmenu.add_command(label="Preview file list (no extract)",
                               command=lambda: self._preview_depot())
        self.dmenu.add_command(label="Download + extract (newest version)",
                               command=self._extract_depot)
        self.dmenu.add_separator()
        self.dmenu.add_command(label="Send to qBittorrent (whole depot)",
                               command=lambda: self._qb_send_depots(False))
        self.dmenu.add_command(label="Send to qBittorrent (only what's missing)",
                               command=lambda: self._qb_send_depots(True))
        self.dmenu.add_separator()
        self.dmenu.add_command(label="Queue HTTP download (whole depot)",
                               command=self._http_queue_depots)
        self.dmenu.add_command(label="Open extracted output",
                               command=self._open_extracted)
        self.dmenu.add_command(label="Copy depot id(s)", command=self._copy_depot_ids)
        self.dmenu.add_separator()
        self.dmenu.add_command(label="Delete this depot's dats (keep blobs)",
                               command=self._delete_dats)

    def _build_browse(self, nb):
        f = ttk.Frame(nb, padding=6)
        nb.add(f, text="Browse")

        row = ttk.Frame(f)
        row.pack(fill="x", pady=(0, 6))
        ttk.Button(row, text="< Up", width=6, command=self._go_up).pack(side="left")
        ttk.Label(row, textvariable=self.path_var,
                  font=("Segoe UI", 9, "bold")).pack(side="left", padx=8)
        ttk.Label(row, text="Filter:").pack(side="left", padx=(14, 2))
        ent = ttk.Entry(row, textvariable=self.filter_var, width=40)
        ent.pack(side="left")
        ent.bind("<KeyRelease>", lambda _e: self._apply_filter())
        ttk.Checkbutton(row, text="regex", variable=self.regex_var,
                        command=self._apply_filter).pack(side="left", padx=6)
        ttk.Label(row, text='tip: "852_" or "depot:852"', foreground="#777").pack(side="left")

        body = ttk.Frame(f)
        body.pack(fill="both", expand=True)

        cols = ("name", "size", "date")
        self.tv = ttk.Treeview(body, columns=cols, show="headings", selectmode="extended")
        for c, w, a in (("name", 700, "w"), ("size", 110, "e"), ("date", 150, "w")):
            self.tv.heading(c, text=c.capitalize())
            self.tv.column(c, width=w, anchor=a, stretch=(c == "name"))
        sb = ttk.Scrollbar(body, orient="vertical", command=self.tv.yview)
        self.tv.configure(yscrollcommand=sb.set)
        self.tv.pack(side="left", fill="both", expand=True)
        sb.pack(side="left", fill="y")
        self.tv.bind("<Double-1>", self._on_double)
        self.tv.bind("<<TreeviewSelect>>", lambda _e: self._update_sel_label())

        btns = ttk.Frame(body)
        btns.pack(side="left", fill="y", padx=(8, 0))
        ttk.Button(btns, text="Add selected", width=20,
                   command=self._add_selected).pack(pady=2)
        ttk.Button(btns, text="Add ALL filtered", width=20,
                   command=self._add_filtered).pack(pady=2)
        ttk.Button(btns, text="Select all shown", width=20,
                   command=lambda: self.tv.selection_set(self.tv.get_children())).pack(pady=2)
        ttk.Separator(btns).pack(fill="x", pady=8)
        ttk.Button(btns, text="Get extractor", width=20,
                   command=self._add_extractor).pack(pady=2)
        ttk.Button(btns, text="Get readme.txt", width=20,
                   command=lambda: self._quick(["readme.txt"])).pack(pady=2)
        ttk.Button(btns, text="Get checksum lists", width=20,
                   command=lambda: self._quick(["blobs.sha256", "dats.sha256",
                                                "blobs_dates.txt", "dats_dates.txt"])).pack(pady=2)

    def _build_depot(self, nb):
        f = ttk.Frame(nb, padding=6)
        nb.add(f, text="Depot picker")
        self.depot_tab = f

        row = ttk.Frame(f)
        row.pack(fill="x", pady=(0, 6))
        ttk.Label(row, text="Depot id:").pack(side="left")
        e = ttk.Entry(row, textvariable=self.depot_var, width=10)
        e.pack(side="left", padx=4)
        e.bind("<Return>", lambda _e: self._scan_depot())
        ttk.Button(row, text="Scan", command=self._scan_depot).pack(side="left")
        ttk.Button(row, text="Rescan from server",
                   command=lambda: self._scan_depot(True)).pack(side="left", padx=4)
        ttk.Label(row, text="   version:").pack(side="left")
        ttk.Entry(row, textvariable=self.maxver_var, width=8).pack(side="left", padx=4)
        ttk.Button(row, text="Download + extract",
                   command=self._extract_from_picker).pack(side="left", padx=(12, 4))
        ttk.Button(row, text="Queue only (no extract)",
                   command=self._add_depot).pack(side="left")
        self.depot_note = ttk.Label(f, text="", foreground="#b35c00",
                                    wraplength=1000, justify="left")
        self.depot_note.pack(fill="x", pady=(0, 4))

        cmd = ttk.Frame(f)
        cmd.pack(fill="x", pady=(0, 6))
        ttk.Label(cmd, text="extract:").pack(side="left")
        ttk.Button(cmd, text="Copy", width=6,
                   command=self._copy_cmd).pack(side="right", padx=(6, 0))
        ttk.Entry(cmd, textvariable=self.cmd_var, state="readonly").pack(
            side="left", fill="x", expand=True, padx=4)
        self.maxver_var.trace_add("write", lambda *_: self._update_cmd())

        body = ttk.Frame(f)
        body.pack(fill="both", expand=True)

        cols = ("version", "blobcrc", "blob", "dat", "have")
        heads = {"version": "Version", "blobcrc": "Blob CRC (--blobcrc)",
                 "blob": "Blob size", "dat": "Dat size", "have": "On disk"}
        self.dtv = ttk.Treeview(body, columns=cols, show="headings", selectmode="extended")
        for c, w, a in (("version", 80, "e"), ("blobcrc", 240, "w"),
                        ("blob", 130, "e"), ("dat", 130, "e"), ("have", 110, "w")):
            self.dtv.heading(c, text=heads[c])
            self.dtv.column(c, width=w, anchor=a)
        self.dtv.bind("<<TreeviewSelect>>", self._on_pick_version)
        sb = ttk.Scrollbar(body, orient="vertical", command=self.dtv.yview)
        self.dtv.configure(yscrollcommand=sb.set)
        self.dtv.pack(side="left", fill="both", expand=True)
        sb.pack(side="left", fill="y")

        side = ttk.Frame(body)
        side.pack(side="left", fill="y", padx=(8, 0))
        ttk.Button(side, text="Queue selected rows", width=22,
                   command=lambda: self._add_depot(only_selected=True)).pack(pady=2)
        ttk.Button(side, text="Preview files (no extract)", width=22,
                   command=self._preview_picker).pack(pady=2)
        ttk.Label(side, wraplength=180, justify="left", foreground="#555",
                  text=("Depots are stored as deltas: to extract version N you need "
                        "every version 0..N of both the blob and the dat.\n\n"
                        "If a version appears twice, Valve did a full reset - pass the "
                        "CRC of the blob you want to extract.exe with --blobcrc.")).pack(pady=8)

    def _build_extract(self, nb):
        f = ttk.Frame(nb, padding=6)
        nb.add(f, text="Extract")
        self.extract_tab = f

        g = ttk.Frame(f)
        g.pack(fill="x")
        ttk.Label(g, text="Depot:").grid(row=0, column=0, sticky="w")
        ttk.Entry(g, textvariable=self.edepot_var, width=10).grid(row=0, column=1, padx=4)
        ttk.Label(g, text="Version:").grid(row=0, column=2, sticky="w", padx=(10, 0))
        ttk.Entry(g, textvariable=self.ever_var, width=8).grid(row=0, column=3, padx=4)
        ttk.Label(g, text="Blob CRC:").grid(row=0, column=4, sticky="w", padx=(10, 0))
        ttk.Entry(g, textvariable=self.ecrc_var, width=12).grid(row=0, column=5, padx=4)
        ttk.Label(g, text="(only for reset depots)", foreground="#777").grid(
            row=0, column=6, sticky="w")

        ttk.Label(g, text="Only files matching:").grid(row=1, column=0, columnspan=2,
                                                       sticky="w", pady=(6, 0))
        ttk.Entry(g, textvariable=self.efilter_var, width=44).grid(
            row=1, column=2, columnspan=4, sticky="we", padx=4, pady=(6, 0))
        ttk.Label(g, text="regex, blank = everything", foreground="#777").grid(
            row=1, column=6, sticky="w", pady=(6, 0))

        ttk.Label(g, text="Extract to:").grid(row=2, column=0, sticky="w", pady=(6, 0))
        ttk.Entry(g, textvariable=self.out_var, width=44).grid(
            row=2, column=2, columnspan=4, sticky="we", padx=4, pady=(6, 0))
        ttk.Button(g, text="Browse...", command=self._pick_out).grid(
            row=2, column=6, sticky="w", pady=(6, 0))

        btns = ttk.Frame(f)
        btns.pack(fill="x", pady=8)
        self.btn_extract = ttk.Button(btns, text="Queue: download what's missing, "
                                                  "then extract",
                                      command=self._go_extract)
        self.btn_extract.pack(side="left")
        ttk.Button(btns, text="Queue: extract only (skip download)",
                   command=lambda: self._go_extract(download=False)).pack(side="left", padx=6)
        ttk.Button(btns, text="Stop", command=self._stop_extract).pack(side="left")
        ttk.Button(btns, text="Open output folder",
                   command=self._open_out).pack(side="left", padx=(12, 0))
        ttk.Button(btns, text="Clear log",
                   command=lambda: self.log_txt.delete("1.0", "end")).pack(side="right")

        q = ttk.LabelFrame(f, text="Task queue", padding=6)
        q.pack(fill="x", pady=(0, 6))
        qrow = ttk.Frame(q)
        qrow.pack(fill="x")
        self.task_note_var = tk.StringVar(value="nothing queued")
        ttk.Label(qrow, textvariable=self.task_note_var, foreground="#555").pack(side="left")
        ttk.Label(qrow, foreground="#777",
                  text=("   extractions and processing runs, one after another - "
                        "queue more from the Depot picker and the Process tab")
                  ).pack(side="left")
        ttk.Button(qrow, text="Remove", command=self._remove_tasks).pack(side="right")
        qbody = ttk.Frame(q)
        qbody.pack(fill="x", pady=(4, 0))
        self.ttv = ttk.Treeview(qbody, columns=("kind", "what", "status"),
                                show="headings", height=4)
        for c, w, a in (("kind", 80, "w"), ("what", 620, "w"), ("status", 90, "w")):
            self.ttv.heading(c, text=c.capitalize())
            self.ttv.column(c, width=w, anchor=a, stretch=(c == "what"))
        tsb = ttk.Scrollbar(qbody, orient="vertical", command=self.ttv.yview)
        self.ttv.configure(yscrollcommand=tsb.set)
        self.ttv.pack(side="left", fill="x", expand=True)
        tsb.pack(side="left", fill="y")
        self.ttv.tag_configure("run", foreground="#0b57d0")

        wrap = ttk.Frame(f)
        wrap.pack(fill="both", expand=True)
        self.log_txt = tk.Text(wrap, height=12, wrap="none", font=("Consolas", 9))
        lsb = ttk.Scrollbar(wrap, orient="vertical", command=self.log_txt.yview)
        self.log_txt.configure(yscrollcommand=lsb.set)
        self.log_txt.pack(side="left", fill="both", expand=True)
        lsb.pack(side="left", fill="y")
        self._log("Pick a depot on the Depot picker tab and press "
                  "\"Download + extract\" - everything else is automatic.")

    def _build_qbit(self, nb):
        f = ttk.Frame(nb, padding=6)
        nb.add(f, text="qBittorrent")
        self.qb_tab = f

        g = ttk.LabelFrame(f, text="Connection", padding=8)
        g.pack(fill="x")
        ttk.Label(g, text="Web UI:").grid(row=0, column=0, sticky="w")
        ttk.Entry(g, textvariable=self.qb_url_var, width=30).grid(row=0, column=1, padx=4)
        ttk.Label(g, text="User:").grid(row=0, column=2, sticky="w", padx=(10, 0))
        ttk.Entry(g, textvariable=self.qb_user_var, width=14).grid(row=0, column=3, padx=4)
        ttk.Label(g, text="Password:").grid(row=0, column=4, sticky="w", padx=(10, 0))
        ttk.Entry(g, textvariable=self.qb_pass_var, width=14, show="*").grid(
            row=0, column=5, padx=4)
        ttk.Button(g, text="Connect", command=self._qb_connect).grid(row=0, column=6, padx=6)
        ttk.Checkbutton(g, text="remember password (stored as plain text)",
                        variable=self.qb_savepw_var).grid(row=1, column=1, columnspan=2,
                                                          sticky="w", pady=(6, 0))
        ttk.Checkbutton(g, text="connect automatically when the app starts",
                        variable=self.qb_auto_var).grid(row=1, column=3, columnspan=4,
                                                        sticky="w", pady=(6, 0))
        ttk.Label(g, textvariable=self.qb_status_var, foreground="#0b57d0").grid(
            row=2, column=0, columnspan=7, sticky="w", pady=(6, 0))

        g2 = ttk.LabelFrame(f, text="Torrent", padding=8)
        g2.pack(fill="x", pady=8)
        self.qb_combo = ttk.Combobox(g2, textvariable=self.qb_tor_var, width=70,
                                     state="readonly")
        self.qb_combo.pack(side="left")
        self.qb_combo.bind("<<ComboboxSelected>>", self._qb_pick)
        ttk.Button(g2, text="Reload", command=self._qb_load_torrents).pack(side="left", padx=6)

        g3 = ttk.LabelFrame(f, text="Web seed", padding=8)
        g3.pack(fill="x", pady=(0, 8))
        ttk.Label(g3, text="URL:").pack(side="left")
        ttk.Entry(g3, textvariable=self.qb_webseed_var, width=44).pack(side="left",
                                                                      padx=4)
        ttk.Button(g3, text="Add to torrent",
                   command=self._qb_add_webseed).pack(side="left", padx=4)
        ttk.Label(g3, foreground="#555", wraplength=420, justify="left",
                  text=("Lets the torrent pull pieces from the mirror over HTTP as "
                        "well as from peers. Helps when peers are scarce, and the "
                        "URL is remembered.")).pack(side="left", padx=8)
        ttk.Label(f, textvariable=self.torrent_dir_var, foreground="#555").pack(anchor="w")
        ttk.Label(f, text="^ the torrent's folder: read for extraction, never written to",
                  foreground="#777").pack(anchor="w", pady=(0, 6))

        ttk.Checkbutton(f, text="Use qBittorrent for depot downloads when it's connected "
                               "(falls back to HTTP if a file isn't in the torrent)",
                        variable=self.qb_use_var).pack(anchor="w")
        ttk.Label(f, justify="left", foreground="#555", wraplength=980,
                  text=("How it works: pick the release torrent above, then use "
                        "\"Download + extract\" on the Depot picker as usual. Instead of "
                        "pulling files over HTTP, the app raises the priority of just that "
                        "depot's blobs and dats inside the torrent, waits for qBittorrent to "
                        "finish them, and extracts straight out of the torrent folder - "
                        "nothing is copied or downloaded twice. You can also right-click "
                        "any depot (or several) in the Depots tab to just queue its files "
                        "here without extracting.\n\n"
                        "It never lowers the priority of files you already selected, so it "
                        "won't disturb anything else you're seeding or downloading. The "
                        "torrent folder is only ever read - \"Save to\" must point somewhere "
                        "else, and is used only for files the torrent can't give you.")
                  ).pack(anchor="w", pady=8)

        wrap = ttk.Frame(f)
        wrap.pack(fill="both", expand=True)
        self.qb_txt = tk.Text(wrap, height=10, wrap="none", font=("Consolas", 9))
        qsb = ttk.Scrollbar(wrap, orient="vertical", command=self.qb_txt.yview)
        self.qb_txt.configure(yscrollcommand=qsb.set)
        self.qb_txt.pack(side="left", fill="both", expand=True)
        qsb.pack(side="left", fill="y")

    def _build_mirror(self, nb):
        """Files the torrent is still missing, fetchable straight from the server."""
        f = ttk.Frame(nb, padding=6)
        nb.add(f, text="Mirror")
        self.mirror_tab = f

        row = ttk.Frame(f)
        row.pack(fill="x", pady=(0, 6))
        ttk.Button(row, text="Refresh", command=self._mirror_refresh).pack(side="left")
        self.btn_mirror = ttk.Button(row, text="Download selected from server",
                                     command=self._mirror_download)
        self.btn_mirror.pack(side="left", padx=6)
        ttk.Button(row, text="Select all",
                   command=lambda: self.mtv.selection_set(
                       *self.mtv.get_children())).pack(side="left")
        ttk.Button(row, text="Select untouched (0%)",
                   command=self._mirror_select_zero).pack(side="left", padx=4)
        self.mirror_pbar = ttk.Progressbar(row, length=180, mode="determinate")
        self.mirror_pbar.pack(side="right")
        ttk.Label(row, textvariable=self.mirror_status_var,
                  foreground="#0b57d0").pack(side="left", padx=12)

        opts = ttk.Frame(f)
        opts.pack(fill="x", pady=(0, 6))
        ttk.Label(opts, foreground="#555",
                  text=("The torrent is paused for the download and resumed "
                        "afterwards - these are its own files, so it must not be "
                        "writing to them at the same time.")).pack(anchor="w")
        ttk.Checkbutton(
            opts, variable=self.mirror_recheck_var,
            text=("recheck the torrent afterwards, so qBittorrent counts the "
                  "mirrored files and can seed them (a recheck of a large "
                  "torrent takes a while)")).pack(anchor="w")

        body = ttk.Frame(f)
        body.pack(fill="both", expand=True)
        cols = ("name", "depot", "size", "got", "left", "prio")
        heads = {"name": "File", "depot": "Depot", "size": "Size",
                 "got": "Downloaded", "left": "Remaining", "prio": "Priority"}
        self.mtv = ttk.Treeview(body, columns=cols, show="headings",
                                selectmode="extended")
        for c, w, a in (("name", 460, "w"), ("depot", 80, "e"), ("size", 100, "e"),
                        ("got", 200, "w"), ("left", 100, "e"), ("prio", 90, "w")):
            self.mtv.heading(c, text=heads[c],
                             command=lambda x=c: self._sort_mirror(x))
            self.mtv.column(c, width=w, anchor=a, stretch=(c == "name"))
        sb = ttk.Scrollbar(body, orient="vertical", command=self.mtv.yview)
        self.mtv.configure(yscrollcommand=sb.set)
        self.mtv.pack(side="left", fill="both", expand=True)
        sb.pack(side="left", fill="y")
        self.mtv.bind("<<TreeviewSelect>>", self._mirror_selection_note)

        ttk.Label(f, foreground="#555", wraplength=980, justify="left",
                  text=("Everything qBittorrent has queued but not finished. Pick "
                        "the ones you don't want to wait for and pull them from the "
                        "server instead. They are written into the torrent's own "
                        "files, so the extractor finds them where it always looks "
                        "and qBittorrent can seed them once it has rechecked. Each "
                        "file is verified against the sha256 in its name and only "
                        "then put in place, so a failed download can't damage what "
                        "the torrent already had.")).pack(anchor="w", pady=(6, 0))

    def _build_queue(self, parent):
        f = ttk.Frame(parent, padding=(6, 4))
        parent.add(f, weight=2)

        head = ttk.Frame(f)
        head.pack(fill="x")
        ttk.Label(head, text="Download queue",
                  font=("Segoe UI", 9, "bold")).pack(side="left")
        ttk.Label(head, foreground="#555",
                  text=("  - every file this app is fetching over HTTP, from any "
                        "tab. Rows stay after they finish or fail so you can see "
                        "what happened; they are restored when you reopen the app."
                        )).pack(side="left")

        ctl = ttk.Frame(f)
        ctl.pack(fill="x", pady=(0, 4))
        self.btn_start = ttk.Button(ctl, text="Start", command=self._start)
        self.btn_start.pack(side="left")
        self.btn_pause = ttk.Button(ctl, text="Pause", command=self._pause, state="disabled")
        self.btn_pause.pack(side="left", padx=4)
        ttk.Button(ctl, text="Stop", command=self._stop).pack(side="left")
        ttk.Button(ctl, text="Verify on disk", command=self._verify_disk).pack(side="left", padx=(12, 4))
        ttk.Button(ctl, text="Retry failed", command=self._retry).pack(side="left", padx=(0, 4))
        ttk.Button(ctl, text="Clear finished", command=self._clear_done).pack(side="left")
        ttk.Button(ctl, text="Remove all", command=self._clear_all).pack(side="left", padx=4)
        ttk.Button(ctl, text="Restore dates",
                   command=self._restore_dates).pack(side="left", padx=(12, 4))
        ttk.Checkbutton(ctl, text="unattended (auto-retry, no prompts)",
                        variable=self.unatt_var).pack(side="left")
        self.pbar = ttk.Progressbar(ctl, length=280, mode="determinate")
        self.pbar.pack(side="right")

        body = ttk.Frame(f)
        body.pack(fill="both", expand=True)
        cols = ("name", "size", "progress", "speed", "status")
        self.qtv = ttk.Treeview(body, columns=cols, show="headings", height=8)
        for c, w, a in (("name", 620, "w"), ("size", 100, "e"), ("progress", 90, "e"),
                        ("speed", 100, "e"), ("status", 220, "w")):
            self.qtv.heading(c, text=c.capitalize(),
                             command=lambda x=c: self._sort_queue(x))
            self.qtv.column(c, width=w, anchor=a, stretch=(c == "name"))
        sb = ttk.Scrollbar(body, orient="vertical", command=self.qtv.yview)
        self.qtv.configure(yscrollcommand=sb.set)
        self.qtv.pack(side="left", fill="both", expand=True)
        sb.pack(side="left", fill="y")
        self.qtv.bind("<Delete>", lambda _e: self._remove_queued())
        self.qmenu = tk.Menu(self, tearoff=0)
        self.qmenu.add_command(label="Remove from queue", command=self._remove_queued)
        self.qmenu.add_command(label="Copy URL", command=self._copy_url)
        self.qmenu.add_command(label="Open containing folder", command=self._open_job_dir)
        self.qtv.bind("<Button-3>", self._queue_menu)
        self.qtv.tag_configure("done", foreground="#1a7f37")
        self.qtv.tag_configure("err", foreground="#c00000")
        self.qtv.tag_configure("act", foreground="#0b57d0")

    def _build_settings(self, nb):
        """Everything you have to set once, in one place.

        The same three folders are reachable from the top bar and the Extract
        tab, but only if you already know which is which - so a fresh install
        opens here instead of on an empty depot list."""
        outer = ttk.Frame(nb)
        nb.add(outer, text="Settings")
        self.settings_tab = outer
        # the queue pane takes the bottom of the window, so this does not fit in
        # what is left of a default-sized one - give it a scrollbar rather than
        # hiding the Save button below the fold
        canvas = tk.Canvas(outer, highlightthickness=0, borderwidth=0)
        vsb = ttk.Scrollbar(outer, orient="vertical", command=canvas.yview)
        canvas.configure(yscrollcommand=vsb.set)
        canvas.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        f = ttk.Frame(canvas, padding=6)
        self.settings_inner = f
        win = canvas.create_window((0, 0), window=f, anchor="nw")
        f.bind("<Configure>",
               lambda _e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.bind("<Configure>", lambda e: canvas.itemconfigure(win, width=e.width))

        def wheel(e):
            canvas.yview_scroll(-1 if e.delta > 0 else 1, "units")
        # only while the pointer is over it, so the depot list keeps its own wheel
        canvas.bind("<Enter>", lambda _e: canvas.bind_all("<MouseWheel>", wheel))
        canvas.bind("<Leave>", lambda _e: canvas.unbind_all("<MouseWheel>"))

        ttk.Label(f, justify="left", foreground="#555", wraplength=980,
                  text=("Set these once and they are remembered. Nothing here is "
                        "written until you press Save.")).pack(anchor="w", pady=(0, 8))

        g = ttk.LabelFrame(f, text="Where things live", padding=8)
        g.pack(fill="x")
        g.columnconfigure(1, weight=1)

        def row(n, label, var, browse, hint, open_cmd=None):
            ttk.Label(g, text=label).grid(row=n * 2, column=0, sticky="w", pady=(0, 2))
            ttk.Entry(g, textvariable=var).grid(row=n * 2, column=1, sticky="ew", padx=6)
            ttk.Button(g, text="Browse...", command=browse).grid(row=n * 2, column=2)
            if open_cmd:
                ttk.Button(g, text="Open", command=open_cmd).grid(
                    row=n * 2, column=3, padx=(4, 0))
            ttk.Label(g, text=hint, foreground="#777").grid(
                row=n * 2 + 1, column=1, sticky="w", padx=6, pady=(0, 8))

        ttk.Label(g, text="Server:").grid(row=0, column=0, sticky="w", pady=(0, 2))
        self.set_combo = ttk.Combobox(g, textvariable=self.base_var)
        self.set_combo.grid(row=0, column=1, sticky="ew", padx=6)
        ttk.Label(g, text="the mirror the archive is downloaded from - the same box "
                          "as in the top bar", foreground="#777").grid(
            row=1, column=1, sticky="w", padx=6, pady=(0, 8))
        row(1, "Save to:", self.dir_var, self._pick_dir,
            "files fetched over HTTP land here. It must not be inside the torrent "
            "folder", self._open_dir)
        row(2, "Extract to:", self.out_var, self._pick_out,
            "one folder per depot and version is created here", self._open_out)
        row(3, "Torrent folder:", self.torrent_dir_var, self._pick_torrent,
            "read for extraction, never written to. Filled in for you when "
            "qBittorrent connects")
        row(4, "Media out:", self.media_var, self._pick_media,
            "where the Process tab puts images, audio and video. Defaults to "
            '"_media" beside the extracted build', self._open_media)
        row(5, "Source2Viewer:", self.s2v_var, self._pick_s2v,
            "optional: Source2Viewer-CLI.exe, only needed to open .vpk archives "
            "on the Process tab. Not the GUI - it cannot be driven from here")
        self._refresh_servers()

        self.set_note_var = tk.StringVar(value="")
        self.set_note = ttk.Label(f, textvariable=self.set_note_var, wraplength=980,
                                  justify="left")
        self.set_note.pack(anchor="w", pady=(6, 0))

        g2 = ttk.LabelFrame(f, text="Downloading", padding=8)
        g2.pack(fill="x", pady=8)
        ttk.Label(g2, text="threads:").grid(row=0, column=0, sticky="w")
        ttk.Spinbox(g2, from_=1, to=16, width=4, textvariable=self.workers_var).grid(
            row=0, column=1, padx=(4, 12))
        ttk.Label(g2, text="one file only ever gets one connection, so this is how "
                           "many files run at once", foreground="#777").grid(
            row=0, column=2, sticky="w")
        ttk.Checkbutton(g2, text="verify sha256 after every download",
                        variable=self.verify_var).grid(
            row=1, column=0, columnspan=3, sticky="w", pady=(6, 0))
        ttk.Checkbutton(g2, text="group downloads into blobs/<depot>/ and dats/<depot>/",
                        variable=self.group_var, command=self._update_cmd).grid(
            row=2, column=0, columnspan=3, sticky="w")
        ttk.Checkbutton(g2, text="unattended: no prompts, and failed downloads are "
                                 "retried every minute", variable=self.unatt_var).grid(
            row=3, column=0, columnspan=3, sticky="w")

        btns = ttk.Frame(f)
        btns.pack(fill="x", pady=(4, 0))
        ttk.Button(btns, text="Save", command=self._settings_save).pack(side="left")
        ttk.Label(btns, text=f"stored in {SETTINGS_PATH}",
                  foreground="#777").pack(side="left", padx=10)

        for v in (self.dir_var, self.out_var, self.torrent_dir_var, self.base_var):
            v.trace_add("write", lambda *_a: self._settings_check())
        self._settings_check()

    def _pick_torrent(self):
        d = filedialog.askdirectory(initialdir=self.torrent_dir_var.get() or ".")
        if d:
            self.torrent_dir_var.set(d)

    def _pick_media(self):
        d = filedialog.askdirectory(initialdir=self.media_var.get()
                                    or self.out_var.get() or ".")
        if d:
            self.media_var.set(d)

    def _open_media(self):
        d = Path(self.media_var.get().strip() or "")
        if not d or not d.exists():
            self.status_var.set("nothing has been put there yet")
            return
        try:
            os.startfile(str(d))                                    # noqa: B950
        except AttributeError:
            os.system(f'xdg-open "{d}"')

    def _pick_s2v(self):
        f = filedialog.askopenfilename(
            title="Source2Viewer CLI",
            initialdir=str(Path(self.s2v_var.get()).parent) if self.s2v_var.get() else ".",
            filetypes=[("Programs", "*.exe"), ("All files", "*.*")])
        if not f:
            return
        self.s2v_var.set(f)
        self._proc_tool_note()
        if "cli" not in Path(f).stem.lower():
            messagebox.showinfo(
                APP_NAME,
                f"{Path(f).name} looks like the Source2Viewer GUI rather than its "
                f"command line tool.\n\nThe GUI opens whatever it is handed as a "
                f"file, so it cannot unpack archives from here. The same release "
                f"ships Source2Viewer-CLI.exe - point this at that instead.")

    def _settings_check(self):
        """Say what is still missing, while it is still cheap to fix."""
        if not hasattr(self, "set_note_var"):
            return
        save = self.dir_var.get().strip()
        tor = self.torrent_dir_var.get().strip()
        bad = []
        if not self.base():
            bad.append("no server: the depot list cannot be built without one")
        if not save:
            bad.append('"Save to" is empty')
        elif tor:
            try:
                sp, tp = Path(save), Path(tor)
                if sp == tp or tp in sp.parents:
                    bad.append('"Save to" is inside the torrent folder - downloading '
                               "there would collide with qBittorrent, so it is "
                               "refused. Put it alongside, not inside")
            except Exception:                                       # noqa: BLE001
                pass
        if not self.out_var.get().strip():
            bad.append('no "Extract to" folder yet - extraction will ask for one')
        self.set_note_var.set("  -  ".join(bad) if bad else
                              "all set - the depot list builds itself from here")
        self.set_note.configure(foreground="#c00000" if bad else "#1a7f37")

    def _settings_save(self):
        self._save_settings()
        self._settings_check()
        self.status_var.set(f"settings saved to {SETTINGS_PATH.name}")
        # a first run ends here: until now there was nothing to build a list from
        if self.base() and not self.depot_stats:
            self._load_depots()
            self.nb.select(self.depots_tab)

    def _build_process(self, nb):
        """Turn a finished extraction into plain media files.

        Extraction gives you the game as it shipped: loose files plus .vpk
        archives. This pulls the parts you can actually open - images, audio,
        video - into a folder of their own, leaving the build untouched."""
        f = ttk.Frame(nb, padding=6)
        nb.add(f, text="Process")
        self.process_tab = f

        top = ttk.Frame(f)
        top.pack(fill="x")
        ttk.Label(top, text="Extracted builds:").pack(side="left")
        ttk.Button(top, text="Rescan", command=self._proc_refresh).pack(side="left", padx=6)
        ttk.Button(top, text="Open build folder",
                   command=self._proc_open_build).pack(side="left")
        ttk.Button(top, text="Open media folder",
                   command=self._open_media).pack(side="left", padx=6)

        body = ttk.Frame(f)
        body.pack(fill="both", expand=True, pady=(4, 6))
        cols = ("depot", "name", "version", "when", "folder")
        self.ptv = ttk.Treeview(body, columns=cols, show="headings", height=7)
        for c, w, a in (("depot", 80, "e"), ("name", 220, "w"), ("version", 70, "e"),
                        ("when", 130, "w"), ("folder", 460, "w")):
            self.ptv.heading(c, text=c.capitalize())
            self.ptv.column(c, width=w, anchor=a, stretch=(c == "folder"))
        psb = ttk.Scrollbar(body, orient="vertical", command=self.ptv.yview)
        self.ptv.configure(yscrollcommand=psb.set)
        self.ptv.pack(side="left", fill="both", expand=True)
        psb.pack(side="left", fill="y")

        opts = ttk.LabelFrame(f, text="What to pull out (one flat folder each)",
                              padding=8)
        opts.pack(fill="x")
        for i, (kind, exts) in enumerate(MEDIA_KINDS.items()):
            ttk.Checkbutton(opts, text=kind, variable=self.kind_vars[kind]).grid(
                row=i, column=0, sticky="w")
            ttk.Label(opts, text=" ".join(exts), foreground="#777").grid(
                row=i, column=1, sticky="w", padx=8)
        ttk.Checkbutton(opts, text="also unpack .vpk archives (needs Source2Viewer)",
                        variable=self.vpk_var).grid(row=3, column=0, columnspan=2,
                                                    sticky="w", pady=(6, 0))
        ttk.Label(opts, text="arguments:").grid(row=4, column=0, sticky="w")
        ttk.Entry(opts, textvariable=self.s2v_args_var).grid(row=4, column=1,
                                                             sticky="ew", padx=8)
        opts.columnconfigure(1, weight=1)
        ttk.Label(opts, foreground="#777", wraplength=900, justify="left",
                  text=("{input} is each archive, {output} the media folder, {ext} the "
                        "extensions ticked above. Flags vary between Source2Viewer "
                        'releases - press "Tool help" to see what yours takes. It is '
                        "built for Source 2, so on these Source 1 depots it is useful "
                        "for opening .vpk archives rather than converting what is in "
                        "them.")).grid(row=5, column=0, columnspan=2, sticky="w",
                                       pady=(4, 0))

        run = ttk.Frame(f)
        run.pack(fill="x", pady=6)
        self.btn_proc = ttk.Button(run, text="Process selected build(s)",
                                   command=self._proc_run)
        self.btn_proc.pack(side="left")
        ttk.Button(run, text="Stop", command=self._proc_stop_now).pack(side="left", padx=6)
        ttk.Button(run, text="Tool help", command=self._s2v_help).pack(side="left")
        self.proc_note_var = tk.StringVar()
        ttk.Label(run, textvariable=self.proc_note_var,
                  foreground="#555").pack(side="left", padx=10)

        wrap = ttk.Frame(f)
        wrap.pack(fill="both", expand=True)
        self.proc_txt = tk.Text(wrap, height=10, wrap="none", font=("Consolas", 9))
        wsb = ttk.Scrollbar(wrap, orient="vertical", command=self.proc_txt.yview)
        self.proc_txt.configure(yscrollcommand=wsb.set)
        self.proc_txt.pack(side="left", fill="both", expand=True)
        wsb.pack(side="left", fill="y")
        self._proc_tool_note()

    def _proc_tool_note(self):
        exe = self.s2v_var.get().strip()
        if not exe:
            self.proc_note_var.set("Source2Viewer not set - loose media still works")
        elif not Path(exe).exists():
            self.proc_note_var.set(f"Source2Viewer not found at {exe}")
        elif "cli" not in Path(exe).stem.lower():
            self.proc_note_var.set(f"{Path(exe).name} - this looks like the GUI, "
                                   f"not Source2Viewer-CLI.exe")
        else:
            self.proc_note_var.set(f"Source2Viewer: {Path(exe).name}")

    def _proc_log(self, msg: str):
        self.proc_txt.insert("end", msg + "\n")
        self.proc_txt.see("end")
        log_to_disk(msg)

    def _proc_refresh(self):
        """Every extracted build we know of: what was extracted here, plus
        anything already sitting in the output folder."""
        rows, seen = [], set()
        for dep, rec in sorted(self.history.items(), key=lambda kv: int(kv[0])
                               if kv[0].isdigit() else 0):
            out = (rec or {}).get("out", "")
            if out and Path(out).exists():
                rows.append({"depot": dep, "version": rec.get("version", ""),
                             "when": rec.get("when", ""), "path": Path(out)})
                seen.add(str(Path(out)).lower())
        root = Path(self.out_var.get().strip() or "")
        try:
            dirs = sorted(d for d in root.iterdir() if d.is_dir()) if root.exists() else []
        except OSError:
            dirs = []
        for d in dirs:
            if str(d).lower() in seen or d.name.startswith("_"):
                continue
            m = BUILD_RE.match(d.name)
            rows.append({"depot": m.group(1) if m else "", "version": m.group(3) if m else "",
                         "when": "", "path": d})
        self.proc_rows = rows
        self.ptv.delete(*self.ptv.get_children())
        for i, r in enumerate(rows):
            name = self.depot_names.get(r["depot"], "")
            self.ptv.insert("", "end", iid=str(i), values=(
                r["depot"], short_name(name) if name else r["path"].name,
                r["version"], r["when"], str(r["path"])))
        self.status_var.set(f"{len(rows)} extracted build(s) to process"
                            if rows else "nothing extracted yet - use the Extract tab first")

    def _proc_selected(self):
        sel = self.ptv.selection()
        return self.proc_rows[int(sel[0])] if sel else None

    def _proc_selected_rows(self):
        """Every build you have selected, in the order they are listed."""
        return [self.proc_rows[int(i)] for i in sorted(self.ptv.selection(), key=int)
                if int(i) < len(self.proc_rows)]

    def _proc_open_build(self):
        r = self._proc_selected()
        if not r:
            self.status_var.set("pick a build first")
            return
        try:
            os.startfile(str(r["path"]))                            # noqa: B950
        except AttributeError:
            os.system(f'xdg-open "{r["path"]}"')

    def _proc_media_root(self, build: Path) -> Path:
        """Where this build's media goes: your folder if you set one, else
        "_media" beside the build - never inside the build itself."""
        base = self.media_var.get().strip()
        return (Path(base) / build.name) if base else build.parent / "_media" / build.name

    def _proc_stop_now(self):
        if not self.proc_busy:
            return
        self.proc_stop.set()
        if self.proc_proc:
            try:
                self.proc_proc.terminate()
            except Exception:                                       # noqa: BLE001
                pass
        self._proc_log("stopping this run"
                       + (f" - {len(self.tasks)} job(s) still queued, use Stop on "
                          f"the Extract tab to drop those too" if self.tasks else ""))

    def _s2v_help(self):
        """Print what this build of the tool actually accepts."""
        exe = self.s2v_var.get().strip()
        if not exe or not Path(exe).exists():
            self._proc_log('set "Source2Viewer" on the Settings tab first')
            return
        self._proc_log(f"$ {Path(exe).name} --help")

        def work():
            try:
                out = subprocess.run([exe, "--help"], capture_output=True, text=True,
                                     timeout=30, errors="replace",
                                     creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
                text = (out.stdout or "") + (out.stderr or "")
            except Exception as exc:                                # noqa: BLE001
                text = f"could not run it: {exc}"
            self.after(0, lambda: [self._proc_log(l) for l in text.splitlines()[:80]])
        threading.Thread(target=work, daemon=True).start()

    def _proc_run(self):
        """Queue the builds you selected. The options are taken as they are now,
        so you can queue one build, change the ticks, and queue another."""
        rows = self._proc_selected_rows()
        if not rows:
            self.status_var.set("pick an extracted build first")
            return
        kinds = {k for k, v in self.kind_vars.items() if v.get()}
        exe = self.s2v_var.get().strip()
        want_vpk = self.vpk_var.get()
        if want_vpk and (not exe or not Path(exe).exists()):
            if not self._ask("Source2Viewer isn't set, so .vpk archives will be "
                             "skipped and only loose media is pulled out.\n\n"
                             "Carry on?"):
                return
            want_vpk = False
        if not kinds and not want_vpk:
            self.status_var.set("nothing ticked to pull out")
            return
        queued = 0
        for row in rows:
            build = row["path"]
            if not build.exists():
                self._proc_log(f"{build} is gone - press Rescan")
                continue
            self._queue_task({"kind": "process", "path": build,
                              "kinds": set(kinds), "vpk": want_vpk, "exe": exe,
                              "args": self.s2v_args_var.get(),
                              "label": f"process {build.name}"},
                             quiet=len(rows) > 1)
            queued += 1
        if len(rows) > 1:
            self.status_var.set(f"queued {queued} build(s) to process")

    def _proc_start(self, task: dict):
        """Run one queued processing job."""
        build = task["path"]
        kinds = task["kinds"]
        exts = {e for k in kinds for e in MEDIA_KINDS[k]}
        exe, want_vpk, args_tpl = task["exe"], task["vpk"], task["args"]
        out_root = self._proc_media_root(build)
        # what the tool unpacks lands here first; the media is lifted out of it
        stage_root = out_root / "_vpk"

        self.proc_busy = True
        self.proc_stop.clear()
        self.btn_proc.config(state="disabled")
        self._proc_log(f"--- {build.name}: {', '.join(sorted(kinds)) or 'no'} media "
                       f"-> {out_root}")

        def place(src: Path, kind: str, move: bool = False):
            """Put one file in its kind's folder, flat.

            Names collide once the folders are gone, so a clash gets _1, _2 ...
            unless something of that name is already there at the same size -
            that is this file from an earlier run, and it is left alone."""
            folder = out_root / kind
            folder.mkdir(parents=True, exist_ok=True)
            size = src.stat().st_size
            stem, ext, n = src.stem, src.suffix, 0
            while True:
                dest = folder / (f"{stem}{ext}" if not n else f"{stem}_{n}{ext}")
                if not dest.exists():
                    break
                if dest.stat().st_size == size:
                    return None
                n += 1
            if move:
                shutil.move(str(src), str(dest))
            else:
                shutil.copy2(src, dest)        # the build is left as it was
            return dest

        def kind_of(ext: str):
            return next(k for k, v in MEDIA_KINDS.items() if ext in v)

        def work():
            copied = {k: 0 for k in MEDIA_KINDS}
            written = skipped = unpacked = 0
            vpks = []
            try:
                out_root.mkdir(parents=True, exist_ok=True)
                for src in build.rglob("*"):
                    if self.proc_stop.is_set():
                        break
                    if not src.is_file():
                        continue
                    ext = src.suffix.lower()
                    if ext == ".vpk":
                        if not VPK_PART_RE.search(src.name):
                            vpks.append(src)
                        continue
                    if ext not in exts:
                        continue
                    kind = kind_of(ext)
                    if place(src, kind) is None:
                        skipped += 1
                        continue
                    copied[kind] += 1
                    written += 1
                    if written % 200 == 0:
                        self.after(0, lambda n=written: self.status_var.set(
                            f"copied {n:,} files ..."))
            except Exception as exc:                                # noqa: BLE001
                self.after(0, lambda e=exc: self._proc_log(f"copying stopped: {e}"))

            gui = False
            for i, vpk in enumerate(vpks, 1):
                if self.proc_stop.is_set() or not want_vpk:
                    break
                stage = stage_root / vpk.stem
                stage.mkdir(parents=True, exist_ok=True)
                cmd = [exe] + shlex.split(args_tpl.format(
                    input=str(vpk), output=str(stage),
                    ext=",".join(sorted(e.lstrip(".") for e in exts))))
                self.after(0, lambda v=vpk, i=i: self._proc_log(
                    f"[{i}/{len(vpks)}] {v.name}"))
                try:
                    self.proc_proc = subprocess.Popen(
                        cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                        text=True, bufsize=1, errors="replace",
                        creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
                    for line in self.proc_proc.stdout:
                        line = line.rstrip()
                        if not line:
                            continue
                        self.after(0, lambda l=line: self._proc_log("   " + l))
                        if any(sign in line.lower() for sign in S2V_GUI_SIGNS):
                            gui = True
                            break
                    if gui:
                        # it would sit there with a window open, so stop now
                        # rather than doing this eleven more times
                        try:
                            self.proc_proc.terminate()
                        except Exception:                           # noqa: BLE001
                            pass
                        self.after(0, lambda: self._proc_log(
                            "   ^ that is the Source2Viewer GUI, not the CLI: it "
                            "treats every argument as a file to open. Set "
                            "\"Source2Viewer\" on the Settings tab to "
                            "Source2Viewer-CLI.exe from the same release "
                            "(the GUI cannot be driven from here)."))
                        break
                    rc = self.proc_proc.wait()
                    if rc != 0:
                        self.after(0, lambda r=rc: self._proc_log(
                            f"   Source2Viewer exited with code {r}"))
                except FileNotFoundError:
                    self.after(0, lambda: self._proc_log(
                        "   could not start Source2Viewer - check the path in Settings"))
                    break
                except Exception as exc:                            # noqa: BLE001
                    self.after(0, lambda e=exc: self._proc_log(f"   {e}"))
                finally:
                    self.proc_proc = None
                # lift what it unpacked into the same three folders; whatever
                # else it wrote stays in _vpk rather than being thrown away
                for f in sorted(stage.rglob("*")):
                    if self.proc_stop.is_set():
                        break
                    if not f.is_file() or f.suffix.lower() not in exts:
                        continue
                    k = kind_of(f.suffix.lower())
                    if place(f, k, move=True) is None:
                        skipped += 1
                    else:
                        copied[k] += 1
                        unpacked += 1
                try:                        # nothing came out of it: no leftovers
                    stage.rmdir()
                except OSError:
                    pass

            self.after(0, lambda: self._proc_done(copied, skipped, len(vpks),
                                                  want_vpk and not gui, out_root,
                                                  unpacked))
        threading.Thread(target=work, daemon=True).start()

    def _proc_done(self, copied, skipped, nvpk, used_vpk, out_root, unpacked=0):
        self.proc_busy = False
        self.btn_proc.config(state="normal")
        if self.current_task and self.current_task.get("kind") == "process":
            self.after(0, self._task_step)
        total = sum(copied.values())
        parts = [f"{n:,} {k}" for k, n in copied.items() if n]
        msg = (f"{total:,} file(s) pulled out"
               + (f" ({', '.join(parts)})" if parts else "")
               + (f", {skipped:,} already there" if skipped else ""))
        if nvpk and not used_vpk:
            msg += (f" - {nvpk} .vpk archive(s) left alone; set Source2Viewer on the "
                    f"Settings tab to open them")
        elif nvpk:
            msg += (f", {nvpk} .vpk archive(s) opened"
                    + (f" ({unpacked:,} of the files came out of them)"
                       if unpacked else ""))
        if self.proc_stop.is_set():
            msg = "stopped - " + msg
        self._proc_log(msg)
        where = ", ".join(str(out_root / k) for k in MEDIA_KINDS if copied.get(k))
        self._proc_log("they are in " + (where or str(out_root)))
        self.status_var.set(msg)

    # ---- navigation
    def base(self) -> str:
        b = self.base_var.get().strip()
        if not b:
            return ""
        if "://" not in b:
            b = "http://" + b
        return b if b.endswith("/") else b + "/"

    def _refresh_servers(self):
        """Dropdown = the mirrors you listed in mirrors.json, then ones you've used."""
        seen, values = set(), []
        for u in list(self.mirrors) + list(self.servers):
            u = (u or "").strip()
            if u and u not in seen:
                seen.add(u)
                values.append(u)
        for combo in (getattr(self, "base_combo", None),
                      getattr(self, "set_combo", None)):
            try:
                combo["values"] = values
            except Exception:                                       # noqa: BLE001
                pass

    def _remember_server(self):
        """Called once a server has actually answered, so the list stays useful."""
        u = self.base()
        if not u:
            return
        self.servers = [u] + [s for s in self.servers if s != u]
        del self.servers[8:]
        self._refresh_servers()

    def _need_base(self) -> bool:
        """Nothing can be fetched until you say where from."""
        if self.base():
            return True
        self.status_var.set('no server yet - set one on the Settings tab (or in '
                            'the "Server" box at the top), then try again')
        return False

    def url_for(self, path: str) -> str:
        return urljoin(self.base(), quote(path, safe="/"))

    def navigate(self, path: str, refresh: bool = False):
        if self.busy or not self._need_base():
            return
        self.busy = True
        self.status_var.set(f"loading /{path} ...")
        url = self.url_for(path) if path else self.base()
        if not url.endswith("/"):
            url += "/"

        def work():
            try:
                entries = self.listing.get(url, refresh)
                self.after(0, lambda: self._show(path, entries))
            except Exception as exc:                                # noqa: BLE001
                self.after(0, lambda e=exc: self._fail(f"listing failed: {e}"))
        threading.Thread(target=work, daemon=True).start()

    def _fail(self, msg: str):
        self.busy = False
        self.status_var.set(msg)
        messagebox.showerror(APP_NAME, msg)

    def _show(self, path: str, entries):
        self.busy = False
        self.cur_path = path
        self.cur_entries = entries
        self.path_var.set("/" + path)
        self._apply_filter()
        if entries:
            self._remember_server()           # it answered, so keep it on the list

    def _go_up(self):
        p = self.cur_path.rstrip("/")
        if not p:
            return
        self.filter_var.set("")
        self.navigate(p.rsplit("/", 1)[0] if "/" in p else "")

    def _on_double(self, _e):
        sel = self.tv.selection()
        if not sel:
            return
        e = self.filtered[int(sel[0])]
        if e.is_dir:
            self.filter_var.set("")
            self.navigate((self.cur_path + "/" if self.cur_path else "") + e.name)

    # ---- filtering
    def _apply_filter(self):
        q = self.filter_var.get().strip()
        entries = self.cur_entries
        if q:
            if q.lower().startswith("depot:"):
                dep = q.split(":", 1)[1].strip()
                pred = lambda e: e.is_dir or e.name.startswith(dep + "_")   # noqa: E731
            elif self.regex_var.get():
                try:
                    rx = re.compile(q, re.I)
                except re.error as exc:
                    self.status_var.set(f"bad regex: {exc}")
                    return
                pred = lambda e: e.is_dir or bool(rx.search(e.name))        # noqa: E731
            else:
                ql = q.lower()
                pred = lambda e: e.is_dir or ql in e.name.lower()           # noqa: E731
            entries = [e for e in entries if pred(e)]
        self.filtered = entries

        self.tv.delete(*self.tv.get_children())
        for i, e in enumerate(entries[:MAX_ROWS]):
            self.tv.insert("", "end", iid=str(i),
                           values=(("[DIR] " if e.is_dir else "") + e.name,
                                   "-" if e.is_dir else human(e.size), e.date))
        files = [e for e in entries if not e.is_dir]
        total = sum(e.size for e in files)
        more = (f"  (showing first {MAX_ROWS:,} - refine the filter)"
                if len(entries) > MAX_ROWS else "")
        self.status_var.set(
            f"/{self.cur_path} - {len(files):,} files, {human(total)} matched{more}")
        self._update_sel_label()

    def _update_sel_label(self):
        sel = [self.filtered[int(i)] for i in self.tv.selection()]
        files = [e for e in sel if not e.is_dir]
        self.sel_var.set(f"selected: {len(files):,} files, {human(sum(e.size for e in files))}"
                         if files else "")

    # ---- queueing
    def _job_for(self, path: str, name: str, size: int, approx: bool = False) -> Job:
        remote = (path + "/" + name) if path else name      # always flat on the server
        m = NAME_RE.match(name)
        local = remote
        if m and self.group_var.get() and path in ("blobs", "dats"):
            local = f"{path}/{m.group(1)}/{name}"           # blobs/852/852_0_....blob
        return Job(url=self.url_for(remote),
                   rel=os.path.join(*[safe_name(p) for p in local.split("/")]),
                   size=size, sha256=m.group(4).lower() if m else "",
                   approx=approx)

    def _enqueue(self, jobs, urgent: bool = False):
        """Queue these. Returns the job objects now being tracked, which for a
        file already in the queue is the existing one, not the new copy."""
        if not jobs:
            return []
        if not self._writable_save_dir():      # never write into the torrent folder
            return []
        have = {j.url: j for j in self.dl.jobs}
        tracked = [have.get(j.url) or j for j in jobs]
        fresh = [j for j in jobs if j.url not in have]
        if not fresh:
            self.status_var.set("everything selected is already in the queue")
            return tracked
        self.dl.add(fresh, urgent)
        self._sync_queue_rows()
        self.status_var.set(
            f"queued {len(fresh):,} files ({human(sum(j.size for j in fresh))})")
        return tracked

    def _add_selected(self):
        sel = [self.filtered[int(i)] for i in self.tv.selection()]
        self._enqueue([self._job_for(self.cur_path, e.name, e.size, e.approx)
                       for e in sel if not e.is_dir])

    def _add_filtered(self):
        files = [e for e in self.filtered if not e.is_dir]
        if len(files) > 200 and not messagebox.askyesno(
                APP_NAME, f"Queue {len(files):,} files "
                          f"({human(sum(e.size for e in files))})?"):
            return
        self._enqueue([self._job_for(self.cur_path, e.name, e.size, e.approx) for e in files])

    def _quick(self, names):
        try:
            root = self.listing.get(self.base())
        except Exception as exc:                                    # noqa: BLE001
            self._fail(str(exc))
            return
        sizes = {e.name: (e.size, e.approx) for e in root}
        self._enqueue([self._job_for("", n, *sizes[n]) for n in names if n in sizes])

    def _add_extractor(self):
        try:
            entries = self.listing.get(self.base() + "extractor/")
        except Exception as exc:                                    # noqa: BLE001
            self._fail(str(exc))
            return
        self._enqueue([self._job_for("extractor", e.name, e.size, e.approx)
                       for e in entries if not e.is_dir])

    def _on_tab_changed(self, _e=None):
        """Recompute the 'You have' column when you come back to the Depots tab."""
        try:
            cur = self.nb.nametowidget(self.nb.select())
        except Exception:
            return
        if cur is getattr(self, "depots_tab", None) and self.depot_stats:
            self._show_depots()                      # paint now with what we know
            self._refresh_local()                    # recount in the background
        elif cur is getattr(self, "mirror_tab", None) and not self.mirror_job:
            self._mirror_refresh()
        elif cur is getattr(self, "process_tab", None) and not self.proc_busy:
            self._proc_refresh()

    # ---- depot index
    def _autoload_depots(self):
        """Build the depot list on startup, without being asked.

        It is the tab the app opens on, so an empty one is just a button you
        always have to press. Cached listings make this instant; the first run
        on a new server fetches them, in the background, with the status line
        saying so."""
        if self.depot_stats or not self.base():
            return
        self._load_depots()

    def _load_depots(self, refresh: bool = False):
        if not self._need_base():
            return
        self.status_var.set("re-downloading both file listings ..." if refresh else
                            "building the depot list from the file listings ...")
        self.update_idletasks()
        # read on this thread: Tk variables belong to the thread running the UI,
        # and this one now starts by itself before anything is on screen
        base = self.base()

        def work():
            try:
                blobs = self.listing.get(base + "blobs/", refresh)
                dats = self.listing.get(base + "dats/", refresh)
            except Exception as exc:                                # noqa: BLE001
                self.after(0, lambda e=exc: self._fail(str(e)))
                return
            agg = {}
            for kind, entries in (("blobs", blobs), ("dats", dats)):
                for e in entries:
                    m = NAME_RE.match(e.name)
                    if not m:
                        continue
                    d = agg.setdefault(m.group(1), {
                        "depot": m.group(1), "versions": set(),
                        "blobs": 0, "dats": 0, "nblobs": 0, "ndats": 0})
                    d["versions"].add(int(m.group(2)))
                    d[kind] += e.size
                    d["n" + kind] += 1
            rows = []
            for d in agg.values():
                d["nversions"] = len(d["versions"])
                d["maxver"] = max(d["versions"])
                d["total"] = d["blobs"] + d["dats"]
                d.pop("versions")
                rows.append(d)
            # if a refresh silently fell back to cache, the age gives it away
            stale = refresh and (self.listing.age(base + "blobs/") or 0) > 120
            self.after(0, lambda: self._depots_loaded(rows, stale))
        threading.Thread(target=work, daemon=True).start()

    def _reload_names(self):
        """Steam names, with a hand-written depot_names.json taking precedence."""
        names = self.snames.names()
        try:
            names.update({str(k): str(v) for k, v in
                          json.loads(NAMES_PATH.read_text("utf-8")).items()})
        except Exception:
            pass
        self.depot_names = names

    def _fetch_names(self):
        """Name every unnamed depot from Steam (cached, resumable, stoppable)."""
        if self.names_busy:
            self.names_stop.set()
            self.status_var.set("stopping the name fetch ...")
            return
        if not self.depot_stats:
            self.status_var.set('press "Load depot list" first')
            return
        all_ids = [r["depot"] for r in self.depot_stats]
        self.names_busy = True
        self.names_stop.clear()
        self.btn_names.config(text="Stop fetching")
        self.status_var.set("fetching the depot name list ...")

        def prog(done, total, found, errors):
            self.after(0, lambda: self.status_var.set(
                f"asking Steam about the rest: {done:,}/{total:,} lookups, "
                f"{found:,} named{f', {errors} errors' if errors else ''} "
                f"- this is cached, you only pay for it once"))

        def work():
            parts = []
            try:                    # 1. the ready-made list: one request, ~10.9k names
                n = self.snames.fetch_labels()
                parts.append(f"{n:,} names from the depot label list")
                self.after(0, self._names_progress)
            except Exception as exc:                                # noqa: BLE001
                parts.append(f"label list unavailable ({exc})")
            left = [d for d in all_ids if not self.snames.known(d)]
            if left and not self.names_stop.is_set():   # 2. Steam, for the leftovers
                self.after(0, lambda: self.status_var.set(
                    f"asking Steam about {len(left):,} still-unnamed depots ..."))
                try:
                    named, asked, errors = self.snames.resolve(
                        left, prog, self.names_stop.is_set)
                    parts.append(f"{named:,} more of {len(left):,} from Steam "
                                 f"({asked:,} lookups"
                                 f"{f', {errors} errors' if errors else ''})")
                except Exception as exc:                            # noqa: BLE001
                    parts.append(f"Steam lookups failed: {exc}")
            elif not left:
                parts.append("nothing left to look up")
            msg = "; ".join(parts) + (" - stopped" if self.names_stop.is_set() else "")
            self.after(0, lambda: self._names_done(msg))
        threading.Thread(target=work, daemon=True).start()

    def _names_progress(self):
        self._reload_names()
        if self.depot_stats:
            self._show_depots()

    def _names_done(self, msg: str):
        self.names_busy = False
        self.btn_names.config(text="Fetch names from Steam")
        self._reload_names()
        self._show_depots()
        self.status_var.set(msg)

    def _rescan_local(self):
        self._local_cache = None
        self._refresh_local()
        self.status_var.set("re-counting the files in your folders ...")

    def _torrent_root(self):
        """The folder that holds the torrent's blobs/ and dats/, if we know it.

        Not the torrent's save path: a single-folder torrent puts them one level
        below it. It is worked out from the real file names when the torrent is
        picked, and remembered so the depot list still knows about it before
        qBittorrent is connected."""
        d = self.torrent_dir_var.get().strip()
        return Path(d) if d else None

    def _local_files(self) -> set:
        """Every blob/dat basename you actually have, from both folders.

        Scans the download folder and - read only, nothing is ever written
        there - the torrent folder qBittorrent reports. Half-finished files
        don't count: qBittorrent's own ".!qB" parts, our ".part" files, and
        anything the torrent still reports as incomplete."""
        save = Path(self.dir_var.get().strip() or ".")
        tor = self._torrent_root()
        incomplete = {n for n, f in self.qb_index.items()
                      if f.get("progress", 0) < 1}
        return self._collect(save, tor, incomplete)

    @staticmethod
    def _collect(save, tor, incomplete) -> set:
        """The set of finished files in both folders. No Tk, so it is safe in a
        worker thread."""
        names = set(App._scan_files(save))
        if tor and tor != save:
            names |= set(App._scan_files(tor)) - incomplete
        return names

    @staticmethod
    def _scan_files(root) -> dict:
        """basename -> path for every blob/dat under root, flat or grouped."""
        found = {}
        if not root:
            return found
        for sub in ("blobs", "dats"):
            base = Path(root) / sub
            if not base.exists():
                continue
            try:
                stack = [base]
                while stack:
                    for entry in os.scandir(stack.pop()):
                        if entry.is_dir():
                            stack.append(entry.path)
                        elif entry.name.endswith((".blob", ".dat")):
                            found[entry.name] = Path(entry.path)
            except OSError:
                pass
        return found

    def _local_counts(self):
        """How many files of each depot you have. Cached; refilled in the
        background, because counting 60k+ files must not freeze the window."""
        if self._local_cache is None:
            self._refresh_local()
            return {}
        return self._local_cache

    def _refresh_local(self):
        """Recount what's on disk, off the UI thread, then redraw the column."""
        if self._local_busy:
            return
        self._local_busy = True
        save = Path(self.dir_var.get().strip() or ".")     # read Tk vars here,
        tor = self._torrent_root()                         # not in the worker
        incomplete = {n for n, f in self.qb_index.items()
                      if f.get("progress", 0) < 1}

        def work():
            counts = {}
            try:
                for n in self._collect(save, tor, incomplete):
                    dep = n.split("_", 1)[0]
                    counts[dep] = counts.get(dep, 0) + 1
            except Exception:                                       # noqa: BLE001
                pass
            self.after(0, lambda: done(counts))

        def done(counts):
            self._local_busy = False
            self._local_cache = counts
            if self.depot_stats:
                self._show_depots()
        threading.Thread(target=work, daemon=True).start()

    def _depots_loaded(self, rows, stale: bool = False):
        self.depot_stats = rows
        if rows:
            self._remember_server()           # it answered, so keep it on the list
        self._show_depots()
        total = sum(r["total"] for r in rows)
        note = " - refresh failed, showing the cached list" if stale else ""
        self.status_var.set(f"{len(rows):,} depots, {human(total)} in total"
                            f"  |  listings {self._cache_age_text()}{note}")

    def _cache_age_text(self) -> str:
        ages = [a for a in (self.listing.age(self.base() + "blobs/"),
                            self.listing.age(self.base() + "dats/")) if a is not None]
        if not ages:
            return "just fetched"
        s = max(ages)
        if s < 90:
            return "fetched just now"
        if s < 3600:
            return f"cached {int(s // 60)} min ago"
        if s < 86400:
            return f"cached {int(s // 3600)}h ago"
        return f"cached {int(s // 86400)}d ago"

    def _sort_depots(self, col):
        same = self.dsort[0] == col
        self.dsort = (col, not self.dsort[1] if same else False)
        self._show_depots()

    def _show_depots(self):
        q = self.dfilter_var.get().strip().lower()
        rows = self.depot_stats
        local = self._local_counts()

        def ratio(r):
            return local.get(r["depot"], 0) / max(1, r["nblobs"] + r["ndats"])

        if q.startswith("have:"):        # have:complete / partial / none / extracted
            want = q.split(":", 1)[1].strip()
            rows = [r for r in rows if
                    (ratio(r) >= 1 if want.startswith("comp") else
                     0 < ratio(r) < 1 if want.startswith("part") else
                     ratio(r) == 0 if want.startswith("non") else
                     r["depot"] in self.history if want.startswith("extr") else True)]
        elif q:
            rows = [r for r in rows
                    if q in r["depot"] or q in self.depot_names.get(r["depot"], "").lower()]
        key = {"depot": lambda r: int(r["depot"]),
               "name": lambda r: self.depot_names.get(r["depot"], "").lower(),
               "versions": lambda r: r["nversions"],
               "blobs": lambda r: r["blobs"],
               "dats": lambda r: r["dats"],
               "total": lambda r: r["total"],
               # sort by how *complete* a depot is, not by raw file count
               "local": lambda r: (local.get(r["depot"], 0) /
                                   max(1, r["nblobs"] + r["ndats"]),
                                   local.get(r["depot"], 0))}[self.dsort[0]]
        rows = sorted(rows, key=key, reverse=self.dsort[1])

        self.dep_tv.delete(*self.dep_tv.get_children())
        for r in rows:
            dep = r["depot"]
            have = local.get(dep, 0)
            tot = r["nblobs"] + r["ndats"]
            self.dep_tv.insert("", "end", iid=dep, values=(
                dep, short_name(self.depot_names.get(dep, "")), r["nversions"],
                human(r["blobs"]), human(r["dats"]), human(r["total"]),
                f"{have * 100 // max(1, tot)}%  ({have}/{tot})" if have else ""),
                tags=("extracted",) if dep in self.history else ())
        named = sum(1 for r in rows if r["depot"] in self.depot_names)
        if self._on_depots_tab():      # a background recount must not stomp on
            self.status_var.set(       # a message about whatever you're doing now
                f"{len(rows):,} depots shown, {named:,} named"
                + ("" if self.depot_names else
                   '  -  press "Fetch names from Steam" to name them'))

    def _on_depots_tab(self) -> bool:
        try:
            return self.nb.nametowidget(self.nb.select()) is self.depots_tab
        except Exception:                                           # noqa: BLE001
            return False

    def _open_depot_from_list(self, _e):
        sel = self.dep_tv.selection()
        if not sel:
            return
        self.depot_var.set(sel[0])
        self.depot_rows = []
        self.nb.select(self.depot_tab)
        self._scan_depot()

    def _export_depots(self):
        if not self.depot_stats:
            self.status_var.set("load the depot list first")
            return
        p = filedialog.asksaveasfilename(defaultextension=".csv",
                                         initialfile="steam2_depots.csv",
                                         filetypes=[("CSV", "*.csv")])
        if not p:
            return
        local = self._local_counts()
        try:
            with open(p, "w", encoding="utf-8", newline="") as fh:
                fh.write("depot,name,versions,max_version,blob_files,dat_files,"
                         "blob_bytes,dat_bytes,total_bytes,local_files\n")
                for r in sorted(self.depot_stats, key=lambda x: int(x["depot"])):
                    nm = self.depot_names.get(r["depot"], "").replace('"', "'")
                    fh.write(f'{r["depot"]},"{nm}",{r["nversions"]},{r["maxver"]},'
                             f'{r["nblobs"]},{r["ndats"]},{r["blobs"]},{r["dats"]},'
                             f'{r["total"]},{local.get(r["depot"], 0)}\n')
            self.status_var.set(f"wrote {p}")
        except Exception as exc:                                    # noqa: BLE001
            self._fail(f"could not write CSV: {exc}")

    # ---- depot picker
    def _scan_depot(self, refresh: bool = False):
        dep = self.depot_var.get().strip()
        if not dep.isdigit():
            messagebox.showinfo(APP_NAME, "Enter a numeric depot id, e.g. 852")
            return
        if not self._need_base():
            return
        self.status_var.set(f"re-downloading both listings for depot {dep} ..." if refresh else
                            f"scanning depot {dep} ... "
                            f"(the first run downloads both full listings)")
        self.update_idletasks()

        def work():
            try:
                blobs = self.listing.get(self.base() + "blobs/", refresh)
                dats = self.listing.get(self.base() + "dats/", refresh)
            except Exception as exc:                                # noqa: BLE001
                self.after(0, lambda e=exc: self._fail(str(e)))
                return
            # group by version only: a blob and its dat carry DIFFERENT crcs, so
            # pairing on crc would make every version look duplicated
            rows = {}
            for kind, entries in (("blobs", blobs), ("dats", dats)):
                for e in entries:
                    m = NAME_RE.match(e.name)
                    if not m or m.group(1) != dep:
                        continue
                    ver = int(m.group(2))
                    r = rows.setdefault(ver, {"version": ver, "blobs": [], "dats": []})
                    r[kind].append((m.group(3).lower(), e))
            for r in rows.values():
                r["blobs"].sort()
                r["dats"].sort()
            ordered = [rows[k] for k in sorted(rows)]
            self.after(0, lambda: self._show_depot(dep, ordered))
        threading.Thread(target=work, daemon=True).start()

    def _show_depot(self, dep: str, rows):
        self.depot_rows = rows
        self.depot_id = dep
        self.dtv.delete(*self.dtv.get_children())
        have = self._have_now([e.name for r in rows
                               for _c, e in r["blobs"] + r["dats"]])
        for i, r in enumerate(rows):
            got_b = all(e.name in have for _c, e in r["blobs"]) and r["blobs"]
            got_d = all(e.name in have for _c, e in r["dats"]) and r["dats"]
            self.dtv.insert("", "end", iid=str(i), values=(
                r["version"],
                ", ".join(c for c, _ in r["blobs"]) or "-",
                human(sum(e.size for _, e in r["blobs"])) if r["blobs"] else "missing",
                human(sum(e.size for _, e in r["dats"])) if r["dats"] else "missing",
                "blob + dat" if got_b and got_d else
                "blob only" if got_b else "dat only" if got_d else "-"))
        if not rows:
            self.depot_note.config(text=f"depot {dep}: nothing found")
            self.status_var.set(f"depot {dep}: no files")
            self.cmd_var.set("")
            return

        # a "reset" = the same version exists as more than one blob
        dup = [r for r in rows if len(r["blobs"]) > 1]
        total = sum(sum(e.size for _, e in r["blobs"]) + sum(e.size for _, e in r["dats"])
                    for r in rows)
        if dup:
            sample = "; ".join(f"v{r['version']}: " + ", ".join(c for c, _ in r["blobs"])
                               for r in dup[:4])
            more = f" (+{len(dup) - 4} more versions)" if len(dup) > 4 else ""
            self.depot_note.config(
                text=(f"RESET: depot {dep} has {len(dup)} version(s) with more than one blob - "
                      f"Valve did a full reset here. Download everything, then tell the "
                      f"extractor which blob you mean with --blobcrc <crc>. {sample}{more}"))
        else:
            self.depot_note.config(
                text=(f"depot {dep}: no resets detected - plain "
                      f"'extract <blobs dir> <dats dir> {dep} 0' will work"))

        # extraction walks 0..N, so a hole anywhere in that range is fatal - say
        # so here rather than letting the extractor fail an hour later
        vers = [r["version"] for r in rows]
        gaps = sorted(set(range(min(vers), max(vers) + 1)) - set(vers))
        halves = [r["version"] for r in rows if not r["blobs"] or not r["dats"]]
        bits = []
        if min(vers) != 0:
            bits.append(f"the server's oldest version here is v{min(vers)}, not v0")
        if gaps:
            bits.append("no v" + ", v".join(str(g) for g in gaps[:6])
                        + (" ..." if len(gaps) > 6 else ""))
        if halves:
            bits.append(f"{len(halves)} version(s) have only a blob or only a dat "
                        f"(v{halves[0]})")
        if bits:
            self.depot_note.config(text=self.depot_note.cget("text")
                                   + "   ||   BROKEN CHAIN: " + "; ".join(bits)
                                   + " - extraction needs every version from 0 up")
        self.maxver_var.set(str(max(r["version"] for r in rows)))
        self.status_var.set(f"depot {dep}: {len(rows)} versions, {human(total)} total"
                            f"  |  listings {self._cache_age_text()}")

    # ---- qBittorrent
    def _qb_log(self, msg: str):
        self.qb_txt.insert("end", msg + "\n")
        self.qb_txt.see("end")
        log_to_disk(msg, "[qb] ")

    def _qb_autoconnect(self):
        """Connect on startup so the torrent is ready without a click.

        Skipped on a first run: someone who has never set qBittorrent up
        shouldn't be met with a connection error they didn't ask for."""
        if self.first_run or not self.qb_auto_var.get():
            return
        if not self.qb_url_var.get().strip():
            return
        # Don't fire a login we know will fail: qBittorrent locks an IP out for
        # a while after a few wrong ones, and the password is only on disk if
        # "remember password" is ticked.
        if self.qb_user_var.get().strip() and not self.qb_pass_var.get():
            self.qb_status_var.set("enter your password and press Connect "
                                   "(tick 'remember password' to skip this)")
            self.status_var.set("qBittorrent: password needed - see the "
                                "qBittorrent tab")
            return
        self._qb_log("connecting automatically on startup ...")
        self._qb_connect(auto=True)

    def _qb_connect(self, auto: bool = False):
        self.qb_status_var.set("connecting ...")
        self.update_idletasks()
        client = QBit(self.qb_url_var.get(), self.qb_user_var.get(), self.qb_pass_var.get())

        def work():
            try:
                msg = client.login()
                tors = client.torrents()
            except QBitError as exc:
                self.after(0, lambda e=exc: self._qb_failed(str(e), auto))
                return
            self.after(0, lambda: self._qb_connected(client, msg, tors))
        threading.Thread(target=work, daemon=True).start()

    def _qb_failed(self, msg: str, auto: bool = False):
        self.qb = None
        self.qb_status_var.set(f"not connected - {msg}")
        self._qb_log(f"connection failed: {msg}")
        self._qb_log("Check: qBittorrent > Tools > Preferences > Web UI is enabled, "
                     "and the address/port above match it.")
        self.status_var.set(f"qBittorrent not connected - {msg}  "
                            f"(downloads will use HTTP)")
        if auto:
            try:                       # flag it on the tab, without a popup
                self.nb.tab(self.qb_tab, text="qBittorrent (!)")
            except Exception:
                pass

    def _qb_connected(self, client, msg, tors):
        self.qb = client
        self.qb_status_var.set(f"{msg} - {len(tors)} torrent(s)")
        self._qb_log(f"connected to {client.base} ({msg}), {len(tors)} torrent(s)")
        self.status_var.set(f"qBittorrent connected - {len(tors)} torrent(s)")
        try:
            self.nb.tab(self.qb_tab, text="qBittorrent")
        except Exception:
            pass
        self._qb_fill(tors)

    def _qb_add_webseed(self):
        """Attach the mirror to the torrent as an HTTP source."""
        url = self.qb_webseed_var.get().strip()
        if not url:
            url = self.base()                  # fall back to the server in use
            self.qb_webseed_var.set(url)
        if not url:
            self._qb_log("no web seed URL - type one, or set the Server first")
            return
        if "://" not in url:
            self._qb_log(f"'{url}' is not a URL - it needs http:// or https://")
            return
        if not (self.qb and self.qb_hash):
            messagebox.showinfo(APP_NAME, "Connect and pick the torrent first.")
            return
        thash = self.qb_hash

        def work():
            try:
                have = self.qb.web_seeds(thash)
                if any(u.rstrip("/") == url.rstrip("/") for u in have):
                    msg = f"{url} is already a web seed on this torrent"
                else:
                    self.qb.add_web_seeds(thash, [url])
                    now = self.qb.web_seeds(thash)
                    msg = (f"added {url} as a web seed ({len(now)} in total)"
                           if any(u.rstrip("/") == url.rstrip("/") for u in now)
                           else f"qBittorrent accepted the call but {url} is not "
                                f"listed - check the torrent's properties")
            except QBitError as exc:
                msg = f"could not add the web seed: {exc}"
            self.after(0, lambda: (self._qb_log(msg), self.status_var.set(msg)))
        threading.Thread(target=work, daemon=True).start()

    def _qb_load_torrents(self):
        if not self.qb:
            self._qb_log("connect first")
            return

        def work():
            try:
                tors = self.qb.torrents()
            except QBitError as exc:
                self.after(0, lambda e=exc: self._qb_log(f"error: {e}"))
                return
            self.after(0, lambda: self._qb_fill(tors))
        threading.Thread(target=work, daemon=True).start()

    def _qb_fill(self, tors):
        self.qb_torrents = tors
        labels = [f'{t.get("name", "?")[:70]}  [{t.get("progress", 0) * 100:.0f}%]'
                  for t in tors]
        self.qb_combo["values"] = labels
        pick = next((i for i, t in enumerate(tors) if t.get("hash") == self.qb_hash), None)
        if pick is None:
            # guess the release torrent by name
            pick = next((i for i, t in enumerate(tors)
                         if re.search(r"steam2|terarelease|blob", t.get("name", ""), re.I)), None)
        if pick is not None:
            self.qb_combo.current(pick)
            self._qb_pick()

    def _qb_pick(self, _e=None):
        i = self.qb_combo.current()
        if i < 0 or i >= len(self.qb_torrents):
            return
        t = self.qb_torrents[i]
        self.qb_hash = t.get("hash", "")
        self.qb_save_path = t.get("save_path", "")
        self._qb_log(f'selected "{t.get("name")}" ({t.get("progress", 0) * 100:.1f}% complete, '
                     f'save path {self.qb_save_path})')

        def work():
            try:
                files = self.qb.files(self.qb_hash)
            except QBitError as exc:
                self.after(0, lambda e=exc: self._qb_log(f"could not read files: {e}"))
                return
            self.after(0, lambda: self._qb_indexed(files))
        threading.Thread(target=work, daemon=True).start()

    def _qb_indexed(self, files):
        self.qb_index = {Path(f["name"].replace("\\", "/")).name: f for f in files}
        nblob = sum(1 for n in self.qb_index if n.endswith(".blob"))
        ndat = sum(1 for n in self.qb_index if n.endswith(".dat"))
        self._qb_log(f"indexed {len(files):,} files in the torrent "
                     f"({nblob:,} blobs, {ndat:,} dats)")
        if not nblob and not ndat:
            self._qb_log("warning: this torrent has no .blob/.dat files - "
                         "is it the right one?")
            return
        bd, dd = self._qb_torrent_dirs()
        if bd and dd and bd.parent == dd.parent:
            self.torrent_dir_var.set(str(bd.parent))
            self._qb_log(f"torrent folder: {bd.parent} (read only - nothing is "
                         f"ever written there)")
        self._local_cache = None            # the torrent changes what you "have"
        if self.depot_stats:
            self._show_depots()

    # ---- depot list: right-click actions
    def _depot_menu(self, e):
        iid = self.dep_tv.identify_row(e.y)
        if iid and iid not in self.dep_tv.selection():
            self.dep_tv.selection_set(iid)
        if not self.dep_tv.selection():
            return
        sel = self.dep_tv.selection()
        n = len(sel)
        state = "normal" if (self.qb and self.qb_hash and self.qb_index) else "disabled"
        one = "whole depot" if n == 1 else f"{n} depots"
        self.dmenu.entryconfig(1, state="normal" if n == 1 else "disabled")
        self.dmenu.entryconfig(2, label="Download + extract (newest version)"
                               if n == 1 else f"Download + extract {n} depots in turn")
        self.dmenu.entryconfig(4, state=state, label=f"Send to qBittorrent ({one})")
        self.dmenu.entryconfig(5, state=state,
                               label="Send to qBittorrent (only what's missing)")
        self.dmenu.entryconfig(7, label=f"Queue HTTP download ({one})")
        self.dmenu.entryconfig(8, state="normal" if n == 1 and sel[0] in self.history
                               else "disabled")
        self.dmenu.entryconfig(11, label="Delete this depot's dats (keep blobs)"
                               if n == 1 else f"Delete the dats of {n} depots "
                                              f"(keep blobs)")
        self.dmenu.tk_popup(e.x_root, e.y_root)

    def _selected_depots(self):
        return list(self.dep_tv.selection())

    def _extract_depot(self):
        """Right-click -> download + extract the newest version of each depot."""
        deps = self._selected_depots()
        if not deps:
            return
        if len(deps) > 1 and not messagebox.askyesno(
                APP_NAME,
                f"Queue {len(deps)} depots, newest version of each?\n\nThey run "
                f"one after another. Anything missing is fetched first (from the "
                f"torrent if it can be), and you won't be asked again per depot."):
            return
        for dep in deps:
            self._queue_task({"kind": "extract", "depot": dep, "version": None,
                              "download": True,
                              "label": f"extract depot {dep} (newest)"}, quiet=True)
        self.nb.select(self.extract_tab)
        self.status_var.set(f"queued {len(deps)} extraction(s)")

    # ---- the task queue: extractions and processing runs, one at a time
    def _queue_task(self, task: dict, quiet: bool = False):
        """Add a long job to the queue, and start it if nothing else is running.

        Extraction and processing both take minutes and both write to the same
        folders, so they share one queue instead of racing each other."""
        task.setdefault("status", "queued")
        self.tasks.append(task)
        self.task_total += 1
        self._render_tasks()
        if not quiet:
            waiting = len(self.tasks) - (0 if self.current_task else 1)
            self.status_var.set(
                task["label"] + (f" - queued, {waiting} ahead of it"
                                 if waiting > 0 else " - starting"))
        if not self.current_task:
            self._task_next()
        return task

    def _task_next(self):
        """Start the next job, or report that the queue has run dry."""
        self.task_pending = False
        if self.current_task:                  # something is still going
            return
        if not self.tasks:
            if self.task_total > 1:
                self._log(f"=== queue finished: {self.task_total} job(s) ===")
                self.status_var.set(f"queue finished - {self.task_total} jobs")
                self.bell()
            self.task_total = 0
            self._render_tasks()
            return
        task = self.tasks.pop(0)
        self.current_task = task
        task["status"] = "running"
        self._render_tasks()
        left = len(self.tasks)
        self._log("")
        self._log(f"=== {task['label']}"
                  + (f", {left} more queued ===" if left else " ==="))
        if task["kind"] == "process":
            self._proc_start(task)
        else:
            self._ensure_depot_rows(task["depot"], lambda: self._begin_extract(task))

    def _task_step(self):
        """Whatever was running has ended, however it ended - move along."""
        self.current_task = None
        self._render_tasks()
        if (self.tasks or self.task_total) and not self.task_pending:
            self.task_pending = True
            self.after(1200, self._task_next)

    def _tasks_running(self) -> bool:
        return bool(self.tasks) or self.task_total > 1

    def _render_tasks(self):
        if not hasattr(self, "ttv"):
            return
        self.ttv.delete(*self.ttv.get_children())
        rows = ([self.current_task] if self.current_task else []) + list(self.tasks)
        for i, t in enumerate(rows):
            self.ttv.insert("", "end", iid=str(i),
                            values=(t["kind"], t["label"], t.get("status", "queued")),
                            tags=("run",) if t.get("status") == "running" else ())
        self.task_note_var.set(f"{len(self.tasks)} waiting" if self.tasks else
                               ("running" if self.current_task else "nothing queued"))

    def _remove_tasks(self):
        """Drop the selected jobs. The one already running is left alone - use
        Stop for that."""
        rows = ([self.current_task] if self.current_task else []) + list(self.tasks)
        drop = {id(rows[int(i)]) for i in self.ttv.selection()
                if int(i) < len(rows) and rows[int(i)] is not self.current_task}
        if not drop:
            self.status_var.set("pick queued job(s) to remove - Stop cancels the "
                                "one that is running")
            return
        self.tasks = [t for t in self.tasks if id(t) not in drop]
        self.task_total = max(1, self.task_total - len(drop)) if self.tasks or \
            self.current_task else 0
        self._render_tasks()
        self.status_var.set(f"removed {len(drop)} queued job(s)")

    def _ask(self, msg: str) -> bool:
        """Confirmations, minus the ones you've already answered for a whole
        batch or turned off with unattended mode."""
        if self._tasks_running() or self.unatt_var.get():
            return True
        return messagebox.askyesno(APP_NAME, msg)

    def _copy_depot_ids(self):
        ids = self._selected_depots()
        if ids:
            self.clipboard_clear()
            self.clipboard_append(" ".join(ids))
            self.status_var.set(f"copied {len(ids)} depot id(s)")

    # ---- what's inside a depot, without extracting it
    def _preview_depot(self, dep=None, ver=None):
        """Read the file list straight out of the newest blob's manifest.

        Blobs are small and you already have all of them, so this answers
        "what's actually in here?" without unpacking gigabytes of dats."""
        if dep is None:
            deps = self._selected_depots()
            if len(deps) != 1:
                messagebox.showinfo(APP_NAME, "Select one depot to preview.")
                return
            dep = deps[0]
        dirs = []
        for root in (self._torrent_root(), Path(self.dir_var.get().strip() or ".")):
            if root:
                dirs += [root / "blobs", root / "blobs" / dep]
        self.status_var.set(f"reading depot {dep}'s manifest ...")

        def work():
            best, best_v = None, -1
            for d in dirs:
                try:
                    for p in d.glob(f"{dep}_*.blob"):
                        m = NAME_RE.match(p.name)
                        if not m:
                            continue
                        v = int(m.group(2))
                        if ver is not None and v > ver:
                            continue
                        if v > best_v:
                            best, best_v = p, v
                except OSError:
                    continue
            if best is None:
                self.after(0, lambda: self.status_var.set(
                    f"no blob for depot {dep} on disk - download one first"))
                return
            try:
                files = manifest_of(best)
            except Exception as exc:                                # noqa: BLE001
                self.after(0, lambda e=exc: self.status_var.set(
                    f"could not read depot {dep}'s manifest: {e}"))
                return
            self.after(0, lambda: self._preview_window(dep, best_v, files))
        threading.Thread(target=work, daemon=True).start()

    def _preview_picker(self):
        """Picker -> preview the version currently targeted in 'up to version'."""
        if not self.depot_id:
            messagebox.showinfo(APP_NAME, "Scan a depot first.")
            return
        v = self.maxver_var.get().strip()
        self._preview_depot(self.depot_id, int(v) if v.isdigit() else None)

    def _preview_window(self, dep: str, ver: int, files):
        name = self.depot_names.get(dep, "")
        win = tk.Toplevel(self)
        win.title(f"depot {dep}" + (f" - {short_name(name, 1)}" if name else "")
                  + f", version {ver} - {len(files):,} files")
        win.geometry("900x560")
        top = ttk.Frame(win, padding=6)
        top.pack(fill="x")
        ttk.Label(top, text="Filter:").pack(side="left")
        fv = tk.StringVar()
        ttk.Entry(top, textvariable=fv, width=40).pack(side="left", padx=4)
        info = ttk.Label(top, text="")
        info.pack(side="left", padx=10)
        body = ttk.Frame(win, padding=(6, 0))
        body.pack(fill="both", expand=True)
        tv = ttk.Treeview(body, columns=("path", "size"), show="headings")
        tv.heading("path", text="Path")
        tv.heading("size", text="Size")
        tv.column("path", width=700, anchor="w", stretch=True)
        tv.column("size", width=110, anchor="e")
        sb = ttk.Scrollbar(body, orient="vertical", command=tv.yview)
        tv.configure(yscrollcommand=sb.set)
        tv.pack(side="left", fill="both", expand=True)
        sb.pack(side="left", fill="y")

        def fill(*_):
            q = fv.get().strip().lower()
            rows = [f for f in files if q in f[0].lower()] if q else files
            tv.delete(*tv.get_children())
            for path, size in rows[:MAX_ROWS]:
                tv.insert("", "end", values=(path, human(size)))
            info.config(text=f"{len(rows):,} files, {human(sum(s for _p, s in rows))}"
                             + (f" (showing the first {MAX_ROWS:,})"
                                if len(rows) > MAX_ROWS else ""))
        fv.trace_add("write", fill)
        fill()

        bot = ttk.Frame(win, padding=6)
        bot.pack(fill="x")

        def save():
            p = filedialog.asksaveasfilename(
                defaultextension=".txt", initialfile=f"depot_{dep}_v{ver}_files.txt",
                filetypes=[("Text", "*.txt")])
            if not p:
                return
            try:
                with open(p, "w", encoding="utf-8") as fh:
                    for path, size in files:
                        fh.write(f"{size}\t{path}\n")
                self.status_var.set(f"wrote {p}")
            except Exception as exc:                                # noqa: BLE001
                self._fail(f"could not write the list: {exc}")

        ttk.Button(bot, text="Save list ...", command=save).pack(side="left")
        ttk.Button(bot, text="Close", command=win.destroy).pack(side="right")
        ttk.Label(bot, foreground="#777",
                  text="read from the manifest in the blob - nothing was extracted"
                  ).pack(side="left", padx=10)
        self.status_var.set(f"depot {dep} v{ver}: {len(files):,} files in the manifest")

    def _depot_entries(self, deps, cb):
        """All blob+dat listing entries for these depots (threaded, uses the cache)."""
        want = set(deps)

        def work():
            try:
                blobs = self.listing.get(self.base() + "blobs/")
                dats = self.listing.get(self.base() + "dats/")
            except Exception as exc:                                # noqa: BLE001
                self.after(0, lambda e=exc: self._fail(str(e)))
                return
            out = []
            for kind, entries in (("blobs", blobs), ("dats", dats)):
                for en in entries:
                    m = NAME_RE.match(en.name)
                    if m and m.group(1) in want:
                        out.append((kind, en))
            self.after(0, lambda: cb(out))
        threading.Thread(target=work, daemon=True).start()

    def _qb_send_depots(self, missing_only: bool):
        """Right-click -> tell qBittorrent to download these depots' files."""
        deps = self._selected_depots()
        if not deps:
            return
        if not (self.qb and self.qb_hash and self.qb_index):
            messagebox.showinfo(APP_NAME, "Connect to qBittorrent first "
                                          "(qBittorrent tab).")
            return
        self.status_var.set(f"looking up {len(deps)} depot(s) ...")

        def got(entries):
            names = [en.name for _k, en in entries]
            if missing_only:
                have = self._local_files()
                names = [n for n in names if n not in have]
            if not names:
                self.status_var.set("nothing to fetch - you already have it all")
                return
            self._qb_send_names(names, f"{len(deps)} depot(s)")
        self._depot_entries(deps, got)

    def _qb_send_names(self, names, label: str):
        """Raise the priority of these files in the torrent, in the background."""
        def work():
            try:
                ids, already, missing, todo = self._qb_raise(names)
            except QBitError as exc:
                self.after(0, lambda e=exc: (
                    self._qb_log(f"could not queue {label}: {e}"),
                    self.status_var.set(f"qBittorrent refused: {e}")))
                return

            def done():
                msg = (f"qBittorrent: {label} -> {len(names)} files, "
                       f"{already} already complete, {len(ids)} queued "
                       f"({human(todo)})")
                if missing:
                    msg += f", {len(missing)} not in the torrent"
                self._qb_log(msg)          # stay where you are: the status bar and
                self.status_var.set(msg)   # the qBittorrent log both have the details
            self.after(0, done)
        threading.Thread(target=work, daemon=True).start()

    def _qb_raise(self, names):
        """Select these files in the torrent. Returns (queued, complete, missing, bytes)."""
        missing = [n for n in names if n not in self.qb_index]
        ids, already = [], 0
        todo = 0
        for n in names:
            f = self.qb_index.get(n)
            if not f:
                continue
            if f.get("progress", 0) >= 1:
                already += 1
            else:
                ids.append(f["index"])
                todo += f["size"] * (1 - f.get("progress", 0))
        if ids:
            # only ever raises: whatever else you have selected stays selected
            self.qb.set_priority(self.qb_hash, ids, QBit.PRIO_HIGH)
            self.qb.resume(self.qb_hash)
        return ids, already, missing, todo

    def _dat_paths_for(self, deps) -> list:
        """Every .dat of these depots that is on disk, in either folder.

        Blobs are never included: they are kilobytes, they hold the manifest,
        and losing them would take the depot out of the list entirely."""
        want, out, seen = set(deps), [], set()
        for root in (self._torrent_root(), Path(self.dir_var.get().strip() or "")):
            if not root:
                continue
            for name, path in self._scan_files(root).items():
                m = NAME_RE.match(name)
                if not (m and name.endswith(".dat") and m.group(1) in want):
                    continue
                key = str(path).lower()
                if key not in seen:
                    seen.add(key)
                    out.append(path)
        return out

    def _delete_dats(self):
        """Reclaim the space a depot's dats take, once you have extracted it.

        The dats are the whole weight of a depot; the blobs are kilobytes. This
        marks them "do not download" in the torrent first - otherwise
        qBittorrent would simply fetch them again - and only then deletes them.
        It is the one place the app removes anything from the torrent folder,
        so it always asks, even in unattended mode."""
        deps = self._selected_depots()
        if not deps:
            return
        paths = self._dat_paths_for(deps)
        on_disk = 0
        for pth in paths:
            try:
                on_disk += pth.stat().st_size
            except OSError:
                pass
        want = set(deps)
        ids, marked = [], 0
        if self.qb and self.qb_hash and self.qb_index:
            for name, f in self.qb_index.items():
                m = NAME_RE.match(name)
                if m and name.endswith(".dat") and m.group(1) in want:
                    ids.append(f["index"])
                    marked += 1
        if not paths and not ids:
            self.status_var.set("no dats of those depots anywhere on disk")
            return

        who = f"depot {deps[0]}" if len(deps) == 1 else f"{len(deps)} depots"
        lines = [f"Delete the dats of {who}?", ""]
        if paths:
            lines.append(f"{len(paths):,} file(s) on disk, {human(on_disk)} freed.")
        else:
            lines.append("Nothing is on disk yet.")
        if ids:
            lines.append(f'{marked:,} file(s) in the torrent will be set to "do not '
                         f'download" first, so qBittorrent does not fetch them again.')
        else:
            lines.append("qBittorrent is not connected, so nothing can be marked - "
                         "the torrent will download them again unless you connect "
                         "first and repeat this.")
        lines += ["", "The blobs are kept, so the depot stays listed and its file "
                      "list can still be previewed. Extracting it later means "
                      "fetching the dats again.", "", "This cannot be undone."]
        if not messagebox.askyesno(APP_NAME, "\n".join(lines)):
            return

        # nothing queued should quietly put them back
        names = {pth.name for pth in paths}
        drop = {id(j) for j in self.dl.jobs
                if j.status != STATUS_ACTIVE and Path(j.rel).name in names}
        if drop:
            with self.dl.lock:
                self.dl.jobs = [j for j in self.dl.jobs if id(j) not in drop]
                self.dl.dirty = set(range(len(self.dl.jobs)))
            self._sync_queue_rows()
        self.status_var.set(f"deleting the dats of {who} ...")

        def work():
            was_running = False
            if ids:
                # stop it first: it must not be writing to these while their
                # priority changes, and Windows will not delete a file it holds
                _ok, was_running = self._qb_hold("the deletion")
                try:
                    self.qb.set_priority(self.qb_hash, ids, QBit.PRIO_SKIP)
                except QBitError as exc:
                    self.after(0, lambda e=exc: (
                        self._log(f"qBittorrent would not mark the files: {e}"),
                        self._qb_release(was_running),
                        self.status_var.set(f"nothing deleted - qBittorrent refused: {e}")))
                    return
                time.sleep(1.5)
            gone = freed = 0
            errs = []
            for pth in paths:
                try:
                    n = pth.stat().st_size
                    pth.unlink()
                    gone += 1
                    freed += n
                except OSError as exc:
                    errs.append(f"{pth.name}: {exc}")
            self.after(0, lambda: self._dats_deleted(who, gone, freed, marked, errs,
                                                     bool(ids), was_running))
        threading.Thread(target=work, daemon=True).start()

    def _dats_deleted(self, who, gone, freed, marked, errs, held=False,
                      was_running=False):
        msg = f"{who}: {gone:,} dat(s) deleted, {human(freed)} freed"
        if marked:
            msg += f", {marked:,} marked \"do not download\""
        if errs:
            msg += f", {len(errs)} could not be removed"
            for line in errs[:10]:
                self._log("could not delete " + line)
            if len(errs) > 10:
                self._log(f"... and {len(errs) - 10} more")
            self._log("files still open are usually held by qBittorrent - pause the "
                      "torrent and try again")
        if held:
            msg += self._qb_release(was_running)
        self._log(msg)
        self.status_var.set(msg)
        self._local_cache = None            # "You have" has just changed
        self._refresh_local()
        if self.qb and self.qb_hash:        # so the Mirror tab and the menus agree
            self._qb_reload_files()

    def _qb_reload_files(self):
        """Re-read the torrent's file list after we have changed it."""
        if not (self.qb and self.qb_hash):
            return

        def work():
            try:
                files = self.qb.files(self.qb_hash)
            except QBitError:
                return
            self.after(0, lambda: self._qb_indexed(files))
        threading.Thread(target=work, daemon=True).start()

    def _http_queue_depots(self):
        deps = self._selected_depots()
        if not deps:
            return
        if not self._writable_save_dir():
            return
        self.status_var.set(f"looking up {len(deps)} depot(s) ...")

        def got(entries):
            jobs = [self._job_for(kind, en.name, en.size, en.approx) for kind, en in entries]
            if not jobs:
                self.status_var.set("nothing found for those depots")
                return
            if self._ask(f"Queue {len(jobs)} files "
                         f"({human(sum(j.size for j in jobs))}) over HTTP?"):
                self._enqueue(jobs)
        self._depot_entries(deps, got)

    # ---- mirror: pull what the torrent hasn't finished straight from the server
    def _mirror_refresh(self, note: str = ""):
        """note survives the refresh, so the result of a run isn't wiped by the
        file count that lands a second later."""
        self._mirror_note = note
        if not (self.qb and self.qb_hash):
            self.mirror_status_var.set("connect to qBittorrent first")
            return
        self.mirror_status_var.set("reading the torrent's file list ...")

        def work():
            try:
                files = self.qb.files(self.qb_hash)
            except QBitError as exc:
                self.after(0, lambda e=exc: self.mirror_status_var.set(f"error: {e}"))
                return
            self.after(0, lambda: self._mirror_fill(files))
        threading.Thread(target=work, daemon=True).start()

    def _mirror_fill(self, files):
        """Everything qBittorrent means to download but hasn't finished."""
        rows = [f for f in files
                if f.get("progress", 0) < 1 and f.get("priority", 0) > 0]
        rows.sort(key=lambda f: Path(f["name"].replace("\\", "/")).name)
        self.mirror_rows = rows
        self.qb_index.update({Path(f["name"].replace("\\", "/")).name: f
                              for f in files})
        self._mirror_render()

    @staticmethod
    def _mirror_base(f) -> str:
        """The plain filename, whichever separator the torrent used."""
        return f["name"].replace(chr(92), "/").rsplit("/", 1)[-1]

    def _mirror_select_zero(self):
        """Select every file the torrent hasn't started - usually what you want
        to mirror, since half-finished ones are already moving."""
        zero = [str(i) for i, f in enumerate(self.mirror_rows)
                if not f.get("progress", 0)]
        self.mtv.selection_set(*zero) if zero else self.mtv.selection_remove(
            *self.mtv.get_children())
        if zero:
            self.mtv.see(zero[0])
        if not zero:
            self.mirror_status_var.set("nothing is at 0% - the torrent has "
                                       "started them all")
            return
        self._mirror_selection_note()

    def _mirror_selection_note(self, _e=None):
        """Say what a run would cost before anyone commits to it."""
        if self.mirror_job:
            return                             # the poll owns the status line
        try:
            sizes = [self.mirror_rows[int(i)].get("size", 0)
                     for i in self.mtv.selection()]
        except (ValueError, IndexError):
            return
        if not sizes:
            self._mirror_render()              # back to the file count
            return
        secs = mirror_eta(sizes, self.rate_agg, self.rate_conn)
        note = (f"roughly {duration(secs)} at the speed you're getting"
                if secs else "no download speed measured yet, so no estimate")
        self.mirror_status_var.set(
            f"{len(sizes):,} selected, {human(sum(sizes))} - "
            f"{note}, torrent paused throughout")

    def _sort_mirror(self, col):
        same = self.msort[0] == col
        self.msort = (col, not self.msort[1] if same else False)
        self._mirror_render()

    def _mirror_render(self):
        """Draw the list in the chosen order.

        Row ids stay the index into mirror_rows, so re-sorting never disturbs
        what you have selected or which files a download would fetch."""
        def depot_of(f):
            m = NAME_RE.match(self._mirror_base(f))
            return int(m.group(1)) if m else -1

        def remaining(f):
            return f.get("size", 0) * (1 - f.get("progress", 0))

        key = {"name": self._mirror_base, "depot": depot_of,
               "size": lambda f: f.get("size", 0),
               "got": lambda f: f.get("progress", 0), "left": remaining,
               "prio": lambda f: f.get("priority", 0)}[self.msort[0]]
        rows = self.mirror_rows
        order = sorted(range(len(rows)), key=lambda i: key(rows[i]),
                       reverse=self.msort[1])
        keep = set(self.mtv.selection())
        self.mtv.delete(*self.mtv.get_children())
        label = {QBit.PRIO_SKIP: "skip", QBit.PRIO_NORMAL: "normal",
                 QBit.PRIO_HIGH: "high", QBit.PRIO_MAX: "maximum"}
        left = 0
        for i in order:
            f = rows[i]
            n = self._mirror_base(f)
            m = NAME_RE.match(n)
            size, prog = f.get("size", 0), f.get("progress", 0)
            left += size - size * prog
            self.mtv.insert("", "end", iid=str(i), values=(
                n, m.group(1) if m else "-", human(size), bar(prog),
                human(size - size * prog),
                label.get(f.get("priority"), f.get("priority"))))
        if keep:
            self.mtv.selection_set(*[i for i in keep if self.mtv.exists(i)])
        msg = f"{len(rows):,} unfinished files, {human(left)} still to fetch"
        if getattr(self, "_mirror_note", ""):
            msg = f"{self._mirror_note}  |  {msg}"
            self._mirror_note = ""
        self.mirror_status_var.set(msg)

    def _mirror_download(self):
        if self.mirror_job:
            messagebox.showinfo(APP_NAME, "A mirror download is already running.")
            return
        try:
            sel = [self.mirror_rows[int(i)] for i in self.mtv.selection()]
        except (ValueError, IndexError):
            sel = []
        if not sel:
            self.mirror_status_var.set("select some files first")
            return
        if not self._need_base() or not self._writable_save_dir():
            return
        if not self.qb_save_path:
            self.mirror_status_var.set("qBittorrent hasn't told us where the "
                                       "torrent lives - press Connect again")
            return
        root = Path(self.qb_save_path)
        jobs = []
        for f in sel:
            n = self._mirror_base(f)
            kind = ("blobs" if n.endswith(".blob") else
                    "dats" if n.endswith(".dat") else "")
            if not kind:
                continue
            j = self._job_for(kind, n, f.get("size", 0))
            # straight into the torrent's own file: qBittorrent can then verify
            # and seed it, and the extractor finds it where it always looks
            rel = f["name"].replace(chr(92), "/")
            j.dest = str(root / rel)
            j.rel = rel                      # what the queue shows
            j.overwrite = True               # replace qB's partial copy at the end
            jobs.append(j)
        if not jobs:
            self.mirror_status_var.set("none of those are blobs or dats")
            return
        total = sum(j.size for j in jobs)
        biggest = max(j.size for j in jobs)
        secs = mirror_eta([j.size for j in jobs], self.rate_agg, self.rate_conn)
        if secs is None:
            estimate = ("\n\nNo speed measured on this mirror yet, so there is "
                        "no estimate. Mirrors differ enormously - the status bar "
                        "will show the real rate once it starts.")
        else:
            estimate = f"\n\nEstimated {duration(secs)} at the speed you're getting."
            if secs > 20 * 60:
                estimate += ("\n\nThe torrent stays paused for all of it.")
                if self.rate_conn > 0 and biggest / self.rate_conn > 20 * 60:
                    estimate += (
                        f"\n\nThe largest file here is {human(biggest)}, and one "
                        f"file only ever gets one connection "
                        f"({human_speed(self.rate_conn)} so far), so extra threads "
                        f"cannot speed it up. The torrent may be the better route "
                        f"for something that big.")
        if not self._ask(f"Fetch {len(jobs)} file(s) ({human(total)}) from the "
                         f"server instead of waiting for the torrent?{estimate}"):
            return
        if not self._space_ok(total):
            return

        # These files belong to the torrent, so qBittorrent must not be writing
        # to them while we do. Pausing is not optional here.
        paused, was_running = self._qb_hold("the mirror download")
        if not paused:
            messagebox.showwarning(
                APP_NAME,
                "Could not pause the torrent, and these files belong to it - "
                "letting qBittorrent write to them at the same time risks "
                "corrupting them.\n\nPause it yourself in qBittorrent, then try "
                "again.")
            self.mirror_status_var.set("not started - the torrent would not pause")
            return
        # track whatever the queue actually holds for these URLs, and let them
        # jump ahead of any backlog - the torrent is paused until they finish
        self.mirror_job = {"jobs": self._enqueue(jobs, urgent=True) or jobs,
                           "paused": paused, "was_running": was_running}
        self._start()
        self.btn_mirror.config(state="disabled")
        self.mirror_status_var.set(
            f"downloading {len(jobs)} file(s), {human(total)} ...")
        self._mirror_poll()

    def _mirror_poll(self):
        if not self.mirror_job:
            return
        jobs = self.mirror_job["jobs"]
        total = sum(j.size for j in jobs)
        got = sum(j.size if j.status in (STATUS_DONE, STATUS_SKIP) else j.done
                  for j in jobs)
        self.mirror_pbar.config(maximum=max(1, total), value=got)
        done = sum(1 for j in jobs
                   if j.status not in (STATUS_QUEUED, STATUS_ACTIVE))
        speed = sum(j.speed for j in jobs if j.status == STATUS_ACTIVE)
        self.mirror_status_var.set(
            f"mirroring {done}/{len(jobs)} file(s), {human(got)} of "
            f"{human(total)}" + (f" at {human_speed(speed)}" if speed else ""))
        if any(j.status in (STATUS_QUEUED, STATUS_ACTIVE) for j in jobs):
            self.after(1000, self._mirror_poll)
            return
        self._mirror_finished()

    def _mirror_finished(self):
        job, self.mirror_job = self.mirror_job, None
        self.btn_mirror.config(state="normal")
        self.mirror_pbar.config(value=0)
        done = [j for j in job["jobs"] if j.status in (STATUS_DONE, STATUS_SKIP)]
        msg = f"mirrored {len(done)}/{len(job['jobs'])} file(s)"
        if len(done) < len(job["jobs"]):
            msg += f", {len(job['jobs']) - len(done)} failed"
        self._local_cache = None

        # The files are in the torrent's own layout now, but qBittorrent still
        # believes they are missing - only a recheck changes its mind.
        rechecked = False
        if done and self.mirror_recheck_var.get() and self.qb and self.qb_hash:
            try:
                self.qb.recheck(self.qb_hash)
                rechecked = True
                self._qb_log("recheck started - qBittorrent is verifying the "
                             "mirrored files")
                msg += ", rechecking"
            except QBitError as exc:
                self._qb_log(f"could not start a recheck: {exc}")

        if job["paused"]:
            msg += self._qb_release(job.get("was_running", True))
        if done and not rechecked:
            msg += " - recheck the torrent in qBittorrent to have it count them"
        self._log(msg)
        self._mirror_refresh(msg)

    def _qb_hold(self, why: str):
        """Stop the torrent while we touch its files.

        Returns (ok, was_running). A torrent you had already stopped is left
        stopped afterwards - we only ever put it back the way we found it."""
        try:
            state = self.qb.state(self.qb_hash)
        except QBitError as exc:
            state = ""
            self._qb_log(f"could not read the torrent's state ({exc}) - "
                         f"assuming it was running")
        if state and not QBit.is_running(state):
            self._qb_log(f"torrent is already stopped ({state}) - it will be left "
                         f"that way after {why}")
            return True, False
        try:
            ok = self.qb.pause(self.qb_hash)
        except QBitError as exc:
            self._qb_log(f"could not pause the torrent: {exc}")
            return False, True
        if ok:
            self._qb_log(f"torrent paused for {why}")
        return ok, True

    def _qb_release(self, was_running: bool) -> str:
        """Undo _qb_hold. Says what happened, for the status line."""
        if not was_running:
            self._qb_log("torrent left stopped - it was not running before")
            return ", torrent left stopped (it was not running before)"
        try:
            self.qb.resume(self.qb_hash)
            self._qb_log("torrent resumed")
            return ", torrent resumed"
        except QBitError as exc:
            self._qb_log(f"could NOT resume the torrent: {exc}")
            return " - COULD NOT RESUME THE TORRENT, do it in qBittorrent"

    def _qb_torrent_dirs(self):
        """Locate the torrent's blobs/ and dats/ folders on disk."""
        root = Path(self.qb_save_path or "")
        bd = dd = None
        for name, f in self.qb_index.items():
            p = root / f["name"].replace("\\", "/")
            if bd is None and name.endswith(".blob"):
                bd = p.parent
            elif dd is None and name.endswith(".dat"):
                dd = p.parent
            if bd and dd:
                break
        return bd, dd

    def _qb_start(self, dep: str, ver: int, rows) -> bool:
        """Select this depot's files in the torrent. False = caller should use HTTP."""
        if not (self.qb and self.qb_hash and self.qb_index):
            return False
        needed = []
        for r in rows:
            for _c, e in r["blobs"]:
                needed.append(e.name)
            for _c, e in r["dats"]:
                needed.append(e.name)
        missing = [n for n in needed if n not in self.qb_index]
        if missing:
            self._log(f"{len(missing)} of {len(needed)} files aren't in the torrent - "
                      f"using HTTP instead")
            self._qb_log(f"depot {dep}: {len(missing)} files not found in the torrent, "
                         f"falling back to HTTP")
            return False

        bd, dd = self._qb_torrent_dirs()
        if not bd or not dd:
            self._log("could not locate the torrent's blobs/dats folders - using HTTP")
            return False

        try:
            raise_ids, already, _missing, todo_bytes = self._qb_raise(needed)
        except QBitError as exc:
            self._log(f"qBittorrent refused the request ({exc}) - using HTTP")
            return False

        self._log(f"qBittorrent: {len(needed)} files for depot {dep} v0-{ver}; "
                  f"{already} already complete, {len(raise_ids)} to fetch "
                  f"({human(todo_bytes)})")
        if raise_ids:
            self._qb_log(f"depot {dep}: raised priority on {len(raise_ids)} files")
        self.pipe = {"mode": "qb", "depot": dep, "version": ver,
                     "needed": needed, "dirs": (bd, dd), "polls": 0, "done": -1}
        if not raise_ids:
            self._log("everything is already in the torrent - extracting now")
            self.pipe = None
            self._run_extract(bdir=bd, ddir=dd)
            return True
        self._log(f'waiting for qBittorrent ... (press "Stop" to give up; '
                  f"files come from {bd.parent})")
        self._qb_poll()
        return True

    def _qb_poll(self):
        if not self.pipe or self.pipe.get("mode") != "qb":
            return

        def work():
            try:
                files = self.qb.files(self.qb_hash)
            except QBitError as exc:
                self.after(0, lambda e=exc: self._log(f"lost qBittorrent: {e}"))
                self.after(0, lambda: self.after(5000, self._qb_poll))
                return
            idx = {Path(f["name"].replace("\\", "/")).name: f for f in files}
            self.after(0, lambda: self._qb_progress(idx))
        threading.Thread(target=work, daemon=True).start()

    def _qb_progress(self, idx):
        if not self.pipe or self.pipe.get("mode") != "qb":
            return
        needed = self.pipe["needed"]
        self.qb_index.update({n: f for n, f in idx.items() if n in self.qb_index})
        done = sum(1 for n in needed if idx.get(n, {}).get("progress", 0) >= 1)
        got = sum(idx[n]["size"] * idx[n].get("progress", 0) for n in needed if n in idx)
        tot = sum(idx[n]["size"] for n in needed if n in idx)
        self.status_var.set(f"qBittorrent: {done}/{len(needed)} files, "
                            f"{human(got)} / {human(tot)}")
        if done >= len(needed):
            bd, dd = self.pipe["dirs"]
            self.pipe = None
            self._local_cache = None
            self._log(f"qBittorrent finished all {len(needed)} files")
            self._run_extract(bdir=bd, ddir=dd)
            return

        # say something every ~30s, and name what it's still waiting on, so a
        # stalled torrent doesn't look like a hung app
        self.pipe["polls"] += 1
        if self.pipe["polls"] % 10 == 1 or done != self.pipe["done"]:
            waiting = [n for n in needed if idx.get(n, {}).get("progress", 0) < 1]
            self._qb_log(f"{done}/{len(needed)} complete, {human(tot - got)} left; "
                         f"waiting on " + ", ".join(waiting[:3])
                         + (f" +{len(waiting) - 3} more" if len(waiting) > 3 else ""))
            if self.pipe["polls"] > 20 and done == self.pipe["done"]:
                self._qb_log("no progress yet - is the torrent paused, or are these "
                             "files still set to 'Do not download' by something else?")
            self.pipe["done"] = done
        self.after(3000, self._qb_poll)

    # ---- extract tab / pipeline
    def _log(self, msg: str):
        self.log_txt.insert("end", msg + "\n")
        self.log_txt.see("end")
        log_to_disk(msg)

    def _pick_out(self):
        d = filedialog.askdirectory(initialdir=self.out_var.get() or self.dir_var.get() or ".")
        if d:
            self.out_var.set(d)

    def _open_out(self):
        d = self.last_out or Path(self.out_var.get().strip() or "")
        if not d or not d.exists():
            self.status_var.set("nothing extracted there yet")
            return
        try:
            os.startfile(str(d))                                    # noqa: B950
        except AttributeError:
            os.system(f'xdg-open "{d}"')

    def _writable_save_dir(self) -> bool:
        """Refuse to download into the torrent's own folder - qBittorrent owns it."""
        tor = self._torrent_root()
        save = Path(self.dir_var.get().strip() or ".")
        if not tor:
            return True
        try:
            inside = save == tor or tor in save.parents
        except Exception:                                           # noqa: BLE001
            inside = False
        if not inside:
            return True
        messagebox.showinfo(
            APP_NAME,
            f'"Save to" points inside the torrent folder:\n\n{save}\n\n'
            f"Downloading there would drop extra files into what qBittorrent "
            f"manages, and its next recheck would fight with them. Point "
            f'"Save to" (top bar) at a different folder - it is only used for '
            f"the few files the torrent can't give you. The torrent folder is "
            f"still read for extraction, never written to.")
        self.status_var.set('change "Save to" - it must not be inside the '
                            'torrent folder')
        return False

    def _local_paths(self) -> dict:
        """basename -> full path, across the torrent folder and the download folder.

        A file the torrent hasn't finished is skipped: it exists on disk at full
        size but is full of holes, and handing that to the extractor would be
        worse than not finding it at all."""
        save = Path(self.dir_var.get().strip() or ".")
        tor = self._torrent_root()
        found = self._scan_files(tor) if tor and tor != save else {}
        if self.qb_index:
            for n, f in self.qb_index.items():
                if f.get("progress", 0) < 1:
                    found.pop(n, None)
        for n, p in self._scan_files(save).items():
            found.setdefault(n, p)
        return found

    def _have_now(self, names) -> set:
        """Which of these exact files are on disk and finished.

        A handful of stat() calls, so the picker can show it per version
        without waiting for the full folder scan."""
        dirs = []
        for root in (self._torrent_root(), Path(self.dir_var.get().strip() or ".")):
            if root:
                dirs += [root / "blobs", root / "dats"]
        out = set()
        for n in names:
            f = self.qb_index.get(n)
            if f and f.get("progress", 0) < 1:      # in the torrent, not finished
                continue
            dep = n.split("_", 1)[0]
            for d in dirs:
                if (d / n).exists() or (d / dep / n).exists():
                    out.add(n)
                    break
        return out

    def _chain_names(self, dep: str, ver: int):
        """Every blob+dat filename in the 0..ver chain, or None if not scanned."""
        if self.depot_id != dep or not self.depot_rows:
            return None
        blobs, dats = [], []
        for r in self.depot_rows:
            if r["version"] <= ver:
                blobs += [e.name for _c, e in r["blobs"]]
                dats += [e.name for _c, e in r["dats"]]
        return blobs, dats

    @staticmethod
    def _sibling(known: Path, want: str, dep: str) -> Path:
        """Given the blobs folder, name the dats folder (or the other way round),
        for both the flat and the grouped layout."""
        if known.name == dep:                       # ...\blobs\852
            return known.parent.parent / want / dep
        return known.parent / want                  # ...\blobs

    def _stage(self, dep: str, ver: int, blobs, dats, paths):
        """Chain split across folders: build one folder of links to the files.

        Hard links, so nothing is copied and the torrent folder is untouched -
        it only gets a second name pointing at the same bytes. Falls back to a
        real copy across drives."""
        stage = Path(self.out_var.get().strip() or ".") / "_stage" / f"{dep}_v{ver}"
        copied = 0
        for sub, names in (("blobs", blobs), ("dats", dats)):
            d = stage / sub
            shutil.rmtree(d, ignore_errors=True)
            d.mkdir(parents=True, exist_ok=True)
            for n in names:
                src, dst = paths[n], d / n
                try:
                    os.link(src, dst)
                except OSError:
                    shutil.copy2(src, dst)
                    copied += 1
        self._log(f"the chain is spread over two folders - collected "
                  f"{len(blobs) + len(dats)} files in {stage}"
                  + (f" ({copied} had to be copied)" if copied else " (hard links)"))
        self.stage_dir = stage
        return stage / "blobs", stage / "dats"

    def _resolve_dirs(self, dep: str, ver):
        """Work out which folders to hand the extractor. (None, None) = can't."""
        paths = self._local_paths()
        chain = self._chain_names(dep, ver) if isinstance(ver, int) else None
        if chain:
            blobs, dats = chain
            missing = [n for n in blobs + dats if n not in paths]
            if missing:
                self._log(f"{len(missing)} of {len(blobs) + len(dats)} files for "
                          f"depot {dep} v0-{ver} aren't on disk yet "
                          f"(first: {missing[0]})")
                return None, None
            bdirs = {paths[n].parent for n in blobs}
            ddirs = {paths[n].parent for n in dats}
            if len(bdirs) <= 1 and len(ddirs) <= 1:
                bd = bdirs.pop() if bdirs else None
                dd = ddirs.pop() if ddirs else None
                # some depots are blob-only, with no dats anywhere in the chain.
                # That is not a split chain - pair the folder with its sibling
                # instead of copying everything into a staging folder.
                if bd and not dd:
                    dd = self._sibling(bd, "dats", dep)
                elif dd and not bd:
                    bd = self._sibling(dd, "blobs", dep)
                if bd and dd:
                    return bd, dd
            return self._stage(dep, ver, blobs, dats, paths)

        # not scanned: fall back to whichever folder actually holds this depot
        cands = []
        for root in (self._torrent_root(), Path(self.dir_var.get().strip() or ".")):
            if not root:
                continue
            cands += [(root / "blobs" / dep, root / "dats" / dep),
                      (root / "blobs", root / "dats")]
        for bdir, ddir in cands:
            if bdir.is_dir() and ddir.is_dir() and \
                    any(bdir.glob(f"{dep}_*.blob")) and any(ddir.glob(f"{dep}_*.dat")):
                return bdir, ddir
        return None, None

    def _find_extractor(self):
        """extract.exe, from the download folder or from the torrent itself."""
        for root in (Path(self.dir_var.get().strip() or "."), self._torrent_root()):
            if root and (root / "extractor" / "extract.exe").exists():
                return root / "extractor" / "extract.exe"
        return None

    def _picker_version(self):
        """The version the picker is pointed at: the row you selected if you
        selected one, otherwise whatever the Version box says."""
        sel = self.dtv.selection()
        if sel:
            picked = [self.depot_rows[int(i)]["version"] for i in sel
                      if int(i) < len(self.depot_rows)]
            if picked:
                return max(picked)
        v = self.maxver_var.get().strip()
        return int(v) if v.isdigit() else max(r["version"] for r in self.depot_rows)

    def _picker_crc(self, ver: int) -> str:
        """--blobcrc, needed only when a reset put two blobs on one version."""
        chain = [r for r in self.depot_rows if r["version"] <= ver]
        if not any(len(r["blobs"]) > 1 for r in chain):
            return ""
        target = next((r for r in chain if r["version"] == ver), None)
        return target["blobs"][0][0] if target and target["blobs"] else ""

    def _on_pick_version(self, _e=None):
        """Selecting a version in the picker points everything at that version."""
        sel = self.dtv.selection()
        if not sel or not self.depot_rows:
            return
        picked = [self.depot_rows[int(i)]["version"] for i in sel
                  if int(i) < len(self.depot_rows)]
        if picked:
            self.maxver_var.set(str(max(picked)))

    def _extract_from_picker(self):
        """Depot picker -> queue the version you picked, and its chain."""
        if not self.depot_rows or not self.depot_id:
            messagebox.showinfo(APP_NAME, "Scan a depot first.")
            return
        dep = self.depot_id
        ver = self._picker_version()
        if not any(r["version"] == ver for r in self.depot_rows):
            messagebox.showinfo(APP_NAME, f"Depot {dep} has no version {ver}. Pick "
                                          f"one from the list, or type one that exists.")
            return
        if not self.out_var.get().strip():
            self.out_var.set(str(Path(self.dir_var.get().strip() or ".") / "extracted"))
        self._queue_task({"kind": "extract", "depot": dep, "version": ver,
                          "download": True,
                          "label": f"extract depot {dep} v{ver}"})
        self.nb.select(self.extract_tab)

    def _go_extract(self, download: bool = True):
        """The Extract tab's own buttons: queue what the fields say."""
        dep, v = self.edepot_var.get().strip(), self.ever_var.get().strip()
        if not dep.isdigit() or not v.isdigit():
            messagebox.showinfo(APP_NAME, "Set a depot id and a version first.")
            return
        if not self.out_var.get().strip():
            self.out_var.set(str(Path(self.dir_var.get().strip() or ".") / "extracted"))
        self._queue_task({"kind": "extract", "depot": dep, "version": int(v),
                          "download": download, "crc": self.ecrc_var.get().strip(),
                          "filter": self.efilter_var.get().strip(),
                          "label": f"extract depot {dep} v{v}"
                                   + ("" if download else " (no download)")})

    def _begin_extract(self, task: dict):
        """Run one queued extraction: the depot's rows are loaded by now."""
        dep = task["depot"]
        ver = task.get("version")
        if ver is None:                       # "newest", resolved once we can see
            ver = max((r["version"] for r in self.depot_rows), default=None)
            if ver is None:
                self._log(f"depot {dep}: nothing to extract")
                self._task_step()
                return
            task["version"] = ver
            task["label"] = f"extract depot {dep} v{ver}"
            self._render_tasks()
        self.edepot_var.set(dep)
        self.ever_var.set(str(ver))
        self.ecrc_var.set(task.get("crc") or self._picker_crc(ver))
        if task.get("filter") is not None:
            self.efilter_var.set(task["filter"])
        if not self.out_var.get().strip():
            self.out_var.set(str(Path(self.dir_var.get().strip() or ".") / "extracted"))
        if not task.get("download", True):
            self._run_extract()
            return
        self._start_pipeline(dep, ver)

    def _ensure_depot_rows(self, dep: str, cb):
        if self.depot_id == dep and self.depot_rows:
            cb()
            return
        self._log(f"scanning depot {dep} (loading the file listings) ...")
        self.depot_var.set(dep)
        self.depot_rows = []
        self._scan_depot()

        def wait(n=0):
            if self.depot_rows and self.depot_id == dep:
                cb()
            elif n > 180:
                self._log("gave up waiting for the listing - check your connection")
                self._task_step()
            else:
                self.after(1000, lambda: wait(n + 1))
        wait()

    def _start_pipeline(self, dep: str, ver: int):
        rows = [r for r in self.depot_rows if r["version"] <= ver]
        if not rows:
            self._log(f"depot {dep} has no version {ver}")
            self._task_step()
            return
        # prefer the torrent when it's connected and actually has these files
        if self.qb_use_var.get() and self.qb and self.qb_hash:
            if self._qb_start(dep, ver, rows):
                return

        jobs = []
        for r in rows:
            for _crc, e in r["blobs"]:
                jobs.append(self._job_for("blobs", e.name, e.size, e.approx))
            for _crc, e in r["dats"]:
                jobs.append(self._job_for("dats", e.name, e.size, e.approx))
        root = Path(self.dir_var.get().strip() or ".")
        if not self._find_extractor():
            jobs.append(self._job_for("extractor", "extract.exe", 1933312))

        # anything the torrent already has counts as present - don't download twice
        elsewhere = self._local_paths()

        def present(j):
            p = root / j.rel
            if p.exists() and size_match(p.stat().st_size, j.size, j.approx):
                return True
            q = elsewhere.get(Path(j.rel).name)
            return bool(q) and size_match(q.stat().st_size, j.size, j.approx)

        missing = [j for j in jobs if not present(j)]
        need = sum(j.size for j in missing)
        self._log(f"depot {dep}, versions 0-{ver}: {len(jobs)} files needed, "
                  f"{len(jobs) - len(missing)} already on disk, "
                  f"{len(missing)} to download ({human(need)})")
        if not missing:
            self._run_extract()
            return
        if not self._space_ok(need):
            self._task_step()
            return
        if not self._ask(f"Download {len(missing)} files ({human(need)}) for depot "
                         f"{dep}, then extract version {ver}?"):
            self._task_step()
            return
        if not self._writable_save_dir():
            self._task_step()
            return
        self._enqueue(missing)
        self.pipe = {"jobs": missing, "depot": dep, "version": ver}
        self._start()
        self._log("downloading ... (the queue at the bottom shows progress)")
        self._pipe_poll()

    def _pipe_poll(self):
        if not self.pipe or self.pipe.get("mode") == "qb":
            return
        jobs = self.pipe["jobs"]
        if any(j.status in (STATUS_QUEUED, STATUS_ACTIVE) for j in jobs):
            self.after(1000, self._pipe_poll)
            return
        bad = [j for j in jobs if j.status in (STATUS_ERR, STATUS_BAD, STATUS_STOP)]
        self.pipe = None
        if bad:
            self._log(f"{len(bad)} file(s) did not download - not extracting.")
            for j in bad[:5]:
                self._log(f"   {Path(j.rel).name}: {j.error or j.status}")
            self._log('Press "Retry failed" in the queue, then try again.')
            self._task_step()
            return
        self._log("all files downloaded")
        self._run_extract()

    def _run_extract(self, bdir=None, ddir=None):
        dep, v = self.edepot_var.get().strip(), self.ever_var.get().strip()
        root = Path(self.dir_var.get().strip() or ".")
        exe = self._find_extractor()
        if not exe:
            self._log("extract.exe is missing - downloading it now, then press Extract again")
            if not self._writable_save_dir():
                return
            self._enqueue([self._job_for("extractor", "extract.exe", 1933312)])
            self._start()
            self._task_step()
            return
        if bdir is None or ddir is None:
            bdir, ddir = self._resolve_dirs(dep, int(v) if v.isdigit() else None)
        if not bdir or not ddir or not bdir.exists() or not ddir.exists():
            self._log(f"couldn't find depot {dep}'s files in "
                      f"{self.dir_var.get().strip() or '.'}"
                      + (f" or {self._torrent_root()}" if self._torrent_root() else "")
                      + ' - use "Download + extract" to fetch what\'s missing')
            self._task_step()
            return
        out_root = Path(self.out_var.get().strip() or (root / "extracted"))
        out_root.mkdir(parents=True, exist_ok=True)
        # extraction doesn't consume the dats - you need room for the output too
        if self.depot_id == dep and self.depot_rows and v.isdigit():
            est = sum(e.size for r in self.depot_rows if r["version"] <= int(v)
                      for _c, e in r["dats"])
            try:
                free = shutil.disk_usage(str(out_root)).free
            except Exception:                                       # noqa: BLE001
                free = None
            if free is not None and est and free < est:
                # unattended runs must not answer "yes" to a full disk
                if self.unatt_var.get() or not messagebox.askyesno(
                        APP_NAME,
                        f"Depot {dep} v{v} is {human(est)} of dats, so the output "
                        f"could be about that big, but only {human(free)} is free "
                        f"on {out_root.drive or out_root}.\n\nExtract anyway?"):
                    self._log("skipped - not enough free space for the output")
                    self._task_step()
                    return
        # The extractor strips every ':' from output paths - including the drive
        # letter - so an absolute --out silently becomes a relative one. Run it
        # inside the output folder and give it a plain relative name instead,
        # sanitised the same way it would sanitise it, so both agree on the path.
        sub = out_folder_name(dep, self.depot_names.get(dep, ""), v)
        self.last_out = out_root / sub
        if len(str(self.last_out)) > 150:
            self._log("warning: that output path is very long; Windows may refuse "
                      "deep paths inside it. A short folder like D:\\steam2 is safer.")

        args = [bdir, ddir, dep, v, "--out", sub]
        if self.ecrc_var.get().strip():
            args += ["--blobcrc", self.ecrc_var.get().strip()]
        if self.efilter_var.get().strip():
            args += ["--filter", self.efilter_var.get().strip()]

        self._log("")
        self._log(f"[working dir: {out_root}]")
        self._log("> extract.exe " + " ".join(
            f'"{a}"' if " " in str(a) else str(a) for a in args))
        self.btn_extract.config(state="disabled")
        self.status_var.set(f"extracting depot {dep} v{v} ...")
        self.ext.run(exe, args, out_root,
                     lambda line: self.after(0, lambda x=line: self._log(x)),
                     lambda rc: self.after(0, lambda c=rc: self._extract_done(c)))

    def _extract_done(self, rc: int):
        self.btn_extract.config(state="normal")
        if self.stage_dir:              # links only - removing them frees the names,
            shutil.rmtree(self.stage_dir, ignore_errors=True)   # never the torrent's data
            self.stage_dir = None
        if rc == 0:
            n = sum(1 for p in self.last_out.rglob("*") if p.is_file()) \
                if self.last_out and self.last_out.exists() else 0
            self._log(f"finished - {n:,} files extracted to {self.last_out}")
            self.status_var.set(f"extraction finished - {n:,} files")
            self._remember_extract(n)
        else:
            self._log(f"extractor exited with code {rc} - see the messages above")
            self.status_var.set("extraction failed")
        if not self._tasks_running():
            self.bell()                       # long jobs shouldn't need watching
        self._task_step()

    def _remember_extract(self, nfiles: int):
        """Keep a note of what has been extracted, so the list can show it."""
        dep, v = self.edepot_var.get().strip(), self.ever_var.get().strip()
        if not dep:
            return
        self.history[dep] = {"version": v, "files": nfiles,
                             "when": time.strftime("%Y-%m-%d %H:%M"),
                             "out": str(self.last_out or "")}
        try:
            HISTORY_PATH.write_text(json.dumps(self.history, indent=1), "utf-8")
        except Exception:                                           # noqa: BLE001
            pass
        if self.depot_stats and self._on_depots_tab():
            self._show_depots()

    def _open_extracted(self):
        """Right-click -> open the folder an earlier extraction wrote to."""
        deps = self._selected_depots()
        rec = self.history.get(deps[0]) if deps else None
        d = Path(rec["out"]) if rec and rec.get("out") else None
        if not d or not d.exists():
            self.status_var.set("nothing extracted for that depot yet")
            return
        try:
            os.startfile(str(d))                                    # noqa: B950
        except AttributeError:
            os.system(f'xdg-open "{d}"')

    def _stop_extract(self):
        """Stop whatever is running and drop the rest of the queue."""
        self.pipe = None
        if self.tasks:
            self._log(f"queue cleared - {len(self.tasks)} job(s) not started")
        self.tasks, self.task_total, self.task_pending = [], 0, False
        self.current_task = None
        if self.ext.busy:
            self.ext.kill()
            self._log("stopped.")
        if self.proc_busy:                  # the queue holds both kinds of job
            self._proc_stop_now()
        self._render_tasks()
        self.btn_extract.config(state="normal")

    def _space_ok(self, need: int) -> bool:
        root = Path(self.dir_var.get().strip() or ".")
        try:
            root.mkdir(parents=True, exist_ok=True)
            free = shutil.disk_usage(str(root)).free
        except Exception:                                           # noqa: BLE001
            return True
        if need and free < need * 1.05:
            return messagebox.askyesno(
                APP_NAME, f"That needs {human(need)} but only {human(free)} is free on "
                          f"{root.drive or root}.\n\nStart anyway?")
        return True

    def _update_cmd(self, *_):
        """Build the exact extract.exe line for the scanned depot + target version."""
        if not self.depot_rows or not self.depot_id:
            self.cmd_var.set("")
            return
        dep = self.depot_id
        v = self.maxver_var.get().strip()
        ver = int(v) if v.isdigit() else max(r["version"] for r in self.depot_rows)
        # show the folder the files are most likely in: the torrent's, if there
        # is one, otherwise your download folder
        root = self._torrent_root() or Path(self.dir_var.get().strip() or ".")
        if self.group_var.get() and not self._torrent_root():
            bdir, ddir = root / "blobs" / dep, root / "dats" / dep
        else:
            bdir, ddir = root / "blobs", root / "dats"

        # naive mode aborts if ANY version in the 0..ver chain has two blobs,
        # and --blobcrc must name a blob of the TARGET version
        chain = [r for r in self.depot_rows if r["version"] <= ver]
        extra = ""
        if any(len(r["blobs"]) > 1 for r in chain):
            target = next((r for r in chain if r["version"] == ver), None)
            if target and target["blobs"]:
                extra = f' --blobcrc {target["blobs"][0][0]}'
        self.cmd_var.set(f'extract.exe "{bdir}" "{ddir}" {dep} {ver}{extra}')

    def _copy_cmd(self):
        if self.cmd_var.get():
            self.clipboard_clear()
            self.clipboard_append(self.cmd_var.get())
            self.status_var.set("extract command copied to clipboard")

    def _add_depot(self, only_selected: bool = False):
        if not self.depot_rows:
            return
        rows = ([self.depot_rows[int(i)] for i in self.dtv.selection()]
                if only_selected else list(self.depot_rows))
        if not only_selected and self.maxver_var.get().strip().isdigit():
            cap = int(self.maxver_var.get().strip())
            rows = [r for r in rows if r["version"] <= cap]
        jobs = []
        for r in rows:
            for _crc, e in r["blobs"]:
                jobs.append(self._job_for("blobs", e.name, e.size, e.approx))
            for _crc, e in r["dats"]:
                jobs.append(self._job_for("dats", e.name, e.size, e.approx))
        if not jobs:
            return
        if not self._ask(f"Queue {len(jobs)} files "
                         f"({human(sum(j.size for j in jobs))})?"):
            return
        self._enqueue(jobs)

    # ---- queue view / run control
    def _sel_jobs(self):
        want = set(self.qtv.selection())
        return [j for j in self.dl.jobs if j.iid in want]

    def _queue_menu(self, e):
        iid = self.qtv.identify_row(e.y)
        if iid:
            if iid not in self.qtv.selection():
                self.qtv.selection_set(iid)
            self.qmenu.tk_popup(e.x_root, e.y_root)

    def _remove_queued(self):
        jobs = self._sel_jobs()
        if not jobs:
            return
        drop = {id(j) for j in jobs if j.status != STATUS_ACTIVE}
        with self.dl.lock:
            self.dl.jobs = [j for j in self.dl.jobs if id(j) not in drop]
            self.dl.dirty = set(range(len(self.dl.jobs)))
        for j in jobs:
            if id(j) in drop:
                j.status = STATUS_STOP          # so a worker skips it if already dequeued
        self._sync_queue_rows()
        self.status_var.set(f"removed {len(drop)} from the queue")

    def _copy_url(self):
        jobs = self._sel_jobs()
        if jobs:
            self.clipboard_clear()
            self.clipboard_append("\n".join(j.url for j in jobs))
            self.status_var.set(f"copied {len(jobs)} URL(s)")

    def _open_job_dir(self):
        jobs = self._sel_jobs()
        if not jobs:
            return
        d = (Path(self.dir_var.get().strip() or ".") / jobs[0].rel).parent
        if not d.exists():
            self.status_var.set("not downloaded yet")
            return
        try:
            os.startfile(str(d))                                    # noqa: B950
        except AttributeError:
            os.system(f'xdg-open "{d}"')

    def _sync_queue_rows(self):
        existing = set(self.qtv.get_children())
        for j in self.dl.jobs:
            j.iid = str(id(j))
            if j.iid not in existing:
                self.qtv.insert("", "end", iid=j.iid,
                                values=(j.rel.replace("\\", "/"), human(j.size),
                                        "", "", j.status))
        keep = {str(id(j)) for j in self.dl.jobs}
        for iid in existing - keep:
            self.qtv.delete(iid)
        self._apply_queue_sort()

    def _sort_queue(self, col):
        same = self.qsort[0] == col
        self.qsort = (col, not self.qsort[1] if same else False)
        self._apply_queue_sort()

    def _apply_queue_sort(self):
        """Reorder the rows in place. move() keeps each row's id, so the live
        progress and speed updates keep landing on the right line."""
        col, rev = self.qsort
        if not col:
            return                             # untouched: the order you added
        key = {"name": lambda j: j.rel.lower(),
               "size": lambda j: j.size,
               "progress": lambda j: j.done / max(1, j.size),
               "speed": lambda j: j.speed,
               "status": lambda j: j.status}[col]
        for pos, j in enumerate(sorted(self.dl.jobs, key=key, reverse=rev)):
            if j.iid and self.qtv.exists(j.iid):
                self.qtv.move(j.iid, "", pos)

    def _start(self):
        d = Path(self.dir_var.get().strip() or ".")
        try:
            d.mkdir(parents=True, exist_ok=True)
        except Exception as exc:                                    # noqa: BLE001
            self._fail(f"cannot create save folder: {exc}")
            return
        need = sum(max(0, j.size - j.done) for j in self.dl.jobs
                   if j.status in (STATUS_QUEUED, STATUS_ACTIVE))
        if not self._space_ok(need):
            return
        self.dl.save_dir = d
        self.dl.n_workers = max(1, int(self.workers_var.get()))
        self.dl.verify = bool(self.verify_var.get())
        self._save_settings()
        self.dl.start()
        self.btn_pause.config(state="normal", text="Pause")
        self.status_var.set("downloading ...")

    def _pause(self):
        if self.dl.pause.is_set():
            self.dl.pause.clear()
            self.btn_pause.config(text="Resume")
            self.status_var.set("paused")
        else:
            self.dl.pause.set()
            self.btn_pause.config(text="Pause")
            self.status_var.set("downloading ...")

    def _stop(self):
        self.dl.stop()
        self.btn_pause.config(state="disabled", text="Pause")
        self.status_var.set("stopped (partial .part files kept, Start resumes them)")

    def _verify_disk(self):
        """Hash every queued file that exists on disk against the sha256 in its name."""
        if self.dl.running:
            messagebox.showinfo(APP_NAME, "Stop the queue first.")
            return
        root = Path(self.dir_var.get().strip() or ".")
        targets = [j for j in self.dl.jobs if j.sha256 and (root / j.rel).exists()]
        if not targets:
            self.status_var.set("nothing on disk to verify")
            return
        self.status_var.set(f"verifying {len(targets)} files on disk ...")

        def work():
            bad = 0
            for n, j in enumerate(targets, 1):
                p = root / j.rel
                try:
                    ok = sha256_file(p).lower() == j.sha256.lower()
                except Exception as exc:                            # noqa: BLE001
                    ok, j.error = False, str(exc)
                if ok:
                    j.status, j.error = STATUS_DONE, ""
                else:
                    j.status, bad = STATUS_BAD, bad + 1
                    j.error = j.error or "sha256 mismatch on disk - delete and re-download"
                self.dl.mark(j)
                self.after(0, lambda n=n: self.status_var.set(
                    f"verifying {n}/{len(targets)} ..."))
            self.after(0, lambda: self.status_var.set(
                f"verified {len(targets)} files - {bad} corrupt"))
        threading.Thread(target=work, daemon=True).start()

    def _restore_dates(self):
        """Apply the timestamps recorded in the archive's *_dates.txt lists.

        These are not when the depot is from - they are how the files looked on
        the content server when it was archived, and the uploader warns the dat
        dates are the less trustworthy half. Only your own download folder is
        touched; the torrent folder is left exactly as qBittorrent wrote it."""
        save = Path(self.dir_var.get().strip() or ".")
        lists = []
        for root in (save, self._torrent_root()):
            if root:
                for nm in ("blobs_dates.txt", "dats_dates.txt"):
                    if (root / nm).exists() and (root / nm) not in lists:
                        lists.append(root / nm)
        if not lists:
            if self._ask("The date lists aren't on disk yet. Download "
                         "blobs_dates.txt and dats_dates.txt from the server now?"):
                self._quick(["blobs_dates.txt", "dats_dates.txt"])
                self._start()
                self.status_var.set('fetching the date lists - press "Restore dates" '
                                    "again when they finish")
            return
        files = self._scan_files(save)
        if not files:
            self.status_var.set("nothing in your download folder to re-date")
            return
        self.status_var.set(f"restoring timestamps on {len(files):,} file(s) ...")

        def work():
            done = bad = 0
            for lp in lists:
                try:
                    with open(lp, encoding="utf-8", errors="replace") as fh:
                        for line in fh:
                            nm, _tab, stamp = line.partition("\t")
                            p = files.get(nm.strip())
                            if not p:
                                continue
                            t = parse_stamp(stamp)
                            if t is None:
                                bad += 1
                                continue
                            try:
                                os.utime(p, (t, t))
                                done += 1
                            except OSError:
                                bad += 1
                except OSError:
                    continue
            self.after(0, lambda: self.status_var.set(
                f"set the archive's recorded date on {done:,} file(s)"
                + (f", {bad:,} could not be set" if bad else "")
                + " - these are archival dates, not release dates "
                  "(the torrent folder was not touched)"))
        threading.Thread(target=work, daemon=True).start()

    def _unattended_tick(self):
        """Keep a long run going without anyone at the keyboard."""
        self.after(60000, self._unattended_tick)
        if not self.unatt_var.get():
            return
        bad = [j for j in self.dl.jobs
               if j.status in (STATUS_ERR, STATUS_STOP, STATUS_BAD)]
        if bad and not self.dl.running:
            self._retry()
            self._start()
            self._log(f"unattended: retrying {len(bad)} failed file(s)")

    def _retry(self):
        n = self.dl.requeue_failed()
        self.status_var.set(f"re-queued {n} files")
        if n and not self.dl.running:
            self._start()

    def _clear_done(self):
        self.dl.clear_finished()
        self._sync_queue_rows()

    def _clear_all(self):
        self.dl.stop()
        self.dl.jobs.clear()
        self._sync_queue_rows()
        self.btn_pause.config(state="disabled")

    # ---- periodic UI refresh
    def _tick(self):
        with self.dl.lock:
            dirty = list(self.dl.dirty)
            self.dl.dirty.clear()
            jobs = list(self.dl.jobs)
        for i in dirty:
            if i >= len(jobs):
                continue
            j = jobs[i]
            if not j.iid or not self.qtv.exists(j.iid):
                continue
            pct = (f"{100.0 * j.done / j.size:.0f}%" if j.size
                   else ("" if not j.done else human(j.done)))
            tag = ("done" if j.status in (STATUS_DONE, STATUS_SKIP) else
                   "err" if j.status in (STATUS_ERR, STATUS_BAD) else
                   "act" if j.status == STATUS_ACTIVE else "")
            self.qtv.item(j.iid,
                          values=(j.rel.replace("\\", "/"), human(j.size), pct,
                                  human_speed(j.speed),
                                  j.status + (f" - {j.error}" if j.error else "")),
                          tags=(tag,) if tag else ())
        # active rows move without a status change, so refresh them every tick
        for j in jobs:
            if j.status == STATUS_ACTIVE and j.iid and self.qtv.exists(j.iid):
                self.qtv.set(j.iid, "progress",
                             f"{100.0 * j.done / j.size:.0f}%" if j.size else human(j.done))
                self.qtv.set(j.iid, "speed", human_speed(j.speed))

        total, done, speed, counts = self.dl.stats()
        # learn the rates from what is actually happening, so estimates follow
        # the mirror in use instead of a number baked in months ago
        if speed > 0:
            self.rate_agg = speed if not self.rate_agg else \
                self.rate_agg * 0.7 + speed * 0.3
            fastest = max((j.speed for j in jobs if j.status == STATUS_ACTIVE),
                          default=0.0)
            if fastest > 0:
                self.rate_conn = fastest if not self.rate_conn else \
                    max(self.rate_conn * 0.7 + fastest * 0.3, fastest)
        self.pbar["maximum"] = max(total, 1)
        self.pbar["value"] = done
        title = APP_NAME
        if self.dl.running and total:
            title = f"{100.0 * done / total:.0f}% - {human_speed(speed)} - {APP_NAME}"
        elif self.ext.busy:
            title = f"extracting - {APP_NAME}"
        if self.title() != title:
            self.title(title)
        if self.dl.running and counts.get(STATUS_ACTIVE):
            self.status_var.set(
                f"{human(done)} / {human(total)}  |  {human_speed(speed)}  |  "
                f"ETA {eta(total - done, speed)}  |  "
                f"done {counts.get(STATUS_DONE, 0) + counts.get(STATUS_SKIP, 0)}/{len(jobs)}"
                f"  errors {counts.get(STATUS_ERR, 0) + counts.get(STATUS_BAD, 0)}")
        elif self.dl.running and not any(t.is_alive() for t in self.dl.workers):
            self.dl.running = False
            self.btn_pause.config(state="disabled")
            self.status_var.set(
                f"queue finished - {counts.get(STATUS_DONE, 0)} downloaded, "
                f"{counts.get(STATUS_SKIP, 0)} already had, "
                f"{counts.get(STATUS_ERR, 0) + counts.get(STATUS_BAD, 0)} failed")
        self.after(250, self._tick)

    # ---- misc
    def _pick_dir(self):
        d = filedialog.askdirectory(initialdir=self.dir_var.get() or ".")
        if d:
            self.dir_var.set(d)

    def _open_dir(self):
        d = Path(self.dir_var.get())
        try:
            d.mkdir(parents=True, exist_ok=True)
            os.startfile(str(d))                                   # noqa: B950 (windows)
        except AttributeError:
            os.system(f'xdg-open "{d}"')
        except Exception as exc:                                    # noqa: BLE001
            self.status_var.set(f"cannot open folder: {exc}")

    def _save_queue(self):
        try:
            pend = [j for j in self.dl.jobs if j.status not in (STATUS_DONE, STATUS_SKIP)]
            if pend:
                QUEUE_PATH.write_text(json.dumps(
                    [{"url": j.url, "rel": j.rel, "size": j.size,
                      "sha256": j.sha256, "approx": j.approx}
                     for j in pend]), "utf-8")
            elif QUEUE_PATH.exists():
                QUEUE_PATH.unlink()
        except Exception:
            pass

    def _load_queue(self):
        try:
            raw = json.loads(QUEUE_PATH.read_text("utf-8"))
        except Exception:
            return
        jobs = [Job(url=d["url"], rel=d["rel"], size=d.get("size", 0),
                    sha256=d.get("sha256", ""), approx=bool(d.get("approx")))
                for d in raw if d.get("url")]
        if jobs:
            self.dl.add(jobs)
            self._sync_queue_rows()
            self.status_var.set(f"restored {len(jobs)} unfinished downloads - press Start")

    def _on_close(self):
        # never leave a torrent paused because the app went away mid-mirror -
        # unless it was already stopped when we found it
        if (self.mirror_job and self.mirror_job.get("paused") and self.qb
                and self.mirror_job.get("was_running", True)):
            try:
                self.qb.resume(self.qb_hash)
            except Exception:                                       # noqa: BLE001
                pass
        self.dl.stop()
        self.ext.kill()
        self._save_settings()
        self._save_queue()
        self.destroy()


if __name__ == "__main__":
    App().mainloop()
