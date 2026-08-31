# steam2 depot downloader

A desktop GUI for browsing, downloading and **extracting** an archive of Valve's
old steam2 content server — 10,876 depots, 12.1 TB of `.blob` and `.dat` files —
with a depot index, real game names, qBittorrent integration and a one-press
download → extract pipeline. Point it at whichever mirror you use: set the
**Server** field in the top bar, and it's remembered.

*Old Steam (steam2) content depots · blobs and dats · manifests · depot
archaeology and game preservation.*

**No dependencies.** Python 3.8+ with tkinter (the python.org Windows installer
includes it). Windows out of the box; Linux/macOS need Wine for the extractor.

```bash
python steam2_downloader.py
```

Everything — settings, cache, folders — is created on first run.

## Quick start

1. A fresh install opens on **Settings**: pick the mirror and the folders, then
   press Save. If you use the torrent, *Save to* must be a *different* folder
   from the torrent's (see [Folders](#folders)).
2. **Depots** builds itself on startup; press *Fetch names from Steam* once.
3. Right-click a depot → **Download + extract**.

It works out which blobs and dats it needs, skips what you have, fetches the
extractor if missing, and runs it with the right arguments — including
`--blobcrc` on reset depots. You never type a command.

## The tabs

**Depots** — all 10,876, built from the server's own file lists when the app
starts, with sizes, version counts and **You have** as a completion percentage
counting both your folder and the torrent's. Sort by any
column; **Find** takes text or `have:complete` / `partial` / `none` /
`extracted`. Already-extracted depots are tinted green.

Right-click one (or several): open in picker · preview file list · download +
extract (several run in turn) · send to qBittorrent, all or only what's missing ·
queue over HTTP · open extracted output · copy ids · delete its dats.

**Delete this depot's dats** reclaims the space once you have extracted a depot.
The dats are the entire weight of it; the blobs are kilobytes and hold the
manifest, so they are kept and the depot stays listed and previewable. Every dat
of that depot is set to *do not download* in the torrent first - otherwise
qBittorrent would simply fetch it again - and the torrent is stopped while the
files go, since Windows will not delete a file qBittorrent still holds open. It
is started again only if it was running to begin with. The files are removed
from your folder and the torrent's alike. It is the one thing that deletes
anything in the torrent folder, so it always asks first, even in unattended
mode, and anything qBittorrent still holds open is reported rather than silently
skipped.

**Browse** — the raw server index, cached locally. The filter box takes `852_`,
`depot:852` for exact ids, or a regex. *Add ALL filtered* queues the whole match
set, not just the visible rows.

**Depot picker** — one row per version with its blob CRC, sizes, and whether you
hold that version's blob, dat, both or neither. **Select a version and press
Download + extract and you get that version**, not the newest: the *version* box
follows whatever row you pick, and the chain 0…N is fetched to build it.
Banners warn about resets and about broken chains (no v0, a missing version, a
version with only half a pair).

**Extract** — depot, version, CRC, an optional regex filter, output folder. The
extractor's output streams into the log.

Extractions and processing runs share one **task queue**, shown on this tab: add
as many as you like, from here, from the picker or from the Process tab, and
they run one after another rather than refusing while something else is busy.
Remove queued jobs from the list; *Stop* ends the running one and drops the
rest.

**Mirror** — every file qBittorrent has queued but not finished, with size, a
progress bar and how much is left. Sort by any column; **Select untouched (0%)**
grabs everything the torrent hasn't started. Select any number and pull them
straight from the server instead of waiting for peers.

They are written **into the torrent's own files**, so the extractor finds them
where it always looks and qBittorrent can seed them. That means:

- the torrent is paused for the run — not optional, since qBittorrent must not
  write to those files at the same time. If it won't pause, the run doesn't
  start. Afterwards it is put back exactly as it was found: a torrent that was
  already stopped stays stopped, and only one that was actually running is
  started again. The same rule holds everywhere the app pauses it.
- each file is downloaded beside the original, verified against the sha256 in
  its name, and only then moved into place. A failed or corrupt download can't
  damage the partial data the torrent already had.
- qBittorrent still thinks the files are missing until it rechecks. Tick
  **recheck the torrent afterwards** to have it done for you, or run a recheck
  yourself later — a recheck of a multi-terabyte torrent is not quick.

Select some files and the status line estimates how long the run would take,
warning before a run over twenty minutes. The estimate comes from the speed
you are actually getting this session — no rates are assumed, because mirrors
differ by orders of magnitude (one measured at 1.9 MB/s while another served the
same file at 10 KB/s). Until something has been downloaded it says so instead of
guessing.

**One file only ever gets one connection**, so extra threads can't speed up a
single large file. On a slow mirror that makes the multi-gigabyte depots a bad
trade against the torrent; on a fast one it hardly matters. The **Server**
dropdown is worth trying when throughput looks poor.

**Process** — what to do with a build once it is extracted. Pick one of your
extracted depots — several at once, they queue up — and pull the **images,
audio and video** out of them into three
flat folders — `images/`, `audio/`, `videos/` — under the media folder. The
game's own directory tree is *not* kept, so two files called `wall01.vtf`
become `wall01.vtf` and `wall01_1.vtf`; a name that is already there at the same
size is one you pulled out before and is left alone, so re-running doesn't pile
up copies. Loose media is copied, needs no tools, and the build is never
modified.

`.vpk` archives need a tool. Point **Source2Viewer** at the **CLI** —
`Source2Viewer-CLI.exe` from
[ValveResourceFormat](https://github.com/ValveResourceFormat/ValveResourceFormat),
*not* the GUI of the same name, which just opens whatever it is handed and can't
be driven from here (if you pick it anyway, the app recognises its complaints
and stops rather than opening a window per archive). Multi-part archives are
opened through their `_dir` file. Each one unpacks into `_media/_vpk/<archive>/`
and its media is then lifted into the same three folders, leaving anything else
it produced in `_vpk`. It is optional — leave it empty and loose media still
works, with the archives reported as skipped. Be aware that Source2Viewer
targets **Source 2** while these depots are Source 1: expect it to open `.vpk`
archives rather than convert what is inside them. The argument line is editable
for that reason, and *Tool help* prints what your build accepts.

**Settings** — the mirror, the four folders (*Save to*, *Extract to*, the
torrent folder, and where processed media goes), the optional Source2Viewer
path, and the download options. It says what is still missing, and warns if
*Save to* would land inside the torrent folder.

**Queue** — Start/Pause/Stop, resumable via HTTP Range. *Verify on disk*
re-hashes against the sha256 in each filename. *Restore dates* applies the
timestamps from `blobs_dates.txt` / `dats_dates.txt` — these are *archival*
dates, recording how the files sat on the content server when it was captured
rather than when a depot is from, and the blob dates are the more trustworthy
half. *Unattended* drops the prompts and retries failures every minute.

## Names

The dump contains no names anywhere. **Fetch names from Steam** builds them from
a ready-made depot→game list covering this exact dump, then fills gaps via
`api.steamcmd.net` (steam2 depots sit next to the app that owns them, so an
unknown depot is looked up by its own id and a few below). Cached in
`.s2cache/steam_names.json` — you pay for it once, and a stopped fetch resumes.
A hand-written `depot_names.json` next to the script overrides everything.

## Preview without extracting

Right-click → **Preview file list**, or *Preview files* in the picker. Reads the
manifest out of the depot's newest blob and lists every path and size, with a
filter and *Save list…*. Blobs are kilobytes, so this answers "is this the one?"
without unpacking gigabytes. If the bytes don't validate as that depot's
manifest it says so rather than showing a guess.

## qBittorrent

Enable the Web UI in qBittorrent, then fill in the address, user and password on
the **qBittorrent** tab and press **Connect**. It auto-selects the release
torrent and reconnects on startup.

On *Download + extract*, instead of crawling the origin server the app raises the
priority of just that depot's files in the torrent, waits for them, and extracts
straight out of the torrent's folder. Nothing is copied or downloaded twice, and
it **only ever raises** priorities — whatever else you're seeding is untouched.
Files missing from the torrent fall back to HTTP automatically.

Troubleshooting: the Web UI often binds to `::`, so prefer `http://localhost:8080`
over a hard-coded `127.0.0.1`. *"rejected the username or password"* means
exactly that (4.x reports it as `Fails.`, 5.x as `401`) — fix it before retrying,
since qBittorrent locks an IP out after enough bad tries. Expired sessions are
re-established automatically, so long runs don't die halfway.

## Folders

| Folder | Owner | Contents |
|---|---|---|
| torrent folder | qBittorrent | the dump. Only ever **read**, except a deliberate mirror download or a dat deletion you confirm |
| **Save to** | the app | only what the torrent can't provide |
| **Output** | the app | extracted files |

The torrent folder is learned from qBittorrent itself and never written to; if
*Save to* points inside it, the app refuses to queue rather than dropping loose
files into a folder qBittorrent will recheck. Keep them side by side, e.g.
`D:\steam2\torrent` and `D:\steam2\http`.

When one chain is split across both folders the extractor can't take two inputs,
so the app collects it into `<output>\_stage\` using **hard links** — no copying,
nothing touched — and deletes them afterwards.

## How the format works

Filenames are `depot_version_crc_sha256.ext`, so every download is verified for
free from its own name. A blob and its dat have **different** CRCs; only the
version links them.

- **blobs** — the file table and manifest (names, sizes, offsets). Kilobytes.
- **dats** — the actual bytes, compressed and encrypted. There is nothing to
  open in a `.dat`; all structure lives in the blobs.
- **depot keys** are compiled into the extractor. If one is missing it stops.

**Deltas.** Extracting version N needs *every* version 0..N of both files. Old
versions are not redundant copies — don't delete them. The picker queues the
whole chain for you.

**Resets.** If a depot was reset the same version exists as two blobs, and the
extractor needs `--blobcrc` to know which you mean. The app fills this in.

Extraction doesn't consume the dats, so you need room for both at once.

## Running the extractor by hand

One trap: it strips **every** `:` from `--out`, including the drive letter, so an
absolute path silently becomes a relative one and it extracts nothing. Run it
inside the output folder with a relative name:

```bash
cd D:\steam2\extracted
D:\steam2\extractor\extract.exe "D:\steam2\blobs" "D:\steam2\dats" 852 10 --out 852_v10
```

Arguments: blobs dir, dats dir, depot, version. Options: `--out`, `--filter
<regex>`, `--blobcrc <crc>`, `--key <key>`. `extract.exe` is a win64 build; build
`src.zip` with xmake elsewhere.

## Files it writes

| Path | What |
|---|---|
| `.s2cache/` | cached listings and fetched depot names — safe to delete |
| `s2downloader.json` | folders, threads, qBittorrent settings, window size |
| `s2queue.json` | unfinished queue, restored next launch |
| `s2extracted.json` | what was extracted, when, and where |
| `s2downloader.log` | the log panes, kept after closing (rotates at 5 MB) |
| `depot_names.json` | optional, yours — overrides fetched names |
| `<out>/<depot> - <name>_v<version>/` | extracted files |

Mirrors do not all run the same directory index, and some publish rounded sizes
("3.5 KiB") rather than byte counts. Both layouts are read, and a rounded size is
only ever compared to the precision it was given in - the sha256 in every
filename is the real check. An index that cannot be read is reported as an
error rather than cached as an empty archive.

Expect the server to be slow — 5–25 s just to start answering. Timeouts are 90 s
with retries and keep-alive; listings are cached, and a failed refresh keeps the
cached copy rather than losing it.
