#!/usr/bin/env python3
"""Bundle chapters/<lang>/*.md into site/stream.json for the replay site.

Each chapter is parsed into blocks (headings and paragraphs). Each block is a
list of units: text runs, inline math, display math and Lean markers. Every
unit has a typing cost, and the site replays the sequence on a shared clock.

The language versions of a chapter must be block-parallel (same number and
kind of blocks). Each block gets one duration on the shared timeline, the
maximum of its costs over languages, so switching language keeps the viewer
at the same place.

Usage: python3 tools/build_site.py [--rate CHARS_PER_SEC] [--epoch UNIX_MS]
"""

import argparse
import json
import re
import time
from tempfile import NamedTemporaryFile
from datetime import datetime, timezone
from pathlib import Path

import check

ROOT = Path(__file__).resolve().parent.parent

# The stream's notional start, when no previous stream.json exists: the day the
# project began. Chapter numbers count up from here.
PROJECT_START_MS = int(datetime(2026, 11, 6, tzinfo=timezone.utc).timestamp() * 1000)

# --- shared clock (must match site/app.js exactly) ---------------------------
M32 = 0xFFFFFFFF


def imul(a, b):
    return ((a & M32) * (b & M32)) & M32


def mulberry32(a):
    a &= M32

    def rnd():
        nonlocal a
        a = (a + 0x6D2B79F5) & M32
        t = imul(a ^ (a >> 15), 1 | a)
        t = ((t + imul(t ^ (t >> 7), 61 | t)) & M32) ^ t
        return ((t ^ (t >> 14)) & M32) / 4294967296

    return rnd


def raw_perm(pss, k):
    rnd = mulberry32((imul(pss, 0x9E3779B1) + 12345) & M32)
    arr = list(range(k))
    for i in range(k - 1, 0, -1):
        j = int(rnd() * (i + 1))
        arr[i], arr[j] = arr[j], arr[i]
    return arr


def perm(pss, k):
    """Chapter order for pass `pss`; never repeats a chapter across a boundary."""
    arr = raw_perm(pss, k)
    if pss > 0 and k > 2 and arr[0] == raw_perm(pss - 1, k)[-1]:
        arr[0], arr[1] = arr[1], arr[0]
    return arr


def chapter_number_at(data, now_ms):
    """Number of the chapter being typed at time now_ms."""
    costs = [sum(b["c"] for b in c["blocks"]) for c in data["chapters"]]
    total = sum(costs)
    p = max(0, int((now_ms - data["epoch"]) / 1000 * data["rate"]))
    pss, q = divmod(p, total)
    for idx, ci in enumerate(perm(pss, len(costs))):
        if q < costs[ci]:
            return data["base"] + pss * len(costs) + idx
        q -= costs[ci]
    return data["base"] + (pss + 1) * len(costs)
TOKEN = re.compile(r"\$\$(.+?)\$\$|\$(.+?)\$|\[\[([\w']+)\]\]|\*")


def parse_inline(text: str):
    units, italic, pos = [], False, 0
    for m in TOKEN.finditer(text):
        if m.start() > pos:
            units.append({"t": "text", "s": text[pos:m.start()], "it": italic})
        if m.group(1) is not None:
            units.append({"t": "display", "tex": m.group(1).strip()})
        elif m.group(2) is not None:
            units.append({"t": "math", "tex": m.group(2), "it": italic})
        elif m.group(3) is not None:
            units.append({"t": "lean", "name": m.group(3)})
        else:
            italic = not italic
        pos = m.end()
    if pos < len(text):
        units.append({"t": "text", "s": text[pos:], "it": italic})
    for u in units:
        if u["t"] == "text":
            u["c"] = len(u["s"])
        elif u["t"] in ("math", "display"):
            u["c"] = max(2, len(u["tex"]) // 4)
        else:
            u["c"] = 1
    return units


def parse_chapter(path: Path):
    blocks, para = [], []

    def flush():
        if para:
            blocks.append({"k": "p", "u": parse_inline(" ".join(para))})
            para.clear()

    for line in path.read_text().splitlines():
        s = line.strip()
        h = re.match(r"^(#{1,3}) (.*)$", s)
        if h:
            flush()
            blocks.append({"k": f"h{len(h.group(1))}", "u": parse_inline(h.group(2))})
        elif not s:
            flush()
        else:
            para.append(s)
    flush()
    return blocks


def lean_source(cid: str):
    source = (ROOT / "theories" / f"{cid}.lean").read_text()
    declarations = {
        match.group(1): source.count("\n", 0, match.start()) + 1
        for match in re.finditer(r"^(?:theorem|def|class|lemma)\s+([\w']+)", source, re.M)
    }
    return {"source": source, "lines": declarations}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rate", type=float, default=12.0, help="characters per second")
    ap.add_argument("--epoch", type=int, help="stream start, unix ms (default: keep or now)")
    ap.add_argument("--live", action="store_true", help="publish the latest chapter to the live viewer")
    args = ap.parse_args()
    if args.rate <= 0:
        ap.error("--rate must be positive")
    out = ROOT / "site" / ("live.json" if args.live else "stream.json")
    old = json.loads(out.read_text()) if not args.live and out.exists() else {}
    now = int(time.time() * 1000)
    if args.epoch:
        epoch, base = args.epoch, 1
    elif "base" in old:
        # Continue the numbering: restart the clock now, at the next chapter.
        epoch, base = now, chapter_number_at(old, now) + 1
    else:
        epoch, base = PROJECT_START_MS, 1
    langs = sorted(d.name for d in (ROOT / "chapters").iterdir() if d.is_dir())
    ids = sorted({p.stem for p in (ROOT / "chapters").glob("*/*.md")})
    if not ids:
        raise SystemExit("No chapters to publish")
    if args.live:
        ids = ids[-1:]
        errors = check.check(ids[0])
        if errors:
            raise SystemExit("\n".join(errors))
        epoch = now
        base = int(ids[0])
    chapters = []
    for cid in ids:
        versions = {lang: parse_chapter(ROOT / "chapters" / lang / f"{cid}.md") for lang in langs}
        kinds = {lang: [b["k"] for b in bl] for lang, bl in versions.items()}
        if len({tuple(k) for k in kinds.values()}) != 1:
            raise SystemExit(f"chapter {cid}: language versions are not block-parallel: "
                             + ", ".join(f"{l}={len(k)} blocks" for l, k in kinds.items()))
        blocks = []
        for i in range(len(kinds[langs[0]])):
            per = {lang: versions[lang][i]["u"] for lang in langs}
            cost = max(sum(u["c"] for u in us) for us in per.values())
            blocks.append({"k": versions[langs[0]][i]["k"], "c": cost, "u": per})
        chapters.append({"id": cid, "blocks": blocks, "lean": lean_source(cid)})
    data = {
        "epoch": epoch,
        "base": base,
        "rate": args.rate,
        "langs": langs,
        "repo": "https://github.com/shnkl-gh/infinite-scroll-bourbaki",
        "chapters": chapters,
    }
    with NamedTemporaryFile(mode="w", encoding="utf-8", dir=out.parent, delete=False) as tmp:
        tmp_path = Path(tmp.name)
        try:
            json.dump(data, tmp, ensure_ascii=False, separators=(",", ":"))
            tmp.close()
            tmp_path.chmod(0o644)
            tmp_path.replace(out)
        finally:
            tmp_path.unlink(missing_ok=True)
    total = sum(b["c"] for c in chapters for b in c["blocks"])
    print(f"site/{out.name}: {len(chapters)} chapter(s), {total} units of typing, "
          f"{total / args.rate / 60:.1f} min per pass at {args.rate} chars/s; "
          f"chapter now being typed: {chapter_number_at(data, now)}")


if __name__ == "__main__":
    main()
