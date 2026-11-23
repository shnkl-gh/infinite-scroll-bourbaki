#!/usr/bin/env python3
"""Check chapters against their Lean certificates.

For every chapter NNNNN (chapters/<lang>/NNNNN.md, one file per language):
  1. theories/NNNNN.lean must exist and compile with Lean, with no `sorry`;
  2. every [[name]] reference in the chapter must name a theorem, def or
     class declared in that Lean file.

Usage: python3 tools/check.py [NNNNN ...]
"""

import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ELAN_LEAN = Path.home() / ".elan" / "bin" / "lean"
LEAN = shutil.which("lean") or (str(ELAN_LEAN) if ELAN_LEAN.is_file() else None)


def check(cid: str) -> list[str]:
    errors = []
    versions = sorted((ROOT / "chapters").glob(f"*/{cid}.md"))
    if not versions:
        return [f"{cid}: no chapter files"]
    theory = ROOT / "theories" / f"{cid}.lean"
    if not theory.exists():
        return [f"{cid}: missing {theory.relative_to(ROOT)}"]
    src = theory.read_text()
    if re.search(r"\b(?:sorry|admit)\b", src):
        errors.append(f"{cid}: theory contains a proof placeholder")
    if re.search(r"^\s*axiom\s+", src, re.M):
        errors.append(f"{cid}: theory adds an axiom declaration")
    res = subprocess.run([str(LEAN), str(theory)], capture_output=True, text=True, cwd=ROOT)
    if res.returncode != 0 or "error" in res.stdout:
        errors.append(f"{cid}: Lean failed:\n{res.stdout}{res.stderr}")
    declared = set(re.findall(r"^(?:theorem|def|class|lemma)\s+([\w']+)", src, re.M))
    refs = {}
    for chapter in versions:
        lang = chapter.parent.name
        refs[lang] = re.findall(r"\[\[([\w']+)\]\]", chapter.read_text())
        for name in sorted(set(refs[lang])):
            if name not in declared:
                errors.append(f"{cid} [{lang}]: [[{name}]] is not declared in the theory")
    if len({tuple(r) for r in refs.values()}) > 1:
        errors.append(f"{cid}: the language versions cite different Lean declarations")
    return errors


def main():
    if LEAN is None:
        print("Lean was not found. Install it with tools/install-lean.sh, then run this check again.")
        return 1
    ids = sys.argv[1:] or sorted({p.stem for p in (ROOT / "chapters").glob("*/*.md")})
    errors = [e for cid in ids for e in check(cid)]
    for e in errors:
        print(e)
    print(f"checked {len(ids)} chapter(s): {'OK' if not errors else f'{len(errors)} problem(s)'}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
