#!/usr/bin/env python3
"""Hunt for deep consequences of a seed's axioms.

1. Generate random candidate laws over the seed's signature (universally
   quantified equations, and relation atoms when ρ is present).
2. Keep only those that hold in every model of size <= 3 (necessary, not
   sufficient).
3. Ask Vampire to prove each survivor from the axioms, and measure the
   proof: the number of inference steps.
4. Print the candidates ranked by proof length, and save each proof to
   work/deep/<seed>/<n>.proof for the formal step.

Only results that are proved, and then checked in Lean, go into a chapter.

Usage: python3 tools/deep.py 00007 [--candidates 3000] [--prove 80] [--time 3]
"""

import argparse
import json
import random
import re
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import explore  # noqa: E402
import seedgen as sg  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent


# --- TPTP --------------------------------------------------------------------

def tptp_term(t):
    k = t[0]
    if k == "var":
        return t[1].upper()
    if k == "e":
        return "e0"
    if k == "op":
        return f"f({tptp_term(t[1])},{tptp_term(t[2])})"
    return f"g({tptp_term(t[1])})"


def tptp_formula(f):
    k = f[0]
    if k == "eq":
        return f"{tptp_term(f[1])} = {tptp_term(f[2])}"
    if k == "rel":
        return f"r({tptp_term(f[1])},{tptp_term(f[2])})"
    if k == "pred":
        return f"{f[1]}({tptp_term(f[2])})"
    if k == "not":
        return f"~ ({tptp_formula(f[1])})"
    if k == "and":
        return f"({tptp_formula(f[1])} & {tptp_formula(f[2])})"
    if k == "imp":
        return f"({tptp_formula(f[1])} => {tptp_formula(f[2])})"
    q = "!" if k == "forall" else "?"
    return f"({q}[{','.join(v.upper() for v in f[1])}] : {tptp_formula(f[2])})"


def tptp_problem(axioms, conjecture):
    lines = [f"fof(ax{i}, axiom, {tptp_formula(a)})." for i, a in enumerate(axioms, 1)]
    lines.append(f"fof(goal, conjecture, {tptp_formula(conjecture)}).")
    return "\n".join(lines) + "\n"


def prove(vampire, axioms, conjecture, seconds):
    """Return Vampire's proof text, or None."""
    res = subprocess.run(
        [vampire, "--mode", "vampire", "-t", str(seconds), "--proof", "on"],
        input=tptp_problem(axioms, conjecture), capture_output=True, text=True,
    )
    out = res.stdout
    if "Refutation found" not in out:
        return None
    return out


INFERENCE = re.compile(r"^\d+\. .*\[(\w[\w ]*?)(?: \d+(?:,\d+)*)?\]\s*$", re.M)
NON_STEPS = {"input", "negated conjecture", "flattening", "ennf transformation",
             "rectify", "skolemisation", "skolemize", "cnf transformation", "nnf transformation",
             "pure predicate removal", "true and false elimination", "definition unfolding",
             "avatar component clause", "avatar split clause", "avatar sat refutation",
             "avatar contradiction clause"}


def proof_steps(proof):
    return sum(1 for m in INFERENCE.finditer(proof) if m.group(1) not in NON_STEPS)


# --- candidates --------------------------------------------------------------

def candidates(sig, n, rng):
    g = sg.Gen(rng)
    g.sig = set(sig)
    seen = set()
    for _ in range(n * 20):
        if len(seen) >= n:
            break
        nv = rng.choice([1, 2, 2, 3])
        vars_ = ["x", "y", "z"][:nv]
        at = g.atom(vars_, need=vars_, depth=rng.choice([2, 3]))
        if at is None:
            continue
        c = ("forall", vars_, at)
        if repr(c) not in seen:
            seen.add(repr(c))
            yield c


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("seed")
    ap.add_argument("--candidates", type=int, default=3000)
    ap.add_argument("--prove", type=int, default=80)
    ap.add_argument("--time", type=int, default=3)
    ap.add_argument("--rng", type=int, default=0)
    ap.add_argument("--seed-dir", default=str(ROOT / "seeds"))
    ap.add_argument("--vampire", help="path to the Vampire executable")
    args = ap.parse_args()
    vampire = args.vampire or shutil.which("vampire")
    if not vampire:
        ap.error("install Vampire on PATH or specify --vampire")

    d = json.loads((Path(args.seed_dir) / f"{args.seed}.json").read_text())
    axioms = [explore.to_syntax(a["formula"]) for a in d["axioms"]]
    sig = set(d["signature"])
    sg.MAX_EXAMPLES_PER_SIZE = 10**9
    models = [m for n in (1, 2, 3) for m in sg.find_models(sig, axioms, n, float("inf"))]
    ax_reprs = {repr(a) for a in axioms}

    rng = random.Random(args.rng)
    survivors = []
    for c in candidates(sig, args.candidates, rng):
        if repr(c) in ax_reprs:
            continue
        if all(m.holds(c, {}) for m in models):
            survivors.append(c)
    print(f"{len(models)} small models; {len(survivors)} candidates survive the model filter")

    # Prefer shorter statements: Bourbaki states laws one can read.
    survivors.sort(key=lambda c: sg.term_size(c[2][1]) + sg.term_size(c[2][2]))
    out_dir = ROOT / "work" / "deep" / args.seed
    out_dir.mkdir(parents=True, exist_ok=True)
    results = []
    for c in survivors[: args.prove]:
        p = prove(vampire, axioms, c, args.time)
        if p is not None:
            results.append((proof_steps(p), c, p))
    results.sort(key=lambda r: -r[0])
    summary = []
    for i, (steps, c, p) in enumerate(results, 1):
        (out_dir / f"{i:03d}.proof").write_text(f"% {sg.human_formula(c)}\n{p}")
        summary.append({"n": i, "steps": steps, "human": sg.human_formula(c), "formula": c})
    (out_dir / "summary.json").write_text(json.dumps(summary, ensure_ascii=False, indent=1))
    print(f"{len(results)} proved (of {min(len(survivors), args.prove)} tried). Longest proofs:")
    for s in summary[:15]:
        print(f"  {s['steps']:4d} steps  #{s['n']:03d}  {s['human']}")


if __name__ == "__main__":
    main()
