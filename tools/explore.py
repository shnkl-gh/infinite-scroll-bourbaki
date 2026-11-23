#!/usr/bin/env python3
"""Explore a seed's small models, to guide the formal step.

Enumerates all models of sizes 1-3 (relations included). Prints:
  * the number of models and of isomorphism classes (relations ignored);
  * for each element definition: whether it holds everywhere, or nowhere
    beyond the trivial model, and the most elements it holds for in one model;
  * implications between element definitions that hold in every small model
    (conjectures only: prove them in Lean, or find a counterexample);
  * for each pair with no such implication, a small separating model, ready
    for a Lean `decide` example.

Results are evidence, never theorems. Only statements proved in Lean go into
a chapter.

Usage: python3 tools/explore.py 00003
"""

import itertools
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import seedgen as sg  # noqa: E402

KEYS = {"var", "e", "op", "phi", "eq", "rel", "pred", "not", "and", "imp", "forall", "exists"}


def to_syntax(x):
    """JSON lists back to the generator's tuple syntax."""
    if isinstance(x, list):
        if x and isinstance(x[0], str) and x[0] in KEYS:
            return tuple(to_syntax(y) for y in x)
        return [to_syntax(y) for y in x]
    return x


def canon(m):
    n, best = m.n, None
    for p in itertools.permutations(range(n)):
        inv = {p[i]: i for i in range(n)}
        key = (
            tuple(p[m.op[inv[a] * n + inv[b]]] for a in range(n) for b in range(n)),
            tuple(p[m.phi[inv[a]]] for a in range(n)) if m.phi else None,
            p[m.e] if m.e is not None else None,
        )
        best = key if best is None or key < best else best
    return best


def main():
    sid = sys.argv[1]
    d = json.loads((Path(__file__).resolve().parent.parent / "seeds" / f"{sid}.json").read_text())
    sg.MAX_EXAMPLES_PER_SIZE = 10**9
    axioms = [to_syntax(a["formula"]) for a in d["axioms"]]
    defs = {x["name"]: {"kind": x["kind"], "param": "a", "body": to_syntax(x["formula"])}
            for x in d["definitions"]}
    sig = set(d["signature"])
    models = [m for n in (1, 2, 3) for m in sg.find_models(sig, axioms, n, float("inf"))]
    for m in models:
        m.compute_defs(defs)
    print(f"{len(models)} models of size <= 3, "
          f"{len({(m.n, canon(m)) for m in models})} classes up to isomorphism (ignoring ρ)")
    el = [k for k in defs if defs[k]["kind"] == "element"]
    st = [k for k in defs if defs[k]["kind"] != "element"]
    for k in el:
        tags = []
        if all(all(m.preds[k]) for m in models):
            tags.append("holds for every element of every model")
        if not any(any(m.preds[k]) for m in models if m.n > 1):
            tags.append("holds for no element of any non-trivial model")
        tags.append(f"at most {max(sum(m.preds[k]) for m in models)} element(s) per model")
        print(f"{k}: " + "; ".join(tags))
    for k in st:
        vals = [m.preds[k] for m in models if m.n > 1]
        print(f"{k} (structure): " + ("always" if all(vals) else "never (n>1)" if not any(vals) else "varies"))
    for a, b in itertools.permutations(el, 2):
        sep = next(((m, i) for m in models for i in range(m.n)
                    if m.preds[a][i] and not m.preds[b][i]), None)
        if sep is None:
            print(f"conjecture: {a} => {b}")
        else:
            m, i = sep
            print(f"{a} does not imply {b}: size {m.n}, element {i}, {m.to_json()}")


if __name__ == "__main__":
    main()
