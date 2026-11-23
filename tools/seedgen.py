#!/usr/bin/env python3
"""Seed generator for infinite-scroll-bourbaki.

A seed is a random theory:
  * a signature: a carrier E with a binary operation ⋆, and optionally a
    unary map φ, a distinguished element e and a binary relation ρ;
  * random axioms over that signature;
  * random definitions, each built on the vocabulary before it.

To keep seeds non-degenerate, the generator searches exhaustively for models
of size 2 and 3. It rejects a theory with no such model, i.e. one whose only
models are trivial or too large to find this way. The models it finds are
written out as examples, together with which definitions they satisfy.

Output for seed N:
  seeds/N.json  machine-readable seed: formulas, human strings, examples
  seeds/N.lean  Lean 4 skeleton (core Lean only). It states the theory and
                certifies each example model with `decide`.
The formal step (plan step 3) adds theorems and proofs on top of the skeleton.

Usage:
  python3 tools/seedgen.py               # next free seed id, random rng seed
  python3 tools/seedgen.py --rng 1234    # reproducible
  python3 tools/seedgen.py --count 5
"""

from __future__ import annotations

import argparse
import itertools
import json
import random
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SEED_DIR = ROOT / "seeds"

MODEL_SIZES = (2, 3)
MAX_EXAMPLES_PER_SIZE = 3
SEARCH_TIME_LIMIT = 20.0  # seconds per theory

# ---------------------------------------------------------------------------
# Syntax
#
# Terms:    ("var", name) | ("e",) | ("op", t, u) | ("phi", t)
# Formulas: ("eq", t, u) | ("rel", t, u) | ("pred", name, t)
#           | ("not", f) | ("and", f, g) | ("imp", f, g)
#           | ("forall", [vars], f) | ("exists", [vars], f)
# ---------------------------------------------------------------------------


def term_symbols(t) -> set[str]:
    k = t[0]
    if k == "var":
        return set()
    if k == "e":
        return {"e"}
    if k == "op":
        return {"op"} | term_symbols(t[1]) | term_symbols(t[2])
    if k == "phi":
        return {"phi"} | term_symbols(t[1])
    raise ValueError(t)


def formula_symbols(f, defs: dict) -> set[str]:
    k = f[0]
    if k == "eq":
        return term_symbols(f[1]) | term_symbols(f[2])
    if k == "rel":
        return {"rel"} | term_symbols(f[1]) | term_symbols(f[2])
    if k == "pred":
        return defs[f[1]]["symbols"] | term_symbols(f[2])
    if k == "not":
        return formula_symbols(f[1], defs)
    if k in ("and", "imp"):
        return formula_symbols(f[1], defs) | formula_symbols(f[2], defs)
    if k in ("forall", "exists"):
        return formula_symbols(f[2], defs)
    raise ValueError(f)


def term_vars(t) -> set[str]:
    k = t[0]
    if k == "var":
        return {t[1]}
    if k == "e":
        return set()
    if k == "op":
        return term_vars(t[1]) | term_vars(t[2])
    return term_vars(t[1])


def term_size(t) -> int:
    k = t[0]
    if k in ("var", "e"):
        return 1
    if k == "op":
        return 1 + term_size(t[1]) + term_size(t[2])
    return 1 + term_size(t[1])


# --- rendering --------------------------------------------------------------


def human_term(t, top=True) -> str:
    k = t[0]
    if k == "var":
        return t[1]
    if k == "e":
        return "e"
    if k == "phi":
        return f"φ({human_term(t[1])})"
    s = f"{human_term(t[1], False)} ⋆ {human_term(t[2], False)}"
    return s if top else f"({s})"


def human_formula(f, top=True) -> str:
    k = f[0]
    if k == "eq":
        return f"{human_term(f[1])} = {human_term(f[2])}"
    if k == "rel":
        return f"{human_term(f[1])} ρ {human_term(f[2])}"
    if k == "pred":
        return f"{f[1]}({human_term(f[2])})"
    if k == "not":
        return f"¬({human_formula(f[1])})"
    if k == "and":
        s = f"{human_formula(f[1], False)} ∧ {human_formula(f[2], False)}"
    elif k == "imp":
        s = f"{human_formula(f[1], False)} ⇒ {human_formula(f[2], False)}"
    else:
        q = "∀" if k == "forall" else "∃"
        s = f"{q} {' '.join(f[1])}, {human_formula(f[2])}"
    return s if top else f"({s})"


def lean_term(t, top=True, infix=True) -> str:
    """Lean syntax. Inside the class declaration the ⋆ notation does not exist
    yet, so axioms there are rendered with `infix=False` (prefix `op`)."""
    k = t[0]
    if k == "var":
        return t[1]
    if k == "e":
        return "e"
    if k == "phi":
        s = f"φ {lean_term(t[1], False, infix)}"
    elif infix:
        s = f"{lean_term(t[1], False, infix)} ⋆ {lean_term(t[2], False, infix)}"
    else:
        s = f"op {lean_term(t[1], False, infix)} {lean_term(t[2], False, infix)}"
    return s if top else f"({s})"


def lean_formula(f, top=True, infix=True) -> str:
    k = f[0]
    lt = lambda t, tp=True: lean_term(t, tp, infix)  # noqa: E731
    lf = lambda g, tp=True: lean_formula(g, tp, infix)  # noqa: E731
    if k == "eq":
        return f"{lt(f[1])} = {lt(f[2])}"
    if k == "rel":
        return f"ρ {lt(f[1], False)} {lt(f[2], False)}"
    if k == "pred":
        return f"{f[1]} {lt(f[2], False)}"
    if k == "not":
        return f"¬{lf(f[1], False)}"
    if k == "and":
        s = f"{lf(f[1], False)} ∧ {lf(f[2], False)}"
    elif k == "imp":
        s = f"{lf(f[1], False)} → {lf(f[2], False)}"
    else:
        q = "∀" if k == "forall" else "∃"
        s = f"{q} {' '.join(f[1])} : E, {lf(f[2])}"
    return s if top else f"({s})"


# --- evaluation in a finite model -------------------------------------------


class Model:
    def __init__(self, n, op=None, phi=None, e=None, rel=None):
        self.n = n
        self.op = op  # tuple, length n*n
        self.phi = phi  # tuple, length n
        self.e = e  # int
        self.rel = rel  # tuple of 0/1, length n*n
        self.preds: dict[str, tuple] = {}  # element predicates, computed

    def term(self, t, env):
        k = t[0]
        if k == "var":
            return env[t[1]]
        if k == "e":
            return self.e
        if k == "op":
            return self.op[self.term(t[1], env) * self.n + self.term(t[2], env)]
        return self.phi[self.term(t[1], env)]

    def holds(self, f, env) -> bool:
        k = f[0]
        if k == "eq":
            return self.term(f[1], env) == self.term(f[2], env)
        if k == "rel":
            return self.rel[self.term(f[1], env) * self.n + self.term(f[2], env)] == 1
        if k == "pred":
            return self.preds[f[1]][self.term(f[2], env)]
        if k == "not":
            return not self.holds(f[1], env)
        if k == "and":
            return self.holds(f[1], env) and self.holds(f[2], env)
        if k == "imp":
            return (not self.holds(f[1], env)) or self.holds(f[2], env)
        vs, body = f[1], f[2]
        rng = range(self.n)
        if k == "forall":
            return all(
                self.holds(body, {**env, **dict(zip(vs, vals))})
                for vals in itertools.product(rng, repeat=len(vs))
            )
        return any(
            self.holds(body, {**env, **dict(zip(vs, vals))})
            for vals in itertools.product(rng, repeat=len(vs))
        )

    def compute_defs(self, defs: dict):
        for name, d in defs.items():
            if d["kind"] == "element":
                a = d["param"]
                self.preds[name] = tuple(
                    self.holds(d["body"], {a: i}) for i in range(self.n)
                )
            else:
                self.preds[name] = self.holds(d["body"], {})

    def to_json(self):
        out = {"size": self.n, "op": list(self.op)}
        if self.phi is not None:
            out["phi"] = list(self.phi)
        if self.e is not None:
            out["e"] = self.e
        if self.rel is not None:
            out["rel"] = list(self.rel)
        return out


# --- random generation ------------------------------------------------------


class Gen:
    def __init__(self, rng: random.Random):
        self.r = rng
        self.sig = {"op"}
        if rng.random() < 0.4:
            self.sig.add("phi")
        if rng.random() < 0.3:
            self.sig.add("e")
        if rng.random() < 0.3:
            self.sig.add("rel")

    def term(self, vars_, depth):
        r = self.r
        leaves = [("var", v) for v in vars_]
        if "e" in self.sig and r.random() < 0.15:
            leaves.append(("e",))
        if depth == 0 or r.random() < 0.3:
            return r.choice(leaves)
        if "phi" in self.sig and r.random() < 0.25:
            return ("phi", self.term(vars_, depth - 1))
        return ("op", self.term(vars_, depth - 1), self.term(vars_, depth - 1))

    def atom(self, vars_, need=(), depth=2):
        """Random atom over vars_ mentioning every variable in `need`."""
        for _ in range(200):
            if "rel" in self.sig and self.r.random() < 0.25:
                a = ("rel", self.term(vars_, depth - 1), self.term(vars_, depth - 1))
            else:
                a = ("eq", self.term(vars_, depth), self.term(vars_, depth))
            t, u = a[1], a[2]
            if t == u:
                continue
            if a[0] == "eq" and term_size(t) + term_size(u) < 3:
                continue  # x = y, x = e, ...: forces triviality
            vs = term_vars(t) | term_vars(u)
            if not set(need) <= vs:
                continue
            return a
        return None

    def axiom(self):
        nv = self.r.choice([1, 2, 2, 3, 3])
        vars_ = ["x", "y", "z"][:nv]
        if self.r.random() < 0.2 and nv >= 2:
            hyp, concl = self.atom(vars_, depth=1), self.atom(vars_)
            if hyp is None or concl is None:
                return None
            body = ("imp", hyp, concl)
        else:
            body = self.atom(vars_, need=vars_)
            if body is None:
                return None
        return ("forall", vars_, body)

    def definition(self, name, defs):
        r = self.r
        elem_preds = [n for n, d in defs.items() if d["kind"] == "element"]
        choice = r.random()
        if choice < 0.2:
            body = self.atom(["x", "y"], need=["x", "y"])
            if body is None:
                return None
            return {"kind": "structure", "body": ("forall", ["x", "y"], body)}
        if elem_preds and choice < 0.55:
            q = r.choice(elem_preds)
            variant = r.randrange(3)
            if variant == 0:  # closure-type
                body = ("forall", ["x"], ("imp", ("pred", q, ("var", "x")),
                                          ("pred", q, ("op", ("var", "a"), ("var", "x")))))
            elif variant == 1:  # witnessed by an element of the earlier kind
                at = self.atom(["a", "x"], need=["a", "x"], depth=1)
                if at is None:
                    return None
                body = ("exists", ["x"], ("and", ("pred", q, ("var", "x")), at))
            else:  # refinement of the earlier notion
                at = self.atom(["a", "x"], need=["a", "x"], depth=1)
                if at is None:
                    return None
                body = ("and", ("pred", q, ("var", "a")), ("forall", ["x"], at))
            return {"kind": "element", "param": "a", "body": body}
        at = self.atom(["a", "x"], need=["a", "x"])
        if at is None:
            return None
        q = "forall" if r.random() < 0.65 else "exists"
        return {"kind": "element", "param": "a", "body": (q, ["x"], at)}


# --- model search -----------------------------------------------------------


def find_models(sig, axioms, n, deadline):
    """Exhaustive search for models of size n, pruning each axiom at the
    earliest level where all of its symbols are assigned."""
    levels = [s for s in ("op", "phi", "e", "rel") if s in sig]
    ax_syms = [(a, formula_symbols(a, {})) for a in axioms]
    check_at = {lvl: [] for lvl in levels}
    for a, syms in ax_syms:
        last = max((levels.index(s) for s in syms), default=0)
        check_at[levels[last]].append(a)

    domains = {
        "op": lambda: itertools.product(range(n), repeat=n * n),
        "phi": lambda: itertools.product(range(n), repeat=n),
        "e": lambda: iter(range(n)),
        "rel": lambda: itertools.product((0, 1), repeat=n * n),
    }
    found = []

    def rec(i, m):
        if time.monotonic() > deadline:
            raise TimeoutError
        if i == len(levels):
            found.append(Model(n, m.op, m.phi, m.e, m.rel))
            return len(found) >= MAX_EXAMPLES_PER_SIZE
        lvl = levels[i]
        for val in domains[lvl]():
            setattr(m, lvl, val)
            if all(m.holds(a, {}) for a in check_at[lvl]):
                if rec(i + 1, m):
                    return True
        setattr(m, lvl, None)
        return False

    rec(0, Model(n))
    return found


# --- seed assembly ----------------------------------------------------------


def make_seed(rng: random.Random):
    for _attempt in range(500):
        g = Gen(rng)
        axioms = [a for a in (g.axiom() for _ in range(rng.choice([1, 2, 2, 3]))) if a]
        if not axioms or len(set(map(repr, axioms))) < len(axioms):
            continue
        deadline = time.monotonic() + SEARCH_TIME_LIMIT
        try:
            models = []
            for n in MODEL_SIZES:
                models += find_models(g.sig, axioms, n, deadline)
        except TimeoutError:
            continue
        if not models:
            continue  # no non-trivial model of size <= 3: reject

        defs: dict = {}
        for i in range(rng.choice([3, 4, 5])):
            name = f"d{i + 1}"
            for _ in range(50):
                d = g.definition(name, defs)
                if d is None:
                    continue
                d["symbols"] = formula_symbols(d["body"], defs) | (
                    {"op"} if d["kind"] == "element" else set()
                )
                defs[name] = d
                break
        for m in models:
            m.compute_defs(defs)
        return g.sig, axioms, defs, models
    raise RuntimeError("could not generate a non-degenerate seed")


def lean_table(values, n):
    return f"tbl [{', '.join(map(str, values))}] {n} (by decide)"


def render_lean(seed_id, rng_seed, sig, axioms, defs, models) -> str:
    ns = f"Bourbaki.Seed{seed_id}"
    L = [
        f"/-! Seed {seed_id}. Generated by tools/seedgen.py (rng seed {rng_seed}).",
        "",
        "Skeleton only: the signature, axioms, definitions and certified example",
        "models. The formal step adds theorems and proofs below. -/",
        "",
        "set_option warn.classDefReducibility false",
        "",
        f"namespace {ns}",
        "",
        "/-- Look up entry `i` of a finite table, as an element of `Fin n`. -/",
        "def tbl (L : List Nat) (n : Nat) (h : 0 < n) (i : Nat) : Fin n :=",
        "  ⟨L.getD i 0 % n, Nat.mod_lt _ h⟩",
        "",
        "class Structure (E : Type) where",
        "  op : E → E → E",
    ]
    if "phi" in sig:
        L.append("  φ : E → E")
    if "e" in sig:
        L.append("  e : E")
    if "rel" in sig:
        L.append("  ρ : E → E → Prop")
    for i, a in enumerate(axioms, 1):
        L.append(f"  ax{i} : {lean_formula(a, infix=False)}")
    L += [
        "",
        "open Structure",
        "infixl:70 \" ⋆ \" => Structure.op",
        "",
        "section",
        "variable {E : Type} [Structure E]",
        "",
    ]
    for name, d in defs.items():
        if d["kind"] == "element":
            L.append(f"def {name} (a : E) : Prop := {lean_formula(d['body'])}")
        else:
            L.append(f"def {name} : Prop := {lean_formula(d['body'])}")
    L += ["", "end", ""]
    for j, m in enumerate(models, 1):
        n = m.n
        L.append(f"/-- Example {j}: a model of order {n}. -/")
        L.append(f"def ex{j} : Structure (Fin {n}) where")
        L.append(f"  op := fun a b => {lean_table(m.op, n)} ({n} * a.val + b.val)")
        if m.phi is not None:
            L.append(f"  φ := fun a => {lean_table(m.phi, n)} a.val")
        if m.e is not None:
            L.append(f"  e := {m.e}")
        if m.rel is not None:
            L.append(
                f"  ρ := fun a b => [{', '.join(map(str, m.rel))}].getD ({n} * a.val + b.val) 0 = 1"
            )
        for i in range(1, len(axioms) + 1):
            L.append(f"  ax{i} := by decide")
        L.append("")
    L += [f"end {ns}", ""]
    return "\n".join(L)


def to_json(seed_id, rng_seed, sig, axioms, defs, models):
    def hint(name, d):
        vals = [m.preds[name] for m in models]
        if d["kind"] == "element":
            flat = [v for t in vals for v in t]
        else:
            flat = vals
        if all(flat):
            return "true in every example found"
        if not any(flat):
            return "false in every example found"
        return "varies across the examples"

    return {
        "id": seed_id,
        "rng_seed": rng_seed,
        "generator": "tools/seedgen.py",
        "signature": sorted(sig),
        "axioms": [{"name": f"ax{i}", "formula": a, "human": human_formula(a)}
                   for i, a in enumerate(axioms, 1)],
        "definitions": [
            {
                "name": n,
                "kind": d["kind"],
                "formula": d["body"],
                "human": (f"{n}(a) :⇔ " if d["kind"] == "element" else f"{n} :⇔ ")
                + human_formula(d["body"]),
                "hint": hint(n, d),
            }
            for n, d in defs.items()
        ],
        "examples": [
            {**m.to_json(), "satisfies": {k: (list(v) if isinstance(v, tuple) else v)
                                          for k, v in m.preds.items()}}
            for m in models
        ],
        "notes": f"Exhaustive model search over sizes {list(MODEL_SIZES)}, "
                 f"at most {MAX_EXAMPLES_PER_SIZE} examples per size.",
    }


def next_id() -> str:
    SEED_DIR.mkdir(exist_ok=True)
    existing = [int(p.stem) for p in SEED_DIR.glob("*.json") if p.stem.isdigit()]
    return f"{(max(existing) + 1) if existing else 1:05d}"


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--rng", type=int, help="rng seed (default: random)")
    ap.add_argument("--count", type=int, default=1)
    args = ap.parse_args(argv)
    for k in range(args.count):
        rng_seed = (args.rng + k) if args.rng is not None else random.randrange(2**31)
        sig, axioms, defs, models = make_seed(random.Random(rng_seed))
        sid = next_id()
        (SEED_DIR / f"{sid}.json").write_text(
            json.dumps(to_json(sid, rng_seed, sig, axioms, defs, models),
                       ensure_ascii=False, indent=1) + "\n")
        (SEED_DIR / f"{sid}.lean").write_text(
            render_lean(sid, rng_seed, sig, axioms, defs, models))
        print(f"seeds/{sid}  (rng {rng_seed}): {len(axioms)} axioms, "
              f"{len(defs)} definitions, {len(models)} examples")


if __name__ == "__main__":
    sys.exit(main())
