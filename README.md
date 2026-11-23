# Infinite Scroll Bourbaki

Python chooses a signature for a first order theory at random. It generates
axioms in that signature and keeps them only if it finds a model with two or
three elements.

Python builds definitions by putting quantifiers on randomly generated
equations or relations. A new definition can use an earlier one. Python
looks for counterexamples to implications between the definitions in small
models. Vampire, an optional theorem prover, can prove some consequences of
the axioms.

Claude chooses which results to pursue, writes their proofs in Lean, and
writes and reviews the English and French chapters. Lean checks the formal
proofs.

[Watch the prerecorded replay](https://www.ms.u-tokyo.ac.jp/~kelly/infinite-scroll-bourbaki/index.html).
Seven chapters, about 30 minutes per loop.

For new chapters, fork the repository on GitHub. Sign in to
[Claude Code](https://code.claude.com/docs/en/setup) on your computer and paste
this, with the link to your fork:

> Follow the README at [link to your fork]. Set up the project, start the
> live viewer, and generate a chapter. Give me the link to open.

<details>
<summary>Setup and generation workflow for Claude Code</summary>

Clone the fork and work from its root. The project needs Python 3.9 or later
and Lean 4.35.0 via elan. If elan is missing, use `tools/install-lean.sh`.
Run `lean --version` in the clone to load the pinned toolchain. Serve the
viewer with `python3 -m http.server 8000 --bind 127.0.0.1 --directory site`.
The browser address is `http://127.0.0.1:8000/?live`.

Generate one seed with `python3 tools/seedgen.py`. Explore it with
`python3 tools/explore.py NNNNN`, substituting the new seed ID. Copy
`seeds/NNNNN.lean` to `theories/NNNNN.lean` and develop the results in core
Lean without proof placeholders or extra axioms. Optionally use
`python3 tools/deep.py NNNNN` if Vampire is available.

Write `chapters/en/NNNNN.md` and `chapters/fr/NNNNN.md`. Match the block
structure and `[[name]]` declaration references across the two versions.
Use `@N` for chapter numbers and `@S` for species subscripts, as in the
existing chapters.

Before release, compare each prose claim and argument with the Lean source.
Try to settle each question in the draft from the axioms and existing lemmas.
For existence questions, try to construct a model and look for an argument
forcing the structure to collapse. Formalize any answer you find in Lean and
revise both versions. Keep a local note of any question you leave out
because this pass could not settle it. If a mistake reaches the viewer,
use it as a test case for the generation and review procedure.

Run `python3 tools/check.py` to compile the theories and verify the
declaration references. Publish the chapter to the local viewer with
`python3 tools/build_site.py --live`. The viewer checks for new
chapters every five seconds.

</details>
