# Lane: pin-recount-shapes — the recount tool now covers every pinned-list shape

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for this pass`, pin-recount-shapes, 2026-08-29).**
`scripts/recount-pinned-inventory.py` recognized exactly one array shape and
answered "no pinned inventory array found" for the site whose merge it was run
against. Its counting engine is now shape-independent, verified against every
pinned array in the tree, and carries six new mutation-verified controls. The
survey below **re-measures**
[`docs/research/11-design-review/2026-08-29-the-pin-recount-tool-covers-one-of-four-shapes.md`](../../research/11-design-review/2026-08-29-the-pin-recount-tool-covers-one-of-four-shapes.md)
and corrects it in four places.

Commits: `ce173137b` (engine), `ed8335521` (controls), plus this file.

## What landed

**One engine, not four regexes.** The line-shape heuristic (`^        \("` /
`^        \($`) is gone. The tool now masks comments, string literals and char
literals, then splits each array literal on **top-level commas** with a
bracket-depth counter. That covers `[(&str, crate::NameId, &str); N]`,
`[crate::NameId; N]`, `[&str; N]`, `let`/`const`/`static` and function-return
positions, and multiple pinned arrays per file.

Masking is load-bearing twice, not cleanup. This repository's doc comments carry
deliberately unbalanced brackets (`[0,n)`, intra-doc links) that wreck a depth
counter; and `creal/inventory.rs`'s module docs **quote a pin declaration in
prose** to explain why that pin is gone, which an unmasked scan matches and then
fails on as "not terminated by `];`". The old control suite worked around that
with an anchored grep and noted the anchor "is also the right fix for the tool" —
masking is that fix and is strictly stronger (an anchored scan still matches an
indented `//!` code block).

**Verified, both directions.** All 72 pinned-array sites in the tree report
`declared == counted`, which agrees with the compiler (the tree builds, so every
pin is correct by construction) — so a tool that were wrong about any real shape
would show a false `PIN WRONG` here. That is not a vacuous pass: the pre-existing
`a_wrong_pin_exits_nonzero` control pins that the tool can say `PIN WRONG` at
all, and `every_wrong_pin_in_one_file_is_rewritten` pins that it rewrites the
right pin when a file has several.

**One diagnostic bug found and fixed.** `single`/`wrapped` were measured on the
source, so an entry preceded by a `//` block read as *wrapped*.
`int_prelude_tests.rs`'s `derived_lemmas` reported `wrapped=1` with nothing
wrapped in it. `wrapped` names the measured 210-vs-283 failure, so it must not
also fire for a comment; it is now measured on the masked text.

## Deliverable 1 — the re-measured survey

Detail moved to [`../notes/248-pin-recount-shapes.md`](../notes/248-pin-recount-shapes.md).

