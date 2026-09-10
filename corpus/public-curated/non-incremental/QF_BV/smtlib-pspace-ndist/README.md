# SMT-LIB `QF_BV/pspace` `ndist.b` slice (committed)

Twenty-one satisfiable `QF_BV` benchmarks vendored from the SMT-LIB 2024
non-incremental release, division `QF_BV`, family `pspace/`. Names flatten the
original path (`/` -> `__`) in the same style as the sibling
`quantified/UF/smtlib-sledgehammer-clean/` directory.

Provenance, from the files' own `:source`: *"We give a counter-example for
(x + 1 <= y) -> (x < y). Contributed by Andreas Froehlich, Gergely Kovasznai,
Armin Biere, Institute for Formal Models and Verification, JKU, Linz, 2013.
source: http://fmv.jku.at/smtbench and 'Efficiently Solving Bit-Vector Problems
Using Model Checkers' by Andreas Froehlich, Gergely Kovasznai, Armin Biere. In
Proc. 11th Intl. Workshop on Satisfiability Modulo Theories (SMT'13), pages
6-15, aff. to SAT'13, Helsinki, Finland, 2013."*

Every file carries `(set-info :status sat)`.

## Selection criteria

The whole `ndist.b` sub-family, taken without exception: it is exactly the
`pspace/` members annotated `:status sat` (`ndist.a` is the `unsat` twin, and
`power2sum` and `shift1add` are `unsat` throughout). Selecting the whole
sub-family rather than a hand-picked subset means the vendored set cannot be
tuned to a verdict.

Reproduce with:

```sh
D=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/QF_BV/pspace
for f in "$D"/ndist.b.*.smt2; do
  b=$(basename "$f" .smt2)
  cp "$f" "corpus/public-curated/non-incremental/QF_BV/smtlib-pspace-ndist/smtlib__QF_BV__pspace__${b}.smt2"
done
```

## Why these are committed rather than read from the NAS corpus

Roadmap item 3.9
([`docs/solver-comparison-2026-09/11-roadmap-and-plan.md`](../../../../../docs/solver-comparison-2026-09/11-roadmap-and-plan.md)):
our bit-blasting path — the path we actually ship — misses 43 of 166 real
satisfiable SMT-LIB `QF_BV` instances at a 10 s budget, and **the committed
corpus structurally cannot see it**. Its largest satisfiable `QF_BV` file is
1,368 bytes, its median instance lowers to zero AND gates, and 36,471 of
SMT-LIB's 46,191 `QF_BV` files are larger than its largest.

This family is the cheapest possible witness to that class. Each file is
**745 bytes** and its term DAG is **six nodes**:

```smt2
(declare-fun x () (_ BitVec 24491))
(declare-fun y () (_ BitVec 24491))
(assert (bvuge x y))
(assert (bvule (bvadd x (_ bv1 24491)) y))
```

so it costs 88 KB to commit the whole family, and nothing about it is large
except the **bit width**. That is the point: it separates "the instance is big"
from "the instance is wide", and no word-level rewrite rule touches it
(measured in
[`rewrite-depth-gap-2026-09-10.md`](../../../../../docs/research/03-measurements/rewrite-depth-gap-2026-09-10.md)).

## What gates them, and what does not

`corpus/regression/`'s sweep would pin **nothing** here. That gate is a
soundness gate by construction: it *skips* `unknown`, so a file that regresses
from `sat` to `unknown` is counted as a coverage gap and the suite stays green.
Dropping these files there would look like coverage and gate nothing.

These files currently return `unknown`, so a test asserting `sat` on them would
be red today. What pins them instead is a **decide-frontier ratchet** over the
width-graduated sibling corpus,
[`corpus/public-curated/synthetic/QF_BV/width-graduated/`](../../../synthetic/QF_BV/width-graduated/),
which emits the identical shape across a ladder of widths so the measurement is
"the largest width we decide" — a number that can only move one way. The
ratchet, its floor, and its non-vacuity controls live in
[`crates/axeyum-solver/tests/qfbv_width_frontier.rs`](../../../../../crates/axeyum-solver/tests/qfbv_width_frontier.rs).

The files here are the ratchet's **upper anchor**: a companion assertion checks
that every one of them still carries `:status sat` and that none of them is ever
answered `unsat`. A wrong verdict on a satisfiable instance fails loudly; a
miss is counted, not ignored.

## Measurement

[`docs/research/03-measurements/why-43-satisfiable-qfbv-miss-2026-09-10.md`](../../../../../docs/research/03-measurements/why-43-satisfiable-qfbv-miss-2026-09-10.md).
