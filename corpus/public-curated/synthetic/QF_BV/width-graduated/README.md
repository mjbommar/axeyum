# Width-graduated satisfiable QF_BV (generated, status by construction)

Twenty-nine committed `QF_BV` benchmarks in two families, each family the same
formula shape emitted across a ladder of **bit widths**. Generated
deterministically by
[`scripts/gen-graduated-qfbv-width.py`](../../../../../scripts/gen-graduated-qfbv-width.py):

```sh
python3 scripts/gen-graduated-qfbv-width.py
```

This directory follows the model of the sibling
[`synthetic/QF_NRA`, `synthetic/QF_NIA`](../../README.md) graduated corpus: a
difficulty **knob** per family, a status established **by construction**, and a
measurement reported as a **DECIDE-FRONTIER** — the largest knob decided —
rather than a pass/fail count.

## Why this exists

Roadmap item 3.9
([`docs/solver-comparison-2026-09/11-roadmap-and-plan.md`](../../../../../docs/solver-comparison-2026-09/11-roadmap-and-plan.md)):
our bit-blasting path misses 43 of 166 real satisfiable SMT-LIB `QF_BV`
instances at a 10 s budget, and the committed corpus cannot see the class —
its largest satisfiable `QF_BV` file is 1,368 bytes and its median instance
lowers to zero AND gates.

The real SMT-LIB family that does show the class,
[`QF_BV/pspace/ndist.b.*`](../../../non-incremental/QF_BV/smtlib-pspace-ndist/),
is vendored beside this one. But it ships only widths **20,000-29,980** — 21
files that are all on the *same side* of our threshold. Vendoring it alone pins
a capability class and locates no frontier, and a frontier is what a ratchet
needs. These files supply the ladder that brackets it.

## Families and status provenance

| family | knob | files | shape | witness (checked before emission) |
|---|---|---:|---|---|
| `bvwide-addcmp-wNNNNN` | width 64 … 32768 | 15 | `(bvuge x y)` and `(bvule (bvadd x 1) y)` — verbatim `ndist.b` | `x = 2**w - 1` (all ones), `y = 0` |
| `bvwide-mul-wNNNNN` | width 8 … 4096 | 14 | `(= (bvmul x y) 15)` | `x = 3`, `y = 5` |

Both are `:status sat`. The generator evaluates the witness against every
assertion in exact Python integer arithmetic **before writing the file** and
aborts the run on a witness that does not satisfy it, so the status is a
checkable fact rather than an annotation inherited from a solver. A DISAGREE in
measurement is therefore a genuine bug — in us — not a mislabeled file.

`addcmp` is satisfied at every width by the same argument: `x >= y` holds, `x+1`
wraps to `0`, and `0 <= 0` holds. `mul` is satisfied at every width `>= 4`
because `3 * 5 = 15` does not overflow.

## Why two families rather than one

They have different **cost curves over the same knob**, which is what separates
"wide inputs are hard" from "one particular circuit is hard":

- `addcmp` lowers to a ripple-carry incrementer plus two unsigned comparators —
  gate count roughly **linear** in the width.
- `mul` lowers through `lower_mul_op`'s shift-and-add
  (`crates/axeyum-bv/src/lib.rs`), whose gate count is roughly **quadratic** in
  the width — the pre-lowering estimator in
  `crates/axeyum-solver/src/sat_bv_backend.rs` charges `bvmul` at `8w²`
  accordingly. Nothing constant-folds, because both operands are symbolic.

So the two families are expected to cross the wall at widths an order of
magnitude apart, and a change that moves only one of them is telling you which
part of the pipeline moved.

## What gates them

[`crates/axeyum-solver/tests/qfbv_width_frontier.rs`](../../../../../crates/axeyum-solver/tests/qfbv_width_frontier.rs)
— a decide-frontier ratchet per family, plus non-vacuity and soundness controls.
`corpus/regression/`'s sweep deliberately does **not** pin these: it skips
`unknown`, so a file regressing from `sat` to `unknown` reads there as a
coverage gap and the suite stays green.

## Measurement

[`docs/research/03-measurements/why-43-satisfiable-qfbv-miss-2026-09-10.md`](../../../../../docs/research/03-measurements/why-43-satisfiable-qfbv-miss-2026-09-10.md).
