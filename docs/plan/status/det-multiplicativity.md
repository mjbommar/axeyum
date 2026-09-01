# Lane: det-multiplicativity

<!-- plan-section: lane-status -->

Status: **DID NOT CLOSE at symbolic `n`.** Five theorems landed axiom-free;
the remaining obligation is written out as two rendered types in
[ADR-1440](../../research/09-decisions/adr-1440-multiplicativity-needs-a-selection-lemma-not-a-leibniz-agreement.md).

Base: merged local `main` at `3be794a8e` (origin/main lagged at `46bc65cc4`).

## Landed

All in `crates/axeyum-lean-kernel/src/rat_prelude/matrix_det.rs`, all
`Declaration::Theorem`, all `Kernel::axiom_footprint` empty.

| declaration | what it says |
| --- | --- |
| `Rat.det_row_replaced` | expanding along row `t` sees the rest of the matrix only through `A`'s minors |
| `Rat.det_row_zero` | a zero row kills the determinant |
| `Rat.det_row_smul` | scaling a row scales the determinant |
| `Rat.det_row_multilinear` | row `t` as a `sumRange` of `n` coefficient rows splits into a `sumRange` of `n` cofactor sums |
| `Rat.det_matMul_2` | `det (matMul A B 2) 2 = det A 2 * det B 2`, symbolic in both matrices |

The first four are **row multilinearity at symbolic dimension**, the
prerequisite ADR-1310 lists first for step 4 and which nothing in this prelude
supplied. What existed was `row_add_split`: a private two-term additivity
phrased in the private `rset_row`/`wrapped_matrix` builders, with
`det_row_swap` as its only consumer.

`det_matMul_2` is cheap only because `Rat.det2_mul` (the eight-variable ring
identity) predates `Rat.det`, and because `2` is a literal so `Rat.sumRange`
iota-reduces. `n = 3` is not done — no `det3_mul`, eighteen variables.

## Sizing findings, against the three steps below this one

- **No new induction**, matching `det_row_swap` and unlike `det_alternating`:
  `Rat.det_row_expansion` is already dimension-general, so all four are
  straight-line at a symbolic `m`.
- **`Rat.det_congr` WAS needed** — once, inside `det_row_replaced`; the other
  three reach it through that one. Third data point: `det_alternating` needed
  none, `det_row_swap` needed two. The rule is not per-theorem — `det_congr` is
  needed exactly when a step relates a minor to a matrix named elsewhere.
- **The hard part was not the mathematics.** Reading the existing file for the
  idioms took longer than writing any proof. Notably `Rat.det2_mul` already
  existed and was found only by grepping the prelude's name list for `det2`,
  which turned the `n = 2` case from a feared 400-line ring computation into
  about 120 lines of index bookkeeping.

## What is left

Two statements, both written as rendered types in ADR-1440:

1. **The expansion.** `det (matMul A B n) n = sumMaps n n (fun g => prodRange
   (fun i => A i (g i)) n * det (B∘g) n)` — `det_row_multilinear` applied once
   per row, over hybrid matrices, plus a `Rat.prodRange`/`Rat.sumMaps` port
   (both measured ABSENT; the `Int` versions exist).
2. **The selection lemma.** `det (B∘g) n = det (matId∘g) n * det B n` — where
   the difficulty actually is.

ADR-1440's substantive correction to ADR-1310: taking
`sgnOrZero g n := det (matId∘g) n` makes the sign a DEFINITION, so
"`leibniz` agrees with `det`" — the theorem ADR-1310 flagged as separate and
hard — becomes the `B := matId` instance of (1) and stops being a task. (2)
is a different statement and is the real one.

**Do (2) first.** (1) is long but every ingredient is in the tree; (2) needs a
new combinatorial argument, and if it does not close then (1) buys nothing.

## Gate

`cargo test -p axeyum-lean-kernel --lib rat_prelude::` — **156 passed, 0
failed**, 241.87 s, run twice (once before `det_matMul_2`, once after). The
workspace gate and `clippy` were NOT run by this lane; `cargo check -p
axeyum-lean-kernel --lib` is clean and `rustfmt --edition 2024` was applied to
every touched file.
