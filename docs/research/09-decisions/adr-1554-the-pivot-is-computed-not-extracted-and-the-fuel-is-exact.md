# ADR-1554: Row-echelon form is a computed definition, the pivot search returns a `Nat` rather than eliminating an `Exists`, and the fuel is `cols` exactly

Status: accepted
Date: 2026-09-02
Index-summary: `Rat.rowEchelon` lands as a `Definition` the kernel REDUCES —
Gaussian elimination over ℚ at symbolic dimension, with the pivot index found
by a fuelled bounded search returning a `Nat`, never by eliminating an
`Exists`. Twenty-nine axiom-free declarations in `rat_prelude/echelon.rs`:
`Rat.isZeroB` (the decided zero test, `ble x 0 && ble 0 x`) with four bridge
theorems to the propositional `Eq x 0`; the three elementary row operations
`rowSwap`/`rowScale`/`rowAddMul`, each one `Rat.matSetRow` write, with their
`_at`/`_off` equations; the search and sweep definitions `pivotSearch`,
`clearBelow`, `echelonAux`, `rowEchelon`; and the decidable predicate
`leadingIndex`/`echelonStepOk`/`isEchelon`. Three design decisions are recorded
and each is load-bearing. (1) A `Prop`-valued `Eq x 0` cannot branch a
definition, so the zero test is `Bool`-valued — this is where ℚ's decidable
order is spent, and it is why ADR-0603 row 2 (a boundary refutation) is EMPTY
for this family. (2) The fuel for `rowEchelon` is `cols` and that is exact, not
generous: the pivot column advances on BOTH branches of the loop, so `cols`
steps reach the exit guard and no more are possible. (3) A zero row's
`leadingIndex` is `cols`, which turns "leading entries move right, zero rows
last" into one comparison rather than a three-way split, and is the quantity
`Rat.rank` will count. `rowEchelon_isEchelon` is NOT attempted and its four
obligations are sized here.
Index-status: accepted

Related: ADR-1543 (`Rat.det_matMul` and `Rat.matSetRow`, which this builds on),
ADR-0603 (graded statement families), ADR-0601 (one trust anchor),
the 2026-08-27 architecture review §3a (computed, not extracted).

## Context

`Rat.rank` does not exist, and
<!-- was-absent: Rat.rank -->
[`docs/formalized-math-2026-08/09-*.md`](../../formalized-math-2026-08) §4.3
concedes it. Rank is read off a row-echelon form and rank-nullity follows from
the same construction, so the echelon form is the piece that has to land first.

Step 0, on a FRESH index built in this lane's worktree (2,092 declarations,
411 in the `Rat` namespace): `shape_search --name-like echelon` ABSENT,
`--name-like rank` ABSENT, `--name-like pivot` ABSENT, `--name-like addRow`
ABSENT, `--name-like rowScale` ABSENT.

**The coordinator's step 0 was run against a STALE prebuilt binary and its
`matSetRow` / `matSubstRows` verdicts were wrong.** That binary reported
`declarations=2835` with `--include-constructed` and a bare-index positive
control of 1,963 against a current 2,092; it did not know `Rat.matSetRow`,
which exists in `rat_prelude/det_mul.rs` and had landed the same day. It DID
know `Rat.det_matMul_2` — a dimension-2 result that predates the merge — so the
freshness probe passed while the index was old. This is the documented
stale-prebuilt false-ABSENT hazard, arriving through a positive control that
happened to be older than the change. The rebuild took 73 seconds and turned
two ABSENTs into `FOUND 3` each, and `Rat.matSetRow` is now the single
primitive all three row operations are built from.

## Decision

Land `crates/axeyum-lean-kernel/src/rat_prelude/echelon.rs`: twenty-nine
declarations, every one admitted with an empty `Kernel::axiom_footprint`.

### 1. The zero test is `Bool`-valued, and that is what "computed" means here

Row reduction has to BRANCH on whether a candidate pivot is zero. A
`Prop`-valued `Eq x 0` cannot drive that: the kernel will not reduce a
`Decidable`-free case analysis on a proposition, and a definition built by
eliminating an `Exists` is a definition the kernel cannot evaluate at a
concrete matrix — which is exactly the evidence this repository leans on to
detect a wrong `Definition`.

So `Rat.isZeroB x := if Rat.ble x 0 then Rat.ble 0 x else false`. Over ℚ the
order is decidable (`Rat.ble` is a plain function into `Bool`), so this is
total, needs no `Decidable` instance and no choice principle, and the whole
elimination reduces at concrete arguments.

`Nat.lnp_bounded_search` — the least-number principle, which the brief named as
a candidate — is **not** the right tool and cannot be. Its conclusion is an `Or`
of `Prop`s. It is what you use to PROVE a least element exists; it cannot be
the thing a definition computes with. The computed counterpart is
`Rat.pivotSearchAux`, a structural recursion on a fuel counter returning a
`Nat`.

The two are reconciled by four theorems, which are the only place the decided
test meets the propositional one:

    Rat.isZeroB_zero              : isZeroB 0 = true                       -- Eq.refl
    Rat.eq_zero_of_isZeroB        : ∀ x, isZeroB x = true  → x = 0
    Rat.isZeroB_of_eq_zero        : ∀ x, x = 0 → isZeroB x = true
    Rat.ne_zero_of_isZeroB_false  : ∀ x, isZeroB x = false → Not (x = 0)

`eq_zero_of_isZeroB` is where the decidability is actually spent:
`Rat.le_antisymm` over two `Rat.le_of_ble_eq_true` bridges, under a `Bool` case
split on `ble x 0` whose `false` branch contradicts the hypothesis outright.

**Consequence for ADR-0603.** A graded statement family's row 2 is a boundary
refutation — the counterexample that shows why the general constructive form
cannot be strengthened. For this family row 2 is **empty, by proof**: there is
no boundary to refute, because the order on ℚ is decidable and the general form
IS the exact form. That is a real difference from the `CReal` families, where
the same construction would need a Markov-style side condition, and it is worth
saying rather than leaving as a silent omission.

### 2. The fuel for `rowEchelon` is `cols`, and it is exact

`Rat.echelonAux rows cols fuel M pr pc` recurses structurally on `fuel`,
because the loop is not structural in any of its real arguments. The step is:
stop if `pr >= rows` or `pc >= cols`; otherwise search column `pc` at or below
row `pr` for a nonzero entry. If there is none, the column is already clear and
only `pc` advances. If there is one, swap it into place, clear everything
below, and advance both cursors.

`Rat.rowEchelon M rows cols := echelonAux rows cols cols M 0 0`.

`cols` is exact rather than generous **because `pc` advances on both branches**.
Starting at `pc = 0`, after `k` iterations `pc = k`, so at `k = cols` the exit
guard has fired and no further step is possible. Both inner sweeps
(`pivotSearchAux`, `clearBelowAux`) take fuel `rows` for the same reason.

This is not tidiness. Every `Nat` numeral this prelude builds is unary, so a
magnitude formed is a magnitude walked; the alternative `rows * cols` would
form a product for no gain. The two exhaustion answers are deliberately the
SAME value in both searches — `rows` for `pivotSearch`, `cols` for
`leadingIndex` — so a caller reads "not found" from one test and never has to
distinguish "searched everything" from "ran out of fuel".

### 3. A zero row's `leadingIndex` is `cols`

`Rat.leadingIndex M r cols` is the first column of row `r` with a nonzero
entry, and `cols` when the row is zero. Because a leading index is always at
most `cols`, `Nat.ble cols l` says exactly "row `l` is zero", and the adjacent
row test collapses to one comparison:

    Rat.echelonStepOk l1 l2 cols := ble (succ l1) l2 || (ble cols l1 && ble cols l2)

Both conjuncts of the second clause are required. Dropping `ble cols l2` would
read "the leading indices increase, or the first row is zero", which accepts
`[[0,0],[1,0]]` — a zero row above a nonzero one, in no textbook's echelon
form. That case is a registered test.

`cols` for a zero row is also the quantity `Rat.rank` counts: the rank of the
echelon form is the number of rows whose leading index is strictly below
`cols`.

### 4. Each row operation has a kernel-checked inverse

This is what rank INVARIANCE consumes next, and each carries a side condition
that is load-bearing rather than defensive:

- `Rat.rowSwap_involutive` is UNCONDITIONAL, `i = j` included. That corner is
  not free: at `r = i` the outer write reads row `j` of the once-swapped
  matrix, and which `matSetRow` equation applies depends on whether `j = i`, so
  the proof carries a second `Nat.beq j i` split inside the first branch.
- `Rat.rowAddMul_inverse` REQUIRES `Nat.beq j i = false`. At `i = j` the
  operation scales row `i` by `1 + k` and its inverse is a scaling by
  `1/(1+k)`, not an addition of `-k`. The hypothesis also does the work inside
  the proof: it is what says row `j` still holds `M j` after the first step,
  which is the only reason the two multiples cancel.
- `Rat.rowScale_inverse` takes `Not (Eq k 0)` rather than `0 < k`, so it covers
  the negative pivots elimination actually produces.

## What is NOT decided here

**`rowEchelon_isEchelon : ∀ A r c, isEchelon (rowEchelon A r c) r c = true` is
not attempted.** It is a full correctness proof of Gaussian elimination at
symbolic dimension, and sizing it honestly is more useful than a partial
attempt. Its four obligations, in dependency order:

1. **`isZeroB` ↔ `Eq 0`.** Landed here (§1). This was the only cheap one.
2. **`pivotSearch`'s postcondition.** A fuel induction giving: the returned
   index is either `rows`, and then every entry of column `c` in `[start, rows)`
   is zero; or it is in `[start, rows)` with a nonzero entry there. Both halves
   need obligation 1 to move between the `Bool` the search branches on and the
   `Prop` the invariant states.
3. **`clearBelow`'s postcondition.** For every `r` in `(pr, rows)` the swept
   matrix has `0` at `(r, pc)`, and rows outside that range are untouched. The
   arithmetic core is `a + (-(a/b)) * b = 0` given `b ≠ 0` — which is where
   obligation 2's nonzero pivot is spent, through
   `Rat.mul_inv_cancel_of_ne_zero` and `Rat.ne_zero_of_isZeroB_false`.
4. **The loop invariant.** A conjunction over the row range — rows `[0, pr)`
   are in echelon form with strictly increasing leading indices all below `pc`,
   and rows `[pr, rows)` are zero throughout `[0, pc)` — preserved by the step
   and implying the conclusion at exhaustion. This is a fuel induction with the
   invariant as an explicit `Prop` in the motive, and it is the largest piece.

Obligations 2 and 3 are each a lane. Obligation 4 is at least a lane on its own
and probably two. `Rat.rank` and rank-nullity do **not** depend on obligation 4:
rank can be defined and its invariance under the elementary operations proved
from §4's inverse laws alone, which is what the next lane should take.

## Consequences

- The three row operations are single `Rat.matSetRow` writes, so their
  `_at`/`_off` equations are one lemma application each rather than an
  induction. Anything else built over rows of a ℚ matrix should reach for
  `matSetRow` first.
- Fourteen evaluation tests reduce every definition at concrete arguments
  against hand-computed values, each with a control that must FAIL to be defeq.
  The three 2×2 inputs are chosen so each branch of the loop is the only thing
  that produces the observed answer, and the 3×3 forces a mid-run re-pivot.
  `Rat.isEchelon` is asserted FALSE on three non-echelon inputs, not merely
  true on echelon ones — a predicate returning `true` unconditionally passes
  every positive test there is.
- `matrix_det.rs`'s `bool_cases_eq` becomes `pub(super)`. It is the
  equation-keeping `Bool` split all four hypothesis-carrying proofs here need,
  and reusing it rather than re-deriving it keeps
  `scripts/check-shape-duplicates.py` honest.
- Measured cost: the `rat` prelude build is 1.61–1.66 s after this change
  (three runs of `prelude_build_timing`) against a briefed baseline of ~1.65 s.
  No measurable change; the run-to-run spread exceeds any effect.
