# Lane: determinant-laws

## Status

**In progress.** Target: the first of the four laws ADR-1120 left open for
`Rat.det` at general `n` — `det matId n = 1` at symbolic `n`.

## Plan

The blocker ADR-1120 named ("an induction relating minor structure across
dimensions") resolves into one reusable congruence lemma plus a small
`sumRange` peel:

1. `Rat.sumRange_eq_head_of_tail_zero` — `(∀ k, f (succ k) = 0) →
   sumRange f (succ n) = f 0`. Induction on `n` against
   `Rat.sumRange_succ`'s right-peel.
2. `Rat.det_congr` — `(∀ r c, A r c = B r c) → det A n = det B n`.
   This is the piece `funext`'s absence forces: `matMinor matId 0 0` is
   *pointwise* the identity and cannot be shown *equal* to it, so `det`
   needs its own pointwise congruence. Induction on `n`, with the step
   applying the IH at the two minors.
3. `Rat.det_matId` — induction on `n`; the `j = 0` summand survives and
   `det_congr` carries its minor back to `matId`.

## Landed changes

(none yet)
