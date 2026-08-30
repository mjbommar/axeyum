# Notes: 375-supon-ub-arbitrary

Detail moved out of [`../status/375-supon-ub-arbitrary.md`](../status/375-supon-ub-arbitrary.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

1. **The level** — an arbitrary level ABOVE a scheduled one, made usable for
   one epsilon by `meshMax_le_supOn_add` (`mesh_max_le_add_of_modulus` is
   depth-uniform). This handles the mesh-maximum side.
2. **The accuracy the mesh is ASKED for** — `outer2 := succ (2·outer)`, one
   halving finer than the modulus itself demands, so `mesh_le_of_ge` reports
   `Δ ≤ 1/(2·outer + 2)` and the locate epsilon can be the same size. The two
   fuse to exactly the `1/(outer + 1)` `uc_spec` consumes. **No amount of extra
   LEVEL substitutes for this**, because the schedule's guarantee is stated at
   the accuracy you asked for.

The same halving runs a second time at the outer accuracy (`kk := succ (2·e)`)
to split the final `1/(e+1)` between the uniform-continuity transfer and the
mesh-maximum gap.

## The value/argmax distinction is untouched

No `argmax`-shaped declaration was added and none should be.
`CReal.evt_attained_max_decides_sign` proves an attaining maximiser would
decide the sign of an arbitrary real — a genuine impossibility result, not an
unfinished proof.

## EVT comparability — the honest verdict

**EVT is now ELIGIBLE for the per-statement dominance claim, and on the two
axes ADR-0692/0699 settled it passes.** Trusted base: `creal` stays at 0.
Computational content: `supOn` now carries both halves of the supremum
characterization, and the specific gap ADR-0710 named is closed.

**Two things still separate the statements**, and a referee must be told both:

1. **Our hypothesis is stronger.** `UniformlyContinuousOn F a b` versus
   Mathlib's continuity on a compact set. We do **not** have Heine–Cantor
   in-tree — measured, with a positive control, not assumed. This is not an
   oversight: Heine–Cantor is not constructively available, which is why
   Bishop-style analysis takes uniform continuity as the definition. The two
   developments quantify over different classes of input.
2. **Our conclusion is a bound, not an attained maximum**, permanently, by
   `evt_attained_max_decides_sign`.

So: EVT's supremum is now stated and proved here in a form comparable to
Mathlib's, axiom-free, with computational content Mathlib's does not carry —
under a stronger hypothesis and with a constructive rather than attained
conclusion. That is a per-statement comparison a referee can check. **It is not
a coverage claim and must not be quoted as one.**

## Next

The obvious follow-on is not more `supOn` machinery. It is to decide, at the
strategy layer, whether the hypothesis difference in (1) should be recorded as
a permanent axis of the comparison — the way breadth already is — rather than
as an open task, since no amount of work in this kernel removes it.
