# Notes: 359-ivt-evt-pareto

Detail moved out of [`../status/359-ivt-evt-pareto.md`](../status/359-ivt-evt-pareto.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- The survey this lane was handed does not hold up: 11 + 2 + 4 = 17, not 15
  (the two row-2 facts are inside the 11); an id-substring match misses
  `F:cas-extremum-irrational-argmax`, the most EVT-shaped fact in the ledger,
  and the seven `F:creal-crossing*` rows; and a content match additionally
  catches two unrelated `nat` facts.
- **9 of the 11 `CReal` IVT/EVT facts are `provenance.curation =
  "generated-unreviewed"`**, with prose that says outright it makes no
  mathematical characterisation. The family is this repository's flagship
  worked example and its ledger rows do not describe it.
- IVT row 2's non-vacuity check is genuinely well built — environment-derived,
  with a positive control of the same declaration kind — but it tests **four
  hand-written names**, and the fact labels that `exhaustive-enumeration`.
- The four theorems establishing both row-2 hypothesis classes
  (`ivtPlateau_nonpos_at_zero`, `_nonneg_at_one`, `_uniformly_continuous`,
  `evtLinear_uniformly_continuous`) have no facts of their own; they appear in
  the ledger only inside one `checker_command` string.
- Every IVT/EVT/MVT CAS row classifies `evaluation` under
  `scripts/check-cas-substance.py`; **none is in the `refl` class**. But
  `evaluation` is the deflating reading: the kernel-reconstructed rows prove
  polynomial evaluations and their signs, not IVT or EVT, and say so in their
  own axiom lists.

## What would close it

`CReal.supOn`, then `CReal.evt_approx_max` (the structural mirror of
`ivt_approx`), then a fact for `evtLinear_uniformly_continuous` and non-vacuity
evidence on the EVT row-2 fact. The five rungs below `supOn` are landed and
axiom-free.

## Not checked

Mathlib's own axiom footprints (needs a Mathlib build); unprovability of
analytic LLPO (metatheoretic, not machine-checkable by this kernel); and no
`cargo test` was run — the tests cited were **read, not executed**.
