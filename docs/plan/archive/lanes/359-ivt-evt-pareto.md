# 359 — IVT/EVT Pareto audit

<!-- plan-section: lane-status -->

**Status: DONE.** Measurement task, not a build task. **No fact was
reclassified, reopened or edited.**

## The answer

The Pareto claim holds **for IVT** and **not for EVT**.

| ADR-0603 row | IVT | EVT |
| --- | --- | --- |
| 1 general constructive | `CReal.ivt_approx` — genuine | **ABSENT** (`CReal.supOn` not in the environment) |
| 2 boundary refutation | `CReal.ivt_exact_root_decides_sign` — survives a harsh reading | `CReal.evt_attained_max_decides_sign` — theorem sound, ledger evidence thin |
| 3 decidable fragment | CAS; substantive half is `cas-internal` | CAS; substantive half is `cas-internal` |
| 4 labeled import | **ABSENT** | **ABSENT** |

EVT is a refutation of the classical statement with nothing constructive
standing in its place, so it is a trade rather than a dominance:
Mathlib's `IsCompact.exists_isMaxOn` proves EVT for an arbitrary compact subset
of an arbitrary topological space and we prove nothing positive at all.
`creal/supremum.rs` already says `CReal.supOn` is "still not landed"; nothing in
<!-- was-absent: CReal.supOn -->
the ledger or in `07-the-cost-model-and-pareto-position.md` records that EVT is
being cited as a dominance example while its row 1 is missing.

## Deliverables

- Audit: `docs/formalized-math-2026-08/08-ivt-and-evt-measured-against-mathlib.md`
- Decision: `docs/research/09-decisions/adr-0675-evt-is-a-refutation-with-no-row-one-behind-it.md`
- Instruments and raw outputs are retained under
  `docs/formalized-math-2026-08/evidence/ivt-evt/`: the declaration probe,
  fact-dump script, kernel declaration inventory, and IVT/EVT fact dump.

## Also found

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
