# ADR-0031: Reduction trust ledger (typed, countable trust holes)

Status: accepted
Date: 2026-06-15

## Context

The stack's `unsat` results are "checked **modulo trusted reduction**": the
clausal layer carries a DRAT proof (ADR-0011/0012) and the bit-blast reduction
carries an exhaustive miter, but every other reduction (array elimination
ADR-0010, Ackermann ADR-0013, int-blasting ADR-0014, datatype elimination
ADR-0022, fp→bv ADR-0023) is trusted with the caveat living only in prose. That
makes the trusted base un-auditable: you cannot count it, report it per result,
or watch it shrink.

This closes the first step of Track 3 / P3.0 of the parity plan
(`docs/plan/track-3-proof-lean/P3.0-trust-ledger.md`) and follows the
"trusted small checking" identity (ADR-0002, ADR-0005). It mirrors cvc5's
`TrustId` (`references/cvc5/src/proof/trust_id.h`), where every reduction is
either a checkable proof step or a typed trust hole graded by a pedantic level.

## Decision

**Introduce a typed `TrustId` taxonomy with a pedantic level (0–10) and a
certified/hole status per reduction, and record on every `EvidenceReport` the set
of `TrustStep`s that result depended on.**

- `axeyum_solver::trust` owns `TrustId` (one variant per reduction the stack
  relies on), `ALL_TRUST_IDS` (canonical deterministic order), per-variant
  `label`/`meaning`/`pedantic_level`/`is_certified`/`reference`, and a
  golden-rendered `trust_ledger_markdown()`.
- `EvidenceReport` gains `trusted_steps: Vec<TrustStep>`; each producer in
  `evidence.rs` records the reductions its result went through and whether *this
  run* certified each (e.g. bit-blast is `certified: false` on the plain DRAT
  export route because that route does not run the miter, even though a miter
  route exists).
- The rendered ledger is golden-tested against
  `docs/research/08-planning/trust-ledger.md` (regenerate with
  `UPDATE_TRUST_LEDGER=1 cargo test -p axeyum-solver --test trust_ledger`),
  exactly like the capability matrix — so the trusted-base inventory cannot drift.

## Evidence

The ledger renders 11 reductions, of which **5 remain trust holes** (array-elim,
ackermann, int-blast, datatype-elim, fpa2bv) and 6 are certified (bit-blast,
tseitin, sat-refutation, term-level-enum, farkas, lra-dpll). Per-result tests in
`tests/evidence.rs` confirm: a DRAT QF_BV `unsat` reports bit-blast + tseitin +
sat-refutation (no array reduction); a small QF_BV `unsat` reports only the
term-level step; a QF_ABV `unsat` additionally reports the array-elim trust hole
(`certified: false`); a QF_LRA `unsat` reports the Farkas step and no bit-blast.

## Alternatives

- *Keep the caveat in prose.* Rejected: not countable, drifts, cannot drive to
  zero.
- *Put the steps on `Provenance`.* Rejected: `Provenance` is `Eq` and used in
  equality assertions; a per-result step list belongs on the report, not the
  reproducibility metadata.
- *A boolean "trusted/not" flag.* Rejected: loses the per-reduction identity and
  the pedantic grading that lets P3.5 prioritize which hole to certify next.

## Consequences

- **Easier:** auditing the trusted base; prioritizing reduction-certificate work
  (Track 3 P3.5) by pedantic level; reporting to a consumer exactly what an
  `unsat` trusts.
- **Harder:** every new reduction must now add a `TrustId` variant and record its
  step (enforced socially + by the well-formed golden test), not silently widen
  the trusted base.
- **Revisited when:** P3.5 certifies a reduction (array ROW/IDX/EXT first) — its
  `is_certified` flips to `true` and the ledger's hole count drops; the goal is
  zero holes.
