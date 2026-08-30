# ADR-0675: EVT is a refutation with no row 1 behind it, so it is not a Pareto example

Status: accepted
Date: 2026-08-30
Index-summary: Audited IVT and EVT against Mathlib at the pinned commit. IVT's
ADR-0603 family is complete and its row 2 survives a harsh reading; EVT has
row 2 and **no row 1** — `CReal.supOn` is not in the environment — so EVT is a
refutation of the classical statement with nothing constructive behind it, and
per-statement dominance is currently false for it.
Index-status: accepted

- **Lane:** `ivt-evt-pareto`
- **Audit document:**
  [`docs/formalized-math-2026-08/08-ivt-and-evt-measured-against-mathlib.md`](../../formalized-math-2026-08/08-ivt-and-evt-measured-against-mathlib.md)
- **Corrects:** the standing use of "results like IVT and EVT" as a *pair* of
  worked dominance examples. It holds for IVT. It does not hold for EVT.
- **Reclassifies nothing.** No fact was edited. Where a fact overstates itself
  that is recorded in the audit document for a separate lane.

## Context

The programme goal is that the architecture makes results like IVT and EVT
Pareto-dominant over a traditional Mathlib formalization.
`07-the-cost-model-and-pareto-position.md` is careful that this is a
*per-statement* claim plus uncontested axes, never global dominance over a
200k-theorem library. ADR-0603 says a classical theorem lands as a graded
family: row 1 general constructive form, row 2 boundary refutation, row 3
decidable-fragment exact form, row 4 labeled import. Row 2 is the axis a
classical library has no counterpart for, so the claim leans on it.

Nobody had audited it.

## Decision

**Cite IVT as the worked dominance example. Do not cite EVT until
`CReal.supOn` and an `evt_approx_max` row 1 land.**

## What was measured

Read from the kernel environment at this lane's own HEAD (a stale prebuilt
binary reports a false ABSENT, which is the verdict that matters here), and
from Mathlib at `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

### IVT's family is complete

Row 1 is `CReal.ivt_approx` — arbitrary `F`, arbitrary uniform-continuity
witness, arbitrary `a ≤ b`, and `n` universally quantified, concluding
`∃ x ∈ [a,b], |F x| ≤ 1/(n+1)`. That is the general constructive approximate
IVT, not a special case dressed as one. Axiom footprint `0`.

Row 2 is `CReal.ivt_exact_root_decides_sign`, and it holds up on four checks:
the hypothesis class is *proved* on the plateau family
(`ivtPlateau_nonpos_at_zero`, `_nonneg_at_one`, `_uniformly_continuous`, all
axiom-free) rather than assumed; the written-out root hypothesis is pinned
definitionally equal to `ivtPlateau`; non-vacuity is checked against
`kernel.environment()` **with a positive control of the same declaration
kind**; and `creal/ivt_boundary.rs` states its own scope honestly, including
that ADR-0603's name "boundary refutation" is "looser than what is proved."

### EVT's row 1 does not exist

The extreme-value module's inventory shard declares exactly three things:
`CReal.evtLinear` (def), `CReal.evt_attained_max_decides_sign` (row 2),
`CReal.evtLinear_uniformly_continuous`. Filtering the fresh inventory to
`prelude = creal` finds no supremum, attainment or approximate-maximum
theorem, against a positive control of 24 `creal` theorems whose names contain
`max`. `CReal.supOn` is not in the environment.

`creal/supremum.rs` already says this — "**Still not landed: `CReal.supOn`
itself** … This is not a hedge — it is the honest outcome of a real attempt" —
and draws the distinction that makes the gap structural rather than
bookkeeping: **the supremum VALUE of a uniformly continuous function on a
compact interval is constructive; the ARGMAX is not.** Row 2 refutes the
argmax. The value is the substitute, and it is the missing row.

### Row 4 is absent for both

Zero facts mention `intermediate_value` or `exists_isMaxOn`. Five facts carry
`proof_route = "imported-kernel-lean"`; none is analytic.

## Consequences

Pareto dominance requires being no worse on every axis and better on at least
one. For EVT we are strictly better on the boundary axis and strictly worse on
"does the library give you a usable extreme value theorem" — Mathlib proves it
for an arbitrary compact subset of an arbitrary topological space
(`IsCompact.exists_isMaxOn`, `Mathlib/Topology/Order/Compact.lean:246`) and we
prove nothing positive at all. That is not dominance; it is a trade.

The fix is ordinary work and its first rungs are landed: `CReal.maxRange` and
its order lemmas, `meshLevelCount`, `meshMax` with `meshMax_step_le`/`_mono`,
`expOfModulus`/`trueExpOfModulus`, all axiom-free.

## Alternatives rejected

- **Weaken the claim to "IVT and EVT together show the architecture works."**
  Rejected: it is the aggregation move `07-…` exists to forbid. A per-statement
  claim is checked per statement.
- **Count `F:cas-extremum-irrational-argmax` as EVT's positive row.** Rejected
  under ADR-0601: it carries four CAS axioms including
  `cas.extremum-certificate-not-kernel-reconstructed`, so it is `cas-internal`
  and cannot be headline. Its kernel-reconstructed sibling
  (`F:cas-evt-endpoint-exclusion-cubic-kernel-checked`) proves three polynomial
  evaluations and two comparisons — `cas_substance.shape = "evaluation"` — and
  states in its own axiom list that the EVT implication is not reconstructed.
- **Treat row 2 alone as sufficient.** Rejected, and this is the point of the
  ADR: a boundary result says *how far the constructive fragment reaches*. With
  no row 1, it says the fragment reaches nowhere, which is a claim about our
  library rather than about mathematics.

## Open, and recorded rather than fixed

- Row 2's non-vacuity check tests four hand-written names
  (`CReal.le_total`, `lt_total`, `leTotal`, `ltTotal`). The fact labels this
  `evidence.kind = "exhaustive-enumeration"`, which reads stronger than a
  literal list. Unprovability of analytic LLPO is metatheoretic and is not
  machine-checked anywhere — `creal/ivt_boundary.rs` says so.
- `F:creal-evt-attained-max-decides-sign` carries **no** non-vacuity evidence
  of its own and is `provenance.curation = "generated-unreviewed"`. Its
  conclusion is the same Prop as IVT's, so the IVT check covers it
  mathematically; nothing in the ledger says so.
- The four theorems establishing both row-2 hypothesis classes have no facts;
  they appear in the ledger only inside one `checker_command` string.
