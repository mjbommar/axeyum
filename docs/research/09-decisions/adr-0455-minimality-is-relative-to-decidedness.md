# ADR-0455: A Minimality Claim Is Only As Strong As The Decidedness Of Its Tests

Status: accepted
Index-summary: A minimal-subset claim is absolute only if every subset test was decided; an inconclusive test forces a conservative keep and inflates the answer
Date: 2026-08-15

## Context

Two lanes in unrelated domains, on the same day, produced a claim of the form
*"this subset is minimal"* — and both discovered, independently and without
naming it, that the claim has two very different strengths depending on
something outside the subset itself.

**Geometry.** `groebner_cert::certify` returns the certificate for the smallest
non-degeneracy condition subset that succeeds. Those conditions appear as
hypotheses in a fact's `formal.statement`, so "smallest" is not bookkeeping — it
is part of what the theorem claims. But a subset can fail to succeed for two
reasons: it is genuinely *not in the ideal*, or the reduction *declined* on a
budget ceiling. Under the first, the subset is truly insufficient. Under the
second, we simply do not know.

**Operations research.** `unsat_core` is deletion-based: it drops a row, re-solves,
and keeps the row if the remainder is still unsatisfiable. A row whose removal
leaves the solver at `unknown` is **conservatively kept** — the right call for
soundness, and it means a "minimized" core is only irreducible if every
leave-one-out solve came back decided. That lane re-solved all 24 subsets across
three instances and treated `unknown` as a failure rather than a pass.

The shape is identical, and it generalises to any procedure that reports a
minimal or irreducible subset by removing elements and re-testing:

> A removal test that is **inconclusive** forces a conservative *keep*. Keeps
> inflate the reported subset. So the reported subset is minimal **among the
> removals we could decide**, which is a weaker statement than minimal — and the
> two are indistinguishable in the output unless someone records which regime
> the run was in.

## Decision

**Any minimality or irreducibility claim must record whether every removal test
was decided.** Two regimes, named explicitly rather than left to the reader:

- **Absolute.** Every subset/removal test returned a definite verdict. The
  reported subset is minimal, full stop — no larger budget, faster algorithm, or
  different heuristic can shrink it, because the answer never depended on those.
- **Budget-relative.** At least one test was inconclusive (declined, `unknown`,
  timed out). The subset is the smallest we could *establish*, and a stronger run
  might shrink it. Say so where the claim is made, not in a diary.

Where the absolute regime is affordable, **measure it** rather than assuming the
weaker one. Both lanes found it was affordable and both found the result was
absolute, which is precisely why the distinction was worth drawing: the honest
weaker claim would have understated what had actually been established.

This is not a new mechanism. It is a reporting obligation on mechanisms that
already exist, and it belongs beside the ledger's other honesty rules —
`epistemic_status` versus `external_status`, `proof_route` scoping
`axiom_footprint`, and evidence `checkers` recording independence.

## Evidence

- `crates/axeyum-cas/examples/geometry_order_audit.rs` — runs **every** condition
  subset of every corpus theorem under both monomial orders. All subsets came
  back *decided* (`in ideal` / `not in ideal`), never declined. Since ideal
  membership does not depend on the monomial order, that upgraded the corpus's
  six condition sets from budget-relative to **absolute**, and the six
  certificates were byte-identical across orders.
- `crates/axeyum-solver/examples/infeasibility_iis.rs` — re-solves every
  leave-one-out subset and replays each returned model through the IR ground
  evaluator. All 24 across three instances returned `sat`, so the cores are
  irreducible absolutely. Core-to-instance ratios 4.9%, 15.6%, 8.3%; identical
  cores independently re-derived by z3 4.13.3.
- The counter-case is the one that motivates the rule: had a geometry subset
  declined on `ReductionSteps`, the honest report would have been "smallest among
  the subsets the budget decided", and switching the default monomial order —
  which *does* change which subsets are reachable — could then have silently
  changed what six facts claim.

## Consequences

**A claim can get stronger without the computation changing.** The geometry
condition sets did not move when the order changed; what moved was our knowledge
that they *could not* move. That is a real epistemic gain and the ledger should
be able to express it.

**Cost.** Establishing absoluteness is `2^n` subset tests in the geometry case
and `n` re-solves in the IIS case. Affordable at current sizes, and it will not
always be. When it is not, the budget-relative claim is the correct one to make —
the failure this ADR prevents is making the strong claim by default, not making
the weak one when it is warranted.

**Not decided here:** whether `fact.schema.json` should carry a structured field
for this rather than prose in `formal.statement` and `notes`. Two instances is
thin evidence for a schema change; a third would justify it.
