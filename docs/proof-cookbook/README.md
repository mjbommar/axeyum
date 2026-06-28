# Proof Certificate Cookbook

The Proof Certificate Cookbook is the planned guide to Axeyum's trust story:
fast search is untrusted, but answers are replayed or independently checked by
small verifiers.

The cookbook should teach proof artifacts by example. Each recipe should start
with a tiny formula, show the solver route, show the evidence artifact, name the
checker, and describe whether the result reconstructs to Lean.

## Audience

- Users who need to know what "proved" means in Axeyum.
- Contributors adding a new unsat route.
- Reviewers auditing the trusted computing base.
- Educators explaining SAT/SMT certificates.

## Planned Artifacts

```text
docs/proof-cookbook/
  README.md
  ROADMAP.md
  recipes/
    # planned tiny route-by-route examples
```

## Roadmap

The detailed implementation plan lives in [ROADMAP.md](ROADMAP.md).

## First Recipe Candidates

- Boolean CNF unsat with LRAT.
- QF_BV unsat through bit-blast plus SAT proof.
- QF_UF unsat through congruence closure / Alethe.
- QF_LRA unsat through a Farkas certificate.
- QF_LIA integer infeasibility through a Diophantine certificate.
- Array read-over-write unsat through checked array elimination.
- Datatype constructor contradiction through structural evidence.

Each recipe should link back to [trust-ledger](../research/08-planning/trust-ledger.md)
and to the implementation files that emit and check the artifact.
