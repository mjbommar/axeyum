# Proof Certificate Cookbook

The Proof Certificate Cookbook is the guide to Axeyum's trust story: fast
search is untrusted, but answers are replayed or independently checked by small
verifiers.

The cookbook should teach proof artifacts by example. Each recipe should start
with a tiny formula, show the solver route, show the evidence artifact, name the
checker, and describe whether the result reconstructs to Lean.
The route-level tamper command index lives in
[Checker Tamper Matrix](../foundational-resources/CHECKER-TAMPER-MATRIX.md).

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
    qf-bv-bitblast.md
    boolean-cnf-lrat.md
    finite-model-replay.md
    qf-uf-congruence-alethe.md
    qf-lra-farkas.md
    qf-lia-diophantine.md
    array-row-axiom.md
    lean-horizon-template.md
```

## Roadmap

The detailed implementation plan lives in [ROADMAP.md](ROADMAP.md).
For active route tamper coverage and gaps, use
[Checker Tamper Matrix](../foundational-resources/CHECKER-TAMPER-MATRIX.md).

## First Recipe Candidates

First recipes now landed:

- [QF_BV Bit-Blast Evidence](recipes/qf-bv-bitblast.md)
- [Boolean CNF DRAT/LRAT Evidence](recipes/boolean-cnf-lrat.md)
- [Finite Model Replay Evidence](recipes/finite-model-replay.md)
- [QF_UF Congruence And Alethe Evidence](recipes/qf-uf-congruence-alethe.md)
- [QF_LRA Farkas Evidence](recipes/qf-lra-farkas.md)
- [QF_LIA Diophantine Evidence](recipes/qf-lia-diophantine.md)
- [Array Read-Over-Write Axiom Evidence](recipes/array-row-axiom.md)
- [Lean Horizon Template](recipes/lean-horizon-template.md)

Remaining initial candidates:

- Datatype constructor contradiction through structural evidence.

Each recipe should link back to [trust-ledger](../research/08-planning/trust-ledger.md)
and to the implementation files that emit and check the artifact.
