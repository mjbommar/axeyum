# Boolean CNF DRAT/LRAT Evidence

## Problem Shape

Tiny unsat shape:

```text
x
not x
```

As CNF:

```text
(x) and (not x)
```

Expected result: `unsat`.

This is the proof route needed by small Boolean refutation resources such as
pigeonhole and finite graph non-colorability.

## Solver Route

Axeyum's CNF layer owns:

- stable CNF variables and clauses;
- DIMACS-style literal rendering;
- a proof-producing CDCL core for reference proof generation;
- independent DRAT and LRAT checkers.

The search that finds the contradiction is not trusted. A Boolean `unsat`
claim is accepted only when the generated proof checks against the original
CNF.

## Evidence Artifact

Current checked artifacts:

- DRAT proof steps: clause additions/deletions, including a final empty clause.
- LRAT proof steps: clause additions with explicit unit-propagation hints.

For `(x) and (not x)`, the proof is just the empty clause, justified by unit
propagation from the two input clauses.

## Checker

Implementation links:

- [crates/axeyum-cnf/src/drat.rs](../../../crates/axeyum-cnf/src/drat.rs)
- [crates/axeyum-cnf/src/lrat.rs](../../../crates/axeyum-cnf/src/lrat.rs)
- [crates/axeyum-cnf/src/proof_sat.rs](../../../crates/axeyum-cnf/src/proof_sat.rs)

The DRAT checker verifies each added clause by RUP/RAT reasoning and confirms
that the empty clause is derived. The LRAT checker follows explicit hint chains
and does no proof search.

Rejection coverage includes:

- unjustified DRAT additions;
- verified DRAT proofs that do not derive the empty clause;
- corrupted LRAT hints;
- bogus LRAT clauses.

## Lean Reconstruction

Status: not complete for the general CNF/DRAT/LRAT route.

The in-tree checker is the current trust anchor. Lean reconstruction of the
Boolean proof trace remains a future graduation criterion for resources that
need kernel-checked UNSAT evidence.

## Trust Boundary

Trusted or not yet kernel-certified:

- the search that produces the refutation;
- any graph, pigeonhole, or other domain-to-CNF encoder until its lowering
  evidence is explicit.

Checked:

- the DRAT/LRAT proof against the concrete CNF;
- rejection of tampered or incomplete proof artifacts.

Downgrade behavior:

- if a proof cannot be produced or checked, a resource must keep the route as a
  proof gap or report `unknown`, not a proved `unsat`.

## Commands

Focused CNF checker tests:

```sh
cargo test -p axeyum-cnf drat
cargo test -p axeyum-cnf lrat
```

Foundational resource examples that currently point at this route:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/logic-basics-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/proof-methods-refutation-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-coloring-v0
```

## Links

- [SMT Fragment Atlas](../../atlas/README.md)
- [support matrix](../../research/08-planning/support-matrix.md)
- [trust ledger](../../research/08-planning/trust-ledger.md)
- [Logic Basics pack](../../../artifacts/examples/math/logic-basics-v0/)
- [Proof Methods By Refutation pack](../../../artifacts/examples/math/proof-methods-refutation-v0/)
- [Graph Coloring pack](../../../artifacts/examples/math/graph-coloring-v0/)
