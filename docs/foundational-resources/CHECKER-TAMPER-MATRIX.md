# Checker Tamper Matrix

This matrix connects public resource-row rejection to the route-specific
checker tamper regressions in the proof cookbook and learner pages.

It is intentionally not another query guide over `expected.json` rows. Public
resource rows show malformed mathematical claims that Axeyum rejects. Checker
tamper tests corrupt the evidence artifact itself and prove the small checker
refuses it.

Use this alongside:

- [Rejection Case Queries](REJECTION-CASE-QUERIES.md) for malformed source-row
  discovery.
- [Proof Route Family Selection](PROOF-ROUTE-FAMILY-SELECTION.md) for choosing
  the representative family before promoting another checked row.
- [Proof Certificate Cookbook](../proof-cookbook/README.md) for route recipes.

## Audit Order

For a route-level review, run the checks in this order:

1. Find source rows with [Rejection Case Queries](REJECTION-CASE-QUERIES.md).
2. Open the linked example pack and recipe.
3. Run the route's positive evidence regression.
4. Run the route's tamper or negative-fixture regression.
5. Record any route without a tamper command as a proof-route gap, not as a
   checked-tamper route.

The foundational resource smoke script checks source rows and negative
fixtures. It does not run the route-specific cargo tests listed below.

## Route Matrix

| Route | Public resource layer | Checker/tamper layer | What rejection proves | Current boundary |
|---|---|---|---|---|
| Finite model replay | `python3 scripts/query-foundational-resources.py checks --fragment finite --proof-status replay-only --require-any` | `python3 scripts/check-foundational-negative-fixtures.py` | Malformed or drifted resource fixtures are rejected by the schema/replay boundary. | This is not proof-object tamper; it checks finite data and validator behavior. |
| Bool/CNF DRAT/LRAT | `python3 scripts/query-foundational-resources.py checks --route boolean --proof-status checked --expected-result unsat --require-any` | `cargo test -p axeyum-cnf --test math_resource_boolean_routes proof_methods_refutation_php_3_2_rejects_tampered_drat_and_lrat` | Removing the final DRAT refutation step or clearing LRAT hints is rejected. | Domain-to-CNF lowering is still a separate trust boundary unless lowering evidence exists. |
| QF_BV DRAT | `python3 scripts/query-foundational-resources.py checks --route qf-bv --proof-status checked --expected-result unsat --require-any` | `cargo test -p axeyum-solver --test math_resource_bv_routes qf_bv_resource_route_rejects_tampered_drat_certificate` | A truncated DRAT proof for the generated CNF is rejected. | Plain DRAT checks the generated CNF, not a Lean proof of every bit-blast step. |
| QF_LIA/Diophantine | `python3 scripts/query-foundational-resources.py checks --route Diophantine --proof-status checked --expected-result unsat --require-any` | `cargo test -p axeyum-solver --test math_resource_lia_routes qf_lia_resource_route_rejects_tampered_diophantine_certificate` | A corrupted contradiction-row constant is rejected after recomputing from source equalities. | Nonlinear integer arithmetic and theorem-level modular arithmetic remain outside this route. |
| QF_LRA/Farkas | `python3 scripts/query-foundational-resources.py checks --route Farkas --proof-status checked --expected-result unsat --require-any` | `cargo test -p axeyum-solver --test math_resource_lra_routes linear_optimization_objective_threshold_rejects_tampered_farkas_certificate` | A multiplier tamper that prevents variable cancellation is rejected. | This is exact rational linear arithmetic, not floating-point or nonlinear proof. |
| QF_UF/Alethe | `python3 scripts/query-foundational-resources.py checks --route Alethe --proof-status checked --expected-result unsat --require-any` | `cargo test -p axeyum-solver --test math_resource_uf_routes qf_uf_resource_route_rejects_tampered_alethe_certificate` | A truncated Alethe proof missing the closing step is rejected. | Covered congruence shapes are checked; arbitrary quotient or algebra theorems remain horizons. |
| Array read-over-write | `python3 scripts/query-foundational-resources.py checks --field topology --route Alethe --proof-status checked --require-any` and array route recipes | `cargo test -p axeyum-solver --test evidence produce_evidence_certifies_small_array_axiom_unsats` | Current regression proves direct ROW axiom evidence rechecks with no trusted reduction step. | Add a corrupted array-certificate regression before calling this route tamper-covered. |
| Lean horizon | `python3 scripts/query-foundational-resources.py checks --proof-status lean-horizon --expected-result not-run --require-any` | `python3 scripts/validate-foundational-concepts.py` and `./scripts/check-links.sh` | Metadata and docs keep theorem horizons explicit. | No tamper test exists until a concrete Lean artifact and no-`sorryAx` check exist. |

## Recipe And Learner Anchors

| Route | Recipe | Learner page with tamper boundary |
|---|---|---|
| Bool/CNF DRAT/LRAT | [Boolean CNF DRAT/LRAT Evidence](../proof-cookbook/recipes/boolean-cnf-lrat.md) | [Proof Object Anatomy](../learn/math/proof-object-anatomy-end-to-end.md) |
| QF_BV DRAT | [QF_BV Bit-Blast Evidence](../proof-cookbook/recipes/qf-bv-bitblast.md) | [QF_BV Bit-Blast Certificate Anatomy](../learn/math/qf-bv-bitblast-certificate-anatomy-end-to-end.md) |
| QF_LIA/Diophantine | [QF_LIA Diophantine Evidence](../proof-cookbook/recipes/qf-lia-diophantine.md) | [Diophantine Certificate Anatomy](../learn/math/diophantine-certificate-anatomy-end-to-end.md) |
| QF_LRA/Farkas | [QF_LRA Farkas Evidence](../proof-cookbook/recipes/qf-lra-farkas.md) | [Farkas Certificate Anatomy](../learn/math/farkas-certificate-anatomy-end-to-end.md) |
| QF_UF/Alethe | [QF_UF Congruence And Alethe Evidence](../proof-cookbook/recipes/qf-uf-congruence-alethe.md) | [Alethe Certificate Anatomy](../learn/math/alethe-certificate-anatomy-end-to-end.md) |
| Finite replay | [Finite Model Replay Evidence](../proof-cookbook/recipes/finite-model-replay.md) | [Finite Countermodel Replay](../learn/math/finite-countermodel-replay.md) |
| Array ROW | [Array Read-Over-Write Axiom Evidence](../proof-cookbook/recipes/array-row-axiom.md) | route-specific learner page still pending |
| Lean horizon | [Lean Horizon Template](../proof-cookbook/recipes/lean-horizon-template.md) | [Analysis/Topology Proof Horizons](../learn/math/analysis-topology-proof-horizons.md) |

## Maintenance Rules

- Do not say a resource row is tamper-tested unless the route command above, or
  a narrower replacement command in the recipe, corrupts evidence and expects
  rejection.
- Do not replace source-row rejection queries with cargo tamper tests; they
  answer different questions.
- When adding a new checker recipe, add one positive check command and one
  corrupted-evidence command here before marking the route reviewer-ready.
- When a route cannot yet corrupt an evidence artifact, state the gap as the
  current boundary and keep the resource claim at replay-only, checked-with-gap,
  or Lean-horizon as appropriate.
