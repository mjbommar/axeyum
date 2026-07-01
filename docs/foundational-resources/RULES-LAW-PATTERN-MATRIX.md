# Rules/Law Pattern Matrix

This matrix connects the current rules-as-code packs to the math-resource
concept rows, proof routes, and copyable queries that already exist in Axeyum.
It is the practical companion to the
[Rules/Law Crosswalk](RULES-LAW-CROSSWALK.md) and the
[Rules/Law Resource Queries](RULES-LAW-QUERIES.md): the crosswalk explains the
reuse story, the query guide shows the raw JSON boundary, and this page says
which rule patterns are actually covered today.
For the learner-facing walkthrough, see
[Rules/Law Trust Boundary](../learn/rules-law-trust-boundary.md).

Scope:

- the formal rule models are still human-authored;
- generated rows are finite replay fixtures, not legal interpretations;
- checked rows use the current Bool/QF_LIA regression route unless noted;
- rule packs are not solver benchmarks unless a separate benchmark corpus says
  so.

## Current Pack Surface

```sh
python3 scripts/query-rules-as-code.py summary
```

Expected current boundary:

```text
rule_packs=4
bounded_sample_rows=882
generated_query_rows=1626
check_results={'sat': 6, 'unsat': 17}
proof_statuses={'checked': 17, 'replayed': 6}
```

| Pack | Domain | Main Pattern | Checked Rows | Generated Families |
|---|---|---|---|---|
| `benefit_eligibility_v0` | benefits | predicates, thresholds, effective dates | consistency, coverage, monotonicity, implementation equivalence | `coverage` (576), `income_monotonicity_adjacent` (528) |
| `authorization_policy_v0` | authorization | roles, tenant relations, explicit deny, versions | tenant isolation, deny precedence, admin tenant guard, implementation equivalence | `bounded_requests` (96), `version_delta_adjacent` (48) |
| `tax_benefit_arithmetic_v0` | tax/benefit | caps, phase-outs, threshold cliffs, dates | nonnegative benefit, cap, phase-out monotonicity, implementation equivalence | `bounded_benefits` (66), `income_phaseout_adjacent` (60) |
| `procurement_scoring_v0` | procurement | exclusions, deadlines, bid caps, score monotonicity | debarment, late submission, bid cap, score monotonicity, implementation equivalence | `bounded_awards` (144), `quality_monotonicity_adjacent` (108) |

## Pattern Coverage

| Rule Pattern | Current Rule Checks | Math-Resource Concepts | Current Route | Consumer Query |
|---|---|---|---|---|
| Complete finite fact patterns | benefit `coverage`, authorization `bounded_requests`, procurement `bounded_awards` | `curriculum_predicate_logic`, `bridge_counterexample_proof`, `family_boolean_cnf_lrat` | finite replay plus checked Bool/QF_LIA obligations | `python3 scripts/query-rules-as-code.py rows --text expected --limit 5 --require-any` |
| Explicit exclusions and required predicates | procurement `debarment_exclusion`, benefit `consistency`, authorization tenant checks | `curriculum_predicate_logic`, `bridge_finite_boolean_algebra` | checked Bool/QF_LIA | `python3 scripts/query-rules-as-code.py checks --text exclusion --require-any` |
| Roles, tenants, relations, and category maps | authorization `tenant_isolation`, `admin_tenant_guard`, generated role/action rows | `bridge_partition_relation_roundtrip`, `bridge_finite_image_preimage_inverse`, `bridge_qf_uf_alethe_anatomy` | checked Bool/QF_LIA today; QF_UF/Alethe is the natural upgrade | `python3 scripts/query-rules-as-code.py rows --pack authorization_policy_v0 --text tenant --limit 5 --require-any` |
| Thresholds, caps, dates, and deadlines | benefit threshold/date witnesses, tax cap/phase-out checks, procurement deadline and bid-cap checks | `bridge_totality_conventions`, `bridge_exact_vs_floating_arithmetic`, `bridge_lp_objective_farkas` | QF_LIA checked rows plus finite replay | `python3 scripts/query-rules-as-code.py checks --text cap --require-any` |
| Adjacent monotonicity | benefit income, tax phase-out, procurement quality-score monotonicity | `bridge_lp_objective_farkas`, `bridge_rational_convexity_shadow`, `bridge_bounded_family_asymptotic_boundary` | QF_LIA checked rows today; QF_LRA/Farkas when rational allocation/scoring appears | `python3 scripts/query-rules-as-code.py families --text adjacent --require-any` |
| Version and effective-date transitions | benefit `temporal_transition`, authorization `version_delta`, tax temporal rows | `bridge_finite_dynamics_euler_replay`, `bridge_bounded_family_asymptotic_boundary` | finite replay and QF_LIA date/version obligations | `python3 scripts/query-rules-as-code.py rows --text version --limit 5 --require-any` |
| Precedence, deny-over-permit, and overrides | authorization `explicit_deny_precedence` | `bridge_finite_boolean_algebra`, `bridge_partition_relation_roundtrip`, `bridge_qf_uf_alethe_anatomy` | checked Bool/QF_LIA today; finite-order/QF_UF route when priority vocab becomes first-class | `python3 scripts/query-rules-as-code.py checks --text precedence --require-any` |
| Bounded implementation equivalence | all four packs have `implementation_equivalence` | `bridge_finite_image_preimage_inverse`, `bridge_qf_uf_alethe_anatomy`, `family_finite_algebra_alethe` | checked Bool/QF_LIA mismatch obligations plus executable replay | `python3 scripts/query-rules-as-code.py checks --text implementation_equivalence --require-any` |

## Proof-Route Translation

| Rules/Law Need | Preferred Math Route | Current Status | Upgrade Trigger |
|---|---|---|---|
| `sat` witness explanation | finite replay | present in every pack | add minimized witnesses when the same boundary is hard to inspect manually |
| Boolean consistency or coverage | Boolean CNF/LRAT or Bool/QF_LIA | currently Bool/QF_LIA checked | move tiny pure-Boolean rows to CNF/LRAT when the encoded source formula is small enough for a learner |
| Integer thresholds and dates | QF_LIA/Diophantine or arithmetic-DPLL | current checked route | add source-linked LIA route examples for repeated date-window or count-obstruction patterns |
| Rational allocation or exact caps | QF_LRA/Farkas | not yet needed by current rule packs | use when a real policy pack needs rational shares, LP-style eligibility, or allocation constraints |
| Role/category equality conflicts | QF_UF/Alethe | planned upgrade for relation-heavy packs | use when role maps, category equivalences, or quotient-like classifications become first-class |
| Broad legal schema theorem | Lean horizon | out of scope for current packs | only after kernel-checked reconstruction can state the formal theorem |

## Queries To Keep Working

These are the matrix smoke queries. They intentionally use the same public JSON
boundary as downstream consumers:

```sh
python3 scripts/query-rules-as-code.py checks --text monotonicity --require-any
python3 scripts/query-rules-as-code.py checks --text implementation_equivalence --require-any
python3 scripts/query-rules-as-code.py families --text adjacent --require-any
python3 scripts/query-rules-as-code.py rows --pack authorization_policy_v0 --family version_delta_adjacent --text analyst --limit 3 --require-any
python3 scripts/query-rules-as-code.py rows --pack tax_benefit_arithmetic_v0 --family income_phaseout_adjacent --text 2026-07-01 --limit 3 --require-any
python3 scripts/query-rules-as-code.py rows --pack procurement_scoring_v0 --family quality_monotonicity_adjacent --limit 3 --require-any
```

The corresponding math-resource lookups remain:

```sh
python3 scripts/query-foundational-resources.py concepts --text predicate --require-any
python3 scripts/query-foundational-resources.py concepts --text totality --require-any
python3 scripts/query-foundational-resources.py concepts --text graph --require-any
python3 scripts/query-foundational-resources.py routes --route qf_lia_diophantine --require-any
python3 scripts/query-foundational-resources.py routes --route qf_lra_farkas --require-any
python3 scripts/query-foundational-resources.py routes --route qf-uf-congruence-alethe --require-any
```

## Next Build Rule

Do not add another rule pack just to increase count. Add one only when it
exercises a distinct current math proof shape or repeated consumer need, for
example:

- graph reachability plus temporal state transitions;
- rational allocation or LP-style caps needing QF_LRA/Farkas;
- role/category equivalence needing QF_UF/Alethe;
- small pure-Boolean coverage rows suited to CNF/LRAT certificate anatomy.

Until then, keep the boundary as committed JSON, generated dashboards, and
copyable query commands.
