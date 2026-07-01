# Rules/Law Resource Queries

This guide gives copyable queries for the current
[Rules-as-Code Verification Lab](../rules-as-code/README.md) JSON boundary.
It complements the [Rules/Law Crosswalk](RULES-LAW-CROSSWALK.md): the crosswalk
maps math proof shapes to policy checks, while this page shows how a consumer
can find the committed rule packs, checked obligations, and generated bounded
query rows without reading prose.
For the current pattern-to-route coverage table, see the
[Rules/Law Pattern Matrix](RULES-LAW-PATTERN-MATRIX.md).
For the learner-facing trust-boundary walkthrough, see
[Rules/Law Trust Boundary](../learn/rules-law-trust-boundary.md).

The scope remains deliberately small:

- rule text and formalizations are human-authored;
- generated rows are deterministic finite domains, not legal advice;
- checked `unsat` rows must keep source-linked SMT-LIB artifacts and the
  `rules_as_code_examples` evidence regression;
- generated query rows are planning/replay fixtures, not solver benchmarks.

## Summary

```sh
python3 scripts/query-rules-as-code.py summary
```

Current expected summary:

```text
rule_packs=7
bounded_sample_rows=1037
generated_query_rows=1942
check_results={'sat': 9, 'unsat': 27}
proof_statuses={'checked': 27, 'replayed': 9}
```

## Find Packs By Pattern

All checked Bool/QF_LIA packs:

```sh
python3 scripts/query-rules-as-code.py packs \
  --fragment QF_LIA \
  --proof-status checked \
  --require-any
```

All checked QF_LRA/Farkas packs:

```sh
python3 scripts/query-rules-as-code.py packs \
  --fragment QF_LRA \
  --proof-status checked \
  --require-any
```

The procurement scoring pack:

```sh
python3 scripts/query-rules-as-code.py packs \
  --text procurement \
  --require-any
```

Use this when a downstream consumer needs to locate the current policy domains:
benefit eligibility, authorization, tax/benefit arithmetic, procurement
scoring, grant allocation, category equivalence, and workflow reachability.

The category-equivalence pack:

```sh
python3 scripts/query-rules-as-code.py packs \
  --pack category_equivalence_v0 \
  --require-any
```

The workflow-reachability pack:

```sh
python3 scripts/query-rules-as-code.py packs \
  --pack workflow_reachability_v0 \
  --require-any
```

## Find Checked Obligations

All source-linked checked obligations:

```sh
python3 scripts/query-rules-as-code.py checks \
  --proof-status checked \
  --validation bool_qf_lia_solver_regression \
  --require-any
```

Grant-allocation QF_LRA/Farkas obligations:

```sh
python3 scripts/query-rules-as-code.py checks \
  --pack grant_allocation_v0 \
  --validation qf_lra_farkas_solver_regression \
  --proof-status checked \
  --require-any
```

Procurement-specific checked obligations:

```sh
python3 scripts/query-rules-as-code.py checks \
  --pack procurement_scoring_v0 \
  --proof-status checked \
  --require-any
```

This returns the debarment, late-submission, bid-cap, score-monotonicity, and
implementation-equivalence rows. Each row points back through
`expected.json` to an SMT-LIB artifact under the pack and a focused
`rules_as_code_examples` regression.

Category-equivalence checked QF_UF/Alethe obligations:

```sh
python3 scripts/query-rules-as-code.py checks \
  --pack category_equivalence_v0 \
  --proof-status checked \
  --validation qf_uf_alethe_solver_regression \
  --require-any
```

These rows expose source-linked QF_UF SMT-LIB artifacts that the
`rules_as_code_examples` harness proves with `prove_qf_uf_unsat_alethe` and
checks with `Evidence::check`.

Workflow-reachability checked Bool/QF_LIA obligations:

```sh
python3 scripts/query-rules-as-code.py checks \
  --pack workflow_reachability_v0 \
  --proof-status checked \
  --validation bool_qf_lia_solver_regression \
  --require-any
```

These rows expose source-linked Bool/QF_LIA SMT-LIB artifacts for the no-skip,
terminal-state, and implementation-equivalence obligations.

## Find Generated Query Families

Grant allocation generated families:

```sh
python3 scripts/query-rules-as-code.py families \
  --pack grant_allocation_v0 \
  --require-any
```

Procurement generated families:

```sh
python3 scripts/query-rules-as-code.py families \
  --pack procurement_scoring_v0 \
  --require-any
```

Quality-score monotonicity rows:

```sh
python3 scripts/query-rules-as-code.py families \
  --pack procurement_scoring_v0 \
  --text quality \
  --require-any
```

The two current procurement families are:

- `bounded_awards`: every bounded bid/score/date/exclusion fact pattern;
- `quality_monotonicity_adjacent`: adjacent quality-score comparisons for
  fixed non-score facts.

The two grant-allocation families are:

- `bounded_allocations`: every bounded shelter/clinic/admin rational share
  triple;
- `balanced_budget_allocations`: only triples whose shares sum to exactly `1`,
  with floor and cap flags exposed.

The two category-equivalence families are:

- `bounded_category_rows`: every bounded category/program pair;
- `equivalence_pair_rows`: equivalent-category pairs for each program, exposing
  whether priority-review congruence holds.

The workflow-reachability families are:

- `bounded_transition_rows`: every bounded one-step state/action/supervisor
  fact pattern;
- `two_step_reachability_rows`: bounded two-step paths obtained by composing
  the same transition function.

## Inspect Generated Rows

Late procurement rows:

```sh
python3 scripts/query-rules-as-code.py rows \
  --pack procurement_scoring_v0 \
  --family bounded_awards \
  --text 2026-08-02 \
  --limit 3 \
  --require-any
```

Balanced grant-allocation rows:

```sh
python3 scripts/query-rules-as-code.py rows \
  --pack grant_allocation_v0 \
  --family balanced_budget_allocations \
  --text 1/2 \
  --limit 3 \
  --require-any
```

Authorization version-delta rows:

```sh
python3 scripts/query-rules-as-code.py rows \
  --pack authorization_policy_v0 \
  --family version_delta_adjacent \
  --text analyst \
  --limit 3 \
  --require-any
```

Tax phase-out rows:

```sh
python3 scripts/query-rules-as-code.py rows \
  --pack tax_benefit_arithmetic_v0 \
  --family income_phaseout_adjacent \
  --text 2026-07-01 \
  --limit 3 \
  --require-any
```

Benefit coverage rows:

```sh
python3 scripts/query-rules-as-code.py rows \
  --pack benefit_eligibility_v0 \
  --family coverage \
  --text veteran \
  --limit 3 \
  --require-any
```

Category-equivalence pair rows:

```sh
python3 scripts/query-rules-as-code.py rows \
  --pack category_equivalence_v0 \
  --family equivalence_pair_rows \
  --text emergency_housing \
  --limit 3 \
  --require-any
```

Workflow two-step reachability rows:

```sh
python3 scripts/query-rules-as-code.py rows \
  --pack workflow_reachability_v0 \
  --family two_step_reachability_rows \
  --text '"final_state":"approved"' \
  --limit 3 \
  --require-any
```

## Validation

The standard rules-as-code gate now smoke-checks this query surface:

```sh
just rules-as-code
```

Equivalent direct commands:

```sh
python3 scripts/gen-rules-as-code-dashboard.py
python3 scripts/validate-rules-as-code.py
python3 scripts/query-rules-as-code.py summary
python3 scripts/query-rules-as-code.py packs --text procurement --require-any
python3 scripts/query-rules-as-code.py checks --pack procurement_scoring_v0 --proof-status checked --require-any
python3 scripts/query-rules-as-code.py families --pack procurement_scoring_v0 --text quality --require-any
python3 scripts/query-rules-as-code.py rows --pack procurement_scoring_v0 --family bounded_awards --text 2026-08-02 --limit 3 --require-any
python3 scripts/query-rules-as-code.py packs --pack grant_allocation_v0 --require-any
python3 scripts/query-rules-as-code.py checks --pack grant_allocation_v0 --validation qf_lra_farkas_solver_regression --proof-status checked --require-any
python3 scripts/query-rules-as-code.py families --pack grant_allocation_v0 --text balanced --require-any
python3 scripts/query-rules-as-code.py rows --pack grant_allocation_v0 --family balanced_budget_allocations --text 1/2 --limit 3 --require-any
python3 scripts/query-rules-as-code.py packs --pack category_equivalence_v0 --require-any
python3 scripts/query-rules-as-code.py checks --pack category_equivalence_v0 --proof-status checked --validation qf_uf_alethe_solver_regression --require-any
python3 scripts/query-rules-as-code.py families --pack category_equivalence_v0 --text equivalence --require-any
python3 scripts/query-rules-as-code.py rows --pack category_equivalence_v0 --family equivalence_pair_rows --text emergency_housing --limit 3 --require-any
python3 scripts/query-rules-as-code.py packs --pack workflow_reachability_v0 --require-any
python3 scripts/query-rules-as-code.py checks --pack workflow_reachability_v0 --proof-status checked --validation bool_qf_lia_solver_regression --require-any
python3 scripts/query-rules-as-code.py families --pack workflow_reachability_v0 --text reachability --require-any
python3 scripts/query-rules-as-code.py rows --pack workflow_reachability_v0 --family two_step_reachability_rows --text '"final_state":"approved"' --limit 3 --require-any
```

Run the solver evidence regression when a checked SMT-LIB fixture changes:

```sh
cargo test -p axeyum-solver --test rules_as_code_examples
```
