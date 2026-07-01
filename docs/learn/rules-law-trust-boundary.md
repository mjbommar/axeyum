# Rules/Law Trust Boundary

Rules-as-code examples use the same resource pattern as the math packs:

```text
human source rule -> small formal model -> generated facts or solver query
-> replayed witness or checked obligation -> explicit theorem/legal horizon
```

Axeyum does not interpret law. A human writes the rule text, citation, and
formal model. Axeyum checks the small logical obligations that follow from that
model.

## The Current Surface

Start with the committed rules/law JSON boundary:

```sh
python3 scripts/query-rules-as-code.py summary
```

The current result is:

```text
rule_packs=6
bounded_sample_rows=1013
generated_query_rows=1774
check_results={'sat': 8, 'unsat': 24}
proof_statuses={'checked': 22, 'proof-gap': 2, 'replayed': 8}
```

The six packs are deliberately small:

| Pack | What It Teaches | Trust Boundary |
|---|---|---|
| [benefit eligibility](../rules-as-code/examples/benefit-eligibility-v0/README.md) | predicates, thresholds, effective dates | `sat` threshold/date witnesses replay; consistency, coverage, monotonicity, and implementation-equivalence obligations are checked |
| [authorization policy](../rules-as-code/examples/authorization-policy-v0/README.md) | roles, tenants, explicit deny, policy versions | version-delta witnesses replay; tenant isolation, deny precedence, admin guard, and equivalence obligations are checked |
| [tax benefit arithmetic](../rules-as-code/examples/tax-benefit-arithmetic-v0/README.md) | caps, phase-outs, monotone integer formulas | threshold/date witnesses replay; nonnegativity, cap, phase-out monotonicity, and equivalence obligations are checked |
| [procurement scoring](../rules-as-code/examples/procurement-scoring-v0/README.md) | exclusions, deadlines, bid caps, score monotonicity | bonus-threshold witnesses replay; exclusion, deadline, cap, score monotonicity, and equivalence obligations are checked |
| [grant allocation](../rules-as-code/examples/grant-allocation-v0/README.md) | exact rational shares, budget balance, minimum floors, administrative caps | allocation witnesses replay; budget, floor, cap, and equivalence obligations are checked through QF_LRA/Farkas |
| [category equivalence](../rules-as-code/examples/category-equivalence-v0/README.md) | equivalent categories, normalization, priority program | category/program witnesses replay; category congruence and equivalence obligations are explicit QF_UF/Alethe proof gaps |

The model and evidence boundary is recorded in three places:

- [Rules/Law Crosswalk](../foundational-resources/RULES-LAW-CROSSWALK.md):
  which math proof pattern a rule check reuses;
- [Rules/Law Pattern Matrix](../foundational-resources/RULES-LAW-PATTERN-MATRIX.md):
  which patterns are covered by the current packs;
- [Rules/Law Resource Queries](../foundational-resources/RULES-LAW-QUERIES.md):
  how to inspect the JSON boundary without reading prose.

## Replayed Witnesses

A replayed witness is a concrete fact pattern that the pack recomputes from the
source model. It is useful for edge cases, but it is not a proof of a universal
property.

For example, procurement generated rows replay bounded award decisions:

```sh
python3 scripts/query-rules-as-code.py rows \
  --pack procurement_scoring_v0 \
  --family bounded_awards \
  --text 2026-08-02 \
  --limit 3 \
  --require-any
```

What is trusted here:

- the committed rule model and sample domain are the source of the row;
- the deterministic generator enumerates the bounded fact pattern;
- the validator recomputes the expected output.

What is not claimed:

- real procurement compliance;
- completeness over all bids, dates, vendors, and procurement rules;
- solver performance or Z3/cvc5 parity.

## Checked Obligations

A checked obligation asks for a bad state and expects `unsat`. The solver may
search however it wants, but the row is useful only because the result is
replayed or checked by an independent route.

Inspect the checked obligations:

```sh
python3 scripts/query-rules-as-code.py checks \
  --proof-status checked \
  --validation bool_qf_lia_solver_regression \
  --require-any
```

Representative checked shapes:

| Shape | Example Checks | Math Resource Route |
|---|---|---|
| impossible dual output | benefit `consistency` | finite predicates plus Bool/QF_LIA |
| uncovered complete fact pattern | benefit `coverage` | finite predicate totality |
| forbidden actor/resource boundary | authorization `tenant_isolation` | relations/functions now; QF_UF/Alethe later for role maps |
| deny-over-permit | authorization `explicit_deny_precedence` | finite orders and Boolean replay |
| bad threshold or cap | tax `cap_respected`, procurement `bid_cap_respected`, grant `admin_cap_respected` | QF_LIA for integer caps; QF_LRA/Farkas for rational shares |
| bad monotonicity | benefit income, tax phase-out, procurement quality score | exact arithmetic monotonicity |
| category congruence | category equivalence priority rows | finite equivalence classes; QF_UF/Alethe proof gap |
| model vs implementation mismatch | checked in the Bool/QF_LIA and QF_LRA/Farkas packs; proof-gap for category equivalence | bounded equivalence and executable replay; QF_UF/Alethe when category functions are the issue |

## How To Read A Rule Pack

When reviewing a new or existing pack, read it in this order:

1. `source.md`: the human-authored rule text or paraphrase.
2. `model.md`: the symbols, bounded domain, and formal rule function.
3. `checks.md`: which claims are `sat`, `unsat`, or replay-only.
4. `expected.json`: the machine-readable expected rows and proof status.
5. generated query rows under `docs/rules-as-code/generated/queries/`.

Then run:

```sh
python3 scripts/gen-rules-as-code-dashboard.py
python3 scripts/validate-rules-as-code.py
python3 scripts/query-rules-as-code.py checks --text monotonicity --require-any
python3 scripts/query-rules-as-code.py checks --pack grant_allocation_v0 --validation qf_lra_farkas_solver_regression --proof-status checked --require-any
python3 scripts/query-rules-as-code.py checks --pack category_equivalence_v0 --proof-status proof-gap --require-any
python3 scripts/query-rules-as-code.py families --text adjacent --require-any
cargo test -p axeyum-solver --test rules_as_code_examples
```

## What Would Justify The Next Pack

Do not add another pack just to increase the count. Add one only if it
exercises a distinct proof shape or repeated consumer need:

| Needed Shape | Why It Would Be New | Likely Route |
|---|---|---|
| workflow reachability | policy state transitions and forbidden paths, not just scalar facts | Boolean CNF/LRAT or finite graph replay |
| checked role/category equivalence | the category pack now has source-linked QF_UF artifacts, but not checked Alethe evidence | QF_UF/Alethe |
| pure Boolean coverage certificate | tiny coverage/consistency rows that should show proof-object anatomy | Boolean CNF/LRAT |
| multi-period allocation | repeated rational budgets with carryover/state transitions | QF_LRA/Farkas plus finite transition replay |

Until one of those appears, the right work is improving queries, validation,
and explanations around the existing packs.
