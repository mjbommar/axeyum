# Rules/Law Crosswalk For Foundational Resources

## Purpose

This crosswalk shows how the math-curriculum resources can be reused by the
[Rules-as-Code Verification Lab](../rules-as-code/README.md) without inventing a
separate reasoning stack.

The scope is deliberately small:

- humans still author the formal rule model and source citations;
- Axeyum checks the formalized obligations, witnesses, and counterexamples;
- every `sat` witness must replay against the rule model;
- every `unsat` result needs a named proof route or an explicit gap;
- no row here is legal advice or automatic statutory interpretation.

The reusable identity is the same as the core project:

```text
untrusted fast search, trusted small checking
```

For the current covered-pattern table and copyable JSON queries, see the
[Rules/Law Pattern Matrix](RULES-LAW-PATTERN-MATRIX.md). This crosswalk is the
design map; the pattern matrix is the current coverage map.
For a learner-facing walkthrough of the trust boundary, see
[Rules/Law Trust Boundary](../learn/rules-law-trust-boundary.md).

## Workflow

Use the math resources as a staging path for a rule pack:

1. Cite the source clause or policy paragraph.
2. Translate only the needed terms into a small formal model.
3. Pick the corresponding math-resource pattern below.
4. Encode a `sat` witness or `unsat` obligation in the indicated fragment.
5. Replay the witness or check the proof artifact.
6. Render the counterexample back in domain language with source citations.

If a rule cannot be expressed in one of the rows below, keep it as a proof gap
or Lean horizon until the formal dependency is clear.

## Resource Pattern Map

| Rule/Policy Need | Math Resource Pattern | Example Packs | Axeyum Route | First Rule-Pack Use |
|---|---|---|---|---|
| Complete fact patterns, eligibility predicates, required conditions | finite predicate logic and Boolean replay | [`finite-predicate-v0`](../../artifacts/examples/math/finite-predicate-v0/), [`logic-basics-v0`](../../artifacts/examples/math/logic-basics-v0/) | Bool/CNF, finite replay, later CNF/LRAT | consistency and coverage in [`benefit-eligibility-v0`](../rules-as-code/examples/benefit-eligibility-v0/) |
| Membership, roles, jurisdictions, actor/resource relations | finite sets, relations, functions, equivalence classes | [`finite-sets-v0`](../../artifacts/examples/math/finite-sets-v0/), [`relations-functions-v0`](../../artifacts/examples/math/relations-functions-v0/), [`equivalence-classes-v0`](../../artifacts/examples/math/equivalence-classes-v0/) | finite replay, QF_UF/Alethe for functional conflicts | tenant/resource role tables in [`authorization-policy-v0`](../rules-as-code/examples/authorization-policy-v0/) and category normalization in [`category-equivalence-v0`](../rules-as-code/examples/category-equivalence-v0/) |
| Thresholds, ages, dates, deadlines, counts | integer and rational arithmetic | [`integer-lia-v0`](../../artifacts/examples/math/integer-lia-v0/), [`natural-arithmetic-v0`](../../artifacts/examples/math/natural-arithmetic-v0/), [`rationals-lra-v0`](../../artifacts/examples/math/rationals-lra-v0/) | QF_LIA/Diophantine, arithmetic-DPLL, QF_LRA/Farkas | income threshold, age cutoff, effective date split in [`benefit-eligibility-v0`](../rules-as-code/examples/benefit-eligibility-v0/) and tax phase-out thresholds in [`tax-benefit-arithmetic-v0`](../rules-as-code/examples/tax-benefit-arithmetic-v0/) |
| Threshold cliffs, caps, deadlines, and monotonicity | optimization and convexity shadows | [`linear-optimization-v0`](../../artifacts/examples/math/linear-optimization-v0/), [`convexity-rational-v0`](../../artifacts/examples/math/convexity-rational-v0/) | QF_LRA/Farkas or QF_LIA for exact-linear impossibility; finite replay for examples | "one dollar above threshold" witnesses, cap checks, and phase-out monotonicity in [`tax-benefit-arithmetic-v0`](../rules-as-code/examples/tax-benefit-arithmetic-v0/), bid-cap/deadline/score monotonicity in [`procurement-scoring-v0`](../rules-as-code/examples/procurement-scoring-v0/), and rational share caps in [`grant-allocation-v0`](../rules-as-code/examples/grant-allocation-v0/) |
| Rational allocation, exact shares, and LP-style policy caps | rational arithmetic plus finite LP shadows | [`rationals-lra-v0`](../../artifacts/examples/math/rationals-lra-v0/), [`linear-optimization-v0`](../../artifacts/examples/math/linear-optimization-v0/), [`finite-sdp-v0`](../../artifacts/examples/math/finite-sdp-v0/) | QF_LRA/Farkas for universal linear impossibility; finite rational replay for witnesses | shelter/clinic/admin share constraints and budget balance in [`grant-allocation-v0`](../rules-as-code/examples/grant-allocation-v0/) |
| Workflow state, dependency chains, delegated authority, forbidden paths | graph reachability and cuts | [`graph-reachability-v0`](../../artifacts/examples/math/graph-reachability-v0/), [`graph-cut-v0`](../../artifacts/examples/math/graph-cut-v0/), [`graph-d-separation-v0`](../../artifacts/examples/math/graph-d-separation-v0/) | Bool/CNF with DRAT/LRAT for small refutations; finite replay for paths | tenant-isolation boundary checks in [`authorization-policy-v0`](../rules-as-code/examples/authorization-policy-v0/) |
| Precedence, hierarchy, explicit deny, override, classification levels | finite orders and lattices | [`finite-order-lattices-v0`](../../artifacts/examples/math/finite-order-lattices-v0/) | finite relation replay, Bool/CNF for set-family top/precedence conflicts, QF_UF/Alethe for equality conflicts | explicit deny over role/admin permit in [`authorization-policy-v0`](../rules-as-code/examples/authorization-policy-v0/) |
| Versioned rules and transition points | bounded finite dynamics and arithmetic dates | [`bounded-dynamics-v0`](../../artifacts/examples/math/bounded-dynamics-v0/), [`finite-euler-method-v0`](../../artifacts/examples/math/finite-euler-method-v0/) | finite transition replay, QF_LIA/QF_LRA for bounded transitions | old-threshold versus new-threshold eligibility examples |
| Implementation equivalence | finite functions and bounded counterexample search | [`function-composition-v0`](../../artifacts/examples/math/function-composition-v0/), [`relations-functions-v0`](../../artifacts/examples/math/relations-functions-v0/) | finite replay, QF_UF/Alethe when function consistency is the issue | logical model versus executable eligibility/allocation functions, plus category-map equivalence in [`category-equivalence-v0`](../rules-as-code/examples/category-equivalence-v0/) |

## Standard Rule Checks

| Check | Query Shape | Expected Result | Route | Trust Boundary |
|---|---|---|---|---|
| consistency | assert two incompatible outputs, such as `eligible and ineligible` | `unsat` | Bool/CNF or Bool+QF_LIA | Search is untrusted; certificate or replay of exhaustive finite domain is trusted. |
| coverage | assert no output is assigned for a complete fact pattern | `unsat` | Bool/CNF, finite predicate replay | Domain completeness and encoder coverage are trusted separately. |
| threshold cliff | ask for examples at `t`, `t + 1`, and version boundaries | `sat` | QF_LIA or finite replay | Witness facts replay against the source rule model. |
| monotonicity | assert `x2 >= x1`, bad lower result, good higher result | `unsat` unless an exception applies | QF_LIA/QF_LRA, sometimes Farkas | Exception guards must be explicit in the formula. |
| forbidden path | assert reachability from allowed state to forbidden state | `unsat` for a blocked path, `sat` for a real escalation | Bool/CNF or graph replay | Graph construction and certificate checking are separate trust steps. |
| precedence | assert lower-priority rule overrides higher-priority rule | `unsat` | finite order replay or QF_UF/Alethe | The precedence relation must be cited and replayed. |
| temporal transition | same facts, different effective version, different outcome | `sat` when the rule intentionally changes; otherwise `unsat` | QF_LIA over date/version variables | Date encoding and effective-interval source citations are trusted inputs. |
| implementation equivalence | assert model output differs from executable output | `unsat` over bounded domain or fragment | finite replay, Bool/QF_LIA, QF_UF | The executable model is not trusted unless the witness checker replays it. |

## Benefit Eligibility V0 Mapping

The current
[`benefit-eligibility-v0`](../rules-as-code/examples/benefit-eligibility-v0/)
pack already exercises the first slice of this crosswalk:

| Pack Check | Current Evidence | Crosswalk Pattern | Next Axeyum Upgrade |
|---|---|---|---|
| `consistency` | source-linked Bool/QF_LIA fixture with checked Axeyum evidence | finite predicates plus Bool/QF_LIA | broaden from one fixed source-linked obligation to reusable generated consistency queries |
| `coverage` | source-linked Bool/QF_LIA no-output fixture with checked Axeyum evidence, plus finite-sample replay | finite predicate totality | broaden to generated coverage queries over representative complete fact patterns |
| `threshold_cliff` | concrete witnesses replay | integer thresholds | produce minimized QF_LIA witnesses at and just above active thresholds |
| `monotonicity` | source-linked Bool/QF_LIA fixture with checked Axeyum evidence for the fixed no-exception obligation | arithmetic monotonicity | broaden to generated exception-aware monotonicity queries |
| `temporal_transition` | concrete witnesses replay | versioned arithmetic dates | keep the old/new date split explicit and test both sides of the effective date |
| `implementation_equivalence` | source-linked Bool/QF_LIA mismatch fixture with checked Axeyum evidence for the active-threshold slice, plus executable witness replay | bounded equivalence | broaden to generated mismatch queries over versioned/bounded domains |

Validation for the current pack remains:

```sh
python3 scripts/validate-rules-as-code.py
```

## Authorization Policy V0 Mapping

The current
[`authorization-policy-v0`](../rules-as-code/examples/authorization-policy-v0/)
pack exercises the access-control slice of this crosswalk:

| Pack Check | Current Evidence | Crosswalk Pattern | Next Axeyum Upgrade |
|---|---|---|---|
| `tenant_isolation` | source-linked Bool/QF_LIA fixture with checked Axeyum evidence | membership and tenant/resource relations | broaden from the fixed admin cross-tenant query to generated role/action tenant-boundary queries |
| `explicit_deny_precedence` | source-linked Bool/QF_LIA fixture with checked Axeyum evidence | finite precedence/order checks | add a finite order/lattice rendering of deny-over-permit once a reusable rule-priority vocabulary exists |
| `admin_tenant_guard` | source-linked Bool/QF_LIA fixture with checked Axeyum evidence | delegated authority plus forbidden boundary | add graph/reachability-shaped administrative-process examples when a workflow pack lands |
| `version_delta` | concrete witnesses replay | versioned finite policy tables | keep only intended version deltas replayable; reject unintended deltas through generated bounded queries |
| `implementation_equivalence` | source-linked Bool/QF_LIA mismatch fixture with checked Axeyum evidence | bounded equivalence | broaden to generated mismatch queries over all bounded role/action/version rows |

## Tax Benefit Arithmetic V0 Mapping

The current
[`tax-benefit-arithmetic-v0`](../rules-as-code/examples/tax-benefit-arithmetic-v0/)
pack exercises the threshold/cap/phase-out slice of this crosswalk:

| Pack Check | Current Evidence | Crosswalk Pattern | Next Axeyum Upgrade |
|---|---|---|---|
| `non_negative_benefit` | source-linked Bool/QF_LIA fixture with checked Axeyum evidence | integer floors and bounded arithmetic | broaden from the fixed bounded rule to generated nonnegative-output queries for multiple phase-out formulas |
| `cap_respected` | source-linked Bool/QF_LIA fixture with checked Axeyum evidence | threshold caps and exact-linear bounds | use `grant-allocation-v0` as the rational QF_LRA/Farkas reference when future caps require exact shares |
| `threshold_cliff` | concrete witnesses replay | integer threshold cliffs | produce minimized witnesses at each active threshold and one unit above it |
| `phaseout_monotonicity` | source-linked Bool/QF_LIA fixture with checked Axeyum evidence for the active linear phase-out slice, plus finite-sample replay of the full piecewise rule | arithmetic monotonicity | broaden to generated monotonicity queries over all bounded piecewise branches |
| `temporal_transition` | concrete witnesses replay | versioned arithmetic dates | keep only intended threshold changes replayable across effective-date boundaries |
| `implementation_equivalence` | source-linked Bool/QF_LIA mismatch fixture with checked Axeyum evidence for the active linear phase-out slice, plus executable witness replay | bounded equivalence | broaden to generated mismatch queries over all bounded income/date/household rows |

## Procurement Scoring V0 Mapping

The current
[`procurement-scoring-v0`](../rules-as-code/examples/procurement-scoring-v0/)
pack exercises the exclusion/deadline/bid-cap/bonus slice of this crosswalk:

| Pack Check | Current Evidence | Crosswalk Pattern | Next Axeyum Upgrade |
|---|---|---|---|
| `debarment_exclusion` | source-linked Bool/QF_LIA fixture with checked Axeyum evidence | finite predicates and explicit exclusions | broaden from the fixed debarment contradiction to generated exclusion queries over multiple policy dimensions |
| `late_submission_exclusion` | source-linked Bool/QF_LIA fixture with checked Axeyum evidence | encoded dates and temporal deadlines | add richer effective-window rows if a later policy pack needs multi-version deadlines |
| `bid_cap_respected` | source-linked Bool/QF_LIA fixture with checked Axeyum evidence | threshold caps and exact-linear bounds | add more scoring variants only when they introduce distinct LIA pressure; rational allocation pressure now lives in `grant-allocation-v0` |
| `score_bonus_threshold` | concrete witnesses replay | threshold cliffs with exceptions | produce minimized witnesses around each bonus boundary |
| `score_monotonicity` | source-linked Bool/QF_LIA fixture with checked Axeyum evidence, plus finite-sample replay over the bounded domain | arithmetic monotonicity | broaden to generated monotonicity queries over multiple scoring components |
| `implementation_equivalence` | source-linked Bool/QF_LIA mismatch fixture with checked Axeyum evidence, plus executable witness replay | bounded equivalence | broaden to generated mismatch queries over all bounded procurement fact rows |

## Grant Allocation V0 Mapping

The current
[`grant-allocation-v0`](../rules-as-code/examples/grant-allocation-v0/)
pack exercises the rational-allocation slice of this crosswalk:

| Pack Check | Current Evidence | Crosswalk Pattern | Next Axeyum Upgrade |
|---|---|---|---|
| `allocation_witnesses` | concrete rational-share witnesses replay | rational allocation and finite LP shadows | add minimized witness rendering around each active floor/cap boundary |
| `total_budget_respected` | source-linked QF_LRA/Farkas fixture with checked Axeyum evidence | exact rational budget balance | broaden from the fixed impossible total to generated balanced/unbalanced budget queries |
| `shelter_minimum_respected` | source-linked QF_LRA/Farkas fixture with checked Axeyum evidence | minimum-share constraints | add generated near-boundary rows for alternative minimum-share formulas |
| `clinic_minimum_respected` | source-linked QF_LRA/Farkas fixture with checked Axeyum evidence | minimum-share constraints | reuse when later packs need multiple floor constraints over the same allocation |
| `admin_cap_respected` | source-linked QF_LRA/Farkas fixture with checked Axeyum evidence | administrative-cap constraints | broaden to cap families with more buckets only when the source model requires them |
| `implementation_equivalence` | source-linked QF_LRA/Farkas mismatch fixture with checked Axeyum evidence, plus executable witness replay | bounded equivalence over rational domains | broaden to generated mismatch queries over all bounded allocation triples |

## Category Equivalence V0 Mapping

The current
[`category-equivalence-v0`](../rules-as-code/examples/category-equivalence-v0/)
pack exercises the category-map and quotient-like classification slice of this
crosswalk:

| Pack Check | Current Evidence | Crosswalk Pattern | Next Axeyum Upgrade |
|---|---|---|---|
| `category_witnesses` | concrete category/program witnesses replay | finite equivalence classes and category normalization | add minimized witness rendering for category-map edge cases if the domain grows |
| `equivalent_categories_same_priority` | source-linked QF_UF/Alethe fixture with checked Axeyum evidence | equivalent categories and function congruence | add broader category-map variants only when they introduce distinct congruence pressure |
| `implementation_equivalence_qf_uf_gap` | source-linked QF_UF/Alethe mismatch fixture with checked Axeyum evidence | model/implementation equivalence for category functions | reuse when later packs need category-function equivalence rather than arithmetic equivalence |

## Proof Route Reuse

| Proof Route | Rules/Law Use | Existing Recipe |
|---|---|---|
| finite replay | satisfiable witnesses, source-clause examples, bounded domains | [`finite-model-replay.md`](../proof-cookbook/recipes/finite-model-replay.md) |
| Boolean CNF/LRAT | consistency, coverage, forbidden combinations, small graph policies | [`boolean-cnf-lrat.md`](../proof-cookbook/recipes/boolean-cnf-lrat.md) |
| QF_LIA/Diophantine | integer thresholds, counts, dates, divisibility-like eligibility constraints | [`qf-lia-diophantine.md`](../proof-cookbook/recipes/qf-lia-diophantine.md) |
| QF_LRA/Farkas | exact rational thresholds, allocation, caps, linear-program policy checks | [`qf-lra-farkas.md`](../proof-cookbook/recipes/qf-lra-farkas.md) |
| QF_UF/Alethe | function/table consistency, role maps, quotient-like equivalence of categories | [`qf-uf-congruence-alethe.md`](../proof-cookbook/recipes/qf-uf-congruence-alethe.md) |
| Lean horizon | general statutory schemas, unbounded temporal logic, deep normative logic | [`lean-horizon-template.md`](../proof-cookbook/recipes/lean-horizon-template.md) |

Rules/law packs should prefer replay and small certificates first. General
theorems about a legal framework stay Lean-horizon until a kernel-checked route
exists.

## Build Order

1. Keep `benefit-eligibility-v0` as the first reference pack. Landed: source-linked
   Bool/QF_LIA fixtures for consistency, coverage, fixed no-exception
   monotonicity, and active-threshold implementation equivalence. The generated
   query-row JSON now broadens the bounded applicant domain into replayed
   coverage and adjacent-income monotonicity rows.
2. Landed: add the authorization-policy pack from the
   [rules-as-code roadmap](../rules-as-code/ROADMAP.md), reusing
   tenant/resource relations, precedence, bounded version deltas, and
   Bool/QF_LIA proof fixtures for tenant isolation, explicit deny precedence,
   admin tenant guarding, and implementation equivalence. The generated
   query-row JSON now broadens that source model into bounded
   role/action/version requests and adjacent-version delta rows.
3. Landed: add
   [`tax-benefit-arithmetic-v0`](../rules-as-code/examples/tax-benefit-arithmetic-v0/),
   reusing QF_LIA threshold, phase-out, cap, effective-date, and monotonicity
   patterns. The generated query-row JSON now broadens the bounded
   income/date/household domain into benefit replay and adjacent-income
   phase-out monotonicity rows.
4. Landed: add the generated
   [`rules-query-dashboard.md`](../rules-as-code/generated/rules-query-dashboard.md),
   which reads committed rule-pack JSON and counts the bounded query families
   available for generated coverage, equivalence, threshold, cap, version-delta,
   and monotonicity checks.
5. Landed: add deterministic generated query-row JSON under
   [`../rules-as-code/generated/queries/`](../rules-as-code/generated/queries/)
   for all three initial rule packs; `validate-rules-as-code.py` replays those
   1,374 rows from the committed source models.
6. Landed: add
   [`procurement-scoring-v0`](../rules-as-code/examples/procurement-scoring-v0/),
   reusing finite predicates, bid caps, deadline arithmetic, bonus threshold
   witnesses, quality-score monotonicity, and Bool/QF_LIA proof fixtures. The
   generated query-row JSON now broadens the bounded bid/score/date/exclusion
   domain into award replay and adjacent-score monotonicity rows.
7. Landed: add
   [`grant-allocation-v0`](../rules-as-code/examples/grant-allocation-v0/),
   reusing exact rational shares, budget balance, minimum-share floors,
   administrative caps, finite allocation witnesses, and QF_LRA/Farkas proof
   fixtures. The generated query-row JSON now broadens the bounded share
   domain into allocation replay and balanced-budget rows.
8. Landed: add
   [`category-equivalence-v0`](../rules-as-code/examples/category-equivalence-v0/),
   reusing finite equivalence classes, category normalization, generated
   equivalence-pair rows, and source-linked checked QF_UF/Alethe artifacts for
   congruence and implementation-equivalence obligations.
9. Promote only those rows that have deterministic replay plus a source-linked
   regression or proof route.

## Non-Goals

- Do not parse natural-language law automatically.
- Do not claim a finite bounded rule pack proves compliance with a real statute.
- Do not benchmark rule packs as solver parity rows unless the fragment,
  corpus, and oracle comparison are explicit.
- Do not hide source interpretation inside solver formulas; every formal rule
  must cite the human-readable source clause it encodes.
