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
| Membership, roles, jurisdictions, actor/resource relations | finite sets, relations, functions, equivalence classes | [`finite-sets-v0`](../../artifacts/examples/math/finite-sets-v0/), [`relations-functions-v0`](../../artifacts/examples/math/relations-functions-v0/), [`equivalence-classes-v0`](../../artifacts/examples/math/equivalence-classes-v0/) | finite replay, QF_UF/Alethe for functional conflicts | authorization subjects, role tables, jurisdiction membership |
| Thresholds, ages, dates, deadlines, counts | integer and rational arithmetic | [`integer-lia-v0`](../../artifacts/examples/math/integer-lia-v0/), [`natural-arithmetic-v0`](../../artifacts/examples/math/natural-arithmetic-v0/), [`rationals-lra-v0`](../../artifacts/examples/math/rationals-lra-v0/) | QF_LIA/Diophantine, arithmetic-DPLL, QF_LRA/Farkas | income threshold, age cutoff, effective date split |
| Threshold cliffs and monotonicity | optimization and convexity shadows | [`linear-optimization-v0`](../../artifacts/examples/math/linear-optimization-v0/), [`convexity-rational-v0`](../../artifacts/examples/math/convexity-rational-v0/) | QF_LRA/Farkas for exact-linear impossibility; finite replay for examples | "one dollar above threshold" witness and bad monotonicity query |
| Workflow state, dependency chains, delegated authority, forbidden paths | graph reachability and cuts | [`graph-reachability-v0`](../../artifacts/examples/math/graph-reachability-v0/), [`graph-cut-v0`](../../artifacts/examples/math/graph-cut-v0/), [`graph-d-separation-v0`](../../artifacts/examples/math/graph-d-separation-v0/) | Bool/CNF with DRAT/LRAT for small refutations; finite replay for paths | authorization and administrative-process packs |
| Precedence, hierarchy, explicit deny, override, classification levels | finite orders and lattices | [`finite-order-lattices-v0`](../../artifacts/examples/math/finite-order-lattices-v0/) | finite relation replay, QF_UF/Alethe for equality conflicts | deny-over-permit precedence and rule priority checks |
| Versioned rules and transition points | bounded finite dynamics and arithmetic dates | [`bounded-dynamics-v0`](../../artifacts/examples/math/bounded-dynamics-v0/), [`finite-euler-method-v0`](../../artifacts/examples/math/finite-euler-method-v0/) | finite transition replay, QF_LIA/QF_LRA for bounded transitions | old-threshold versus new-threshold eligibility examples |
| Implementation equivalence | finite functions and bounded counterexample search | [`function-composition-v0`](../../artifacts/examples/math/function-composition-v0/), [`relations-functions-v0`](../../artifacts/examples/math/relations-functions-v0/) | finite replay, QF_UF/Alethe when function consistency is the issue | logical model versus executable eligibility function |

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
| `consistency` | finite-sample replay | finite predicates plus Bool/QF_LIA | encode `eligible and ineligible` as a source-linked query and require checked `unsat` evidence |
| `coverage` | finite-sample replay | finite predicate totality | encode a no-output fact pattern and keep the finite-domain boundary explicit |
| `threshold_cliff` | concrete witnesses replay | integer thresholds | produce minimized QF_LIA witnesses at and just above active thresholds |
| `monotonicity` | finite-sample replay | arithmetic monotonicity | encode the bad monotonicity pattern with exception guards and expect `unsat` |
| `temporal_transition` | concrete witnesses replay | versioned arithmetic dates | keep the old/new date split explicit and test both sides of the effective date |
| `implementation_equivalence` | executable validator replay | bounded equivalence | add an existential mismatch query over the bounded sample domain |

Validation for the current pack remains:

```sh
python3 scripts/validate-rules-as-code.py
```

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

1. Keep `benefit-eligibility-v0` as the reference pack and add source-linked
   Bool/QF_LIA fixtures for consistency, coverage, monotonicity, and bounded
   implementation equivalence.
2. Add the authorization-policy pack from the
   [rules-as-code roadmap](../rules-as-code/ROADMAP.md) and reuse graph
   reachability plus finite order/lattice checks for tenant isolation and
   deny-over-permit precedence.
3. Add the tax/benefit arithmetic pack and reuse QF_LIA/QF_LRA threshold,
   phase-out, cap, and monotonicity patterns.
4. Promote only those rows that have deterministic replay plus a source-linked
   regression or proof route.

## Non-Goals

- Do not parse natural-language law automatically.
- Do not claim a finite bounded rule pack proves compliance with a real statute.
- Do not benchmark rule packs as solver parity rows unless the fragment,
  corpus, and oracle comparison are explicit.
- Do not hide source interpretation inside solver formulas; every formal rule
  must cite the human-readable source clause it encodes.
