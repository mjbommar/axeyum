# Rules-as-Code Verification Lab Roadmap

## Charter

Build a small, auditable lab for applying Axeyum to laws, policies, and other
rule systems. The lab should demonstrate how solver-backed reasoning can check
formalized rules for contradictions, uncovered cases, edge cases, monotonicity,
temporal transitions, policy conflicts, and implementation equivalence.

The lab must stay honest: Axeyum verifies a formal model supplied by humans. It
does not infer legislative intent from prose.

## Non-Goals

- Automatic natural-language law parsing.
- Legal advice.
- A full replacement for Catala, OpenFisca, LegalRuleML, Akoma Ntoso, Cedar, or
  Open Policy Agent.
- Encoding a large statute before the tiny examples are validated.
- Treating solver output as authoritative without replay and explanation.

## External Context

This lab should interoperate conceptually with existing work:

- [LegalRuleML](https://www.oasis-open.org/standard/legalruleml-core-specification-version-1-0-oasis-standard/)
  for legal normative rule representation.
- [Akoma Ntoso](https://www.oasis-open.org/standard/akn-v1-0/) for structured
  legal documents and citations.
- [Catala](https://github.com/catalalang/catala) for literate programming of
  law.
- [OpenFisca](https://openfisca.org/en/) for tax and benefit computation.
- [Cedar](https://cedarpolicy.com/) and [OPA/Rego](https://openpolicyagent.org/docs/policy-language)
  for authorization and policy-as-code workflows.

Axeyum's role is narrower and complementary: proof-oriented checks, model
replay, minimized counterexamples, and eventually Lean-checkable explanations
for formalized rule obligations.

## Current Status

The first four rule packs have landed:

- [Benefit Eligibility V0](examples/benefit-eligibility-v0/README.md)
- [Authorization Policy V0](examples/authorization-policy-v0/README.md)
- [Tax Benefit Arithmetic V0](examples/tax-benefit-arithmetic-v0/README.md)
- [Procurement Scoring V0](examples/procurement-scoring-v0/README.md)

The first metadata schema lives at
[rules-core.schema.json](../../artifacts/ontology/rules-core.schema.json).
The local validator
[validate-rules-as-code.py](../../scripts/validate-rules-as-code.py) discovers
each pack and checks metadata shape, citation file references, expected check
records, concrete witness replay, pack-specific finite-sample invariants, and
the generated query-row JSON under [`generated/queries/`](generated/queries/).
Solver proof integration has started: benefit consistency, coverage,
monotonicity, and bounded implementation equivalence now have source-linked
Bool/QF_LIA fixtures; authorization tenant isolation, explicit deny precedence,
admin tenant guarding, and bounded implementation equivalence do as well; and
tax/benefit non-negativity, cap, active phase-out monotonicity, and bounded
implementation equivalence now have checked fixtures. Procurement debarment,
late submission, bid-cap, score-monotonicity, and bounded implementation
equivalence checks also have checked fixtures. They are checked by
`cargo test -p axeyum-solver --test rules_as_code_examples`; benefit threshold
and temporal-transition rows, authorization version-delta rows, tax/benefit
threshold-cliff and temporal-transition rows, and procurement bonus-threshold
rows remain replayed witnesses.
The generated
[Rules Query Dashboard](generated/rules-query-dashboard.md) now reads the four
pack JSON files and exposes 882 bounded sample rows plus 1,626 deterministic
generated query rows for coverage, income monotonicity, version deltas,
threshold/cap checks, deadlines, bid-cap exclusions, and monotonicity.

The cross-resource reuse map is
[Rules/Law Crosswalk For Foundational Resources](../foundational-resources/RULES-LAW-CROSSWALK.md).
Use it to choose math-resource patterns, proof routes, and trust boundaries
before adding new rule packs.

The current pattern matrix is
[Rules/Law Pattern Matrix](../foundational-resources/RULES-LAW-PATTERN-MATRIX.md).
It records which finite predicate, role/tenant, threshold, monotonicity,
version, precedence, and bounded-equivalence patterns are actually covered by
the four current packs and which math proof routes they reuse.

The learner-facing trust-boundary page is
[Rules/Law Trust Boundary](../learn/rules-law-trust-boundary.md). It explains
how to read current packs from source rule to formal model, replayed witness,
checked obligation, and explicit legal/theorem horizon.

## Audience

| Audience | Need |
|---|---|
| Policy engineer | Find contradictory or overbroad policies before deployment. |
| Rules-as-code researcher | Compare solver-backed verification with executable law systems. |
| Compliance engineer | Produce concrete edge-case witnesses and regression tests. |
| Axeyum contributor | Exercise arithmetic, datatypes, arrays, quantifiers, and proofs outside program verification. |

## Rule Pack Structure

Each example rule pack should eventually live under:

```text
docs/rules-as-code/examples/<pack-id>/
  README.md
  source.md          # human-readable rule text or paraphrase
  model.md           # formalization notes
  checks.md          # consistency/coverage/equivalence checks
  expected.md        # expected solver outcomes and witnesses
```

The planned machine-readable metadata should live under:

```text
artifacts/ontology/rules-core.schema.json
```

Suggested metadata fields:

```json
{
  "id": "benefit_eligibility_v0",
  "domain": "benefits",
  "jurisdiction": "example",
  "source_citations": [
    {
      "label": "Example Rule 1(a)",
      "uri": "source.md#rule-1a"
    }
  ],
  "effective_interval": {
    "from": "2026-01-01",
    "to": null
  },
  "actors": ["applicant", "agency"],
  "inputs": [
    {"name": "age", "sort": "Int"},
    {"name": "income", "sort": "Int"},
    {"name": "resident", "sort": "Bool"}
  ],
  "outputs": [
    {"name": "eligible", "sort": "Bool"}
  ],
  "checks": [
    "consistency",
    "coverage",
    "monotonicity",
    "threshold_cliff",
    "implementation_equivalence"
  ],
  "axeyum_fragments": ["QF_LIA", "Bool"],
  "proof_expectation": "replay first; Lean route when available"
}
```

## First Example Pack: Eligibility With Exceptions

Status: first pack landed as
[Benefit Eligibility V0](examples/benefit-eligibility-v0/README.md).

Model a tiny benefits rule:

- eligible if age is at least 18;
- income is at most a threshold;
- applicant is a resident;
- exception: sanctioned applicants are ineligible;
- override: veterans are eligible under a higher threshold;
- threshold changes after an effective date.

Checks:

1. **Consistency**
   - There is no assignment where the same rule version proves both eligible and
     ineligible.
2. **Coverage**
   - Every complete applicant fact pattern produces one of eligible or
     ineligible.
3. **Threshold cliff**
   - Generate examples just below, at, and above the threshold.
4. **Monotonicity**
   - More income should not turn ineligible into eligible unless the veteran
     override applies.
5. **Temporal transition**
   - Same facts can change result only when the effective date changes.
6. **Implementation equivalence**
   - A small executable function agrees with the logical model on bounded
     domains or by solver proof.

Exit criteria:

- All checks have tiny formulas.
- Sat witnesses replay and are minimized where useful.
- Unsat checks name their proof/evidence route or explicitly state the current
  gap.

## Second Example Pack: Authorization Policy

Status: landed as
[Authorization Policy V0](examples/authorization-policy-v0/README.md), with
source-linked Bool/QF_LIA proof fixtures for tenant isolation, explicit deny
precedence, admin tenant guarding, and bounded implementation equivalence.

Model a small access-control policy:

- users, roles, resources, actions;
- permit/deny precedence;
- explicit deny wins;
- admin override;
- tenant isolation.

Checks:

- A user from tenant A cannot access tenant B's resource.
- Explicit deny overrides role permit.
- Admin override does not bypass tenant isolation unless stated.
- Policy version N and N+1 differ only on intended requests.

This pack connects to Cedar/OPA-style policy use cases without depending on
either implementation.

## Third Example Pack: Tax/Benefit Arithmetic

Status: landed as
[Tax Benefit Arithmetic V0](examples/tax-benefit-arithmetic-v0/README.md), with
source-linked Bool/QF_LIA proof fixtures for non-negativity, cap,
active-phase-out monotonicity, and bounded implementation equivalence.

Model a tiny tax/benefit formula:

- income bands;
- phase-out rate;
- household size adjustment;
- cap;
- effective-date threshold change.

Checks:

- no negative benefit;
- benefit is non-increasing with income in ordinary ranges;
- discontinuities are explicitly documented;
- implementation agrees with the logical model on bounded inputs.

This pack exercises LIA/optimization and counterexample minimization.

## Fourth Example Pack: Procurement Scoring

Status: landed as
[Procurement Scoring V0](examples/procurement-scoring-v0/README.md), with
source-linked Bool/QF_LIA proof fixtures for debarment exclusion, late
submission exclusion, bid-cap enforcement, score monotonicity, and bounded
implementation equivalence.

Model a tiny procurement award rule:

- debarred vendors are excluded;
- late submissions are excluded;
- bids above a cap are excluded;
- small-business status adds a fixed score bonus;
- adjusted score must meet an award threshold.

Checks:

- excluded vendors, late submissions, and over-cap bids cannot be awarded;
- the small-business bonus flips the intended threshold edge;
- increasing quality score cannot lose an award when other facts stay fixed;
- implementation agrees with the logical model on bounded inputs.

This pack exercises finite predicates, integer thresholds, encoded dates,
monotonicity, and checked implementation-equivalence fixtures.

## Validation Checks

Near-term documentation checks:

```sh
just rules-as-code
./scripts/check-links.sh
python3 scripts/gen-rules-as-code-dashboard.py
python3 scripts/validate-rules-as-code.py
python3 scripts/query-rules-as-code.py summary
python3 scripts/query-rules-as-code.py checks --text monotonicity --require-any
python3 scripts/query-rules-as-code.py families --text adjacent --require-any
```

Rule-pack solver checks:

```sh
cargo test -p axeyum-solver --test rules_as_code_examples
```

The interface stays explicit:

- every rule-pack check has an expected `sat`/`unsat`/`unknown`;
- every `sat` witness replays against the original rule model;
- every `unsat` either has a checker/proof route or is marked as evidence gap;
- every counterexample includes source citations.

## Capability Links

The lab should exercise and link to:

- [SMT Fragment Atlas](../atlas/README.md)
- [Proof Certificate Cookbook](../proof-cookbook/README.md)
- [capability matrix](../research/08-planning/capability-matrix.md)
- [support matrix](../research/08-planning/support-matrix.md)
- [trust ledger](../research/08-planning/trust-ledger.md)
- [P4 use-case frontend plan](../plan/track-4-usecases-frontend/README.md)

Likely Axeyum fragments:

- Bool and propositional structure;
- QF_LIA for thresholds, ages, dates, and incomes;
- QF_UF for abstract actors/resources;
- datatypes for enumerated statuses;
- arrays/relations for policy tables;
- optimization/minimization for smallest counterexamples.

## Graduation Criteria

The lab graduates from notes to a real sibling project when:

- at least three rule packs are implemented;
- every pack has executable checks;
- witnesses replay and are rendered in domain language;
- checks are linked to source citations;
- at least one pack compares a logical model to executable code;
- proof/evidence status is tracked per check;
- the lab has users outside Axeyum core development.

Until then, keep it as small Markdown examples plus focused tests.
