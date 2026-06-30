# Rules-as-Code Verification Lab

The Rules-as-Code Verification Lab explores how Axeyum can help reason about
laws, policies, eligibility rules, compliance controls, and other structured
rule systems.

The goal is not automatic legal interpretation. The first goal is a disciplined
workflow for human-authored formalizations: cite the source rule, encode a small
logical model, check consistency and edge cases, replay counterexamples, and
state the trust boundary.

## Audience

- Engineers building policy or compliance engines.
- Researchers studying executable law and rules as code.
- Axeyum contributors looking for non-program-analysis applications.
- Domain experts who need concrete examples instead of solver internals.

## Planned Artifacts

```text
docs/rules-as-code/
  README.md
  ROADMAP.md
  generated/
    rules-query-dashboard.md
  examples/
    benefit-eligibility-v0/
    authorization-policy-v0/
    tax-benefit-arithmetic-v0/
artifacts/ontology/
  rules-core.schema.json
scripts/
  validate-rules-as-code.py
```

Current example packs:

- [Benefit Eligibility V0](examples/benefit-eligibility-v0/README.md)
- [Authorization Policy V0](examples/authorization-policy-v0/README.md)
- [Tax Benefit Arithmetic V0](examples/tax-benefit-arithmetic-v0/README.md)

## Roadmap

The detailed implementation plan lives in [ROADMAP.md](ROADMAP.md).

The math-resource reuse plan lives in
[Rules/Law Crosswalk For Foundational Resources](../foundational-resources/RULES-LAW-CROSSWALK.md).
It maps finite predicates, arithmetic thresholds, graph reachability,
precedence, and proof routes to concrete policy/rule checks.

The generated bounded-query surface lives in
[Rules Query Dashboard](generated/rules-query-dashboard.md). It reads the
committed rule-pack JSON and counts the sample rows and generated-query families
that can become coverage, equivalence, threshold, cap, and monotonicity checks.

## First Example Theme

Start with a small eligibility rule, not a full statute:

- applicant facts: age, income, residency, application date;
- rule output: eligible / ineligible / unknown;
- exceptions: disqualifying status or special override;
- temporal version: threshold changes on a date;
- checks: consistency, coverage, monotonicity, threshold cliff, implementation
  equivalence, and counterexample explanation.

This is enough to exercise the solver without pretending to parse natural
language law.

The second pack,
[Authorization Policy V0](examples/authorization-policy-v0/README.md), reuses
finite predicates, tenant/resource relations, precedence, and bounded
implementation-equivalence checks for a Cedar/OPA-style access-control shape.

The third pack,
[Tax Benefit Arithmetic V0](examples/tax-benefit-arithmetic-v0/README.md),
reuses integer thresholds, phase-out monotonicity, caps, effective-date
transitions, and bounded implementation-equivalence checks for a tax/benefit
arithmetic shape.

Validate the current packs with:

```sh
python3 scripts/validate-rules-as-code.py
python3 scripts/gen-rules-as-code-dashboard.py
cargo test -p axeyum-solver --test rules_as_code_examples
```
