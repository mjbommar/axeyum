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
  examples/
    benefit-eligibility-v0/
artifacts/ontology/
  rules-core.schema.json
scripts/
  validate-rules-as-code.py
```

The first example pack is
[Benefit Eligibility V0](examples/benefit-eligibility-v0/README.md).

## Roadmap

The detailed implementation plan lives in [ROADMAP.md](ROADMAP.md).

The math-resource reuse plan lives in
[Rules/Law Crosswalk For Foundational Resources](../foundational-resources/RULES-LAW-CROSSWALK.md).
It maps finite predicates, arithmetic thresholds, graph reachability,
precedence, and proof routes to concrete policy/rule checks.

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

Validate the current pack with:

```sh
python3 scripts/validate-rules-as-code.py
```
