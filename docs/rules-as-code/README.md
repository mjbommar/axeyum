# Rules-as-Code Verification Lab

The Rules-as-Code Verification Lab explores how Axeyum can help reason about
laws, policies, eligibility rules, compliance controls, and other structured
rule systems.

The goal is not automatic legal interpretation. The first goal is a disciplined
workflow for human-authored formalizations: cite the source rule, encode a small
logical model, check consistency and edge cases, replay counterexamples, and
state the trust boundary.

The lab now runs on real statute text. The
[Computer Fraud and Abuse Act V0](examples/cfaa-1030-v0/README.md) pack is
compiled from a machine-lifted copy of 18 U.S.C. § 1030
([Lifting the U.S. Code](uscode/README.md)): every rule is keyed to a provision
identifier, quotes the provision, and is checked against the section's
quantities, cross-references, and defined terms before any solver runs. The
seven earlier packs use invented rules and remain the place to exercise new
fragments.

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
    queries/
      authorization-policy-v0.json
      benefit-eligibility-v0.json
      category-equivalence-v0.json
      grant-allocation-v0.json
      procurement-scoring-v0.json
      tax-benefit-arithmetic-v0.json
      workflow-reachability-v0.json
      cfaa-1030-v0.json
    rules-query-dashboard.md
  examples/
    benefit-eligibility-v0/
    authorization-policy-v0/
    category-equivalence-v0/
    grant-allocation-v0/
    procurement-scoring-v0/
    tax-benefit-arithmetic-v0/
    workflow-reachability-v0/
    cfaa-1030-v0/          # real statute: rules.json, compiled.json, smt2/
  uscode/
    sources/               # GovInfo section renderings
    lifted/                # lifted provision graphs
artifacts/ontology/
  rules-core.schema.json
scripts/
  validate-rules-as-code.py
  query-rules-as-code.py
  uscode_lift.py
  uscode_query.py
  rules_ir.py
```

Current example packs:

- [Benefit Eligibility V0](examples/benefit-eligibility-v0/README.md)
- [Authorization Policy V0](examples/authorization-policy-v0/README.md)
- [Tax Benefit Arithmetic V0](examples/tax-benefit-arithmetic-v0/README.md)
- [Procurement Scoring V0](examples/procurement-scoring-v0/README.md)
- [Grant Allocation V0](examples/grant-allocation-v0/README.md)
- [Category Equivalence V0](examples/category-equivalence-v0/README.md)
- [Workflow Reachability V0](examples/workflow-reachability-v0/README.md)
- [Computer Fraud and Abuse Act V0](examples/cfaa-1030-v0/README.md), the first
  pack built from real statute text

## From U.S. Code To Checked Rules

```text
GovInfo section ──uscode_lift.py──▶ lifted provision graph ──rules_ir.py──▶ trace gate ──▶ SMT-LIB ──▶ Axeyum evidence
                                                   ▲                          │
                                       rules.json (provision-keyed)           └──▶ Python evaluation, witnesses, sweeps
```

- [`scripts/uscode_lift.py`](../../scripts/uscode_lift.py): GovInfo HTML to a
  provision tree with resolved cross-references, definitions, term uses, and
  quantities ([Lifting the U.S. Code](uscode/README.md)).
- [`scripts/uscode_query.py`](../../scripts/uscode_query.py): questions over the
  lifted section (`cited-by`, `cites`, `term`, `quantities`, `show`).
- [`scripts/rules_ir.py`](../../scripts/rules_ir.py): compiles a
  provision-keyed `rules.json` against the lifted section, refuses untraceable
  rules, evaluates fact patterns, and emits SMT-LIB obligations.
- `cargo run -q -p axeyum-solver --features full --example rules_check -- FILE.smt2…`:
  decides obligations and prints the evidence kind and re-check result.

## Roadmap

The detailed implementation plan lives in [ROADMAP.md](ROADMAP.md).

The math-resource reuse plan lives in
[Rules/Law Crosswalk For Foundational Resources](../foundational-resources/RULES-LAW-CROSSWALK.md).
It maps finite predicates, arithmetic thresholds, graph reachability,
precedence, and proof routes to concrete policy/rule checks.

The generated bounded-query surface lives in
[Rules Query Dashboard](generated/rules-query-dashboard.md). It reads the
committed rule-pack JSON, links deterministic generated query-row JSON under
[`generated/queries/`](generated/queries/), and counts the sample rows and
generated-query families that can become coverage, equivalence, threshold, cap,
and monotonicity checks.

The copyable downstream query guide lives in
[Rules/Law Resource Queries](../foundational-resources/RULES-LAW-QUERIES.md).
It uses `scripts/query-rules-as-code.py` to find coverage summaries, packs,
checked obligations, generated query families, and bounded rows from the
committed JSON boundary.

The current pattern matrix lives in
[Rules/Law Pattern Matrix](../foundational-resources/RULES-LAW-PATTERN-MATRIX.md).
It maps finite predicates, tenant relations, thresholds, monotonicity,
versioning, precedence, and bounded equivalence back to math concept rows,
proof routes, current packs, and copyable queries.

The learner-facing trust-boundary walkthrough is
[Rules/Law Trust Boundary](../learn/rules-law-trust-boundary.md). It explains
how to read a rule pack from source text through replayed witnesses and checked
obligations without treating the pack as legal advice or a solver benchmark.

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

The fourth pack,
[Procurement Scoring V0](examples/procurement-scoring-v0/README.md), reuses
finite predicates, bid caps, score thresholds, submission deadlines,
small-business bonus edge cases, monotonicity, and bounded
implementation-equivalence checks for a procurement award shape.

The fifth pack,
[Grant Allocation V0](examples/grant-allocation-v0/README.md), reuses exact
rational shares, budget-balance constraints, minimum program shares,
administrative caps, finite replay, and QF_LRA/Farkas evidence for an
allocation shape.

The sixth pack,
[Category Equivalence V0](examples/category-equivalence-v0/README.md), reuses
equivalence classes, finite functions, category normalization, and checked
QF_UF/Alethe rows for a role/category classification shape.

The seventh pack,
[Workflow Reachability V0](examples/workflow-reachability-v0/README.md),
reuses finite graph reachability, transition-system replay, terminal-state
guards, and checked Bool/QF_LIA rows for a workflow/state-machine shape.

The eighth pack,
[Computer Fraud and Abuse Act V0](examples/cfaa-1030-v0/README.md), models the
punishment clauses of 18 U.S.C. § 1030(c)(2)–(c)(4) and the civil action of
§ 1030(g). Its eight checks are all checked: four certified `unsat`
refutations (coverage, civil gate within the felony factors, monotonicity of
the maximum, implementation equivalence) and four replayed `sat` findings (the
(c)(2)(B)/(c)(2)(C) overlap, the "exceeds" versus "at least" $5,000 threshold
mismatch, the omission of factor (VI) from the civil gate, and a transcription
bug in a decision table).

Validate the current packs with:

```sh
python3 scripts/gen-rules-as-code-dashboard.py
python3 scripts/validate-rules-as-code.py
python3 scripts/query-rules-as-code.py summary
python3 scripts/query-rules-as-code.py coverage --by domain --require-any
python3 scripts/query-rules-as-code.py coverage --by validation --require-any
python3 scripts/query-rules-as-code.py coverage --by fragment --format json --require-any
python3 scripts/query-rules-as-code.py packs --pack category_equivalence_v0 --require-any
python3 scripts/query-rules-as-code.py packs --pack workflow_reachability_v0 --require-any
python3 scripts/uscode_lift.py docs/rules-as-code/uscode/sources/USCODE-2023-title18-partI-chap47-sec1030.htm docs/rules-as-code/uscode/lifted/usc-t18-s1030.json --check
python3 scripts/rules_ir.py docs/rules-as-code/examples/cfaa-1030-v0/rules.json --check
cargo test -p axeyum-solver --features full --test rules_as_code_examples
```
