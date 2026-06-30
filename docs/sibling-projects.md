# Sibling Project Notes

These notes collect possible sibling projects around Axeyum. They are not
commitments; they are a map of adjacent artifacts that could make Axeyum easier
to explain, measure, apply, or integrate.

The organizing principle is simple: incubate small knowledge and documentation
artifacts inside this repo first; split only when a sibling has an independent
audience, release cycle, corpus size, or dependency stack.

## What Counts As A Sibling

A sibling project should make one of these things more true:

- Axeyum is easier to learn.
- Axeyum's capabilities are easier to classify and compare.
- Axeyum's proof and trust story is easier to audit.
- Axeyum can be applied to important reasoning domains.
- Axeyum has clean upstream/downstream integration boundaries.

This includes educational content, machine-readable taxonomies, benchmark
observatories, proof corpora, symbolic-execution frontends, policy/law
reasoning tools, and reusable libraries.

## Incubate Here First

Keep a sibling inside the Axeyum repo while it is mostly:

- documentation;
- a schema or machine-readable artifact;
- tightly coupled to solver semantics, proof routes, or benchmarks;
- useful for CI, planning, capability tracking, or onboarding;
- small enough to review with ordinary Axeyum changes.

Good incubation locations:

```text
docs/atlas/                  # SMT/theory/solver taxonomy notes
docs/proof-cookbook/         # certificate and reconstruction guide
docs/rules-as-code/          # law/policy reasoning notes
docs/usecases/               # EVM, WASM, compiler validation, policy
artifacts/ontology/          # JSON/YAML/RDF-style capability/rule schemas
artifacts/examples/          # small curated examples, not huge corpora
```

Split into a separate repository only when the project becomes a standalone
app, a large corpus, a public course/site, or a library with a separate release
cycle.

## Detailed First-Incubator Roadmaps

The first step is to turn the top three incubators into concrete, reviewable
roadmaps before adding data, examples, or code. Each roadmap defines audience,
content structure, example shape, validation checks, Axeyum capability links,
and graduation criteria.

| Incubator | Folder | Detailed plan | First concrete output |
|---|---|---|---|
| SMT Fragment Atlas | [docs/atlas/](atlas/README.md) | [Atlas roadmap](atlas/ROADMAP.md) | [smt-fragments.json](../artifacts/ontology/smt-fragments.json) plus [schema](../artifacts/ontology/smt-fragments.schema.json) and [validator](../scripts/validate-smt-fragment-atlas.py). |
| Proof Certificate Cookbook | [docs/proof-cookbook/](proof-cookbook/README.md) | [Cookbook roadmap](proof-cookbook/ROADMAP.md) | Route-by-route recipes for tiny proof/evidence examples. |
| Rules-as-Code Verification Lab | [docs/rules-as-code/](rules-as-code/README.md) | [Rules-as-code roadmap](rules-as-code/ROADMAP.md) plus [rules/law crosswalk](foundational-resources/RULES-LAW-CROSSWALK.md) | [Benefit Eligibility V0](rules-as-code/examples/benefit-eligibility-v0/README.md) and [Authorization Policy V0](rules-as-code/examples/authorization-policy-v0/README.md) with citations, checks, replayed witnesses, schema, validator, checked Bool/QF_LIA rows, and math-resource reuse map. |

## Broader Foundational Resource Expansion

The next planning layer is
[Foundational Resource Expansion](foundational-resources/README.md): a
source-grounded roadmap for foundational mathematics, computer science, logic,
and statistics resources. It was researched with web search, GitHub metadata,
and shallow reference clones, then organized into source notes and a concrete
roadmap:

- [source research ledger](foundational-resources/SOURCES.md);
- [university math field taxonomy](foundational-resources/MATH-FIELDS.md);
- [expansion roadmap](foundational-resources/ROADMAP.md).
- [math resource buildout roadmap](foundational-resources/RESOURCE-BUILDOUT-ROADMAP.md).

This plan subsumes the earlier "Math Theory Library For Automation" idea into a
larger resource ecosystem with schemas, example packs, validators, proof/replay
status, and graduation criteria. The math lane is now explicitly grounded in
18 undergraduate/graduate fields, from logic, set theory, discrete math, graph
theory, number theory, and linear algebra through analysis, topology, measure,
probability, statistics, optimization, numerical analysis, dynamics, geometry,
and functional analysis.

## Families

### Core Knowledge

Taxonomies and reference artifacts that describe what Axeyum can reason about.

- SMT Fragment Atlas
- Solver Capability Ontology
- Proof Route Ontology
- Reasoning Knowledge Base
- Formal Semantics Cards

### Education

Material that teaches automated reasoning through Axeyum.

- Axeyum Academy
- Proof Certificate Cookbook
- Symbolic Execution Cookbook
- Reasoning Pattern Library
- Lean Certificate Gallery

### Measurement And Observability

Artifacts that make progress measurable and regressions visible.

- SMT-LIB Observatory
- Benchmark Fuzzer Lab
- Law/Policy Corpus Observatory
- Proof Debugger

### Developer Tooling

Tools that make Axeyum easier to inspect, connect, or embed.

- Axeyum Visualizer
- Counterexample UX Toolkit
- IR Adapter Suite
- Memory Model Library
- Solver-Aided DSL Framework

### Program Verification

Downstream projects where Axeyum powers concrete verification workflows.

- Rust Property SDK
- EVM Verification
- WASM Verification
- Compiler Optimization Validator
- Executable Standards Verifier

### Rules, Law, And Policy

Reasoning about laws and rules is adjacent to SMT/proof work: statutes,
regulations, authorization policies, compliance controls, tax/benefit formulas,
and data-governance policies all contain structured rules with exceptions,
precedence, temporal versions, and edge cases.

Useful solver-backed tasks include:

- consistency checking;
- detecting contradictory duties or permissions;
- finding uncovered cases;
- proving implementation equivalence to a rule specification;
- generating concrete edge-case examples;
- checking monotonicity and threshold cliffs;
- validating temporal effective-date transitions;
- explaining counterexamples with citations back to source clauses.

Candidate projects:

- Rules-as-Code Verification Lab
- Legal Document to Logic Pipeline
- Rules Ontology / Norm Graph
- Policy-as-Code Verifier
- Tax/Benefit Rule Engine Verifier
- Digital Rights / Data Policy Verifier
- Knowledge Graph Constraint Verifier

## Ranked Top 30

| Rank | Project | Type | Near-term placement | Why |
|---:|---|---|---|---|
| 1 | SMT Fragment Atlas | Taxonomy / data | `docs/atlas/`, `artifacts/ontology/` | Gives a machine-readable map of logics, operators, semantics, decision procedures, proof routes, benchmarks, and Axeyum status. |
| 2 | Proof Certificate Cookbook | Education / reference | `docs/proof-cookbook/` | Explains DRAT/LRAT, Alethe, Farkas, EUF congruence, Lean reconstruction, replay, and trust levels. |
| 3 | Axeyum Academy | Education | `docs/academy/` or `docs/learn/` first | A structured course from SAT to SMT to proofs to symbolic execution. |
| 4 | Rules-as-Code Verification Lab | Law/rules application | `docs/rules-as-code/` | Applies solver/proof workflows to statutes, benefits, eligibility, compliance, and administrative rules. |
| 5 | SMT-LIB Observatory | Benchmark platform | `bench-results/`, later separate | Tracks parse coverage, solve rate, proof coverage, disagreements, PAR-2, and dominance coverage over time. |
| 6 | Axeyum Visualizer | Tool / app | design notes first, later separate | Visualizes terms, rewrites, AIG/CNF, SAT models, proof DAGs, and replay failures. |
| 7 | Symbolic Execution Cookbook | Education / examples | `docs/usecases/symexec/` | Practical guide for path conditions, memory, CFGs, pruning, model witnesses, replay, and safety. |
| 8 | Legal Document to Logic Pipeline | Law/rules tooling | `docs/rules-as-code/` | Bridges structured legal documents and rule notations into checkable logic with citations back to source clauses. |
| 9 | Policy-as-Code Verifier | Policy application | `docs/usecases/policy/` first | Verifies Cedar/Rego-style authorization policies for conflicts, gaps, unintended permissions, and regressions. |
| 10 | Counterexample UX Toolkit | Library / UX | workspace crate later | Minimizes, renders, replays, and converts models into useful tests and reports. |
| 11 | IR Adapter Suite | Library family | workspace crates first | Connects SMT-LIB, BTOR2, TPTP, Lean, Why3, LLVM-like IRs, MIR-like IRs, WASM, and EVM. |
| 12 | Memory Model Library | Core-adjacent library | workspace crate | Reusable byte memory, word storage, stack/heap, endianness, aliasing, symbolic stores, and initialization models. |
| 13 | Lean Certificate Gallery | Proof corpus | `docs/proof-cookbook/` or `bench-results/` | Public corpus of generated Lean modules, axiom status, source formulas, replay results, and explanations. |
| 14 | Rules Ontology / Norm Graph | Ontology | `artifacts/ontology/` | Models obligations, permissions, prohibitions, exceptions, precedence, effective dates, actors, resources, and remedies. |
| 15 | Tax/Benefit Rule Engine Verifier | Law/rules app | `docs/rules-as-code/` first | Checks tax and benefit implementations for equivalence, monotonicity, cliffs, dead provisions, and examples. |
| 16 | Rust Property SDK | Downstream library | workspace crate | High-level symbolic inputs, assumptions, minimized counterexamples, evidence, and Lean artifacts for Rust users. |
| 17 | EVM Verification Sibling | Downstream app | workspace crate, maybe separate later | Handles storage, calldata, keccak-as-UF, ABI constraints, gas/path guards, and exploit witnesses. |
| 18 | WASM Verification Sibling | Downstream app | workspace crate, maybe separate later | WASM lifter plus symbolic executor and proof-backed safety/counterexamples. |
| 19 | Compiler Optimization Validator | Verification app | `docs/usecases/compiler/`, crate later | Alive2-like validation for rewrites and optimization over a small SSA IR, then larger compiler subsets. |
| 20 | Benchmark Fuzzer Lab | Testing / corpus | `crates/axeyum-bench`, `tests/` | Differential fuzzing against Z3/cvc5, shrinkers, hard-instance generators, and proof-reconstruction fuzzing. |
| 21 | Datalog / Static Analysis Bridge | Adapter / analysis | `docs/usecases/datalog/` first | Translates Datalog analyses to constraints/proofs for bounded checks, counterexamples, consistency, and synthesis. |
| 22 | Knowledge Graph Constraint Verifier | Data constraints | `docs/usecases/kg/` first | SHACL-like graph constraints compiled to SMT/proofs, with counterexample graph generation. |
| 23 | Digital Rights / Data Policy Verifier | Policy/law app | `docs/usecases/policy/` | Reasons about permissions, prohibitions, purpose, consent, retention, jurisdiction, and data sharing. |
| 24 | Formal Semantics Cards | Education / reference | `docs/reference/semantics/` | Short precise references for BV division, FP NaNs, arrays, quantifiers, strings, datatypes, legal exceptions, and temporal rules. |
| 25 | Reasoning Pattern Library | Examples | `artifacts/examples/` | Reusable patterns for overflow, aliasing, monotonicity, extensionality, eligibility, policy conflict, and access-control escalation. |
| 26 | Proof Debugger | Developer tool | design note first | Explains failed reconstruction: unsupported rule, bad replay, missing lemma, Lean kernel rejection, or trust gap. |
| 27 | Foundational Resource Expansion | Library / ontology / education | `docs/foundational-resources/`, `artifacts/ontology/`, `artifacts/examples/` | Groups, rings, orders, automata, PL semantics, logic benchmarks, finite probability, statistics, and proof horizons tied to solver/proof routes. |
| 28 | Solver-Aided DSL Framework | Library framework | separate only after prototype | Rosette-like framework for small DSLs with symbolic values, verification, synthesis, and counterexample lifting. |
| 29 | Executable Standards Verifier | Compliance app | `docs/usecases/standards/` | Encodes RFCs, protocol rules, file formats, and API contracts, then checks implementations or examples. |
| 30 | Law/Policy Corpus Observatory | Data platform | separate once large | Tracks formalization coverage, examples, conflicts, temporal versions, and provenance for legal/policy corpora. |

## Recommended First Incubators

Do not start 30 projects at once. Start with three small, compounding
incubators:

1. **SMT Fragment Atlas**
   - Folder: [docs/atlas/](atlas/README.md).
   - Plan: [Atlas roadmap](atlas/ROADMAP.md).
   - First artifact: [smt-fragments.json](../artifacts/ontology/smt-fragments.json)
     plus [schema](../artifacts/ontology/smt-fragments.schema.json) and
     [validator](../scripts/validate-smt-fragment-atlas.py).
   - Include: logic name, sorts, operators, semantic notes, decision route,
     proof route, benchmark rows, current Axeyum status.
   - Value: makes planning, docs, and capability reporting share one source.

2. **Proof Certificate Cookbook**
   - Folder: [docs/proof-cookbook/](proof-cookbook/README.md).
   - Plan: [Cookbook roadmap](proof-cookbook/ROADMAP.md).
   - First artifact: `docs/proof-cookbook/recipes/`.
   - Include: one tiny formula per certificate route, the emitted evidence, the
     checker, and the Lean reconstruction status.
   - Value: explains the trusted-small-checking identity better than prose.

3. **Rules-as-Code Verification Lab**
   - Folder: [docs/rules-as-code/](rules-as-code/README.md).
   - Plan: [Rules-as-code roadmap](rules-as-code/ROADMAP.md).
   - Crosswalk:
     [Rules/Law Crosswalk](foundational-resources/RULES-LAW-CROSSWALK.md).
   - First artifacts:
     [Benefit Eligibility V0](rules-as-code/examples/benefit-eligibility-v0/README.md)
     and [Authorization Policy V0](rules-as-code/examples/authorization-policy-v0/README.md)
     plus [rules-core schema](../artifacts/ontology/rules-core.schema.json)
     and [validator](../scripts/validate-rules-as-code.py).
   - Include: small eligibility and authorization rules with exceptions,
     precedence, temporal versions, and executable examples; show consistency,
     tenant isolation, implementation equivalence, and counterexample
     generation.
   - Value: tests whether law/policy reasoning can become a real Axeyum use
     case without polluting solver core.

After those exist, choose between the **Axeyum Visualizer** and
**Symbolic Execution Cookbook** depending on whether the biggest bottleneck is
debugging internals or onboarding users.

## Graduation Criteria

A sibling should split out of this repo only when most of these are true:

- it has users who do not need the Axeyum source tree;
- it has dependencies that should not affect core CI;
- it has a separate release cadence;
- it owns large generated data or corpora;
- it needs independent issue tracking;
- it can depend on Axeyum as a library instead of reaching into internals.

Until then, keep it close and boring: Markdown notes, small machine-readable
artifacts, focused examples, and links from the main docs.
