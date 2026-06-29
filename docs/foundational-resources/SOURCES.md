# Source Research Ledger

Research date: 2026-06-29.

This note records the sources used to plan the foundational-resource expansion.
The goal is not to ingest upstream content. The goal is to learn organization,
coverage, schema ideas, validation practices, and gaps that Axeyum can address
with small checkable artifacts.

## Local Context Inspected

- [formal mathematics curriculum](../curriculum/README.md)
- [curriculum graph](../curriculum/curriculum.toml)
- [depth and scope note](../curriculum/DEPTH.md)
- [curriculum backlog](../curriculum/BACKLOG.md)
- [formal mathematics tour](../research/08-planning/formal-mathematics-tour.md)
- [sibling project notes](../sibling-projects.md)
- [SMT Fragment Atlas](../atlas/README.md)
- [Proof Certificate Cookbook](../proof-cookbook/README.md)
- [Rules-as-Code Verification Lab](../rules-as-code/README.md)

## Web Sources

| Area | Source | Use For Expansion |
|---|---|---|
| Mathematics taxonomy | [MSC2020](https://mathscinet.ams.org/mathscinet/msc/msc2020.html) and [MSC2020 overview](https://msc2020.org/) | Broad field taxonomy for mathematical sciences; useful as a research-level cross-check, not as Axeyum's exact schema. |
| University curriculum | [MIT Mathematics department overview](https://catalog.mit.edu/schools/science/mathematics/) and [MIT Course 18 catalog](https://catalog.mit.edu/subjects/18/) | Sanity check that the field spine spans undergraduate and graduate pure/applied areas such as algebra, analysis, geometry, topology, combinatorics, numerical analysis, probability, and statistics. |
| Formal mathematics | [Lean mathlib overview](https://leanprover-community.github.io/mathlib-overview.html) and [mathlib4 docs](https://leanprover-community.github.io/mathlib4_docs/) | Coverage map for algebra, order, topology, analysis, probability, measure theory, tactics, and naming conventions. |
| Formal math tutorial | [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) | Chapter sequence for a proof-assistant-facing bridge from basics to algebra, topology, calculus, integration, and measure. |
| Formal proof library | [Isabelle Archive of Formal Proofs](https://www.isa-afp.org/) | Large-scale formalization categories and publication-style metadata. |
| Set-theoretic foundation | [Metamath Proof Explorer](https://us.metamath.org/mpeuni/mmset.html) | ZFC-to-number-systems dependency style and tiny-kernel proof culture. |
| SMT benchmarks | [SMT-LIB](https://smt-lib.org/) and [SMT-COMP](https://smt-comp.github.io/) | Logic/theory taxonomy, benchmark metadata, solver comparison discipline. |
| ATP benchmarks | [TPTP](https://www.tptp.org/) | First-order/higher-order theorem-proving problem taxonomy and status labels. |
| SAT benchmarks | [SATLIB](https://www.cs.ubc.ca/~hoos/SATLIB/) | Classic SAT benchmark family organization. |
| PL education | [Software Foundations](https://softwarefoundations.cis.upenn.edu/) | Computer-science proof curriculum structure: logic, programming languages, verification, and proof automation. |
| PL education | [Programming Language Foundations in Agda](https://plfa.github.io/) | Dependent-type and PL semantics curriculum shape. |
| Separation logic | [Iris project](https://iris-project.org/) | Concurrent separation-logic frontier and proof-mode organization. |
| Statistics education | [OpenIntro Statistics](https://www.openintro.org/book/os/) | Open statistics textbook coverage and pedagogical sequence. |
| Probabilistic programming | [Stan](https://mc-stan.org/), [PyMC](https://www.pymc.io/), [Pyro](https://pyro.ai/), [Turing.jl](https://turinglang.org/) | Model, inference, diagnostics, and probabilistic-programming vocabulary. |

## GitHub Search And Metadata

GitHub metadata was gathered with `gh search repos` and `gh repo view`.
Representative current repositories:

| Repository | Current Signal | Expansion Lesson |
|---|---|---|
| [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4) | Lean 4 mathematical library; GitHub metadata reports active updates and an Apache-2.0 license. | Use a hierarchical namespace and docs-generation model; map Axeyum concepts to formal-library areas without trying to mirror the library. |
| [leanprover-community/mathematics_in_lean](https://github.com/leanprover-community/mathematics_in_lean) | Tutorial repo with online book, Lean files, and exercises. | Pair prose with executable files and keep learner-facing copies separate from source material. |
| [math-comp/math-comp](https://github.com/math-comp/math-comp) | Mathematical Components for Rocq/Coq; active algebra/formalization library. | Algebraic hierarchy and finite-structure design are useful models for Axeyum's finite decidable examples. |
| [UniMath/UniMath](https://github.com/UniMath/UniMath) | Univalent mathematics library. | Mark foundations and proof-assistant horizons clearly; not all foundational material is solver-checkable. |
| [MetaRocq/metarocq](https://github.com/MetaRocq/metarocq) | Verified metatheory and implementation of Rocq in Rocq. | Candidate reference for future proof-kernel/metatheory resources, not an Axeyum near-term dependency. |
| [PrincetonUniversity/VST](https://github.com/PrincetonUniversity/VST) | Verified Software Toolchain. | Program-verification resource family should separate semantics, memory model, proof artifacts, and examples. |
| [DeepSpec/sf](https://github.com/DeepSpec/sf) | Software Foundations distribution repository. | CS resources should be sequenced as executable proof lessons, not only topic descriptions. |
| [SMT-LIB/SMT-LIB-db](https://github.com/SMT-LIB/SMT-LIB-db) | Tooling to build a database of SMT-LIB benchmarks and properties. | Axeyum resource catalogs should have machine-readable metadata, not only Markdown. |
| [stan-dev/stan](https://github.com/stan-dev/stan) | Stan language implementation; active Bayesian-inference repository. | Statistics resources need model-language, inference, diagnostics, and validation tracks. |
| [pymc-devs/pymc](https://github.com/pymc-devs/pymc) | Bayesian modeling and probabilistic programming in Python. | Probabilistic examples should distinguish model checking, inference diagnostics, and numerical approximation. |
| [pyro-ppl/pyro](https://github.com/pyro-ppl/pyro) | Deep universal probabilistic programming with PyTorch. | Use probabilistic-programming examples carefully; most inference is approximate, so Axeyum should focus first on finite/discrete checks. |
| [TuringLang/Turing.jl](https://github.com/TuringLang/Turing.jl) | Julia Bayesian inference and probabilistic-programming ecosystem. | Good vocabulary source for model/inference taxonomy, but not a proof target. |

## Shallow Clones Inspected

Ignored local shallow clones were created under `references/resource-*`:

- `resource-mathlib4`
- `resource-mathematics-in-lean`
- `resource-sf`
- `resource-smtlib-db`

These clones were used only to inspect repository layout, chapter/module names,
and metadata organization. They are ignored by `.gitignore` and should not be
committed.

## Main Findings

1. The existing Axeyum curriculum has a strong mathematics DAG, but it should
   become one lane inside a broader "foundational resources" ecosystem.
2. The mathematics lane needs a durable university-style field spine before
   concept rows sprawl. That spine is now recorded in
   [University Math Field Taxonomy](MATH-FIELDS.md).
3. Formal math libraries organize by hierarchy and namespace; Axeyum should
   organize by concept, solver fragment, evidence route, and example family.
4. CS resources need separate tracks for automata, computability, algorithms,
   programming languages, semantics, verification, concurrency, and systems.
5. Logic resources should bridge SAT/SMT/ATP/proof assistants: benchmark
   statuses, proof artifacts, theory support, and proof-reconstruction horizons.
6. Statistics resources require extra honesty: exact finite probability and
   symbolic checks are near-term; MCMC/VI/inference diagnostics are mostly
   numerical and should be treated as replayable experiments, not proof claims.
7. Every expansion should have a machine-readable row and a validation command
   before becoming user-facing documentation.
