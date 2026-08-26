# Axeyum overall vision and status review

Date: 2026-08-26  
Repository checkpoint: `c75ff8af5a9b7907abdde01873ef656d8f716da8`

This review starts from executable code, generated artifacts, and recent Git
history. Documentation is used to explain contracts, not as evidence that a
capability exists. The action plan is
[`top-three-focus-plan-2026-08.md`](top-three-focus-plan-2026-08.md).

## The product thesis

Axeyum should be understood as an **evidence-native reasoning runtime**, not as
a smaller clone of Lean, Z3, or Mathematica.

Its unit of durable value is a result with a precise typed statement, an
identified search route, independently checkable evidence appropriate to that
route, explicit assumptions and provenance, and graph identity that lets the
result become input to later search.

Fast solvers, CAS algorithms, proof agents, LLMs, Mathlib, and external tools
may all propose or supply material. Axeyum's distinctive responsibility is to
keep proposal, checking, admission, and durable knowledge separate. The
long-horizon bet is that this connective tissue can turn heterogeneous
reasoners into a compounding system without asking users to trust the most
complex component.

## What exists in code

### Reasoning spine

The workspace contains 22 product crates. The main path is real:

```text
typed IR and query
  -> rewrite and planning
  -> theory dispatch or BV -> AIG -> CNF -> SAT
  -> sat / unsat / unknown plus route metadata
  -> original-query model replay or route-specific evidence checking
```

The default solver build is pure Rust. `unknown` is a first-class result.
Original-query replay survives query slicing and lowering. The full solver has
substantial implementations for BV, arrays, EUF, arithmetic, floating point,
datatypes, bounded strings, quantifiers, interpolation, optimization, and
selected combinations. The WASM crate runs scalar QF_BV in a browser; Python
exposes typed IR, solving, replay, and bounded proof producers.

This is broad working code, but not uniform solver maturity. The committed
scoreboard has 35 baselines over 24 logic fragments and decides 762 of 992
files, with 674 oracle comparisons and no recorded disagreement. That is useful
bounded regression evidence, not SMT-LIB-wide parity or a representative
industrial benchmark result.

### Checking and mathematical library

`axeyum-lean-kernel` implements an independent Rust Lean-core profile with
universes, dependent terms, reduction, definitional equality, inductives,
recursors, declaration admission, dependency inspection, and axiom footprints.
`axeyum-lean-import` keeps the untrusted `lean4export` reader outside that
kernel and rejects unsupported or contaminated streams explicitly.

The generated current projection measures:

- 1,600 declarations;
- 1,246 theorems;
- 251 definitions;
- 29 constructors, 22 inductives, and 22 recursors;
- 30 declared axioms, all in the retained `AxReal` negative-control package;
- 1,570 declarations with an empty measured footprint; and
- 7,108 direct theorem-dependency edges.

The constructive Nat, Int, Rat, CReal, Complex, logic, and string packages have
zero measured trusted declarations. This is a narrower, differently engineered
foundation than Mathlib, not evidence that Axeyum is globally “more sound.”
Mathlib has vastly greater elaborator, tactic, library, and community coverage;
Axeyum has unusually explicit route-local footprint measurement and an
independent implementation.

### Evidence and consumers

The solver contains multiple evidence families rather than one boolean
“certified” flag: model replay, DRAT/CNF checking, Farkas and arithmetic
certificates, Alethe routes, solver-to-kernel reconstruction, CAS-local exact
checks, and domain-specific witness replay. The bounded Rust verifier,
property-testing SDK, EVM analysis, scenarios, Python package, and WASM surface
exercise the substrate as consumers.

This is a strength only when every route states its own assurance. A checked BV
model does not certify an unrelated CAS result, and an independently admitted
Lean theorem does not upgrade a proofless SMT route.

### Knowledge and autonomous loop

The ledger contains 696 propositions: 502 proved, 4 refuted, 2 computed, 185
open, and 3 conjectured. Validation re-derives evidence and reports 603 rows
with two or more independent checks. The lemma index covers all 1,246 kernel
theorems and 7,108 direct edges, but only 395 theorems link exactly to 390
ledger facts; 851 kernel theorems have no exact fact link.

The operation registry, typed producer declines, agent episodes, held-out
partitions, candidate capsules, second-kernel checks, and crash-safe ledger
transaction are real. Reusable production has settled an 11-fact population,
and an admitted result has changed later scheduling. The stronger autonomous
compounding claim remains small:

- an earlier fixed reflexivity grammar accepted 2 of 138 checked type slices;
- proof-isolated bounded application accepted 6 of 109 already settled Nat
  controls; and
- the same search over 80 genuinely open/conjectured arrow-free statements
  with one target-independent elementary palette accepted 0.

Of those 80, 37 reached search and returned `NoTypedApplication`; 43 failed
closed because the direct statement capsule reached an unlisted theorem,
axiom, or quotient declaration. The existing ADR-0484 type-slice route—not a
weaker importer—handles that second class by generalization and exact checked
specialization. The remaining problem is productive proof search and semantic
contracts, not merely transport.

## Comparative position

The comparisons below use the neighbors' own stated capabilities as context;
Axeyum's side is based on the code and artifacts above.

| Neighbor | Neighbor's mature center | Axeyum's real advantage | Axeyum's real deficit |
|---|---|---|---|
| Lean + Mathlib | Interactive dependent-type proving, elaboration, tactics, IDEs, and an enormous maintained library | Independent Rust checking, route-local footprint/dependency measurement, and integration with solver/CAS evidence | No comparable elaborator, tactic ecosystem, IDE, library scale, compatibility, or community |
| Z3 / cvc5 | Decades of optimized SMT algorithms, theory combination, quantifier heuristics, proof production, APIs, and industrial use | Pure-Rust default, original-query replay as a product contract, and a route from heterogeneous evidence into a durable theorem ledger | Lower performance and coverage; uneven proof portability; limited public-corpus evidence; many incomplete fragments |
| Isabelle + Sledgehammer | Mature interactive proving, premise selection, ATP orchestration, proof reconstruction, and user workflow | More explicit machine-readable operations, episodes, provenance, and autonomous-production accounting | No similarly mature premise selection, simplifier, proof language, IDE, or broad reconstruction yield |
| Metamath | Extremely small stable verification language, tens of thousands of proofs, and several independent verifiers | Rich typed computation, solvers, evidence routes, and program-analysis consumers in one runtime | A much larger and younger checking implementation, far smaller library, and fewer independent kernel implementations |
| AlphaProof/AlphaGeometry/learned agents | Large-scale learned search and strong benchmark performance in selected mathematical domains | Model-independent authority: deterministic producers and LLMs cross the same fail-closed checker and transaction boundary | No learned premise selector or search system with comparable conversion rate, training scale, or benchmark result |
| Specialist CAS and program analyzers | Deep algorithms and polished workflows within one domain | Common provenance and checking vocabulary across symbolic math, SMT, proofs, and program witnesses | Many integrations are shallow relative to specialists; breadth increases maintenance and product-surface complexity |

Primary external references: [Lean documentation](https://lean-lang.org/lean4/doc),
[Z3 Guide](https://microsoft.github.io/z3guide/),
[cvc5 documentation](https://cvc5.github.io/docs/latest/),
[Isabelle documentation](https://isabelle.in.tum.de/documentation.html),
[Metamath](https://us.metamath.org/), and
[Google DeepMind's AlphaProof report](https://deepmind.google/blog/ai-solves-imo-problems-at-silver-medal-level/).

## Strongest parts

1. **Trust-boundary engineering.** Search is untrusted; admissions are checked;
   footprints come from the environment; malformed, unsupported, budgeted, and
   contaminated cases decline rather than inherit a stronger claim.
2. **Evidence connective tissue.** Terms, source models, lowering maps,
   certificates, theorem dependencies, fact identities, operations, and
   episodes are retained as first-class artifacts.
3. **Breadth without a mandatory native solver.** A pure-Rust path supports
   embedding, Python, bounded verification, and browser execution while native
   solvers remain optional oracles.
4. **Honest experimental method.** Exact hashes, immutable external corpora,
   mutation controls, held-out partitions, negative results, and separate
   production credit make it difficult to inflate progress accidentally.
5. **A nontrivial independent mathematical base.** The kernel is no longer a
   toy checker and the constructed arithmetic tower is meaningful work.

## Weakest parts

1. **Autonomous conversion, by a wide margin.** Architecture and checking are
   ahead of premise selection and proof construction. Zero of the latest 80
   open targets converted under the fixed baseline.
2. **Graph connectivity and semantic availability.** Two thirds of kernel
   theorems lack exact fact links. Type slices often erase the behavior a proof
   needs, so checked local contracts and retrieval must reconnect meaning to
   search without leaking source proofs.
3. **Specialist depth and product focus.** Twenty-two crates and many evidence
   routes create a large integration surface. Each specialist surface is less
   complete than its dedicated neighbor, and there is no single polished
   workflow that demonstrates why a user should choose the whole stack today.
4. **Compatibility and independent validation.** The Lean importer is pinned
   to a selected Lean 4.30/export profile; the custom kernel does not implement
   the full Lean system; most of its library has not been reproduced by
   multiple independent kernel implementations.
5. **Benchmark authority.** Current scoreboards are excellent regressions but
   too small and selected to establish broad parity, performance, or proof
   coverage.

## The three priorities

### 1. Prove autonomous reusable production

Use the existing exact-goal and type-slice boundaries to build dependency-
ranked premise selection, checked semantic contracts, and bounded proof-plan
composition. Measure on frozen open populations. Register authority only after
one unchanged operation proves at least three previously open siblings, and
require one new result in the checked proof closure of a later result.

### 2. Make the theorem graph operational

Connect kernel theorems, fact identities, concepts, semantic contracts,
producer capabilities, declines, and reverse consumers into one queryable
substrate. Mechanical identity is automatic; semantic links are reviewed;
missing links remain explicit. Optimize for “what checked premises and
strategies can attack this exact open goal?” rather than catalog size.

### 3. Establish one compelling integrated product path

Choose a narrow workflow where the full architecture matters—for example,
bounded Rust verification or proof-carrying SMT-to-Lean reconstruction—and make
installation, API, evidence inspection, reproduction, CI, and failure
diagnostics excellent. Publish larger public comparisons with route-specific
assurance. Let success there decide which solver/CAS/prover depth to build next.

## Bottom line

Axeyum is an unusually ambitious and technically real reasoning stack. Its most
defensible innovation is not a new logic or a larger theorem count; it is the
attempt to make heterogeneous reasoning compound through small checking,
explicit evidence, and durable graph state.

The architecture is credible. The checking discipline is often excellent. The
autonomous flywheel is not yet demonstrated at useful scale. The next era of
the project should be judged primarily by new open facts proved by reusable
operations and then consumed by later proofs—not by additional manually written
theorems, solver fragments, or metadata in isolation.
