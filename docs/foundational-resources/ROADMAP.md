# Foundational Resource Expansion Roadmap

## Charter

Build a comprehensive sibling-resource ecosystem for foundational mathematics,
computer science, logic, and statistics. The ecosystem should be useful to
learners, solver contributors, proof contributors, and downstream application
builders.

This is not a plan to import Mathlib, Software Foundations, Stan, or SMT-LIB.
It is a plan to build Axeyum-native maps, examples, schemas, and validators
that connect those worlds to Axeyum's strengths:

```text
untrusted fast search, trusted small checking
```

## Non-Goals

- Replacing textbooks, formal libraries, or benchmark libraries.
- Scraping upstream content into this repository.
- Treating approximate statistics or machine-learning inference as proof.
- Claiming a general theorem when Axeyum only checks bounded instances.
- Expanding public solver surface without proof/replay/checker obligations.

## Audiences

| Audience | Needs |
|---|---|
| Learner | A path from logic and examples to formal proof and solver evidence. |
| Solver contributor | Concept families that become meaningful benchmark and fuzz corpora. |
| Proof contributor | Clear Lean-horizon targets and certificate routes per concept. |
| Educator | Small runnable examples with honest limitations. |
| Application builder | Patterns for rules, programs, policies, data, and statistics. |

## Artifact Families

### 1. Foundational Concept Atlas

Purpose: one machine-readable map from concepts to prerequisites, decidability,
Axeyum fragments, example families, proof routes, and source references.
For mathematics rows, the authoritative field spine is
[University Math Field Taxonomy](MATH-FIELDS.md).

Near-term files:

```text
docs/foundational-resources/
  README.md
  SOURCES.md
  MATH-FIELDS.md
  MATH-CURRICULUM-BUILDOUT.md
  ROADMAP.md
  generated/
artifacts/ontology/
  foundational-concepts.schema.json
  foundational-concepts.json
  foundational-example-pack.schema.json
artifacts/examples/math/
  template-v0/
  logic-basics-v0/
  finite-predicate-v0/
  proof-methods-refutation-v0/
  induction-obligations-v0/
  finite-sets-v0/
  relations-functions-v0/
  finite-cardinality-v0/
  natural-arithmetic-v0/
  integer-lia-v0/
  gcd-bezout-v0/
  modular-arithmetic-v0/
  number-theory-v0/
  rationals-lra-v0/
  reals-rcf-shadow-v0/
  sequence-limit-shadow-v0/
  metric-continuity-v0/
  calculus-algebraic-shadow-v0/
  linear-algebra-rational-v0/
  numerical-linear-algebra-v0/
  spectral-linear-algebra-v0/
  matrix-invariants-v0/
  random-matrix-finite-v0/
  finite-markov-chain-v0/
  exact-statistical-tests-v0/
  finite-groups-v0/
  finite-rings-v0/
  finite-fields-v0/
  polynomial-identities-v0/
  counting-v0/
  graph-coloring-v0/
  finite-probability-v0/
  descriptive-statistics-v0/
  linear-optimization-v0/
  coordinate-geometry-v0/
  finite-topology-v0/
  finite-compactness-v0/
  finite-connectedness-v0/
  finite-measure-v0/
  bounded-dynamics-v0/
  finite-operator-v0/
  complex-algebraic-v0/
scripts/
  gen-foundational-concepts.py
  validate-foundational-concepts.py
  gen-foundational-dashboards.py
  validate-foundational-example-pack.py
```

Seed from:

- [curriculum graph](../curriculum/curriculum.toml)
- [SMT Fragment Atlas](../atlas/README.md)
- [Proof Certificate Cookbook](../proof-cookbook/README.md)
- [Rules-as-Code Verification Lab](../rules-as-code/README.md)

Required row fields:

- stable id and title;
- domain: mathematics, computer-science, logic, statistics;
- prerequisites and unlocks;
- decidability class: decidable, computable, bounded, numerical, proof-horizon;
- Axeyum fragment links;
- example pack links;
- proof/evidence status;
- upstream source references;
- graduation criteria.

### 2. Mathematics Expansion

Current base: [formal mathematics curriculum](../curriculum/README.md).
Field spine: [University Math Field Taxonomy](MATH-FIELDS.md).
Detailed execution plan:
[Math Curriculum Resource Buildout Plan](MATH-CURRICULUM-BUILDOUT.md).

Add depth in four waves:

| Wave | Content | Axeyum Slice | First Artifacts |
|---|---|---|---|
| M1 | Rational and real algebra | LRA, NRA, exact rational witnesses | rationals and reals example packs; Farkas/SOS proof links |
| M2 | Algebraic hierarchy | finite groups/rings/fields, finite fields | Cayley-table validators; finite-field examples |
| M3 | Linear algebra | fixed matrices over `Q` and finite fields | matrix identity and linear-system packs |
| M4 | Probability and measure foundations | finite probability first; measure theory as proof horizon | finite distribution examples; statistics bridge |

Practical first backlog:

1. `foundational-concepts.json` rows for all existing curriculum nodes.
2. `field_id` validation against the 18 fields in
   [MATH-FIELDS.md](MATH-FIELDS.md).
3. Graph coloring examples with coloring witnesses and unsat/proof-route status.
4. Rational density and trichotomy examples, backed by LRA evidence.
5. Finite-field inverse examples over small primes.
6. Matrix inverse, LU, residual bounds, interval boxes, iterative-method error
   replay, and inconsistent linear system examples with Farkas evidence where
   applicable.
7. Finite probability examples: total mass, conditional probability table,
   Bayes rule over finite domains.

Boundary:

- calculus, topology, measure theory, and general infinite-cardinality facts
  remain Lean-horizon unless reduced to algebraic/finite checks.

### 3. Computer Science Foundations

Add a CS resource track parallel to the math curriculum:

| Track | Concepts | Axeyum Slice | Example Types |
|---|---|---|---|
| Automata and languages | DFA/NFA, regex, minimization, product automata | BV, finite sets, SAT | equivalence, emptiness, counterexample strings |
| Computability and complexity | decidability, reductions, NP, SAT | educational/proof horizon | reductions as finite artifacts |
| Algorithms | sorting, search, graph reachability, shortest paths | BV/LIA, finite graphs | counterexample generation, invariant checks |
| Programming languages | lambda calculus, operational semantics, type systems | finite-step semantics, proof horizon | small-step traces, preservation/progress finite slices |
| Compilers | SSA, optimizations, refinement | BV, arrays, memory model | Alive2-style rewrite validation |
| Concurrency and distributed systems | interleavings, locks, consensus sketches | bounded model checking | schedules and replayed traces |
| Security and cryptography | finite protocols, access control, toy crypto | BV, UF, arrays | attack witnesses, equivalence checks |

First artifacts:

```text
docs/foundational-resources/cs/
  automata-roadmap.md       # planned
  pl-semantics-roadmap.md   # planned
  algorithms-roadmap.md     # planned
artifacts/examples/cs/
  dfa-equivalence-v0/       # planned
  sorting-network-v0/       # planned
```

Validation rule: every CS example must have either a replayed witness trace or
a checked `unsat`/safety certificate.

### 4. Logic And Proof Resources

Connect SAT, SMT, ATP, proof assistants, and proof certificates.

| Track | Source Models | Axeyum Role |
|---|---|---|
| SAT | SATLIB, DIMACS, proof traces | CNF, DRAT/LRAT, proof replay |
| SMT | SMT-LIB, SMT-COMP, SMT-LIB-db | fragment atlas, benchmark metadata, proof coverage |
| ATP | TPTP | first-order/higher-order status vocabulary and problem taxonomy |
| Proof assistants | Lean, Rocq/Coq, Isabelle, Metamath | proof-horizon targets and kernel-checkable reconstruction |
| Separation logic | Iris, VST | program-verification frontier and proof explanation examples |

First artifacts:

1. Extend the [Proof Certificate Cookbook](../proof-cookbook/README.md) with:
   - CNF/LRAT recipe;
   - QF_LIA Diophantine recipe;
   - datatype structural recipe;
   - proof failure/debugging recipe.
2. Add a logic-problem status schema:
   - problem family;
   - expected status;
   - required solver fragment;
   - evidence route;
   - replay/proof command.
3. Add a small "SAT to SMT to Lean" lesson path in `docs/learn/`.

### 5. Statistics And Probability Resources

Statistics needs a separate honesty model because much of the practical stack
is approximate.

| Layer | Content | Axeyum Slice | Trust Story |
|---|---|---|---|
| Finite probability | probability mass functions, events, conditioning | rational arithmetic, finite sums | exact replay/check |
| Descriptive statistics | mean, variance, covariance, contingency tables | LRA/LIA/BV | exact calculation and invariant checks |
| Statistical tests | simple exact tests, binomial tails | bounded arithmetic | exact for small finite domains |
| Bayesian models | conjugate finite examples first | rational arithmetic, finite enumeration | posterior table replay |
| Probabilistic programs | finite discrete traces | symbolic execution / enumeration | trace replay and normalization check |
| MCMC/VI diagnostics | Stan/PyMC/Pyro/Turing vocabulary | numerical experiment docs | not proof; reproducibility checks only |
| Causal inference | DAGs, d-separation, adjustment sets | finite graph algorithms | witness paths and blocked-path checks |

First artifacts:

```text
docs/foundational-resources/statistics/
  probability-roadmap.md       # planned
  bayesian-roadmap.md          # planned
  causal-roadmap.md            # planned
artifacts/examples/math/
  finite-probability-v0/       # landed
  descriptive-statistics-v0/   # landed
```

First concrete examples:

1. Finite probability mass table sums to one.
2. Bayes rule over a two-by-two diagnostic-test table.
3. Mean/variance identity for a small integer data set.
4. Simpson's paradox witness table.
5. Causal d-separation witness in a tiny DAG.

Boundary:

- MCMC, HMC, variational inference, floating-point diagnostics, and model
  calibration are not proof claims. Treat them as reproducible experiments with
  seeds, tolerances, and explicit numerical assumptions.

## Cross-Cutting Schemas

### Foundational Concept Row

Planned minimal JSON shape:

```json
{
  "id": "finite_probability",
  "domain": "statistics",
  "title": "Finite Probability",
  "prerequisites": ["sets", "rationals"],
  "decidability": "computable",
  "axeyum_fragments": ["Bool", "QF_LRA"],
  "example_packs": ["artifacts/examples/statistics/finite-bayes-table-v0"],
  "proof_routes": ["replay", "Farkas when encoded as LRA"],
  "source_refs": ["OpenIntro Statistics", "Mathlib probability"],
  "open_gaps": ["No shared foundational-concepts validator yet"]
}
```

### Example Pack Requirements

Every example pack should include:

- `README.md`;
- `metadata.json`;
- `model.md`;
- `checks.md`;
- `expected.json`;
- validator command;
- source references;
- proof/evidence status per check;
- graduation criteria.

This deliberately mirrors the first
[rules-as-code pack](../rules-as-code/examples/benefit-eligibility-v0/README.md).

## Phased Plan

### Phase F0: Source-Grounded Inventory

Status: this planning note.

Exit criteria:

- Record source ledger with web/GitHub/clone evidence.
- Identify domains and artifact families.
- Link the plan from docs navigation and sibling notes.

### Phase F1: Foundational Concept Atlas MVP

Status: first math seed landed. The atlas currently validates 23 curriculum
rows and 18 math-field rows; example-pack schemas and validated packs are still
Phase F2 work.

Exit criteria:

- Add `foundational-concepts.schema.json`. **Done for the math seed.**
- Generate `foundational-concepts.json` from existing curriculum nodes plus the
  first math-field rows from [MATH-FIELDS.md](MATH-FIELDS.md) and first
  CS/statistics/logic rows. **Done for the 23 curriculum rows and 18 math-field
  rows; CS/statistics-specific non-math rows remain future work.**
- Validate math `field_id` values against the university field taxonomy.
  **Done.**
- Add dependency/acyclicity/link validator. **Done for atlas row links and
  curriculum prerequisites/unlocks.**
- Document which rows are decidable, bounded, numerical, or proof-horizon.
  **Done in the JSON and generated dashboards.**

### Phase F2: Mathematics Deepening

Status: example-pack schema and validating template scaffold landed; the first
substantive packs,
[`logic-basics-v0`](../../artifacts/examples/math/logic-basics-v0/),
validates propositional SAT witness replay, tautology/contradiction truth-table
checks, De Morgan equivalence, and a tiny CNF refutation.
[`proof-methods-refutation-v0`](../../artifacts/examples/math/proof-methods-refutation-v0/),
now validates with a SAT witness control case and a checked deterministic
CNF truth-table refutation for `PHP(3,2)`.
[`induction-obligations-v0`](../../artifacts/examples/math/induction-obligations-v0/)
validates bounded induction base, step, and conclusion obligations with the
full induction schema kept as a Lean-horizon row.
[`finite-cardinality-v0`](../../artifacts/examples/math/finite-cardinality-v0/)
validates finite bijection replay, proper-subset injection replay, exhaustive
finite injection/surjection refutations, and an infinite-cardinality
Lean-horizon row.
[`modular-arithmetic-v0`](../../artifacts/examples/math/modular-arithmetic-v0/)
also validates with replayed CRT/inverse witnesses and exhaustive finite
non-invertibility/Fermat-style checks.
[`rationals-lra-v0`](../../artifacts/examples/math/rationals-lra-v0/)
validates exact rational density, additive inverse, trichotomy, and transitivity
checks without floating-point arithmetic.
[`metric-continuity-v0`](../../artifacts/examples/math/metric-continuity-v0/)
validates finite Lipschitz, epsilon-delta, and open-ball preimage checks with
exact rational metrics, plus checked rejection of an overlarge delta.
[`linear-algebra-rational-v0`](../../artifacts/examples/math/linear-algebra-rational-v0/)
validates exact rational matrix-vector replay, LU factorization replay, and a
row-scaling inconsistency certificate for a singular system.
[`numerical-linear-algebra-v0`](../../artifacts/examples/math/numerical-linear-algebra-v0/)
validates exact residual bounds, rational solution boxes, Jacobi one-step
contraction replay, and checked rejection of a false residual bound.
[`spectral-linear-algebra-v0`](../../artifacts/examples/math/spectral-linear-algebra-v0/)
validates exact finite eigenpair replay, orthogonal eigenbasis checks,
Rayleigh quotients, spectral decomposition replay, and checked rejection of a
false eigenpair.
[`matrix-invariants-v0`](../../artifacts/examples/math/matrix-invariants-v0/)
validates exact trace/determinant characteristic-polynomial replay,
characteristic roots, Cayley-Hamilton replay, finite Gershgorin intervals, and
checked rejection of a false characteristic polynomial.
[`finite-compactness-v0`](../../artifacts/examples/math/finite-compactness-v0/)
validates finite open-cover/subcover checks, minimal subcover enumeration,
finite-intersection families, bad-cover rejection, and a compactness
Lean-horizon row.
[`finite-connectedness-v0`](../../artifacts/examples/math/finite-connectedness-v0/)
validates finite connectedness via clopen-subset enumeration, open separations,
bad-connected-claim rejection, and a connectedness Lean-horizon row.
[`random-matrix-finite-v0`](../../artifacts/examples/math/random-matrix-finite-v0/)
validates exact finite random-matrix moments, expected Gram matrices, rank
probabilities, and checked rejection of a false trace-square moment.
[`finite-markov-chain-v0`](../../artifacts/examples/math/finite-markov-chain-v0/)
validates exact stochastic matrices, finite-horizon distribution evolution,
stationary distributions, and checked rejection of a malformed transition row.
[`exact-statistical-tests-v0`](../../artifacts/examples/math/exact-statistical-tests-v0/)
validates exact binomial tails, hypergeometric point probabilities, one-sided
Fisher p-values, and checked rejection of a false p-value.
[`graph-coloring-v0`](../../artifacts/examples/math/graph-coloring-v0/)
validates finite graph coloring witnesses, invalid-coloring replay, and an
exhaustive two-colorability refutation for `K3`.
[`graph-reachability-v0`](../../artifacts/examples/math/graph-reachability-v0/)
validates finite BFS shortest-distance replay, deterministic DFS traversal
replay, disconnected no-path refutation, and edge-cut separation replay.
[`graph-matching-v0`](../../artifacts/examples/math/graph-matching-v0/)
validates finite matching witnesses, invalid-overlap rejection, augmenting-path
flip replay, and a perfect-matching obstruction by exhaustive enumeration.
[`graph-d-separation-v0`](../../artifacts/examples/math/graph-d-separation-v0/)
validates finite DAG d-separation checks for chains, forks, colliders, and
descendant-opened colliders.
[`graph-cut-v0`](../../artifacts/examples/math/graph-cut-v0/)
validates finite minimum edge-cut and vertex-cut certificates, plus checked
rejection of non-separating one-edge and one-vertex cuts.
[`finite-probability-v0`](../../artifacts/examples/math/finite-probability-v0/)
validates exact finite probability mass tables, conditional probability, and
Bayes posterior replay.
[`descriptive-statistics-v0`](../../artifacts/examples/math/descriptive-statistics-v0/)
validates exact mean/variance identities, contingency-table margins, and a
Simpson's paradox count-table witness.
[`linear-optimization-v0`](../../artifacts/examples/math/linear-optimization-v0/)
validates exact LP feasibility witnesses, objective-threshold replay, and a
tiny checked Farkas infeasibility certificate.
[`coordinate-geometry-v0`](../../artifacts/examples/math/coordinate-geometry-v0/)
validates exact midpoint, collinearity, and squared-distance coordinate checks.
[`finite-topology-v0`](../../artifacts/examples/math/finite-topology-v0/)
validates finite topology axioms, closure/interior computation, and exact finite
metric-ball replay.
[`finite-measure-v0`](../../artifacts/examples/math/finite-measure-v0/)
validates finite sigma-algebra axioms, exact finite additivity, and
event/complement measure replay.
[`bounded-dynamics-v0`](../../artifacts/examples/math/bounded-dynamics-v0/)
validates exact rational recurrence traces, bounded invariant witnesses, and
threshold reachability replay.
[`finite-operator-v0`](../../artifacts/examples/math/finite-operator-v0/)
validates exact finite-dimensional norm, matrix-operator, and Chebyshev
recurrence checks.
[`complex-algebraic-v0`](../../artifacts/examples/math/complex-algebraic-v0/)
validates exact complex arithmetic, conjugate/norm replay, and a fixed
polynomial-root witness using real-pair algebra.

Exit criteria:

- At least five new math example packs.
- At least two use checked solver evidence, not only witness replay.
- At least one finite spectral-linear-algebra pack validates eigenpair and
  decomposition claims while keeping general spectral theorems on the proof
  horizon.
- Curriculum status/backlog updated from the new examples.

### Phase F3: CS Foundations Track

Exit criteria:

- DFA equivalence pack with counterexample strings and `unsat` equivalence
  checks.
- Sorting-network or small algorithm-correctness pack.
- PL small-step trace pack with replayed traces and explicit proof gaps.

### Phase F4: Logic And Proof Track

Exit criteria:

- Proof cookbook covers LRAT, Diophantine, datatype, and proof-debug recipes.
- A tiny SAT/SMT/Lean lesson path exists under `docs/learn/`.
- Logic-problem status schema validates at least ten examples.

### Phase F5: Statistics And Probability Track

Exit criteria:

- Finite probability and Bayes-table packs validate.
- Finite Markov-chain stochastic-matrix and finite-horizon evolution checks
  validate exactly.
- Descriptive-statistics invariants validate exactly.
- Exact finite statistical-test p-values validate as rational finite sums.
- The first finite random-matrix bridge validates exact matrix-valued
  probability tables without asymptotic or floating-point claims.
- Numerical/probabilistic-programming material has an explicit "not proof"
  status and reproducibility metadata.

### Phase F6: Generated Views And Graduation

Exit criteria:

- Generate a dashboard table by domain and decidability class.
- Cross-link foundational concepts to SMT Fragment Atlas rows and proof recipes.
- At least one validator runs in the normal docs/check workflow.
- Decide whether the resource ecosystem remains in-repo or splits.

## Priority Backlog

| Rank | Item | Domain | Why First |
|---:|---|---|---|
| 1 | `foundational-concepts.json` schema and validator | all | Makes every future row checkable and prevents prose drift. |
| 2 | Math field rows from [MATH-FIELDS.md](MATH-FIELDS.md) | math | Grounds the atlas in a university-style undergrad/graduate curriculum before example sprawl. |
| 3 | Graph coloring pack | math/CS/logic | Direct finite SAT/SMT example with witnesses, unsat claims, and proof-route pressure. |
| 4 | Finite probability pack | statistics/math | Adds a missing fourth domain with exact replay and rational checks. |
| 5 | DFA equivalence pack | CS/logic | Classic finite reasoning; natural SAT/SMT examples with counterexample strings. |
| 6 | QF_LRA rational examples | math | Reuses mature Farkas evidence and fills a planned curriculum node. |
| 7 | CNF/LRAT cookbook recipe | logic/proof | Explains trusted-small-checking at the smallest proof-object level. |
| 8 | Finite-field examples | math/CS | Bridges algebra, cryptography, coding theory, and BV reasoning. |
| 9 | Descriptive statistics pack | statistics | Exact arithmetic examples before approximate inference. |
| 10 | Generated foundational dashboard | all | Makes coverage and proof gaps visible. |

## Graduation Criteria

The foundational-resource ecosystem graduates from planning to a real sibling
project when:

- the concept atlas validates in CI;
- at least 40 concept rows exist across all four domains;
- at least 12 example packs validate;
- at least 6 packs use checked Axeyum evidence;
- every pack states proof/replay/numerical status;
- generated docs are deterministic;
- at least one downstream user can consume the data without reading Axeyum
  internals.
