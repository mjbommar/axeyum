# Math Curriculum Detailed Resource Build Plan

## Purpose

This is the execution ledger for building the full math-resource ecosystem from
the curriculum spine. It sits below the broad roadmap and above individual
pack edits:

```text
curriculum node -> concept row -> example pack -> learner page
-> proof route -> solver reuse -> consumer boundary
```

Use this file when choosing the next commit-sized work item. Use
[MATH-CURRICULUM-BUILDOUT.md](MATH-CURRICULUM-BUILDOUT.md) for phase history,
[MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md](MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md)
for per-node gates, [RESOURCE-BUILDOUT-ROADMAP.md](RESOURCE-BUILDOUT-ROADMAP.md)
for the broader resource-family plan, and
[PROOF-UPGRADE-FRONTIER.md](PROOF-UPGRADE-FRONTIER.md) for route-specific proof
upgrades.

The invariant stays simple:

```text
untrusted fast search, trusted small checking
```

Every resource should make one bounded/computable claim checkable, or clearly
state the Lean/theorem horizon when a bounded check is not a theorem.

## Current Baseline

The committed resource query currently reports:

- 23 curriculum-node concept rows.
- 18 field rows.
- 22 bridge-concept rows.
- 2 example-family rows.
- 84 non-template math packs.
- 413 expected checks.
- 195 checked proof/evidence rows.
- 171 replay-only rows.
- 47 Lean-horizon rows.
- 69 promoted solver-reuse packs.
- 6 non-benchmark-horizon solver-reuse packs.
- 9 unclassified solver-reuse packs.

The next phase is therefore a depth phase, not a seed phase. New packs are
allowed only when they fill a clear curriculum/field hole that cannot be served
by upgrading an existing pack.

## Resource Unit Contract

Every new or upgraded resource must answer these questions before it lands:

| Question | Required Answer |
|---|---|
| Audience | learner, educator, proof contributor, solver contributor, consumer, or several |
| Curriculum anchor | one `curriculum.toml` node or one field extension from `MATH-FIELDS.md` |
| Mathematical claim | finite claim, bounded shadow, computable witness, numerical check, or theorem horizon |
| Encoding route | Bool/CNF, QF_BV, QF_LIA, QF_LRA, QF_UF, QF_NRA/RCF, finite replay, or Lean horizon |
| Evidence route | model replay, DRAT/LRAT, Farkas, Diophantine, Alethe, QF_BV DRAT, or explicit gap |
| Trust boundary | what is generated/searched versus what is independently replayed or checked |
| Graduation | exact command, regression, proof route, or horizon dependency needed for the next gate |

Do not land a resource that only says a topic name. A useful row has either a
validated example, a planned example with a validation rule, or a named
theorem-horizon dependency.

## Gate Model

| Gate | Meaning | Required Check |
|---|---|---|
| R0 source | curriculum node or field taxonomy row exists | local link to `curriculum.toml` or `MATH-FIELDS.md` |
| R1 concept | atlas row exists with fragments, proof routes, and gaps | `python3 scripts/validate-foundational-concepts.py` |
| R2 pack | pack files validate and expected rows are machine-readable | `python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/<pack>` |
| R3 learner | a learner page exposes the check and limitation | `./scripts/check-links.sh` |
| R4 evidence | checked replay/certificate or explicit Lean horizon | route-specific cargo test plus pack validator |
| R5 solver reuse | regression, fuzz seed, corpus slice, or non-benchmark horizon is linked | query helper shows non-unclassified `solver_reuse` |
| R6 consumer | JSON/query consumer is enough, or a boundary decision proves more | `python3 scripts/consume-foundational-resources.py` |

No row should be described beyond its gate. A bounded finite example can be a
good R2/R3 lesson while still not being a theorem.

## Build Waves

### Wave 1: Stabilize The Existing 84 Packs

Goal: every current non-template pack has a deliberate R5 disposition:
`promoted`, `non-benchmark-horizon`, or a clear reason to remain unclassified.

Current unclassified queue:

| Pack | Practical Next Step |
|---|---|
| `induction-obligations-v0` | mark bounded obligations as non-benchmark or promote one QF_LIA bad-step row |
| `cardinality-principles-v0` | choose a small inclusion-exclusion/double-counting proof route or mark theorem rows horizon |
| `polynomial-factorization-rational-v0` | promote a rational coefficient obstruction or mark as replay-centered |
| `reals-rcf-shadow-v0` | keep RCF/NRA shadows explicit; promote only when the certificate route is ready |
| `sequence-limit-shadow-v0` | promote one finite tail-bound LRA row or mark general convergence as Lean horizon |
| `calculus-algebraic-shadow-v0` | promote a polynomial identity/refutation only if the chosen route checks the original claim |
| `calculus-riemann-sum-v0` | choose exact finite-sum replay versus an LRA false-integral artifact |
| `multivariable-calculus-rational-v0` | promote a bad-gradient/Jacobian row if it adds new solver pressure |
| `complex-plane-transforms-v0` | promote the false real-part row only if the real-pair route is source-linked |

Recently classified as explicit non-benchmark-horizon rows:

| Pack | Upgrade Trigger |
|---|---|
| `bounded-dynamics-v0` | add a bounded safety or invariant-refutation row with a source-linked QF_LRA/BV artifact |
| `complex-algebraic-v0` | add a false real-pair algebra or polynomial-root row with a source-linked LRA/NRA artifact |
| `coordinate-geometry-v0` | add a false collinearity, midpoint, distance, or incidence row with a source-linked QF_LRA/NRA artifact |
| `finite-measure-v0` | add a bad normalization, additivity, or complement row with a source-linked QF_LRA/Farkas artifact |
| `finite-operator-v0` | add a false operator-bound, norm inequality, or recurrence row with a source-linked exact-rational artifact |
| `finite-topology-v0` | add a malformed finite topology or metric-ball row with a source-linked Bool/CNF or QF_LRA artifact |

Exit criteria:

- `python3 scripts/query-foundational-resources.py summary` shows no accidental
  candidate drift.
- Every still-unclassified pack has a short reason in the proof frontier or this
  file's next revision.
- `PROOF-UPGRADE-FRONTIER.md` names the first checked route for every promoted
  pack family.

### Wave 2: Complete The Curriculum-Layer Learner Spine

Goal: each curriculum node has a learner-facing path that separates checkable
slices from theorem horizons.

| Layer | Curriculum Nodes | Learner Work |
|---|---|---|
| Foundations | propositional logic, predicate logic, proof methods, induction, sets, relations/functions, cardinality | proof object anatomy, finite countermodels, quotient/partition replay, bounded induction warnings |
| Number systems | naturals, integers, rationals, reals, complex | exact arithmetic versus real completeness, real-pair complex algebra, total operation conventions |
| Core structures | divisibility, modular arithmetic, groups, rings, fields, polynomials, sequences/limits, counting | table replay, quotient maps, coefficient arithmetic, bounded sequence shadows, pigeonhole/counting proofs |
| Destinations | number theory, linear algebra, calculus | arithmetic certificates, matrix corpora, exact calculus shadows, FTC/convergence horizons |

Exit criteria:

- Every pack appears in a focused lesson or an explicitly named combined
  lesson.
- Every lesson has a run/check command or a link to pack validation.
- No lesson implies a finite bounded check proves an unbounded theorem.

### Wave 3: Proof-Route Depth

Goal: make checked evidence normal for representative UNSAT rows.

| Route | Curriculum Pressure | Build Pattern | Stop Condition |
|---|---|---|---|
| Bool/CNF DRAT/LRAT | logic, sets, graphs, counting, finite topology | commit small DIMACS artifact, emit DRAT, elaborate/check LRAT, add tamper regression | one representative row per source family is promoted |
| QF_BV DRAT | finite fields/rings, residue arithmetic, bit encodings | add fixed-width SMT-LIB artifact and DRAT-backed bit-blast regression | width is educationally meaningful, not incidental |
| QF_LIA/Diophantine | integer equations, gcd, counts, homology coefficients | encode minimal obstruction and check integer certificate | recurring obstruction has a cookbook example |
| QF_LRA/Farkas | rationals, matrices, LP, probability tables, geometry, dynamics | express exact rational conflict, emit/recheck Farkas certificate | source pack links artifact and learner page names trust boundary |
| QF_UF/Alethe | finite functions, quotients, algebra maps, actions, modules | encode congruence/equality conflict and check Alethe | table replay and equality proof are distinct in docs |
| Lean horizon | induction, completeness, compactness, measure, asymptotics, Hilbert/Banach facts | state theorem shape, prerequisites, and missing reconstruction dependency | finite rows are not counted as theorem proof |

Exit criteria:

- `PROOF-UPGRADE-FRONTIER.md` can be read as a work queue, not as a stale wish
  list.
- Each active route has at least one end-to-end learner page that shows a
  successful certificate and a rejected tampered certificate.

### Wave 4: Solver Feedback And Benchmark Hygiene

Goal: educational examples become useful solver assets without distorting the
education layer into a benchmark suite.

Build rules:

- Promote a row only after its mathematical source object is stable and replayed.
- Keep source-level artifacts under the pack folder.
- Name the solver pressure in `solver_reuse`: clause learning, BV lowering,
  integer obstruction, Farkas certificate, EUF congruence, array extensionality,
  finite expansion, or Lean reconstruction.
- Keep general theorem horizons out of performance scoring.
- Use example-family rows for recurring proof/solver shapes rather than
  repeating prose across packs.

Exit criteria:

- A solver contributor can query by field plus route and find source-linked
  artifacts.
- Regression tests cite the pack, and the pack cites the regression.
- No resource-backed benchmark claim exists without a committed corpus and
  measured result.

### Wave 5: Consumer, Rules/Law, And Library Boundaries

Goal: make the resource system useful outside docs while keeping the boundary
boring until real demand exists.

Build order:

1. Keep JSON schemas, validators, generated dashboards, and query helper as the
   public contract.
2. Add rules/law examples only when they reuse existing math-resource patterns:
   finite predicates, thresholds, reachability, precedence, optimization, and
   proof routes.
3. Add typed accessors only after repeated scripts duplicate parsing logic.
4. Split a crate or separate repo only after a boundary decision cites at least
   three duplicated consumers or one external release-cadence need.

Exit criteria:

- `scripts/consume-foundational-resources.py` and
  `scripts/query-foundational-resources.py` cover the common consumer questions.
- A boundary decision can point at real usage, not project size alone.

## Field Build Ledger

| Field | Current Role | Next Resource Work | Evidence Route |
|---|---|---|---|
| `logic_and_proof` | SAT, refutation, finite proof patterns, induction bounds | finish proof-object anatomy and PHP CNF promotions | Bool/CNF DRAT/LRAT, QF_LIA, Lean horizon |
| `set_theory_and_foundations` | finite sets, relations, functions, quotients, lattices, cardinality | tighten finite/infinite boundaries and quotient/image/preimage vocabulary | finite replay, Bool/CNF, QF_UF/Alethe, Lean horizon |
| `discrete_math` | counting, generating functions, graph resources, finite actions | maintain pigeonhole and coefficient-convolution examples; add new rows only for distinct counting pressure | Bool/CNF, QF_LIA, finite replay |
| `graph_theory` | coloring, reachability, search runtime, matching, cuts, d-separation | keep one promoted representative per family; add asymptotic horizons only as proof targets | Bool/CNF, QF_BV, QF_LIA, finite replay |
| `number_theory` | gcd, modular arithmetic, residues, bounded Diophantine checks | group recurring divisibility and residue obstructions | QF_LIA/Diophantine, QF_BV |
| `linear_algebra` | exact matrices, vector spaces, duals, modules, tensors, spectral rows | make matrix rows queryable by computation type and solver route | QF_LRA/Farkas, finite replay, QF_UF/Alethe |
| `abstract_algebra` | finite groups/rings/fields, homomorphisms, ideals, modules, tensors | add narrower rows only when multiple packs reuse them | QF_UF/Alethe, QF_BV, finite replay |
| `real_analysis` | bounded rational intervals, metric continuity, RCF shadows, calculus shadows | keep bounded shadows distinct from completeness/convergence theorems | QF_LRA/Farkas, QF_NRA/RCF, Lean horizon |
| `complex_analysis` | real-pair algebra and transformations | keep algebraic replay rows non-benchmark until a checked real-pair contradiction exists | real-pair LRA/NRA, finite replay, Lean horizon |
| `topology` | finite topologies, compactness, connectedness, continuous maps, homology | upgrade finite topology from non-benchmark only with a tiny source-level axiom conflict | Bool/CNF, QF_UF/Alethe, QF_LIA, Lean horizon |
| `measure_theory` | finite measures, product measure, integration, random variables | upgrade finite-measure replay through a bad finite-additivity or complement certificate | QF_LRA/Farkas, finite replay, Lean horizon |
| `probability_theory` | finite probability, kernels, Markov chains, martingales, hitting times, concentration | keep table rows exact and route bad rows through LRA/LIA | QF_LRA/Farkas, QF_LIA, finite replay |
| `statistics` | descriptive stats, exact tests, regression, finite count tables | distinguish exact finite tests from numerical/statistical inference | QF_LIA, QF_LRA/Farkas, replay |
| `optimization_and_convexity` | LP/Farkas, convexity, least squares, Hessians | add route notes from LP to Farkas and from Hessians to exact matrix checks | QF_LRA/Farkas, QF_NRA shadows |
| `numerical_analysis` | residuals, Euler steps, exact error recurrences, matrix algorithms | keep finite replay and numerical-honesty rows distinct from promoted exact residual/error certificates | QF_LRA/Farkas, replay, Lean horizon |
| `differential_equations_and_dynamical_systems` | bounded recurrences and Euler traces | upgrade bounded dynamics from non-benchmark only with checked invariant/transition counterexamples | QF_LRA/Farkas, replay, Lean horizon |
| `geometry` | coordinate, affine, orientation/area rational geometry | upgrade coordinate geometry from non-benchmark only with source-linked incidence/distance conflicts | QF_LRA/Farkas, finite replay |
| `functional_analysis_and_operator_theory` | finite operators, inner products, Chebyshev systems | keep finite-dimensional operator replay non-benchmark until a checked bad-bound row exists | QF_LRA/Farkas, replay, Lean horizon |

## Curriculum Node Build Ledger

| Node | Build Priority | Practical Work |
|---|---|---|
| `propositional-logic` | maintain | keep tiny CNF and tamper tests as the smallest trust story |
| `predicate-logic` | maintain | finite expansion now has a Bool/CNF proof-route regression; keep arbitrary-domain validity horizon explicit |
| `proof-methods` | promote | PHP/refutation CNF artifact and proof-object lesson |
| `induction` | horizon clarity | separate bounded obligations from Lean induction schema |
| `sets` | maintain | keep finite set/lattice false claims checked and linked |
| `relations-and-functions` | maintain | add image/preimage rows only when reused by several packs |
| `cardinality` | classify | decide finite cardinal principles route versus infinite Lean horizon |
| `naturals` | maintain | keep bounded prefix and LIA/BV width limits explicit |
| `integers` | maintain | group common Diophantine obstructions |
| `rationals` | maintain | exact rational order and Farkas conflicts are already the model |
| `reals` | deepen | distinguish RCF shadows, LRA bounded deltas, and completeness horizon |
| `complex` | non-benchmark now | real-pair replay first; promote only after a checked algebraic contradiction |
| `divisibility-and-euclid` | maintain | use gcd/Bezout rows as arithmetic-certificate examples |
| `modular-arithmetic` | maintain | keep LIA nonunit and BV fixed-width residue routes distinct |
| `groups` | maintain | table replay plus Alethe equality conflicts |
| `rings` | maintain | BV fixed finite rings only when width is conceptually relevant |
| `fields` | maintain | finite fields plus linear-algebra links; arbitrary-field facts horizon |
| `polynomials` | deepen | polynomial identities now have a QF_LIA false-root regression; factorization still needs a solver-reuse decision |
| `sequences-and-limits` | classify | bounded tails can be checked; convergence theorem stays Lean horizon |
| `counting` | promote | pigeonhole CNF/LRAT and coefficient-count rows |
| `number-theory` | maintain | bounded residue and Diophantine families |
| `linear-algebra` | deepen | matrix corpus notes and route-specific regression back-links |
| `calculus` | classify | exact algebraic shadows now; theorem layer later |

## Commit-Sized Queue

Pick one row per commit unless the change is purely navigational.

1. Landed: promote the `proof-methods-refutation-v0` and `counting-v0`
   `PHP(3,2)` rows through source-linked DIMACS plus DRAT/LRAT regression.
2. Landed: classify `bounded-dynamics-v0`, `complex-algebraic-v0`,
   `coordinate-geometry-v0`, `finite-measure-v0`, `finite-operator-v0`, and
   `finite-topology-v0` as explicit non-benchmark educational rows until they
   gain negative, certificate-bearing examples.
3. Landed: promote `generating-functions-v0` through a source-linked finite
   Cauchy-product coefficient QF_LIA/Diophantine artifact and route regression.
4. Landed: promote `polynomial-identities-v0` through a source-linked false
   rational-root QF_LIA/Diophantine artifact and route regression.
5. Landed: promote `finite-predicate-v0` through a source-linked finite
   quantifier-expansion Bool/CNF artifact and DRAT/LRAT route regression.
6. Promote or classify the remaining unclassified packs, starting with compact
   source-level conflicts where the route is clear.
7. Upgrade finite-topology from non-benchmark with an axiom conflict only if the
   CNF stays source-level readable.
8. Upgrade finite-measure from non-benchmark with a finite-additivity or
   complement conflict through QF_LRA/Farkas.
9. Upgrade coordinate-geometry from non-benchmark with a collinearity/distance
   conflict through QF_LRA/Farkas.
10. Add a proof-object learner page that follows one resource from source claim
   to emitted proof and corrupted-proof rejection.
11. Add a generated or query-based audit for unclassified solver-reuse packs if
   manual tracking starts to drift.
12. Revisit the library boundary after unclassified packs are resolved and at
   least one non-doc consumer repeats resource parsing logic.

## Validation Checklist

For plan-only edits:

```sh
git diff --check
./scripts/check-links.sh
```

For resource metadata or generated dashboard changes:

```sh
./scripts/check-foundational-resources.sh
python3 scripts/consume-foundational-resources.py
python3 scripts/query-foundational-resources.py summary
```

For a pack upgrade:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/<pack>
<route-specific cargo test>
./scripts/check-foundational-resources.sh
./scripts/check-links.sh
```

For a solver-reuse promotion, the pack must link the route regression and the
regression must include the source artifact from the pack folder.
