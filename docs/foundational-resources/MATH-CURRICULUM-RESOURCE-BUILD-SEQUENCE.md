# Math Curriculum Resource Build Sequence

## Purpose

This is the practical build plan for turning the formal math curriculum into a
complete resource ecosystem. It is intentionally more operational than the
master plan. For the single owner-facing resource-family plan, use
[`MATH-CURRICULUM-COMPREHENSIVE-RESOURCE-PLAN.md`](MATH-CURRICULUM-COMPREHENSIVE-RESOURCE-PLAN.md):

```text
curriculum node -> field extension -> concept row -> example pack
-> learner page -> proof route -> solver feedback -> consumer boundary
```

Use this file to decide what to build next across the existing resource
families: educational content, taxonomy/ontology rows, example packs, proof
artifacts, solver-regression hooks, rules/law transfer examples, and eventual
library boundaries.

The invariant stays:

```text
untrusted fast search, trusted small checking
```

A finite or bounded artifact is useful only when the document says exactly what
is checked, what is trusted, and what remains a theorem/proof horizon.

## Current Baseline

The committed public query boundary currently reports:

- 111 concept rows: 23 curriculum nodes, 18 field rows, 65 bridge concepts, and
  5 example-family rows.
- 108 non-template math example packs.
- 623 expected checks: 334 `sat`, 218 `unsat`, and 71 `not-run`.
- 300 checked proof/evidence rows, 252 replay-only rows, and 71 Lean-horizon
  rows.
- 108 promoted solver-reuse packs.
- 0 unclassified solver-reuse packs.

The seed phase is complete. The build problem is now depth, navigation, proof
quality, and reuse.

## Build Principles

1. Build from the curriculum DAG first.
   Every new resource must point to one node in
   [`docs/curriculum/curriculum.toml`](../curriculum/curriculum.toml) or one
   field in [`MATH-FIELDS.md`](MATH-FIELDS.md).
2. Add bridge concepts only after reuse is visible.
   One pack does not need a new ontology row unless the concept is likely to
   organize later packs, learner pages, or consumer queries.
3. Prefer proof-route upgrades over duplicate examples.
   If a topic already has a pack, the next unit is usually checked evidence,
   a learner page, or a solver back-link.
4. Keep theorem boundaries explicit.
   Bounded epsilon-delta checks, finite topologies, finite graphs, finite
   matrix examples, and finite probability tables are not general theorems.
5. Keep the public boundary JSON-first.
   Split crates or repos only after repeated consumers prove the boundary.

## Definition Of Done For Any Resource

Every new or upgraded resource should land with the following answers:

| Gate | Required Artifact | Required Answer |
|---|---|---|
| R0 | curriculum or field anchor | Which node or field owns this? |
| R1 | concept row | What vocabulary does this add or reuse? |
| R2 | example pack | What exact finite/bounded/computable claim is checked? |
| R3 | learner page | How does a learner replay the example and see the limit? |
| R4 | proof route | Is the result replay-only, checked by certificate, or horizon? |
| R5 | solver reuse | Does this become a regression/fuzz/corpus row, or explicitly not? |
| R6 | consumer boundary | Can a query consumer find it without reading prose? |

Minimum validation for a resource increment:

```sh
python3 scripts/validate-foundational-concepts.py
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/<pack>
python3 scripts/query-foundational-resources.py summary
./scripts/check-links.sh
```

For route promotions, also run the route-specific cargo regression named in the
pack metadata.

## Stage 1: Normalize Navigation

Goal: make the existing 108 packs easy to discover by curriculum layer, field,
concept, proof route, and solver pressure.

Work:

- Add or refresh query examples whenever a field gains a substantial route.
- Keep the field-readiness and proof-route matrices synchronized with the
  generated summary.
- Make every broad learner cluster link to the focused pack pages it covers.
- Keep the matrix-computation, analysis/theorem-horizon, rules/law, and
  consumer-query guides as indexes over committed JSON, not hand-maintained
  claims.

Exit:

- A user can answer "show me all topology QF_UF/Alethe rows" or "show me all
  linear-algebra Farkas rows" with `scripts/query-foundational-resources.py`.
- Generated dashboards, README links, and planning counts agree with
  `python3 scripts/query-foundational-resources.py summary`.

## Stage 2: Complete The Learner Spine

Goal: every curriculum node and every major field extension has at least one
learner path that shows the trust boundary.

Work by layer:

| Layer | Curriculum / Field Surface | Learner Buildout |
|---|---|---|
| Foundations | logic, predicates, proof methods, induction, sets, relations, cardinality | finite countermodel replay, proof-by-refutation, proof-object anatomy, finite quantifier expansion, bounded induction warnings, finite/infinite cardinality boundary |
| Number systems | naturals, integers, rationals, reals, complex | exact arithmetic, totality conventions, bounded real shadows, delta-epsilon balls, real-pair complex algebra, completeness/analysis horizon |
| Core structures | divisibility, modular arithmetic, groups, rings, fields, polynomials, sequences, counting | gcd/CRT certificates, finite algebra tables, quotients, modules, tensors, polynomial factor/replay, recurrence prefixes, finite counting and generating functions |
| Destinations | number theory, linear algebra, calculus | bounded Diophantine checks, matrix computation index, LU checked product-entry rows, rank/residual/eigen/random-matrix rows, exact derivative/integral shadows, root-finding and optimization steps |
| Field extensions | graph theory, topology, measure/probability/statistics, optimization, numerical analysis, dynamics, geometry, functional analysis | graph coloring/search/runtime, finite topologies and homology shadows, exact finite probability/measure tables, Farkas optimization rows, Euler/root-finding/line-search rows, coordinate/circle/inversion geometry, finite operator and Chebyshev rows |
| Rules/law transfer | eligibility, authorization, tax/benefit arithmetic, future policy packs | finite predicates, thresholds, caps, temporal versions, precedence, reachability, monotonicity, and checked proof fixtures reused from math packs |

Exit:

- Every pack appears in a focused learner page or a named combined page.
- Every learner page has a runnable validation command.
- Every page says whether the row is replay-only, checked, or theorem horizon.

## Stage 3: Upgrade Proof Evidence

Goal: make checked evidence normal for representative negative rows.

Priority order:

| Route | Build Next | Why |
|---|---|---|
| Boolean CNF/LRAT | graph coloring/search, pigeonhole, small finite topology/set-family conflicts | smallest end-to-end "search then proof check" story |
| QF_LIA/Diophantine | gcd/divisibility, modular nonunit, finite count contradictions, homology torsion, exact tail-count rows | recurring integer obstruction pattern |
| QF_LRA/Farkas | rational order, LP thresholds, residual bounds, probability/measure tables, geometry, root finding, KKT/SDP/line-search rows | exact rational certificate route is already productive |
| QF_UF/Alethe | functions, quotients, homomorphisms, modules, ideals, topology preimage/quotient rows | equality-heavy finite structure and congruence conflicts |
| QF_BV/DRAT | fixed-width residues, finite fields/rings, bit-encoded graph/color rows | useful only when bit width is part of the mathematical story |
| Lean horizon | induction, completeness, compactness, convergence, measure theory, general algebra, Hilbert/Banach/Chebyshev theorem layers | keeps finite shadows from being mistaken for general proofs |

Exit:

- Each active route has at least one learner page that shows the untrusted
  solver result, the small independent check, and tamper rejection.
- The proof-upgrade frontier can be read as a route-specific queue, not a
  generic list of wishes.

## Stage 4: Add Missing Curriculum Depth

New packs should be added only when they introduce a distinct mathematical
object, a distinct proof route, or a field/curriculum hole.

### Foundations And Set Theory

Build next:

- finite lattice/set-family false-claim rows with checked evidence where the
  source object is small enough for a learner;
- richer finite countermodel pages for predicate logic;
- quotient/relation/function examples that feed topology, algebra, and rules
  packs instead of living as isolated set examples.

Stop line:

- Full first-order validity, choice, ordinal/cardinal arithmetic, and infinite
  cardinality stay Lean-horizon.

### Number Systems And Arithmetic

Build next:

- sharper exact-vs-floating examples for numerical-analysis learners;
- additional gcd/divisibility and CRT rows only when they become shared
  certificate examples;
- algebraic-real or RCF shadows only when they create real solver pressure.

Stop line:

- Do not imply bounded arithmetic prefixes or fixed-width BV rows prove
  unbounded arithmetic theorems.

### Analysis, Calculus, And Optimization

Build next:

- a delta-epsilon and metric-ball resource index that ties
  `real-analysis-rational-v0`, `metric-continuity-v0`, and compactness shadows
  into one learner path;
- a root-finding and line-search path that separates exact finite arithmetic
  from convergence theorems;
- additional KKT, active-set, SDP, and projection/prox rows only when they add
  a new certificate shape or solver pressure.

Stop line:

- Completeness, IVT/MVT/FTC, compactness theorems, KKT sufficiency, duality,
  and convergence rates stay Lean-horizon until reconstruction exists.

### Linear Algebra And Matrix Computation

Build next:

- keep the matrix index current for LU replay plus checked product-entry rows,
  rank/nullity, residual, projection, eigenpair, characteristic-polynomial,
  checked trace-invariant, tensor/module, chain/cochain, operator,
  Chebyshev, and random-matrix rows;
- add matrix-corpus rows only after the educational pack links the regression
  and the regression links the source pack;
- add finite-field and module linear-algebra rows when they exercise Alethe or
  BV routes, not just another table replay.

Stop line:

- Numerical stability, spectral theorem, infinite-dimensional operator theory,
  and asymptotic random-matrix laws are theorem horizons unless a finite exact
  statement is explicitly named.

### Discrete Math And Graph Theory

Build next:

- graph coloring rows with CNF/LRAT artifacts;
- graph reachability and BFS/DFS runtime-pathology packs that replay finite
  traces, queue/stack states, and step counters;
- matching/cut/d-separation rows only when they introduce a new proof or
  solver pressure shape.

Stop line:

- Complexity bounds, asymptotic graph families, and broad graph theorems are
  theorem horizons unless encoded as a fixed finite instance.

### Topology And Algebraic Topology

Build next:

- finite quotient-topology replay: quotient map, fibers, saturated opens,
  preimage-open definition, and checked bad quotient-open evidence;
- cohomology-ring quotienting rows only after the current cup-product and
  cohomology packs can state the quotient boundary cleanly;
- theorem-invariance rows only as Lean-horizon targets until reconstruction.

Stop line:

- Homeomorphism invariance, compactness preservation, universal coefficient
  theorems, exact sequences, and general cohomology-ring laws are not finite
  checks.

### Probability, Statistics, And Measure

Build next:

- finite probability and measure tables that expose exact rational replay,
  pushforward distributions, conditional expectation, martingales, kernels,
  hitting times, concentration, and finite integration;
- exact finite statistical-test rows where the integer/count or rational-table
  certificate is small;
- random-matrix moment rows that stay finite and exact before any asymptotic
  language is introduced.

Stop line:

- Lebesgue measure, convergence theorems, limit laws, consistency/asymptotic
  inference, and almost-everywhere reasoning stay Lean-horizon.

### Functional Analysis And Operator Theory

Build next:

- finite Chebyshev-system rows that replay interpolation matrices, sign
  alternation, recurrence, and exact residuals;
- finite operator rows that connect norms, projections, Gram matrices,
  Chebyshev slices, and matrix computation queries;
- theorem-horizon rows for Banach/Hilbert facts and minimax/approximation
  theorems.

Stop line:

- Infinite-dimensional completeness, compact operators, spectral theorem
  variants, and general Chebyshev-space theorems require Lean/theorem work.

### Rules And Law Transfer

Build next:

- policy packs that reuse existing math-resource shapes: predicates,
  arithmetic thresholds, caps, phase-outs, graph reachability, temporal
  effective dates, precedence, exceptions, and monotonicity;
- a rules query matrix that maps each legal/rule pattern back to math concept
  rows and proof routes;
- no new rule ontology until the current JSON boundary is exercised by more
  consumers.

Stop line:

- Legal interpretation, real citations, jurisdictional conflicts, and
  natural-language statutory parsing are outside the current trusted checker.

## Stage 5: Turn Resources Into Solver Feedback

Goal: let educational resources pressure the solver without pretending they are
benchmarks too early.

Promotion rule:

```text
source math object is stable
+ replay is deterministic
+ proof/certificate route is named
+ regression or corpus file links back to the pack
= promoted solver-reuse row
```

Good promotion candidates:

- small CNF graph/topology/set-family refutations;
- tiny QF_UF quotient, homomorphism, and preimage conflicts;
- exact QF_LRA/Farkas probability, optimization, geometry, and numerical rows;
- exact QF_LIA count, gcd, torsion, and Diophantine rows;
- fixed-width QF_BV rows only when width is the lesson.

Exit:

- No pack has unclassified solver-reuse metadata.
- Every promoted row states solver pressure: clause learning, bit-blast
  lowering, integer obstruction, Farkas certificate, EUF congruence, finite
  expansion, array/table replay, or Lean reconstruction.

## Stage 6: Consumer And Library Boundaries

Keep the data contract in-repo until real repeated use justifies extraction.

Current public boundary:

- concept atlas schema and JSON;
- example-pack schema plus pack metadata/expected JSON;
- generated Markdown dashboards;
- dependency-free consumer and query scripts.

Split triggers:

| Boundary | Trigger | Contents |
|---|---|---|
| `axeyum-foundational-data` | three consumers duplicate typed parsing | generated types, validated concept rows, pack rows, proof-route metadata |
| `axeyum-math-examples` | encoders are reused outside validators/tests | finite graph, matrix, algebra, topology, probability, and rules encoders |
| standalone resource repo | external course/site/corpus needs independent releases | lessons, packs, dashboards, generated site, large artifacts |
| rules/law sibling repo | policy packs need their own release cadence | rule schemas, temporal rule graph, example policies, legal-domain docs |

Do not split only because the documentation tree is large.

## First Execution Queue

Pick one item per commit unless the change is purely navigational.

1. Refresh stale planning counts and link this sequence from the resource
   indexes.
2. Audit learner coverage for the current 108 packs and record any remaining
   combined-page-only rows.
3. Landed: add the finite quotient-topology pack and bridge as the next
   distinct topology/set-theory gap, with quotient-map fibers, quotient-open
   preimage replay, saturated-open image replay, and checked QF_UF/Alethe bad
   quotient-open evidence.
4. Landed: add a delta-epsilon/metric-ball learner index across bounded
   real-analysis, metric continuity, sequence-tail shadows, compactness,
   connectedness, and finite continuity/preimage topology shadows.
5. Landed: add graph BFS/DFS runtime-pathology learner and query coverage only
   as finite trace/cost replay, with asymptotic runtime as theorem horizon.
6. Landed: add Chebyshev/operator learner and query coverage only where the
   finite operator/Chebyshev bridge replays exact operator bounds,
   interpolation matrices, sign alternation, recurrence values, residual rows,
   spectral rows, characteristic-polynomial arithmetic, or checked trace
   invariants.
7. Landed: add random-matrix learner and query coverage only as exact finite
   matrix-valued atom tables, moment replay, expected Gram replay,
   rank-mixture replay, and checked QF_LRA/Farkas bad-moment/rank rows before
   any asymptotic statement.
8. Landed: promote the concrete bad finite group-homomorphism row in
   `finite-algebra-homomorphisms-v0` through QF_UF/Alethe after table replay
   identifies `phi(1+1)=1` versus `phi(1)+phi(1)=0`.
9. Landed: promote the false top-element set-family row in
   `finite-order-lattices-v0` through Bool/CNF DRAT/LRAT after exact relation
   replay identifies `B !<= A` while the bad claim that `A` is top requires
   `B <= A`.
10. Add the next rules/law example only by reusing an existing math proof
    shape and the current JSON boundary.

## Maintenance Commands

Plan-only or navigation edits:

```sh
git diff --check
./scripts/check-links.sh
```

Resource or generated-data edits:

```sh
./scripts/check-foundational-resources.sh
python3 scripts/consume-foundational-resources.py
python3 scripts/query-foundational-resources.py summary
```

Proof-route promotions:

```sh
# plus the route-specific regression named by the pack
cargo test -p axeyum-solver --test <route-test> <test-name>
```
