# Math Curriculum Resource Buildout Roadmap

## Purpose

This is the detailed operating plan for building the full foundational-resource
ecosystem from the math curriculum spine. It complements:

- [Math Curriculum Resource Buildout](MATH-CURRICULUM-BUILDOUT.md), the phase
  contract and landed-history log.
- [Math Curriculum Comprehensive Resource Plan](MATH-CURRICULUM-COMPREHENSIVE-RESOURCE-PLAN.md),
  the owner-facing plan across education pages, ontology rows, example packs,
  proof artifacts, solver feedback, rules/law transfer, consumer boundaries,
  and future library splits.
- [Math Curriculum Resource Master Plan](MATH-CURRICULUM-RESOURCE-MASTER-PLAN.md),
  the top-down curriculum-wide sequencing plan across layers, fields, routes,
  solver reuse, and consumer boundaries.
- [Math Curriculum Resource Build Sequence](MATH-CURRICULUM-RESOURCE-BUILD-SEQUENCE.md),
  the practical staged plan for education, ontology, packs, proof artifacts,
  solver feedback, rules/law transfer, and future library boundaries.
- [Math Curriculum Implementation Matrix](MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md),
  the commit-sized gate matrix.
- [Math Curriculum Detailed Build Plan](MATH-CURRICULUM-DETAILED-BUILD-PLAN.md),
  the current execution ledger for existing packs, unclassified solver-reuse
  rows, proof-route depth, and field-by-field next steps.
- [Curriculum Resource Execution Plan](CURRICULUM-RESOURCE-EXECUTION-PLAN.md),
  the current forward plan.
- [University Math Field Taxonomy](MATH-FIELDS.md), the 18-field university
  field spine.

The invariant is:

```text
curriculum node -> concept row -> example pack -> learner page -> proof route
-> solver reuse -> consumer boundary
```

For executable queries that begin at the curriculum-node layer, use
[Curriculum Node Queries](CURRICULUM-NODE-QUERIES.md).
For executable queries that begin at the proof-status/result-status trust
boundary, use [Trust Boundary Queries](TRUST-BOUNDARY-QUERIES.md).
For downstream row and pack display labels over the same status fields, use
[Claim Label Matrix](CLAIM-LABEL-MATRIX.md).
For the stable JSON/query file and field contract exposed at R6, use
[Public Data Contract](PUBLIC-DATA-CONTRACT.md).
For executable queries that begin at the SMT-fragment demand layer, use
[Fragment Demand Queries](FRAGMENT-DEMAND-QUERIES.md).
For executable queries that begin from malformed claims and checked rejection
rows, use [Rejection Case Queries](REJECTION-CASE-QUERIES.md).
For route-specific corrupted-evidence commands and tamper gaps, use
[Checker Tamper Matrix](CHECKER-TAMPER-MATRIX.md).

The product is not a textbook and not a formal-library clone. It is a system of
small resources that make Axeyum's identity concrete:

```text
untrusted fast search, trusted small checking
```

## Current Baseline

The current committed data boundary reports:

- 23 curriculum-node concept rows.
- 18 math-field concept rows.
- 76 bridge-concept rows.
- 5 example-family rows.
- 139 non-template math example packs.
- 915 expected checks.
- 365 checked proof/evidence rows.
- 448 replay-only rows.
- 102 Lean-horizon rows.
- 139 promoted solver-reuse packs.
- 0 non-benchmark-horizon solver-reuse packs.
- 0 unclassified solver-reuse packs.
- 139 focused learner-linked packs, with no path-only, index-only, or missing
  learner buckets; see [Learner Coverage Audit](LEARNER-COVERAGE-AUDIT.md).

This is broad enough that the next work is not "create a few examples." The
next work is to make the resource system deep, navigable, and reusable:

- split broad curriculum nodes into reusable concept rows;
- upgrade representative rows from replay-only to checked certificates;
- turn selected examples into solver regressions and fuzz seeds;
- make every lesson expose the trust boundary;
- keep consumer/API boundaries JSON-first until repeated use proves a library
  split is worth it.

## Source Of Truth

Build from the sources in this order:

1. [curriculum.toml](../curriculum/curriculum.toml): authoritative 23-node math
   prerequisite DAG.
2. [MATH-FIELDS.md](MATH-FIELDS.md): 18-field university expansion taxonomy.
3. Existing non-template packs under `artifacts/examples/math/`.
4. [SMT Fragment Atlas](../atlas/README.md): fragment and support vocabulary.
5. [Proof Certificate Cookbook](../proof-cookbook/README.md): evidence-route
   vocabulary.
6. [Rules-as-Code Verification Lab](../rules-as-code/README.md): downstream
   pattern reuse for policy/law/rule reasoning.

If a generated dashboard disagrees with prose, fix the source JSON/metadata or
the generator. Do not hand-edit generated views.

## Resource Layers

### R1: Concept Atlas

Audience: learners, proof contributors, solver contributors, and downstream
consumers.

Build plan:

- Keep one row per curriculum node and one row per math field.
- Add bridge-concept rows only when multiple packs need the same vocabulary.
- Add example-family rows for repeated solver/proof shapes, not for every pack.
- Add field-specific concept rows when a broad curriculum node hides materially
  different ideas, such as quotient maps, kernels/images, compactness shadows,
  Farkas infeasibility, or finite model replay.

Minimum row content:

- curriculum or field anchor;
- decidability scope;
- Axeyum fragment route;
- example packs;
- proof routes;
- open gaps;
- graduation criteria.

Near-term concept-row families:

| Family | Why It Matters | First Rows |
|---|---|---|
| finite model replay and proof methods | Repeated witness-check and finite-proof stories across foundation packs | model replay, finite countermodel replay, counterexample replay, refutation-as-query, finite proof-pattern replay, finite quantifier expansion, bounded induction obligations |
| proof object anatomy | Explains checked UNSAT beyond "solver says no" | landed rows for Boolean CNF DRAT/LRAT, QF_LRA Farkas, QF_UF Alethe, and QF_BV bit-blast certificate anatomy |
| set/foundations structure vocabulary | Keeps finite set checks, function-table replay, finite cardinality, and infinite theorem horizons from blurring together | landed rows for finite Boolean algebra, finite partition/relation roundtrips, finite image/preimage/inverse tables, finite bijection/cardinality, and cardinality theorem horizons |
| algebraic structure maps | Current algebra packs are broad | homomorphism, kernel/image, quotient, action, ideal, module, tensor |
| analysis/topology boundaries | Prevents overclaiming bounded examples | metric ball, epsilon-delta shadow, compactness shadow, connectedness shadow, continuity preimage |
| matrix computation | Bridges education and solver corpora | LU replay, rank/nullity, residual bound, eigenpair, characteristic polynomial, finite random-matrix moment |
| probability/statistics tables | Many packs share finite probability structure | landed rows for finite probability mass tables, finite distribution distance, pushforward distributions, stochastic kernels, conditional expectation, and tail/count obstructions |
| rules/law transfer | Reuses math concepts for policies | finite predicate, threshold, exception, precedence, temporal version |

Graduation signal: `python3 scripts/validate-foundational-concepts.py` passes
and the generated dashboards expose the row without manual prose.

### R2: Example Packs

Audience: learners, educators, proof contributors, and solver contributors.

Every pack should have:

- `README.md`: audience, scope, limitations, and lesson links;
- `metadata.json`: fields, concepts, fragments, proof routes, validator command,
  and optional `solver_reuse`;
- `model.md`: finite model and symbols;
- `checks.md`: expected SAT/UNSAT/UNKNOWN rows and trust story;
- `expected.json`: machine-readable expected outcomes;
- optional `cnf/` or `smt2/` artifacts only when small and stable.

Pack build sequence:

1. Define one exact finite or computable claim.
2. Add at least one positive witness row and one negative/counterexample row
   when the concept naturally supports both.
3. Replay every witness against the mathematical source object.
4. For UNSAT, use checked evidence when available; otherwise mark the proof
   route explicitly as replay-only, gap, or Lean horizon.
5. Add a focused learner page once the pack validates and teaches a distinct
   workflow.
6. Promote one representative row into a solver regression only after the pack
   replay is deterministic.

Graduation signal: `python3 scripts/validate-foundational-example-pack.py
artifacts/examples/math/<pack>` passes, and the pack appears in learner and
proof dashboards.

### R3: Learner Pages

Audience: learners and educators.

Each page should be a small proof/checking walkthrough, not a generic textbook
chapter.

Required structure:

1. State the concept.
2. State the finite or computable slice Axeyum checks.
3. Name the exact pack and check rows.
4. Show the model, counterexample, or certificate route.
5. State the proof horizon and current missing dependency.
6. Include a runnable validation command.

Build plan:

- Keep the nine cluster pages as the table of contents.
- Keep focused end-to-end pages for packs that have enough substance to teach a
  complete loop.
- Prefer route notes over duplicated pack metadata.
- Never imply a finite bounded check proves a general theorem.

Graduation signal: `./scripts/check-links.sh` passes, the learner/proof
dashboard shows no missing learner link for the pack, and
[Learner Coverage Audit](LEARNER-COVERAGE-AUDIT.md) stays current after any pack
count change.

### R4: Proof And Evidence

Audience: proof contributors, reviewers, and users who need assurance.
Use [Proof Route Family Selection](PROOF-ROUTE-FAMILY-SELECTION.md) as the
compact selector for the current representative proof families before adding
another checked negative row.
Use [Proof Route Learner Snippets](../learn/math/proof-route-learner-snippets.md)
for compact learner-facing route wording on focused pack pages.
Use [Proof Upgrade Queries](PROOF-UPGRADE-QUERIES.md) when a contributor needs
executable replay-only row, route-relevant pack, checked-row, and horizon
lookups before promoting another certificate row.
Use [Trust Boundary Queries](TRUST-BOUNDARY-QUERIES.md) when a consumer needs
status-first checked, replay-only, and Lean-horizon drilldowns before deciding
what a resource can claim.
Use [Claim Label Matrix](CLAIM-LABEL-MATRIX.md) when the same consumer needs
allowed display labels for checked witnesses/refutations, finite replay rows,
Lean horizons, or mixed-trust pack cards; use
`query-foundational-resources.py labels` to audit the labels from JSON.
Use [Public Data Contract](PUBLIC-DATA-CONTRACT.md) when the consumer needs the
stable file list, fields, schema versions, compatibility rules, and required
smoke commands for the JSON boundary.
Use [Rejection Case Queries](REJECTION-CASE-QUERIES.md) when a reviewer needs
route-scoped malformed-claim rows before following cookbook tamper regressions.
Use [Checker Tamper Matrix](CHECKER-TAMPER-MATRIX.md) when a reviewer needs the
focused corrupted-evidence command for each active route.

Route plan:

| Route | Use For | Immediate Work |
|---|---|---|
| finite replay | SAT witnesses, finite table checks, computed witnesses | Make every replay row state what is recomputed independently. |
| Boolean CNF DRAT/LRAT | finite Boolean refutations, graph/search/set-family conflicts | Promote small topology and graph rows that are source-level obvious. |
| QF_BV DRAT | fixed-width residue, bit-vector, and finite algebra conflicts | Promote only when width is part of the educational claim. |
| QF_LIA/Diophantine | integer equations, counts, modular obstructions, rank coefficients, torsion membership | Group recurring gcd/divisibility and quotient-boundary obstructions as cookbook examples. |
| QF_LRA/Farkas | exact rational infeasibility, LP, residuals, root-finding steps, separation rows, KKT rows, active-set QP rows, SDP rows, gradient-descent rows, line-search rows, Wolfe line-search rows, projected-gradient rows, proximal-gradient rows, probability tables | Continue promoting bad table, bad bound, bad iterate, bad width, bad convex-combination, bad separator, bad stationarity, bad complementarity, bad free-gradient, bad degenerate multiplier, bad objective, bad duality-gap, bad slack-entry, bad decrease, bad step-coordinate, bad descent-bound, bad Armijo, bad descent-direction, bad accepted-candidate, bad Wolfe minimizer, bad Wolfe sufficient-decrease, bad Wolfe curvature, bad projection, bad projected-decrease, bad proximal-point, bad composite-decrease, and bad box-proximal-point rows with independent Farkas checks. |
| QF_UF/Alethe | equality-heavy finite functions, quotients, homomorphisms | Use table replay for objects, Alethe for congruence conflicts. |
| Lean horizon | induction schemas, completeness, topology, measure, asymptotics | Record theorem shape and dependencies; do not benchmark as finite checks. |

Graduation signal: route-specific cargo test passes, the pack links the recipe,
and the trust boundary is described in the learner page.

### R5: Solver Reuse

Audience: solver contributors and benchmark maintainers.

The educational resources become solver assets only after their mathematical
meaning is stable.

The focused consumer guide for this layer is
[Solver Reuse Queries](SOLVER-REUSE-QUERIES.md). It records executable
promoted-pack, route, field, and checked-row queries for solver/proof
contributors.

Build plan:

- Add `solver_reuse.status = candidate` only when a row pressures a real solver
  fragment.
- Promote to `promoted` only after a regression, fuzz seed, benchmark slice, or
  explicit non-benchmark-horizon back-link exists.
- Keep source-level artifacts under the pack folder when possible.
- Name the solver pressure in metadata: clause learning, bit-blast lowering,
  LIA divisibility, Farkas certificate, EUF congruence, array extensionality,
  quantifier finite expansion, or Lean reconstruction.

Good promotion candidates:

- one small Bool/CNF row per graph/topology/set-family pattern;
- one LIA row per recurring integer obstruction pattern;
- one LRA row per probability/statistics/optimization bad table;
- one QF_UF row per equality-heavy algebra family;
- one QF_BV row per fixed-width residue or finite algebra pattern.

Graduation signal: the regression or corpus source cites the pack, and the pack
metadata links back to the regression.

### R6: Consumer Boundary

Audience: downstream tools, sibling projects, and future libraries.

Keep the boundary boring until real use proves otherwise:

- committed JSON schemas;
- committed JSON metadata;
- generated Markdown dashboards;
- `scripts/consume-foundational-resources.py`;
- `scripts/query-foundational-resources.py`.

Do not split a crate or repo because the plan is large. Split only when there
are at least three duplicated consumers or one external consumer that needs an
independent release cadence.

Likely future packages:

| Boundary | Trigger | Contents |
|---|---|---|
| `axeyum-foundational-data` | typed accessors are duplicated | concept rows, pack rows, proof routes, dashboard data |
| `axeyum-math-examples` | encoders are duplicated across tests/apps | finite graph, algebra, matrix, topology, probability encoders |
| standalone resource repo | data grows too large for core reviews | examples, lessons, generated site, public release cadence |
| rules/law sibling | rule packs become independently useful | norm graph, citations, temporal rules, eligibility/policy examples |

## Curriculum-Layer Build Plan

### Layer 0: Foundations

Nodes: propositional logic, predicate logic, proof methods, induction, sets,
relations/functions, cardinality.

Current resource surface:

- Boolean SAT and CNF examples.
- Finite predicate expansion.
- Proof-method patterns.
- Bounded induction obligations.
- Finite set, relation, function, lattice, and cardinality packs.

Build next:

- Add concept rows for proof by refutation, proof by cases, finite quantifier
  expansion, finite countermodel replay, induction obligation, and induction
  schema horizon.
- Promote small Boolean refutations to checked DRAT/LRAT where the source
  formula is clear enough for a learner.
- Add reusable schemas for finite relation/function tables, quotient maps,
  finite partitions, image/preimage, and inverse tables.
- Keep full first-order validity, full induction, and infinite cardinality as
  Lean-horizon rows.

Solver/proof pressure:

- Bool/CNF and DRAT/LRAT for finite refutations.
- QF_UF/Alethe for finite function consistency and congruence.
- Lean reconstruction for proof methods and induction schemas.

### Layer 1: Number Systems

Nodes: naturals, integers, rationals, reals, complex numbers.

Current resource surface:

- Bounded natural arithmetic.
- Integer LIA.
- Exact rational LRA.
- Algebraic real/RCF shadows.
- Bounded real-analysis and metric-continuity examples.
- Complex arithmetic as real-pair algebra.

Build next:

- Maintain the landed exact-vs-floating and totality-convention concept rows,
  and keep new arithmetic packs attached to them whenever a row depends on
  exact rational replay, SMT totality, or explicit side conditions.
- Maintain the landed gcd/divisibility witness bridge row for common-divisor,
  Bezout, quotient, modular nonunit, and gcd non-divisibility examples.
- Add concept rows for bounded natural prefixes, rational order, real algebraic
  shadow, metric ball, epsilon-delta shadow, and analytic horizon only when
  they become repeated cross-pack vocabulary.
- Promote representative bad arithmetic rows into LIA, LRA, or QF_BV proof
  routes according to the source concept.
- Add lesson notes that separate exact rationals and algebraic real shadows
  from real completeness.
- Keep complex analysis, holomorphic functions, and analytic continuation as
  Lean-horizon material until proof reconstruction exists.

Solver/proof pressure:

- QF_LIA/Diophantine for integer facts.
- QF_LRA/Farkas for rational order/infeasibility.
- QF_NRA/RCF for algebraic real shadows.
- Lean horizon for completeness and analytic theorems.

### Layer 2: Core Structures And Tools

Nodes: divisibility, modular arithmetic, groups, rings, fields, polynomials,
sequences/limits, counting.

Current resource surface:

- GCD/Bezout, CRT/residue checks, finite groups, monoids, permutation groups,
  actions, rings, fields, ideals, modules, tensor products, polynomial
  identities/factorization, generating functions, counting, and bounded
  sequence/limit shadows.

Build next:

- Split algebra concepts into kernels/images, quotients, ideals, modules,
  tensor universal-property shadows, orbit-stabilizer, Burnside, unit/idempotent
  replay, and homomorphism preservation.
- Landed: use `bridge_polynomial_coefficient_factor_replay` for coefficient
  extraction, division/factor witnesses, GCD/square-free/factor-theorem replay,
  root-finding steps, finite coefficient windows, and polynomial geometry
  obligations. Add narrower resultant or irreducibility rows only when a new
  pack creates distinct solver/proof pressure.
- Promote equality-heavy conflicts through QF_UF/Alethe and fixed-width
  algebra conflicts through QF_BV only when the encoding matches the concept.
- Keep arbitrary group/ring/field theory, general factorization, and full
  convergence theory as Lean-horizon.

Solver/proof pressure:

- QF_UF/Alethe for equality and congruence.
- QF_BV for fixed finite tables and residue arithmetic.
- QF_LIA for divisibility and coefficient obstructions.
- Lean horizon for general algebra and sequences.

### Layer 3: Destinations

Nodes: number theory, linear algebra, calculus.

Current resource surface:

- Bounded number-theory checks.
- Exact rational linear algebra with exact bad LU product-entry replay plus a
  separate checked product-entry proof row and nullspace-component evidence.
- Finite vector/dual/module/tensor resources.
- Inner-product, spectral, matrix-invariant, numerical-linear-algebra, and
  random-matrix finite packs.
- Algebraic calculus, finite Riemann sums, and multivariable rational calculus.
- Multivariable rational calculus now has a promoted bad-gradient QF_LRA/Farkas
  route for the final exact gradient-component contradiction.

Build next:

- Treat number theory as arithmetic-certificate pressure: bounded Diophantine,
  residue, CRT, quadratic residue, sum-of-squares, and modular obstruction
  families.
- Treat linear algebra as the bridge from education to solver-friendly matrix
  corpora: LU/nullspace replay plus a separate checked bad product-entry proof
  row and checked nullspace-component evidence, rank/nullity, residual bounds, eigenpair
  checks, characteristic polynomial, tensor maps, and finite-field linear
  algebra.
- Treat calculus as exact algebraic shadow plus explicit proof horizon:
  derivative identities, Jacobian/Hessian replay, finite sums, bounded
  epsilon-delta samples, and theorem targets for FTC, convergence, and
  differentiability.

Solver/proof pressure:

- QF_LIA and QF_BV for bounded number theory.
- QF_LRA/Farkas for rational matrix infeasibility, residual bounds, and LP.
- QF_NRA for polynomial calculus shadows.
- Lean horizon for analytic calculus theorems.

## Field-By-Field Build Plan

### 1. Logic And Proof

Current packs:

- `logic-basics-v0`
- `finite-predicate-v0`
- `proof-methods-refutation-v0`
- `proof-methods-patterns-v0`
- `induction-obligations-v0`
- `induction-patterns-v0`

Build next:

- Add concept rows for refutation, natural-deduction pattern, finite
  countermodel, bounded induction obligation, and Lean induction schema.
- Keep `finite-predicate-v0`'s promoted finite quantifier-expansion row tied to
  the source CNF/DRAT/LRAT route, and do not treat it as arbitrary-domain
  first-order validity.
- Keep `induction-obligations-v0`'s promoted bounded step-count row tied to
  source QF_LIA arithmetic-DPLL evidence after finite replay computes zero bad
  prefix-sum steps.
- Add a proof-object anatomy lesson that starts from a tiny CNF, emits
  DRAT/LRAT, tampers with it, and shows checker rejection.
- Promote one small proof-method contradiction row to the Boolean CNF route if
  it is not already represented by a checked route.

Graduation:

- At least one learner page traces formula -> untrusted search -> certificate
  -> checker rejection of a corrupted certificate.

### 2. Set Theory And Foundations

Current packs:

- `finite-sets-v0`
- `relations-functions-v0`
- `equivalence-classes-v0`
- `function-composition-v0`
- `finite-order-lattices-v0`
- `finite-cardinality-v0`
- `cardinality-principles-v0`

Build next:

- Add concept rows for finite Boolean algebra, partition, quotient map,
  image/preimage, inverse table, injection/surjection/bijection, and
  finite/infinite cardinality boundary.
- Promote small false set/lattice/cardinality claims to Bool/CNF or QF_UF
  routes when the source encoding is obvious.
- Keep `cardinality-principles-v0`'s promoted overlap-additivity row tied to
  the source QF_LIA/Diophantine artifact after finite replay computes the true
  union count.
- Keep Cantor, choice, ordinal/cardinal arithmetic, and infinite set theory as
  Lean-horizon rows.

Graduation:

- Each false finite claim has checked evidence or an explicit route gap; each
  infinite claim is visibly excluded from solver benchmarks.

### 3. Discrete Math

Current packs:

- `counting-v0`
- `generating-functions-v0`
- graph packs listed under `graph_theory`
- finite permutation/action packs shared with algebra.

Build next:

- Landed finite-counting replay bridge row for finite enumeration, pigeonhole,
  double counting, coefficient extraction, finite orbit counts, and exact
  finite tail counts.
- Landed reusable bounded-family/asymptotic-boundary bridge row for finite graph
  search, recurrence prefixes, generating-function coefficient windows,
  bounded dynamics, and Euler rows.
- Promote finite counting contradictions through CNF/LRAT or LIA when they
  produce small certificates.

Graduation:

- Learner pages state exactly which finite family size is checked and what
  remains asymptotic proof work.

### 4. Graph Theory

Current packs:

- `graph-coloring-v0`
- `graph-reachability-v0`
- `graph-search-runtime-v0`
- `graph-matching-v0`
- `graph-cut-v0`
- `finite-flow-cut-v0`
- `finite-shortest-path-v0`
- `finite-dag-topological-order-v0`
- `graph-d-separation-v0`

Build next:

- Maintain the landed `bridge_finite_graph_replay_obstruction` row for
  coloring, reachability, BFS/DFS traversal, matching, cut, finite flow/cut,
  shortest paths, DAG topological orders, separation, d-separation, and
  graph-counterexample replay.
- Preserve the landed source-linked graph-family proof rows for coloring,
  reachability, matching, cut, flow/cut, shortest-path, topological-order,
  d-separation, and BFS/DFS runtime shapes before adding duplicate examples.
- Add proof-route notes for when graph claims are Boolean SAT, finite replay,
  exact rational flow/cut or shortest-path replay, DAG order/cycle replay, LIA
  cost counters, or Lean-horizon asymptotics.

Graduation:

- A solver contributor can filter graph resources by fragment and immediately
  find source-linked regression candidates.

### 5. Number Theory

Current packs:

- `gcd-bezout-v0`
- `modular-arithmetic-v0`
- `number-theory-v0`
- `integer-lia-v0`
- `natural-arithmetic-v0`
- `finite-fields-v0`
- `finite-ideals-v0`

Build next:

- Add concept rows for gcd witness, Bezout certificate, modular inverse,
  CRT compatibility, quadratic residue, Diophantine obstruction, bounded
  residue enumeration, and deep theorem horizon.
- Promote recurring integer obstructions into QF_LIA/Diophantine examples.
- Use QF_BV only when fixed-width residue semantics is the point of the lesson.

Graduation:

- Every modular or Diophantine row says whether it is a bounded residue check,
  an integer proof route, or a theorem-horizon placeholder.

### 6. Linear Algebra

Current packs:

- `linear-algebra-rational-v0`
- `finite-vector-spaces-v0`
- `finite-dual-spaces-v0`
- `inner-product-spaces-rational-v0`
- `finite-modules-v0`
- `finite-tensor-products-v0`
- `numerical-linear-algebra-v0`
- `spectral-linear-algebra-v0`
- `matrix-invariants-v0`
- `random-matrix-finite-v0`
- `least-squares-regression-v0`
- `multivariable-calculus-rational-v0`

Build next:

- The first generated bridge rows now cover LU/nullspace replay with checked
  bad product-entry and bad nullspace-component evidence, rank/nullity replay, residual bounds, eigenpair
  witnesses, characteristic-polynomial replay with checked bad trace evidence,
  and finite random-matrix moments.
- Add narrower concept rows for matrix multiplication, kernel/image, dual basis,
  transpose, tensor bilinear map, Gram matrix, projection, and finite-field
  linear algebra when one row can serve multiple packs.
- Promote rational infeasibility rows through QF_LRA/Farkas and finite-field
  table rows through replay or QF_UF/Alethe.
- Add a matrix corpus note that explains which rows can become solver
  regressions without turning education examples into performance claims.

Graduation:

- Matrix rows can be queried by computation type: witness replay, Farkas
  infeasibility, finite-field replay, or Lean horizon.

### 7. Abstract Algebra

Current packs:

- `finite-groups-v0`
- `finite-monoids-v0`
- `finite-permutation-groups-v0`
- `finite-group-actions-v0`
- `finite-rings-v0`
- `finite-fields-v0`
- `finite-algebra-homomorphisms-v0`
- `finite-ideals-v0`
- `finite-modules-v0`
- `finite-vector-spaces-v0`
- `finite-dual-spaces-v0`
- `finite-tensor-products-v0`
- `polynomial-identities-v0`
- `polynomial-factorization-rational-v0`

Build next:

- The first generated algebra-map bridge rows now cover homomorphism
  preservation, kernel/image replay, quotient maps, ideal closure, module
  actions, tensor bilinearity, and finite group actions.
- Split remaining broad finite algebra topics only when a new row can serve
  multiple packs: table axiom replay, orbit/stabilizer refinements, Burnside,
  units/idempotents, polynomial factorization, and representation-theory
  horizons.
- Use `family_finite_algebra_alethe` as the first family row and add narrower
  children only when dashboards need better routing.
- Keep the promoted polynomial-identity false-root row tied to the
  QF_LIA/Diophantine regression; promote factorization only when the source
  artifact adds distinct coefficient, root, or irreducibility pressure. The
  current factorization promotion is the fixed discriminant obstruction for
  `x^2 + 1`, checked through QF_LRA/Farkas after exact replay computes
  `D = -4`.
- Keep structure theorems, arbitrary groups/rings/modules, representation
  theory, and category-level facts as Lean-horizon.

Graduation:

- Equality-heavy algebra conflicts have checked Alethe or a named missing
  Alethe-to-Lean route; table replay remains distinct from theorem proof.

### 8. Real Analysis

Current packs:

- `rationals-lra-v0`
- `reals-rcf-shadow-v0`
- `real-analysis-rational-v0`
- `sequence-limit-shadow-v0`
- `bounded-monotone-sequence-v0`
- `finite-recurrence-prefix-v0`
- `finite-root-finding-v0`
- `finite-separation-v0`
- `finite-kkt-v0`
- `finite-active-set-qp-v0`
- `finite-sdp-v0`
- `finite-gradient-descent-v0`
- `finite-line-search-v0`
- `finite-wolfe-line-search-v0`
- `finite-projected-gradient-v0`
- `finite-proximal-gradient-v0`
- `metric-continuity-v0`
- `calculus-algebraic-shadow-v0`
- `calculus-riemann-sum-v0`
- `multivariable-calculus-rational-v0`
- `finite-compactness-v0`
- `finite-connectedness-v0`
- `finite-continuous-maps-v0`

Landed:

- Bridge rows for metric ball, bounded epsilon-delta shadow, compactness
  shadow, connectedness shadow, and continuity-by-preimage.
- Bridge rows for rational interval replay, sequence-tail shadows,
  Cauchy-tail shadows, squeeze shadows, derivative-identity shadows, and
  integration horizons.

Build next:

- Promote exact rational bad-bound rows through QF_LRA/Farkas.
- Keep `sequence-limit-shadow-v0`'s promoted bounded Cauchy-tail and bad
  reciprocal-tail rows plus `bounded-monotone-sequence-v0`'s bad upper-bound
  and bad tail-gap source rows replay-only with separate checked `qf-lra-*`
  proof rows tied to source QF_LRA/Farkas artifacts; keep
  `finite-recurrence-prefix-v0`'s bad finite-value and bad affine-step source
  rows replay-only with separate checked `qf-lra-*` proof rows tied to their
  source QF_LRA/Farkas artifacts; keep
  `finite-root-finding-v0`'s bad Newton-step and bad bisection-width source
  rows replay-only with separate checked `qf-lra-*` proof rows tied to their
  source QF_LRA/Farkas artifacts; keep `finite-separation-v0`'s bad
  convex-combination and bad separator source rows replay-only with separate
  checked `qf-lra-*` proof rows tied to their source QF_LRA/Farkas artifacts;
  keep `finite-kkt-v0`'s bad stationarity and bad
  complementarity rows tied to their source QF_LRA/Farkas artifacts; keep
  `finite-active-set-qp-v0`'s bad free-gradient, bad inactive-slack, and bad
  degenerate-multiplier rows tied to their source QF_LRA/Farkas artifacts; keep `finite-sdp-v0`'s bad objective, bad duality-gap, and bad slack-entry rows tied to their
  source QF_LRA/Farkas artifact; keep `finite-gradient-descent-v0`'s bad decrease,
  bad step-coordinate, and bad descent-bound rows tied to their source QF_LRA/Farkas artifacts; keep `finite-line-search-v0`'s bad Armijo,
  bad descent-direction, and bad accepted-candidate rows tied to their source QF_LRA/Farkas artifacts; keep
  `finite-wolfe-line-search-v0`'s bad minimizer, bad sufficient-decrease, and
  bad curvature rows tied to their source QF_LRA/Farkas artifacts; keep
  `finite-projected-gradient-v0`'s bad projection and bad projected-decrease
  rows tied to their source QF_LRA/Farkas artifacts; keep
  `finite-proximal-gradient-v0`'s bad proximal
  point, bad composite-decrease, and bad box-proximal-point rows tied to their source QF_LRA/Farkas artifacts; keep
  `finite-chebyshev-systems-v0`'s explicit duplicate-node,
  bad interpolation-sample, and bad alternation-magnitude `qf-lra-*` rows tied
  to their source QF_LRA/Farkas artifacts while the malformed source rows remain
  exact replay; and keep general
  convergence, Cauchy completeness, monotone convergence, closed-form
  recurrence solving, root existence, Newton/bisection convergence, separation
  theorems, KKT sufficiency, active-set method theory, SDP duality,
  descent-rate, Wolfe/line-search convergence, projected-gradient convergence, proximal-gradient convergence,
  asymptotics, and stability in the Lean-horizon lane.
- Keep `calculus-riemann-sum-v0`'s promoted false-integral row tied to the
  source QF_LRA/Farkas artifact, and keep FTC/integrability statements in the
  Lean-horizon lane.
- Keep `calculus-algebraic-shadow-v0`'s promoted false-derivative row tied to
  the source QF_LRA/Farkas artifact, and keep differentiability-from-limits and
  MVT statements in the Lean-horizon lane.
- Keep completeness, Bolzano-Weierstrass, Heine-Borel, IVT, MVT, FTC, and
  general convergence as Lean-horizon.

Graduation:

- Every analysis lesson carries a "finite/bounded shadow vs theorem" statement.

### 9. Complex Analysis

Current packs:

- `complex-algebraic-v0`
- `complex-plane-transforms-v0`

Build next:

- Add concept rows for complex-as-real-pair, conjugation, norm, unit roots,
  Mobius transform, fixed polynomial root, and analytic-function horizon.
- Route algebraic claims through real-pair LRA/NRA or finite replay.
- Keep `complex-algebraic-v0`'s promoted bad product-coordinate and bad
  norm-squared rows tied to exact real-pair replay plus the source
  QF_LRA/Farkas artifacts.
- Keep `complex-plane-transforms-v0`'s promoted bad conjugation-product
  imaginary-part and bad unit-square real-part rows tied to source
  QF_LRA/Farkas artifacts after real-pair replay computes
  `conjugate(z*w) = conjugate(z)*conjugate(w) = 5 - 5i` and `i^2 = -1`.
- Keep holomorphicity, contour integration, residues, analytic continuation,
  and algebraic closure as Lean-horizon.

Graduation:

- Complex rows cannot be mistaken for analytic theorem coverage.

### 10. Topology

Current packs:

- `finite-topology-v0`
- `finite-quotient-topology-v0`
- `finite-specialization-order-v0`
- `metric-continuity-v0`
- `finite-compactness-v0`
- `finite-connectedness-v0`
- `finite-continuous-maps-v0`
- `finite-simplicial-homology-v0`
- `finite-chain-complex-torsion-v0`
- `finite-simplicial-cohomology-v0`
- `finite-universal-coefficient-shadow-v0`
- `finite-simplicial-cup-products-v0`

Build next:

- Landed concept rows for metric balls, compactness shadows, connectedness
  shadows, continuity-by-preimage, finite topology-operator/homeomorphism
  replay, finite quotient-topology replay, finite specialization-order replay,
  finite boundary-operator replay,
  finite chain-complex/homology replay, finite torsion-homology replay, finite
  cohomology replay, and finite cup-product replay. Add narrower
  cohomology-ring quotienting or theorem-invariance rows only when reuse or
  solver pressure justifies the split.
- Keep `finite-topology-v0`'s promoted missing-empty-set row tied to the
  source DIMACS artifact and checked Bool/CNF DRAT/LRAT route.
- Promote additional source-level-obvious bad topology rows to Bool/CNF, QF_UF,
  or LIA only when the mathematical object is fixed and tiny.
- Keep general compactness, connectedness, homotopy, homeomorphism invariance,
  homology/cohomology invariance, cohomology-ring laws, and topological spaces
  as Lean-horizon.

Graduation:

- Topology dashboards distinguish finite set-family replay from general
  topological theorem proof.

### 11. Measure Theory

Current packs:

- `finite-measure-v0`
- `finite-measure-monotonicity-v0`
- `finite-integration-v0`
- `finite-product-measure-v0`
- `finite-random-variables-v0`
- `finite-conditional-expectation-v0`
- `finite-martingales-v0`
- `finite-stochastic-kernels-v0`
- probability packs shared with `probability_theory`

Build next:

- Landed bridge rows for finite event-algebra/additivity and finite
  product-measure/integration replay. Add narrower concept rows only when
  multiple packs need distinct finite sigma-algebra, monotonicity,
  simple-function integral, marginal, finite Fubini, random-variable
  pushforward, conditioning-by-partition, or convergence-theorem vocabulary.
- Promote false finite measure/probability tables through QF_LRA/Farkas.
- Keep Lebesgue measure, dominated convergence, monotone convergence, and
  almost-everywhere reasoning as Lean-horizon.

Graduation:

- Finite measure rows show the exact finite universe and never imply
  sigma-finite or Lebesgue theorem coverage.

### 12. Probability Theory

Current packs:

- `finite-probability-v0`
- `finite-random-variables-v0`
- `finite-conditional-expectation-v0`
- `finite-martingales-v0`
- `finite-stochastic-kernels-v0`
- `finite-hitting-times-v0`
- `finite-concentration-v0`
- `finite-markov-chain-v0`
- `finite-product-measure-v0`

Build next:

- Add concept rows for probability table, conditional probability, Bayes
  update, pushforward distribution, independence, stochastic kernel, Markov
  transition, hitting-time equation, martingale condition, stopping-time
  replay, and concentration bound shadow.
- Promote bad normalization, conditional-probability, posterior, kernel-row, expected-time, and
  concentration rows through QF_LRA/Farkas or QF_LIA when exact counts are the
  natural source.
- Keep continuous distributions, stochastic-process limit theorems, optional
  stopping in general, and asymptotic concentration as Lean-horizon.

Graduation:

- Probability rows can be queried by finite table shape and proof route.

### 13. Statistics

Current packs:

- `descriptive-statistics-v0`
- `least-squares-regression-v0`
- `exact-statistical-tests-v0`
- `finite-concentration-v0`
- `finite-probability-v0`
- `random-matrix-finite-v0`

Build next:

- Add concept rows for finite sample statistic, variance identity,
  contingency table, exact binomial tail, Fisher table, least-squares normal
  equations, residual orthogonality, finite sampling, and numerical-honesty
  status.
- Promote bad count/table rows through QF_LIA and bad rational coefficient or
  residual rows through QF_LRA/Farkas, including exact Fisher p-value
  contradictions after fixed-margin replay.
- Mark simulations, MCMC, VI, asymptotic normality, and calibration claims as
  numerical or proof-horizon, never checked proof.

Graduation:

- Every statistics row says whether it is exact finite enumeration,
  certificate-backed infeasibility, or numerical experiment metadata.

### 14. Optimization And Convexity

Current packs:

- `linear-optimization-v0`
- `convexity-rational-v0`
- `least-squares-regression-v0`
- `multivariable-calculus-rational-v0`
- `numerical-linear-algebra-v0`
- `finite-root-finding-v0`
- `finite-separation-v0`
- `finite-kkt-v0`
- `finite-active-set-qp-v0`
- `finite-sdp-v0`
- `finite-gradient-descent-v0`
- `finite-line-search-v0`
- `finite-wolfe-line-search-v0`
- `finite-projected-gradient-v0`
- `finite-proximal-gradient-v0`

Build next:

- Landed bridge rows for LP objective-threshold/Farkas replay and rational
  convexity/gradient shadows. Finite root-finding now adds exact iterate and
  residual-decrease replay, and finite separation adds convex-hull/supporting
  face replay plus replay-only bad separation source rows and separate checked
  proof rows. Finite KKT now adds
  constrained-quadratic stationarity, complementary-slackness replay, and
  checked bad stationarity plus bad complementarity evidence. Finite active-set
  QP now adds exact
  unconstrained-minimizer replay, active-face candidate replay, inactive slack,
  degenerate active-bound replay, and bad free-gradient, bad inactive-slack,
  plus bad degenerate-multiplier Farkas evidence. Finite SDP now adds two-by-two PSD,
  trace/objective, slack, dual-gap replay, and checked bad duality-gap evidence. Finite gradient descent now adds
  exact quadratic step and descent-bound replay plus checked bad descent-bound
  evidence. Finite line search now adds Armijo trial rejection,
  descent-direction sign replay, and accepted-backtrack replay plus checked bad
  descent-direction evidence. Finite Wolfe line
  search now adds sufficient-decrease and curvature replay plus checked bad
  minimizer, bad sufficient-decrease, and bad curvature evidence. Finite projected
  gradient now adds interval projection after a trial step. Finite proximal
  gradient now adds L1 soft-threshold and box-plus-L1 constrained replay after
  a trial step. Convexity rational rows now include checked bad midpoint and
  affine-threshold evidence. Add narrower
  rows only when multiple packs need distinct duality, working-set pivots,
  higher-dimensional SDP, strong-Wolfe/nonconvex
  line-search, group-lasso proximal, affine-threshold variants beyond the
  current row, or stochastic convergence vocabulary.
- Promote small infeasible LP/convexity/root-finding/separation/KKT/active-set
  QP/SDP/descent, line-search, Wolfe-line-search, projected-gradient, and
  proximal-gradient rows through QF_LRA/Farkas.
- Keep general convex analysis, SDP strong duality, KKT sufficiency, and algorithm convergence
  as Lean-horizon until proof support exists.

Graduation:

- At least one standalone learner page traces an LP claim to a Farkas
  certificate and checker.

### 15. Numerical Analysis

Current packs:

- `numerical-linear-algebra-v0`
- `finite-euler-method-v0`
- `bounded-dynamics-v0`
- `matrix-invariants-v0`
- `spectral-linear-algebra-v0`
- `finite-operator-v0`
- `finite-root-finding-v0`

Build next:

- Add concept rows for residual bound, solution box, iterative one-step
  contraction, Euler step, fixed-step error, interval bound, root-finding
  iteration, stability horizon, and floating-point honesty.
- Use exact rational shadows where possible; treat floating-point rows as
  reproducibility checks with explicit tolerance/seed metadata.
- Promote false residual/error/iterate rows through QF_LRA/Farkas when they are
  exact.

Graduation:

- Numerical rows distinguish exact rational certificate, finite deterministic
  computation, and approximate experiment.

### 16. Differential Equations And Dynamical Systems

Current packs:

- `bounded-dynamics-v0`
- `finite-euler-method-v0`
- `finite-hitting-times-v0`
- `finite-markov-chain-v0`

Build next:

- Add concept rows for recurrence trace, bounded invariant, threshold
  reachability, Euler transition, discrete flow, absorbing Markov chain, and
  existence/uniqueness horizon.
- Keep `bounded-dynamics-v0`'s promoted bad transition-step, bad
  threshold-step, and invariant-bound rows tied to exact recurrence replay plus
  separate `qf-lra-*` QF_LRA/Farkas artifacts.
- Promote bad finite transitions, expected-time equations, and invariant
  failures through LRA/LIA or replay according to source shape.
- Keep continuous dynamics, PDEs, chaos, and existence/uniqueness theory as
  Lean-horizon.

Graduation:

- Dynamics pages state whether a row is a discrete bounded system, numerical
  step, stochastic finite system, or continuous theorem target.

### 17. Geometry

Current packs:

- `coordinate-geometry-v0`
- `incidence-geometry-v0`
- `rigid-configuration-geometry-v0`
- `affine-geometry-v0`
- `orientation-area-geometry-v0`
- `finite-circle-geometry-v0`
- `finite-inversion-geometry-v0`
- `finite-cyclic-geometry-v0`
- `complex-plane-transforms-v0`

Build next:

- Add concept rows for midpoint, distance, collinearity, affine map,
  incidence, line equations, barycentric coordinate, signed area, orientation,
  determinant scaling, isometry shadow, and rigidity horizon.
- Keep `coordinate-geometry-v0`'s promoted bad midpoint-coordinate and
  squared-distance rows tied to exact replay plus the source QF_LRA/Farkas
  artifacts.
- Keep `incidence-geometry-v0`'s promoted bad intersection-coordinate and
  point-on-line rows tied to exact replay plus the source QF_LRA/Farkas
  artifacts.
- Keep `rigid-configuration-geometry-v0`'s promoted bad translation-image and
  distance-table rows tied to exact replay plus the source QF_LRA/Farkas
  artifacts.
- Keep `affine-geometry-v0`'s promoted bad midpoint-coordinate and
  bad collinearity-determinant and bad distance-preservation rows tied to
  exact affine replay plus the source QF_LRA/Farkas artifacts.
- Keep `orientation-area-geometry-v0`'s promoted bad affine-area-scaling and
  bad orientation rows tied to exact signed-area replay plus the source
  QF_LRA/Farkas artifacts.
- Keep `finite-circle-geometry-v0`'s promoted bad radius and bad
  line-intersection rows tied to exact circle-coordinate replay plus the source
  QF_LRA/Farkas artifacts.
- Keep `finite-inversion-geometry-v0`'s promoted bad inverse-coordinate and
  inverse-distance-product rows tied to exact inversion replay plus the source
  QF_LRA/Farkas artifacts.
- Keep `finite-cyclic-geometry-v0`'s promoted bad diagonal-intersection,
  bad opposite-angle, and bad Ptolemy rows tied to exact cyclic-configuration
  replay plus the source QF_LRA/Farkas artifacts.
- Promote additional false affine/distance/orientation/incidence/circle/inversion/cyclic
  claims through QF_LRA/Farkas or NRA only when they add distinct exact-rational
  pressure beyond the current area-scaling, nontrivial circle-line,
  inverse-distance-product, higher-degree polynomial-geometry, or
  theorem-reconstruction rows.
- Keep differential geometry, algebraic geometry, global geometry, and
  topology-heavy geometry as Lean-horizon.

Graduation:

- Geometry rows expose whether they are coordinate algebra checks or theorem
  reconstruction targets.

### 18. Functional Analysis And Operator Theory

Current packs:

- `finite-operator-v0`
- `inner-product-spaces-rational-v0`
- `finite-dual-spaces-v0`
- `finite-chebyshev-systems-v0`
- `spectral-linear-algebra-v0`
- `numerical-linear-algebra-v0`

Build next:

- Landed bridge rows for finite inner-product/projection replay and finite
  operator/Chebyshev replay, covering finite-dimensional norms, Gram matrices,
  projections, matrix operators, Chebyshev grids, interpolation matrices, and
  alternating residual witnesses.
- Add narrower concept rows for dual spaces, adjoints, spectral decomposition,
  or Banach/Hilbert horizons only when multiple packs need the same vocabulary.
- Keep `finite-operator-v0`'s promoted bad `l1` norm, bad operator-bound, and
  bad Chebyshev-prefix rows tied to exact replay plus the source QF_LRA/Farkas
  artifacts.
- Keep `inner-product-spaces-rational-v0`'s promoted bad negative-norm and
  bad projection-orthogonality rows tied to exact replay plus the source
  QF_LRA/Farkas artifacts.
- Promote additional finite-dimensional bad norm/operator/projection/
  interpolation rows through QF_LRA/Farkas where exact rational constraints
  apply.
- Keep Banach-space theorems, compact operators, general Chebyshev spaces,
  projection theorem, and topological duals as Lean-horizon.

Graduation:

- Functional-analysis rows make finite-dimensional shadows useful without
  implying infinite-dimensional theorem coverage.

## Cross-Resource Build Plan

### SMT Fragment Atlas

Use the math curriculum as a source of fragment demand:

- Bool/CNF: logic, finite sets, graph coloring, topology set families.
- QF_BV: bounded naturals, residue arithmetic, finite fields, bit-level graph
  encodings.
- QF_LIA: integer equations, modular obstructions, exact counts, rank/count
  constraints.
- QF_LRA: rational inequalities, LP, probability tables, residual bounds.
- QF_NRA/RCF: algebraic real/complex/geometry/calculus shadows.
- QF_UF/Alethe: finite functions, congruence, homomorphisms, quotient maps.
- Quantifier finite expansion: finite predicate logic and bounded first-order
  examples.
- Lean horizon: induction, completeness, topology, measure, asymptotics.

Next work:

- Keep fragment-demand back-links from field dashboards and query guides tied
  to atlas rows.
- Keep the generated
  [curriculum-pressure-by-fragment](generated/curriculum-pressure-by-fragment.md)
  view fresh as new route metadata and proof statuses land.

### Proof Certificate Cookbook

Use curriculum examples as canonical tiny recipes:

- CNF/LRAT: proposition refutation, graph non-colorability, finite cover miss.
- QF_BV: residue nonresidue, finite field/ring fixed-width contradiction.
- QF_LIA: gcd obstruction, exact count contradiction, rank coefficient miss.
- QF_LRA: infeasible linear system, LP threshold, bad probability table.
- QF_UF/Alethe: function single-valuedness, homomorphism preservation, quotient
  congruence.
- Lean horizon: induction schema, completeness theorem, compactness,
  measure-convergence theorem.

Next work:

- Add one tamper/rejection fixture per major route.
- Add a "math example using this route" section to each recipe.

### Rules, Law, And Policy Resources

The rules/law lane should reuse the math curriculum instead of inventing a
separate logic story:

| Math Resource | Rules/Law Reuse |
|---|---|
| finite predicates | eligibility conditions, facts, actors, resources |
| sets and relations | membership, roles, jurisdictions, obligations |
| graph reachability | workflow states, dependency chains, delegated authority |
| orders/lattices | precedence, hierarchy, classification levels |
| linear arithmetic | thresholds, benefits, tax brackets, deadlines |
| optimization | minimum/maximum entitlement, allocation, caps |
| probability/statistics | audit sampling, risk scoring, statistical evidence |
| proof routes | consistency, coverage, equivalence, monotonicity checks |

Detailed mapping:
[RULES-LAW-CROSSWALK.md](RULES-LAW-CROSSWALK.md) records the reusable check
shapes, source math packs, Axeyum fragments, proof routes, and the current
`benefit-eligibility-v0`, `authorization-policy-v0`, and
`tax-benefit-arithmetic-v0` mappings, plus the
`procurement-scoring-v0` exclusion/deadline/bid-cap/bonus mapping and the
`grant-allocation-v0` rational-share/budget/cap mapping, plus the
`category-equivalence-v0` category-normalization and checked QF_UF/Alethe
mapping.

Next work:

- Use the completed `benefit-eligibility-v0`, `authorization-policy-v0`, and
  `tax-benefit-arithmetic-v0` Bool/QF_LIA proof harnesses, plus the
  `procurement-scoring-v0` debarment/deadline/bid-cap/monotonicity fixtures, as
  reference patterns for generated multi-row coverage/equivalence and
  threshold/cap/deadline queries. Use `grant-allocation-v0` as the QF_LRA/Farkas
  reference for rational allocation, exact shares, and budget-balance queries.
  Use `category-equivalence-v0` as the checked QF_UF/Alethe reference for
  role/category equivalence and quotient-like classification queries.
  Use `workflow-reachability-v0` as the finite graph/state-machine reference
  for workflow transitions, terminal states, and bounded path queries.
  Status: the deterministic generated query-row JSON under
  [`../rules-as-code/generated/queries/`](../rules-as-code/generated/queries/)
  now materializes 1,942 bounded generated rows from the seven current rule
  packs, and
  the generated
  [`rules-query-dashboard.md`](../rules-as-code/generated/rules-query-dashboard.md)
  exposes the bounded row counts, generated row counts, query artifacts, and
  query-family inventory.
- Reuse pack schema ideas before creating law-specific schema fields.
- Keep citations and source provenance mandatory for legal/policy examples.

### Complementary Software Libraries

Only build libraries after repeated manual work proves the need.

Candidate library modules:

| Library | Source Of Demand | First Contents |
|---|---|---|
| finite graph encoders | graph packs and solver regressions | coloring, reachability, cuts, matching |
| finite algebra encoders | algebra packs and QF_UF/BV tests | tables, homomorphisms, quotient maps |
| exact matrix fixtures | linear algebra, optimization, numerical rows | LU, rank, residual, eigenpair fixtures |
| finite probability tables | probability, statistics, measure rows | normalization, conditioning, kernels |
| proof-route fixtures | cookbook and resource regressions | tiny CNF, LIA, LRA, UF, BV examples |
| resource data accessors | repeated consumer scripts | typed concept/pack/proof-route views |

Boundary rule: do not create a crate until there are at least three duplicated
call sites or one external consumer.

## Prioritized Execution Queue

Pick one item per commit unless the change is purely navigational.

1. Landed: add concept rows for linear algebra computation families: LU,
   rank/nullity, residual bound, eigenpair, characteristic polynomial, and
   random-matrix finite moment.
2. Landed: add concept rows for algebra maps: homomorphism, kernel/image,
   quotient, ideal, module, tensor bilinearity, and group action.
3. Landed: add "math example using this route" sections to the six active
   proof cookbook recipes.
4. Landed: promote `finite-stochastic-kernels-v0` for small exact-rational
   QF_LRA/Farkas bad-row normalization and bad composition-entry
   contradictions with strong learner value.
5. Landed: promote `finite-ideals-v0` for explicit QF_UF/Alethe
   additive-closure membership and quotient-ring representative congruence
   rows, separating exact bad-ideal replay from checked equality artifacts.
6. Landed: add a rules/law crosswalk doc that maps finite predicates,
   arithmetic thresholds, graph reachability, precedence, and proof routes to
   policy/rule checks.
7. Landed: complete the `benefit-eligibility-v0` Bool/QF_LIA proof harness for
   consistency, coverage, fixed no-exception monotonicity, and active-threshold
   implementation equivalence.
8. Landed: add `authorization-policy-v0` as the second rules/law pack, with
   source-linked Bool/QF_LIA proof fixtures for tenant isolation, explicit deny
   precedence, admin tenant guarding, and bounded implementation equivalence.
9. Landed: add `tax-benefit-arithmetic-v0` as the third rules/law pack, with
   source-linked Bool/QF_LIA proof fixtures for non-negative benefit, cap,
   active phase-out monotonicity, and bounded implementation equivalence.
10. Landed: add the generated
   [`rules-query-dashboard.md`](../rules-as-code/generated/rules-query-dashboard.md)
   for bounded coverage, equivalence, threshold, cap, version-delta, and
   monotonicity query-family counts across the initial rule packs.
11. Landed: add deterministic generated query-row JSON under
   [`../rules-as-code/generated/queries/`](../rules-as-code/generated/queries/)
   for the first three rules/law packs: complete applicant coverage and
   income-monotonicity rows, bounded role/action/version requests and adjacent
   version-delta rows, and tax/benefit amount plus phase-out rows. The
   rules-as-code validator replays all 1,374 rows from committed source pack
   models, and the standard rules check now fails on generated drift.
12. Landed: add `procurement-scoring-v0` as the fourth rules/law pack, with
   source-linked Bool/QF_LIA proof fixtures for debarment exclusion, late
   submission, bid-cap enforcement, score monotonicity, and bounded
   implementation equivalence. The generated query-row JSON now brings the
   rules/law surface to 1,626 replayed rows across four packs for that increment.
13. Landed: add `grant-allocation-v0` as the fifth rules/law pack, with
   source-linked QF_LRA/Farkas proof fixtures for budget balance, shelter and
   clinic minimum shares, administrative caps, and bounded implementation
   equivalence. The generated query-row JSON now brings the rules/law surface
   to 1,766 replayed rows across five packs.
14. Landed: add `category-equivalence-v0` as the sixth rules/law pack, with
   finite category/program replay, generated equivalence-pair rows, and
   source-linked checked QF_UF/Alethe artifacts for category congruence and
   implementation equivalence. The generated query-row JSON now brings the
   rules/law surface to 1,774 bounded generated rows across six packs.
15. Landed: add `workflow-reachability-v0` as the seventh rules/law pack, with
   finite transition replay, generated two-step reachability rows,
   terminal-state rows, and source-linked checked Bool/QF_LIA artifacts for
   no-skip, terminal-state, and implementation-equivalence obligations. The
   generated query-row JSON now brings the rules/law surface to 1,942 bounded
   generated rows across seven packs.
16. Landed: add
   [`RULES-LAW-QUERIES.md`](RULES-LAW-QUERIES.md) plus
   `scripts/query-rules-as-code.py` so downstream consumers can query rule
   packs, checked obligations, generated query families, and bounded generated
   rows without parsing JSON by hand. `just rules-as-code` smoke-checks the
   current procurement queries.
17. Landed: add
   [`RULES-LAW-PATTERN-MATRIX.md`](RULES-LAW-PATTERN-MATRIX.md) so current
   rules/law patterns map back to math concept rows, proof routes, pack
   checks, generated query families, and copyable query commands before any
   new rule ontology or rule-pack count push.
15. Landed: add
   [`rules-law-trust-boundary.md`](../learn/rules-law-trust-boundary.md) as the
   learner-facing rules/law trust-boundary walkthrough from source rule to
   formal model, replayed witness, checked obligation, and explicit horizon.
16. Landed: add a consumer-query recipe for "find all packs for a field and
   route" through the `--route` filter in
   `scripts/query-foundational-resources.py` and
   [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md).
10. Landed: add negative validator fixtures for the foundational example-pack
   schema, covering unknown fields, metadata/check id drift, and missing
   witness references.
11. Landed: audit `planned` vs `covered` statuses through
    [generated/curriculum-status-audit.md](generated/curriculum-status-audit.md)
    so generated resource maturity is separate from source curriculum DAG
    status.
12. Landed: add one route-specific tamper/rejection test per active proof
    certificate route. Boolean CNF/LRAT, QF_BV DRAT, QF_LRA/Farkas,
    QF_LIA/Diophantine, and QF_UF/Alethe now each mutate an emitted resource
    certificate and require checker rejection in the route regression suite.
13. Landed: add generated probability/statistics bridge-concept rows for
    `bridge_probability_mass_table`, `bridge_pushforward_distribution`,
    `bridge_stochastic_kernel`, `bridge_conditional_expectation`, and
    `bridge_tail_count_obstruction`, tying existing finite probability,
    measure, stochastic-kernel, random-variable, exact-test, concentration,
    Markov-chain, hitting-time, and martingale packs to shared finite-table
    vocabulary.
14. Landed: add generated proof/logic bridge-concept rows for
    `bridge_refutation_query`, `bridge_finite_proof_pattern`,
    `bridge_finite_quantifier_expansion`, and
    `bridge_bounded_induction_obligation`, tying existing proof-method,
    finite-predicate, induction, natural-arithmetic, and Boolean/CNF packs to
    shared finite-proof vocabulary.
15. Landed: add generated proof-object anatomy bridge-concept rows for
    `bridge_boolean_cnf_lrat_anatomy`, `bridge_qf_lra_farkas_anatomy`,
    `bridge_qf_uf_alethe_anatomy`, and
    `bridge_qf_bv_bitblast_anatomy`, tying existing proof-object lessons,
    proof-cookbook recipes, and route tamper regressions to shared certificate
    vocabulary.
16. Landed: add generated set/foundations bridge-concept rows for
    `bridge_finite_boolean_algebra`,
    `bridge_partition_relation_roundtrip`,
    `bridge_finite_image_preimage_inverse`,
    `bridge_finite_bijection_cardinality`, and
    `bridge_cardinality_theorem_horizon`, tying existing finite-set,
    relation/function, equivalence-class, function-composition, finite
    cardinality, and cardinality-principle packs to shared set-theory boundary
    vocabulary.
17. Landed: promote `finite-group-actions-v0` through source-linked
    QF_UF/Alethe regressions for `qf-uf-bad-identity-action` and
    `qf-uf-bad-action-compatibility`. The artifacts
    `artifacts/examples/math/finite-group-actions-v0/smt2/bad-identity-action-alethe-conflict.smt2`
    and
    `artifacts/examples/math/finite-group-actions-v0/smt2/bad-compatibility-action-alethe-conflict.smt2`
    are checked by the corresponding `math_resource_uf_routes` regressions.
18. Landed: promote `finite-continuous-maps-v0` through a source-linked
    QF_UF/Alethe regression for the finite preimage-membership conflict. The artifact
    `artifacts/examples/math/finite-continuous-maps-v0/smt2/bad-preimage-membership-alethe-conflict.smt2`
    is checked by
    `cargo test -p axeyum-solver --test math_resource_uf_routes finite_continuous_maps_bad_preimage_emits_checked_alethe`.
19. Landed: promote `finite-product-measure-v0` through source-linked
    QF_LRA/Farkas regressions for `bad-product-measure-rejected` and
    `bad-product-marginal-rejected`. The artifacts
    `artifacts/examples/math/finite-product-measure-v0/smt2/bad-product-measure-farkas-conflict.smt2`
    and
    `artifacts/examples/math/finite-product-measure-v0/smt2/bad-product-marginal-farkas-conflict.smt2`
    are checked by `math_resource_lra_routes`.
20. Landed: promote `finite-random-variables-v0` through source-linked
    QF_LRA/Farkas regressions for `qf-lra-bad-pushforward` and
    `qf-lra-bad-expectation-through-pushforward`, while the original bad rows
    remain exact finite replay. The artifacts
    `artifacts/examples/math/finite-random-variables-v0/smt2/bad-pushforward-farkas-conflict.smt2`
    and
    `artifacts/examples/math/finite-random-variables-v0/smt2/bad-expectation-through-pushforward-farkas-conflict.smt2`
    are checked by `math_resource_lra_routes`.
21. Landed: promote `finite-integration-v0` through a source-linked
    QF_LRA/Farkas regression for `qf-lra-bad-expectation`, while
    `bad-expectation-rejected` remains exact finite replay. The artifact
    `artifacts/examples/math/finite-integration-v0/smt2/bad-expectation-farkas-conflict.smt2`
    is checked by
    `cargo test -p axeyum-solver --test math_resource_lra_routes finite_integration_bad_expectation_emits_checked_farkas`.
22. Landed: split and promote `finite-martingales-v0` through source-linked
    QF_LRA/Farkas regressions: `bad-stopped-expectation-rejected` and
    `bad-martingale-rejected` stay exact finite replay, while
    `qf-lra-bad-stopped-expectation` and `qf-lra-bad-martingale` own the
    checked proof-object refutations. The artifacts
    `artifacts/examples/math/finite-martingales-v0/smt2/bad-stopped-expectation-farkas-conflict.smt2`
    and
    `artifacts/examples/math/finite-martingales-v0/smt2/bad-martingale-farkas-conflict.smt2`
    are checked by
    `cargo test -p axeyum-solver --test math_resource_lra_routes finite_martingales_bad_stopped_expectation_artifact_emits_checked_farkas` and
    `cargo test -p axeyum-solver --test math_resource_lra_routes finite_martingales_bad_conditional_expectation_emits_checked_farkas`.
23. Landed: split `finite-markov-chain-v0` at the solver-reuse metadata layer
    so `bad-stochastic-row-rejected` and
    `bad-stationary-distribution-rejected` remain exact replay, while
    `qf-lra-bad-stochastic-row` and
    `qf-lra-bad-stationary-distribution` own checked QF_LRA/Farkas evidence.
    The source artifacts
    `artifacts/examples/math/finite-markov-chain-v0/smt2/bad-stochastic-row-farkas-conflict.smt2`
    and
    `artifacts/examples/math/finite-markov-chain-v0/smt2/bad-stationary-distribution-farkas-conflict.smt2`
    are checked by
    `cargo test -p axeyum-solver --test math_resource_lra_routes finite_markov_chain_bad_stochastic_row_artifact_emits_checked_farkas` and
    `cargo test -p axeyum-solver --test math_resource_lra_routes finite_markov_chain_bad_stationary_distribution_artifact_emits_checked_farkas`.
24. Landed: revisited the library boundary decision after promoted solver-reuse
    rows reached the consumer query layer. The decision remains JSON-first and
    in-repo: `scripts/query-foundational-resources.py packs --solver-reuse
    promoted --require-any` proves promoted rows are consumer-readable, but no
    external consumer or repeated typed API need justifies a crate or repo split.
25. Landed: promote `finite-concentration-v0` through a source-linked
    QF_LRA/Farkas regression for `qf-lra-bad-concentration-bound`. The artifact
    `artifacts/examples/math/finite-concentration-v0/smt2/bad-concentration-bound-farkas-conflict.smt2`
    is checked by
    `cargo test -p axeyum-solver --test math_resource_lra_routes finite_concentration_bad_tail_bound_artifact_emits_checked_farkas`.
26. Landed: promote `finite-conditional-expectation-v0` through source-linked
    QF_LRA/Farkas regressions for `bad-conditional-expectation-rejected`,
    `bad-total-expectation-rejected`, `bad-tower-property-rejected`, and
    `bad-variance-decomposition-rejected`. The
    artifacts are
    `artifacts/examples/math/finite-conditional-expectation-v0/smt2/bad-conditional-expectation-farkas-conflict.smt2`,
    `artifacts/examples/math/finite-conditional-expectation-v0/smt2/bad-total-expectation-farkas-conflict.smt2`,
    and
    `artifacts/examples/math/finite-conditional-expectation-v0/smt2/bad-tower-property-farkas-conflict.smt2`,
    plus
    `artifacts/examples/math/finite-conditional-expectation-v0/smt2/bad-variance-decomposition-farkas-conflict.smt2`;
    they are checked by
    `cargo test -p axeyum-solver --test math_resource_lra_routes finite_conditional_expectation_bad_table_emits_checked_farkas`,
    `cargo test -p axeyum-solver --test math_resource_lra_routes finite_conditional_expectation_bad_total_expectation_artifact_emits_checked_farkas`, and
    `cargo test -p axeyum-solver --test math_resource_lra_routes finite_conditional_expectation_bad_tower_property_artifact_emits_checked_farkas`, and
    `cargo test -p axeyum-solver --test math_resource_lra_routes finite_conditional_expectation_bad_variance_decomposition_artifact_emits_checked_farkas`.
27. Landed: split and promote `finite-hitting-times-v0` through source-linked
    QF_LRA/Farkas regressions: `bad-survival-mass-rejected` and
    `bad-expected-time-rejected` stay exact finite replay, while
    `qf-lra-bad-survival-mass` and `qf-lra-bad-expected-time` own the checked
    proof-object refutations. The artifacts
    `artifacts/examples/math/finite-hitting-times-v0/smt2/bad-survival-mass-farkas-conflict.smt2`
    and
    `artifacts/examples/math/finite-hitting-times-v0/smt2/bad-expected-time-farkas-conflict.smt2`
    are checked by
    `cargo test -p axeyum-solver --test math_resource_lra_routes finite_hitting_times_bad_survival_mass_artifact_emits_checked_farkas` and
    `cargo test -p axeyum-solver --test math_resource_lra_routes finite_hitting_times_bad_expected_time_emits_checked_farkas`.
28. Landed: promote `finite-euler-method-v0` through a source-linked
    QF_LRA/Farkas regression for `bad-euler-step-rejected`. The existing
    artifact
    `artifacts/examples/math/finite-euler-method-v0/smt2/bad-euler-step-farkas-conflict.smt2`
    is checked by
    `cargo test -p axeyum-solver --test math_resource_lra_routes finite_euler_bad_step_emits_checked_farkas`.
29. Landed: promote `polynomial-identities-v0` through a source-linked
    QF_LIA/Diophantine regression for `false-rational-root-rejected`. The
    artifact
    `artifacts/examples/math/polynomial-identities-v0/smt2/false-rational-root-diophantine-conflict.smt2`
    is checked by
    `cargo test -p axeyum-solver --test math_resource_lia_routes polynomial_identities_false_rational_root_emits_checked_diophantine_evidence`.
30. Landed: promote `finite-predicate-v0` through a source-linked Bool/CNF
    DRAT/LRAT regression for `forall-implies-exists-finite`. The artifact
    `artifacts/examples/math/finite-predicate-v0/cnf/forall-implies-exists.cnf`
    is checked by
    `cargo test -p axeyum-cnf --test math_resource_boolean_routes finite_predicate_forall_implies_exists_emits_checked_drat_and_lrat`.
31. Landed: promote `calculus-riemann-sum-v0` through a source-linked
    QF_LRA/Farkas regression for `false-integral-claim-rejected`. The artifact
    `artifacts/examples/math/calculus-riemann-sum-v0/smt2/false-integral-farkas-conflict.smt2`
    is checked by
    `cargo test -p axeyum-solver --test math_resource_lra_routes calculus_riemann_sum_false_integral_artifact_emits_checked_farkas`.
32. Landed: promote `sequence-limit-shadow-v0` through a source-linked
    QF_LRA/Farkas regression for `bounded-cauchy-tail-no-counterexample`. The
    artifact
    `artifacts/examples/math/sequence-limit-shadow-v0/smt2/bounded-cauchy-tail-farkas-conflict.smt2`
    is checked by
    `cargo test -p axeyum-solver --test math_resource_lra_routes sequence_limit_bounded_cauchy_tail_artifact_emits_checked_farkas`.
33. Landed: add `bounded-monotone-sequence-v0` with finite monotone-prefix
    replay, finite prefix supremum replay, finite tail-gap replay, and a
    source-linked QF_LRA/Farkas regression for a false upper bound; later
    extended with a false tail gap. These now live as replay-only malformed
    source rows plus separate checked `qf-lra-*` proof rows.
34. Landed: add `finite-recurrence-prefix-v0` with Fibonacci prefix replay,
    affine recurrence replay, companion-matrix state replay, and a
    source-linked QF_LRA/Farkas regression for a false Fibonacci value; later
    extended with a false affine step. These now live as replay-only malformed
    source rows plus separate checked `qf-lra-*` proof rows.
35. Landed: promote `multivariable-calculus-rational-v0` through a
    source-linked QF_LRA/Farkas regression for `bad-gradient-rejected`. The
    artifact
    `artifacts/examples/math/multivariable-calculus-rational-v0/smt2/bad-gradient-farkas-conflict.smt2`
    is checked by
    `cargo test -p axeyum-solver --test math_resource_lra_routes multivariable_calculus_bad_gradient_artifact_emits_checked_farkas`.
36. Landed: promote `calculus-algebraic-shadow-v0` through a source-linked
    QF_LRA/Farkas regression for `false-derivative-value-rejected`. The artifact
    `artifacts/examples/math/calculus-algebraic-shadow-v0/smt2/false-derivative-farkas-conflict.smt2`
    is checked by
    `cargo test -p axeyum-solver --test math_resource_lra_routes calculus_algebraic_false_derivative_artifact_emits_checked_farkas`.
37. Landed: promote `complex-plane-transforms-v0` through source-linked
    QF_LRA/Farkas regressions for `bad-unit-square-real-part-rejected` and
    `bad-conjugation-product-imaginary-rejected`. The artifacts
    `artifacts/examples/math/complex-plane-transforms-v0/smt2/bad-unit-square-real-part-farkas-conflict.smt2`
    and
    `artifacts/examples/math/complex-plane-transforms-v0/smt2/bad-conjugation-product-imaginary-farkas-conflict.smt2`
    are checked by the corresponding `complex_plane_bad_*` regressions in
    `math_resource_lra_routes`.
38. Landed: promote `induction-obligations-v0` through a source-linked
    QF_LIA arithmetic-DPLL regression for `sum-formula-step-bounded`. The
    artifact
    `artifacts/examples/math/induction-obligations-v0/smt2/bounded-step-counterexample-count-lia-conflict.smt2`
    is checked by
    `cargo test -p axeyum-solver --test math_resource_lia_routes induction_obligations_bounded_step_count_emits_checked_lia_dpll_evidence`.
39. Landed: promote `cardinality-principles-v0` through a source-linked
    QF_LIA/Diophantine regression for `overlap-additivity-count-conflict`. The
    artifact
    `artifacts/examples/math/cardinality-principles-v0/smt2/overlap-additivity-diophantine-conflict.smt2`
    is checked by
    `cargo test -p axeyum-solver --test math_resource_lia_routes cardinality_principles_overlap_additivity_emits_checked_diophantine_evidence`.
40. Landed: promote `polynomial-factorization-rational-v0` through a
    source-linked QF_LRA/Farkas regression for
    `irreducible-quadratic-discriminant-conflict`. The artifact
    `artifacts/examples/math/polynomial-factorization-rational-v0/smt2/irreducible-quadratic-discriminant-farkas-conflict.smt2`
    is checked by
    `cargo test -p axeyum-solver --test math_resource_lra_routes polynomial_factorization_irreducible_quadratic_discriminant_artifact_emits_checked_farkas`.
41. Landed: promote `reals-rcf-shadow-v0` through a source-linked QF_LRA/Farkas
    regression for `negative-discriminant-farkas-conflict`. The artifact
    `artifacts/examples/math/reals-rcf-shadow-v0/smt2/negative-discriminant-farkas-conflict.smt2`
    is checked by
    `cargo test -p axeyum-solver --test math_resource_lra_routes reals_rcf_shadow_negative_discriminant_artifact_emits_checked_farkas`.
42. Landed: promote `finite-measure-v0` through a source-linked QF_LRA/Farkas
    regression for `qf-lra-bad-complement-measure`. The artifact
    `artifacts/examples/math/finite-measure-v0/smt2/bad-complement-measure-farkas-conflict.smt2`
    is checked by
    `cargo test -p axeyum-solver --test math_resource_lra_routes finite_measure_bad_complement_artifact_emits_checked_farkas`.
43. Landed: add `finite-measure-monotonicity-v0` with normalized finite
    measure-table replay, subset monotonicity, union subadditivity, checked
    QF_LRA/Farkas rejection of false subset-measure and union-subadditivity
    rows, and a focused learner page.
44. Landed: add standalone finite topology and finite measure learner pages.
    `docs/learn/math/finite-topology-end-to-end.md` follows
    `finite-topology-v0` through finite topology axiom replay,
    closure/interior, metric-ball replay, and checked Bool/CNF
    missing-empty-set rejection; `docs/learn/math/finite-measure-end-to-end.md`
    follows `finite-measure-v0` through finite sigma-algebra replay, exact
    finite additivity, event complements, exact bad-complement replay, and
    checked QF_LRA/Farkas complement-additivity evidence.
45. Landed: add standalone linear optimization learner page.
    `docs/learn/math/linear-optimization-end-to-end.md` follows
    `linear-optimization-v0` through exact LP feasible-point replay,
    objective-threshold replay, checked QF_LRA/Farkas infeasible-threshold
    evidence, and tampered-certificate rejection.
46. Landed: add standalone finite probability mass-table learner page.
    `docs/learn/math/finite-probability-mass-tables-end-to-end.md` follows
    `finite-probability-v0` through exact PMF normalization, conditional
    probability replay, Bayes posterior replay, checked QF_LRA/Farkas
    bad-normalization rejection, checked bad-conditional-probability rejection,
    checked bad-posterior rejection, finite independence replay, and checked
    bad-independence rejection, total variation replay, and checked
    bad-total-variation rejection.
47. Landed: add standalone finite-operator learner page.
    `docs/learn/math/finite-operator-end-to-end.md` follows
    `finite-operator-v0` through exact finite-dimensional `l1` norm replay,
    row-sum operator-bound replay, finite Chebyshev recurrence replay,
    checked QF_LRA/Farkas bad norm/bound/prefix evidence, and the
    Banach/Hilbert/compact-operator Lean horizon.
48. Landed: add standalone bounded-dynamics learner page.
    `docs/learn/math/bounded-dynamics-end-to-end.md` follows
    `bounded-dynamics-v0` through exact recurrence trace replay, finite
    invariant checking, threshold reachability, replay-only bad transition-step,
    bad threshold-step, and bad invariant-bound rows, separate checked
    QF_LRA/Farkas proof rows, and the continuous-dynamics/ODE Lean horizon.
49. Landed: add standalone finite-Euler learner page.
    `docs/learn/math/finite-euler-method-end-to-end.md` follows
    `finite-euler-method-v0` through exact explicit-Euler transition replay,
    finite polynomial-solution error tables, monotone invariant checking,
    replay-only bad max-error, bad terminal-error, and bad-step rejection plus
    separate checked QF_LRA/Farkas proof rows, and the
    ODE/numerical-analysis Lean horizon.
50. Landed: add field-level curriculum-readiness consumer queries.
    `scripts/query-foundational-resources.py fields --field probability_theory`
    summarizes pack counts, check counts, proof-status counts, proof-cookbook
    route counts, solver-reuse statuses, sample packs, and Lean-horizon packs
    from the committed JSON contract; the foundational resource smoke check now
    includes a probability/Farkas field-readiness query.
51. Landed: add dynamics field-readiness consumer query coverage.
    `docs/foundational-resources/CONSUMER-QUERIES.md` now shows a
    `differential_equations_and_dynamical_systems` plus Farkas field-readiness
    query and a checked-row drill-down, tying the recent bounded-dynamics,
    finite-Euler, stochastic-kernel, and hitting-time resources to the public
    consumer boundary; the foundational resource smoke check now includes the
    dynamics/Farkas field-readiness query.
52. Landed: add generated geometry and complex-analysis bridge concepts.
    `bridge_coordinate_orientation_geometry` groups the coordinate, affine,
    and orientation/area packs as a finite exact-rational geometry replay
    concept; `bridge_complex_real_pair_transform` groups complex algebraic,
    complex-plane transform, and polynomial-factorization packs as a real-pair
    complex-analysis replay concept. The generated atlas now validates 42
    bridge rows and keeps broader synthetic/differential/analytic theorem
    claims in the Lean-horizon lane.
53. Landed: add generated functional-analysis bridge concepts.
    `bridge_inner_product_projection` groups inner-product, projection,
    residual, least-squares, and dual-space finite replay; and
    `bridge_finite_operator_chebyshev` groups finite operator bounds,
    Chebyshev recurrence, interpolation matrices, and alternating residual
    witnesses. That increment raised the generated atlas to 44 bridge rows and
    keeps Banach, Hilbert, compact-operator, minimax, and
    infinite-dimensional approximation claims in the Lean-horizon lane.
54. Landed: add generated measure-theory bridge concepts.
    `bridge_finite_measure_additivity` groups finite event-algebra,
    additivity, complement, monotonicity, subadditivity, and exact atom-sum replay; and
    `bridge_finite_product_integration` groups finite product tables,
    marginals, finite Fubini-style sums, simple-function integrals, and
    expectation replay. The generated atlas now validates 46 bridge rows and
    keeps Lebesgue measure, product-measure existence, convergence theorems,
    and almost-everywhere claims in the Lean-horizon lane.
55. Landed: add measure-theory field-readiness consumer query coverage.
    `docs/foundational-resources/CONSUMER-QUERIES.md` now shows
    measure/Farkas field readiness, measure bridge concept lookup, and checked
    measure-theory Farkas row drill-downs. The foundational resource smoke
    check now runs those same queries, tying finite measure, product-measure,
    integration, random-variable, conditional-expectation, martingale, kernel,
    hitting-time, and concentration resources to the public JSON consumer
    boundary.
56. Landed: add generated optimization/convexity bridge concepts.
    `bridge_lp_objective_farkas` groups exact LP feasibility,
    objective-threshold witnesses, and checked Farkas threshold conflicts; and
    `bridge_rational_convexity_shadow` groups finite midpoint/Jensen shadows,
    affine monotonicity, exact gradient replay, Hessian-minor witnesses, and
    least-squares normal-equation replay. The generated atlas now validates 48
    bridge rows and keeps duality, KKT sufficiency, SDP, and convergence claims
    in the Lean-horizon lane.
57. Landed: add optimization/convexity field-readiness consumer query coverage.
    `docs/foundational-resources/CONSUMER-QUERIES.md` now shows
    optimization/Farkas field readiness, LP-objective and convexity bridge
    lookup, and checked optimization/convexity Farkas row drill-downs. The
    foundational resource smoke check now runs those same queries, tying exact
    LP thresholds, finite convexity shadows, least-squares normal equations,
    gradient/Hessian replay, residual bounds, and matrix witnesses to the
    public JSON consumer boundary.
58. Landed: add `incidence-geometry-v0`.
    The new geometry pack validates exact line-equation replay, non-parallel
    line intersection, point-on-line replay, checked QF_LRA/Farkas rejection of
    false intersection-coordinate and incidence claims, and a
    projective/synthetic geometry Lean horizon.
    `bridge_coordinate_orientation_geometry` now includes the incidence pack,
    and the learner path includes a focused incidence end-to-end page.
59. Landed: add `rigid-configuration-geometry-v0`.
    The new geometry pack validates exact triangle distance-table replay,
    translation isometry replay, congruent-triangle distance replay, checked
    QF_LRA/Farkas rejection of false translation-image and distance-table
    claims, and a
    graph-rigidity/rigid-motion-classification Lean horizon. The geometry learner path
    now includes a focused rigid-configuration end-to-end page.
60. Landed: add `finite-root-finding-v0`.
    The new numerical-analysis pack validates exact bisection and Newton-step
    replay, fixed residual-decrease checking, checked QF_LRA/Farkas rejection
    of false Newton-iterate and bisection-width claims, and a root-finding
    convergence/stability Lean horizon. The learner path now includes a
    focused finite root-finding end-to-end page.
61. Landed: add `finite-separation-v0`.
    The new optimization/convexity pack validates exact convex-combination
    replay, separating-hyperplane score replay, supporting-face checking,
    replay-only false convex-combination and false separator source rows,
    separate checked `qf-lra-*` Farkas proof rows, and a separation/duality
    Lean horizon. The learner path now includes a focused finite
    hyperplane-separation end-to-end page.
62. Landed: add `finite-kkt-v0`.
    The new optimization/convexity pack validates exact constrained-quadratic
    grid replay, KKT stationarity/complementarity replay,
    checked QF_LRA/Farkas rejection of a false stationarity multiplier, and a
    KKT-sufficiency Lean horizon. The learner path now includes a focused finite
    KKT end-to-end page.
63. Landed: add `finite-sdp-v0`.
    The new optimization/convexity pack validates exact two-by-two PSD replay,
    trace/objective arithmetic, dual-slack matrix replay, zero duality-gap
    checking, checked QF_LRA/Farkas rejection of a false objective claim, and an
    SDP-duality Lean horizon. The learner path now includes a focused finite
    SDP end-to-end page.
64. Landed: add `finite-gradient-descent-v0`.
    The new optimization/convexity and numerical-analysis pack validates exact
    quadratic gradient replay, one descent step, objective-decrease and
    descent-bound replay, checked QF_LRA/Farkas rejection of a false decrease
    claim, and a convergence Lean horizon. The learner path now includes a
    focused finite gradient-descent end-to-end page.
65. Landed: add `finite-line-search-v0`.
    The new optimization/convexity and numerical-analysis pack validates exact
    descent-direction replay, Armijo trial rejection, one accepted backtracked
    step, checked QF_LRA/Farkas rejection of false Armijo acceptance, false
    descent-direction, and accepted-candidate claims, and a line-search
    convergence Lean horizon. The learner path now includes a focused finite
    line-search end-to-end page.
66. Landed: add `finite-projected-gradient-v0`.
    The new optimization/convexity and numerical-analysis pack validates exact
    gradient replay, one unconstrained trial step, interval projection,
    projected objective decrease, checked QF_LRA/Farkas rejection of false
    projected-point and projected-decrease claims, and a projected-gradient
    convergence Lean horizon. The
    learner path now includes a focused finite projected-gradient end-to-end
    page.
67. Landed: add `finite-proximal-gradient-v0`.
    The new optimization/convexity and numerical-analysis pack validates exact
    smooth-gradient replay, one ordinary trial step, L1 soft-threshold
    proximal replay, box-plus-L1 constrained replay, composite objective
    decrease, checked QF_LRA/Farkas rejection of false proximal-point, false
    composite-decrease, and false box-proximal claims, and a proximal-gradient convergence Lean horizon. The
    learner path now includes a focused finite proximal-gradient end-to-end
    page.
68. Landed: add `finite-wolfe-line-search-v0`.
    The new optimization/convexity and numerical-analysis pack validates exact
    descent-direction replay, exact line-minimizer replay, Wolfe
    sufficient-decrease and curvature replay, checked QF_LRA/Farkas rejection
    of false minimizer, sufficient-decrease, and curvature claims, and a Wolfe
    line-search Lean horizon. The
    learner path now includes a focused finite Wolfe line-search end-to-end
    page.
69. Landed: add `finite-active-set-qp-v0`.
    The new optimization/convexity, numerical-analysis, linear-algebra, and
    real-analysis pack validates exact unconstrained-minimizer replay,
    active-face candidate replay, inactive-constraint slack, KKT
    stationarity/complementarity, checked QF_LRA/Farkas rejection of a false
    free-gradient claim, and an active-set-method Lean horizon. The learner path
    now includes a focused finite active-set QP end-to-end page.
70. Landed: add `finite-circle-geometry-v0`.
    The new geometry, linear-algebra, and real-analysis pack validates exact
    point-on-circle replay, tangent-line/radius perpendicularity,
    chord-midpoint perpendicularity, circle-line intersection replay, checked
    QF_LRA/Farkas rejection of false radius and line-intersection claims, and a
    circle-geometry Lean horizon. The learner path now includes a focused
    finite circle-geometry end-to-end page.
71. Landed: add `finite-inversion-geometry-v0`.
    The new geometry, linear-algebra, and real-analysis pack validates exact
    unit-circle inversion replay, inverse-distance product checking,
    collinearity replay, checked QF_LRA/Farkas rejection of a false
    inverse-coordinate claim, and an inversion-geometry Lean horizon. The
    learner path now includes a focused finite inversion-geometry end-to-end
    page.
72. Landed: add `finite-cyclic-geometry-v0`.
    The new geometry, linear-algebra, and real-analysis pack validates exact
    cyclic quadrilateral replay, diagonal-intersection and
    diagonal-perpendicularity replay, opposite-angle dot-product replay,
    rational Ptolemy replay, checked QF_LRA/Farkas rejection of false
    diagonal-intersection, opposite-angle, and Ptolemy claims, and a
    cyclic-geometry Lean horizon. The learner
    path now includes a focused
    finite cyclic-geometry end-to-end page.
73. Landed: add
    [`matrix-computation-index.md`](../learn/math/matrix-computation-index.md).
    The new learner index groups LU, rank/nullity, residual, projection,
    eigenpair, characteristic-polynomial, finite random-matrix, chain-complex,
    operator, module, and tensor rows by proof route, with explicit
    finite-replay, QF_LRA/Farkas, QF_UF/Alethe, QF_LIA/Diophantine,
    Lean-horizon, and numerical-honesty boundaries.
74. Landed: add
    [`analysis-calculus-theorem-horizon-map.md`](../learn/math/analysis-calculus-theorem-horizon-map.md).
    The new learner/planning map groups real completeness, IVT/MVT/FTC,
    compactness, convergence, root-finding, optimization, measure/probability,
    functional-analysis/operator, and dynamics theorem horizons by current
    finite shadow, checked evidence route, missing Lean/theorem dependency, and
    next build artifact.
75. Landed: add
    [`matrix-corpus-benchmark-boundary.md`](../learn/math/matrix-corpus-benchmark-boundary.md).
    The new learner/planning note separates matrix educational resources,
    solver regressions, benchmark-corpus rows, and theorem-horizon claims, and
    records the promotion checklist before matrix rows support solver-reuse or
    performance language.
76. Landed: add
    [`tax-benefit-arithmetic-v0`](../rules-as-code/examples/tax-benefit-arithmetic-v0/)
    as the third rules/law pack, reusing integer threshold, cap, phase-out,
    effective-date, finite replay, and Bool/QF_LIA proof-route patterns.
77. Landed: add
    [`rules-query-dashboard.md`](../rules-as-code/generated/rules-query-dashboard.md)
    as the generated bounded-query surface for the initial rules/law packs.
77a. Landed: add deterministic rules/law query-row JSON under
    [`../rules-as-code/generated/queries/`](../rules-as-code/generated/queries/),
    materializing 1,374 replayed coverage, monotonicity, version-delta,
    threshold, cap, and phase-out rows from the first three rule packs.
77b. Landed: add
    [`procurement-scoring-v0`](../rules-as-code/examples/procurement-scoring-v0/)
    as a rules/law pack that reuses finite predicate exclusions, bid caps,
    encoded deadlines, small-business bonus thresholds, score monotonicity, and
    Bool/QF_LIA checked fixtures. The generated rules query surface now reports
    882 bounded sample rows and 1,626 generated query rows across four packs
    for that increment.
77c. Landed: add
    [`grant-allocation-v0`](../rules-as-code/examples/grant-allocation-v0/)
    as a rational-allocation rules/law pack that reuses exact shares, budget
    balance, minimum-share floors, administrative caps, finite replay, and
    QF_LRA/Farkas checked fixtures. The generated rules query surface now
    reports 1,007 bounded sample rows and 1,766 generated query rows across
    five packs.
77d. Landed: add
    [`category-equivalence-v0`](../rules-as-code/examples/category-equivalence-v0/)
    as a category-normalization rules/law pack that reuses finite equivalence
    classes, generated equivalence-pair rows, and source-linked QF_UF/Alethe
    checked artifacts. The generated rules query surface now reports 1,013
    bounded sample rows, 1,774 generated query rows, and 24 checked obligations
    across six packs.
77e. Landed: add
    [`workflow-reachability-v0`](../rules-as-code/examples/workflow-reachability-v0/)
    as a bounded state-machine rules/law pack that reuses finite graph
    reachability, terminal-state guards, generated two-step path rows, and
    source-linked Bool/QF_LIA checked artifacts. The generated rules query
    surface now reports 1,037 bounded sample rows, 1,942 generated query rows,
    and 27 checked obligations across seven packs.
77f. Landed: add
    [`RULES-LAW-QUERIES.md`](RULES-LAW-QUERIES.md) plus
    `scripts/query-rules-as-code.py` as the rules/law consumer query surface,
    with `just rules-as-code` smoke-checking summary counts, procurement pack
    lookup, checked obligations, generated quality-score families, and late
    generated rows.
77g. Landed: add
    [`RULES-LAW-PATTERN-MATRIX.md`](RULES-LAW-PATTERN-MATRIX.md) as the
    rules/law pattern matrix, mapping the current predicate, relation,
    threshold, monotonicity, version, precedence, workflow, and
    implementation-equivalence patterns back to math concepts, proof routes,
    and smoke-checked queries.
77h. Landed: add
    [`rules-law-trust-boundary.md`](../learn/rules-law-trust-boundary.md) as
    the learner-facing trust-boundary page for reading current rules/law packs
    without treating them as legal advice or solver benchmarks.
78. Landed: add functional-analysis/operator field-readiness consumer queries
    through [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md) and the foundational
    smoke check, covering Farkas field readiness, the operator bridge lookup,
    split finite-operator replay plus checked `qf-lra-*` norm/bound/Chebyshev
    rows, and checked inner-product, Chebyshev, and spectral rows.
79. Landed: add topology field-readiness consumer queries through
    [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md) and the foundational smoke
    check, covering Boolean field readiness, compactness/preimage bridge
    lookups, and checked Boolean/Alethe topology rows.
80. Landed: add statistics field-readiness consumer queries through
    [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md) and the foundational smoke
    check, covering Farkas field readiness, finite-table/tail-count bridge
    lookups, checked exact-rational statistics rows including the bad
    variance Farkas row, and checked Diophantine
    count rows.
81. Landed: add linear-algebra field-readiness consumer queries through
    [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md) and the foundational smoke
    check, covering Farkas/Alethe field readiness, rank/projection bridge
    lookups, checked exact-rational matrix rows, and checked finite
    vector/dual/module/tensor equality rows.
82. Landed: add core algebra/number/graph field-readiness consumer queries
    through [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md) and the foundational
    smoke check, covering abstract-algebra Alethe readiness,
    homomorphism/ideal bridge lookups, checked Alethe and fixed-width QF_BV
    finite-algebra rows, number-theory Diophantine readiness, finite-family
    lookup, checked integer-arithmetic rows, graph-theory Boolean readiness,
    graph-family lookup, and checked finite graph rows.
83. Landed: add `bridge_finite_graph_replay_obstruction` plus graph
    reachability and concept-scoped Boolean route smoke queries, making finite
    coloring, traversal, matching, cut, and d-separation resources discoverable
    without promoting graph theorem, causal, or asymptotic-runtime claims.
84. Landed: add `bridge_finite_dynamics_euler_replay` plus Euler lookup and
    concept-scoped Farkas route smoke queries, making finite recurrence-prefix,
    bounded-dynamics, explicit-Euler, invariant, threshold, and finite-error
    rows discoverable without promoting ODE, stability, convergence-rate,
    stiffness, chaos, or PDE claims.
85. Landed: add `bridge_finite_circle_inversion_cyclic_replay` plus circle
    lookup and concept-scoped Farkas route smoke queries, making finite circle,
    inversion, and cyclic-configuration resources discoverable without
    promoting general circle, inversion, cyclic-quadrilateral, angle, Ptolemy,
    or synthetic geometry theorem claims.
86. Landed: add analysis/numerical/complex field-readiness consumer queries
    through [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md) and the foundational
    smoke check, covering real-analysis Farkas readiness, epsilon/gradient
    bridge lookups, checked bounded-analysis rows, numerical-analysis Farkas
    readiness, residual/operator bridge lookups, checked exact numerical rows,
    complex-analysis Farkas readiness, real-pair bridge lookup, and checked
    algebraic complex rows.
87. Landed: add foundations/discrete/probability field-readiness consumer
    queries through [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md) and the
    foundational smoke check, covering logic/proof Boolean readiness,
    proof-vocabulary lookups, checked proof-pattern/CNF rows,
    set-theory/foundations Alethe readiness, partition bridge lookups, checked
    finite relation/function/quotient rows, discrete-math Diophantine
    readiness, finite-family lookups, checked counting/coefficient/tail-count
    rows, probability-theory Farkas readiness, probability-table lookups, and
    checked finite probability/process rows.
88. Landed: add
    [FIELD-READINESS-QUERY-MATRIX.md](FIELD-READINESS-QUERY-MATRIX.md) as the
    compact all-field R6 consumer matrix, summarizing pack/check counts,
    smoke-checked route, bridge lookup, checked-row drilldown, and
    theorem-horizon boundary for all 18 math fields.
89. Landed: add
    [MATRIX-COMPUTATION-QUERIES.md](MATRIX-COMPUTATION-QUERIES.md) and exact
    `--concept` filters for `query-foundational-resources.py packs/checks`,
    making matrix resources queryable by bridge concept plus proof route.
90. Landed: add
    [PROOF-ROUTE-QUERY-MATRIX.md](PROOF-ROUTE-QUERY-MATRIX.md) and
    `query-foundational-resources.py routes`, making proof/evidence route
    coverage queryable by normalized route alias and optional field scope.
91. Landed: add number-system semantic-boundary bridge rows for
    exact-vs-floating arithmetic and totality conventions. The rows attach to
    exact rational, numerical, finite arithmetic, fixed-width BV, and finite
    function-table packs; `CONSUMER-QUERIES.md` and the foundational smoke
    check now exercise `number_theory` totality lookup and
    `numerical_analysis` floating-boundary lookup.
92. Landed: add the gcd/divisibility witness bridge row, tying
    `gcd-bezout-v0`, `integer-lia-v0`, `modular-arithmetic-v0`, and
    `number-theory-v0` to shared gcd/common-divisor replay, Bezout replay,
    quotient replay, and checked gcd non-divisibility evidence. The
    foundational smoke check now exercises number-theory gcd concept lookup.
93. Landed: add the modular CRT/inverse witness bridge row, tying
    `modular-arithmetic-v0`, `number-theory-v0`, `finite-fields-v0`, and
    `finite-ideals-v0` to concrete CRT congruence replay, modular inverse
    replay, fixed residue searches, finite-field unit/nonunit contrasts,
    checked nonunit/CRT Diophantine evidence, and checked fixed-width
    nonunit-inverse plus Fermat-unit QF_BV evidence. The foundational smoke check now exercises
    number-theory CRT concept lookup.
94. Landed: add the finite-counting replay bridge row, tying `counting-v0`,
    `proof-methods-refutation-v0`, `cardinality-principles-v0`,
    `generating-functions-v0`, `finite-group-actions-v0`, and
    `exact-statistical-tests-v0` to finite enumeration, pigeonhole proofs,
    double-counting tables, coefficient extraction, finite orbit counts, and
    exact finite tail counts. The foundational smoke check now exercises
    discrete-math counting lookup plus concept-scoped Boolean and Diophantine
    route queries.
95. Continue proof-route promotions or consumer-query examples; revisit the
    boundary again only when a non-repo consumer, three duplicated typed access
    call sites, or repeated reusable encoders exist.
96. Landed: add `bridge_finite_chain_homology_replay` plus topology homology
    lookup and concept-scoped Diophantine route smoke queries, making finite
    simplicial-complex closure, oriented boundaries, boundary-squared-zero,
    Betti-rank replay, the checked bad-boundary coefficient row, and the checked
    boundary-square cancellation row
    discoverable without promoting homology invariance, exact sequences,
    homotopy equivalence, cohomology-operation laws, or general algebraic
    topology.
97. Landed: add `bridge_finite_topology_operator_homeomorphism` plus topology
    closure/homeomorphism lookup and concept-scoped Alethe route smoke queries,
    making finite topology axioms, closure/interior replay, finite continuity
    by preimage, homeomorphism replay, checked malformed-topology Bool/CNF
    rows, and checked malformed-preimage QF_UF/Alethe rows discoverable
    without promoting arbitrary closure-operator, homeomorphism-invariance,
    compactness-preservation, connectedness-preservation, homology-invariance,
    or general topology theorems.
98. Landed: add `bridge_finite_boundary_operator_replay` plus topology
    boundary lookup and concept-scoped Diophantine route smoke queries, making
    oriented boundary coefficients, boundary-of-boundary cancellation,
    boundary-matrix shape, and checked bad-boundary coefficient plus
    boundary-square cancellation evidence discoverable without promoting
    functoriality, exactness, homology
    invariance, cohomology-operation laws, or general algebraic topology.
99. Landed: add `finite-specialization-order-v0` and
    `bridge_finite_specialization_order_replay` plus topology specialization
    lookup and concept-scoped Alethe route smoke queries, making finite
    topology-to-preorder replay, singleton-closure characterization, finite
    `T0` antisymmetry replay, and checked bad `T0` evidence discoverable
    without promoting T0 quotients, sobriety, Alexandroff-space/domain-theory
    results, or arbitrary-space specialization-order theorems.
100. Landed: add `finite-simplicial-cohomology-v0` and
     `bridge_finite_cohomology_replay` plus topology cohomology lookup and
     concept-scoped Alethe route smoke queries, making finite F2 coboundary
     replay, `delta^2 = 0`, cohomology-rank replay, non-coboundary cocycle
     checking, and checked bad coboundary-value evidence discoverable without
     promoting cohomology functoriality, cohomology-operation laws, universal
     coefficients, de Rham comparison, sheaf cohomology, duality, or invariance
     theorems.
101. Landed: add `finite-simplicial-cup-products-v0` and
     `bridge_finite_cup_product_replay` plus topology cup lookup and
     concept-scoped QF_BV route smoke queries, making ordered F2 cup-product
     replay, one finite coboundary-Leibniz row, and checked bad cup-product
     QF_BV/DRAT evidence discoverable without promoting associativity, graded
     commutativity, naturality, cohomology-ring quotienting, universal
     coefficients, or invariance theorems.
102. Landed: add `finite-universal-coefficient-shadow-v0` and
     `bridge_finite_universal_coefficient_shadow` plus topology universal
     lookup and concept-scoped Alethe route smoke queries, making one integer
     dual cochain complex, `H^1 = Z/2`, degree-one Hom/Ext bookkeeping, and
     checked bad `H^1 = 0` evidence discoverable without promoting the
     universal coefficient theorem, naturality, splitting choices, Ext/Tor
     laws, exact sequences, or invariance theorems.
103. Landed: add `finite-quotient-topology-v0` and
     `bridge_finite_quotient_topology_replay` plus topology quotient lookup
     and concept-scoped Alethe route smoke queries, making quotient-map
     fibers, same-fiber equivalence pairs, quotient topology by preimage-open
     replay, saturated-open image replay, and checked bad representative/open
     evidence discoverable without promoting quotient topology universal
     properties, quotient-map theorem schemas, or arbitrary preservation and
     invariance theorems.
104. Landed: add `metric-ball-epsilon-delta-index.md`, wiring bounded
     rational balls, finite metric continuity, sequence-tail shadows, finite
     compactness, finite connectedness, and open-preimage topology replay into
     one learner path. The atlas source refs and consumer smoke now expose
     metric-ball and bounded epsilon-delta bridge discovery without promoting
     quantified continuity, compactness, connectedness, or convergence
     theorems.
105. Landed: add `graph-traversal-runtime-index.md`, wiring finite
     reachability, BFS/DFS traversal traces, shortcut-tail cost counters, and
     checked QF_LIA bad-bound refutations into one graph learner path. The
     graph field readiness and smoke queries now expose the LIA runtime route
     while keeping asymptotic algorithm analysis and graph-family lower bounds
     in the theorem-horizon lane.
106. Landed: add `chebyshev-operator-index.md`, wiring finite-dimensional
     operator bounds, Chebyshev recurrence values, Vandermonde interpolation,
     alternating residuals, spectral rows, and characteristic-polynomial plus
     bad-trace arithmetic into one functional-analysis/operator learner path. The
     functional-analysis field readiness and smoke queries now expose
     concept-scoped `bridge_finite_operator_chebyshev` Farkas route lookups
     while keeping Banach/Hilbert-space, compact-operator, Haar-space,
     minimax, alternation-theorem, and infinite-dimensional approximation
     claims in the theorem-horizon lane.
107. Landed: add `random-matrix-moment-index.md`, wiring finite
     matrix-valued probability tables, exact trace/determinant moments,
     expected Gram matrices, rank-mixture probabilities, and checked
     QF_LRA/Farkas bad trace-square and expected-rank evidence into one
     probability/matrix learner path. The probability/statistics field readiness and smoke
     queries now expose concept-scoped `bridge_random_matrix_finite_moment`
     Farkas route lookups while keeping asymptotic spectra, universality,
     concentration theorems, simulation quality, and high-dimensional
     random-matrix claims in theorem/numerical-honesty lanes.
108. Landed: promote the concrete bad group-homomorphism row in
     `finite-algebra-homomorphisms-v0` through QF_UF/Alethe. The new
     `bad-group-homomorphism-alethe-conflict.smt2` artifact isolates the
     table-replayed mismatch `phi(1+1)=1` versus `phi(1)+phi(1)=0`, the solver
     regression checks the emitted Alethe proof object, and the consumer smoke
     now exercises `bridge_homomorphism_preservation` checked-row drilldowns
     without promoting general isomorphism or infinite algebra claims.
109. Landed: promote the false top-element set-family row in
     `finite-order-lattices-v0` through Bool/CNF DRAT/LRAT. The new
     `bad-top-element-rejected.cnf` artifact isolates `B !<= A` versus the bad
     claim that `A` is top and therefore requires `B <= A`; the CNF regression
     emits and checks DRAT/LRAT evidence, and the consumer smoke now exercises
     `bridge_finite_boolean_algebra` checked-row drilldowns without promoting
     complete-lattice or infinite order-theory claims.
110. Landed: extend the fixed-width finite-ring QF_BV/DRAT lane with the
     `bad-multiplicative-identity-qf-bv-drat` row in `finite-rings-v0`.
     Finite table replay isolates `1*1=0` under zero multiplication while the
     claimed identity law requires `1`; the new SMT-LIB artifact is checked by
     `math_resource_bv_routes`, and the learner page now distinguishes the
     distributivity and identity failures without promoting general ring
     theory.
111. Landed: extend the fixed-width finite-field QF_BV/DRAT lane with the
     `bad-prime-field-inverse-candidate-qf-bv-drat` row in
     `finite-fields-v0`. Finite replay isolates `3*4 mod 7 = 5` while the bad
     inverse claim requires `1`; the new SMT-LIB artifact is checked by
     `math_resource_bv_routes`, and the learner page keeps the prime-field bad
     candidate distinct from the composite-modulus no-inverse row.
112. Landed: extend the fixed-width modular-arithmetic QF_BV/DRAT lane with
     the `fermat-units-mod-prime-qf-bv-drat` row in `modular-arithmetic-v0`.
     Finite replay enumerates the units modulo `5`; the new SMT-LIB artifact
     asks for a 3-bit residue `0 < a < 5` with `a^4 mod 5 != 1`, checks the
     bit-blasted DRAT refutation through `math_resource_bv_routes`, and keeps
     Fermat's little theorem itself in the theorem-horizon lane.
113. Landed: extend `finite-operator-v0` with a checked bad `l1` sum-norm
     row. Finite replay computes `u+v=(4,1)` and `||u+v||_1 = 5` from the
     existing triangle witness while the malformed source SMT-LIB artifact
     claims the sum norm is at most `4`; the shared QF_LRA/Farkas route now
     checks both the finite norm conflict and the existing operator-bound
     conflict without promoting Banach/Hilbert-space norm theorems.
114. Landed: extend `inner-product-spaces-rational-v0` with a checked bad
     projection-orthogonality row. Finite replay computes the residual
     `[-1/2,1/2]` for projecting `[2,3]` onto `span([1,1])` and verifies
     `<residual,[1,1]> = 0`, while the malformed source SMT-LIB artifact claims
     the residual inner product is `1`; the shared QF_LRA/Farkas route now
     checks both inner-product positivity and projection-orthogonality
     conflicts without promoting infinite-dimensional projection theorems.
115. Landed: extend `spectral-linear-algebra-v0` with a checked bad
     Rayleigh-quotient row. Finite replay computes numerator `6`, denominator
     `2`, and quotient `3` for `[1,1]` under `[[2,1],[1,2]]`, while the
     malformed source SMT-LIB artifact claims quotient `4`; the shared
     QF_LRA/Farkas route now checks both Rayleigh-quotient and eigenpair
     spectral conflicts without promoting spectral theorem or eigenvalue
     algorithm claims.
116. Landed: extend `finite-inversion-geometry-v0` with a checked bad
     inverse-distance-product row. Exact unit-circle inversion replay computes
     the squared-radius product as `1`, while the malformed source SMT-LIB
     artifact claims `2`; the shared QF_LRA/Farkas route now checks both
     inverse-coordinate and inverse-distance-product conflicts without
     promoting general inversion theorems.
117. Landed: extend `finite-product-measure-v0` with a checked bad marginal
     row. Exact finite product-table replay recomputes the `heads` marginal as
     `1/2`, while the malformed source SMT-LIB artifact claims `2/3`; the
     shared QF_LRA/Farkas route now checks both product atom and marginal
     conflicts without promoting general product-measure or Fubini/Tonelli
     theorems.
118. Landed: extend `random-matrix-finite-v0` with a checked bad
     expected-rank row. Exact rational row-reduction replay computes the
     rank-mixture distribution and `E[rank]=1`, while the malformed source
     SMT-LIB artifact claims `2`; the shared QF_LRA/Farkas route now checks
     both trace-square moment and expected-rank conflicts without promoting
     asymptotic spectral laws, concentration, universality, simulation
     quality, or numerical eigensolver behavior.
119. Landed: extend `finite-operator-v0` with a checked `qf-lra-*` bad
     Chebyshev-prefix row. Exact recurrence replay at `x=1/2` computes `T3=-1`, while the
     malformed source SMT-LIB artifact claims the shifted value
     `T3+1=1/2`; the shared QF_LRA/Farkas route now checks the recurrence
     value conflict without promoting Haar-space, minimax, Banach/Hilbert, or
     infinite-dimensional approximation theorems.
120. Landed: extend `least-squares-regression-v0` with a checked bad
     RSS-improvement row. Exact mean-baseline replay computes baseline RSS
     `14/3`, model RSS `1/6`, and improvement `9/2`, while the malformed
     source SMT-LIB artifact claims improvement `4`; the shared QF_LRA/Farkas
     route now checks both bad coefficient and bad RSS-improvement rows without
     promoting statistical inference, asymptotics, model-selection guarantees,
     or floating-point regression behavior.
121. Landed: add
     [GEOMETRY-RESOURCE-QUERIES.md](GEOMETRY-RESOURCE-QUERIES.md), making the
     geometry lane queryable by bridge concept plus proof route. The guide and
     foundational smoke cover concept-scoped Farkas pack/check queries for
     `bridge_coordinate_orientation_geometry` and
     `bridge_finite_circle_inversion_cyclic_replay`, keeping finite
     coordinate/incidence/rigid/affine/orientation rows and
     circle/inversion/cyclic rows discoverable without promoting broad geometry
     theorem claims.
122. Landed: add
     [ALGEBRA-STRUCTURE-QUERIES.md](ALGEBRA-STRUCTURE-QUERIES.md), making the
     finite algebra lane queryable by bridge concept plus proof route. The
     guide and foundational smoke cover concept-scoped Alethe/QF_BV pack/check
     queries for homomorphism, group-action, module-action, ideal, and modular
     residue bridge concepts while keeping arbitrary algebraic structure
     theorems in the horizon lane.
123. Landed: add
     [GRAPH-DISCRETE-QUERIES.md](GRAPH-DISCRETE-QUERIES.md), making the
     graph/discrete lane queryable by bridge concept plus proof route. The
     guide and foundational smoke cover concept-scoped Boolean, QF_BV, and LIA
     pack/check queries for finite coloring, reachability, matching, cut,
     d-separation, fixed-width coloring, and BFS/DFS runtime rows while
     keeping general graph theorems and asymptotic algorithm claims in the
     horizon lane.
124. Landed: add
     [NUMBER-ARITHMETIC-QUERIES.md](NUMBER-ARITHMETIC-QUERIES.md), making the
     number/arithmetic lane queryable by bridge concept plus proof route. The
     guide and foundational smoke cover concept-scoped Diophantine, QF_BV,
     totality, ideal/quotient, and exact-vs-floating queries for finite
     arithmetic rows while keeping analytic number theory, algebraic number
     theory, unbounded induction, and floating-point guarantees in the horizon
     or numerical-honesty lanes.
125. Landed: add
     [PROBABILITY-STATISTICS-QUERIES.md](PROBABILITY-STATISTICS-QUERIES.md),
     making the probability/statistics lane queryable by bridge concept plus
     proof route. The guide and foundational smoke cover concept-scoped Farkas
     queries for finite probability tables, measure additivity,
     product/integration, pushforwards, conditional expectation, stochastic
     kernels, tail counts, and random-matrix moments while keeping continuous
     probability, asymptotic statistics, stochastic-process limits, simulation
     quality, and floating-point inference claims in horizon lanes.
126. Landed: add
     [TOPOLOGY-HOMOLOGY-QUERIES.md](TOPOLOGY-HOMOLOGY-QUERIES.md), making the
     topology/homology lane queryable by bridge concept plus proof route. The
     guide and foundational smoke cover concept-scoped Boolean, Farkas,
     Alethe, Diophantine, and QF_BV queries for metric shadows, compactness,
     connectedness, quotient topology, specialization order, finite homology,
     torsion, cohomology, UCT shadows, and cup products while keeping general
     topology and algebraic-topology theorem claims in the horizon lane.
127. Landed: extend `finite-kkt-v0` with a source-linked checked
     complementary-slackness refutation. Exact replay computes
     `lambda * (x - bound) = 0` for the boundary quadratic witness while the
     malformed row claims product `1`; the new source SMT-LIB artifact reaches
     independently checked QF_LRA/Farkas evidence through
     `finite_kkt_bad_complementarity_artifact_emits_checked_farkas`.
128. Landed: extend `finite-projected-gradient-v0` with a source-linked checked
     projected-decrease refutation. Exact objective replay computes projected
     decrease `3`, while the malformed row claims `4`; the new source SMT-LIB
     artifact reaches independently checked QF_LRA/Farkas evidence through
     `finite_projected_gradient_bad_decrease_artifact_emits_checked_farkas`.
129. Landed: extend `finite-euler-method-v0` with a source-linked checked
     terminal-error refutation. Exact finite error-table replay computes
     terminal error `3/4`, while the malformed row claims `1/2`; the new source
     SMT-LIB artifact reaches independently checked QF_LRA/Farkas evidence
     through `finite_euler_bad_terminal_error_artifact_emits_checked_farkas`.
130. Landed: extend `finite-sdp-v0` with a source-linked checked slack-entry
     refutation. Exact primal/dual replay computes bottom-right slack entry
     `1`, while the malformed row claims `1/2`; the new source SMT-LIB artifact
     reaches independently checked QF_LRA/Farkas evidence through
     `finite_sdp_bad_slack_entry_artifact_emits_checked_farkas`.
131. Landed: extend `finite-wolfe-line-search-v0` with a source-linked checked
     sufficient-decrease refutation. Exact Wolfe replay computes Armijo RHS
     `1/2`, accepted value `0`, and sufficient-decrease slack `1/2`, while the
     malformed row claims the same slack is nonpositive; the new source
     SMT-LIB artifact reaches independently checked QF_LRA/Farkas evidence
     through
     `finite_wolfe_line_search_bad_sufficient_decrease_artifact_emits_checked_farkas`.
132. Landed: extend `finite-active-set-qp-v0` with a source-linked checked
     inactive-slack refutation. Exact active-face replay computes inactive
     lower-bound slack `0 - (-1) = 1` at `(1,1)`, while the malformed row claims
     the same slack is nonpositive; the new source SMT-LIB artifact reaches
     independently checked QF_LRA/Farkas evidence through
     `finite_active_set_qp_bad_inactive_slack_artifact_emits_checked_farkas`.
133. Landed: extend `finite-gradient-descent-v0` with a source-linked checked
     descent-bound refutation. Exact replay computes descent slack `1/4` from
     decrease `11/4` and descent bound `5/2`, while the malformed row claims
     the same slack is nonpositive; the new source SMT-LIB artifact reaches
     independently checked QF_LRA/Farkas evidence through
     `finite_gradient_descent_bad_descent_bound_artifact_emits_checked_farkas`.
134. Landed: extend `finite-line-search-v0` with a source-linked checked
     descent-direction refutation. Exact derivative replay computes
     directional derivative `-4` from gradient `2` and direction `-2`, while
     the malformed row claims the derivative is nonnegative; the new source
     SMT-LIB artifact reaches independently checked QF_LRA/Farkas evidence
     through
     `finite_line_search_bad_descent_direction_artifact_emits_checked_farkas`.
135. Landed: extend `finite-proximal-gradient-v0` with a source-linked checked
     composite-decrease refutation. Exact replay computes composite values
     `9/2` and `3`, hence decrease `3/2`, while the malformed row claims `2`;
     the new source SMT-LIB artifact reaches independently checked
     QF_LRA/Farkas evidence through
     `finite_proximal_gradient_bad_composite_decrease_artifact_emits_checked_farkas`.
136. Landed: extend `bounded-dynamics-v0` with a source-linked threshold-step
     refutation route. Exact replay computes state `6` at claimed step `2`,
     below threshold `7`, while the malformed row claims the threshold is
     already reached; the source SMT-LIB artifact reaches independently
     checked QF_LRA/Farkas evidence through
     `bounded_dynamics_bad_threshold_step_artifact_emits_checked_farkas`.
137. Landed: extend `complex-plane-transforms-v0` with a source-linked checked
     conjugation-product imaginary-part refutation. Exact real-pair replay
     computes both `conjugate(z*w)` and `conjugate(z)*conjugate(w)` as
     `5 - 5i`, while the malformed row claims imaginary part `5`; the new
     shifted source SMT-LIB artifact reaches independently checked
     QF_LRA/Farkas evidence through
     `complex_plane_bad_conjugation_product_imaginary_artifact_emits_checked_farkas`.
138. Landed: extend `numerical-linear-algebra-v0` with a source-linked checked
     solution-box upper-bound refutation. Exact rational replay computes
     solution first component `6/5`, while the malformed row claims `x0 <= 1`;
     the new source SMT-LIB artifact reaches independently checked
     QF_LRA/Farkas evidence through
     `numerical_linear_algebra_bad_solution_box_upper_bound_artifact_emits_checked_farkas`.
139. Landed: add the generated bounded-family/asymptotic boundary bridge row.
     `bridge_bounded_family_asymptotic_boundary` makes finite BFS/DFS runtime
     counters, recurrence prefixes, fixed coefficient windows, bounded
     dynamics traces, and finite Euler error rows discoverable by one concept.
     Concept-scoped LIA and Farkas queries now return checked rows while
     asymptotic runtime, closed-form recurrence, convergence-rate, and
     limiting theorem claims remain proof-horizon work.
140. Landed: add the generated polynomial coefficient/factor replay bridge row.
     `bridge_polynomial_coefficient_factor_replay` makes fixed polynomial
     identities, factor/division witnesses, finite coefficient windows,
     root-finding steps, derivative shadows, and rational polynomial-geometry
     obligations discoverable by one concept. Concept-scoped Diophantine and
     Farkas queries now return checked rows while general factorization,
     algebraic closure, root distribution, and generating-function convergence
     remain proof-horizon work.
141. Landed: extend `graph-d-separation-v0` with a source-linked checked
     unconditioned-collider CNF row. The fixed DAG `a -> b <- c` with empty
     conditioning has one skeleton path whose middle node is a closed collider;
     the DIMACS artifact encodes that collider-specific blocking rule and the
     malformed active-path claim. The shared Boolean route now checks both the
     conditioned-chain and unconditioned-collider d-separation blockers through
     emitted DRAT, elaborated LRAT, and independent proof checks without
     promoting causal identification or probabilistic graphical-model
     semantics.
142. Landed: split the `finite-continuous-maps-v0` QF_UF/Alethe preimage
     artifact into the explicit `qf-uf-bad-preimage-membership` expected row.
     The finite continuity failure still replays the non-open preimage `{0}`;
     the source SMT-LIB artifact separately checks the malformed table that
     excludes `0` despite `f(0)=u` and `u in {u}`. This makes the topology
     preimage route directly queryable by pack, field, route, and proof status.
143. Landed: extend `finite-simplicial-homology-v0` with a checked
     boundary-square cancellation row. The pack now rejects the malformed claim
     that the coefficient of `[b]` in `boundary(boundary([a,b,c]))` is `1`,
     after exact replay computes the two edge contributions `-1` and `+1`;
     the linked QF_LIA/Diophantine regression checks the source SMT-LIB
     contradiction `coeff_b = 0` and `coeff_b = 1`.
144. Landed: split the `finite-modules-v0` scalar-closure proof-object check
     into an explicit QF_UF/Alethe row. The finite replay row still rejects
     `{0,1}` as a non-submodule by computing `2*1 = 2`; the new
     `qf-uf-bad-submodule-scalar-closure` row isolates the membership
     contradiction for checked Alethe evidence and gives consumers a direct
     pack/route/text query.
145. Landed: split the `finite-vector-spaces-v0` additive-closure proof-object
     check into an explicit QF_UF/Alethe row. The finite replay row still
     rejects `{00,10,01}` as a non-subspace by computing `10 + 01 = 11`; the
     new `qf-uf-bad-subspace-addition-closure` row isolates the membership
     contradiction for checked Alethe evidence and gives consumers a direct
     pack/route/text query.
146. Landed: split the `finite-dual-spaces-v0` covector-additivity proof-object
     check into an explicit QF_UF/Alethe row. The finite replay row still
     rejects the malformed functional by computing `10 + 01 = 11`, `f(11)=1`,
     and `f(10)+f(01)=0`; the new `qf-uf-bad-covector-additivity` row isolates
     the additivity equality contradiction for checked Alethe evidence and
     gives consumers a direct pack/route/text query.
147. Landed: split the `finite-tensor-products-v0` bad-bilinear proof-object
     check into an explicit QF_UF/Alethe row. The finite replay row still
     rejects the malformed table by computing `10 + 01 = 11`,
     `beta(11,1)=00`, and `beta(10,1)+beta(01,1)=11`; the new
     `qf-uf-bad-bilinear-left-additivity` row isolates the additivity equality
     contradiction for checked Alethe evidence and gives consumers a direct
     pack/route/text query.
148. Landed: split the `finite-order-lattices-v0` bad-partial-order
     proof-object check into an explicit QF_UF/Alethe row. The finite replay
     row still rejects the malformed relation by computing `x <= y`,
     `y <= x`, and `x != y`; the new
     `qf-uf-bad-partial-order-antisymmetry` row isolates the antisymmetry
     equality contradiction for checked Alethe evidence and gives consumers a
     direct pack/route/text query.
149. Landed: split the `finite-permutation-groups-v0` bad-nonbijection
     proof-object check into an explicit QF_UF/Alethe row. The finite replay
     row still rejects the malformed self-map by computing `bad(1)=1`,
     `bad(2)=1`, and the missing image `2`; the new
     `qf-uf-bad-nonbijection-injectivity` row isolates the duplicate-preimage
     injectivity contradiction for checked Alethe evidence and gives consumers
     a direct pack/route/text query.
150. Landed: split the `finite-monoids-v0` bad-nonassociative-table
     proof-object check into an explicit QF_UF/Alethe row. The finite replay
     row still rejects the malformed table by computing `(b*b)*b = a` and
     `b*(b*b) = b`; the new `qf-uf-bad-monoid-associativity` row isolates the
     associativity equality contradiction for checked Alethe evidence and
     gives consumers a direct pack/route/text query.
151. Landed: split `finite-group-actions-v0` malformed identity-action and
     action-compatibility rows into exact replay rows plus explicit
     QF_UF/Alethe proof rows. The checked rows are now
     `qf-uf-bad-identity-action` and `qf-uf-bad-action-compatibility`; the
     replay rows still own the finite table computations that expose the bad
     entries. This keeps solver-reuse evidence pointed at checked proof
     artifacts while preserving learner-visible replay.
152. Landed: split `finite-measure-v0` bad complement-measure checking into an
     exact replay row plus an explicit QF_LRA/Farkas proof row. The replay row
     still computes the finite measure-table values and exposes the malformed
     claimed complement measure; the new `qf-lra-bad-complement-measure` row
     owns the source SMT-LIB artifact and gives consumers a direct
     pack/route/text query for the checked complement-additivity conflict.
153. Landed: split `linear-algebra-rational-v0` malformed LU product-entry
     checking into an exact replay row plus an explicit QF_LRA/Farkas proof
     row. The replay row still recomputes the fixed `L*U` product and exposes
     the bad bottom-right entry claim; the new `qf-lra-bad-lu-product-entry`
     row owns the source SMT-LIB artifact and gives consumers a direct
     pack/route/text query for the checked product-entry conflict.
154. Landed: split `descriptive-statistics-v0` malformed variance checking
     into an exact finite-sample replay row plus an explicit QF_LRA/Farkas
     proof row. The replay row still recomputes the fixed sample mean, second
     moment, mean square, and population variance; the new
     `qf-lra-bad-variance` row owns the source SMT-LIB artifact and gives
     consumers a direct pack/route/text query for the checked variance
     equation conflict.
155. Landed: add `finite-flow-cut-v0` as a graph/optimization bridge pack.
     The pack replays one exact directed feasible flow, checks a saturated
     source-side cut certificate, rejects a malformed edge-capacity claim,
     rejects a claimed flow value above the finite cut capacity, and records
     the general max-flow/min-cut theorem as Lean-horizon work. It was
     introduced as `non-benchmark-horizon`; a later promotion adds the
     source-linked QF_LRA/Farkas cut-bound artifact.
156. Landed: promote `finite-flow-cut-v0` with
     `qf-lra-bad-flow-value-cut-bound` as the source-linked checked Farkas row
     for the finite cut upper-bound conflict. The committed SMT-LIB artifact
     isolates `cut_capacity = 3`, `claimed_flow_value = 4`, and
     `claimed_flow_value <= cut_capacity`, while the theorem boundary keeps
     arbitrary-network max-flow/min-cut and algorithm correctness in the
     Lean-horizon lane.
157. Landed: promote `finite-shortest-path-v0` with
     `qf-lra-bad-shorter-distance-potential-bound` as the source-linked
     checked Farkas row for the finite potential lower-bound conflict. The
     committed SMT-LIB artifact isolates `potential_lower_bound = 5`,
     `claimed_upper_bound = 4`, and
     `potential_lower_bound <= claimed_upper_bound`, while the theorem
     boundary keeps arbitrary shortest-path correctness, negative-cycle
     reasoning, all-pairs algorithms, and asymptotic runtime in the
     Lean-horizon lane.
158. Landed: promote `finite-dag-topological-order-v0` with
     `qf-lia-bad-topological-edge-order` as the source-linked checked QF_LIA
     row for the finite topological edge-order conflict. The committed SMT-LIB
     artifact isolates `algebra_position = 2`, `topology_position = 1`, and
     `algebra_position < topology_position`, while the theorem boundary keeps
     topological-sort algorithm correctness, finite linear-extension
     existence, and cycle-obstruction completeness in the Lean-horizon lane.
159. Landed: add `finite-walsh-hadamard-transform-v0` as an exact
     order-4 transform resource. The pack computes the Walsh-Hadamard
     transform, inverse reconstruction, and Parseval scaling, then promotes the
     malformed second coefficient claim through a source-linked QF_LRA/Farkas
     regression without claiming fast-transform, Fourier-analysis, or
     infinite-dimensional orthogonal-basis theorems.
160. Landed: add `finite-qr-decomposition-v0` as an exact rational QR
     factorization resource. The pack computes `Q^T Q`, upper-triangular
     shape, and `Q*R`, then promotes the malformed bottom-right product-entry
     claim through a source-linked QF_LRA/Farkas regression without claiming
     QR existence, Gram-Schmidt/Householder correctness, conditioning, or
     floating-point stability.
161. Landed: add `finite-cholesky-decomposition-v0` as an exact rational
     Cholesky factorization resource. The pack computes lower triangularity,
     positive diagonal entries, `L*L^T`, and leading principal minors, then
     promotes the malformed bottom-right product-entry claim through a
     source-linked QF_LRA/Farkas regression without claiming Cholesky
     existence, algorithm correctness, conditioning, or floating-point
     stability.
162. Landed: add `finite-covariance-matrix-v0` as an exact finite-sample
     covariance resource. The pack computes the sample mean, centered rows,
     centered Gram matrix, covariance matrix, and two-by-two
     positive-semidefinite shadow, then promotes the malformed off-diagonal
     covariance claim through a source-linked QF_LRA/Farkas regression without
     claiming covariance-estimator consistency, PCA, random-matrix asymptotics,
     or floating-point covariance algorithms.
163. Landed: add `finite-newton-step-v0` as an exact finite Newton-step
     resource. The pack computes one two-variable quadratic's gradient,
     Hessian, positive leading minors, Hessian inverse, Newton direction,
     stationary next point, and objective decrease, then promotes the
     malformed next-coordinate claim through a source-linked QF_LRA/Farkas
     regression without claiming Newton convergence, globalization,
     trust-region methods, conditioning, or floating-point Newton algorithms.
164. Landed: add `finite-condition-number-v0` as an exact finite
     condition-number resource. The pack computes one diagonal rational
     matrix inverse, infinity-norm condition number, perturbation-bound shadow,
     and replay-only bad condition-number bound, then promotes the malformed
     `kappa_infinity(A) <= 5` claim through a source-linked QF_LRA/Farkas
     regression without claiming algorithmic stability, singular-value
     theory, pseudospectra, or floating-point roundoff.
165. Landed: add `finite-singular-value-shadow-v0` as an exact finite
     singular-value/SVD-shadow resource. The pack computes `A^T A`, singular
     vectors, `U*Sigma*V^T`, spectral/Frobenius norms, and a two-norm
     condition number for one diagonal rational matrix, then promotes the
     malformed `sigma_max(A) <= 2` claim through a source-linked
     QF_LRA/Farkas regression without claiming the general SVD theorem,
     perturbation theory, pseudospectra, rank-revealing algorithms, or
     floating-point SVD stability.
166. Landed: add `finite-jordan-chain-v0` as an exact finite Jordan-chain
     resource. The pack computes one non-diagonal Jordan block, eigenvector,
     generalized eigenvector, nilpotent part, and similarity reconstruction,
     then promotes a malformed nilpotent-component claim through a
     source-linked QF_LRA/Farkas regression without claiming Jordan normal
     form, diagonalizability criteria, multiplicity theorems, or numerical
     eigensolver behavior.
167. Landed: add `finite-schur-complement-v0` as an exact finite
     block-matrix resource. The pack computes one one-by-one Schur complement,
     determinant factorization, two-sided inverse replay, positive-definite
     shadow, and conditional-variance shadow, then promotes the malformed
     scalar claim `S = 3/2` through a source-linked QF_LRA/Farkas regression
     without claiming general Schur-complement, block-inverse,
     Gaussian-elimination, pivoting, SDP, statistical-conditioning, or
     numerical-stability theorems.
168. Landed: add `finite-gaussian-elimination-v0` as an exact finite
     elimination-transcript resource. The pack computes one pivot multiplier,
     augmented row replacement, determinant pivot product, and
     back-substitution result, then promotes the malformed eliminated-RHS claim
     `8` versus exact `7` through a source-linked QF_LRA/Farkas regression
     without claiming general elimination correctness, pivoting,
     rank-revealing variants, sparse fill-in, conditioning, or floating-point
     stability.
169. Landed: add `finite-conjugate-gradient-v0` as an exact finite
     conjugate-gradient resource. The pack computes one SPD rational solve,
     two CG step sizes, residual orthogonality, A-conjugacy, and the exact
     solution, then promotes the malformed first-step-size claim `1/3` versus
     exact `1/4` through a source-linked QF_LRA/Farkas regression without
     claiming general CG convergence, Krylov minimization, preconditioners,
     roundoff, or floating-point stability.
170. Landed: add `finite-arnoldi-iteration-v0` as an exact finite
     Arnoldi/Krylov resource. The pack computes one rational Arnoldi
     transcript for `A = [[1,2],[3,4]]`, including `q1`, `q2`, projection
     coefficients `h11`, `h21`, `h12`, `h22`, orthonormality, and the exact
     Hessenberg relation `A*Q = Q*H`, then promotes the malformed
     subdiagonal coefficient claim `h21 = 2` versus exact `3` through a
     source-linked QF_LRA/Farkas regression without claiming general
     Arnoldi/GMRES convergence, Ritz-value theory, restart or
     reorthogonalization behavior, or floating-point stability.
171. Landed: add `finite-lanczos-iteration-v0` as an exact finite
     Lanczos/Krylov resource. The pack computes one rational symmetric-matrix
     transcript for `A = [[2,1],[1,2]]`, including `q1`, `q2`, coefficients
     `alpha1`, `beta1`, `alpha2`, exact termination residual, orthonormality,
     and the exact tridiagonal relation `A*Q = Q*T`, then promotes the
     malformed off-diagonal coefficient claim `beta1 = 2` versus exact `1`
     through a source-linked QF_LRA/Farkas regression without claiming general
     Lanczos convergence, Ritz-value theory, breakdown/restart behavior,
     finite-precision orthogonality, or floating-point stability.
172. Landed: add `finite-givens-rotation-v0` as an exact finite
     Givens-rotation resource. The pack computes one rational orthogonal
     transform with `c = 3/5`, `s = 4/5`, verifies `G^T*G = I`,
     `G*[3,4] = [5,0]`, inverse reconstruction, determinant `1`, and norm
     preservation, then promotes the malformed sine coefficient claim
     `s = 3/5` versus exact `4/5` through a source-linked QF_LRA/Farkas
     regression without claiming general QR algorithms, pivoting,
     conditioning, or floating-point stability.
173. Landed: add `finite-householder-reflection-v0` as an exact finite
     Householder-reflection resource. The pack computes one rational
     reflector `v = [2,1]`, denominator `v^T*v = 5`, reflection
     `H = [[-3/5,-4/5],[-4/5,3/5]]`, symmetry, orthogonality,
     `H*[3,4] = [-5,0]`, involution, determinant `-1`, and norm
     preservation, then promotes the malformed top-left entry claim
     `H[0,0] = -4/5` versus exact `-3/5` through a source-linked
     QF_LRA/Farkas regression without claiming general Householder/QR
     algorithms, pivoting, conditioning, or floating-point stability.
174. Landed: add `finite-gram-schmidt-v0` as an exact finite
     Gram-Schmidt resource. The pack computes one rational two-column
     orthogonalization transcript with `a1 = [3,4]`, `a2 = [1,0]`,
     `q1 = [3/5,4/5]`, projection coefficient `r12 = 3/5`, residual
     `[16/25,-12/25]`, `q2 = [4/5,-3/5]`, an upper-triangular `R`,
     orthonormality, and `Q*R = A`, then promotes the malformed
     projection-coefficient claim `r12 = 4/5` versus exact `3/5` through a
     source-linked QF_LRA/Farkas regression without claiming general
     Gram-Schmidt/QR correctness, rank-deficient variants, conditioning, or
     floating-point stability.
175. Landed: add `finite-lu-decomposition-v0` as an exact finite
     LU-decomposition resource. The pack computes one rational two-by-two
     factorization `A = [[2,1],[4,5]] = L*U` with
     `L = [[1,0],[2,1]]`, `U = [[2,1],[0,3]]`, determinant pivot product
     `6`, forward/back substitution for `b = [5,17]`, and the exact solution
     `[4/3,7/3]`, then promotes the malformed multiplier claim `l21 = 3`
     versus exact `2` through a source-linked QF_LRA/Farkas regression without
     claiming general LU existence, pivoting correctness, rank-deficient
     behavior, sparse algorithms, conditioning, or floating-point stability.
176. Landed: add `finite-pivoted-lu-decomposition-v0` as an exact finite
     pivoted-LU resource. The pack computes one rational row-swapped
     factorization with `A = [[1,2],[3,4]]`,
     `P = [[0,1],[1,0]]`, `P*A = [[3,4],[1,2]]`,
     `L = [[1,0],[1/3,1]]`, `U = [[3,4],[0,2/3]]`,
     determinant-sign accounting `det(P) * det(A) = product(pivots) = 2`,
     triangular solve replay for `b = [3,7]`, and the exact solution
     `[1,1]`, then promotes the malformed row-swap determinant claim
     `det(P) = +1` versus exact `-1` through a source-linked QF_LRA/Farkas
     regression without claiming pivot-selection correctness, rank-deficient
     behavior, sparse pivot policies, growth-factor bounds, conditioning, or
     floating-point stability.
177. Landed: add `finite-ldlt-decomposition-v0` as an exact finite LDLT
     resource. The pack computes one rational positive-definite factorization
     with `A = [[4,2],[2,3]]`, `L = [[1,0],[1/2,1]]`,
     `D = [[4,0],[0,2]]`, `L*D*L^T = A`, determinant/product replay
     `det(A) = product(diag(D)) = 8`, positive leading minors `[4,8]`,
     triangular solve replay for `b = [6,5]`, and the exact solution
     `[1,1]`, then promotes the malformed diagonal-entry claim
     `D[1,1] = 3` versus exact `2` through a source-linked QF_LRA/Farkas
     regression without claiming LDLT existence, pivoting strategy
     correctness, indefinite variants, sparse algorithms, conditioning, or
     floating-point stability.
178. Landed: add `finite-orthogonal-diagonalization-v0` as an exact finite
     orthogonal-diagonalization resource. The pack computes one rational
     symmetric spectral shadow with
     `Q = [[3/5,4/5],[-4/5,3/5]]`, `D = diag(1,4)`,
     `A = Q*D*Q^T`, orthogonality, column eigenpairs, trace/eigenvalue-sum
     replay, and determinant/eigenvalue-product replay, then promotes the
     malformed eigenvalue claim `lambda_1 = 5` versus exact `4` through a
     source-linked QF_LRA/Farkas regression without claiming spectral theorem,
     diagonalization criteria, multiplicity theory, perturbation bounds,
     eigensolver convergence, or floating-point stability.
179. Landed: add `finite-real-schur-decomposition-v0` as an exact finite
     real-Schur resource. The pack computes one rational non-symmetric
     spectral shadow with
     `Q = [[3/5,4/5],[-4/5,3/5]]`, `T = [[1,2],[0,4]]`,
     `A = Q*T*Q^T`, orthogonality, upper-triangular shape, triangular coupling
     `A*Q = Q*T`, trace/diagonal-sum replay, and determinant/diagonal-product
     replay, then promotes the malformed superdiagonal claim `T[0,1] = 3`
     versus exact `2` through a source-linked QF_LRA/Farkas regression without
     claiming general Schur theorem, eigenvalue ordering, QR-iteration
     convergence, perturbation bounds, or floating-point stability.
180. Landed: add `finite-polar-decomposition-v0` as an exact finite
     polar-decomposition resource. The pack computes one rational orthogonal
     factor and positive factor with
     `U = [[3/5,4/5],[-4/5,3/5]]`, `P = [[2,0],[0,5]]`,
     `A = U*P`, orthogonality, positive diagonal shape, `A^T*A = P^2`,
     trace/diagonal-sum replay, and determinant/product replay, then promotes
     the malformed diagonal claim `P[1,1] = 4` versus exact `5` through a
     source-linked QF_LRA/Farkas regression without claiming polar theorem,
     partial-isometry variants, square-root functional calculus, iterative
     algorithms, perturbation bounds, or floating-point stability.
181. Landed: add `finite-qr-iteration-step-v0` as an exact finite QR-step
     resource. The pack computes one rational unshifted step
     `Q*R = A0`, `R*Q = A1`, and `Q^T*A0*Q = A1`, replays
     trace/determinant invariants, then promotes the malformed next-step entry
     claim `A1[0,0] = 2` versus exact `7/5` through a source-linked
     QF_LRA/Farkas regression without claiming QR-iteration convergence,
     shifted/deflated variants, Schur theorem reconstruction,
     loss-of-orthogonality analysis, or floating-point eigensolver stability.
182. Landed: add `finite-shifted-qr-step-v0` as an exact finite shifted-QR
     resource. The pack computes one rational shifted step with `mu = 1`,
     `A0 - mu*I = Q*R`, `A1 = R*Q + mu*I`, and
     `A1 = Q^T*A0*Q`, replays trace/determinant invariants, then promotes the
     malformed shifted next-step entry claim `A1[1,1] = 2` versus exact `8/5`
     through a source-linked QF_LRA/Farkas regression without claiming
     shift-selection theory, deflation, QR convergence, Schur theorem
     reconstruction, loss-of-orthogonality analysis, or floating-point
     eigensolver stability.
183. Landed: add `finite-rounding-shadow-v0` as an exact finite
     exact-vs-rounded arithmetic resource. The pack computes one rational
     increment `1/10000`, replays a fixed three-decimal rounding grid where
     the increment is rounded away after summing, then promotes the malformed
     equality claim `exact_delta = rounded_delta` through a source-linked
     QF_LRA/Farkas regression without claiming IEEE floating-point semantics,
     rounding-mode theory, accumulation-error bounds, or numerical-stability
     theorems.
184. Landed: add `finite-interval-arithmetic-shadow-v0` as an exact finite
     rational interval-arithmetic resource. The pack computes one closed
     positive interval product around one, replays endpoint-wise sum/product
     intervals and the second-order product-width term, then promotes the
     malformed shortcut claim `product_upper <= 5001/5000` through a
     source-linked QF_LRA/Farkas regression without claiming general interval
     analysis, dependency management, floating-point outward rounding, QF_FP
     semantics, or numerical-stability theorems.
185. Landed: add `finite-cauchy-riemann-shadow-v0` as an exact finite
     Cauchy-Riemann derivative-shadow resource. The pack computes one
     `f(z)=z^2` real-pair value, bivariate component partials, fixed
     Cauchy-Riemann equalities, and `f'(1+2i)=2+4i`, then promotes the
     malformed derivative real-part claim through a source-linked
     QF_LRA/Farkas regression without claiming holomorphicity, the general
     Cauchy-Riemann theorem, contour integration, residues, or analytic
     continuation.

## Validation Checklist

For plan-only documentation:

```sh
git diff --check
./scripts/check-links.sh
```

For ontology, pack, or dashboard changes:

```sh
./scripts/check-foundational-resources.sh
python3 scripts/consume-foundational-resources.py
python3 scripts/query-foundational-resources.py summary
```

For proof-route promotions, add the focused route-specific cargo regression
before updating metadata or status.

## What Not To Do

- Do not add broad textbook prose without a checkable pack or horizon row.
- Do not call a bounded example a general theorem.
- Do not promote solver reuse without a regression, fuzz seed, benchmark slice,
  or explicit non-benchmark-horizon back-link.
- Do not split a new crate or repository before repeated consumers exist.
- Do not let law/policy/rules examples become legal advice or unsupported
  natural-language parsing claims.
