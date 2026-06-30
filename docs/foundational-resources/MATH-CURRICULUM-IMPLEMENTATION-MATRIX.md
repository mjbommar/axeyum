# Math Curriculum Resource Implementation Matrix

## Purpose

This is the build matrix for turning the formal math curriculum into a durable
resource system. It complements the phase/history plan in
[MATH-CURRICULUM-BUILDOUT.md](MATH-CURRICULUM-BUILDOUT.md) and the forward
execution plan in
[CURRICULUM-RESOURCE-EXECUTION-PLAN.md](CURRICULUM-RESOURCE-EXECUTION-PLAN.md).

The invariant is:

```text
curriculum node -> concept row -> example pack -> learner page -> proof route -> solver feedback -> consumer boundary
```

The build order should stay top-down, but each commit should be narrow: one
concept row group, one example pack, one proof upgrade, one learner lesson, or
one generated dashboard change.

## Resource Acceptance Gates

| Gate | What Exists | Required Check |
|---|---|---|
| R0 source anchor | curriculum node or field row | appears in `curriculum.toml` or `MATH-FIELDS.md` |
| R1 concept row | atlas row with fields, prerequisites, fragments, gaps | `python3 scripts/validate-foundational-concepts.py` |
| R2 example pack | `README.md`, `metadata.json`, `model.md`, `checks.md`, `expected.json` | `python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/<pack>` |
| R3 learner path | focused lesson or named cluster page | `./scripts/check-links.sh` plus generated learner dashboard |
| R4 checked evidence | replay, DRAT/LRAT, Farkas, Alethe, QF_BV DRAT, or Lean horizon | route-specific cargo test plus pack validator |
| R5 solver reuse | regression, fuzz seed, benchmark slice, or explicit non-benchmark horizon | back-link from test/corpus metadata to resource pack |
| R6 consumer boundary | schema/API/data consumer | `python3 scripts/consume-foundational-resources.py` |

Do not promote a row past the gate it actually satisfies. A finite checked
example is useful at R2/R3; it is not a general theorem until an R4 proof route
or Lean reconstruction supports that scope.

## Build Units

Every new or upgraded resource should answer these questions before it lands:

- Audience: learner, solver contributor, proof contributor, educator, consumer,
  or several of these.
- Mathematical claim: exact finite claim, bounded shadow, computable witness, or
  proof-horizon theorem.
- Encoding: Bool/CNF, QF_BV, QF_LIA, QF_LRA, QF_UF, arrays, finite replay, or
  Lean horizon.
- Evidence: SAT witness replay, UNSAT certificate, checked algebraic
  computation, explicit gap, or `unknown` with reason.
- Trust boundary: what is untrusted search/encoding and what is independently
  checked.
- Graduation: concrete command or proof-route target that moves the resource to
  the next gate.

## Curriculum Node Matrix

| Curriculum Node | Current Resource Surface | Next Build Work | Proof / Evidence Route | Graduation Signal |
|---|---|---|---|---|
| `propositional-logic` | `logic-basics-v0`, Boolean learner path | Add proof-object walkthrough for CNF refutation anatomy. | Boolean CNF/LRAT or DRAT; model replay for SAT rows. | Corrupted certificate test fails; lesson names encoder-vs-checker boundary. |
| `predicate-logic` | `finite-predicate-v0` | Add bridge concept rows for finite quantifier expansion and countermodel replay. | Finite expansion plus QF_UF/Alethe for equality-heavy fragments. | Pack rows distinguish finite-domain validity from first-order validity. |
| `proof-methods` | `proof-methods-refutation-v0`, `proof-methods-patterns-v0` | Turn direct/contrapositive/cases/contradiction into reusable proof-pattern rows. | CNF/LRAT for refutation examples; Lean horizon for natural deduction. | Learner page can trace proof method -> solver query -> checked evidence. |
| `induction` | `induction-obligations-v0`, `induction-patterns-v0` | Split bounded base/step checks from induction-schema reconstruction targets. | QF_LIA for finite obstructions; Lean horizon for general induction. | No pack claims full induction from bounded prefixes. |
| `sets` | finite sets, lattices, cardinality packs | Add concept rows for Boolean algebra, finite lattice laws, and counterexample replay. | CNF/LRAT for Boolean refutations; QF_UF/Alethe for lattice/order conflicts. | Every false set/lattice identity has either evidence or an explicit route gap. |
| `relations-and-functions` | relation/function, equivalence, composition, monoid, permutation, action packs | Add reusable rows for quotient maps, image/preimage, inverse tables, and finite actions. | QF_UF/Alethe for function consistency and congruence conflicts. | Equality-heavy rows use checked Alethe where available. |
| `cardinality` | finite cardinality and cardinality-principles packs | Add bridge rows for injection, surjection, bijection, powerset, and infinite horizon. | finite replay/CNF for bounded no-map rows; Lean horizon for Cantor/infinite facts. | Infinite claims are never benchmarked as finite checks. |
| `naturals` | `natural-arithmetic-v0` | Add totality/Peano-shadow concept rows and BV-vs-LIA encoding notes. | Bounded replay, QF_LIA, QF_BV where fixed width is educationally relevant. | Width and finite prefix limits are visible in metadata and lesson text. |
| `integers` | `integer-lia-v0` | Promote common linear-obstruction patterns into shared Diophantine examples. | QF_LIA/Diophantine. | Bad linear rows carry checked integer evidence or a named missing route. |
| `rationals` | `rationals-lra-v0`, rational polynomial pack | Add exact-vs-floating arithmetic row and density/order learner split. | QF_LRA/Farkas for impossible rational inequalities. | Farkas-backed rows recheck independently of solver search. |
| `reals` | RCF shadow, bounded real analysis, metric continuity | Add concept rows for balls, limits, continuity, compactness, and completeness horizons. | QF_LRA/NRA for algebraic shadows; Lean horizon for completeness/general topology. | Each epsilon-delta pack says fixed rational instance vs theorem. |
| `complex` | complex algebraic and transform packs | Add real-pair encoding note and analytic-horizon rows. | NRA/LRA real-pair replay; Lean horizon for holomorphic theory. | Algebraic complex checks avoid claiming analytic coverage. |
| `divisibility-and-euclid` | `gcd-bezout-v0` | Add reusable gcd/divisibility witness schema for number-theory and algebra packs. | Computed witness replay; QF_LIA for divisibility obstructions. | Bezout rows validate both gcd and coefficient identity. |
| `modular-arithmetic` | modular arithmetic and finite ideals | Add quotient-ring and CRT bridge rows. | QF_LIA/Diophantine and QF_BV fixed-width finite residues. | Nonunit inverse rows carry checked arithmetic evidence. |
| `groups` | finite groups, monoids, permutations, actions, homomorphisms | Add concept rows for kernels/images, orbit-stabilizer, Burnside, quotient groups. | QF_UF/Alethe for table congruence and action-law conflicts. | Table checks keep associativity/action-law replay explicit. |
| `rings` | finite rings, ideals, modules, homomorphisms | Extend the landed finite-ring BV route from bad distributivity to more fixed finite ring-table contradictions. | QF_BV bit-blast/DRAT plus QF_UF/Alethe for homomorphism preservation. | Unsat finite-ring rows carry checked CNF evidence without overclaiming Lean. |
| `fields` | finite fields, vector/dual/tensor packs | Extend the landed finite-field BV route from composite no-inverse to more fixed finite-field arithmetic contradictions, then add field-linear-algebra bridge rows for bases, covectors, and bilinear maps. | QF_BV for finite fields; QF_UF/Alethe for table equality conflicts. | Composite-modulus non-field contrast has a checked route. |
| `polynomials` | identities, rational factorization, generating functions | Add coefficient-ring and polynomial-division reusable rows. | Finite replay, QF_LIA/LRA coefficient constraints, Lean horizon for general factorization. | Factorization rows replay product and degree/leading constraints. |
| `sequences-and-limits` | sequence-limit shadow, real-analysis, generating functions | Add bounded tail, Cauchy, recurrence, and convergence-horizon rows. | Finite replay/LRA for bounded tails; Lean horizon for general convergence. | Lessons keep finite prefix evidence separate from convergence theorems. |
| `counting` | counting, permutations, actions, generating functions | Add finite double-counting, Burnside, coefficient extraction, and asymptotic horizon rows. | CNF/LRAT for pigeonhole; finite replay for enumerative witnesses. | Count rows include deterministic universe, enumeration, and replay checksum. |
| `number-theory` | number theory, modular, gcd, integer LIA | Add bounded Diophantine families and proof-route comparisons. | QF_LIA/Diophantine; QF_BV for fixed modulus; Lean horizon for deep theorems. | Each row identifies bounded search vs number-theory theorem. |
| `linear-algebra` | rational matrices, finite vector/dual/module/tensor, spectral, invariants | Add matrix-corpus promotion plan for LU, rank, residual, eigenpair, and tensor rows. | QF_LRA/Farkas, finite-field replay, QF_UF/Alethe for algebraic table conflicts. | Matrix rows can become solver regressions with source-pack back-links. |
| `calculus` | algebraic calculus, Riemann sums, multivariable rational calculus | Add derivative/integral theorem horizon rows plus exact algebraic shadows. | LRA/NRA for polynomial shadows; Lean horizon for FTC, differentiability, convergence. | Calculus packs never conflate finite symbolic replay with analytic theorem proof. |

## Field Extension Matrix

| Field | Curriculum Anchor | Build Next | Solver / Proof Pressure |
|---|---|---|---|
| `logic_and_proof` | foundations layer | proof-object lessons and proof-pattern atlas rows | CNF/LRAT, Alethe, Lean reconstruction |
| `set_theory_and_foundations` | sets, relations, cardinality | quotients, lattices, finite/infinite boundary rows | QF_UF/Alethe, finite replay, Lean horizon |
| `discrete_math` | counting, relations | graph search, matching, cuts, generating functions, asymptotic horizons | SAT/CNF, finite replay, Lean horizon |
| `graph_theory` | sets, relations, counting | extend graph lessons and proof routes beyond coloring into reachability, search runtime, matching, cuts, and d-separation | SAT/CNF, QF_BV for fixed color encodings, BV/LIA counters, model replay |
| `number_theory` | divisibility, modular, fields | bounded Diophantine and residue-family packs | QF_LIA, QF_BV |
| `linear_algebra` | fields, polynomials, relations | LU, rank/nullity, residual, spectral, tensor and module rows | QF_LRA/Farkas, finite-field replay |
| `abstract_algebra` | groups, rings, fields | homomorphisms, ideals, quotients, modules, tensor products | QF_UF/Alethe, QF_BV |
| `real_analysis` | rationals, reals, sequences, calculus | balls, bounded epsilon-delta, compactness/continuity horizons | QF_LRA/NRA, Lean horizon |
| `complex_analysis` | complex, reals, polynomials | real-pair algebra now; analytic rows later | NRA/LRA, Lean horizon |
| `topology` | sets, reals, linear algebra | finite topologies, continuous maps, compactness, connectedness, homology | finite replay, QF_LIA/LRA, Lean horizon |
| `measure_theory` | sets, probability, reals | finite sigma-algebras, product measure, simple integration | finite replay, QF_LRA, Lean horizon |
| `probability_theory` | counting, rationals, measure | probability tables, kernels, Markov chains, hitting times, concentration | QF_LRA, QF_LIA counts, replay |
| `statistics` | probability, linear algebra | exact tests, regression, finite sampling tables, numerical-honesty rows | QF_LRA, QF_LIA, replay |
| `optimization_and_convexity` | rationals, reals, linear algebra | LP/Farkas, convexity, gradients, Hessians | QF_LRA/Farkas, NRA shadows |
| `numerical_analysis` | linear algebra, calculus | residual bounds, Euler steps, interval boxes, exact error recurrences | QF_LRA, replay, numerical-honesty metadata |
| `differential_equations_and_dynamical_systems` | calculus, linear algebra | bounded recurrences, Euler traces, invariant checks | QF_LRA, BV/LIA counters, Lean horizon |
| `geometry` | reals, polynomials, linear algebra | coordinate, affine, oriented-area, incidence, rigidity shadows | QF_LRA/NRA, replay |
| `functional_analysis_and_operator_theory` | linear algebra, real analysis | finite operators, inner products, Chebyshev-system slices | QF_LRA, finite replay, Lean horizon |

## Route-Specific Build Plan

### Boolean CNF/LRAT

Use for finite Boolean refutations: graph coloring, pigeonhole, set identities,
proof-by-contradiction examples.

Build sequence:

1. Commit small deterministic DIMACS artifacts.
2. Add a cargo regression that produces DRAT/LRAT and checks it.
3. Link the proof artifact or generator from `expected.json`.
4. Update the learner page to explain that the encoder is trusted separately
   from the proof checker.

### QF_BV Bit-Blast

Use for fixed-width finite algebra and residue examples where the width is part
of the educational claim.

Build sequence:

1. Add SMT-LIB or generated BV artifacts under the pack.
2. Add model replay for SAT rows against the source finite object.
3. Add DRAT-backed CNF proof checks for UNSAT rows.
4. Keep bit-blast/Tseitin lowering in the trust ledger until Lean
   reconstruction covers the original formula.

### QF_LIA / Diophantine

Use for integer equalities, modular obstructions, counts, rank coefficients, and
finite statistical tail counts.

Build sequence:

1. Encode the impossible integer relation as a tiny SMT-LIB or test fixture.
2. Check the obstruction through the arithmetic proof route.
3. Add a pack row that names the witness or obstruction, not just `unsat`.
4. Promote recurring patterns into reusable cookbook examples.

### QF_LRA / Farkas

Use for rational infeasibility: linear systems, LP thresholds, probability
normalization, expected-time equations, residual bounds, and affine geometry.

Build sequence:

1. Express the row as exact rational constraints.
2. Produce and recheck a Farkas certificate.
3. Link the certificate route from the pack metadata and learner page.
4. Reuse the row as a solver regression only after replay is deterministic.

### QF_UF / Alethe

Use for equality-heavy finite structures: functions, quotient maps,
homomorphisms, monoids, modules, ideals, tensor maps, and action laws.

Build sequence:

1. Encode the equality conflict as a small congruence problem.
2. Export an Alethe proof and check it with the available checker.
3. Keep finite table replay for the mathematical object itself.
4. Add Lean reconstruction only when the Alethe-to-Lean route covers the shape.

### Lean Horizon

Use for general theorems: induction schemas, completeness, compactness, general
algebra, measure convergence, asymptotics, Hilbert/Banach-space theorems, and
analytic complex analysis.

Build sequence:

1. Add a concept row that states the theorem shape and prerequisite resources.
2. Add finite shadows only as examples, not as theorem evidence.
3. Name the missing Lean dependencies in `expected.json` or pack metadata.
4. Promote only after kernel-checked reconstruction lands.

## Commit-Sized Execution Queue

1. R1 bridge-concept rows landed for finite replay, bounded theorem shadows,
   counterexample proof, and Lean horizon; keep future bridge rows narrow and
   generated from `scripts/gen-foundational-concepts.py`.
2. Finish learner audit so every non-template pack appears in a focused lesson
   or a named combined lesson.
3. Continue QF_BV promotions only for fixed-width educational claims that are
   not better served by existing CNF/LRA/LIA routes; the first finite
   rings/fields/graph-coloring DRAT rows are covered.
4. First route-specific proof-upgrade note pass landed on the highest-use
   learner pages: logic/proof, graph/discrete, linear algebra/optimization,
   probability/statistics, and algebra/number theory.
5. Recurring finite algebra equality conflicts now have the
   `family_finite_algebra_alethe` example-family row, backed by the shared
   `math_resource_uf_routes` regression.
6. Recurring exact-rational infeasibility conflicts now have the
   `family_exact_rational_farkas` example-family row, backed by the shared
   `math_resource_lra_routes` regression.
7. Generated dashboard columns for R0-R6 gate level and "next gate" now land
   in the coverage, field, proof-gap, and learner/proof-upgrade dashboards.
8. Selected deterministic R4 packs now have structured `solver_reuse`
   candidate tags: finite cardinality, finite graph packs, integer LIA,
   bounded natural arithmetic, and bounded number theory.
9. Consumer-facing sample queries now land through
   `scripts/query-foundational-resources.py` and
   [CONSUMER-QUERIES.md](CONSUMER-QUERIES.md): summary counts, pack discovery,
   checked-row mining, solver-reuse candidates, and atlas concept lookup over
   the committed JSON data contract.
10. First solver-reuse promotion landed: `logic-basics-v0` now links
    `tiny-cnf-refutation` to a DIMACS artifact and the
    `math_resource_boolean_routes` DRAT/LRAT regression.
11. Revisit crate/repo boundaries only after three real consumers or repeated
    encoder implementations make scripts insufficient.

## Validation Commands

For documentation-only plan edits:

```sh
git diff --check
./scripts/check-links.sh
```

For resource metadata, generated dashboard, or pack edits:

```sh
git diff --check
./scripts/check-foundational-resources.sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/<pack>
python3 scripts/consume-foundational-resources.py
```

For proof-route promotions, add the relevant cargo regression from
[PROOF-UPGRADE-FRONTIER.md](PROOF-UPGRADE-FRONTIER.md) before updating status.
