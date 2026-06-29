# Math Resource Proof Upgrade Frontier

This is the hand-authored execution frontier for turning the current math
curriculum resources from finite replay and proof-gap status into checked
evidence. The generated truth source is
[learner-proof-upgrade-dashboard.md](generated/learner-proof-upgrade-dashboard.md);
this file explains which route to work first, what artifact should be emitted,
and how a pack graduates.

Axeyum's identity stays fixed: untrusted fast search, trusted small checking.
For these resources, prose never upgrades a claim. A pack graduates only when
the original finite obligation is replayed or a proof certificate checks under
the route named in the pack metadata.

## Current Baseline

Generated from the current math resource queue:

- math example packs: 84
- learner-linked packs: 84 focused links
- packs with non-checked proof rows: 73
- non-checked proof rows: 223

Candidate route totals:

| Route | Pack Count | Meaning |
|---|---:|---|
| [Boolean CNF/LRAT](../proof-cookbook/recipes/boolean-cnf-lrat.md) | 3 | Boolean refutations that should carry checked CNF proof objects. |
| [QF_BV bit-blast](../proof-cookbook/recipes/qf-bv-bitblast.md) | 3 | Finite arithmetic/table obligations that should lower through BV/CNF evidence. |
| [QF_LIA Diophantine](../proof-cookbook/recipes/qf-lia-diophantine.md) | 5 | Integer equalities, counts, modular constraints, and rank obstructions. |
| [QF_LRA Farkas](../proof-cookbook/recipes/qf-lra-farkas.md) | 22 | Exact rational infeasibility and linear inequality obligations. |
| [QF_UF/Alethe](../proof-cookbook/recipes/qf-uf-congruence-alethe.md) | 13 | Equality-heavy finite structures and congruence conflicts. |
| [Lean horizon](../proof-cookbook/recipes/lean-horizon-template.md) | 54 | General theorem statements that remain outside bounded SMT replay. |

## Execution Order

### 0. Classify `needs-proof-route` (Current Queue Done)

Classified targets:

- [descriptive-statistics-v0](../../artifacts/examples/math/descriptive-statistics-v0/)
- [finite-probability-v0](../../artifacts/examples/math/finite-probability-v0/)

Classification:

- descriptive-statistics satisfiable witness rows remain finite-model replay;
  future impossible exact-rational statistic constraints use QF_LRA/Farkas, and
  future inconsistent integer margin/count constraints use QF_LIA/Diophantine;
- finite-probability satisfiable witness rows remain finite-model replay;
  future impossible normalization, nonnegativity, conditioning, or Bayes-rule
  constraints use QF_LRA/Farkas;
- keep satisfiable witness rows on finite-model replay, with model replay as
  the checked evidence;
- keep statistical inference, sampling, and continuous probability outside
  proof status until a separate numerical-honesty or Lean route exists.

Graduation:

- both packs have explicit proof-cookbook recipe links in `source_refs`;
- each non-checked expected-result row is either still honestly replay-only or
  has a named certificate route;
- pack validators and foundational dashboard generation pass.

The current generated queue has no `needs-proof-route` rows. Reopen this step
only when new packs enter the dashboard without an upgrade recipe.

### 1. Boolean CNF/LRAT

First targets:

- [graph-coloring-v0](../../artifacts/examples/math/graph-coloring-v0/) (first
  DIMACS-backed DRAT/LRAT regression landed for triangle non-2-colorability)
- [finite-sets-v0](../../artifacts/examples/math/finite-sets-v0/)
  (DIMACS-backed DRAT/LRAT regression landed for malformed distributive-law
  rejection)
- [proof-methods-patterns-v0](../../artifacts/examples/math/proof-methods-patterns-v0/)
  (DIMACS-backed DRAT/LRAT regression landed for contradiction/refutation)

Expected artifact:

- a deterministic CNF encoding for the finite refutation;
- a checked DRAT or LRAT certificate for the concrete CNF;
- a lesson note that separates graph/set/pigeonhole encoding trust from proof
  checking of the generated CNF.

Validation:

```sh
cargo test -p axeyum-cnf drat
cargo test -p axeyum-cnf lrat
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/graph-coloring-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-sets-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/proof-methods-patterns-v0
./scripts/check-foundational-resources.sh
```

Graduation:

- every upgraded unsat row links to a concrete proof artifact or generation
  recipe;
- corrupted or missing certificates are rejected by tests;
- the learner page names the trust boundary: encoder plus search are not the
  trusted core; the certificate checker is.

### 2. QF_LRA/Farkas

First targets:

- [rationals-lra-v0](../../artifacts/examples/math/rationals-lra-v0/)
  (first resource-backed Farkas regression landed for fixed trichotomy and
  order-transitivity refutations)
- [linear-algebra-rational-v0](../../artifacts/examples/math/linear-algebra-rational-v0/)
  (resource-backed Farkas regression landed for the singular inconsistent
  system)
- [linear-optimization-v0](../../artifacts/examples/math/linear-optimization-v0/)
  (resource-backed Farkas regression landed for the objective-threshold
  conflict)
- [convexity-rational-v0](../../artifacts/examples/math/convexity-rational-v0/)
  (resource-backed Farkas regression landed for the bad midpoint-convexity
  row)
- [finite-concentration-v0](../../artifacts/examples/math/finite-concentration-v0/)
  (resource-backed Farkas regression landed for the bad finite tail-bound row)

Secondary targets:

- affine and orientation geometry;
- inner-product, spectral, matrix-invariant, numerical-linear-algebra, and
  random-matrix packs;
- Markov chains, hitting times, Euler shadows, least-squares regression, and
  rational real-analysis rows.

Expected artifact:

- an `UnsatFarkas` certificate for infeasible exact-rational systems;
- exact-rational replay for satisfiable witnesses and equality identities;
- Lean reconstruction only for covered generated modules.

Validation:

```sh
cargo test -p axeyum-solver --test evidence lra_unsat_evidence_carries_a_recheckable_farkas_certificate
cargo test -p axeyum-solver --test evidence tampered_farkas_evidence_fails_its_own_check
cargo test -p axeyum-solver --test lean_crosscheck certified_lra_interpolant_both_farkas_certs_checked_by_real_lean
./scripts/check-foundational-resources.sh
```

Graduation:

- infeasible linear systems carry independently checked rational multipliers;
- nonlinear or general-analysis claims stay replay-only or Lean-horizon unless
  the row has been reduced to a linear certificate with explicit lowering
  evidence;
- dashboards show fewer QF_LRA/Farkas replay-only rows.

### 3. QF_UF/Alethe

First targets:

- [equivalence-classes-v0](../../artifacts/examples/math/equivalence-classes-v0/)
- [relations-functions-v0](../../artifacts/examples/math/relations-functions-v0/)
- [finite-groups-v0](../../artifacts/examples/math/finite-groups-v0/)
- [function-composition-v0](../../artifacts/examples/math/function-composition-v0/)
- [finite-algebra-homomorphisms-v0](../../artifacts/examples/math/finite-algebra-homomorphisms-v0/)

Secondary targets:

- monoids, lattices, permutation groups, vector spaces, dual spaces, modules,
  ideals, and tensor products where the finite table problem is equality-heavy.

Expected artifact:

- an Alethe proof for the congruence conflict or functional-consistency step;
- zero-trust or explicitly accounted trust-step evidence;
- finite model replay for satisfiable structure-table witnesses.

Validation:

```sh
cargo test -p axeyum-solver --test evidence qf_ufbv_unsat_carries_a_zero_trust_alethe_certificate
cargo test -p axeyum-solver --test evidence qf_uf_declared_sort_equality_unsat_carries_zero_trust_alethe_certificate
cargo test -p axeyum-solver --test lean_crosscheck qf_uf_declared_sort_equality_checks_in_real_lean
cargo test -p axeyum-solver --test lean_crosscheck qf_ufbv_refutation_checks_in_real_lean
./scripts/check-foundational-resources.sh
```

Graduation:

- the proof route derives the congruence step rather than trusting an
  Ackermannized rewrite silently;
- pack metadata distinguishes finite algebra-table replay from the general
  algebra theorem horizon;
- learner pages show how the finite witness relates to the broader structure.

### 4. QF_LIA/Diophantine

First targets:

- [modular-arithmetic-v0](../../artifacts/examples/math/modular-arithmetic-v0/)
- [exact-statistical-tests-v0](../../artifacts/examples/math/exact-statistical-tests-v0/)
- [finite-simplicial-homology-v0](../../artifacts/examples/math/finite-simplicial-homology-v0/)
- [induction-patterns-v0](../../artifacts/examples/math/induction-patterns-v0/)

Reference packs already on the route:

- [integer-lia-v0](../../artifacts/examples/math/integer-lia-v0/)
- [gcd-bezout-v0](../../artifacts/examples/math/gcd-bezout-v0/)
- [number-theory-v0](../../artifacts/examples/math/number-theory-v0/)

Expected artifact:

- an `UnsatDiophantine` certificate for integer equality systems;
- integer-interval Lean reconstruction for covered inequality slices;
- finite replay for rows that are count enumeration rather than a solver-form
  LIA contradiction.

Validation:

```sh
cargo test -p axeyum-solver diophantine
cargo test -p axeyum-solver certificate_tamper_is_rejected
cargo test -p axeyum-solver --test int_inequality_lean_reconstruct
./scripts/check-foundational-resources.sh
```

Graduation:

- upgraded rows record the normalized integer system and the divisibility
  obstruction;
- modular examples do not claim proof status until they emit solver-form
  evidence or an explicitly checked finite table;
- homology rank rows state whether the checked object is integer linear
  algebra, finite boundary replay, or the general homology Lean horizon.

### 5. QF_BV Bit-Blast

First targets:

- [finite-rings-v0](../../artifacts/examples/math/finite-rings-v0/)
- [finite-fields-v0](../../artifacts/examples/math/finite-fields-v0/)
- [graph-coloring-v0](../../artifacts/examples/math/graph-coloring-v0/)

Expected artifact:

- model replay against original terms for satisfiable rows;
- checked DRAT evidence for generated CNF in unsat rows;
- an explicit trust-step ledger for bit-blast/Tseitin lowering until Lean
  reconstruction covers the original formula.

Validation:

```sh
cargo test -p axeyum-solver --test evidence unsat_evidence_carries_a_recheckable_drat_certificate
cargo test -p axeyum-solver --test evidence qf_bv_drat_unsat_reports_bitblast_tseitin_sat_steps
./scripts/check-foundational-resources.sh
```

Graduation:

- SAT rows replay lifted models on the source-level finite algebra term;
- unsat rows carry checked CNF evidence and do not overclaim Lean kernel
  coverage for the lowering;
- BV routes are used only where fixed finite width is part of the educational
  claim.

### 6. Lean Horizon Families

First theorem families:

- induction schemas beyond bounded base/step obligations;
- real limits, epsilon-delta continuity, compactness, connectedness, and
  integration;
- finite shadows of measure, probability, martingales, stochastic kernels, and
  hitting times where the general theorem is countable or limiting;
- general algebra and topology statements;
- Chebyshev spaces, operator theory, complex analysis, and functional-analysis
  claims.

Expected artifact:

- a Lean module with no `sorry`;
- a concrete check command beside the graduated resource;
- an axiom audit for exported theorem statements.

Graduation:

- finite shadows continue to validate through their example-pack checks;
- the unbounded theorem stays `lean-horizon` until the Lean command exists and
  passes;
- a Lean file depending on `sorryAx` does not graduate.

## Per-Pack Definition Of Done

A proof upgrade is complete only when all of these are true:

- `metadata.json` names the route in `source_refs` and the relevant
  graduation criteria;
- every upgraded expected-result row has explicit evidence status;
- route-specific tests pass or a generated resource validator checks the
  emitted artifact;
- the learner page states what is trusted and what remains a horizon;
- `python3 scripts/validate-foundational-example-pack.py <pack>` passes;
- `./scripts/check-foundational-resources.sh` regenerates dashboards cleanly;
- `./scripts/check-links.sh` passes.

## Non-Goals

- Do not turn every replay-only row into a proof-object row. SAT witnesses and
  finite-model replay are valid checked evidence when the claim is satisfiable
  or explicitly finite.
- Do not promote general analysis, topology, probability, algebra, or
  functional-analysis theorems from finite shadows to proved results without a
  Lean artifact.
- Do not hide lowering trust behind a solver verdict. If a route depends on
  bit-blasting, CNF encoding, table generation, or abstraction, name the trusted
  and untrusted parts in metadata and lessons.

## Maintenance

Regenerate the mechanical view before choosing the next proof-upgrade target:

```sh
./scripts/check-foundational-resources.sh
```

Then compare this plan with
[proof-gap-dashboard.md](generated/proof-gap-dashboard.md) and
[learner-proof-upgrade-dashboard.md](generated/learner-proof-upgrade-dashboard.md).
When route counts move materially, update this frontier in the same commit as
the pack upgrade so future agents do not mine stale priorities.
