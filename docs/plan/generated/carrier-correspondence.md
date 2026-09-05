# Carrier correspondence ledger

> **Generated; do not edit by hand.** Source: [`artifacts/carrier-correspondence/carrier-correspondence-v1.json`](../../../artifacts/carrier-correspondence/carrier-correspondence-v1.json). Regenerate with `python3 scripts/gen-carrier-correspondence-md.py`; `--check` is the drift gate, registered in `scripts/check.sh` and the `justfile` beside `check-carrier-correspondence.py --check`.

One row per (Axeyum carrier, Mathlib counterpart) pair (`docs/math-department/14-lean-lang.md` Next Ten item 4). A row records both names with a verified source location, the equality regime on each side (this kernel is built from setoids and defined `Equiv`/`Apart` relations where Mathlib is a classical Cauchy or `Quot.sound` quotient -- ADR-0512, ADR-1588), a grade from a closed five-value enum, and at least one witness theorem pair for every grade except `no-counterpart`. A sentence anywhere in the docs claiming this library "shares a theorem with Mathlib" should cite a row here rather than assert it -- ADR-1665.

## Counts by grade

| Grade | Rows |
|---|---:|
| Same statement (`same-statement`) | 3 |
| Constructively stronger (ours) (`constructively-stronger`) | 2 |
| Constructively weaker (ours) (`constructively-weaker`) | 0 |
| Different object (`different-object`) | 10 |
| No counterpart (`no-counterpart`) | 1 |
| **Total** | **16** |

## Rows

### `CC:algs-commring-commring` -- AlgS.CommRing, the setoid commutative-ring record, against Mathlib's Eq-based CommRing class

**Grade:** Same statement (`same-statement`)

**Reason:** The same beta-reduction argument as AlgS.Group applies pointwise to each ring law, but one asymmetry is worth recording: AlgS.mul_zero is a PROVED theorem here while Mathlib's mul_zero is an ASSUMED field of the more primitive MulZeroClass that CommRing inherits, so the two sides differ in what is proved versus what is axiomatized even though the proposition itself is identical.

| | Axeyum | Mathlib |
|---|---|---|
| Carrier | AlgS.CommRing | CommRing |
| Location | `crates/axeyum-lean-kernel/src/nat_prelude/structures_setoid.rs:863` | `Mathlib/Algebra/Ring/Defs.lean:413` |
| Verification | verified-in-kernel-projection | verified-in-pinned-checkout |
| Equality regime | setoid | eq |

**Witness pairs:**

- `AlgS.mul_zero` vs `mul_zero` -- Same proposition (a*0 = 0), different epistemic status: AlgS.mul_zero is derived from the ring axioms without using the multiplicative identity (structures_setoid.rs:2082-2085 doc); Mathlib's mul_zero is a primitive FIELD of MulZeroClass, assumed rather than derived at that layer even though it is classically derivable higher up.
- `AlgS.mul_neg_one` vs `mul_comm` -- AlgS.mul_neg_one (a * -1 = -a) is downstream of mul_zero and commutativity; cited alongside mul_comm as the second generic ring law this spine proves once rather than per-instance.

### `CC:algs-field-field` -- Alg.Field (the Eq-based spine; AlgS.Field is not yet built) against Mathlib's Field class

**Grade:** Same statement (`same-statement`)

**Reason:** Alg.Field's laws are Eq-based like Mathlib's Field, so the same beta-erasure argument as AlgS.Group/CommRing applies directly with no equiv substitution needed; but the row's namesake AlgS.Field is unbuilt, which is itself the finding reviewer 04's stake (docs/math-department/14-lean-lang.md chair 04) asked this ledger to make precise rather than leave as an ADR footnote.

| | Axeyum | Mathlib |
|---|---|---|
| Carrier | Alg.Field (AlgS.Field, named in ADR-1627 / roadmap W3-2 as Rat.fieldS's target type, is UNBUILT) | Field |
| Location | `crates/axeyum-lean-kernel/src/nat_prelude/structures.rs:1550` | `Mathlib/Algebra/Field/Defs.lean:180` |
| Verification | verified-in-kernel-projection | verified-in-pinned-checkout |
| Equality regime | eq | eq |

**Witness pairs:**

- `Alg.Field.mulInv` vs `mul_inv_cancel₀` -- Alg.Field.mulInv is conditional (structures.rs:1389, `cond_inv_field`) matching Mathlib's hypothesis-carrying mul_inv_cancel₀ (h : a ≠ 0); both are bare-inequality hypotheses, not witnessed apartness data, so this pair is same-statement rather than constructively-stronger.
- `Rat.rat_isField` vs *(no Mathlib counterpart for this pair)* -- One-sided: this is the Rat instantiation of Alg.Field, included to show the concrete route from the abstract spine to a landed Field-shaped instance. No single Mathlib lemma names 'Field ℚ instantiated' since it is a type-class instance rather than a theorem there.

**Notes:** The brief that commissioned this ledger named the row 'AlgS.Field ↔ Field'. AlgS.Field does not exist as a kernel declaration (confirmed absent from the projection and from structures_setoid.rs's own nine-record list). Recording this honestly, per the brief's own discipline ('mark anything you could not verify unverified rather than guessing'), rather than inventing a grade for an object that is not built.

### `CC:algs-group-group` -- AlgS.Group, the equiv-parametrized setoid group record, against Mathlib's Eq-based Group class

**Grade:** Same statement (`same-statement`)

**Reason:** structures_setoid.rs's own module doc records that app2(k, equiv, lhs, rhs) beta-reduces to Eq carrier lhs rhs exactly when equiv := @Eq carrier, so every AlgS.Group law is, up to that one substitution, the identical string to the matching Alg.Group / classical Group law.

| | Axeyum | Mathlib |
|---|---|---|
| Carrier | AlgS.Group | Group |
| Location | `crates/axeyum-lean-kernel/src/nat_prelude/structures_setoid.rs:859` | `Mathlib/Algebra/Group/Defs.lean:1192` |
| Verification | verified-in-kernel-projection | verified-in-pinned-checkout |
| Equality regime | setoid | eq |

**Witness pairs:**

- `AlgS.add_left_cancel` vs `mul_left_cancel` -- Proved once, generically, over an arbitrary AlgS.Group; specializes to the additive-cancellation law exactly Mathlib's mul_left_cancel states, modulo the equiv:=Eq substitution and the additive/multiplicative naming convention.
- `AlgS.invInv` vs `inv_inv` -- a^-1^-1 = a in both, again modulo the equiv-vs-Eq substitution.

### `CC:complex-complex` -- Complex over CReal pairs with a proved order-obstruction, against Mathlib's classical Complex struct

**Grade:** Constructively stronger (ours) (`constructively-stronger`)

**Reason:** Complex.no_compatible_order derives False from seven ordered-ring axioms and the witness I constructively (no classical double-negation elimination), a genuine additional result with no Mathlib analogue, which simply never registers a LinearOrder ℂ instance rather than proving one is impossible.

| | Axeyum | Mathlib |
|---|---|---|
| Carrier | Complex | Complex |
| Location | `crates/axeyum-lean-kernel/src/complex.rs:1453` | `Mathlib/Data/Complex/Basic.lean:34` |
| Verification | verified-in-kernel-projection | verified-in-pinned-checkout |
| Equality regime | setoid | eq |

**Witness pairs:**

- `Complex.no_compatible_order` vs *(no Mathlib counterpart for this pair)* -- Grep for 'LinearOrder ℂ' and related order identifiers near Complex in the pinned checkout found no explicit non-orderability theorem -- Mathlib's absence of a LinearOrder ℂ instance is an omission, not a proof. This asymmetry (proved impossibility vs. silent omission) is the row's strongest evidence.
- `Complex.add_comm` vs `add_comm` -- Same ring law, but ours is proved directly over Complex.Equiv here while Mathlib's CommRing ℂ instance inherits it for free from the abstract hierarchy -- comparable content, carrier-transport-shaped modulo the setoid-vs-Eq substitution used throughout this ledger.

### `CC:cpoint-euclideanspace` -- CPoint, a pair of CReals with witnessed non-degeneracy, against Mathlib's EuclideanSpace ​Pi-type

**Grade:** Different object (`different-object`)

**Reason:** The same two-asymmetries pattern ADR-1030 used for EVT: our Ceva theorem assumes strictly more (a witnessed PosBound non-degeneracy rather than a bare inequality) while Mathlib's is stated far more generally (arbitrary field, arbitrary-dimension affine space, indexed beyond 3 points), so neither dominates and the statements are not comparable on one axis.

| | Axeyum | Mathlib |
|---|---|---|
| Carrier | CPoint | EuclideanSpace ℝ (Fin 2) |
| Location | `crates/axeyum-lean-kernel/src/creal_point.rs:1599` | `Mathlib/Analysis/InnerProductSpace/PiL2.lean:110` |
| Verification | verified-in-kernel-projection | verified-in-pinned-checkout |
| Equality regime | setoid | eq |

**Witness pairs:**

- `CPoint.ceva_concurrent_of_ratio_product` vs `prod_div_one_sub_eq_one_of_mem_line_point_lineMap` -- Ours is division-free and its non-degeneracy hypothesis is data (PosBound (mul D D) k), not a bare inequality; theirs is over an arbitrary Field k and AffineSpace, with a bare r i ≠ 0 hypothesis and no witness carried. Stronger in one respect, far more general in another.
- `CPoint.menelaus_collinear_of_ratio_product` vs *(no Mathlib counterpart for this pair)* -- Clean negative, confirmed by grep across the full pinned Mathlib tree for 'menelaus' and 'varignon' (case-insensitive): zero matches for either, against a 53-match positive control on 'AffineSubspace' in the same tree. Menelaus and Varignon have no Mathlib counterpart at this pin, unlike Ceva.

### `CC:creal-real` -- CReal, a Bishop-style regular-sequence real, against Mathlib's Cauchy-quotient Real

**Grade:** Constructively stronger (ours) (`constructively-stronger`)

**Reason:** Graded on the strongest measured comparable case: CReal.ivt_approx returns, for every tolerance, a rational-indexed approximate root with an explicit witness and axiom footprint 0, where Mathlib's intermediate_value_Icc asserts pure existence under [propext, Classical.choice, Quot.sound] (ADR-1030).

| | Axeyum | Mathlib |
|---|---|---|
| Carrier | CReal | Real |
| Location | `crates/axeyum-lean-kernel/src/creal.rs:6326` | `Mathlib/Data/Real/Basic.lean:35` |
| Verification | verified-in-kernel-projection | verified-in-pinned-checkout |
| Equality regime | setoid | quotient-eq |

**Witness pairs:**

- `CReal.ivt_approx` vs `intermediate_value_Icc` -- Ours: for each rational tolerance e>0, computes a point within e of a root, footprint []. Theirs: asserts existence of an exact root over an abstract densely-ordered topological order, footprint [propext, Classical.choice, Quot.sound]. Content in docs/mathematics-2026-08/08-ivt-and-evt-measured-against-mathlib.md.
- `CReal.evt_approx_max` vs `IsCompact.exists_isMaxOn` -- Deliberately NOT evidence for the row's grade -- recorded to prevent the row from being misread as claiming EVT dominance too. ADR-1030 section 1 CONCEDES this pair as different-object: our hypothesis (uniform continuity, Sort 1 data) is strictly stronger and our conclusion (approximate, non-convergent maximum) strictly weaker than Mathlib's pointwise-continuous exactly-attained statement, in the same direction on both axes, so the two are not comparable at all.

**Notes:** This row deliberately grades on IVT rather than averaging IVT and EVT: a single grade field cannot carry two theorems pulling in different directions, and ADR-1030 already adjudicated EVT as non-comparable in print. Reviewer 03's stake (docs/math-department/03-classical-analysis.md) is answered by this row plus its EVT witness, not by a second row.

### `CC:intspace-lebesgue-integral` -- IntSpace, a Daniell-style integral-first integration space, against Mathlib's measure-first Bochner integral

**Grade:** Different object (`different-object`)

**Reason:** The construction order is reversed on the two sides -- Mathlib defines the integral from a pre-existing measure, while IntSpace defines the integral as primitive and derives measure from it in the classical Daniell style -- so even where both eventually integrate the same kind of function, the objects being compared are built in opposite directions with no verified equivalence between them here.

| | Axeyum | Mathlib |
|---|---|---|
| Carrier | IntSpace | the Bochner integral (MeasureTheory.integral) |
| Location | `crates/axeyum-lean-kernel/src/intspace.rs:768` | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:160` |
| Verification | verified-in-kernel-projection | verified-in-pinned-checkout |
| Equality regime | setoid | none |

**Witness pairs:**

- `IntSpace.CReal.integral_congr` vs `integral_congr_ae` -- Mathlib's version quantifies over an almost-everywhere equivalence relative to a measure (f =ᵃᵉ[μ] g), which presupposes the sigma-algebra/measure apparatus IntSpace does not build; ours is a direct congruence over CReal.Equiv with no exceptional null set. COULD NOT FULLY VERIFY a bare (non-ae) integral_nonneg at the general Bochner level in this pinned commit -- the located integral_nonneg is interval-integral-specific (Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1349); a future lane should re-grep before citing a general-measure nonnegativity lemma name here.

### `CC:ipc-logic-modeltheory` -- Provable, a natural-deduction IPC derivation system with a soundness theorem, against Mathlib's algebraic Heyting order theory

**Grade:** Different object (`different-object`)

**Reason:** Ours is proof-theoretic -- a derivation system plus a soundness theorem connecting it to a semantics -- and Mathlib's is purely algebraic (an order-theoretic class) plus an unrelated decision tactic, so the two formalize different KINDS of object even though both are commonly called 'intuitionistic logic'.

| | Axeyum | Mathlib |
|---|---|---|
| Carrier | Provable (ipc_provable.rs / ipc_heyting.rs / ipc_eval.rs / ipc_soundness.rs) | HeytingAlgebra (order-theoretic; no proof-theoretic natural-deduction or soundness system exists in Mathlib for IPC) |
| Location | `crates/axeyum-lean-kernel/src/ipc_provable.rs:175` | `Mathlib/Order/Heyting/Basic.lean:154` |
| Verification | verified-in-kernel-projection | verified-in-pinned-checkout |
| Equality regime | none | eq |

**Witness pairs:**

- `ipc_excluded_middle_not_provable` vs *(no Mathlib counterpart for this pair)* -- Refutes Provable FormulaList.nil (or (var 0) (imp (var 0) bot)) via the soundness theorem against a 3-element Heyting-chain semantics. Mathlib's HeytingAlgebra class states the algebraic laws a Heyting algebra must satisfy but proves no comparable non-provability-of-excluded-middle result for any natural-deduction system, because it has no such system to state it about.

### `CC:metric-metricspace` -- The generic equiv-parametrized Metric record, against Mathlib's topology/uniformity-bundled PseudoMetricSpace

**Grade:** Different object (`different-object`)

**Reason:** Mathlib's class bundles topology, uniformity and bornology data this record does not build at all, and identity-of-indiscernibles is one field there against two plus a congruence field here, so the two records differ in field count and purpose, not merely in strength.

| | Axeyum | Mathlib |
|---|---|---|
| Carrier | Metric.* (instantiated at CReal and CPoint) | PseudoMetricSpace |
| Location | `crates/axeyum-lean-kernel/src/metric.rs:351` | `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:140` |
| Verification | verified-in-kernel-projection | verified-in-pinned-checkout |
| Equality regime | setoid | eq |

**Witness pairs:**

- `Metric.CPoint.distComm` vs `dist_comm` -- Same law (symmetry of distance); ours is proved for a bespoke equiv-parametrized record instantiated at CPoint, theirs is inherited from the full topology-bundled typeclass.
- `Metric.CPoint.distTriangle` vs `dist_triangle` -- Same law (triangle inequality); recorded as a second comparable field alongside distComm, both inside the row graded different-object at the carrier level.

**Notes:** COULD NOT VERIFY: whether Metric.CReal/CPoint's distSelf/distEquiv split has been checked to be logically equivalent to Mathlib's single dist_self field, versus merely analogous in shape -- flagged rather than asserted.

### `CC:nat-finset-finset` -- Nat.Finset, a bounded predicate-plus-bound pair, against Mathlib's nodup Multiset quotient Finset

**Grade:** Different object (`different-object`)

**Reason:** The carriers are not the same construction even loosely: ours is a computed bounded predicate whose own Eq is not set-extensional, theirs is a nodup quotient of lists whose Eq is set-extensional by construction, so no substitution identifies the two types.

| | Axeyum | Mathlib |
|---|---|---|
| Carrier | Nat.Finset | Finset |
| Location | `crates/axeyum-lean-kernel/src/nat_prelude.rs:7413` | `Mathlib/Data/Finset/Defs.lean:75` |
| Verification | verified-in-kernel-projection | verified-in-pinned-checkout |
| Equality regime | eq | quotient-eq |

**Witness pairs:**

- `Nat.Finset.exists_memB_of_card_pos` vs `Finset.card_pos` -- Landed 2026-09-05 (hall-singleton lane), after this repository's kernel-dependency-projection-v1.json was last regenerated -- present in source and in artifacts/facts/F-nat-finset-exists-memb-of-card-pos.json, absent from the projection id list, hence marked source-only rather than kernel-projection-verified. Ours computes a member by bounded search from a positive count (footprint []); Mathlib's card_pos is a biconditional against Finset.Nonempty (`∃ x, x ∈ s`), and extracting a witness from that existential in general goes through Classical.choice.

### `CC:nat-graph-simplegraph` -- Nat.Graph, a computed adjacency-with-forced-symmetry pair, against Mathlib's Prop-field SimpleGraph

**Grade:** Different object (`different-object`)

**Reason:** Adjacency's own well-formedness is computed and forced by construction here, versus assumed as a per-instance Prop field there, and the one instance this repository names beyond that structural gap -- the 3-3 Ramsey number -- has no Mathlib formalization to compare against at all.

| | Axeyum | Mathlib |
|---|---|---|
| Carrier | Nat.Graph | SimpleGraph |
| Location | `crates/axeyum-lean-kernel/src/nat_prelude.rs:7411` | `Mathlib/Combinatorics/SimpleGraph/Basic.lean:92` |
| Verification | verified-in-kernel-projection | verified-in-pinned-checkout |
| Equality regime | eq | eq |

**Witness pairs:**

- `Nat.Graph.HasClique3` vs `SimpleGraph.Adj` -- Not the same object: HasClique3 g := exists a b c, adjB g a b and adjB g b c and adjB g a c, over the computed adjB; Adj is Mathlib's raw relation field, with no forced structural symmetry.
- `Nat.Graph.IsRamseyNumber33` vs *(no Mathlib counterpart for this pair)* -- Clean negative: `grep -rli ramsey Mathlib/Combinatorics/` returns only HalesJewett.lean and Hindman.lean, and in both files 'Ramsey theory' is a descriptive keyword in the module docstring only -- neither states or proves a finite Ramsey number (e.g. R(3,3)=6). No Mathlib counterpart at this pin.

### `CC:nat-multiset-multiset` -- Nat.Multiset, a bounded multiplicity function, against Mathlib's permutation-quotient Multiset

**Grade:** Different object (`different-object`)

**Reason:** A raw bounded multiplicity function and a permutation-quotient of lists are different representations with different Eq behavior at the boundary (unbounded vs bounded support), even though one comparable law transports cleanly.

| | Axeyum | Mathlib |
|---|---|---|
| Carrier | Nat.Multiset | Multiset |
| Location | `crates/axeyum-lean-kernel/src/nat_prelude.rs:7409` | `Mathlib/Data/Multiset/Defs.lean:70` |
| Verification | verified-in-kernel-projection | verified-in-pinned-checkout |
| Equality regime | eq | quotient-eq |

**Witness pairs:**

- `Nat.Multiset.count_add` vs `Multiset.count_add` -- Both state count a (s + t) = count a s + count a t. This one law is carrier-transport-shaped (the same string once the carrier is erased); the row is still graded different-object because the carriers themselves, and their Eq, are not interchangeable outside this one law.

### `CC:nat-rado-partition-regularity` -- Nat.Rado's partition-regularity Rado numbers have no Mathlib counterpart at the pinned commit

**Grade:** No counterpart (`no-counterpart`)

**Reason:** Rado's theorem on partition regularity of linear equations (which Nat.Rado.IsRadoNumber formalizes, generalizing Schur's theorem) is absent from the pinned Mathlib checkout; the one same-named hit (Rado's selection lemma) is a different theorem entirely, confirmed by reading its actual statement.

| | Axeyum | Mathlib |
|---|---|---|
| Carrier | Nat.Rado | *(none)* |
| Location | `crates/axeyum-lean-kernel/src/nat_prelude.rs:7410` | `n/a` |
| Verification | verified-in-kernel-projection | not-applicable |
| Equality regime | eq | none |

**Notes:** Not one of the brief's named required rows -- added because the research needed to confirm Nat.Graph's Ramsey-number gap also settled this adjacent case cleanly, and a clean no-counterpart negative is exactly the kind of row this ledger exists to make citable rather than merely asserted.

### `CC:nat-rm-computability` -- Nat.RM, a bespoke self-referential register machine, against Mathlib's general Partrec.Code halting problem

**Grade:** Different object (`different-object`)

**Reason:** CORRECTS the brief that commissioned this ledger, which assumed Nat.RM has no Mathlib counterpart: Mathlib's Computability library has a general halting-problem theorem and a full Partrec.Code/Turing-machine apparatus, so a counterpart exists; the grade is different-object rather than no-counterpart because Nat.RM is a bespoke, unconnected shallow embedding refuting one self-referential diagonalization instance, not a restriction of Mathlib's universal-code formalism.

| | Axeyum | Mathlib |
|---|---|---|
| Carrier | Nat.RM | the general halting problem over Nat.Partrec.Code |
| Location | `crates/axeyum-lean-kernel/src/nat_prelude.rs:7416` | `Mathlib/Computability/Halting.lean:65` |
| Verification | verified-in-kernel-projection | verified-in-pinned-checkout |
| Equality regime | eq | none |

**Witness pairs:**

- `Nat.RM.self_halting_not_decidable` vs `halting_problem` -- Ours refutes one bespoke H : Nat -> Bool assumed to decide self-halting for a specific register-machine diagonalization (Halts is not shown undecidable for an enumeration of machines, only this one construction); Mathlib's is the general result over its own universal Partrec.Code type, with Rice's theorem as a landed corollary. No transport is recorded between the two computational models.

**Notes:** This is the one row where following the brief's own name literally would have produced a false no-counterpart claim; recorded as a correction rather than silently substituted, per the ledger's own discipline that every cited absence must be a measured negative.

### `CC:rat-matrix-matrix` -- Fixed-size Rat.det2/det3 plus symbolic-dimension Rat.rank, against Mathlib's general-n Matrix

**Grade:** Different object (`different-object`)

**Reason:** det2/det3 are fixed-size (2 and 3 explicit arguments) against Mathlib's Leibniz-formula determinant at arbitrary n, which ADR-1030 already marks as not-comparable rather than a strength difference; Rat.rank is symbolic-dimension and closer to comparable, but the carrier as a whole (four/nine explicit scalars vs. a general function type) is not the same object.

| | Axeyum | Mathlib |
|---|---|---|
| Carrier | Rat matrices (four explicit Rat arguments for 2x2; nine for 3x3; Nat -> Nat -> Rat at symbolic dimension for rank) | Matrix |
| Location | `crates/axeyum-lean-kernel/src/rat_prelude.rs:3516` | `Mathlib/LinearAlgebra/Matrix/Defs.lean:53` |
| Verification | verified-in-kernel-projection | verified-in-pinned-checkout |
| Equality regime | eq | eq |

**Witness pairs:**

- `Rat.det2_mul` vs `Matrix.det` -- Not comparable per ADR-1030's own linear-algebra section: fixed 2x2 versus a general-n alternating multilinear form. Recorded here rather than omitted, since 'not comparable' is itself the finding for this witness.
- `Rat.rank` vs `Matrix.rank` -- CORRECTION to ADR-1030 (2026-08-31), which measured Rat matrices as having no rank (0 matches). Rat.rank now exists at symbolic dimension (Nat -> Nat -> Rat) over the echelon/pivot machinery in rat_prelude/nullity.rs, and is a genuinely comparable pair to Matrix.rank -- unlike det2/det3, this specific pair is not fixed-size-vs-general-n. A future lane grading this pair alone, rather than the carrier as a whole, may find a different grade than this row's different-object.

### `CC:rat-probability-pmf` -- The Rat-valued IsDistribution/sumRange shelf against Mathlib's PMF and its Binomial instance

**Grade:** Different object (`different-object`)

**Reason:** Mathlib's PMF is measure-theoretic, general-type, and NNReal-valued with sigma-algebra machinery available; this shelf is a raw Rat-valued sum-to-one predicate with no measure apparatus, so the two are not the same kind of object even where both formalize a binomial distribution.

| | Axeyum | Mathlib |
|---|---|---|
| Carrier | Rat.IsDistribution / Rat.sumRange (the finite-probability shelf over Rat.OrderedRing) | PMF |
| Location | `crates/axeyum-lean-kernel/src/rat_prelude.rs:3468` | `Mathlib/Probability/ProbabilityMassFunction/Basic.lean:46` |
| Verification | verified-in-kernel-projection | verified-in-pinned-checkout |
| Equality regime | eq | other |

**Witness pairs:**

- `Rat.binomial_expectation` vs `PMF.binomial` -- Both formalize the binomial distribution's core object; ours computes exact rational moments (expectation, variance, a Chebyshev bound, a fourth-moment inequality) directly over Rat, theirs constructs the PMF itself over NNReal without, at this pin, a located moment-computation lemma to compare against directly.

## How to re-measure

```sh
python3 scripts/check-carrier-correspondence.py --check
python3 -m unittest scripts.tests.test_check_carrier_correspondence
python3 scripts/gen-carrier-correspondence-md.py --check
```

