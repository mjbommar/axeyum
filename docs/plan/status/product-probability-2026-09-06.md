# Lane: product-probability — the product space was already here, under a determinant's name

<!-- plan-section: lane-status -->

**The k-fold product probability space landed at ℚ, and the deciding finding is
that the index set already existed** (`WIP`, product-probability, 2026-09-06,
ADR-1677). The brief priced two routes: (a) build a product of index ranges
with a product weight and prove it is again a distribution, or (b) assume the
k-fold product rule the way `Rat.Independent` already assumes the two-fold one.
It also carried a measurement — "no `prod`/`joint`-named declaration in `Rat`
(543), `AlgS` (390) or `IntSpace` (98) is a product space" — which is correct
about NAMES and wrong about structure.

`Rat.sumMaps m n F` (ADR-1543, built for Cauchy–Binet) is a finite sum indexed
by the whole function space `[0,m) → [0,n)`. That IS the k-fold product index
range: `m` factors, each drawing from `[0,n)`, and a point is a choice of one
index per factor. `Int.prodRange_sumRange_expand` is the generalized
distributive law `∏_{i<m} ∑_{k<n} c i k = ∑_g ∏_{i<m} c i (g i)`, which IS the
product-weight normalisation identity with the weights left uninstantiated.
What was genuinely absent was the **ℚ port of that one theorem** — `Rat` had
`prodRange`, `prodRange_shiftFront`, `sumMaps`, `sumMaps_congr`,
`sumMaps_mul_left`, `sumRange_mul_right`, every ingredient the `Int` proof
consumes, and not the theorem.

**So route (a) is not the expensive one, and it lands at ℚ rather than over
`AlgS.OrderedRing`.** ADR-1677 carries the two sizings: ~830 new lines and ten
declarations at ℚ with no new hypothesis on any downstream statement, against
≥ 2,090 at the generic layer plus `mulComm` as an explicit hypothesis on every
product-rule statement — the record ADR-1592 §2 deliberately built `Ring`-based,
and the four-factor regrouping `(F·G)·(f·g) = (F·f)·(G·g)` inside
`prodRange_mul` is exactly a commutativity step. Route (b) is 145 lines but
nothing can discharge its predicate, so it survives only as the statement
interface: `Rat.KIndependent` is the k-fold independence statement and
`Rat.kIndependent_prodWeight` is its witness.

**Ten declarations in `rat_prelude/product_space.rs`**, all axiom-free:
`prodRange_one`, `prodRange_mul`, `prodRange_sumRange_expand`, `prodWeight`,
`prodWeight_nonneg`, `prodWeight_sumMaps_one`, `expectationMaps`,
`KIndependent`, `kIndependent_prodWeight`, `sumMaps_one_of_kIndependent`. The
expansion does two jobs: at `c i := P i` it is the normalisation, and at
`c i k := f i k · P i k` it is, after one `prodRange_mul`, the **k-fold product
rule for expectations** `E[∏_{i<m} f_i] = ∏_{i<m} E_{P_i}[f_i]` — derived, not
assumed. `sumMaps_one_of_kIndependent` is the consequence proved from the
PREDICATE rather than from the construction: independence with normalised
marginals forces a normalised joint, so a downstream theorem may assume
`KIndependent` without separately assuming `W` is a distribution.

**What Hoeffding still needs**, named and not started: the marginal law
`expectationMaps_coord`, that the `j`-th coordinate of the product space is
distributed as `P j`. Without it `E[X_j]` on the product space cannot be
rewritten to a marginal expectation and the centring step of any concentration
argument cannot be stated. It follows from `kIndependent_prodWeight` at
`f_i := f` for `i = j` and `f_i := fun _ => 1` elsewhere, and the work is the
`prodRange` split at a distinguished index (a case analysis on `Nat.beq i j`;
`prodRange_congr` will not do it). After that the mgf bound is an exponential
and lands at `CReal`, through ADR-1612's transfer pair.

`fourth_moment.rs`'s module header ("independence is not expressible here —
there is no product space") and `binomial_rat.rs`'s two obstructions are now
stale on their first half. Neither file was edited by this lane.

Detail in
[ADR-1677](../../research/09-decisions/adr-1677-the-k-fold-product-space-already-exists-as-summaps-and-lands-at-rationals.md).

<!-- plan-section: landed-changes -->

| 2026-09-06 | `3eedfa2b0` | ADR-1677, the measured decision with both sizings. Records that the brief's "no product space" finding was a NAME search, and that searching for the STEP — a finite sum indexed by tuples — finds `Rat.sumMaps` (ADR-1543) and `Int.prodRange_sumRange_expand`. |
| 2026-09-06 | `5545a4f19` | `rat_prelude/product_space.rs`, ten declarations, plus `product_space_tests.rs`. The ten names registered at the END of `named()` in `rat_prelude_tests.rs`, which is the population `every_rat_declaration_is_checked_and_axiom_free` derives against. |
