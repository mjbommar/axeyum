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

**The mutation table, RUN not predicted.** Baseline in a private snapshot
first, as a positive control: `product_space` 7 passed, the every-declaration
sweep 1 passed.

| # | mutation | PREDICTED | RUN |
| --- | --- | --- | --- |
| M1 | `prodWeight` built as a SUM (`rprod_range` → `rsum_range` in `declare_prod_weight`) | kernel rejects `prodWeight_sumMaps_one` | kernel **REJECTED** at prelude build, `TypeMismatch { expected: 5137081, got: 3324873 }`; 7 of 7 `product_space` tests died, and the every-declaration sweep too |
| M2 | the normalisation hypothesis dropped from `prodWeight_sumMaps_one`'s type | kernel rejects | kernel **REJECTED**, `UnboundFVar { id: 16503 }`; 7 of 7 died, and the sweep |
| M3 | one registration guard deleted — `("prodWeight", …)` removed from `named()` | kernel admits; EXACTLY ONE test dies | **admitted**; `product_space` 7 of 7 still passed; `every_rat_declaration_is_checked_and_axiom_free` died alone, "absent from `named`" |
| M4 | `declare_prod_weight_nonneg` dropped from the assembly, name still interned | kernel admits; the toolkit test dies | **admitted**; exactly one of 7 died — `the_product_space_toolkit_is_axiom_free`, "was interned but never declared" — and **the every-declaration sweep PASSED** |
| M5 | `along` transposed (`c i (g i)` → `c (g i) i`) in the definition AND in every proof at once, since both read it | kernel rejects the expansion | kernel **REJECTED**, `TypeMismatch { 5136782 / 5136795 }`; 7 of 7 died, and the sweep |

**Two findings from that table, neither of them predicted.**

First: **three of five are kernel rejections, and that is not an accident of
these three choices.** Every `Definition` in this module appears in the
STATEMENT of a theorem whose proof is built from its literal shape, so a
change to any of them fails `add_declaration` before a test can look at a
value. M5 was constructed specifically to see whether a coordinated change —
one that moves the definition and every proof together — could get past the
gate, and it could not: `prodRange_sumRange_expand`'s `cons`/`shiftFront`
alignment pins which argument the point indexes. So the evaluation tests in
`product_space_tests.rs` are NOT what catches a wrong `prodWeight` in this
module; the kernel is. They are still worth their cost — they are what says
the number is 6 and not 5 or 4 — but the honest claim about them is "they
document and check the intended value", not "they are the guard".

Second, and this one is a gap in an EXISTING gate:
**`every_rat_declaration_is_checked_and_axiom_free` passed under M4.** That
sweep derives its population from the kernel environment and reports every
`Rat.*` `Definition`/`Theorem` that is LIVE and UNLISTED. A name that is
interned and never declared is invisible to it — it is not in the
environment, so there is nothing to be unlisted. The sweep guards one
direction only. `the_product_space_toolkit_is_axiom_free` (which looks each
name up in the environment and panics on a miss) is the only thing guarding
the other, and it is a per-module test that a new module could simply not
write. M3 and M4 are both "a registration guard was removed" and they are
caught by two DIFFERENT tests; neither would have caught the other's mutation.

`fourth_moment.rs`'s module header ("independence is not expressible here —
there is no product space") and `binomial_rat.rs`'s two obstructions are now
stale on their first half. Neither file was edited by this lane.

Detail in
[ADR-1677](../../research/09-decisions/adr-1677-the-k-fold-product-space-already-exists-as-summaps-and-lands-at-rationals.md).

<!-- plan-section: landed-changes -->

| 2026-09-06 | `3eedfa2b0` | ADR-1677, the measured decision with both sizings. Records that the brief's "no product space" finding was a NAME search, and that searching for the STEP — a finite sum indexed by tuples — finds `Rat.sumMaps` (ADR-1543) and `Int.prodRange_sumRange_expand`. |
| 2026-09-06 | `5545a4f19` | `rat_prelude/product_space.rs`, ten declarations, plus `product_space_tests.rs`. The ten names registered at the END of `named()` in `rat_prelude_tests.rs`, which is the population `every_rat_declaration_is_checked_and_axiom_free` derives against. |
| 2026-09-06 | `082a60a21` | `prodWeight_sumMaps_one` binds `∀ n P m`, not `∀ n m P` — the statement-shape test supplied the arguments in the wrong order and the kernel answered `TypeMismatch { got: ExprId(3) }`, a single-digit `got` meaning it wanted a SORT. Also regenerates `crates/axeyum-py/src/kernel/prelude_fields.rs`, which `check-merge-hygiene.sh` reported stale after `RatPrelude` gained a field; `cargo check --workspace --all-targets` exit 0 afterwards. |
| 2026-09-06 | `878f83e0b` | This status file. |
