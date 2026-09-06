# ADR-1677: the k-fold product index range already exists as `Rat.sumMaps`, so the product space is a construction at ℚ, not a hypothesis over `AlgS.OrderedRing`

Status: accepted
Date: 2026-09-06
Lane: `product-probability`

Index-summary: The lane brief asked for a measured choice between (a) building
a product of index ranges with a product weight and proving it is again a
distribution, and (b) assuming the k-fold product rule the way `Independent`
already assumes the two-fold one. The re-measurement changes the terms of the
choice. The brief's finding — "no `prod`/`joint`-named declaration in `Rat`,
`AlgS` or `IntSpace` is a product space" — is correct **about names** and
wrong about structure: `Rat.sumMaps m n F` (ADR-1543, built for Cauchy–Binet)
is a finite sum indexed by the whole function space `[0,m) → [0,n)`, which IS
the k-fold product index range, and `Int.prodRange_sumRange_expand` is the
generalized distributive law `∏_{i<m} ∑_{k<n} c i k = ∑_g ∏_{i<m} c i (g i)`,
which IS the product-weight normalisation identity with the weights left
uninstantiated. Route (a) is therefore far cheaper than the brief priced it,
and it is cheaper **at ℚ** than at the generic layer. **Decision: route (a),
at ℚ.** Measured: ℚ costs one ported theorem (203 lines) plus nine new
declarations, and needs no new hypothesis on any downstream statement;
`AlgS.OrderedRing` would first need `sumMaps` and its five support lemmas
ported into setoid form (1,256 lines at ℚ today, and every `Eq` rewrite
becomes an explicit congruence step) **and** would carry `mulComm` as an
explicit hypothesis on every product-rule statement, because ADR-1592 §2
deliberately built the record `Ring`-based. Route (b) is rejected as the
spine but kept as the *interface*: `Rat.KIndependent` is declared as a
predicate, and `Rat.kIndependent_prodWeight` proves the constructed product
weight satisfies it — a k-fold independence hypothesis that nothing can
discharge is an axiom in disguise, and this is what stops it being one.

Index-status: accepted

## Context

`rat_prelude/probability.rs` (54 axiom-free declarations at ℚ) and
`rat_prelude/probability_s.rs` (29 over `AlgS.OrderedRing`, ADR-1616) are one
weight function `p : Nat → Rat` over one index range `[0, n)`. `Independent A
B p n := E[A·B] = E[A]·E[B]` is a **definition**: the two-fold product rule is
assumed at the point of use, never derived, because there is no second
probability space to take a product with. Everything past two factors —
Hoeffding, joint laws, the variance of a sum of `k` independent variables —
stops there.

The brief's measurement asked whether any product structure existed and
answered no, on a name search for `prod`/`joint` across `Rat` (543
declarations), `AlgS` (390) and `IntSpace` (98), whose only hits were the five
`Rat.prodRange*` names built for determinants.

## The measurement that decides it

**Search for the step, not the name** (contributor guide,
`finding-existing-lemmas.md`). The step a product space needs is: *a finite
sum indexed by tuples*. Searching for that finds it:

| declaration | where | what it is |
| --- | --- | --- |
| `Rat.sumMaps : Nat → Nat → ((Nat → Nat) → Rat) → Rat` | `rat_prelude/sum_maps.rs` (ADR-1543) | the sum over every map `[0,m) → [0,n)` — i.e. over the k-fold product index set, with `m` factors of size `n` |
| `Rat.sumMaps_zero` / `_succ` / `_congr` / `_mul_left` / `_mul_right` | same | its defining equations and the two constant-pulls |
| `Rat.prodRange` / `_zero` / `_succ` / `_shiftFront` / `_congr` | same | the k-fold product `∏_{i<m}` |
| `Int.prodRange_sumRange_expand` | `int_prelude/sum_maps.rs`, 203 lines | `∏_{i<m} (∑_{k<n} c i k) = ∑_g ∏_{i<m} c i (g i)` |

The last row is the whole normalisation proof. Instantiate `c i := p i` (the
`i`-th factor's weight) and it reads: if every marginal sums to one, the
product weight `W g = ∏_{i<m} p i (g i)` sums to one over the product index
set. Instantiate `c i k := f i k * p i k` and it reads, after one
`prodRange_mul`, `E[∏ f_i] = ∏ E[f_i]` — the k-fold product rule for
expectations, **derived**.

**What is genuinely absent** is the ℚ port of that one theorem. `Rat` has
`prodRange`, `sumMaps`, `sumMaps_congr`, `sumMaps_mul_left` and
`prodRange_shiftFront` — every ingredient the `Int` proof consumes — and not
`prodRange_sumRange_expand` itself. Verified in-tree:
`Int.prod_range_sum_range_expand` is a field of `IntPrelude`, and
`RatPrelude`'s "function-space aggregates (ADR-1543)" block declares eleven
names, none of them the expansion.

## The two sizings the brief asked for

Route (a), **at ℚ** — the chosen one:

| piece | new lines | note |
| --- | --- | --- |
| `Rat.prodRange_one` | ~45 | `∏_{i<n} 1 = 1`, induction |
| `Rat.prodRange_mul` | ~90 | `∏ (f·g) = (∏f)·(∏g)`, induction; needs `mul_comm`, free at ℚ |
| `Rat.prodRange_sumRange_expand` | ~205 | port of the `Int` original, same shape |
| `Rat.prodWeight` (Definition) | ~40 | `fun P m g => ∏_{i<m} P i (g i)` |
| `Rat.prodWeight_nonneg` | ~75 | induction over `mul_nonneg` |
| `Rat.prodWeight_sumMaps_one` | ~70 | the normalisation — expand, then `prodRange_congr` to the constant one |
| `Rat.expectationMaps` (Definition) | ~45 | `sumMaps m n (fun g => F g * W g)` |
| `Rat.KIndependent` (Definition) | ~65 | the k-fold independence statement |
| `Rat.kIndependent_prodWeight` | ~115 | the product weight satisfies it |
| `Rat.sumMaps_one_of_kIndependent` | ~80 | consequence, from the predicate |
| **total** | **~830** | **10 declarations, 0 new hypotheses downstream** |

Route (a), **at `AlgS.OrderedRing`** — rejected:

| piece | new lines | note |
| --- | --- | --- |
| `sumMaps` + 5 support lemmas, in setoid form | ≥ 1,256 | that is the ℚ file's current size; the setoid rebuild is strictly larger, because every `Eq`-flavored rewrite becomes an explicit `addCongr`/`mulCongr` step — `probability_s.rs`'s own `declare_sum_range_congr` note records exactly this price for the one-dimensional sum |
| everything in the ℚ column | ~830 | |
| `mulComm` as an explicit hypothesis | 0 lines, but on **every** product-rule statement | `AlgS.OrderedRing` has no `mulComm` (ADR-1592 §2 built the record `Ring`-based so `ofAlg` would type-check) and no projection to `AlgS.CommRing`; `probability_s.rs`'s own `covariance` note records that the centred/computational asymmetry is load-bearing for exactly this reason |
| **total** | **≥ 2,090 + a hypothesis on every statement** | |

So the brief's "prefer the generic `AlgS.OrderedRing` layer if the cost is
comparable" is answered by measurement: **it is not comparable, it is 2.5x
plus a hypothesis**, and the reason is structural rather than incidental —
the generic layer was built from `linarith`'s field set, which has no
multiplicative commutativity and no function-space aggregate.

Route (b), the hypothesis:

| piece | new lines | note |
| --- | --- | --- |
| `Rat.KIndependent` (Definition) | ~65 | the same predicate |
| one consequence | ~80 | |
| **total** | **~145** | **but nothing can discharge the predicate** |

Route (b) is 145 lines against 830. The 685-line difference buys exactly one
thing, and it is the thing that matters here: `kIndependent_prodWeight` is a
**witness**. Without it `KIndependent` is a hypothesis with no known
inhabitant in this development, which is the shape ADR-0601 and the
contributor guide both name as the failure mode — a checker that cannot fail,
a hypothesis that cannot be discharged. With it, `KIndependent` is a
predicate with a constructed model, and route (b)'s interface survives as the
statement form downstream theorems quantify over.

## Decision

1. **Route (a), at ℚ.** The product index range is `Rat.sumMaps m n`, the
   product weight is `Rat.prodWeight P m`, and the normalisation is
   `Rat.prodWeight_sumMaps_one`, proved through the ported
   `Rat.prodRange_sumRange_expand`.
2. `Rat.KIndependent m n P W` is declared as the k-fold independence
   statement — route (b)'s interface — and `Rat.kIndependent_prodWeight`
   proves route (a)'s construction satisfies it. This is the only reason both
   appear: the predicate is the statement form, the construction is its
   witness. No second carrier is built.
3. Nothing is added to `probability_s.rs` or to `AlgS.OrderedRing`. The
   generic layer keeps the two-fold `Independent` it has.

## Consequences

- The two-fold `Independent` in `probability.rs` and `probability_s.rs` is
  unchanged and still a definition. It is not a special case of
  `KIndependent`: it is stated over ONE index range with two variables, and
  `KIndependent` is stated over the product of `m` ranges. Relating them needs
  the marginal law (see below) and is not attempted here.
- The new declarations live in `rat_prelude/product_space.rs`, are registered
  at the END of `named()` in `rat_prelude_tests.rs`, and are covered by
  `every_rat_declaration_is_checked_and_axiom_free`, which derives its
  population from the kernel environment rather than from a literal list.
- **What Hoeffding still needs**, in one paragraph, not started here: the
  missing lemma is the **marginal law**, `Rat.expectationMaps_coord : j < m →
  (∀ i, sumRange (P i) n = 1) → expectationMaps m n (fun g => f (g j))
  (prodWeight P m) = expectation f (P j) n` — that the `j`-th coordinate of
  the product space is distributed as `P j`. Without it, `E[X_j]` on the
  product space cannot be rewritten to a marginal expectation, so the centring
  step `X_j − E[X_j]` of any concentration argument cannot even be stated in
  the shelf's vocabulary. It follows from `kIndependent_prodWeight` by taking
  `f_i := f` at `i = j` and `f_i := fun _ => 1` elsewhere, which needs a
  `prodRange` split at a distinguished index (`prodRange_congr` will not do
  it; the case analysis on `Nat.beq i j` is the work). After that, Hoeffding
  needs the mgf bound `E[e^{tX}] ≤ e^{t²(b−a)²/8}` for a bounded centred
  variable, which is an exponential and therefore lands at `CReal`, not at ℚ
  — a second, larger step that ADR-1612's transfer pair
  (`AlgS.OrderedRing.expectation_map`) is the right route for.
