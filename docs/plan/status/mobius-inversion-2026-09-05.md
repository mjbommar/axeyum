# Lane: mobius-inversion — a multiset selected by a predicate, and the injective half of the divisors ↔ subsets bijection

<!-- plan-section: lane-status -->

**Your lane's block (`PARTIAL — deliverable 1 in full, deliverable 2 by half,
deliverable 3 not at all`, mobius-inversion, 2026-09-06).** Roadmap **W2-18**,
second slice. ADR
[1658](../../research/09-decisions/adr-1658-a-multiset-is-selected-by-value-because-it-has-no-positions.md).

The brief asked for a multiset selected by a `Nat → Bool` predicate over the
multiset's *list positions*. **`Nat.Multiset` has no list** — it is a
multiplicity function plus a bound (ADR-1520) — so the selection landed by
VALUE, over `[0, bound m)`, which is the index space `Nat.Subsets` already folds
over. The deviation, its cost, and the one place it bites are ADR-1658 §1.

**Landed:** 14 declarations, all axiom-free, all registered in
`nat_prelude_tests::definition_names`/`theorem_names` (so the every-declaration
sweep covers them). Definitions `Nat.Multiset.restrict` and
`Nat.Multiset.prodSel`; theorems `Nat.mul_dvd_mul`,
`Nat.prodRange_dvd_prodRange`, `Nat.bool_select_nat_inj_of_pos`, and
`Nat.Multiset.`{`bound_restrict`, `count_restrict`, `count_restrict_pos`,
`prodSel_eq_prod_restrict`, `prodSel_all`, `prodSel_empty`, `prodSel_congr`,
`prodSel_dvd_prod`, `prodSel_injective`}.

The two that matter are `prodSel_dvd_prod` (every selection is a divisor of the
whole product — no hypotheses at all) and `prodSel_injective` (two selections
with equal products agree at every value the multiset contains). Together they
are an injection from selections into the divisors: the injective half of
ADR-1624's bijection. `prodSel_injective` cost **no new arithmetic** — it is
`Nat.Multiset.count_eq_of_prod_eq` (uniqueness of prime factorization, already
proved) read through the one bridge theorem `prodSel_eq_prod_restrict`, which
says the selection fold IS a multiset product.

Two of the fourteen are general and belong to no carrier: the prelude had
`Nat.dvd_mul`, `Nat.dvd_mul_right_of_dvd` and `Nat.dvd_trans` but **nothing
multiplying two divisibilities**, so a pointwise divisibility could not be
pushed under a product fold at all.

**Not attempted or not reached, and this is the handoff:**

- **Surjectivity** — every divisor of a squarefree `n` IS a `prodSel`. Needs
  `d ∣ prod m → ∀ q, count (factorization d) q ≤ count m q`. Bounded work; the
  valuation halves it needs (`pow_count_dvd_prod`,
  `not_pow_succ_count_dvd_prod`, `exponent_unique_of_exact_dvd`) are already in
  `multiset.rs`.
- **The sum transfer, which is the expensive half.**
  `sumRangeIf (· ∣ n) f (n+1) = sumSubsets … (fun s => f (prodSel m s))` relates
  two DIFFERENT index shapes — a `Nat` range and a `Nat → Bool` recursion on the
  width. `Nat.countRange_bij` is the cross-bound law for COUNTS over two `Nat`
  RANGES; there is no `sumRange` twin and no range-to-subset twin of anything,
  so both would be new primitives. It also carries an unmade decision: the
  widths do not match, because `sumSubsets (bound m)` enumerates
  `2^(bound m)` predicates while a squarefree `n` has `2^(distinct primes)`
  divisors, and closing that gap is either a restriction to supported predicates
  or the support enumeration this lane declined. ADR-1658 states it; it does not
  decide it.
- **`Σ_{d∣n} μ(d) = 0` and Möbius inversion.** `Nat.moebiusPos`/`moebiusNeg`/
  `moebiusAbs` already existed (ADR-1619), so the *definition* was never the
  gap. `Nat.dirichlet_assoc` was NOT attempted and remains absent.
- An alternative route that avoids the bijection entirely — the `p`-adic parity
  involution `T(k) = if p²∣k then k else if p∣k then k/p else k*p` at
  `p = minFac n`, which `Nat.sumRange_permute` would consume directly — is
  written into ADR-1658 so it is not re-derived. It needs
  `Squarefree (k*p) ↔ Squarefree k ∧ p ∤ k` and
  `omegaCount (k*p) = omegaCount k + 1`, neither of which exists.

**Mutation: the result is the finding.** Two mutants RUN from a clean tree in
the foreground, restored byte-for-byte. Both killed 6 of 6 tests in
`multiset_select_tests` (exit 101) — but both by a **kernel rejection** at the
same named step (`prodSel laws`), so the prelude never built and the evaluation
controls never ran. Both guards reject through one shared check. No mutant was
found that the kernel admits and the tests catch; that absence is reported
rather than smoothed over.

**Facts:** `F:nat-multiset-prod-sel-injective`,
`F:nat-multiset-prod-sel-dvd-prod`, `F:nat-mul-dvd-mul` — all `proved`,
`axiom_footprint: []`, three evidence rows each (full-rendered-type pin,
footprint, evaluation). `depends_on` edges were completed by
`scripts/check-fact-depends-derived.py --fix`, which derives them from the proof
term rather than from what the author remembered.

**Partition check:** `Nat.Multiset`, `prodSel`, `mul_dvd_mul` and `prodRange`
appear in NONE of `artifacts/structural-index/held-out-exclusion-manifest.json`,
`artifacts/autogenesis/nursery-v2-extension.json`, or
`corpus/glaurung-proof-populations/`. Positive control: both files exist and are
non-empty (`ml430` occurs 1112 times in the nursery extension) and every
held-out id is `F:ml430-int-*`. No held-out family was touched.

<!-- plan-section: landed-changes -->

| 2026-09-06 | mobius-inversion | `Nat.Multiset.restrict`/`prodSel` + 12 theorems (`multiset_select.rs`), registered in the every-declaration sweep — `236c37763` |
| 2026-09-06 | mobius-inversion | the `symm` in `prodSel_eq_prod_restrict` had its endpoints swapped, which is what made the previous commit unable to build the prelude — `1718bad75` |
| 2026-09-06 | mobius-inversion | 6 tests (`multiset_select_tests.rs`): evaluation with named wrong values, both bridge theorems instantiated, the injectivity NECESSITY control, and contains-then-footprint over all 14 names — `2e342d998` |
| 2026-09-06 | mobius-inversion | ADR-1658 and three facts; the bijection's surjective half and the range-to-subset sum transfer sized, not landed |
