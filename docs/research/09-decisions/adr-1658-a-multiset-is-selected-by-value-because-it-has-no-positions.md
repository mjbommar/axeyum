# ADR-1658: A multiset is selected by VALUE, because it has no positions

Status: accepted
Date: 2026-09-06
Index-summary: ADR-1624 named the blocker under Möbius inversion as "a multiset indexed by a `Nat → Bool` predicate", and described it as a product over the selected POSITIONS of the multiset's list representation. `Nat.Multiset` has no list — it is a multiplicity function plus a bound (ADR-1520) — so positions name nothing, and the selection lands by VALUE, over `[0, bound m)`, which is the index space `Nat.Subsets` already folds over. `Nat.Multiset.prodSel m s := prodRange (fun q => if s q then q ^ count m q else 1) (bound m)`, tied to a `Nat.Multiset.restrict` at the SAME bound so that `count_restrict` carries no side condition. The payoff is that `prodSel_injective` — two selections with the same product agree on the support — is `Nat.Multiset.count_eq_of_prod_eq` (uniqueness of prime factorization, already proved) read through one bridge theorem, with no new arithmetic. `prodSel_dvd_prod` gives the easy direction of the bijection. **Möbius inversion did NOT land, and neither did the bijection**: what is missing is surjectivity onto the divisors of a squarefree `n` and, separately, a sum-transfer law between two DIFFERENT index shapes (a `Nat` range and a `Nat → Bool` fold), which this prelude has for COUNTS over two `Nat` ranges (`countRange_bij`) and for nothing else. Two mutants were RUN; both were killed, both by the trusted gate rather than by the evaluation controls, which is itself the finding.
Index-status: accepted

## Context

Roadmap **W2-18**, second slice. The state
[ADR-1624](adr-1624-a-subset-is-a-predicate-because-the-split-law-has-to-be-refl.md)
handed over was precise about the blocker:

> the bijection "divisors of squarefree `n` ↔ subsets of its prime multiset"
> needs a multiset indexed by a `Nat → Bool` predicate — a transfer from
> `sumRangeIf` over `[0, n]` to the subset fold — and nothing indexes a multiset
> by a predicate.

The lane brief built on that and asked for
`Nat.Multiset.prodSel (m : Multiset) (s : Nat → Bool) : Nat`, "the product of
the elements at selected positions (by `Nat.rec` over the multiset's list
representation, position-indexed)".

**There is no list representation.** `Nat.Multiset`
([ADR-1520](adr-1520-a-multiplicity-function-is-a-multiset-and-uniqueness-was-a-representation-problem.md),
`nat_prelude/multiset.rs`) is

```text
inductive Nat.Multiset | mk : (Nat → Nat) → Nat → Nat.Multiset
Nat.Multiset.count m q := if q < bound m then raw m q else 0
```

— a multiplicity function together with a bound. Order is never represented
(that is the whole reason no `Quot.sound` appears anywhere in it and its axiom
footprint is empty), so "the `i`-th element" does not name anything, and a
position-indexed `prodSel` would first have to enumerate the support in
increasing order: a `nth`-of-support construction with its own correctness
theory. That is a development, not a definition.

## Decision

### 1. Select by value; the two index spaces already agree

`Nat.Multiset.prod` folds `prodRange (fun q => q ^ count m q) (bound m)`, i.e.
over `q ∈ [0, bound m)`. A subset of `[0, n)` in this prelude is exactly a
`Nat → Bool` (`Nat.Subsets.empty`/`insertAt`, ADR-1624). Those are the same
index space, so:

```text
Nat.Multiset.prodSel m s := prodRange (fun q => if s q then q ^ count m q
                                                else 1) (bound m)
```

For the intended consumer this is the same object the brief asked for: for a
squarefree `n` every `count` is `0` or `1`, so a selection of values IS a
selection of prime factors. It costs no enumeration of the support, and
`prodSel_all` is `Eq.refl`.

The cost, stated plainly so nobody discovers it later: `prodSel` is **not
injective in `s` over all predicates**, because a `q` outside the support
contributes `q ^ 0 = 1` whichever way `s` decides it. Every theorem below that
mentions injectivity is therefore relativized to the support, and
`prod_sel_injectivity_cannot_reach_outside_the_support` (`multiset_select_tests.rs`)
exhibits the witnesses: `{3}` has bound `4`, and `(· = 3)` and
`insertAt 2 (· = 3)` have the same `prodSel` while disagreeing at `2`, which is
INSIDE the bound. The hypothesis is necessary, not defensive.

### 2. `restrict` keeps the SAME bound, and goes through `raw`

```text
Nat.Multiset.restrict m s := mk (fun q => if s q then raw m q else 0) (bound m)
```

Keeping the bound is what makes

```text
Nat.Multiset.count_restrict : count (restrict m s) q = if s q then count m q else 0
```

**unconditional** — no `q < bound m` side condition, so no consumer ever
threads one. Going through `raw` rather than `count` is what makes its proof
one line of case analysis: both sides then unfold to the same two nested
`Bool.rec`s over `ble (succ q) (bound m)` and `s q` in the opposite order, and
a single `Bool.rec` on `s q` closes it — `false` branch
`Nat.bool_select_nat_same`, `true` branch `Eq.refl`. Through `count` the
statement would still be true and the proof would need a `q < bound m` split.

### 3. The bridge theorem is the whole point

```text
Nat.Multiset.prodSel_eq_prod_restrict : prodSel m s = prod (restrict m s)
```

The selection fold IS a multiset product. That single theorem turns
`Nat.Multiset.count_eq_of_prod_eq` — uniqueness of prime factorization, proved
in `multiset.rs` — into

```text
Nat.Multiset.prodSel_injective :
  (∀ q, 0 < count m q → prime q) → prodSel m s = prodSel m t →
  ∀ q, 0 < count m q → s q = t q
```

with **no new arithmetic**: the prime-support hypothesis transfers across
`restrict` by `count_restrict_pos`, and `Nat.bool_select_nat_inj_of_pos` reads
the `Bool` back out of the resulting count equation. Defining `prodSel`
directly as a `prodRange` and then proving injectivity from scratch would have
been a fresh induction over the fold; routing it through a multiset makes it a
corollary.

The reverse framing is what this ADR wants recorded as reusable: **when a new
fold has an existing theory it could be an instance of, spend the one theorem
that says so before proving anything else about it.**

### 4. Two general laws had to be declared, and neither mentions `Multiset`

- `Nat.mul_dvd_mul : dvd a b → dvd c e → dvd (a*c) (b*e)`. The prelude had
  `dvd_mul`, `dvd_mul_right_of_dvd` and `dvd_trans` but **nothing multiplying
  two divisibilities**, so a pointwise divisibility could not be pushed under a
  product fold at all.
- `Nat.prodRange_dvd_prodRange : (∀ i, dvd (f i) (g i)) →
  dvd (prodRange f n) (prodRange g n)`.

`Nat.Multiset.prodSel_dvd_prod` is then hypothesis-free: every selection names
a divisor of the whole product. That is the easy direction of ADR-1624's
bijection.

## What did NOT land, and what it would cost

Möbius inversion did not land, and neither did the bijection. Being specific
about which piece is missing is the point of writing this down.

`Nat.moebiusPos`/`moebiusNeg`/`moebiusAbs` already exist
([ADR-1619](adr-1619-the-divisor-map-is-a-permutation-only-if-it-fixes-the-non-divisors.md),
`arith_functions_family.rs`) as a graded pair, so deliverable 3's *definition*
was already present and did not need redoing; what is missing is
`Σ_{d∣n} μ(d) = 0` for `n > 1`, and Möbius inversion on top of it.

**Missing piece A — surjectivity.** `prodSel_dvd_prod` says every selection is
a divisor; the converse, that every divisor of a squarefree `n` IS a `prodSel`,
needs `d ∣ prod m → ∀ q, count (factorization d) q ≤ count m q`, i.e. a
divisor-to-valuation comparison. The prelude has the two halves of the
valuation (`pow_count_dvd_prod`, `not_pow_succ_count_dvd_prod`) and
`exponent_unique_of_exact_dvd`, so this is a real but bounded induction — call
it one lane, mostly in `multiset.rs`'s idiom.

**Missing piece B — the sum transfer, which is the harder one.** Even with (A),
`sumRangeIf (· ∣ n) f (n+1) = sumSubsets (bound m) (fun s => f (prodSel m s))`
relates two folds over **different index shapes**: a `Nat` range and a
`Nat → Bool` recursion on the width. This prelude's cross-bound law
`Nat.countRange_bij` is for COUNTS over two `Nat` RANGES. There is no
`sumRange` twin of it, and no range-to-subset twin of anything. Both would be
new primitives, and the second has no analogue anywhere in the prelude to copy.

A consequence worth flagging for whoever picks this up: with `prodSel`
value-indexed and `sumSubsets` folding over `[0, k)`, the natural width is
`bound m`, and `sumSubsets (bound m)` enumerates `2^(bound m)` predicates while
a squarefree `n` has only `2^(number of distinct primes)` divisors. The counts
do not match, and the gap is exactly the values below the bound that are not in
the support. So either the transfer restricts the enumeration to supported
predicates, or the support does after all have to be enumerated into
`[0, k)` — which is the position-indexing this ADR declined, arriving from the
other side. **That choice is the next decision, and it is not made here.**

An alternative route to `Σ_{d∣n} μ(d) = 0` that avoids the bijection entirely
was considered and is recorded so it is not re-derived: the `p`-adic parity
involution `T(k) = if p²∣k then k else if p∣k then k/p else k*p` at
`p = minFac n` is an involution on all of `Nat`, maps divisors of `n` to
divisors of `n`, and flips the parity of `Ω` on the squarefree ones — so
`Nat.sumRange_permute` would apply directly. It needs `Squarefree (k*p) ↔
Squarefree k ∧ p ∤ k` and `omegaCount (k*p) = omegaCount k + 1`, neither of
which exists. It is not obviously cheaper than (A)+(B), and it does not produce
the bijection, which W2-19 and general inclusion–exclusion also want.

## Consequences

- `Nat.Multiset.prodSel` is by VALUE. Anything that needs positions must
  enumerate the support first, and this ADR does not do that.
- Injectivity is relativized to the support and cannot be strengthened at this
  carrier; the test named above is the proof of that, not a caveat.
- Fourteen new names, all registered in
  `nat_prelude_tests::definition_names`/`theorem_names`, so the
  every-declaration sweep covers them; two of them (`mul_dvd_mul`,
  `prodRange_dvd_prodRange`) are general and belong to no carrier.
- Three facts recorded: `F:nat-multiset-prod-sel-injective`,
  `F:nat-multiset-prod-sel-dvd-prod`, `F:nat-mul-dvd-mul`.

## Mutation evidence, and what it actually showed

Both mutants named in the brief's spirit were **RUN**, from a clean tree, in
the foreground, and restored byte-for-byte (`git status` empty afterwards).

| Mutant | Site | Predicted | RUN result |
| --- | --- | --- | --- |
| A: `prodSel` reads the wrong position | `select_factor`, `s q` → `s (succ q)` | the `≠ 1` control in `prod_sel_evaluates_the_two_single_value_selections` (an off-by-one read gives `1`, since `count {2,2,3} 1 = 0`) | killed, 6 of 6 tests in `multiset_select_tests` failed, exit 101 — but by a **kernel rejection** at the named step `prodSel laws`, so the prelude never built and the evaluation control never ran |
| B: `prodSel` ignores the selection | `select_factor`, unselected branch `1` → `q ^ count m q` | the `≠ 12` control in the same test | killed, 6 of 6 failed, exit 101 — again by a **kernel rejection** at `prodSel laws` |

The finding is not "two mutants died". It is that **both died through the same
shared check** — `prodSel_eq_prod_restrict`'s pointwise obligation — and
neither evaluation control was reached. That is the exact shape CLAUDE.md warns
about (six of seven guards in one suite removable with everything still green).
Two things follow, and both are stated rather than assumed away:

1. The theorem layer here really does pin both definitions at the value level:
   `prodSel_all`, `prodSel_empty` and `prodSel_eq_prod_restrict` between them
   constrain `prodSel` at every predicate, and `count_restrict` constrains
   `restrict` at every value. Every single-site value mutation attempted was
   caught before a test ran.
2. Therefore the evaluation tests are, today, **redundant with the kernel** for
   these two definitions — and they are kept anyway, because that redundancy is
   a property of the current theorem set, not of the definitions, and a future
   lane that weakens or generalizes `prodSel_eq_prod_restrict` would remove it
   silently. No mutant was found that the kernel admits and the tests catch;
   that absence is reported, not papered over.
