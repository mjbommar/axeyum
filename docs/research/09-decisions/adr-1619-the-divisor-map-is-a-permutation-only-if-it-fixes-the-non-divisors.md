# ADR-1619: The divisor map is a permutation only if it fixes the non-divisors

Status: accepted
Date: 2026-09-04
Index-summary: `Nat.sumDivisorsBy f n` is the divisor aggregate taking its SUMMAND as an argument (`Nat.sumDivisors` was the `f = id` case, hard-wired), and `Nat.sumDivisorsBy_reindex` is the `d ↦ n/d` reindexing ADR-1598 named as its blocker. The map that reindexes is NOT `d ↦ n/d` — that is not injective on `[0,n]` (at `n = 6` it sends 4, 5 and 6 all to 1) — but `Nat.divisorFlip n d := if d ∣ n then n/d else d`, which fixes the non-divisors and is therefore a genuine involution, hence injective with no bound at all. `Nat.dirichlet_comm` is then a three-line corollary. Möbius lands as a graded `Nat`-valued PAIR; Möbius INVERSION and n-set inclusion-exclusion did NOT land, and the remaining obstruction to each is named.
Index-status: accepted

## Context

Roadmap **W2-18** (multiplicative arithmetic functions as a family) and
**W2-19** (general inclusion-exclusion). Two prior lanes had left precise
handoffs:

- [`docs/math-department/01-number-theory.md`](../../math-department/01-number-theory.md)'s
  progress log, on the primitive-roots lane: *"Existence of a primitive root
  mod a prime did not land, and the obstruction is precise: the counting route
  needs `∑_{d∣n} φ(d) = n`, hence a divisor-set aggregate and the `d ↦ n/d`
  reindexing of a predicate-restricted sum, neither of which exists."*
- The same file's audit row A7: totient multiplicativity was **already proved**
  in the general form (`Nat.totient_mul_of_coprime`), against a review that
  denied it.

The first claim was half right and the correction matters. A divisor-set
aggregate DID exist — `Nat.sumDivisors` (`perfect.rs`, 2026) — but only in a
**monomorphic** form: the summand is hard-wired to `fun d => d`, so it can
express `σ` and nothing else. The reindexing genuinely did not exist.

## Decision

### 1. The aggregate takes its summand as an argument; `σ` becomes an instance

`crates/axeyum-lean-kernel/src/nat_prelude/arith_functions.rs`:

```text
Nat.dvdB d n          := Nat.beq (Nat.mod n d) 0
Nat.sumDivisorsBy f n := Nat.sumRangeIf (fun k => dvdB k n) f (succ n)
Nat.numDivisors n     := sumDivisorsBy (fun _ => 1) n
```

`Nat.sumRangeIf` (`subset_sum.rs`) already supplied the predicate-restricted
fold, so the aggregate is one line. `Nat.dvdB` is deliberately the SAME
expression `Nat.sumDivisors` already inlined, which is why

```text
Nat.sumDivisorsBy_eq_sumDivisors : ∀ n, sumDivisorsBy (fun k => k) n = sumDivisors n
```

is closed by `Eq.refl` — the new aggregate does not replace `σ`, it contains
it, delta for delta.

`dvdB 0 n` is `beq n 0`, because `Nat.mod n 0 = n`. So `0` counts as a divisor
of `0` alone, which is exactly `Nat.dvd`'s own convention (`dvd a n := ∃ q,
n = a * q`), and `Nat.dvd_of_dvdB` therefore needs no positivity hypothesis.

### 2. The map that reindexes is not `d ↦ n/d`

This is the finding. `Nat.sumRange_permute` (`sum_range_permute.rs`) is the
engine — a sum over `[0,n)` is invariant under any `injectiveOn`/`mapsInto`
self-map — and the obvious candidate `fun k => n / k` **cannot be fed to it**.
It is not injective on `[0, n]`: at `n = 6` it sends `4`, `5` and `6` all to
`1`.

The permutation is the one that moves only the divisors:

```text
Nat.divisorFlip n d := bool_select_nat (dvdB d n) (n / d) d
```

Two consequences follow from fixing the non-divisors, and both are load-bearing:

- **It is a genuine involution, not merely an involution on the divisor set.**
  A divisor goes to its cofactor, which is again a divisor, and comes back
  (`Nat.div_div_self_of_dvd : 0 < n → d ∣ n → n / (n / d) = d`); a non-divisor
  goes to itself twice. So `Nat.divisorFlip_involutive` is stated `∀ n, 0 < n →
  ∀ k, flip n (flip n k) = k`, with the `∀ k` INSIDE the positivity so the
  conclusion is the single term the involution-to-injectivity argument
  consumes.
- **Injectivity therefore carries no bound.** `Nat.divisorFlip_injectiveOn`
  quantifies over an ARBITRARY range `m`. Only `Nat.divisorFlip_mapsInto`
  mentions `succ n`, and that is a range fact, not an injectivity fact.

Positivity is load-bearing in both halves: at `n = 0` every `d` divides,
`0 / d = 0`, and the map collapses onto `0`.

The deliverable:

```text
Nat.sumDivisorsBy_reindex : ∀ (f : Nat → Nat) (n : Nat), 0 < n →
  sumDivisorsBy f n = sumDivisorsBy (fun d => f (n / d)) n
```

`sumRange_permute` at `σ := divisorFlip n`, then one `sumRange_congr` whose
pointwise step is a `dvdB k n` dichotomy: at a divisor both sides are
`f (n/k)`, at a non-divisor both are `0`.

### 3. The convolution's commutativity is a corollary, not an argument

`crates/axeyum-lean-kernel/src/nat_prelude/arith_functions_family.rs`:

```text
Nat.IsMultiplicative f := ∀ a b, gcd a b = 1 → f (a*b) = f a * f b
Nat.dirichlet f g n    := sumDivisorsBy (fun d => f d * g (n / d)) n
```

`Nat.dirichlet_comm : 0 < n → dirichlet f g n = dirichlet g f n` is three
steps and no new idea: reindex, replace `n/(n/d)` by `d` at every divisor,
commute the product. That is the return on having built §2 first.

The middle step needs a congruence bounded **by divisibility**, because
`n/(n/d) = d` is false off the divisor set:

```text
Nat.sumDivisorsBy_congr : (∀ d, dvdB d n = true → f d = g d) →
  sumDivisorsBy f n = sumDivisorsBy g n
```

The unconditional `Nat.sumRange_congr` cannot state that hypothesis, which is
why this is a separate lemma rather than a direct application.

Coprimality is spelled `Eq (gcd a b) 1` and not `Nat.Coprime`, because there is
no `Nat.Coprime` constant in this prelude (`shape_search --name Nat.Coprime`
returns `ABSENT` at `declarations=2857`) and `Eq (gcd a b) 1` is what the
existing `Nat.totient_mul_of_coprime` already uses. `IsMultiplicative` is
therefore inhabited immediately: `Nat.isMultiplicative_totient` is that
theorem, repackaged — the audit's row A7 turned into a member of the family
rather than a standalone.

### 4. Möbius lands as a graded pair (ADR-0603 shape)

`μ` takes values in `{-1, 0, 1}` and `Nat` has no negatives. Rather than move
the whole aggregate to `Int` — which would have meant a parallel `Int.sumRange`
toolkit that does not exist — `μ` lands as two `Nat`-valued halves:

```text
Nat.omegaCount n := Nat.Multiset.card (Nat.factorization n)
Nat.moebiusAbs n := if Squarefree n then 1 else 0
Nat.moebiusPos n := if Squarefree n then (if Ω(n) even then 1 else 0) else 0
Nat.moebiusNeg n := if Squarefree n then (if Ω(n) even then 0 else 1) else 0
```

with the two laws that make the pair behave as one signed value:
`moebiusPos n + moebiusNeg n = moebiusAbs n` and
`moebiusPos n * moebiusNeg n = 0`.

Both constants it reads already existed: `Squarefree` (`squarefree.rs`, at the
**bare root namespace**, not `Nat.squarefree`) and `Nat.factorization` /
`Nat.Multiset.card`. `Ω` (with multiplicity) rather than `ω` (distinct) is
harmless here because the two agree exactly on the squarefree numbers, which is
the only place the definitions read it.

## What did not land, and why

Stated precisely so the next lane does not re-derive the obstruction.

- **Möbius inversion.** It needs `∑_{d ∣ n} μ(d) = [n = 1]` — over the graded
  pair, `∑_{d∣n} moebiusPos d = ∑_{d∣n} moebiusNeg d` for `n > 1`. The standard
  proof puts the divisors of the squarefree part of `n` in bijection with the
  SUBSETS of its prime-factor set and reads the alternating sum off the binomial
  theorem. `Nat.Finset.decode`/`existsSubset_of_search` (ADR-1614) supplies the
  subset enumeration, but the bijection *divisors of a squarefree `n` ↔ subsets
  of its prime factors* does not exist and is not a corollary of anything in
  this ADR. That bijection is the next lane's unit of work; the reindexing here
  does not help with it, because it permutes the divisor set rather than
  describing it.
- **`∑_{d∣n} φ(d) = n`, hence primitive-root existence (ADR-1598).** The
  reindexing that lane named IS now present, and its "neither of which exists"
  is closed. What remains is the OTHER half of the counting route: the
  classification of `[0,n)` by `gcd k n`, i.e. that the elements of gcd exactly
  `n/d` are in bijection with the totatives of `d`. That is a separate
  construction and this lane did not attempt it. **Do not read this ADR as
  unblocking ADR-1598 outright** — it removes one of the two named
  prerequisites.
- **W2-19, general inclusion-exclusion.** Not started. The subset enumeration
  (ADR-1614) is there and the two-set case (`countRange_union_add_inter`) is
  there; what is missing is a sum INDEXED BY SUBSETS, which needs
  `sumRange (fun code => ...) (2^n)` together with the parity of
  `Nat.Finset.card (decode n code)`. That is a well-defined next slice and it
  is independent of everything above.

## Consequences

- 29 declarations across two files, every axiom footprint empty.
- `Nat.sumDivisors` is unchanged and now provably an instance of the aggregate,
  so `perfect.rs`'s existing results are untouched.
- `Nat.div_div_self_of_dvd` is worth naming separately: it is the cofactor
  law, it is what makes the involution work, and it is the kind of lemma that
  gets re-derived inline.
- **A process note that is not about mathematics.** One rejected declaration
  fails the whole shared `build_nat_prelude`, and the error is
  `TypeMismatch { expected: ExprId(1704807), got: ExprId(1704813) }` — which
  names neither the declaration nor the terms. `declare_arith_functions_family_all`
  therefore reports the rejected step BY NAME and renders the mismatch. It
  replaced a bisect on the first rejection this lane hit, and the pattern costs
  nothing.

## Evidence

- `crates/axeyum-lean-kernel/src/nat_prelude/arith_functions.rs` (15
  declarations) and `arith_functions_family.rs` (14).
- `arith_functions_tests.rs` (12 tests) and `arith_functions_family_tests.rs`
  (9). Every definition has an evaluation test at numerals whose reference
  distinguishes it from the wrong-but-well-typed readings, and the two central
  theorems (`divisorFlip_involutive`, `sumDivisorsBy_reindex`) are instantiated
  at FULLY DISCHARGED arguments — positivity from `zero_lt_succ`, divisibility
  from `Nat.dvd_mul` at literals — so the kernel really reduces both sides.
- Mutation table in
  [`docs/plan/status/1619-arithmetic-functions.md`](../../plan/status/1619-arithmetic-functions.md).
