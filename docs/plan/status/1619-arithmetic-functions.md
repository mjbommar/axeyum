# Lane: arithmetic-functions — the divisor aggregate, its reindexing, and where Möbius stands

<!-- plan-section: lane-status -->

**Your lane's block (`landed`, arithmetic-functions, 2026-09-04).** Roadmap
**W2-18** (multiplicative arithmetic functions as a family) and **W2-19**
(general inclusion-exclusion), by
[ADR-1619](../../research/09-decisions/adr-1619-the-divisor-map-is-a-permutation-only-if-it-fixes-the-non-divisors.md).
**W2-18 landed except Möbius inversion. W2-19 did not start.** Both negatives
are sized below.

**29 declarations across two new files, every axiom footprint empty**,
`nat_prelude::` green.

### What the handoff got wrong, and what it got right

`docs/math-department/01-number-theory.md`'s progress log said the
primitive-roots lane stalled because *"the counting route needs `∑_{d∣n} φ(d) =
n`, hence a divisor-set aggregate and the `d ↦ n/d` reindexing of a
predicate-restricted sum, neither of which exists."*

- **The aggregate half was half-wrong.** `Nat.sumDivisors` existed
  (`perfect.rs`) but is MONOMORPHIC — the summand is hard-wired to
  `fun d => d`, so it expresses `σ` and nothing else. What was missing was the
  polymorphic form, which is one line over the already-present
  `Nat.sumRangeIf`.
- **The reindexing half was right**, and it was the real work.

### The finding: `d ↦ n/d` is not the map that reindexes

`Nat.sumRange_permute` needs `injectiveOn` + `mapsInto`, and `fun k => n / k`
is **not injective on `[0, n]`** — at `n = 6` it sends `4`, `5` and `6` all to
`1`. The permutation is the one that moves only the divisors:

```text
Nat.divisorFlip n d := if d ∣ n then n / d else d
```

Fixing the non-divisors buys two things, both load-bearing: it is a **genuine
involution on all of `Nat`**, so `Nat.divisorFlip_injectiveOn` quantifies over
an ARBITRARY range and only `mapsInto` mentions `succ n`. Positivity is
load-bearing too — at `n = 0` every `d` divides and the map collapses onto `0`.

### Landed — `nat_prelude/arith_functions.rs` (15)

`Nat.dvdB` with both bridges to `Nat.dvd`; `Nat.sumDivisorsBy`,
`Nat.numDivisors`, and `sumDivisorsBy_eq_sumDivisors` (`Eq.refl` — the new
aggregate CONTAINS `σ`, delta for delta); `Nat.div_div_self_of_dvd`
(`0 < n → d ∣ n → n/(n/d) = d`, worth naming separately, it is the cofactor
law); `Nat.divisorFlip` with two value equations, the involution, and the
`injectiveOn`/`mapsInto` pair; and

```text
Nat.sumDivisorsBy_reindex : ∀ f n, 0 < n →
  sumDivisorsBy f n = sumDivisorsBy (fun d => f (n / d)) n
```

### Landed — `nat_prelude/arith_functions_family.rs` (14)

`Nat.IsMultiplicative` stated once for the family, with
`isMultiplicative_totient` (the already-proved `totient_mul_of_coprime`,
repackaged) and `isMultiplicative_one` as its two members; `Nat.dirichlet` and
`Nat.dirichlet_comm`, whose proof is *only* the reindexing plus the cofactor
law plus `mul_comm`; `Nat.sumDivisorsBy_congr`, the congruence bounded **by
divisibility** rather than by an index bound (`n/(n/d) = d` is false off the
divisor set and the unconditional `sumRange_congr` cannot say so);
`numDivisors_eq_dirichlet` and `sumDivisors_eq_dirichlet`; and Möbius as a
graded pair — `omegaCount`, `moebiusAbs`, `moebiusPos`, `moebiusNeg`, with
`moebius_pos_add_neg` and `moebius_pos_mul_neg`.

Coprimality is spelled `Eq (gcd a b) 1`: there is **no `Nat.Coprime` constant**
in this prelude (`shape_search --name Nat.Coprime` → ABSENT at
`declarations=2857`).

### Did NOT land, sized

- **Möbius inversion.** Needs `∑_{d∣n} μ(d) = [n = 1]`. The standard proof puts
  the divisors of a squarefree `n` in bijection with the SUBSETS of its
  prime-factor set. `Nat.Finset.decode`/`existsSubset_of_search` (ADR-1614)
  gives the subset enumeration, but that bijection does not exist and **the
  reindexing here does not help with it** — it permutes the divisor set rather
  than describing it.
- **`∑_{d∣n} φ(d) = n`, hence primitive-root existence (ADR-1598).** One of the
  two named prerequisites is now closed. The other is not and was not
  attempted: the classification of `[0,n)` by `gcd k n`. **Do not read ADR-1619
  as unblocking ADR-1598 outright.**
- **W2-19, general inclusion-exclusion.** Not started. The missing piece is a
  sum INDEXED BY SUBSETS — `sumRange (fun code => …) (2^n)` together with the
  parity of `Nat.Finset.card (decode n code)`. Independent of everything above,
  and a well-defined next slice.

### Mutation table — and what it does NOT show

Eight wrong-but-well-typed edits, each applied in this lane's own isolated
worktree, rebuilt, and run against the 21 tests in the two modules. **No mutant
survived.** But the interesting column is HOW each died.

| mutant | what it makes wrong | killed by | tests dead |
|---|---|---|---|
| M1 | `sumDivisorsBy`'s bound `succ n` → `n` (the proper-divisor reading) | trusted gate | 19 / 21 |
| M2 | `divisorFlip` → the naive `n / k` | trusted gate | 19 / 21 |
| M3 | `numDivisors` sums the divisors instead of counting them | trusted gate | 19 / 21 |
| M4 | `dirichlet` → the pointwise product over divisors | trusted gate | 19 / 21 |
| M5 | `moebiusPos` reads the parity the other way round | trusted gate | 19 / 21 |
| M6 | `moebiusAbs` is `1` everywhere, ignoring squarefreeness | trusted gate | 19 / 21 |
| M7 | **coordinated**: BOTH Möbius halves swap parity, so both graded-pair laws remain TRUE | trusted gate | 19 / 21 |
| M8 | `omegaCount` counts the prime factors of `n+1` | **evaluation test** | **1 / 21** |

**Seven of the eight were killed by `Kernel::add_declaration` refusing a
dependent proof, not by any evaluation test firing on its own.** The two
survivors in every 19-kill row are the pure-Rust reference tests, which touch no
kernel. So those seven rows credit the kernel, not the test suite, and a
mutation table that stopped at M6 would have overstated what the tests guard.

M7 was built to escape that: swapping BOTH Möbius parities leaves
`moebius_pos_add_neg` and `moebius_pos_mul_neg` true, so the gate ought to be
blind. It is not — the proof terms are written against the specific branch
order (`select_nat_true` at `(one, zero)`), so a relabelled definition breaks
them even though the statement survives. Worth knowing: in this prelude a
*statement*-preserving mutation is still usually a *proof*-breaking one.

M8 is the one the gate genuinely cannot see. `omegaCount`'s VALUE is read by no
proof — both laws case-split on whatever the parity `Bool` happens to be — so
shifting it by one leaves every declaration admissible and changes only what
the definitions compute. **Exactly one test died, and it is the right one**
(`moebius_takes_its_classical_values`). That row, and only that row, measures
the evaluation tests.

### A process note

One rejected declaration fails the whole shared `build_nat_prelude`, and the
error is `TypeMismatch { expected: ExprId(1704807), got: ExprId(1704813) }` —
which names neither the declaration nor the terms.
`declare_arith_functions_family_all` therefore reports the rejected step **by
name** and renders the mismatch. It replaced a bisect on this lane's one
rejection and costs nothing.

<!-- plan-section: landed-changes -->

| 2026-09-04 | arithmetic-functions | W2-18: the divisor aggregate `Nat.sumDivisorsBy` and its `d ↦ n/d` reindexing (ADR-1598's named blocker), the Dirichlet convolution with `dirichlet_comm` as a corollary of it, `Nat.IsMultiplicative` with totient as a member, and Möbius as a graded `Nat`-valued pair — 29 declarations, footprints empty. Möbius inversion and W2-19 did not land; both obstructions sized. ADR-1619. |
