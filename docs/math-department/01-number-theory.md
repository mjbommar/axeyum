# 01 — Number theory

Reviewer: an elementary and analytic number theorist
Verdict, 2026-09-06: **impressed; the shelf grew, the ceiling did not move**
Last measured: 2026-09-06 at `2104b55f7`

> "You have added a named theorem I care about and a function called π. One of
> those is a result. The other is a definition with three lemmas, and until one
> of them is an inequality, the analytic door is still shut."

> **AUDITED 2026-09-04, RE-MEASURED 2026-09-06.** Every absence claim in this
> file was re-checked against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for the first pass, and the
> corrections marked **[AUDIT]** below. Across the twelve files, 11 of 76
> absence claims were false and 12 more overstated the gap; the cause is that
> the ledger characterises only 38% of its proved facts and does not cover 430
> kernel theorems at all (ADR-1605). The 2026-09-06 pass found the opposite
> failure as well — **two rows of this file's own "what we have" table named
> declarations that do not exist**, one of them for a theorem that is not
> proved at all. Corrections marked **[NAME]**.

> **Retired 2026-09-06 (ADR-1674):** the 430 is not reproducible by its own
> method - three later readings give 599, 620, 721 and 973 on three different
> denominators. The measured, gated figure is **721 of 3,079 registered
> kernel theorem names uncovered**, ratcheted by `gen-ledger-coverage`.

## The persona

Works on primes, congruences, Diophantine equations, and L-functions. Values
theorems with names and a proof you can follow. Deeply unimpressed by
infrastructure claims and completely convinced by Wilson's theorem. Their test
for whether a formalization is serious is quadratic reciprocity: it is the
first result in the subject that cannot be bluffed, it has no short proof, and
every real library has it or is not yet real.

## What the library has today

**Still by a wide margin the largest area in the ledger: 1,291 proved ℕ/ℤ
facts — 916 ℕ and 375 ℤ — against 262 open and 2 conjectured** (twin primes and
strong Goldbach, both recorded as open problems, not as work). On 2026-09-04
the same query returned 1,218 proved and 257 open, so the field added 73 proved
facts in two days.

The trusted surface under all of it is measured, not asserted.
`nat_axiom_inventory --require-axiom-free nat` reports `nat: axiom=0` and
`integer: axiom=0`; all 30 axioms in the build belong to `AxReal`, the
axiomatized ordered-field real carrier, which nothing in this shelf touches.
The kernel index behind every claim below holds **3,323 declarations** (872
definitions, 2,231 theorems), of which 1,118 theorems are in the `Nat`
namespace and 396 in `Int`.

Named results present:

| result | where |
|---|---|
| Wilson's theorem | `Int.wilson`, with `Int.wilsonHalfSplit` |
| Quadratic reciprocity | `Int.legendreSym`, `Int.firstSupplementaryLaw{Residue,NotResidue}`, `Int.secondSupplementaryLaw` |
| Fermat's little theorem | `Int.pow_prime_sub_one_modeq_one` |
| **Fermat's two-squares theorem** | `Int.fermatTwoSquares` — every prime `p ≡ 1 (mod 4)` is `a² + b²` (landed 2026-09-06) |
| Euler's totient | `Nat.totient`, its computation lemmas, and `Nat.totient_mul_of_coprime` |
| Multiplicative order and primitive roots | `Int.IsOrder` with `order_exists`, `order_unique`, `order_dvd_totient`, `pow_modeq_one_iff_order_dvd`; `Int.IsPrimitiveRoot`, `Int.primitive_root_pow_injective` |
| Bézout's identity | **[NAME]** `Int.gcd_eq_gcd_ab` (existential), `Int.gcd_eq_gcd_ab_witnesses` and `Nat.gcd_eq_gcd_ab` (with the explicit `Int.gcdA`/`Nat.gcdA` and `Nat.xgcdAux_sound`). The name this file previously gave, `Int.bezout_witnesses`, is ABSENT from a 3,323-declaration index |
| Chinese remainder theorem | `Int.crt_exists`, `Int.crt_unique`, `Nat.crt_unique` |
| Euclid's infinitude of primes | `Int.euclid_infinitude`, and now `Nat.primeCounting'_unbounded` in counting form |
| Irrationality of √2 | `Nat.no_rational_sqrt_two` |
| Unique factorization | `Nat.exists_prime_factorization` with `Nat.Multiset.count_eq_of_prod_eq` |
| Kummer/Pascal divisibility | "a prime divides the interior binomial coefficients of its own row" |
| Fibonacci identities | **[NAME]** `Nat.fib_add`, `Nat.coprime_fib_succ`, `Int.fib_cassini`, `Int.fib_two_mul`. `Int.gcd_fib` is ABSENT, and so is the theorem it named: `gcd (fib m) (fib n) = fib (gcd m n)` is **not proved**, because `Nat.gcd` is a `WellFounded.fix` and mirroring its descent needs `well_founded_fix_eq` at each step (`fibonacci.rs`, module doc) |
| Arithmetic functions as a family | `Nat.sumDivisorsBy`, `Nat.numDivisors`, `Nat.IsMultiplicative` (totient an instance), `Nat.dirichlet` with `dirichlet_comm`, and Möbius as **[NAME]** `Nat.moebiusPos`/`moebiusNeg`/`moebiusAbs` — a graded pair, because ℕ has no sign (`Nat.moebius` itself is ABSENT) |
| Prime counting | `Nat.primeCounting`, `Nat.primeCounting'`, both monotonicity laws, `Nat.isPrime_eq_true_of_prime`; `Nat.primorial` with 7 laws |
| Modular arithmetic | a large `Int.ModEq` family: cancellation, `of_mul_left`, `cancel_left_div_gcd`, negation of modulus |
| Least-number principle | `Nat.lnp_bounded_search`, `Nat.least_divisor_search`, `Nat.lnp_decidable` |

The ℤ carrier is characterized categorically (`Int.Characterization.categorical`,
with `induction`, `injective`, `surjective`, `rec_unique`), which is unusual
and worth more to a foundations reader than to this one.

**The 262 open ℕ/ℤ facts are not one population.** 257 are transcribed Mathlib
v4.30 propositions sitting in the ledger as a work queue — `Nat.choose_lt_pow`,
`Int.exists_least_of_bdd`, `Int.add_emod`, and so on. The other five are the
library's own: four first-order-logic facts filed under the `Nat` fragment
(the formula decoder, the diagonal lemma, Henkin completeness, the first
incompleteness theorem), and **one that this field's own work created** — the
composite characterisation of sums of two squares, opened when
`Int.fermatTwoSquares` landed and its converse did not. That is a declared
frontier, not a gap in the record.

## Their verdict

Wilson and quadratic reciprocity, constructively, with nothing assumed, was
already the point at which they stopped treating this as a toy. Two days later
there is a second named theorem of the same class: **Fermat's two-squares
theorem**, by Euler's descent, with the descent step stated for reuse rather
than inlined. That is not a lemma dressed up as a result. It is the shape of
proof this field actually values — an infinite descent, carried by an order
shelf built for it, with the multiplier indexed by an ℕ so the arithmetic is
definitional and the whole proof holds exactly one transport.

They would also notice, with less warmth, that the two shelves opened *toward*
the analytic side did not arrive at a theorem. There is now a `Nat.primorial`
and a `Nat.primeCounting`, and eight and five declarations respectively about
them. Every one of those is a monotonicity law, an unfolding equation, or a
bridge between two spellings of "prime". **Not one of them is a bound.** The
sharpest quantitative statement on the shelf is `choose (2m+1) m ≤ 4^m` — real,
and exactly the estimate Erdős's argument needs — sitting next to a primorial
it has not yet been connected to.

So the summary has to be split. **The elementary and Diophantine shelf moved
forward by a named 17th-century theorem and a reusable method.** The analytic
shelf acquired an object and no inequality about it. And the algebraic shelf —
rings of integers, ideals, class groups — is exactly where it was, because its
blocker is a kernel decision and not a queue.

## What they would say is missing

- **Algebraic number theory, entirely.** `shape_search --name-like ideal` and
  `--name-like classgroup` are both ABSENT against the 3,323-declaration index.
  No rings of integers, no ideals, no unique factorization in a Dedekind
  domain, no class group, no units theorem. Unchanged since 2026-09-04.
- ~~**Multiplicative structure.**~~ **[AUDIT/2026-09-06] mostly landed, in
  three slices.** Möbius exists (as the graded pair above), Dirichlet
  convolution exists with commutativity and two bridges, `IsMultiplicative`
  exists with the totient as an instance, and the subset-indexed sum machinery
  underneath is 52 declarations in `Nat.Subsets`. What is missing is now two
  named theorems, not a family: **Möbius inversion** (`--name-like inversion`:
  ABSENT) and **`Nat.dirichlet_assoc`**. Totient multiplicativity was already
  proved on 2026-08-30 (`Nat.totient_mul_of_coprime`, audit row A7).
- ~~**Primitive roots and the structure of (ℤ/n)\*.**~~ **[AUDIT] landed
  2026-09-04** (roadmap W1-7), except existence modulo a prime.
- **Analytic anything, still — but the first rung is now half-built.** π exists,
  is monotone, and is unbounded; `--name-like zeta` is ABSENT and there are no
  Dirichlet series and no L-functions. There is **no upper or lower bound on
  π(x) of any kind**, which is the whole of what "analytic" would mean here.
- ~~**Classical Diophantine results.**~~ **Half wrong as of 2026-09-06.** Sums
  of two squares is proved and the descent is a reusable declaration. Pell's
  equation (`--name-like pell`: ABSENT) and continued fractions
  (`--name-like continuedfraction`: ABSENT) are still absent.

## The blocker

Three now, of three different kinds, and the third is new.

**For algebraic number theory: `Quot.sound`.** ℤ/n as a quotient ring, ideals
as quotients, and every construction downstream of them require proving that
related representatives are equal, which this kernel cannot do. The modular
arithmetic here is done with an explicit `ModEq` relation instead, which works
and does not scale to ideals. Unchanged. See [04-algebra.md](04-algebra.md).

**For Dirichlet series and L-functions: the classical analysis stack.** Complex
analysis, contour integration, and convergence all sit behind
[03-classical-analysis.md](03-classical-analysis.md).

**For Chebyshev's bounds: neither of the above.** This is the finding of the
last two days and it is worth stating plainly, because the earlier version of
this file got it wrong by inheriting the analytic blocker. Chebyshev's
π(x) estimates need no analysis at all. What they need, measured rather than
guessed, is:

1. a divisibility law for a product over a predicate-restricted range —
   `Nat.prodRange` has neither permutation invariance nor a swap lemma, and the
   ℤ counterparts took roughly 650 lines;
2. `p ∣ choose (2m+1) m` for `m+1 < p ≤ 2m+1` — the kernel's only
   choose-divisibility lemma is `Nat.prime_dvd_choose`, which has the prime on
   *top* and cannot be specialised to this;
3. for the exponent form, Legendre's formula. `Nat.divMaxPow` is declared, but
   its lemmas belong to the evaluation family **`natural-max-power-dividing`**,
   which is genuinely held out and has never been scored.

Items 1 and 2 are effort, sized and unblocked. Item 3 is **a partition
constraint, not mathematics** — the work is briefable only at the cost of
spending a blind evaluation family, and that is a decision somebody has to make
rather than a lemma somebody has to prove. This reviewer would say that is a
perfectly respectable reason not to have the theorem, and an entirely different
kind of reason from the other two, and that the file should never again
collapse it into "waiting on analysis".

Nothing here touches the elementary material below it, and there is a great
deal of that left.

## Next five, in their priority order

- [x] **1. The structure of (ℤ/n)\* and primitive roots.** *Landed 2026-09-04;
      `Int.IsOrder` and `Int.IsPrimitiveRoot` measured present today. Existence
      of a primitive root mod a prime still did not land: it needs
      `∑_{d∣n} φ(d) = n`, and half that obstruction closed — the divisor
      aggregate `Nat.sumDivisorsBy` and its reindexing primitive now exist; the
      classification of `[0,n)` by `gcd k n` does not.*
- [~] **2. Multiplicative arithmetic functions as a family.** *Three slices
      landed — 29 declarations (ADR-1619), 14 (ADR-1658), 12 (ADR-1671), all
      axiom-free. Möbius, the divisor function, Dirichlet convolution and
      multiplicativity are all present. What is open is Möbius inversion and
      `dirichlet_assoc`; both sit behind one `Nat.prodRange` range-stability
      law, `(∀ i, a ≤ i → f i = 1) → a ≤ b → prodRange f b = prodRange f a`,
      which the mobius-transfer lane identified as the single highest-value
      target on this shelf.*
- [x] **3. Unique factorization as a theorem, not a construction.** **[AUDIT]
      Already proved**: `Nat.Multiset.count_eq_of_prod_eq` with
      `Nat.exists_prime_factorization` (audit row A5), both re-confirmed
      present today.
- [x] **4. Sums of two squares, with the descent argument reusable.**
      *Done 2026-09-06 as `Int.fermatTwoSquares`, in three slices; the descent
      step is a named declaration and the ℤ order shelf built for it is 18 laws
      that outlive it. The residue is one open fact — the composite
      characterisation — which needs a factorisation multiset.*
- [~] **5. Chebyshev-type bounds on π(x).** *The shelf is open and empty of
      bounds: `Nat.primorial` with 7 laws, `Nat.primeCounting`/`primeCounting'`
      with both monotonicity laws, the boolean-to-propositional primality
      bridge that turned out to be the keystone nobody had priced, and Euclid
      in counting form. No inequality on π yet. Blocked as set out above: two
      sized elementary lemmas, and one ingredient in a held-out family.*

Three of the five are closed and two are partly landed, so the reviewer's own
list is nearly spent. Asked what would replace it, they name the same three
they would have named in 1850: an inequality on π, Möbius inversion, and a
second Diophantine method (Pell, via continued fractions) to sit beside the
descent — and they note that the first two are now each one named lemma away,
which is not something they could have said two days ago.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: 1,218 proved ℕ/ℤ facts, 257 open. Wilson, quadratic reciprocity, Fermat, Euler totient, Bézout, CRT, Euclid, √2 irrational all present and axiom-free. | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Next Five item 1 landed** (roadmap W1-7): `int_prelude/mult_order.rs`, 11 declarations with empty footprints — multiplicative order by bounded search, order divides the totient, `a^k ≡ 1 ↔ ord ∣ k`, primitive roots, and power injectivity (ADR-1598). **Existence of a primitive root mod a prime did not land**, and the obstruction is precise: the counting route needs `∑_{d∣n} φ(d) = n`, hence a divisor-set aggregate and the `d ↦ n/d` reindexing of a predicate-restricted sum, neither of which exists. Two design findings recorded: the search predicate must be shifted (`a^(j+1) ≡ 1`, since the unshifted form is true at j=0 for every a), and `Coprime (a^i) n` falls out of the order relation via the Bézout certificate already inside it. | `a9ef9465d`; `int_prelude::` 87 passed |
| 2026-09-05 | **Next Five item 2 partly landed** (roadmap W2-18, ADR-1619): the divisor-set aggregate `sumDivisorsBy`, its reindexing primitive, `numDivisors`, `IsMultiplicative` with the totient as an instance, and Dirichlet convolution with commutativity — 29 declarations, footprint 0. The obstruction ADR-1598 named for primitive-root existence is half closed: the aggregate and reindexing exist; the classification of `[0,n)` by `gcd k n` does not. **The reindexing map this reviewer and every brief assumed, `d ↦ n/d`, is not the one that works** — it is not injective on the range — and the involution fixing non-divisors is. Möbius inversion did not land and is sized: it needs the divisors of a squarefree number in bijection with subsets of its prime factors. | `3e650f81a`; `nat_prelude::` 562 passed |

| 2026-09-05 | **Item 4, first slice** (roadmap W3-10, ADR-1633): `Int.IsSumOfTwoSquares`, the Brahmagupta–Fibonacci identity emitted by the ring producer rather than proved by hand, closure under multiplication, the mod-4 refutation, and a reusable descent step shaped for `Nat.strongInduction`; 20 declarations, footprint 0. **Fermat's theorem is open on order, not algebra**: ℤ has no `natAbs_le_iff`, `mul_le_mul`, or `sq_le_sq`, so the strict decrease of the descent measure cannot yet be stated. The reviewer's blocker was wrong in one place: −1 as a residue mod `p ≡ 1 (mod 4)` was already proved (ADR-1235). | `e5c1d09cd` |
| 2026-09-05 | **Item 5, first slice** (roadmap W3-11, ADR-1637): `Nat.primorial` with its equations and monotonicity, and `choose (2m+1) m ≤ 4^m`, sharper than the existing power-of-two bound; 15 declarations, footprint 0. Erdős's `primorial n ≤ 4^n` is open on a divisibility law for predicate-restricted products. **The π(x) bounds were not attempted and should not be briefed**: five rows of the held-out family `discrete-step-and-counting-bounds` are that shelf and the family has never been scored; two of its rows are one lemma application away, which is a fact about the evaluation, not a task. | `88ee63a0e` |
| 2026-09-05 | **Item 4, second slice** (roadmap W3-10, ADR-1647): the ℤ order shelf (18 laws), centered remainders with the strict decrease of the descent measure, the multiplier bounds, and the entry point from a square root of −1 mod p; 25 axiom-free declarations. **This file's blocker was two-thirds stale**: two of the three named missing lemmas already existed under other names, a reminder that a recorded obstacle accumulates staleness by construction. Fermat's theorem is now four sized, unblocked pieces away. | `75222395b`; `int_prelude::` 123 passed in the lane |
| 2026-09-06 | **Item 4 landed: Fermat's two-squares theorem** (roadmap W3-10, ADR-1650). Every prime congruent to 1 mod 4 is a sum of two integer squares, a kernel theorem with empty footprint, by the descent stated for reuse in the first slice, the integer order shelf of the second, and a strong induction whose multiplier is an ℕ index so the order facts are definitional. The statement recorded in the ledger while the fact was open matched the kernel's rendering byte for byte. Three of this reviewer's five items are now done; the two open ones are Chebyshev's bounds and the Möbius residue, each with a lane on it. | `ad586e607`; `int_prelude::` 128 passed in the lane |
| 2026-09-06 | **Item 2, second slice** (roadmap W2-18, ADR-1658): a multiset product selected by a predicate, shown to be a multiset product in its own right, hence dividing the full product and injective on selections by unique factorisation; 14 axiom-free declarations. The brief's position-indexed design was wrong for this carrier, which has no order. Möbius inversion still waits on the sum transfer between a range index and a subset fold, and on Dirichlet associativity. | `700c23071`; `nat_prelude_tests::` 249 passed in the lane |
| 2026-09-06 | **Item 5, second slice** (roadmap W3-11, ADR-1655): monotonicity of the prime-counting function, the bridge from the boolean primality test to the propositional one (which turned out to be the keystone nobody had priced), and infinitude of primes in counting form. Chebyshev's bound proper is blocked on Legendre's formula, whose family is held out for evaluation, and on a divisibility law for products over restricted ranges; both are named, neither is effort. | `1b5a1d86d`; nat sweeps 7 passed in the lane |
| 2026-09-06 | **Item 2, third slice** (roadmap W2-18, ADR-1671): the masked subset fold `Nat.Subsets.sumSubsetsOn`/`sumSelOn` with its grading law — the one law a mask-ignoring fold fails, so it was designed in as the discriminating guard — and `Nat.Multiset.count_le_of_dvd_prod`, the divisor-valuation bound; 12 axiom-free declarations. Two sizings corrected downward and one shape refuted: a congruence cannot restrict *which* predicates a fold visits, so the mask had to become a parameter. Surjectivity's blocker MOVED to a `prodRange` range-stability law, which is now the single highest-value target on the shelf. | `2be11c9ab` |
| 2026-09-06 | **Whole file re-measured against main.** Ledger: 1,291 proved ℕ/ℤ facts (916 ℕ, 375 ℤ), 262 open, 2 conjectured — up from 1,218/257. Open facts partitioned for the first time: 257 Mathlib transcriptions, 5 native. Trusted surface read from the kernel, not from prose: `nat: axiom=0`, `integer: axiom=0`, all 30 axioms in `AxReal`. Index: 3,323 declarations. **Two rows of the "what we have" table were wrong** — `Int.bezout_witnesses` and `Int.gcd_fib` are both ABSENT; Bézout exists under `Int.gcd_eq_gcd_ab`, but `gcd (fib m) (fib n) = fib (gcd m n)` is **not proved at all**, so the table claimed a theorem the library does not have. `Nat.moebius` is likewise absent (it is a graded pair). The Chebyshev blocker was rewritten: it is not the analysis stack, it is two sized elementary lemmas plus one ingredient in a held-out family — a partition constraint, which is a third kind of blocker and had been collapsed into the second. Nothing number-theoretic is pending in an unmerged worktree: of the sixteen live worktrees, the only branch touching this shelf is a prime-power-casework lane whose five ℕ facts are **already `proved` on main**, with their kernel theorems (`Nat.prime_eq_one_of_pow`, `Nat.prime_mul_eq_prime_sq_iff`, `Nat.prime_not_prime_pow_ne_one`, …) declared in `prime_char.rs` rather than in the file that branch adds. | `2104b55f7` |

## How to re-measure

```sh
python3 - <<'PY'
import json, glob, collections
c = collections.Counter()
for f in glob.glob('artifacts/facts/*.json'):
    d = json.load(open(f)); fr = (d.get('formal') or {}).get('fragment')
    if fr in ('Nat', 'Int'): c[(fr, d.get('epistemic_status'))] += 1
for k in sorted(c): print(k, c[k])
PY

# the trusted surface, read from the kernel and not from any prose
cargo run --release -p axeyum-lean-kernel --example nat_axiom_inventory \
  -- --require-axiom-free nat

# does a named result exist? search the SHAPE, and rebuild first -- a stale
# binary reports a false ABSENT, and on 2026-09-06 the prebuilt one in the
# main checkout was six kernel source files behind main.
cargo run --release -p axeyum-lean-kernel --example shape_search -- --const Nat.totient
just brief "primitive root"
```

Two traps this re-measurement hit, recorded so the next one does not:

- **`shape_search` honours only the LAST `--name`.** Passing
  `--name A --name B --name C` silently answers about `C` alone and prints
  `FOUND 1`, which reads exactly like a successful three-way check. One name
  per invocation — the same failure mode already documented for
  `nat_theorem_inventory`. `--name-like` is the right tool for a family, and it
  ignores case, `_` and `.`, so a snake_case guess still retrieves a camelCase
  declaration.
- **An `ABSENT` verdict on a name is not an absent theorem.** Both false rows
  in the table above were found by probing the name; only one of them was
  actually a missing result. Follow every `ABSENT` with a `--name-like` on the
  concept before writing the gap down.

## Related

- [10-logic-and-foundations.md](10-logic-and-foundations.md) — the ℤ
  categoricity result, the least-number-principle work, and the four
  first-order facts counted as open ℕ rows above
- [04-algebra.md](04-algebra.md) — the `Quot.sound` blocker in full
- [07-combinatorics.md](07-combinatorics.md) — `Nat.Multiset`, `Nat.Finset`,
  and the `Nat.Subsets` fold the Möbius work is built on
