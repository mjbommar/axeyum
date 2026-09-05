# ADR-1637: The primorial is a product over `minFac`, and Chebyshev's lower bound runs into a blind family

Status: accepted
Date: 2026-09-05
Index-summary: `Nat.primorial` lands as `prodRangeIf (fun i => beq (minFac i) i) (fun i => i) (succ n)` rather than over the already-declared `Nat.isPrime`, because `isPrime` is a divisor COUNT whose bridge to `prime_condition` is a counting argument in its own right while `minFac`'s bridge is three existing lemmas; and the brief's second and third deliverables — both stated about `Nat.primeCounting` — are held back because five of the ten rows of the preregistered, never-scored held-out family `discrete-step-and-counting-bounds` are exactly the `Nat.primeCounting` shelf

Related: ADR-0653 (an unblocking lane declares the CONSTRUCTION and nothing
else), ADR-1559 (`primeCounting`/`lcmUpto` are that construction, for draw 19),
ADR-0542 (held-out isolation and the amendment ledger), ADR-1614
(`Nat.strongInduction`)

## Context

Roadmap W3-11 asks for Chebyshev-type bounds on the prime-counting function in
pure ℕ exponent form:

1. the primorial bound `∏ {p prime, p ≤ n} ≤ 4^n` (Erdős);
2. `4^n ≤ (2n+1) · (2n)^(π(2n))`, which IS Chebyshev's lower bound and needs no
   real logarithm;
3. infinitude of the primes in the counting form, `∀ k, ∃ n, k ≤ π(n)`.

Two things had to be decided before any of it could be written, and neither was
a mathematical question.

## Decision 1 — the primorial's predicate is `minFac`, not `Nat.isPrime`

This prelude already carries a `Bool`-valued primality predicate.
`prime_counting.rs` declares

```text
Nat.isPrime n := beq (countRange (fun d => beq (n % (d+1)) 0) n) 2
```

— *n has exactly two divisors in `[1,n]`* — and, per ADR-0653, **no theorem
about it at all**. So the predicate is in the environment and its meaning is
not: bridging `isPrime n = true` to this prelude's

```text
prime_condition x := 2 ≤ x ∧ ∀ c, c ∣ x → c = 1 ∨ c = x
```

means proving *a natural number has exactly two divisors iff it is prime*, a
counting argument over `countRange` with an explicit two-element enumeration.
That is a lemma in its own right and it is not what a primorial needs.

`Nat.minFac` needs no counting. `min_fac_dvd.rs` already carries all three
pieces — `min_fac_dvd : 2 ≤ n → minFac n ∣ n`,
`min_fac_two_le : 2 ≤ n → 2 ≤ minFac n` and
`min_fac_prime : 2 ≤ n → prime_condition (minFac n)` — and both directions of

```text
Nat.min_fac_eq_self_of_prime : ∀ n, prime_condition n → minFac n = n
Nat.prime_of_min_fac_eq_self : ∀ n, 2 ≤ n → minFac n = n → prime_condition n
```

fall out with **no new induction**: forward is `Or.resolve_left` on the divisor
disjunction with `2 ≤ 1` refuted by `not_succ_le_self`, reverse is one
`Eq.rec` transport of `min_fac_prime` along the equation.

So

```text
Nat.primorial n := prodRangeIf (fun i => beq (minFac i) i) (fun i => i) (succ n)
```

### The `i = 1` row is deliberate

`minFac` has Mathlib's two boundary conventions, `minFac 0 = 2` and
`minFac 1 = 1`. So `i = 1` **passes** the predicate and is not prime. It
contributes the factor `1`, the multiplicative identity, so the value is still
exactly `∏ {p prime, p ≤ n}` — measured, not argued: the evaluation test pins
`1, 1, 2, 6, 6, 30, 30, 210` at `n = 0 … 7`.

A COUNT built on this predicate would be off by one and would need a `2 ≤ i`
conjunct, which costs a `Bool`-valued conjunction this prelude does not have
(`bool_select_nat` is `Bool.rec` at `Nat`; there is no `Bool.rec` at `Bool`
helper). A PRODUCT does not need it. This is one more reason the primorial is
not routed through the counting shelf.

The one visible cost is in `Nat.primorial_succ_of_not_prime`, which carries a
`2 ≤ succ n` premise it looks like it should not need. It does: at `n = 0` the
selector is TRUE (`minFac 1 = 1`) although `1` is not prime, so `cond = false`
is not derivable there. The conclusion still holds at `n = 0`
(`primorial 1 = primorial 0 = 1`); what fails is this route to it, and the
Erdős induction only ever needs the premise-carrying form.

## Decision 2 — deliverables 2 and 3 are held back, on a partition check

Both are statements **about `Nat.primeCounting`**. That constant is the subject
of five of the ten rows of the preregistered held-out family
`discrete-step-and-counting-bounds`
(`artifacts/autogenesis/nursery-v2-extension.json`):

| row | statement |
| --- | --- |
| `Nat.monotone_primeCounting` | `Monotone Nat.primeCounting` |
| `Nat.monotone_primeCounting'` | `Monotone Nat.primeCounting'` |
| `Nat.primeCounting'_eq_zero_iff` | `∀ {n}, n.primeCounting' = 0 ↔ n ≤ 2` |
| `Nat.primeCounting_add_le` | the totient step bound |
| `Nat.primeCounting'_add_le` | the same, primed |

Every one is `partition: "held-out"`, and the family has **never been scored**:
`artifacts/autogenesis/holdout-evaluation-v1.json` is the only committed
evaluation record and it scores `integer-absolute-value`, not this one.

Neither gate that fires at push forbids the brief's inequality on its face.
`check-autogenesis-holdout-isolation.py` forbids *settling* a held-out fact or
*referencing* its id, and `4^n ≤ (2n+1) · (2n)^(π(2n))` is neither — this run
reports `held_out=216 settled=0 references=0 verdict=PASS` with the primorial
shelf in the tree. The objection is ADR-0653's rule, which R9 is only a proxy
for: *a family may be blind only if its mathematics is unpublished.* A lane
that states Chebyshev's lower bound over `Nat.primeCounting` publishes the
mathematics of `Mathlib.NumberTheory.PrimeCounting`, which is the whole of this
family's `Nat` half.

### The measured half of that, which is worth the coordinator's attention

**Two of the ten rows are one existing-lemma application away from the
environment as it stands today, before this lane wrote anything.**
`Nat.primeCounting' = Nat.count Nat.isPrime`, `Nat.count` is definitionally
`Nat.countRange`, and `Nat.countRange_le_of_le : ∀ f m n, Le m n →
Le (countRange f m) (countRange f n)` has been in this prelude since the
counting shelf landed. That IS `Monotone Nat.primeCounting'` — held-out row 7 —
with `f := Nat.isPrime`, and row 6 follows from it through
`primeCounting n = primeCounting' (succ n)` and `le_succ_succ`.

Nothing has been declared, so nothing is spent. But it means the family's
blindness does not rest on the mathematics being hard here; it rests on nobody
having written the two lines. That is exactly `check-holdout-adjacency.py`'s
**shape 2** ("our development proves the same proposition under another name,
so R9's exact-name comparison sees nothing"), reached by construction rather
than by accident — and it is a reason to score or amend the family deliberately
rather than to leave it standing as a measurement nobody can cash.

So: **the primorial shelf lands, stated entirely without `Nat.primeCounting`,
and the counting form is not stated here.** This is a decision about who may
spend the family, not a claim that the mathematics is out of reach. The
coordinator owns the board; an amendment ledger (ADR-0542) or a preregistered
evaluation record is the lawful route, and either is a spend that a lane brief
cannot authorise on its own.

The consequence for the roadmap is precise and worth stating plainly: **W3-11's
headline inequality cannot be landed by any lane until the family is either
scored or amended.** Deliverable 1 is independent of it and is where the work
went.

## What landed

All in `crates/axeyum-lean-kernel/src/nat_prelude/primorial.rs`, registered
from `nat_prelude.rs`, every declaration axiom-free.

| name | statement |
| --- | --- |
| `Nat.primorial` | `fun n => prodRangeIf (fun i => beq (minFac i) i) (fun i => i) (succ n)` |
| `Nat.primorial_zero` | `primorial 0 = 1` |
| `Nat.primorial_succ` | `primorial (succ n) = primorial n * bool_select_nat (beq (minFac (succ n)) (succ n)) (succ n) 1` |
| `Nat.min_fac_eq_self_of_prime` | `∀ n, prime_condition n → minFac n = n` |
| `Nat.prime_of_min_fac_eq_self` | `∀ n, 2 ≤ n → minFac n = n → prime_condition n` |
| `Nat.primorial_succ_of_prime` | `∀ n, prime_condition (succ n) → primorial (succ n) = primorial n * succ n` |
| `Nat.primorial_succ_of_not_prime` | `∀ n, 2 ≤ succ n → ¬ prime_condition (succ n) → primorial (succ n) = primorial n` |
| `Nat.primorial_pos` | `∀ n, 0 < primorial n` |
| `Nat.primorial_le_succ` | `∀ n, primorial n ≤ primorial (succ n)` |
| `Nat.primorial_mono` | `∀ m n, m ≤ n → primorial m ≤ primorial n` |

And in `nat_prelude/central_binomial.rs`, the arithmetic half of Erdős's odd
step, which is independent of everything above:

| name | statement |
| --- | --- |
| `Nat.mul_two_eq_add_self` | `∀ a, mul a 2 = add a a` |
| `Nat.le_of_add_self_le_add_self` | `∀ a b, add a a ≤ add b b → a ≤ b` |
| `Nat.four_pow_eq_two_pow_add_self` | `∀ m, pow 4 m = pow 2 (add m m)` |
| `Nat.choose_two_mul_succ_le_two_pow` | `∀ m, choose (succ (add m m)) m ≤ pow 2 (add m m)` |
| `Nat.choose_two_mul_succ_le_four_pow` | `∀ m, choose (succ (add m m)) m ≤ pow 4 m` |

The last is **strictly sharper** than what `Nat.choose_le_two_pow` already gave
at that row (`2^(2m+1) = 2 · 4^m`), and the factor of two is exactly what
Erdős's induction cannot afford. Two steps this prelude did not have came out
of it and are reusable: *two DISTINCT terms of a `sumRange` are together at
most the sum* (`le_sumRange_of_lt` was the one-term form), and `a + a ≤ b + b →
a ≤ b` (`le_of_add_le_add_right` cancels a COMMON summand and does not apply).

## What did NOT land, sized

**`Nat.primorial_le_four_pow : ∀ n, primorial n ≤ 4^n`** — Erdős's bound. Its
strong induction is available (`Nat.strongInduction`, ADR-1614) and its even
step is `primorial_succ_of_not_prime` above. The odd step is the whole cost and
it decomposes into two pieces, of which the first landed and the second did
not:

1. **`choose (2m+1) m ≤ 4^m`.** This one LANDED — see the table above.
2. **`(∏ {p prime, m+1 < p ≤ 2m+1}) ∣ choose (2m+1) m`.** This is the real
   obstruction. Each such prime divides the coefficient, but turning "each of
   these pairwise-distinct primes divides `N`" into "their product divides `N`"
   needs a *product over a predicate-restricted range* divisibility lemma with
   a coprimality side condition, and `subset_product.rs`'s own module doc
   records that `Nat.prodRange` has no permutation-invariance and no swap
   lemma (the `Int` counterparts span ~650 lines and "took three drafts to
   close"). Sizing: same order as `int_prelude/prod.rs`, i.e. a lane of its
   own, not an addition to this file.

Neither is a kernel-limitation finding. Both are expressible; the second is
simply large.

## Alternatives rejected

- **Bridge `Nat.isPrime` instead.** Rejected on cost, not on holdout grounds:
  the divisor-count characterisation is a real lemma and it buys nothing the
  `minFac` route does not already give. Note it is NOT forbidden — the module
  doc of `prime_counting.rs` records that no Mathlib row is named
  `Nat.isPrime` and no row's type mentions it, so a theorem about `isPrime`
  alone touches no held-out row.
- **State deliverable 2 over `Nat.countRange Nat.isPrime` to avoid naming
  `Nat.primeCounting`.** Rejected outright. `primeCounting' = count isPrime`
  and `count` is definitionally `countRange`, so this is the same term wearing
  a different name — a rendered-type dodge past a checker whose subject is the
  mathematics, not the spelling.
- **Give `primorial` a `2 ≤ i` conjunct in the predicate.** Rejected: it costs
  a `Bool` conjunction this prelude does not have, and the product is
  unchanged without it. The evaluation tests are what establish "unchanged".
