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

The two gates that fire at push do not forbid what the brief asked for.
`check-autogenesis-holdout-isolation.py` forbids *settling* a held-out fact or
*referencing* its id; `4^n ≤ (2n+1) · (2n)^(π(2n))` is neither. But
`check-holdout-adjacency.py`'s own docstring names the shape this would be —
**shape 2, a differently-named theorem**, "our development proves the same
proposition under another name, so R9's exact-name comparison sees nothing" —
and the route to `choose 2n n ≤ (2n)^(π(2n))` runs through monotonicity of
`Nat.count` at `isPrime`, which is `Monotone Nat.primeCounting'` under another
name. ADR-0653 states the rule the incident established: *a family may be blind
only if its mathematics is unpublished*, and R9 is a proxy for it.

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

## What did NOT land, sized

**`Nat.primorial_le_four_pow : ∀ n, primorial n ≤ 4^n`** — Erdős's bound. Its
strong induction is available (`Nat.strongInduction`, ADR-1614) and its even
step is `primorial_succ_of_not_prime` above. The odd step is the whole cost and
it decomposes into two pieces that are NOT in this prelude:

1. **`choose (2m+1) m ≤ 4^m`.** `Nat.sum_choose_row` gives
   `∑_{k ≤ 2m+1} choose (2m+1) k = 2^(2m+1)` and `Nat.choose_symm_of_eq_add`
   gives `choose (2m+1) m = choose (2m+1) (m+1)`, so the missing step is *two
   DISTINCT terms of a `sumRange` are together at most the sum*.
   `Nat.le_sumRange_of_lt` is the one-term form; the two-term form is
   reachable from `Nat.sumRange_split` (split at `m`, then split the tail at
   `2`) plus `le_of_mul_le_mul_left`. Estimated small — one lemma and a
   cancellation.
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
