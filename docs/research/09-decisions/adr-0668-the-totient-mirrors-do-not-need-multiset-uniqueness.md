# ADR-0668: the remaining totient mirrors do not need multiset uniqueness

Status: accepted
Date: 2026-08-30
Index-summary: The Euler-product route to the three open `ml430` totient
mirrors needs unique factorisation, which this kernel cannot state; a
prime-peeling induction reaches all three using only *existence* of a prime
divisor plus Euclid's lemma. `Nat.totient_prime_pow` landed on that route.
Index-status: accepted

- **Lane:** `totient-prime-power`
- **Supersedes:** nothing. **Corrects:** the sizing in
  `docs/plan/status/349-totient-mul-finish.md` ("that framework does not
  exist here"), which was right about the *Euler-product* route and was read
  as a statement about the targets.

## Context

Three `ml430` mirrors remain in the `natural-totient` family, all
`partition: development` (re-checked before this lane touched them, 3 rows
found against a positive control):

    F:ml430-nat-totient-dvd-of-dvd-9622e44a
      ∀ a b, a ∣ b → φ(a) ∣ φ(b)
    F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7
      ∀ a b, φ(gcd a b) * φ(a*b) = φ(a) * φ(b) * gcd a b
    F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7
      ∀ a b, a ∣ b → φ(a) = φ(b) → a = b ∨ 2*a = b

`Nat.totient_mul_of_coprime` landed earlier the same day, and that lane
*measured* — rather than asserted — that multiplicativity is not sufficient
for any of the three. Its handoff then named the missing framework: a
prime-power totient value plus "a factorization product".

The classical way to get that product is the Euler formula
`φ(n) = n · ∏_{p|n} (1 − 1/p)`, and it needs the factorisation to be
**unique**. `nat_prelude/factorization.rs` has only the existence half, and
says in its own module doc why:

> This kernel has no `List`, `Finset`, or product type, so "the multiset of
> prime factors" is not expressible. […] Uniqueness needs multiset equality
> of the factor list, which needs a type this kernel does not have, and is
> **not attempted here**.

That is a real obstruction. The question this ADR answers is whether it is an
obstruction **to the three targets**, or only to one route to them.

## Decision

**It is only an obstruction to the Euler-product route. All three targets are
reachable without multiset uniqueness**, by a prime-peeling induction whose
only number-theoretic inputs are:

1. every `n > 1` has a prime divisor (`Nat.exists_prime_dvd`, already present
   — far weaker than unique factorisation);
2. Euclid's lemma, `p | a·b → p|a ∨ p|b` (`Nat.euclid_lemma`, already
   present);
3. `gcd(p·a, p·b) = p·gcd(a,b)` (`Nat.gcd_mul_right`, already present);
4. **the prime step** `φ(p·x) = p·φ(x)` if `p | x`, else `(p−1)·φ(x)`.

Only (4) was missing, and **it is now landed**, in the divisibility form the
two divisibility-shaped targets actually consume:

    Nat.totient_dvd_totient_mul_prime : ∀ x q, Prime q → φ(x) ∣ φ(x·q)

One case split on `Nat.coprime_or_dvd_of_prime`, whose two branches have the
*identical* shape and differ only in which product lemma supplies the rewrite:
`Nat.totient_mul_of_coprime` (landed by the `totient-mul-finish` lane) in the
coprime branch, `Nat.totient_mul_of_dvd` (landed by this lane) in the dividing
one.

**Why uniqueness drops out.** Each target is a statement that is *preserved
along a chain of prime steps*. The chain is built from **some** factorisation
of the cofactor, and every step is justified on its own terms; nothing ever
compares two factorisations, so nothing needs them to agree. Uniqueness would
be required only to evaluate a closed-form product, which none of these
arguments does.

### The three routes

Write `ε(x) = p` if `p | x`, else `p − 1`, so (4) reads `φ(p·x) = ε(x)·φ(x)`.

**Target 1** — `a ∣ b → φ(a) ∣ φ(b)`. Strong induction on `d = b/a`. If
`d = 1`, done. Otherwise take **any** prime `p | d`; step `a → a·p`,
`d → d/p`. Each step multiplies `φ` by `ε ≥ 1`, so divisibility is preserved,
and transitivity closes the chain.

**Target 2** — `φ(gcd) · φ(a·b) = φ(a)·φ(b)·gcd`. Strong induction on
`gcd(a,b)`, with the coprime base case being exactly the already-landed
`totient_mul_of_coprime` (`φ(1) = 1` and the trailing `gcd = 1` collapse it).
Peel a prime `p | gcd(a,b)`; with `a = p·a₁`, `b = p·b₁`, input (3) gives
`gcd(a,b) = p·gcd(a₁,b₁)`, so the measure strictly decreases. Applying (4)
four times reduces the whole identity to

    ε(a₁·b₁) · ε(gcd(a₁,b₁)) = ε(a₁) · ε(b₁)

which is a four-case truth table in `[p|a₁]`, `[p|b₁]` — and **the only place
primality is used**, via Euclid's lemma, because it is what makes
`p | a₁·b₁ ⟺ p|a₁ ∨ p|b₁`.

**Target 3** — `a ∣ b → φ(a) = φ(b) → a = b ∨ 2a = b`. Target 1's chain, with
the multiplier tracked: `ε = 1` exactly when `p = 2` and the current value is
odd. One such step makes the value even, so a second would contribute `ε = 2`.
Hence the chain has length 0 (`a = b`) or 1 with `p = 2` (`2a = b`).

### What landed on this route

`Nat.totient_prime_pow : ∀ p j, Prime p → φ(p^(j+1)) = p^(j+1) − p^j`,
axiom-free, together with the counting law under it:

    Nat.totient_mul_of_dvd : ∀ m e, Dvd e m → φ(m·e) = φ(m)·e

`totient_mul_of_dvd` carries **no primality, no positivity and no
factorisation** — the hypothesis is `e ∣ m` and nothing more. The prime power
follows by induction on the exponent with `Dvd p (p^(j+1))` supplied by
`Nat.dvd_mul_left`, because `pow` recurses on its exponent and `pow p (succ j)`
is *definitionally* `mul (pow p j) p`. No factor multiset is named anywhere.

## Consequences

- The three mirrors stay **open**, but their obstruction is now named
  correctly and is much smaller. Targets 1 and 3 need only the well-founded
  induction that chains `Nat.totient_dvd_totient_mul_prime` along a
  factorisation of the cofactor; Target 2 needs the ε truth table written as a
  four-leaf case split. That is ordinary work, not a type-theoretic wall, and
  no new number theory is required for any of it.
- **Do not size them against unique factorisation.** A handoff that says
  "needs a factorization product" is describing one route; this repository has
  now been bitten twice by promoting a route-local blocker into a claim about
  a target (see `CLAUDE.md`'s entry on `binaryRec` and `WellFounded.fix`).
- `factorization.rs`'s module doc stays exactly as it is. Uniqueness really is
  not expressible here; this ADR does not weaken that, it removes the three
  totient mirrors from the list of things that were thought to depend on it.

## Evidence

Every numeric claim above was checked in Python **before** any Rust, and is
re-executable:

    python3 scripts/tests/check-totient-prime-power-numerics.py

37 checks, 0 failed. Each positive check is exhaustive over its stated range;
each negative control is asserted to *genuinely* fail, and did:

| claim | check | control |
| --- | --- | --- |
| the gcd bridge needs `e ∣ m` | `3` | `3N` — fails at 165 non-dividing pairs |
| `φ(m·e) = φ(m)·e` for `e ∣ m` | `4` | `4N` — fails at 493 non-dividing pairs, smallest `(1,2)` |
| `φ(p^k) = p^k − p^(k−1)` | `5` | `5N` — fails at 42 composite `(c,k)`, smallest `c=4,k=1` |
| the prime step `φ(p·x) = ε(x)·φ(x)` | `6` | `6N` — fails at 488 composite multipliers |
| Target 1 | `7`, `7R` | `7N` — hypothesis load-bearing, fails at 2769 non-dividing pairs |
| **the ε identity Target 2 reduces to** | `8E` | `8EN` — **fails at 450 composite triples**, so Euclid is load-bearing |
| Target 2 | `8`, `8R` | `8N` — strictly stronger than multiplicativity at 53 non-coprime pairs |
| Target 3 | `9`, `9E`, `9T` | `9N` — hypothesis load-bearing |
| the prime step, as landed | `11` | `11N` — the TRANSPOSED divisibility, fails at 142 pairs |

Check `11V` is a control *about a control*, and it is the reason this lane did
not simply copy the composite check that discriminates `totient_prime_pow`.
`φ(x) ∣ φ(x·q)` is Target 1 specialised — `x` always divides `x·q` — so it is
**true at every composite `q` as well**, failing at zero of them. Primality is
a requirement of the proof *route*, not of the proposition, and a composite
control here would have been vacuous. The script measures that rather than
assuming it.

Check `10` is the one that speaks directly to *this ADR's* claim: it re-runs
Target 1's peeling induction with a **different** (greatest-first rather than
least-first) choice of prime divisor at each step and requires the same
verdict at every pair. If uniqueness were load-bearing, the two orders could
disagree. They do not — which is the numeric form of "the argument never needs
the factorisation to be unique".

The two prior scripts in this area were also re-run rather than inherited,
both exit 0:

    python3 scripts/tests/check-totient-mul-coprime-numerics.py
    python3 scripts/tests/check-countrange-bijection-numerics.py

Kernel side: `nat_prelude::` 200 passed, 0 failed; both new facts'
`checker_command`s run and were mutation-verified to discriminate (a
transposed factor order and a swapped divisibility direction each exit 1).

## Alternatives considered

- **Build multiset equality.** Rejected: it needs a `List`/`Finset` type, and
  ADR-0001's "add a boundary only when use proves it" applies. Nothing here
  needs it once the peeling route is available.
- **`n₂ = gcd(n, m^N)` for large `N` as a factorisation-free "m-part".** This
  is definable without any new type, and it does give the coprime
  decomposition. But proving its defining property still needs per-prime
  reasoning, so it buys nothing over peeling and costs a new definition —
  which the kernel could not tell us was wrong.
- **State the prime power subtractively and induct in that form.** Rejected:
  `Nat.sub` is truncated, so the inductive step would carry a `Le` side
  condition at every rung. The multiplicative form
  (`Nat.totient_pow_succ_of_prime`) is the induction and the subtractive form
  is a one-step corollary through `Nat.add_sub_cancel_left`.
