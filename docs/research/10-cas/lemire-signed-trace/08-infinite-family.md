# The monomial-composition window family: Lemire at every n = m*t

Status: research note, 2026-08-22, **rewritten**. The first version of this note
claimed `n = 2*3^k` was the only provable infinite family and that monomial
composition stays in-window only for degree-2 seeds. Both are false. The theorem
below is the correct general statement; the old family is its `m = 2` case. The
theorem is proved and machine-checked in two independent engines (the lane's
Rust `GF(2)` CAS as producer, python-flint as cross-check); the script is
`scripts/lemire-signed-trace/lemire_composition_family.py` and the ledger fact is
`F:gf2-lemire-monomial-composition-family`.

Nothing here is new mathematics. Theorem A is a textbook irreducibility criterion
plus a one-line observation about the window, applied to this lane's certified
seed ledger. What it buys is stated honestly in "Status" at the end: density
zero, never a prime `n`, and no approach to the all-`n` statement.

## The conjecture

Kaser and Lemire, *Strongly universal string hashing is fast*, Comput. J.
**57**(11) (2014), arXiv:1202.4961, section "GF Multilinear": for every `L`
there is an irreducible polynomial of degree `L` over `GF(2)` all of whose
non-leading terms have degree at most `floor(L/2)`. They verified it for
`L in {1..400}` from Arndt's table and conjectured it in general; the motivation
is Barrett reduction in a string-hashing kernel. The conjecture was first
posed publicly by Lemire on MathOverflow ("Can we always find such an
irreducible polynomial of degree `n` where `degree(p(x)-x^n) <= n/2`?",
23 Nov 2011). In that thread Elkies and Zaimi state the expected truth
(subdegree `O(log n)`), Ellenberg gives the Legendre / Cramer-under-RH
framing (`n/2 + log n` is what RH buys), Voloch notes Cohen's
prescribed-coefficient bound stops at `m < n/2 + O(log n)`, and **Emil
Jerabek already gives the `n = 2*3^k` family `x^{2*3^k}+x^{3^k}+1`** (an
exercise in Lidl--Niederreiter, per Lahtonen). So the `m = 2` case below has
2011 priority on MathOverflow; nothing in this note is new mathematics.

## Theorem A

Let `f` be irreducible over `F_2` of degree `m` with `f(0) != 0` and order
`e = ord(f)` (the multiplicative order of a root in `F_{2^m}^x`), and suppose `f`
is **in-window**, i.e. `deg(f - x^m) <= floor(m/2)`. Let `t >= 2` satisfy

- (i) `rad(t) | e` -- every prime divisor of `t` divides `e`; and
- (ii) `gcd(t, (2^m-1)/e) = 1`.

Then `f(x^t)` is an **in-window irreducible** of degree `mt` and order `et`.
Hence Kaser--Lemire holds at `n = mt`.

### Proof

*Irreducibility* is Lidl--Niederreiter, *Finite Fields* (Encyclopedia of
Mathematics and its Applications 20), 2nd ed., **Theorem 3.35**. The book states
it in the *exhaustive* form: if `f_1, ..., f_N` are all the distinct monic
irreducibles over `F_q` of degree `m` and order `e`, and `t >= 2` has every prime
factor dividing `e` but not `(q^m-1)/e` (and `q^m = 1 mod 4` when `4 | t`), then
`f_1(x^t), ..., f_N(x^t)` are all the distinct monic irreducibles of degree `mt`
and order `et`. The single-polynomial "iff" form used here is Handbook of Finite
Fields, **Thm 3.2.5** (after Menezes et al. 1993); the exhaustive statement of
LN 3.35 implies the direction we need. At `q = 2` the fourth hypothesis is
vacuous: `e | 2^m-1` is odd, so (i) already forces `t` odd.

*The window is the one-liner.* Monomial substitution scales the tail and the
degree by the **same** factor:

```
f(x^t) - x^{mt} = (f - x^m)(x^t),   so
deg(f(x^t) - x^{mt}) = t * deg(f - x^m) <= t * floor(m/2) <= floor(mt/2),
```

the last inequality holding for **every** `t >= 1` (equality when `m` is even;
for `m` odd it is `t(m-1)/2 <= (mt-1)/2`, i.e. `t >= 1`). So a monomial
substitution can never leave the window, whatever the seed. Machine-checked for
all `m < 200` and all odd `t < 200` (control 3 of the script). `QED`

The window therefore costs nothing: every hypothesis of Theorem A is about
irreducibility alone.

## The criterion, without factoring `2^m-1`

Hypotheses (i) and (ii) collapse into one condition per prime. Write
`v_p` for the `p`-adic valuation and `M = 2^m-1`. Then

```
rad(t) | e  and  gcd(t, M/e) = 1
  <=>  for every prime p | t:  p | e  and  p nmid M/e
  <=>  for every prime p | t:  v_p(e) = v_p(M) >= 1
  <=>  for every prime p | t:  p | M  and  x^{M/p} != 1  in  F_2[x]/(f).
```

The last line is the operational form and it needs **no factorization of
`2^m-1`**: it is one modular exponentiation per candidate prime. (`v_p(e) <
v_p(M)` is exactly `e | M/p`, i.e. `alpha^{M/p} = 1` for a root `alpha`.) This is
also what the lane's Rust CAS computes -- `monomial_prime_eligibility` /
`root_is_not_prime_power` in `axeyum_cas::gf2` -- which attributes the passage
from `x^t - alpha` irreducible over `F_{2^m}` to `f(x^t)` irreducible over `F_2`
to Capell's lemma.

Deciding whether a *given* prime `p` can occur in `t` is likewise cheap:

```
p | 2^m-1   <=>   ord_p(2) | m,
```

so the candidate primes for a seed of degree `m` are found by a table of
`ord_p(2)`, and only the `x^{M/p} != 1` test is polynomial work. Call the
resulting set

```
A(f) = { p prime : p | 2^m-1 and x^{(2^m-1)/p} != 1 mod f }
```

the **admissible primes of the seed** `f`. Theorem A applies to exactly those
`t >= 2` all of whose prime factors lie in `A(f)`.

### Corollary (primitive seeds)

If `f` is *primitive*, i.e. `e = 2^m-1`, then `(2^m-1)/e = 1` and condition (ii)
is vacuous, so `A(f)` is the full set of prime divisors of `2^m-1` and Theorem A
applies to every `t >= 2` with `rad(t) | 2^m-1`. This is the best possible seed
at its degree, and no other seed of degree `m` enlarges the reachable set.

## Instances

| seed `f` | `m` | `e` | `A(f)` | degrees reached |
| --- | --- | --- | --- | --- |
| `x^2+x+1` | 2 | 3 | `{3}` | `n = 2*3^k`, `k >= 1` |
| `x^3+x+1` | 3 | 7 | `{7}` | `n = 3*7^k` (**odd**) |
| `x^4+x+1` | 4 | 15 | `{3,5}` | `n = 4*3^a*5^b` |
| `x^5+x^2+1` | 5 | 31 | `{31}` | `n = 5*31^k` (**odd**) |
| `x^6+x+1` | 6 | 63 | `{3,7}` | `n = 6*3^a*7^b` |
| `x^8+x^4+x^3+x^2+1` | 8 | 255 | `{3,5,17}` | `n = 8*3^a*5^b*17^c` |
| `x^9+x^4+1` | 9 | 511 | `{7,73}` | `n = 9*7^a*73^b` (**odd**) |
| `x^10+x^3+1` | 10 | 1023 | `{3,11,31}` | `n = 10*3^a*11^b*31^c` |
| `x^12+x^6+x^4+x+1` | 12 | 4095 | `{3,5,7,13}` | `n = 12*3^a*5^b*7^c*13^d` |

The `m = 2` row **is** the old note-08 family: `x^2+x+1` composed with `x^{3^k}`
is `x^{2*3^k} + x^{3^k} + 1 = Phi_{3^{k+1}}`, and Theorem A reproves
Fredricksen--Wisniewski's "`x^{2k}+x^k+1` irreducible over `GF(2)` iff `k` is a
power of `3`" in one direction. The `m = 3`, `m = 5` and `m = 9` rows give **odd**
`n`, which the first version of this note said was impossible ("every cyclotomic
degree `phi(m)` is even"). Explicit odd witnesses, all verified irreducible and
in-window by both engines: `x^21+x^7+1`, `x^147+x^49+1`, `x^1029+x^343+1`,
`x^{7203}+x^{2401}+1` (`m = 3`), and `x^{155}+x^{62}+1` (`m = 5`, `t = 31`).

## Coverage: what the theorem reaches, exactly

Applied to a **ledger of known seeds** `L` -- for this lane, one certified
in-window irreducible for every degree `m <= 3000`, plus every in-window
irreducible found by a bounded per-degree search -- Theorem A proves
Kaser--Lemire on

```
S(L, N) = { m*t <= N : m in L, t >= 2, rad(t) subset A(f) for one seed f of degree m }.
```

Note the quantifier: the primes of a single `t` must all be admissible for **one**
seed; mixing seeds of the same degree is not allowed. The script computes
`S(L, N)` exactly for `N = 10^5` and re-verifies members by direct irreducibility
testing that shares no logic with the criterion.

### Coverage table (exact; `data/composition-coverage.txt`)

Seeds: the certified in-window irreducible for every degree `m <= 3000`, plus
every in-window irreducible found by a bounded per-degree candidate search
(exhaustive below degree 22, then trinomials, then pentanomials), at most 12
distinct seeds per degree.

| `N` | `#(S cap [1,N])` | `#S/N` | composites `<= N` | fraction of composites covered |
| --- | --- | --- | --- | --- |
| `10^2` | 22 | 0.2200 | 74 | 0.297 |
| `10^3` | 243 | 0.2430 | 831 | 0.2924 |
| `10^4` | 2086 | 0.2086 | 8770 | 0.2379 |
| `10^5` | 8394 | 0.0839 | 90407 | 0.0929 |

- **Smallest composite not in `S`: `4`** (then `8, 9, 10, 14, 15, 16, 22, 25,
  26, 27, 28, 32, 33`). Smallest **odd** composite not in `S`: `9` (then
  `15, 25, 27, 33, 35, 39, 45, 49, 51, 55, 57`). `4 = 2*2` fails because the
  only degree-2 seed has order `3` and `t = 2` violates (i); `9 = 3*3` fails
  because the only degree-3 seeds have order `7`.
- **No prime is in `S`** and **no power of two is in `S`** (both asserted by the
  script): `n = mt` with `t >= 2` is composite, and (i) forces `t` odd.
- **The density falls only once `N` passes `2 * 3000`.** Every composite
  `n <= 6000` has all of its proper divisors inside the certified ledger, so the
  coverage there is the true value for this seed set; beyond it, divisors above
  `3000` are simply unavailable and the measured fraction drops. That drop is an
  artefact of the ledger, and so is the apparently healthy `~0.24` before it:
  see note 09 `(B4)`.
- **Proved asymptotics.** `W = max_f |A(f)| = 16` over this ledger (first
  attained at `m = 360`), so `#S(L,N) = O((log N)^16)` and the density tends to
  zero -- but the implied constant is enormous and the bound
  `sum_m prod_{p in A(f)} (1 + log(N/m)/log p)` evaluates to `6.5e7` at
  `N = 10^5`, i.e. it is vacuous over the entire computed range. Honest
  statement: density zero is **proved asymptotically and not observed**.
- Most productive seed degrees: `m = 24, 12, 48, 36, 20, 8, 16, 40, 96, 72`
  (highly composite `m`, because `2^m-1` then has many prime factors). Most
  frequent multipliers: `t = 3, 27, 9, 7, 31, 49, 5, 25, 81, 23, 17, 15`.

**Re-verification.** 411 members are re-verified by a *direct* irreducibility
test of `f(x^t)` -- a Rabin certificate produced and replay-checked in the Rust
CAS -- with degrees from `6` to `20000`, and 220 of those are re-derived a third
time by python-flint's independent Rabin test; the script asserts the two engines
agree and that every witness is in-window. The `20000` cap is on the *sample*,
not on the coverage set: a Rabin chain over a dense modulus costs
`~degree^3/64` word operations. Individual larger members were checked by hand
and pass -- `m = 3, t = 16807` (degree `50421`), `m = 12, t = 8125` (degree
`97500`), `m = 2, t = 3^10` (degree `118098`).

The full membership table for `n <= 10^4` -- each member with its `(m, t, seed)`
-- is `data/composition-coverage-members-1e4.txt`; every `n` not listed there is
not in `S`.

## Status

Honest accounting of what this is:

- **It is a textbook theorem applied to a certified seed ledger, not a new
  idea.** The irreducibility half is Lidl--Niederreiter Thm 3.35 (with Capell's
  lemma behind it); the contribution is the observation that monomial
  substitution is exactly window-preserving, so the theorem transports
  Kaser--Lemire from a seed degree to all its admissible multiples.
- **Density zero.** For a *fixed finite* ledger `L`, `#S(L, N)` is bounded by
  `sum_{m in L} prod_{p in A(f_m)} (1 + log(N/m)/log p) = O((log N)^W)` with
  `W = max_m |A(f_m)|`. Any coverage fraction measured in a finite range is an
  artefact of the ledger growing with the range, not a density (note 09,
  Barrier III).
- **Never a prime `n`, never a power of two.** `n = mt` with `t >= 2` forces `n`
  composite, and (i) forces `t` odd, so `2^a` is never reached. The prime-`n`
  blocker of note 09 says no construction in the known provable toolbox does
  better.
- **It does not approach the all-`n` statement**, which still needs the
  phase-aware estimate of the roadmap (`F:gf2-lemire-cylinder-twist-sup-bound`).
- **And the truth is far stronger than what it proves.** In Arndt's
  `lowbit-irredpoly.txt` the *minimal* subdegree of an in-window irreducible is
  `<= 10` for every `n <= 400` -- it tracks `~log_2 n`, not `n/2`. Theorem A
  produces witnesses whose tail sits at exactly `t*deg(f - x^m)`, i.e. at the
  top of the window, so it is nowhere near the observed behaviour. The analytic
  ceiling matches the observation better: the top `n/2 - log_2 n` coefficients
  are prescribable unconditionally by Hayes/Weil, and Kaser--Lemire is the last
  `~log_2 n` of them (note 09, "Literature ceiling").

## What the first version of this note got wrong

Recorded because the errors were load-bearing in notes 00 and 09.

1. "`Phi_{3^{k+1}}` is the **unique** cyclotomic window family, and it is the
   only provable one." The uniqueness *among cyclotomic polynomials* is right;
   the conclusion that it is the only provable family is wrong. Every in-window
   seed generates one.
2. "The family gives only even `n`, so it does not touch the odd endpoint."
   Wrong: `m = 3` gives `n = 3*7^k`, all odd.
3. "Monomial composition `f(x^k)` is in-window only for degree-2 seeds." Wrong
   in the strongest way -- monomial composition is in-window for *every* seed,
   because the tail and the degree scale by the same factor. This sentence,
   carried into note 09, was the reason the construction route was declared
   exhausted at `n = 2*3^k`.
