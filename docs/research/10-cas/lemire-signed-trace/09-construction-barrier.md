# The construction barrier: what the provable toolbox can and cannot reach

Status: research note, 2026-08-22, **rewritten**. The first version of this note
stated the barrier correctly in outline and wrongly in two of its lemmas; both
errors are corrected below and the density corollary is redone for the union
over all seeds. Concrete claims machine-checked in the lane's Rust `GF(2)` CAS
with python-flint as an independent cross-check
(`scripts/lemire-signed-trace/lemire_composition_family.py`, controls 1--5).
This is the third barrier -- moduli (note 03 section 5), symmetry (note 06),
construction (here).

## Correction to the first version

Two lemmas were wrong, and both were used to conclude that the construction
route was exhausted at `n = 2*3^k`.

1. **"Monomial composition `f(x^k)` is in-window only for degree-2 seeds."**
   False. Monomial substitution scales the tail and the degree by the *same*
   factor, so it is in-window for **every** seed and every `t >= 1`
   (`deg(f(x^t) - x^{mt}) = t*deg(f - x^m) <= t*floor(m/2) <= floor(mt/2)`).
   Note 08 Theorem A is the corrected statement, and it yields odd degrees
   (`n = 3*7^k`) as well as even ones.
2. **"For `g = x^d + r` non-monomial, `f(g)` has `tail >= d(n-1) > nd/2`, so the
   only survivor is the seed `x^2+x+1`."** False as stated. Over `F_2`,
   `(x^d + r)^m = ((x^d + r)^{lsb(m)})^{m/lsb(m)}` and
   `(x^d+r)^{lsb(m)} = x^{d*lsb(m)} + r^{lsb(m)}`, where `lsb(m)` is the least
   power of two in the binary expansion of `m`. So for a monic substitution
   `sigma = x^k + (tail of degree s)` the second layer of `f(sigma)` sits at
   degree

   ```
   k*m - (k - s) * lsb(m),
   ```

   (the lower terms of `f` contribute only at degrees `<= k*floor(m/2) <= km/2`,
   so they cannot raise it, and cancellation could in principle lower it), and
   `f(sigma)` is in-window **iff** `(k - s) * lsb(m) >= ceil(km/2)`. For a
   non-monomial `sigma` this forces `k*lsb(m) >= km/2`, i.e. `lsb(m) >= m/2`,
   i.e. `m` a **power of two** -- not `m = 2`. Machine-checked (control 3b):
   over the certified in-window seeds of degrees `2..12` and `16` and all monic
   `sigma` of degree `2..5` with a nonzero tail, the tail formula is exact and
   the seed degrees admitting an in-window non-monomial composition are exactly
   `{2, 4, 8, 16}`. The first version's own example
   `(x^4+x+1)(x^2+x) = x^8+x^4+x^2+x+1` is in-window and contradicts its lemma
   in the same paragraph that states it.

   This is not new to the repository: it is `composition_shape_criterion` in the
   lane's own Rust CAS (`axeyum_cas::gf2`), with the `least_binary_place` field
   and the `classified_shape_criterion` "monomial, or power-of-two `n` and
   shaped `sigma`". The library had it right; the note did not.

**The barrier's conclusion survives both corrections** -- every construction is
still degree-multiplicative -- but its proof and its counting had to be redone,
and the corrected version is sharper and says something the first version did
not: the obstruction is at **prime** `n`.

## Barrier III, stated precisely

Fix the **provable toolbox** `T`: the constructions over `F_2` for which an
irreducibility criterion is known and checkable.

| construction | hypotheses | output degree |
| --- | --- | --- |
| monomial composition `f -> f(x^t)` | `rad(t) \| e`, `gcd(t,(2^m-1)/e)=1` (LN 3.35) | `m*t`, `t >= 2` |
| general composition `f -> f(sigma)`, `deg sigma = k` | Cohen-type criteria (theorem number not verified by this lane) | `m*k`, `k >= 2` |
| Meyn `R`-transform `f -> x^m f(x + x^{-1})` | Meyn's trace condition | `2m` |
| `Q`-transform `f -> f(x^2+x)` | trace condition | `2m` |
| Moebius / `PGL_2(F_2)` | always | `m` (degree-preserving) |
| composed products (Brawley--Carlitz) | `gcd(m_1,m_2)=1` etc. | `m_1 * m_2` |
| Cohen/Kyuregyan recursive `f -> h^m f(g/h)` | explicit trace conditions | `m * max(deg g, deg h)` |
| cyclotomic `Phi_M` (and its factors) | `2` primitive root mod `M` (factors: degree `ord_M(2)`) | `phi(M)` (resp. `ord_M(2)`) |
| Carlitz--Drinfeld cyclotomic | Euclid/Carlitz torsion | multiple of `deg F` |
| norm from `F_{2^k}[x]` to `F_2[x]` | `gcd` conditions | `m*k`, `k >= 2` |

**(B0) Degree-multiplicativity.** Every row produces a degree that is a proper
multiple of a smaller input degree, or is degree-preserving, or is `phi(M)` /
`ord_M(2)` for a cyclotomic modulus. Structurally: a fixed algebraic recipe
`rho` of degree `e` applied to a root `alpha` of a degree-`n` irreducible
produces `beta = rho(alpha)` with `F_2(beta) subset F_{2^{ne}}`, so
`[F_2(beta):F_2]` divides `ne`.

**(B1) Prime-`n` blocker.** Let `n >= 5` be prime. No construction in `T`
produces an irreducible of degree `n` from data of smaller degree.

*Proof.* Row by row. Monomial composition, general composition, composed
products, recursive `h^m f(g/h)` and the norm all give a degree `m*k` with
`k >= 2`; `n` prime forces `m = 1`, and a degree-1 seed is `x` or `x+1`, of
order `1`, so hypothesis (i) `rad(t) | e = 1` fails for every `t >= 2` (monomial
case) and the other cases return the substitution itself rather than a new
polynomial. The `R`- and `Q`-transforms and the norm with `k = 2` give even
degree, never prime for `n >= 3`. Moebius maps preserve the degree, so they
reach no degree not already realized -- this is exactly the orbit of size
`<= 2` of Barrier II. For cyclotomic `Phi_M`: `phi(M)` is prime only for
`phi(M) = 2`, i.e. `M in {3,4,6}`, giving degree `2`. For an irreducible
*factor* of `Phi_M` of degree `ord_M(2) = n`: every irreducible of degree `n`
divides `Phi_{ord(root)}`, so this is a tautology and not a construction -- the
modulus `M` carries no information about the window (see "Directions closed").
Carlitz--Euclid overshoots to degree `~2^ell deg F` (note 02 section 5C). `QED`

**(B2) Power-of-two blocker.** `n = 2^a` is never reached by monomial
composition, because `e | 2^m-1` is odd, so hypothesis (i) forces `t` odd.
(Independently, Swan's theorem gives *no* irreducible trinomial at all when
`8 | n`, so those degrees need pentanomial-or-denser witnesses; the committed
witness table is about half pentanomials for this reason.)

**(B3) Lacunarity, corrected.** The first version's "a lacunary set `{n_0 c^k}`
has at most `log_c X` elements below `X`" is the count for a *single geometric
progression*, which is not what a seed generates. For a seed `f` of degree `m`
with admissible prime set `A(f)` (note 08), the reachable multipliers are the
`A(f)`-smooth-and-supported integers, so

```
#{ t <= X : rad(t) subset A(f) }  <=  prod_{p in A(f)} (1 + log X / log p)
                                  <=  (1 + log_2 X)^{omega}, omega = |A(f)|,
```

and summing over a ledger `L` of seeds,

```
#S(L, N)  <=  sum_{m in L} max_{f of degree m} prod_{p in A(f)} (1 + log(N/m)/log p).
```

For a **fixed finite** ledger this is `O((log N)^W)` with `W = max_f |A(f)|`,
hence density zero. That is what is *proved*.

**(B4) What is only observed, and why the observation is not a density.** For
`N` inside the range where the ledger itself grows -- this lane certifies an
in-window seed for every `m <= 3000`, so every composite `n <= 6000` has all of
its proper divisors in the ledger -- the measured coverage is a substantial
*fraction*, not a vanishing one (see note 08's table). That is not evidence
against (B3); it is the statement that `(log N)^W` has not started to lose to
`N` yet. Measured on this ledger, `W = max_f |A(f)| = 16` (first attained at
`m = 360`) and the bound of (B3) evaluates to `6.5e7` at `N = 10^5`: it exceeds
`N` and is therefore vacuous over the whole computed range. Density zero here is
*proved asymptotically and not observed*, and saying otherwise would be reading
a `(log N)^16` into a table that stops at `10^5`. The temptation to read it as positive
density is exactly the circularity the barrier is about: "a positive proportion
of `m` have an in-window seed" **is** Kaser--Lemire. Theorem A multiplies a
known answer; it does not produce one.

**(B5) The reduction.** Combining (B1)--(B3): the construction angle reduces the
conjecture to the degrees it cannot reach -- the primes, the powers of two, and
those composites `n` every one of whose proper divisors `m` fails to carry an
in-window seed whose admissible primes contain all primes of `n/m` -- and stops.
No enlargement of the toolbox within `T` changes this, because every row of the
table is degree-multiplicative.

## Honest scope

Barrier III rules out the *known* provable toolbox as listed. It is **not** a
logical impossibility theorem: a genuinely new construction that produced a
prime degree from smaller data, or a seed family whose degrees run in an
arithmetic progression, would evade it. No such construction or seed family is
known. What has changed relative to the first version is that the barrier is now
located precisely -- at prime `n`, where every row of the table is silent for a
structural reason (`n = m*k` has no factorization with both factors `>= 2`) --
rather than asserted as "no positive-density family exists".

## Does the norm map destroy the window? Yes (checked)

The norm `N: F_{2^k}[x] -> F_2[x]`, `N(f) = prod_{i<k} f^{(2^i)}` (Frobenius on
coefficients), multiplies the degree by `k`. If `f = x^n + g` over `F_{2^k}` with
`g != 0`, the top two layers of the product are `x^{nk}` and the sum of the
`k` terms `x^{n(k-1)} g^{(i)}`, so the second layer sits at degree
`n(k-1) + deg g`. In-window would need

```
n(k-1) + deg g <= nk/2   <=>   deg g <= n(1 - k/2),
```

which for `k >= 2` forces `deg g <= 0`: only a **constant** tail survives.
Verified (control 4a): over `F_4`, `N(x^3 + w x + 1)` has degree `6` and tail
degree `4 > 3`, matching the prediction `n(k-1) + deg g = 4`. And the surviving
constant-tail case is not new: for `c` of order `3` in `F_4`,
`N(x^n + c) = (x^n + c)(x^n + c^2) = x^{2n} + x^n + 1`, which is the `m = 2`
family of note 08 again (control 4b). So the norm route adds nothing.

## Directions closed (exact scans, unchanged)

- **Cyclotomic `Phi_M` irreducible and in-window:** scan of all odd `M <= 2000`
  with `2` a primitive root mod `M` -- only `M in {3,9,27,81,243,729}`, i.e. the
  degrees `n = 2*3^k`. Forced: `(Z/M)^x` cyclic needs `M = p^a`; the second term
  of `Phi_{p^a}` sits at degree `(p-2)p^{a-1} <= phi/2` iff `p <= 3`, and `p = 2`
  is reducible. (Correct as stated -- but "the unique cyclotomic family" is not
  "the unique provable family", which is where the first version of note 08 went
  wrong.)
- **Factors of `Phi_M`:** in-window irreducible factors are exactly the known
  low-weight witnesses; every irreducible divides some `Phi_{ord(root)}`, so this
  is tautological and `M` does not predict the window. For prime `n` the root of
  an in-window irreducible has order a divisor `d` of `2^n-1` with
  `ord_d(2) = n` -- generically `2^n-1` itself -- so the relevant modulus is a
  large generic one with no small-conductor structure.
- **Artin--Schreier `x^{2^s}+x+1`:** irreducible only for `s = 1,2`; general
  `x^n+x+1` irreducible for a sparse set whose infinitude is open.
- **Trinomials `x^n + x^k + 1`, `k <= n/2`, general `n`:** whether infinitely
  many are irreducible is *open* (unsourced here -- the first version cited
  Brent--Zimmermann arXiv:2105.06013, which is about *almost*-irreducible
  trinomials at Mersenne exponents and is not about this question). Theorem A
  settles exactly the compositional sub-family.
- **Carlitz/Drinfeld cyclotomic:** the Euclid/Carlitz argument yields
  irreducibles of degree `~ 2^ell deg F`, overshooting (note 02 section 5C).
- **Composition with a linearized `L`:** a special case of the shape criterion
  above; window survives only for power-of-two seed degrees, and the degrees are
  `deg L * m`, still multiplicative.
- **Swan/parity as a lower bound:** Swan's theorem gives only the parity of the
  factor count. Swan-odd yet reducible (`>= 3` factors) trinomials are abundant
  in-window -- first instances `(n,k,#factors) = (10,5,3), (12,1,3), (13,2,3),
  (14,1,3), ...` -- and separating `r = 1` from odd `r >= 3` needs a
  smallest-factor bound that does not hold. Swan proves only *negative* results.

## Literature ceiling: what is actually known about prescribed coefficients

The window prescribes the top `ell = ceil(n/2)-1` coefficients of a degree-`n`
irreducible, all of them zero. Three different quantities get called "the
prescribed-coefficient ceiling", they differ by more than a constant, and the
first version of this note quoted the wrong one.

- **Top (leading) positions, any `q` -- the relevant one.** Hayes (1965) plus
  Weil give, in the sharp explicit form of Hsu (1996, Thm 2.4) = Cohen (2005,
  Thm 2.1) as quoted by Gao (arXiv:2109.14154, Cor. 2),

  ```
  #{ f monic irreducible of degree n with its top l coefficients prescribed }
        >=  q^{n-l}/n  -  (l+1) * q^{n/2}/n,
  ```

  positive exactly when `l < n/2 - log_q(l+1)`. At `q = 2` the top
  `n/2 - log_2 n` coefficients are therefore prescribable **unconditionally**,
  while Kaser--Lemire asks for `ceil(n/2)-1`. **The entire gap is `~log_2 n`
  coefficients.** Measured shortfall (prescribable `l` vs required `ell`):
  `n = 64`: `27` vs `31`; `n = 1024`: `503` vs `511`; `n = 4096`: `2037` vs
  `2047`. Gao remarks that the bound goes negative at `l >= ceil(n/2)` -- Weil
  stops there structurally, not incidentally. Pollack's Prop. 10 is the same
  input in the form "any `s` low plus `t` high coefficients with
  `s + t <= (1/2 - eps) n`, all `q`".
- **Arbitrary positions, fixed `q`.** Pollack, *Irreducible polynomials with
  several prescribed coefficients*, Finite Fields Appl. **22** (2013) 70--78:
  `floor((1-eps) sqrt n)` coefficients in arbitrary positions, uniformly in `q`.
  Ha, same title, Finite Fields Appl. **40** (2016) 10--25: `(1/4 - eps) n`
  arbitrary positions, but only for `q >= q_0(eps)`; at arbitrary `q` his Thm
  1.3 gives `r <= n/10` for `n >= 52`, i.e. `delta = 1/10` at `F_2`.
  Garefalakis (2008): `(1/3 - eps) n` *consecutive* coefficients set to zero, in
  any position.

So the first version's sentence -- "the provable prescribed-coefficient ceiling
at `q = 2` is `sqrt n`, far below `n/2`" -- is **wrong as stated**. `sqrt n` is
the *arbitrary-position* ceiling; the ceiling for the *top* positions, which is
what the window is about, is `n/2 - log_2 n`. The correct statement, and the one
that should replace it in note 00:

> Kaser--Lemire is `log_2 n` coefficients past what Weil proves. It is exactly
> the classical square-root barrier -- RH gives short intervals of length
> `sqrt(X) log X` where Legendre needs `sqrt(X)` -- transplanted to `F_2[t]`.

Two consequences for the lane.

1. **The gap is a log factor, not a power.** That is a *stronger* reason to work
   the analytic side (notes 05 and 07, and the roadmap's `(HWO)`), not a weaker
   one: the saving required over Weil is the roadmap's factor `~4 ell`, i.e.
   logarithmic in `X`, which is exactly the shape of the missing estimate.
2. **These are counting theorems, not constructions.** They are character-sum
   and sieve results, they exhibit no explicit family, so they are not part of
   the toolbox `T` and Barrier III does not touch them. The explicit route stops
   at multiples of known degrees; the analytic route stops `log_2 n` short. The
   two stop for different reasons and neither is repaired by enlarging the other.

The same inequality gives the trivial-field boundary: the window is nonempty by
Weil alone once `q > n/2` (even `n`) or `q > (n+1)^2/4` (odd `n`). Kaser--Lemire
is a theorem for every fixed field except the smallest ones, and `q = 2` is the
extreme case. The barrier is not broken at fixed `q` anywhere in the literature:
Bank--Bary-Soroker--Rosenzweig (Duke 2015) is `q -> infinity` at fixed degree,
and Sawin--Shusterman (Ann. Math. 2022) needs odd `p` and `q > 685090 p^2`.

*Sourcing note: the statements in this section come from a literature sweep run
for this lane (secondary sources except Pollack 2013 and the arXiv v1 of Ha
2016, which were read directly). Numbering and constants should be re-checked
against the primary sources before they are quoted outside this repository.*

## The four sides, mapped

- **Averaging** -> the almost-all theorem (note 05): all but `< 4 ell^2 2^{-ell}`
  patterns realized.
- **Symmetry** -> barrier (note 06): no action moves the identity class
  (orbit `<= 2`).
- **Phase correlation** -> isolated (note 07): the one unblocked analytic target,
  not reachable at fixed `q`; the Witt carry collapses to Weil above Kerdock.
- **Construction** -> barrier (here): the toolbox is degree-multiplicative, so it
  transports Kaser--Lemire from known degrees to their multiples (note 08,
  Theorem A) and is structurally silent at prime `n`. For a fixed finite seed
  ledger the reachable set has counting function `O((log N)^W)`, density zero.

Each side goes exactly as far as it can and stops at the same wall: a
phase-aware cancellation estimate for a complete character family at fixed
`q = 2` and growing conductor, whose integer analogue is conditional (GRH +
pair correlation) and whose function-field analogues are all `q -> infinity`.
