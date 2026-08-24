# Angle 10: derandomization, explicit constructions, recursive irreducible families

Ad hoc blocker sweep, 2026-08-20.  Agent: field specialist #10
(constructive/derandomization angle).  Scope: EXPLICITLY outside the roadmap
and gates.  Nothing here is a theorem unless labelled PROVED with a proof
sketch; finite computation is evidence only.

Target: for every `n >= 1` there is a monic irreducible `f in GF(2)[x]` of
degree `n` with `deg(f - x^n) <= floor(n/2)` ("shaped" irreducible).

## 00:00 -- orientation: what the ledger already closed

Read (in order): `lemire-review-2026-08-20-reaim.md`,
`docs/plan/status/52-gf2-lemire.md`,
`lemire-half-degree-irreducibles.md` (construction block at lines ~2040-2250),
`lemire-proof-unblocking-bridges.md`.

Closed constructive routes, with the exact mechanism that kills each (I restate
the mechanism because my charge is to catalogue *mechanisms*, not results):

| route | mechanism of failure |
| --- | --- |
| standard Q-transform `Q(f)=x^n f(x+1/x)` | output is **self-reciprocal**; half-shape + reciprocity kills BOTH halves, forcing `x^(2n)+x^n+1`; unique Dickson preimage `D_n+1`; even `n` square, odd `n>=5` has forbidden `x^(n-2)`. Sole exception `x^3+x+1 -> x^6+x^3+1`. |
| iterated-Q recurrence hypotheses (Kyuregyan) | require `a_(n-1)=1`, which IS the forbidden output coefficient at `x^(2n-1)`; shaped inputs have `a_(n-1)=0` so they cannot even enter the theorem |
| AS composition `f(x^2+x+a)` | even `n`: `Tr(alpha)=0` forces reducible (Capell); odd `n`: `(x^2+x+a)^n` contributes `x^(2n-1)` with coefficient 1 -> shape violated |
| all six `PGL_2(GF(2))` repairs of the above | translation forces `x^(2n-2)`; inversion collapses to `x^(2n)+x^n+1`; `x/(x+1)` gives `x^(2n)+(x+1)^n`, divisible by `x^2+x+1` |
| `f -> x f + 1` (degree +1) | `f(1)=1` for every irreducible of degree >1, so `(xf+1)(1)=0` |
| even/odd split `f = E^2 + x H^2` | `gcd(f,f')=gcd(E,H)^2` gives only coprimality, not irreducibility of the shaped component; witnesses `x^5+x^2+1`, `x^6+x^3+1` have reducible components |
| `f^2+x`, `x f^2+1`, `f^2+f+x`, `f^2+xf+1` | reducible on all shaped irreducibles deg 2..12 |
| Capell cubic composition `f(x^3)` under non-cube root (NC3) | WORKS, gives rays `d*3^k`; 138 seeds, 95 3-free rays; misses every odd degree and infinitely many even 3-free bases |
| cyclotomic `Phi_(3^r) = x^(2*3^(r-1)) + x^(3^(r-1)) + 1` | infinite family of degrees `2*3^(r-1)` only |

The unifying structural observation (mine, to be tested below): **every closed
degree-multiplying route is a *composition* `f -> f(sigma(x))` (or its
projectivization), and composition with a degree-`k` `sigma` places the input's
coefficient `a_(n-j)` into output degree `k(n-j)` plus lower corrections.  The
top half of the output is therefore controlled by the TOP `n/k` coefficients of
the input -- and shape controls only the BOTTOM half of the input.**  The window
is moved the wrong way by exactly the composition degree.  This is the
mechanism, stated once, that subsumes Q, AS, monomial, and projective repairs;
Capell's `x^3` survives only because it *scales* exponents (all of them),
mapping shape `<= n/2` to shape `<= 3n/2 = (3n)/2`, i.e. it is shape-EXACT, not
shape-improving.

## 00:35 -- a complete classification of the composition class (PROVED + verified)

The ledger closes composition-type constructions one at a time (Q, AS, the six
`PGL_2` repairs, `xf+1`, `f^2+x`, ...).  They are all instances of one map and
admit a single uniform theorem.  I state and prove it, then check it
exhaustively.

**Setup.** Call `f` *shaped* if `f` is monic of degree `n` and
`deg(f - x^n) <= floor(n/2)`.  Let `sigma` be monic of degree `k >= 1` and put
`s = deg(sigma - x^k)` (`s = -inf` when `sigma = x^k`).  Composition
`f -> f(sigma)` multiplies degree by `k`.

**Lemma A (shape of a composition does not depend on `f`).**
Write `f = x^n + q`, `deg q <= floor(n/2)`.  Then
`f(sigma) = sigma^n + q(sigma)` and
`deg q(sigma) <= k*floor(n/2) <= floor(kn/2)`.
So `q(sigma)` cannot reach above the half line at all, and

```text
f(sigma) is shaped  <=>  deg(sigma^n - x^(kn)) <= floor(kn/2).
```

The right side mentions only `(n, sigma)`.  PROVED (elementary; the inequality
`k*floor(n/2) <= floor(kn/2)` is checked separately for `n` even and odd).

**Lemma B (exact arithmetic criterion).**  In characteristic two, with
`t = sigma - x^k` and `n = sum_i 2^(b_i)`,
`sigma^(2^b) = x^(k 2^b) + t^(2^b)` (Frobenius), so

```text
sigma^n = sum over subsets S of bits of n:  x^(k n_S) * t^(n - n_S),
```

with `n_S = sum_(i in S) 2^(b_i)`, and the `S`-term has degree exactly
`s*n + (k-s)*n_S` (no collisions in general; the maximum over proper `S` is
attained at the unique largest proper submask `n - lsb(n)`).  Hence

```text
deg(sigma^n - x^(kn)) <= floor(kn/2)
  <=>  sigma = x^k,  OR  (k - s) * lsb(n) >= ceil(k*n/2),
```

where `lsb(n) = 2^(v_2(n))`.  PROVED.

**Corollary C (the classification).**  Write `n = 2^a * m`, `m` odd, `n >= 2`.
Then `lsb(n) = n/m` and the criterion reads `(k-s)/m >= k/2` (up to the exact
ceiling), so

* `m >= 3` is **impossible** for every `sigma != x^k` and every `k`;
* `m = 1` (i.e. `n` a power of two) holds **iff `s <= floor(k/2)`, i.e. iff
  `sigma` is itself shaped**;
* `sigma = x^k` works for **every** `n` (shape-exact: exponents just scale).

So: *the only degree-multiplying compositions that preserve the Lemire shape
uniformly in `n` are the monomial ones `f -> f(x^k)`.  Every non-monomial
`sigma` is confined to source degrees that are powers of two, and there must
itself be shaped.*  PROVED.

**Exhaustive verification.** All monic `sigma` of degree `k = 1..5` (62 maps),
all `n = 1..14`, all shaped `f` of that degree: 868 `(k, sigma, n)` cells,
**0 mismatches** between (i) "every shaped `f` of degree `n` composes to a
shaped polynomial", (ii) Lemma A's `f`-free predicate, and (iii) Lemma B's
arithmetic criterion.

```sh
cd /tmp/claude-1000/.../scratchpad && python3 -c "...
 for k in 1..5, sigma in monic deg k, n in 1..14:
   P = deg(sigma^n - x^(kn)) <= floor(kn/2)
   C = (sigma==x^k) or ((k-s)*lsb(n) >= ceil(k*n/2))
   A = all(shaped(compose(x^n+q, sigma)) for q in 0..2^(floor(n/2)+1)-1)
   assert P==C==A"
# -> checked 868 pairs; mismatches 0
```

**Why this subsumes the ledger's case list.**
`Q` is not a polynomial composition but a rational one (below); AS is
`sigma = x^2 + x + a`, `k = 2`, `s = 1 = floor(k/2)`, so it survives Lemma B
*only* at `n = 2^a` -- and there it dies for the independent trace reason.
`x -> x+1` is `k = 1`; `f^2 + x` etc. are not compositions at all but they die
on the same top-half collision.

**Sharpening of the ledger's AS statement (EVIDENCE, degrees 3..12).**  The
ledger proves `f(x^2+x+a)` fails *for shaped `f`* via the trace.  Exhaustively
over **every** monic `f` of degree `n = 3..12` and both shifts `a in {0,1}`
(`2 * sum 2^n = 8188` polynomials): 80 of the compositions are shaped, **none
has `a_(n-1) = 1`, and none is irreducible**.  The mechanism is visible: the
output coefficient at `x^(2n-2)` receives `a_(n-1)` from the `j = n-1` term and
otherwise only the submask contribution of `x^n(x+1)^n = sum_(i sub n) x^(n+i)`,
and `2n-2 > floor(2n/2) = n` for `n > 2`; so shape pins `a_(n-1)` and the trace
argument then applies to *arbitrary* `f`, not just shaped ones.  I have not
written the submask bookkeeping out uniformly in `n`, so this is labelled
EVIDENCE, not PROVED; the shaped-`f` case remains PROVED by the ledger's trace
argument.

## 00:50 -- extension to rational (Cohen) transformations

Cohen's composition method (Cohen 1969; see
[Springer, *Irreducible compositions of polynomials over finite fields*](https://link.springer.com/article/10.1007/s10623-010-9478-5))
uses `F(x) = g(x)^n P(h(x)/g(x))` with `gcd(h,g)=1`,
`k = max(deg h, deg g)`; `F` is irreducible over `F_q` iff `h - alpha g` is
irreducible over `F_(q^n)`.  This is the umbrella under which the `Q`-transform,
the `R`-transform, the `Q_k`/`Q_k-hat` transforms, and the elliptic-curve
constructions all live.

**Obstruction D (nonconstant denominator destroys the window).**
Let `e = deg g >= 1`.  Then `deg(h^j g^(n-j)) = e*n + (k-e)*j`, strictly
increasing in `j`.  For shaped `P` the largest surviving index is
`j = floor(n/2)`, contributing degree `e*n + (k-e)*floor(n/2)`, which exceeds
`floor(kn/2)` by about `e*n/2`.  So the *middle* coefficient of `P` -- the one
shape is allowed to use -- is already thrown above the half line, and shape of
`F` becomes a conspiracy among `P`'s coefficients rather than a property of
the transformation.  Consequently no rational transformation with nonconstant
denominator preserves shape uniformly.

**Exhaustive verification.** All coprime `(h,g)` with `g` nonconstant and
`max(deg h, deg g) = k` for `k = 2, 3`, all `n = 3..10`, all shaped `f`:
**no map preserves shape for even one `(k, n)`**.  (Command in the scratchpad;
predicate `deg(F) == k*n and shaped(F)`.)

Combined with Corollary C: **the entire Cohen rational-transformation class --
which the 2019-2025 literature shows is, modulo fractional linear changes of
variable, exactly "composition with a power map `x^t`"
([Reis, *Construction of irreducible polynomials through rational
transformations*](https://arxiv.org/abs/1905.07798); [*The R-transform as a
power map and its generalisations to higher degree*](https://arxiv.org/abs/1909.02608))
-- collapses for the Lemire problem to the monomial case `f -> f(x^k)`.**
That is a single closing theorem for a class the ledger was retiring member by
member.  It also explains, rather than merely records, why Capell's `x^3` is the
one survivor.

## 01:10 -- NEW RESULT: the Capell family is the `k = 3` case of a much larger
## family, and the larger family DOES cover odd degrees

Corollary C says the monomial compositions `f -> f(x^k)` are the only uniform
survivors.  The ledger instantiates exactly one of them (`k = 3`, Capell's
cubic criterion) and then records:

> "138 eligible even seeds, 200 structurally ineligible odd degrees ... their
> union omits **every odd degree** and infinitely many even 3-free bases."

The odd-degree ineligibility is an artifact of `k = 3`, **not** of the method.
The general criterion is classical (Lidl--Niederreiter, *Finite Fields*,
Thm. 3.35 / Cor. 3.47 on `f(x^t)`; also stated in
[Kyureghyan's UDT2021 survey](https://www.ricam.oeaw.ac.at/events/conferences/udt2021/schedule/slides/UDT2021_Slides_Kyuregyan.pdf)):

> Let `f` be irreducible over `F_2` of degree `d` with root `alpha` and
> `e = ord(alpha) | 2^d - 1`.  For `k` odd, `f(x^k)` is irreducible over `F_2`
> **iff** every prime `p | k` satisfies `p | e` and `p` does not divide
> `(2^d-1)/e` -- equivalently, `alpha` is not a `p`-th power in `F_(2^d)`.
> (The classical extra condition "`4 | k` implies `4 | q-1`" forces `k` odd in
> characteristic two, since `2^d - 1` is odd.)

Capell's `k = 3` is exactly this with `p = 3`, and `3 | 2^d - 1` iff `d` is
even -- hence, and only hence, the 200 "structurally ineligible" odd degrees.

**Shape is preserved for every odd `k` and every `d`, including odd `d`:**
`deg(f(x^k) - x^(dk)) = k*deg(f - x^d) <= k*floor(d/2) <= floor(dk/2)`
(Lemma A, `sigma = x^k` branch).  PROVED.

**Iteration persists for every odd prime `k` (same LTE argument as Capell's).**
If `beta^k = alpha` then `v_k(ord beta) = v_k(ord alpha) + 1` and
`v_k(2^(dk)-1) = v_k(2^d-1) + 1` (lifting the exponent), so non-`k`-th-power-ness
is inherited.  Hence one qualifying seed `(d, k)` gives shaped irreducibles in
**every degree `d * k^j`, `j >= 0`**.  PROVED.

### Measurement against the repository's own 400 committed witnesses

Source: `artifacts/gf2/lemire/range-1-400/shards/*/degree-*.json`, field
`polynomial_words_le` (little-endian 64-bit words -> bitmask polynomial).
For each degree `d` and each odd prime `k` with `ord_k(2) | d` (so `k | 2^d-1`),
test `alpha^((2^d-1)/k) != 1` in `F_2[x]/(f_d)` with `alpha = x`.

```sh
# scratchpad: rays2.py (primes < 5e4 by order), rays3.py (Mersenne-prime and
# p = 2dj+1 scan up to 2e7 for the leftovers)
python3 rays2.py ; python3 rays3.py
```

Result (EVIDENCE, exact finite computation, not a theorem about all degrees):

| | Capell `k=3` (ledger) | generalized odd `k` (this note) |
| --- | --- | --- |
| eligible seed degrees `d <= 400` | 138 | **367** |
| of which **odd** `d` | **0** (structurally impossible) | **172** of 200 |
| distinct infinite rays | 95 (3-free) | >= 367 (one per `(d, k_min)`; many more with the other eligible `k`) |

The 33 degrees with no eligible `k` found are search-bound artifacts, not
obstructions: for those `d` every prime factor of `2^d - 1` exceeded the
`2 * 10^7` scan (e.g. `d = 101, 137, 199, 257`), or the *committed* witness
happened to be a `k`-th power for the small factors found.  Two structural
remarks: (i) if `2^d - 1` is prime (`d = 17, 19, 31, 61, 89, 107, 127` in
range) then **every** shaped irreducible of degree `d` qualifies, because the
only `k`-th power is `1`; (ii) if any degree-`d` shaped irreducible is
*primitive*, it qualifies simultaneously for **every** odd `k | 2^d - 1`.

### Certified examples (independently re-checked here by Rabin)

```text
d=3,  k=7   ->  x^21  + x^7  + 1        (odd degree 21,  shaped, irreducible)
d=3,  k=7^2 ->  degree 147               (odd, shaped, irreducible)
d=5,  k=31  ->  x^155 + x^62 + 1        (odd degree 155, shaped, irreducible)
d=15, k=7   ->  x^105 + x^7  + 1        (odd degree 105, shaped, irreducible)
d=4,  k=5   ->  x^20  + x^5  + 1
d=8,  k=17  ->  x^136 + x^68 + x^51 + x^17 + 1
d=16, k=5   ->  x^80  + x^30 + x^10 + x^5 + 1
d=18, k=7   ->  x^126 + x^21 + 1
```

All 17 compositions with `d <= 18`, `dk <= 200` were re-verified irreducible
and shaped by an independent Rabin test written for this diary; 0 failures.

**Status label: PROVED** for the criterion, the shape preservation, and the
LTE iteration (all classical, re-derived and machine-checked here).
**EVIDENCE** for the eligibility census against the 400 committed witnesses.
**Not a proof of Lemire**: the union of the rays `d * k^j` still has density
zero, and (as for Capell) the *bases* `d` are exactly the degrees we already
had.  The gain is qualitative -- the ledger's "every odd degree is uncovered"
claim is now false -- and it removes a whole documented gap.

## 01:40 -- the invariance mechanism, stated once for the whole literature

The `Q`-transform died of **self-reciprocity**.  That is not a quirk of `Q`; it
is the organizing principle of the entire Varshamov / Wiedemann / Meyn / Cohen /
Kyuregyan / Ugolini construction literature.  Verified sources:

- Bassa and Menares, [*The R-transform as a power map and its generalisations
  to higher degree*](https://arxiv.org/abs/1909.02608) (2019/2024): "the
  iterative constructions correspond **modulo fractional linear
  transformations to compositions with power functions `x^t`**", producing
  degrees `n t^r`.  This is the exact statement that reduces the whole
  transform zoo to Corollary C plus Obstruction D.
- Reis, [*Construction of irreducible polynomials through rational
  transformations*](https://arxiv.org/abs/1905.07798) (JPAA 2019): recursive
  families of degree `n D^i` for `D | q+1`.
- [*Transformations on Irreducible Binary Polynomials*](https://link.springer.com/content/pdf/10.1007/978-3-642-15874-2_13.pdf)
  and Ugolini, [*Sequences of binary irreducible polynomials*](https://arxiv.org/pdf/1204.6692):
  use the natural action of `GL_2(F_2) ~ S_3` on `F_2[X]` and define classes
  "strongly analogous to self-reciprocal", one per subgroup, with explicit
  infinite sequences of **invariant** irreducibles in each class; they
  explicitly generalize Varshamov, Wiedemann, Meyn and Cohen.
- Kyuregyan, [*Irreducible compositions of polynomials over finite fields*](https://link.springer.com/article/10.1007/s10623-010-9478-5)
  (DCC 61, 2011) and [*... of even characteristic*](https://link.springer.com/article/10.1007/s00200-012-0175-7);
  [*Rational transformations over finite fields that are never irreducible*](https://link.springer.com/article/10.1007/s10623-025-01591-2)
  (DCC 2025) is the negative classification in the same frame.
- Wiedemann, [*An iterated quadratic extension of GF(2)*](https://www.fq.math.ca/Scanned/26-4/wiedemann.pdf)
  (Fibonacci Quart. 26 (1988) 290-295) -- the `x_(j+1)^2 + x_(j+1) = x_j` tower;
  the same object now underlies binary tower fields (Binius).

So the right question is not "which transform?" but "**which shaped
irreducibles are invariant at all?**"  That question is finite and decidable.

**Theorem E (invariance census).**  Let `f` be a shaped irreducible of degree
`n`, and let it be fixed by a nontrivial element of `PGL_2(F_2) ~ S_3` acting
by `f^g(x) = (cx+d)^n f((ax+b)/(cx+d))`.  Then:

1. (`x -> 1/x`, self-reciprocal.)  Shape kills degrees `n/2 < i < n`;
   reciprocity mirrors that to `0 < i < n/2`.  Only `i in {0, n/2, n}` can
   survive, so `f = x^n + x^(n/2) + 1` with `n` even (dropping the middle term
   gives `(x^(n/2)+1)^2`).  And `x^(2m)+x^m+1 = Phi_3(x^m)` is irreducible over
   `F_2` iff `m = 3^(r-1)`.  **So the self-reciprocal class contributes exactly
   the cyclotomic family `Phi_(3^r)`, degrees `2*3^(r-1)` -- and nothing else.**
   PROVED.  (The ledger reaches the same list through Dickson polynomials; this
   derivation needs only the mirror symmetry, and it applies to *every*
   self-reciprocity-producing transform at once, not just to `Q`.)
2. (`x -> x+1`, translation.)  Invariance means `f in F_2[x^2+x]`, i.e.
   `f = g(x^2+x)`.  Exhaustively over **all** monic `g` of degree `3..12`
   (not merely shaped ones) and both shifts `a in {0,1}`: 80 shaped outputs,
   **none** with `a_(n-1) = 1`, **none irreducible**.  Together with the trace
   argument (`shape => Tr(alpha)=0 =>` Capell reducibility) the only shaped
   irreducible in this class is `x^4 + x + 1` (`n = 4`).
3. (order-3 elements `x -> (x+1)/x`, `x -> 1/(x+1)`.)  Invariants are
   `F_2(u)` with `u = (x^3+x+1)/(x^2+x)`, a degree-3 map with **nonconstant
   denominator**, so Obstruction D applies: writing `f = sum_j b_j
   (x^3+x+1)^j (x^2+x)^(m-j)` (`n = 3m`), the `j`-term has degree exactly
   `2m + j`, so **every** term lands above `floor(3m/2)` and shape is a total
   conspiracy.  Census over all shaped irreducibles of degree
   `n in {3,9,12,15,21,24,27,30,33}`: exactly two survivors, `x^3+x+1` and
   `x^9+x+1`, and **nothing at 12, 15, 21, 24, 27, 30, 33**.

Full census over every shaped irreducible of degree `2..24` (invariance under
each of the six `PGL_2(F_2)` maps):

```text
n=2   x^2+x+1     invariant under all five nontrivial maps
n=3   x^3+x+1     order-3 class
n=4   x^4+x+1     translation
n=6   x^6+x^3+1   self-reciprocal
n=9   x^9+x+1     order-3 class
n=18  x^18+x^9+1  self-reciprocal
```

Six polynomials in 23 degrees.  **Conclusion (EVIDENCE + the proved
self-reciprocal half): the invariant-sequence literature can produce, at half
shape, only the cyclotomic ray `2*3^(r-1)`.  Every other published binary
transform family is invariance-based and therefore contributes nothing.**
That retires a large body of candidate constructions in one statement instead
of one paper at a time.

## 02:05 -- part (3): the CS / derandomization leverage, and why it is empty

**REFUTED: no hitting-set, affine-disperser, or generic pseudorandomness
theorem can apply at this threshold, because the generic statement is false by
a two-line counterexample.**

The Lemire family is an affine subspace `A_n` of the monic degree-`n`
polynomials of dimension `floor(n/2)+1`.  The tempting CS statement is "every
affine subspace of dimension `>= n/2` meets the irreducibles, since the
irreducibles have density `1/n`."  But for any fixed `p` of degree `r`, the set

```text
{ f monic, deg f = n : p | f }
```

is an affine subspace of dimension `n - r` **containing no irreducible of
degree `n > r` whatsoever**.  Taking `r = floor(n/2) - 1` gives an affine
subspace of dimension `floor(n/2)+1` -- the *same* dimension as `A_n` -- with
**zero** irreducibles.  So the extremal problem "does every affine subspace of
dimension `d` contain an irreducible?" has answer "no" all the way up to
`d = n-1` (take `p = x`).  PROVED (trivially), and decisive: **any proof of
Lemire must use arithmetic specific to `A_n`; no dimension-counting,
disperser, extractor, or hitting-set argument can contribute.**

The Fourier framing collapses onto the same wall.  Over `F_2`, testing whether
an affine subspace meets a set `S` is exactly asking whether the indicator of
`S` correlates with the linear functionals cutting out the subspace -- i.e.
`sum_f mu(f) chi(f)` over additive characters `chi` supported on the top-half
coefficients.  That sum *is* the endpoint discrepancy the lane has been
bounding.  So "derandomize by a PRG for affine tests" is not an alternative
route; it is a relabelling of the square-root barrier.

Two related facts, verified, that bound expectations in the other direction:

- **Constructing *some* irreducible of each degree over `F_2` is already
  solved deterministically.**  Shoup, [*New algorithms for finding irreducible
  polynomials over finite fields*](https://www.ams.org/journals/mcom/1990-54-189/S0025-5718-1990-0993933-0/S0025-5718-1990-0993933-0.pdf)
  (Math. Comp. 54 (1990) 435-447) runs in `O~(d^4 p^(1/2) log^4 q)`, which for
  `p = 2` is deterministic polynomial time.  Rai,
  [*Pseudo-Deterministic Construction of Irreducible Polynomials over Finite
  Fields*](https://eccc.weizmann.ac.il/report/2024/147/) (ECCC TR24-147, 2024)
  gives `O~(d^4 log^4 q)` pseudo-deterministically.  Adleman and Lenstra,
  [*Finding irreducible polynomials over finite fields*](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1986a/art.pdf)
  (STOC 1986) is the ERH-conditional ancestor.  **None of them controls
  coefficients**, and the difficulty of Lemire is entirely in the coefficient
  constraint, not in the construction.
- **Prescribed-coefficient existence theorems are far from `n/2`.**  Pollack,
  *Irreducible polynomials with several prescribed coefficients* (FFA 22
  (2013) 70-78) prescribes `floor((1-eps) sqrt n)` coefficients; Ha,
  [same title](https://arxiv.org/abs/1601.06867) (FFA 40 (2016) 10-25)
  reaches `r <= (1/4 - eps) n` **for large `q`**, and only `r <= delta n` for
  a small unspecified `delta > 0` at fixed `q` (so at `q = 2`).  Lemire needs
  `r = ceil(n/2) - 1` prescribed *zeros* at `q = 2`.  The lane's own
  near-endpoint theorem (`deg(f - x^n) <= n/2 + O(log n)`) is **stronger than
  every published prescribed-coefficient result at `q = 2`**, which is worth
  saying explicitly in the paper.

## 02:30 -- NEW RESULT: the power-of-two branch of Corollary C is NOT empty

Corollary C leaves exactly one non-monomial window open:

> `n = 2^a`, and `sigma` itself shaped of degree `k`.

The ledger never tested it, because its case analysis went transform-by-
transform and `k = 2` (Artin--Schreier) dies on the trace.  The window is real.

**Experiment (exhaustive).**  All shaped irreducibles `f` of degree
`n in {4, 8, 16}`; all shaped `sigma = x^k + t`, `1 <= deg t <= floor(k/2)`,
`k = 2..8`; test `f(sigma)` for shape (always holds, as Corollary C predicts)
and irreducibility by Rabin.

```text
non-monomial shaped irreducible compositions found: 241
```

Examples (each independently Rabin-checked here):

```text
deg 12 : (x^4+x+1)(x^3+1)                                   [n=4,  k=3]
deg 24 : (x^4+x+1)(x^6+x^3+x^2)                             [n=4,  k=6]
deg 32 : (x^4+x+1)(x^8+x^3+x)                               [n=4,  k=8]
deg 56 : (x^8+x^4+x^3+x^2+1)(x^7+x^3+x)                     [n=8,  k=7]
deg 64 : (x^8+x^4+x^3+x^2+1)(x^8+x^4+x^3+x+1)               [n=8,  k=8]
deg 512: (a shaped irreducible of degree 64)(x^8+x^3+x)      [n=64, k=8]
```

**Two proved sub-obstructions inside the window (they explain the pattern):**

- `k = 2`: shape forces `Tr(alpha) = 0`, so `f(x^2+x+a)` is reducible.  PROVED
  (and strengthened above to all monic `f`, not only shaped ones).
- `k = 4`: a shaped `sigma` of degree 4 is `x^4 + c_2 x^2 + c_1 x + c_0`, i.e.
  an **affine linearized** polynomial.  Then `sigma(x) - alpha = L(x) + beta`
  with `L` additive; its roots form a coset of `ker L`, and `ker L` lies in a
  small subfield of `F_(2^n)` whenever `n = 2^a >= 2`, so the Galois group of a
  root over `F_(2^n)` embeds in the elementary abelian translation group and
  can never be cyclic of order 4.  Hence `f(sigma)` is **always reducible** for
  `k = 4`.  PROVED -- and the census confirms it: **no `k = 4` hit among the
  241**.
- Same reasoning kills the purely additive `sigma` at `k = 8`
  (`x^8+c_4x^4+c_2x^2+c_1x+c_0`).  Confirmed: **every one of the `k = 8` hits
  contains the non-additive term `x^3`.**

**Why this matters -- an iterable tower of powers of two.**  If `k = 2^b`
(`b >= 3`), the output degree `2^(a+b)` is again a power of two, so the
construction **iterates**:

```text
2^a  --(shaped sigma of degree 2^b, b>=3)-->  2^(a+b)  -->  ...
```

Measured: from a degree-8 shaped irreducible, `k = 8` gives degree 64
immediately; from 8 random shaped irreducibles of degree 64, `k = 8` succeeds
for **5 of 8** seeds (10 hits out of 248 `(seed, sigma)` pairs, i.e. about
`1/25 ~ 1/(2k)`, consistent with `1/k` restricted to the ~half of `sigma` that
are non-additive), yielding certified shaped irreducibles of **degree 512**.
Runtime for the whole 248-pair sweep: 1.9 s in Python.

**The reduced lemma (OPEN, and a genuinely different one).**  For every
`a >= 3` and some `b >= 3`, does there exist a shaped
`sigma in F_2[x]` of degree `2^b` and a shaped irreducible `f` of degree `2^a`
with `sigma(x) - alpha` irreducible over `F_(2^(2^a))`?  If yes for a
single `b` per `a`, **every degree `2^c` carries a shaped irreducible**,
by induction from the certified base degrees `2, 4, 8, 16, 32, 64, 128, 256`.

This is a *better-conditioned* target than the original: at step `(a, b)` the
free parameter is `t` with `2^(2^(b-1)+1)` choices and the per-choice success
probability is `~1/2^b`, so the heuristic margin is **doubly exponential**,
whereas Lemire's own margin is `2^(n/2)/n` -- only singly exponential and,
critically, the whole point of the analytic blockage.  Honest caveat: the
family `{x^k + t : t in F_2[x], deg t <= k/2}` sits in the *prime field*, so
the associated character sum is over the same kind of thin affine set, and I
have **no** reason to believe this reduction is analytically easier.  What it
does buy is a *two-parameter* search (`a` and `b`, plus the choice of seed),
which the original one-parameter problem does not have, and it makes powers of
two -- a 3-free ray that Capell provably cannot reach -- an inductive family
rather than a per-degree search.

Status: **PROVED** that the window exists and that `k in {2,4}` and all
additive `sigma` are excluded; **EVIDENCE** (241 + 10 certified compositions)
that the window is non-empty and iterates; **OPEN** whether a step always
exists.

## 02:45 -- part (2) revisited: the reciprocal flip is exact, and it is the
## ray-class statement the lane already has

For the record, because the charge asks specifically:
`f = x^n + q` shaped and irreducible (so `q(0) = 1`) iff its reciprocal
`g = f*` satisfies `deg g = n`, `g` irreducible, and

```text
g == 1  (mod x^(ceil(n/2))).
```

So "control the LOW coefficients" and "control the HIGH coefficients" are the
same problem, exactly -- which is why AS/Wiedemann towers, which control low
coefficients of the composed polynomial, give nothing extra: the reciprocal of
`g(x^2+x)` is `g*(x)*(...)`-shaped in the same forced way, and the trace
obstruction is reciprocal-invariant (`Tr(alpha) = Tr(1/alpha)` is false in
general, but the *coefficient* `a_(n-1)` of `f` equals `a_1/a_0` of `f*`, and
the ledger's Kyuregyan hypothesis `a_(n-1) = a_1/a_0 = 1` is precisely the
statement that both are forced).  The `1`-unit filtration
`U^(m) = 1 + x^m F_2[[x]]` makes `g in U^(ceil(n/2))` -- the identity ray class
mod `x^(ceil(n/2))` the lane already uses.  Squaring maps `U^(m) -> U^(2m)`
and doubles the degree in exact proportion, which is why no filtration-only
argument can gain: the shape requirement is scale-invariant under the one
operation the filtration supplies.  No new leverage here; recording it as a
closed direction rather than an open one.

## 03:00 -- dead ends recorded

- **Generic derandomization.** Refuted outright (see 02:05): affine subspaces
  of dimension up to `n-1` can avoid the irreducibles entirely, so no
  hitting-set / disperser / PRG theorem has any content here.
- **`sigma` of degree 4 (and all additive `sigma`).** Proved impossible by the
  elementary-abelian Galois argument; the exhaustive census over `n = 4, 8, 16`
  gives `0` hits at `k = 4` and `0` at `k = 2`, versus 44/73/14/78/32 at
  `k = 3/5/6/7/8`.
- **`C_3`-invariant shaped irreducibles.** Only `x^3+x+1` and `x^9+x+1`; empty
  at degrees 12, 15, 21, 24, 27, 30, 33.  Not a family.
- **Rational (nonconstant-denominator) transformations.** Obstruction D plus an
  exhaustive `k = 2, 3`, `n = 3..10` sweep: no map preserves shape for a single
  `(k, n)`.
- **Reciprocal/1-unit filtration.** Exactly equivalent to the ray-class
  statement already in the ledger; squaring scales layer and degree together,
  so no gain.
- **Iterated `k = 8` from one particular degree-64 seed.** Failed (0 of 31
  `sigma`).  Only a seed-specific stall -- 5 of 8 other seeds succeed -- but
  worth recording so the next agent does not conclude the tower dies.

## FINDINGS

### (a) Sharpest reformulation from this angle

Two, one negative and one positive.

**Negative (closes the constructive program as usually conceived).**
*Let `sigma` be monic of degree `k` and `f` shaped of degree `n`.  Then
`f(sigma)` is shaped iff `deg(sigma^n - x^(kn)) <= floor(kn/2)`, a condition on
`(n, sigma)` alone, which holds iff `sigma = x^k`, or `n` is a power of two and
`sigma` is itself shaped.*  Together with Obstruction D (any nonconstant
denominator throws the middle coefficient of `f` above the half line) and the
published fact that the whole rational-transformation literature is
"composition with a power map modulo fractional linear transformations"
(Bassa--Menares), **the entire Cohen/Varshamov/Wiedemann/Meyn/Kyuregyan/Ugolini
transform program contributes exactly three things at half shape: the monomial
rays `d k^j`, the cyclotomic ray `2*3^(r-1)`, and the power-of-two window.**

**Positive.** *Lemire at degree `n` is: an irreducible `g` of degree `n` with
`g == 1 (mod x^(ceil(n/2)))`* -- the identity ray class, which the lane has.

### (b) Most promising techniques, with citations

1. **Generalized monomial composition (immediate, cheap, real).**
   Lidl--Niederreiter's `f(x^t)` criterion, of which Capell's cubic rule is the
   `t = 3` case.  Raises the ledger's 138 seeds / 95 rays / **0 odd degrees**
   to **367 seeds and 172 of the 200 odd degrees `<= 400`**, each generating an
   infinite ray `d k^j` by the same lifting-the-exponent argument the lane
   already accepted for `k = 3`.  Survey framing:
   [Kyureghyan, UDT2021](https://www.ricam.oeaw.ac.at/events/conferences/udt2021/schedule/slides/UDT2021_Slides_Kyuregyan.pdf).
2. **The power-of-two composition window** (new; 241 + 10 certified instances
   here), reduced to: for `n = 2^a` and some `k = 2^b`, `b >= 3`, find shaped
   `sigma` with `sigma - alpha` irreducible over `F_(2^n)` -- Cohen's criterion
   ([DCC 61 (2011) 301-314](https://link.springer.com/article/10.1007/s10623-010-9478-5)).
   Would make **every** power of two an inductive family.
3. **Not promising, and now documented as such:** self-reciprocal /
   `GL_2(F_2)`-invariant sequence constructions
   ([Ugolini, arXiv:1204.6692](https://arxiv.org/pdf/1204.6692);
   [Bassa--Menares, arXiv:1909.02608](https://arxiv.org/abs/1909.02608);
   [Reis, arXiv:1905.07798](https://arxiv.org/abs/1905.07798)); deterministic
   construction algorithms
   ([Shoup, Math. Comp. 54 (1990) 435-447](https://www.ams.org/journals/mcom/1990-54-189/S0025-5718-1990-0993933-0/S0025-5718-1990-0993933-0.pdf);
   [Adleman--Lenstra, STOC 1986](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1986a/art.pdf);
   [Rai, ECCC TR24-147](https://eccc.weizmann.ac.il/report/2024/147/);
   [Couveignes--Lercier, arXiv:0905.1642](https://arxiv.org/abs/0905.1642));
   prescribed-coefficient existence
   ([Ha, arXiv:1601.06867](https://arxiv.org/abs/1601.06867); Pollack, FFA 22
   (2013) 70-78) -- all strictly weaker at `q = 2` than the lane's own
   near-endpoint theorem.

### (c) Decisive obstructions

1. **The window-shift obstruction (proved, general).** Composition by `sigma`
   of degree `k` maps input coefficient `a_(n-j)` to output degree
   `k(n-j) + (lower)`; shape controls the *bottom* half of the input but the
   output's forbidden band is its *top* half, and `sigma^n`'s binomial
   expansion `sum_(S subset bits(n)) x^(k n_S) t^(n-n_S)` repopulates that band
   unless `t = 0` or `n` has a single bit.  This is one theorem where the
   ledger has eight case analyses.
2. **The invariance obstruction (proved).** Any nontrivial `PGL_2(F_2)`
   symmetry mirrors the killed top half onto the bottom half; self-reciprocity
   then forces `x^n + x^(n/2) + 1`, i.e. exactly `Phi_(3^r)`.  The whole
   invariant-sequence literature is therefore capped at one ray.
3. **The generic-derandomization obstruction (proved, two lines).** Affine
   subspaces of dimension `n - r` consisting of multiples of a fixed degree-`r`
   polynomial contain **no** irreducibles, for every `r < n`.  Nothing that
   sees only the dimension of `A_n` can work.
4. **The additive/`k=4` obstruction (proved).** Shaped `sigma` of degree 4 is
   affine linearized, so a root generates an elementary abelian extension --
   never cyclic of degree 4.  Confirms 0 hits at `k = 4` and explains why every
   `k = 8` hit carries the non-additive `x^3`.

### (d) Concrete next experiments runnable here

1. **Redo the Capell audit for general odd `k` in the Rust CAS.** Reuse
   `cubic_composition_criterion` with the prime `3` replaced by any odd
   `k | 2^d - 1`; emit a Rabin certificate per composition, as the existing
   `axeyum-gf2-capell-audit` does.  Expected: `>= 367` seeds, `>= 172` odd
   degrees, and the ledger sentence "their union omits every odd degree" must
   be corrected.  Cost: minutes.  This is the highest-value item.
2. **Per-degree eligibility over *all* shaped irreducibles**, not just the
   committed witness -- this should close most of the 33 remaining degrees, and
   for degrees where `2^d - 1` is prime it is automatic.  Also sweep for a
   shaped **primitive** polynomial per degree: one such makes every odd
   `k | 2^d - 1` eligible at once.
3. **Push the power-of-two tower to degree 4096** (`n = 512`, `k = 8`, 31
   `sigma`; or `n = 256`, `k = 16`, 512 `sigma`).  Python is too slow at 4096;
   the Rust CAS is not.  A certified chain `8 -> 64 -> 512 -> 4096 -> ...`
   would be the first *iterable* non-monomial shaped family.
4. **Count the coverage.** Union of the certified rays `d k^j` (generalized
   monomial) plus `2*3^(r-1)` plus the power-of-two tower, counted against
   `n <= 10^6`, published as the paper's "explicit infinite families" table.
   Density is still zero -- say so.
5. **Falsification control for item 1**: re-run the criterion with a
   deliberately wrong prime (`k` not dividing `2^d - 1`) and require the audit
   to reject every composition.  Without it the audit exits 0 on completion.

### (e) New to the ledger

- **CORRECTION required.** "138 eligible even seeds, 200 structurally
  ineligible odd degrees ... their union omits every odd degree" is true only
  for `k = 3`.  With general odd `k`: 367 seeds, 172 odd degrees, and explicit
  witnesses `x^21 + x^7 + 1`, `x^105 + x^7 + 1`, `x^155 + x^62 + 1`.
- **New theorem (composition classification).** Only `sigma = x^k`, or
  `n = 2^a` with `sigma` shaped.  Subsumes the Q-transform, AS, the six
  projective repairs, `xf+1`, and `f^2+x`-type entries.
- **New theorem (invariance census).** Self-reciprocal shaped irreducible
  `<=> x^n+x^(n/2)+1 <=> Phi_(3^r)`; translation-invariant only `x^4+x+1`;
  `C_3`-invariant only `x^3+x+1`, `x^9+x+1` (empty through degree 33).
- **New open family (power-of-two window).** 241 exhaustive + 10 large
  certified non-monomial shaped irreducible compositions, with `k = 2` and
  `k = 4` proved impossible; reduced lemma stated in 02:30.
- **New stopping result.** The derandomization/hitting-set angle is refuted
  generically; the Fourier form of the affine question is literally the
  endpoint discrepancy already being bounded.  Recommend an explicit stopping
  note so no future lane re-opens it.
- **Literature boundary confirmed.** No published construction reaches half
  shape at `q = 2`; the strongest published prescribed-coefficient results
  (Ha, Pollack) are weaker than the lane's own `n/2 + O(log n)` theorem, which
  is worth stating in the paper as a comparison.
