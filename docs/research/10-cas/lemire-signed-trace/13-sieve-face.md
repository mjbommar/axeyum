# The sieve face of Kaser--Lemire: exact Type I, `P_3`, and the parity barrier

Status: research note, 2026-08-22 (angle 2 of the backward-chains diary,
[11-backward-chains-diary.md](11-backward-chains-diary.md)). Companions:
[01-target-and-toolkit.md](01-target-and-toolkit.md) (the target and `(HWO)`),
[03-uncertainty-analogy.md](03-uncertainty-analogy.md) section 5 (Barrier I, the
Fourier fake population), [05-almost-all-theorem.md](05-almost-all-theorem.md),
[09-construction-barrier.md](09-construction-barrier.md).

Everything finite here is re-derived and asserted by
`scripts/lemire-signed-trace/lemire_sieve_face.py` (exits nonzero on any failed
assertion; six mutation controls, each shown to trip). Bulk producer: the Rust
`GF(2)` CAS binary `axeyum-lemire-sieve` (new; source mirrored as
`scripts/lemire-signed-trace/axeyum-lemire-sieve.rs.txt`), whose local `u64`
polynomial layer is checked against the crate's `Gf2Poly`/`Gf2Context` and whose
factorisation is checked against `certify_irreducible` on all `32766` monic
polynomials of degree `<= 14` (`selfcheck`, `mismatches=0`). Independent
cross-check: python-flint in the lane venv. Linear programs: scipy/HiGHS, with
every LP-value-zero row re-certified over `Q` by an exact rational witness, so
no floating-point LP result is load-bearing.

Notation throughout: `W_n = {x^n + g : deg g <= floor(n/2)}`,
`h = floor(n/2) + 1`, `ell = n - h = ceil(n/2) - 1`, `|W_n| = 2^h`. `X = 2^n` is
the "size" of an element, so `|W_n|` is between `X^{1/2}` and `2 X^{1/2}`.
`M_n` is the set of all `2^n` monic polynomials of degree `n`. For monic `d`,
`A_d = #{F in W_n : d | F}`, and `|d| = 2^{deg d}`.

## 0. Summary

1. **Type I is exact, with zero remainder, up to the full size of the set**
   (Lemma 1): `A_d = 2^{h-k}` for every monic `d` of degree `k <= h`, with no
   error term at all, so `W_n` has level of distribution `D = |W_n| = 2^h`. This
   is strictly better than the integer analogue (where `[x, x + sqrt x]` has
   `|r_d| <= 1` and the level is `sqrt x / log x`), and it is the best possible:
   beyond `k = h` the counts are `0/1`-valued and `sum_{deg d = k}|r_d| = 2|W_n|`
   for *every* `k > h` (Corollary 3).
2. **What the sieve proves.** The sifting parameter at the prime level is `s = 1`
   exactly, so no lower bound for primes. It does give `P_4` with all factors of
   degree `> (1/4 - eps) n` (Theorem 6), and, with Kuhn weights, `P_3` with all
   factors of degree `> alpha n` for every `alpha < 1/6` (Theorem 7), `n_0`
   explicit modulo one absolute constant. A fully self-contained explicit form
   with no sieve black box is Theorem 8 (Brun's pure sieve with exact
   remainders, `P_{O(log n)}` with a table). The exact upper bound is
   Theorem 9: `#{irreducible in W_n} <= |W_n|/G_L`, `L = floor(h/2)`, an exact
   Brun--Titchmarsh with *no* error term, measured `3.0x` to `3.3x` the truth at
   `n <= 44` and `-> 4x`.
3. **The `P_3`-with-factors-`> n/4` statement, which is true and abundant in the
   data (about `5%` of `W_44`), is exactly out of sieve reach:** it needs
   `s > 2` at `y = n/4`, and `s = h/y = 2 + 4/n`, so the Jurkat--Richert main
   term is `~ 4 e^gamma / n` while the sieve's own error is `O((log D)^{-1/3})
   = O(n^{-1/3})`. The sieve face reproduces the lane's `1/n` deficit exactly.
4. **The parity barrier is a theorem here, with an exact rational witness**
   (Theorem 10 and Theorem 12): for `10 <= n <= 15` there is an explicit
   nonnegative rational `w` on `M_n`, vanishing on every irreducible, with
   `sum_{F : d | F} w(F) = 2^{n - deg d}` *exactly* for every monic `d` of degree
   `<= h`. By LP duality this says: **no lower-bound sieve using only the Type-I
   data of `W_n` at its own exact level can prove that `W_n` contains an
   irreducible.** The level at which the data does force a prime is
   `k_max(n) = h + 1` for `10 <= n <= 15`, `k_max(16) = h + 2`, and
   `k_max(17) >= h + 2` (Table 3) --
   a new exact measurement.
5. **A sieve proof at level `2^h` would prove Legendre for `F_2[t]`**
   (Proposition 11): the best such bound is at most `min_{A_0} #{irreducible F :
   deg(F - A_0) < h}` over *all* monic centres `A_0` of degree `n`, because every
   such window has identical exact Type-I data. So the sieve face cannot
   separate Kaser--Lemire from angle 5's uniform conjecture.
6. **Type II transplants back onto the same character family** (Proposition 13):
   expanding `1[ml in W_n]` in Hayes characters turns every bilinear form into a
   weighted average of the same `S_n(chi)`, with `A_M(chi) B_L(chi)` in place of
   `S_n(chi)`. The sieve route does not bypass `(HWO)`. Converse: `(HWO)` gives
   the count, not the bilinear forms; Type II is strictly stronger.

Nothing here proves Kaser--Lemire and nothing here disproves it. The content is
that the sieve face is now *located*, with the same exactness the rest of the
lane demands.

## 1. The exact Type-I lemma

**Lemma 1 (exact Type I).** Let `n >= 1`, `h = floor(n/2)+1`, `ell = n - h`, and
let `d` be monic of degree `k`. Write `d* = x^k d(1/x)` (so `d*(0) = 1`, a unit
in `F_2[[x]]`) and let `c = (d*)^{-1} mod x^{ell+1}`. Then

```text
A_d = #{F in W_n : d | F} = 2^{h-k}                       for 0 <= k <= h,
A_d = 1 if deg(c) <= n-k, else 0,                         for h < k <= n.
```

In particular the remainder `r_d = A_d - |W_n|/|d|` is **identically zero** for
every monic `d` with `deg d <= h`, and `A_d` is `0/1`-valued above that.

*Proof.* `F` is monic of degree `n`, so `F = d m` with `m` monic of degree
`n - k`, and reversal is multiplicative on degrees: `F* = d* m*`, where
`F* = x^n F(1/x)` and `m* = x^{n-k} m(1/x)`. The window condition
`deg(F - x^n) < h` says exactly that the coefficients of `x^{n-1}, ..., x^h` of
`F` vanish, i.e. `F* = 1 mod x^{ell+1}`. Hence

```text
d | F for some F in W_n with cofactor m   <=>   m* = (d*)^{-1} mod x^{ell+1}.
```

As `m` runs over the monic polynomials of degree `n-k`, `m*` runs over *all*
polynomials of degree `<= n-k` with constant term `1`, i.e. over `2^{n-k}` free
coefficients in positions `1, ..., n-k`. The condition prescribes the
coefficients in positions `1, ..., ell`. If `n - k >= ell`, i.e. `k <= h`, those
positions are among the free ones and the remaining `n-k-ell = h-k` are
unconstrained: `A_d = 2^{h-k}`. If `n - k < ell`, the prescription can be met
only if `c` has no coefficient in positions `n-k+1, ..., ell`, i.e.
`deg c <= n-k`, and then `m*` is unique. QED

**Corollary 2 (all levels sum to the same thing).** For every `0 <= k <= n`,

```text
sum_{d monic, deg d = k} A_d = sum_{F in W_n} tau_k(F) = 2^h,
```

`tau_k(F)` the number of monic divisors of `F` of degree `k`. Indeed `d <-> F/d`
gives `tau_k = tau_{n-k}`, and for `k > h` we have `n - k < ell < h`, so the
identity follows from Lemma 1 at level `n-k`. Combined with `A_d in {0,1}` for
`k > h`, this says: **exactly `2^h` of the `2^k` monic `d` of degree `k` divide
some element of `W_n`, for every `k > h`.**

**Corollary 3 (no level beyond `2^h`, not even on average).** For `k > h`,

```text
sum_{deg d = k} |r_d| = 2^h (1 - 2^{h-k}) + (2^k - 2^h) 2^{h-k}
                      = 2 (2^h - 2^{2h-k})  ->  2^{h+1} = 2 |W_n|.
```

So there is no Bombieri--Vinogradov-style *averaged* level beyond `2^h` either:
the total remainder at any single level `k > h` is twice the size of the whole
set. Every extension past `2^h` must be bilinear (well-factorable `lambda_d`
against `r_d`), which is precisely the Type II input of section 7.

**Corollary 4 (uniformity: the sieve sees only "an interval").** For *every*
monic `A_0` of degree `n`, the interval `I(A_0) = {F : deg(F - A_0) < h}` has
`#{F in I(A_0) : d | F} = 2^{h-k}` exactly for every monic `d` of degree
`k <= h`. (Same proof: the map from the top `ell` coefficients of `m` to the
coefficients of `x^{n-1}, ..., x^h` of `dm` is unitriangular, hence a bijection.)
`W_n` is the case `A_0 = x^n`. Verified for `n <= 14` and four centres each.

**Machine check.** `axeyum-lemire-sieve typei n 3` enumerates every element of
`W_n`, factors it, and tallies `A_d` over all its divisors of degree
`<= h + 3`. Over `n = 2 .. 34` (454 rows, `data/sieve-typeI-n2-34.txt`):
**zero exceptions**. For `k <= h` the number of distinct `d` seen is exactly
`2^k` and `min A_d = max A_d = 2^{h-k}`; for `h < k <= n` the maximum is `1` and
the number of `d` seen is exactly `2^h`; and `sum_{deg d = k} A_d = 2^h` on every
row with `k <= n`. The checker independently recomputes all of this with
python-flint for `6 <= n <= 20` (153 `(n,k)` pairs), and verifies the reversal
criterion of Lemma 1 on every monic `d` of degree `h < k <= h+3`.

**Consequence for the sieve.** `W_n` has level of distribution `D = 2^h = |W_n|`
with identically vanishing remainders. To detect an irreducible of degree `n` one
must sift by every irreducible of degree `<= floor(n/2)`, i.e. `z = 2^{n/2}`, so

```text
s = log D / log z = h / (n/2) = 1 + 2/n  ->  1.
```

`s = 1` is the parity line: `f(s) = 0` for `s <= 2`. Section 6 makes the failure
exact rather than asymptotic.

## 2. Mertens for `F_2[t]`

The sieve density is `omega(P)/|P| = 2^{-deg P}`, and
`sum_{deg P <= y} (deg P) 2^{-deg P} = y + O(1)`: sieve dimension `kappa = 1`
(linear sieve), with `log X` playing the role of `n log 2` and `log z` of
`y log 2`, so `s` is a ratio of degrees and `log q` cancels.

**Lemma 5 (Mertens over `F_q[t]`, exact form).** Let
`V(y) = prod_{deg P <= y} (1 - |P|^{-1})` over monic irreducibles of `F_q[t]`.
Then

```text
log(1/V(y)) = H_y + R_y,   H_y = sum_{N <= y} 1/N,   |R_y| <= 4 q^{-y/2},
```

hence `V(y) = e^{-gamma} / y (1 + O(1/y))` -- the classical Mertens constant,
with no `q`-dependent correction.

*Proof.* `-log(1-u) = sum_r u^r / r` gives
`log(1/V(y)) = sum_{m <= y} I_m sum_{r >= 1} q^{-mr}/r`, `I_m` the number of
monic irreducibles of degree `m`. Reindex by `N = mr`: the coefficient of
`q^{-N}` is `(1/N) sum_{m | N, m <= y} m I_m`. For `N <= y` every divisor `m` of
`N` satisfies `m <= N <= y`, and `sum_{m | N} m I_m = q^N`, so those terms
contribute exactly `sum_{N <= y} 1/N`. For `N > y` only proper divisors `m <= y`
survive, so `m <= N/2` and
`sum_{m | N, m <= N/2} m I_m <= sum_{m <= N/2} q^m <= 2 q^{N/2}`, whence
`|R_y| <= sum_{N > y} 2 q^{-N/2}/N <= 4 q^{-y/2}`. QED

Machine-checked at `q = 2` for `1 <= y <= 40` at 60 digits (the residual is
`< 4 . 2^{-y/2}` on every row) and `y V(y)/e^{-gamma} = 0.9876` at `y = 40`,
matching `1 - 1/(2y)`. Mutation control M6 (constant doubled) trips.

## 3. What the linear sieve proves

The sieve axioms are verified: `|A| = 2^h`, `omega` multiplicative with
`omega(P) = 1`, dimension `1` (section 2), remainders `r_d = 0` for
`deg d <= h` (Lemma 1). So the Jurkat--Richert linear sieve
(Friedlander--Iwaniec, *Opera de Cribro*, Thm. 11.12; Halberstam--Richert Thm.
8.3) applies verbatim with `D = 2^h`, `z = 2^y`, `s = h/y`, and with the
remainder sum *identically zero* -- the one place where the function field is
strictly better than `Z`.

```text
f(s) = 0            (s <= 2),        f(s) = 2 e^gamma log(s-1) / s   (2 <= s <= 4),
F(s) = 2 e^gamma / s   (0 < s <= 3).
```

**Theorem 6 (`P_4` with large factors).** For every `eps > 0` there is
`n_0(eps)` such that for `n >= n_0(eps)`, `W_n` contains an `F` all of whose
irreducible factors have degree `> (1/4 - eps) n`. Since four factors of degree
`> n/4` would have total degree `> n`, such an `F` has at most **4** irreducible
factors with multiplicity.

*Proof.* Take `y = floor((1/4 - eps)n)`, so `s = h/y = 2/(1 - 4eps) + O(1/n)` is
bounded away from `2`; `f(s) >= 8 e^gamma eps + O(eps^2)` is a positive constant
and beats the sieve's `O((log D)^{-1/3}) = O(n^{-1/3})` error for `n` large. The
remainder sum is `0`. QED

Note this is `P_4`, not `P_3`: the diary brief's "`s > 2` hence at most 3
factors" is off by one, because `4/(1-4eps) > 4`. `P_3` needs a weight.

**Theorem 7 (`P_3`, Kuhn weights).** Let `1/8 <= alpha < 1/6`. For
`n >= n_0(alpha)`, `W_n` contains an `F` with `Omega(F) <= 3` all of whose
irreducible factors have degree `> alpha n`.

*Proof.* Put `y_1 = alpha n`, `y_2 = n/3`, `lambda = 1/2`, and

```text
Sigma = sum_{F in W_n, (F, Pi(y_1)) = 1} ( 1 - (1/2) #{P | F : y_1 < deg P <= y_2} )
```

(the inner count with multiplicity). If `Sigma > 0` some `F` has no irreducible
factor of degree `<= y_1` and at most one factor in `(y_1, y_2]`. If such an `F`
had `Omega(F) = t >= 4` then, since at most `2` factors can have degree `> n/3`,
at least `t - 2 >= 2` lie in `(y_1, y_2]` -- contradiction. So `Omega(F) <= 3`.

For the lower bound, `Sigma >= S(W_n, y_1) - (1/2) sum_{y_1 < deg P <= y_2}
S(A_P, y_1) - O(2^{h-y_1}/y_1)` (the last term absorbs prime powers). Each
`A_P = {F in W_n : P | F}` has `|A_P| = 2^{h-p}` and, by Lemma 1 applied to `Pd`,
**exact** Type-I data to level `2^{h-p}`, so `s_P = (h-p)/y_1 <= 1/(2alpha) - 1
<= 3` and the linear-sieve upper bound applies with `F(s_P) = 2 e^gamma / s_P`.
Dividing by `|W_n| V(y_1)`, using `I_p 2^{-p} = 1/p + O(2^{-p/2}/p)` and
`V(y_1) = e^{-gamma}/y_1 (1 + O(1/y_1))` (Lemma 5),

```text
Sigma / (|W_n| V(y_1))  ->  f(1/(2 alpha)) - 2 e^gamma alpha [ log(t/(1/2 - t)) ]_{alpha}^{1/3}
                          = 4 e^gamma alpha log((1-2alpha)/(2alpha))
                              - 2 e^gamma alpha log((1-2alpha)/alpha)
                          = 2 e^gamma alpha log( (1-2alpha) / (4 alpha) )  =:  G(alpha),
```

which is `> 0` exactly for `alpha < 1/6`. QED

```text
alpha    1/8      2/15     1/7      2/13     1/6.2    1/6
s_1      4.000    3.750    3.500    3.250    3.100    3.000
f(s_1)   0.9784   0.9609   0.9326   0.8888   0.8525   0.8230
G        0.1805   0.1513   0.1136   0.0646   0.0280   0.0000
```

**`n_0` explicitly.** The only non-numeric input is the absolute constant `K` in
the Jurkat--Richert error `K (log D)^{-1/3}`; I know of no published value. At
`alpha = 1/8` the margin is `G = 0.1805`, the error enters with multiplier
`1 + lambda sum_{y_1 < p <= y_2} 1/p = 1 + (1/2)log(8/3) = 1.49`, and the
`O(1/y_1)` arithmetic errors are below `0.03` once `n > 300`. So it suffices that
`1.49 K (log D)^{-1/3} < 0.15` with `log D = h log 2 > 0.34 n`, i.e.

```text
n_0(1/8) = max( 300, 2825 K^3 ).     K = 1/2: n_0 = 354.   K = 1: n_0 = 2828.
```

Richert's continuous weights would raise the reachable `alpha` above `1/6`
somewhat; they do not change the `alpha < 1/4` ceiling, which is
`f(1/(2alpha)) > 0`.

**Theorem 8 (fully explicit, no sieve black box).** Let `r, y` satisfy
`(2r+1) y <= h` and `sum_{j >= 2r+2} m(y)^j / j! < V(y)`, where
`m(y) = sum_{deg P <= y} 2^{-deg P}`. Then, by Bonferroni truncation of the
Legendre sieve -- every divisor occurring has degree `<= (2r+1)y <= h`, so by
Lemma 1 **every** term is exact --

```text
S(W_n, y) >= 2^h ( V(y) - sum_{j >= 2r+2} m(y)^j / j! ) > 0.
```

Admissible pairs (computed exactly, 60 digits):

```text
y        3     5     7    10    11    18    30    38
2r+1     5     5     7     7     9     9    11    13
h >=    15    25    49    70    99   162   330   494
n >=    28    48    96   138   196   322   658   986
```

So, unconditionally and with no unspecified constant: `W_n` contains an element
with no irreducible factor of degree `<= 3` for every `n >= 28`, none of degree
`<= 10` for `n >= 138`, none of degree `<= 30` for `n >= 658`. Since `2r+1` grows
like `e^2 log y`, this route gives `P_r` only with `r = O(log n)`; the fixed `r`
of Theorems 6 and 7 needs Jurkat--Richert.

**Why `P_3` with factors `> n/4` is out of reach, exactly.** "All factors of
degree `> n/4`" is equivalent to `Omega <= 3` together with that degree bound
(four factors would overflow the degree), and the census below shows such `F`
are abundant -- about `5%` of `W_44`. But proving it needs `y` with
`y + 1 > n/4` and `s = h/y > 2`, and

```text
y = n/4  =>  s = h/y = (n/2 + 1)/(n/4) = 2 + 4/n,   f(s) = 4 e^gamma / n + O(1/n^2),
```

against a sieve error `K (log D)^{-1/3} ~ K (0.34 n)^{-1/3}`. The ratio
`f(s)/error ~ 7.1 / (K n^{2/3}) -> 0`: the linear sieve never proves it, at any
`n`. The margin the window offers past `X^{1/2}` is `+1` in `h`, i.e. the same
one-bit / `log`-sized surplus that Hayes--Weil is short of (note 00), showing up
here as `s - 2 = 4/n`.

## 4. The census (CAS), against the sieve

`axeyum-lemire-sieve factor n` factors every element of `W_n` and reports the
joint histogram of `(Omega, least factor degree)`; `n = 2 .. 44`,
`data/sieve-window-factorizations-n2-44.txt`. Its `IRRED` column reproduces the
lane's independently pinned `irreducible-counts-n2-38.txt` on every row, and
python-flint reproduces the whole histogram for `n <= 22`.

**Table 1.** `S(>t)` is `#{F in W_n : every irreducible factor has degree > t}`.

```text
   n |   |W_n| |    I_n | S(>n/4) | S(>n/6) | S(>n/8) | Om<=2  | Om<=3   | Om<=3, >n/8 | S(>n/4)/|W_n|
  12 |      128 |     12 |      19 |      24 |      32 |     33 |      66 |          29 | 0.1484
  16 |      512 |     28 |      60 |      96 |      96 |    124 |     234 |          91 | 0.1172
  20 |     2048 |    101 |     202 |     294 |     384 |    394 |     853 |         363 | 0.0986
  24 |     8192 |    320 |     690 |     967 |    1176 |   1505 |    3029 |        1124 | 0.0842
  28 |    32768 |   1195 |    2420 |    3877 |    4704 |   5028 |   11410 |        4422 | 0.0739
  32 |   131072 |   4024 |    8586 |   12818 |   15504 |  18679 |   42015 |       14780 | 0.0655
  36 |   524288 |  14716 |   30739 |   44483 |   62016 |  67490 |  158922 |       57976 | 0.0586
  40 |  2097152 |  52039 | 111756 |  177959 |  205039 | 250161 |  597382 |      195351 | 0.0533
  44 |  8388608 | 191124 | 407981 |  618035 |  820154 | 925430 | 2266867 |      766763 | 0.0486
```

Checked for every `n <= 44`: `S(>n/4) > 0` (so the `P_3`-with-large-factors
statement is *true* in the whole computed range even though the sieve cannot
prove it), and `S(>n/4)` equals `#{Omega <= 3 and all factors > n/4}` on every
row -- the degree bound alone forces `Omega <= 3`. Mutation control M4 lowers the
threshold to `n/5`, where the implication is false, and trips.

The Jurkat--Richert **main term** at the largest admissible `y` (i.e. `y` the
largest integer with `h/y > 2`) is below the truth on every row `n >= 12`, as it
must be; but at these `y` the sieve error exceeds the main term, so the column is
an arithmetic consistency check, not a proof. Sample: `n = 44`, `y = 11`,
`s = 2.091`, main term `60531` against `S(>11) = 407981`.

## 5. The exact Brun--Titchmarsh upper bound

**Theorem 9 (exact, no error term).** Let `L = floor(h/2)` and

```text
G_L = sum over squarefree monic d with deg d <= L of  prod_{P | d} (|P| - 1)^{-1}.
```

Then `#{F in W_n : F irreducible} <= |W_n| / G_L`.

*Proof.* Selberg's `Lambda^2` sieve with weights supported on `deg d <= L`: the
quadratic form is `sum_{d_1,d_2} lambda_{d_1} lambda_{d_2} A_{[d_1,d_2]}` and
`deg [d_1,d_2] <= 2L <= h`, so by Lemma 1 every entry is **exactly**
`2^{h - deg[d_1,d_2]}` and the standard diagonalisation gives `|A|/G_L` with no
remainder at all. An `F in W_n` with no irreducible factor of degree `<= L` and
degree `n > 2L` need not be irreducible, but every irreducible is counted. QED

```text
   n |  h |  L |    G_L | |W_n|/G_L |    I_n | bound/truth
   10 |  6 |  3 |  5.286 |      12.1 |      7 |  1.73
   16 |  9 |  4 |  6.391 |      80.1 |     28 |  2.86
   24 | 13 |  6 |  8.373 |     978.4 |    320 |  3.06
   32 | 17 |  8 | 10.382 |   12625.0 |   4024 |  3.14
   40 | 21 | 10 | 12.381 |  169380.9 |  52039 |  3.25
   44 | 23 | 11 | 13.383 |  626801.0 | 191124 |  3.28
```

`G_L = L + 1.38 + o(1)`, so the bound is `(2 + o(1)) |W_n| / h = (4 + o(1))
|W_n| / n`, exactly the classical Brun--Titchmarsh `2 y / log y` at
`log y = (1/2) log X`, and a factor `4` above the truth `~ |W_n| / n`. Verified
for every even `n <= 40`. Mutation control M5 triples `L` (illegitimate: the
remainders no longer vanish) and the "bound" drops below the truth at `n = 10`,
which is exactly the point -- the level restriction `2L <= h` is load-bearing.
Compare Hsu (JNT 1996) and Bagshaw--Kerr (Mathematika 2025), which are
Brun--Titchmarsh upper bounds in `F_q[T]`; the novelty here is only that the
window's remainders vanish identically, so the bound has no error term.

## 6. The parity population, and the level at which the data forces a prime

### 6.1 The LP duality statement

Fix `n` and a level `K`. A **lower-bound sieve certificate at level `K`** is a
family of reals `(lambda_d)` indexed by the monic `d` with `deg d <= K` such that

```text
sum_{d | F, deg d <= K} lambda_d  <=  1[F irreducible]     for every F in M_n.        (C)
```

Any such family gives `#{irreducible in W_n} >= sum_d lambda_d A_d`, and this is
exactly what every lower-bound sieve (Brun, Selberg-`Lambda^2`-plus-Buchstab,
Rosser--Iwaniec, Kuhn or Richert weights, and any linear combination of them) is:
the sieve only ever learns `A_d`. Note (C) is required on all of `M_n` and not
merely on `W_n`, because a sieve never learns which subset of `M_n` its sequence
is; section 6.4 measures what changes if one grants it that.

**Theorem 10 (LP duality).** Put

```text
LP(n,K) = min { sum_{F in M_n irreducible} w(F)  :  w >= 0 on M_n,
                sum_{F : d | F} w(F) = 2^{n - deg d} for every monic d, deg d <= K }.
```

Then `2^{h-n} LP(n,K)` is exactly the supremum of `sum_d lambda_d A_d` over
certificates (C). In particular `LP(n,K) = 0` if and only if there exists a
nonnegative `w` on `M_n` vanishing on every irreducible with the exact Type-I
data, and in that case **no lower-bound sieve at level `2^K` can prove that `W_n`
contains an irreducible.**

*Proof.* The primal above and the dual `max sum_d lambda_d 2^{n - deg d}` subject
to (C) are an LP pair; both are feasible (`w = 1`; `lambda = 0`), so strong
duality applies. A certificate has `sum_{d | F} lambda_d = lambda_1` for
irreducible `F` (no other divisor has degree `<= K < n`), so normalising
`lambda_1 = 1` is free, and `sum_d lambda_d A_d = 2^{h-n} sum_d lambda_d
2^{n - deg d}` by Lemma 1. QED

Define `k_max(n) = min { K : LP(n,K) > 0 }`. The window's own exact level is
`K = h`, so **the barrier is the statement `k_max(n) > h`**, and `k_max(n) - h`
measures how much more than the truth a sieve would have to be handed.

### 6.2 The transfer bound, and why a sieve proof would prove Legendre

**Proposition 11.** For every monic `A_0` of degree `n`, and every certificate
(C) at level `K <= h`,

```text
sum_d lambda_d A_d  <=  #{ F irreducible : deg(F - A_0) < h }.
```

Hence the best level-`2^h` sieve lower bound for the irreducibles in `W_n` is at
most `min_{A_0} #{irreducible in I(A_0)}`, the minimum over *all* `2^ell`
top-half patterns.

*Proof.* Sum (C) over `F in I(A_0)` and use Corollary 4: the left side is
`sum_d lambda_d 2^{h - deg d} = sum_d lambda_d A_d`. QED

**Corollary.** A sieve proof of Kaser--Lemire from Type-I data at the window's
own level would *simultaneously* prove Legendre's conjecture for `F_2[t]` -- that
every window `{A_0 + g : deg g <= floor(n/2)}` contains an irreducible, for every
monic `A_0` of degree `n`. That is exactly the uniform conjecture of angle 5
(diary, "five angles" item 5), so **the sieve face cannot separate the identity
class from the uniform statement**; it is blind to the very distinction that
Barriers I--III of note 00 are about. Checked: for `6 <= n <= 16` every one of
the `2^ell` windows does contain an irreducible (minimum over windows `2, 2, 2,
2, 5, 4, 4, 6, 13, 11, 24`), consistent with note 05 section 4.

### 6.3 Exact prime-free populations

**Theorem 12 (parity barrier, exact, machine-checked).** For each
`n in {10, 11, 12, 13, 14, 15}` there is an explicit nonnegative rational `w` on
`M_n` with

```text
w(F) = 0 for every irreducible F of degree n,
sum_{F in M_n, d | F} w(F) = 2^{n - deg d}  exactly, for every monic d of degree <= h.
```

Consequently `LP(n,h) = 0` and no lower-bound sieve at level `2^h` can prove that
`W_n` contains an irreducible.

The witnesses are in `data/sieve-parity-population-n{10,...,15}.txt`, one exact
fraction per polynomial (supports `113, 122, 237, 242, 482, 501`). The checker
re-verifies, over `Q` with `Fraction` arithmetic: nonnegativity, vanishing on
every irreducible, and **all** `2^{h+1} - 1` Type-I equalities. Mutation controls
M2 (a unit of mass moved onto an irreducible) and M3 (one value perturbed by
`1/7`) both trip.

Provenance: the support comes from an LP vertex (HiGHS); the values are then
re-solved exactly over `Q` on that support by rational Gaussian elimination, so
the certificate is exact and the floating-point solve is only a search heuristic.

**Remark (the classical Liouville example is not exact enough).** The textbook
parity population `w = 1 + lambda` (`lambda` the Liouville function, so `w = 2`
on `Omega` even and `0` on `Omega` odd, killing the primes) has

```text
sum_{F : d | F} w(F) = 2^{n-k} + lambda(d) L(n-k),   L(j) = sum_{deg m = j} lambda(m),
```

and over `F_2[t]`, `sum_F lambda(F) u^{deg F} = (1-2u)/(1-2u^2)`, so
`L(j) = 2^{j/2}` (`j` even), `-2^{(j+1)/2}` (`j` odd) -- never zero. Its Type-I
remainders are of exact square-root size `|r_d| <= sqrt(2 . 2^n/|d|)`, which the
window's *identically zero* remainders distinguish. Indeed the LP says more:
**demanding the support lie inside `{Omega even}` is infeasible for every
`n in {8,...,16}` tested.** The exact-data population must put mass on
`Omega = 3, 5, ...` as well; the minimum forced odd-`Omega` mass is

```text
n            8      10      11      12      13      14      15      16
mass/2^n  0.1563  0.1108  0.1406  0.0423  0.0729  0.0321  0.0375  0.0094
```

i.e. of square-root order, decaying like the `2^{-(n-h)/2}` the Liouville defect
predicts. A completely multiplicative correction is impossible: if `w = 1 + theta`
with `theta` completely multiplicative and `theta(P) = -1` for every irreducible
`P`, then `theta = lambda`. So any exact prime-free population is genuinely
non-multiplicative -- which is why the construction here is an LP witness and not
a formula.

### 6.4 `k_max(n)`: the level at which the data does force a prime

**Table 3** (`data/sieve-lp-levels.txt`; values in the `M_n` normalisation, so
divide by `2^{n-h}` for the `W_n` scale).

```text
  n |  h | LP(n,h-1) | LP(n,h) | LP(n,h+1) | LP(n,h+2) |  I_n  | k_max(n) | k_max - h
  6 |  4 |         0 |       4 |         8 |         9 |     9 |        4 |     0
  7 |  4 |         0 |       8 |        16 |        18 |    18 |        4 |     0
  8 |  5 |         0 |       8 |        20 |        26 |    30 |        5 |     0
  9 |  5 |         0 |      16 |        40 |        52 |    56 |        5 |     0
 10 |  6 |         0 |       0 |        48 |        76 |    99 |        7 |     1
 11 |  6 |         0 |       0 |        96 |       144 |   186 |        7 |     1
 12 |  7 |         0 |       0 |        96 |       192 |   335 |        8 |     1
 13 |  7 |         0 |       0 |       192 |    336.23 |   630 |        8 |     1
 14 |  8 |         0 |       0 |        32 |    344.08 |  1161 |        9 |     1
 15 |  8 |         - |       0 |        64 |         - |  2182 |        9 |     1
 16 |  9 |         - |       0 |         0 |    298.08 |  4080 |       11 |     2
 17 |  9 |         - |       0 |         0 |         ? |  7710 |     >=11 |  >=2
```

Readings.

- The barrier switches on at `n = 10`. For `6 <= n <= 9` the exact Type-I data at
  level `2^h` *does* force a prime; from `n = 10` it does not. Small-`n`
  intuition about this problem is therefore actively misleading.
- For `10 <= n <= 15`, `k_max(n) = h + 1` exactly: **one more level** of exact
  data would settle the window. That level is not available even in principle
  (Corollary 3). At `n = 16` even `h + 1` is not enough, and the trend of
  `k_max - h` is upward, consistent with the asymptotic expectation
  `k_max(n) ~ n` (the parity principle is `s > 2`, i.e. `K > n`).
- The `LP(n,h+1)` values, put on the `W_n` scale, are far *below* the truth: at
  `n = 10`, `48 . 2^{-4} = 3` against `I_10(1) = 7`; at `n = 14`,
  `32 . 2^{-6} = 0.5` against `19`. So even a sieve handed one impossible extra
  level would prove only a fraction of the truth.
- `LP(n,n) = I_n` always (the level-`n` data pins `w = 1`), and `LP` is
  nondecreasing in `K`; both checked.

**Contrast: confining the population to `W_n`.** If one *additionally* tells the
argument that the population is supported on `W_n` itself, the picture inverts:
the LP value equals the full irreducible count of `W_n` already at `K = h`
(measured: `n = 11, 12, 13` give exactly `I_n(1) = 4, 12, 6` at `K = h` and `0`
at `K = h-1`; `n = 14` gives `18` of `19` already at `K = h-1` and `19` at
`K = h`). The reason is Lemma 1 at `k = h`, where
`A_d = 1` is a singleton constraint pinning `b(F) = 1` for every `F in W_n` with a
divisor of degree `h`; the lower levels then propagate. This is *not* a sieve
statement -- the certificate it produces uses the arithmetic of which `d` divide
which `F`, i.e. it presupposes the answer -- but it is a sharp statement about
information: **the Type-I data at level `2^h` determines the number of
irreducibles in `W_n` if one is also told the population lives in `W_n`.** What a
sieve lacks is not the data; it is the confinement.

## 7. Chen, switching, and Iwaniec's bilinear remainder

- **Chen's `P_2` is not reachable without Type II.** Chen's switching principle
  needs, besides the linear sieve at level `X^{1/2}`, an upper bound for the
  count of `F = P_1 P_2 P_3` with `deg P_1` small, obtained from
  Bombieri--Vinogradov-strength Type-I-on-average *for the shifted sequence*.
  Here the sequence is the window itself: the analogous input is exact Type-I
  data at level beyond `2^h`, which Corollary 3 rules out absolutely (the total
  remainder at any level `k > h` is `2|W_n|`). The bilinear input enters at
  exactly that point.
- **Bombieri's asymptotic sieve** needs Type I to level `X^{1-delta}`. We have
  `X^{1/2}` and provably nothing more, so it does not apply at all.
- **Iwaniec's well-factorable / bilinear remainder form** of the linear sieve
  replaces `sum_{deg d <= K} |r_d|` by `sum_d lambda_d r_d` with `lambda`
  well-factorable, i.e. by bilinear sums in the remainders. For `deg d = k > h`
  the remainders are `r_d = A_d - 2^{h-k}` with `A_d in {0,1}`, so
  `sum_d lambda_d r_d = sum_d lambda_d A_d - 2^{h-k} sum_d lambda_d`, and the
  first sum is exactly a bilinear count of products landing in the window. That
  is the Type II form of the next section: **the well-factorable remainder sums
  for `deg d > h` ARE the missing Type II estimate**, not an alternative to it.

## 8. Type II transplant

**Proposition 13 (transplant).** Let `M + L = n` and let `alpha, beta` be
arbitrary complex coefficients on the monic polynomials of degrees `M`, `L`. With
`<G>_ell = x^{deg G} G(1/x) mod x^{ell+1}` in `E_ell` and `chi` running over the
`2^ell` characters of `E_ell`,

```text
B(M,L; alpha, beta) := sum_{deg m = M} sum_{deg l = L} alpha_m beta_l 1[ m l in W_n ]
                     = 2^{-ell} sum_chi A_M(chi) B_L(chi),
A_M(chi) = sum_{deg m = M} alpha_m chi(<m>_ell),   B_L(chi) = sum_{deg l = L} beta_l chi(<l>_ell).
```

*Proof.* `<.>_ell` is multiplicative, `m l in W_n` is `<ml>_ell = 1`, and
`1[g = 1] = 2^{-ell} sum_chi chi(g)` on `E_ell`. QED

So every Type II sum over the window is a `chi`-average over the *same* Hayes
family that carries `S_n(chi)`, with `A_M(chi) B_L(chi)` in place of `S_n(chi)`;
the `alpha = beta = 1` case is the ball-transform pair whose `n`-th power sums
build `L(chi, T)` (note 01 section 3, and the horizontal cohomology of angle 4 is
exactly this case). The main term is the `chi = 1` contribution
`2^{-ell} (sum alpha)(sum beta) = 2^{h-n} (sum alpha)(sum beta)`; a Type II
estimate with saving `n^{-A}` is precisely a bound of size `2^{h-n} |sum alpha|
|sum beta| n^{-A}` for `sum_{chi != 1} A_M(chi) B_L(chi)`. Since the prime count
itself is `2^{-ell} sum_chi S_n(chi)` and Vaughan's identity writes `S_n(chi)` as
a fixed finite combination of Type I pieces (exact, Lemma 1) and Type II pieces
of the above shape, **the sieve route does not bypass `(REL)`/`(HWO)`: it
re-weights the same sum over the same family, and the cancellation still has to
come from across `chi`.** Note 08 v1 asserted this; this is the proposition.

**Converse, stated honestly.** `(HWO)` gives the *count*: it bounds the layer
sums `T_{j,s}` of `S_n(chi)`, which through the Haar telescope yields
`N_ell(1) > 0`. It does **not** give the bilinear forms: those are statements
about `A_M(chi) B_L(chi)` for arbitrary `alpha, beta`, uniform in the
coefficients, and imply (for example) Mobius/Liouville cancellation in the window
of the Carmon--Rudnick type. Type II `=>` count; `(HWO)` `=>` count; Type II is
strictly stronger than `(HWO)` in content and neither implies the other formally.
The useful range for the asymptotic sieve is `M, L` both `>= delta n`, i.e. both
factors longer than any Type-I range, which is exactly `deg d > h` -- the region
Corollary 3 shows is remainder-saturated.

## 9. Connections to record

1. **Legendre for `F_2[t]` = angle 5's uniform conjecture, and the sieve cannot
   tell them apart.** Proposition 11 and its corollary: because every window
   `I(A_0) = {A_0 + g : deg g <= floor(n/2)}` has the *same* exact Type-I data
   (Corollary 4), any sieve bound at level `2^h` that is positive for `W_n` is
   positive for every window. Kaser--Lemire is the single window `A_0 = x^n`;
   angle 5's uniform conjecture is all `2^ell` of them. A sieve proof of the one
   is automatically a proof of the other. Conversely a single prime-free window
   at some `n` would kill the level-`2^h` sieve route outright; none exists for
   `n <= 16` (checked here) or in note 05's range.
2. **Provenance.** Ellenberg's 2011 MathOverflow answer (MO 81717) posed exactly
   this face -- Legendre's conjecture for `F_2[t]`, with Cramer-under-RH giving
   `n/2 + log n`. Voloch's MO 39100 (2010) is the Carlitz-curve face of the same
   window. The sieve content of Ellenberg's remark is Lemma 1 plus `s = 1`; this
   note makes both exact and adds what the sieve does and does not give.
3. **Where angle 2 meets angle 4.** Proposition 13's `A_M(chi) B_L(chi)` at
   `alpha = beta = 1` is the object whose `n`-th power sums are the `S_n(chi)` of
   note 12; the horizontal (conductor-aspect) sums `A_r(n,j)` of angle 4 are the
   `alpha = beta = 1`, unweighted case. Angle 2's endpoint (a Type II estimate
   with saving `n^{-A}` for `M, L >= delta n`) and angle 4's `(Q1')` (the pair
   `(i_max, C)` for the layer representation) are two coordinates on the same
   sum: `(Q1')` controls each `chi` geometrically, Type II controls the weighted
   average over `chi`. Neither is implied by the other.

## 10. Reproduction

```sh
# CAS (primary engine), from the lane snapshot
S=/data0/axeyum/scratch/snap-lemire-signed-trace-47fd7b440
$S/target/release/axeyum-lemire-sieve selfcheck 20000     # -> mismatches=0
$S/target/release/axeyum-lemire-sieve typei 24 3
$S/target/release/axeyum-lemire-sieve factor 40
$S/target/release/axeyum-lemire-sieve dump 14

# checker (independent cross-check + all mutation controls), ~2 s
/data0/axeyum/scratch/lemire-signed-trace-lemire-venv/bin/python \
    scripts/lemire-signed-trace/lemire_sieve_face.py        # -> SIEVE-FACE OK
```

Data: `scripts/lemire-signed-trace/data/sieve-typeI-n2-34.txt`,
`sieve-window-factorizations-n2-44.txt`, `sieve-lp-levels.txt`,
`sieve-parity-population-n{10,...,15}.txt`. Rust source mirror:
`scripts/lemire-signed-trace/axeyum-lemire-sieve.rs.txt`.

## 11. Corrections to earlier notes

- **Note 04, shape 4 ("Literature"):** "no Harman/Chen-type lower-bound sieve
  exists in `F_q[T]`" is too strong. The linear sieve applies verbatim over
  `F_q[t]` (dimension `1`, Lemma 5 supplies Mertens); what fails is not the
  machinery but the sifting parameter, `s = 1` at the prime level. Theorems 6--8
  are lower-bound sieve results in `F_2[t]` for this very window.
- **Diary brief for angle 2:** "`s > 2` ... hence at most 3 irreducible factors"
  is off by one; `s > 2` at `y = (1/4 - eps) n` gives at most **4**. `P_3`
  requires a weighted sieve (Theorem 7) and then only for factors of degree
  `> alpha n` with `alpha < 1/6`.
- **Diary brief, task C:** the parity population cannot be supported on `W_n`
  itself. Confined to `W_n`, the exact Type-I data at level `2^h` *determines*
  the irreducible count (section 6.4). The barrier is real but lives on `M_n`,
  which is also the correct sieve formalisation, since a sieve never learns the
  confinement.
- **Note 03 section 5 (Barrier I) is a different object.** Barrier I is a
  population on the class group `E_ell` matching the *Fourier* data of low
  conductor and obeying Weil at high conductor; the population here is on `M_n`
  and matches the *divisor* data exactly to level `2^h`. Neither implies the
  other: Barrier I's `F` is supported on classes, so it says nothing about
  factorisations, while the sieve population has no control on its Fourier
  coefficients at conductor `>= a`. They are two barriers, not one, and they
  block disjoint method classes (moduli-only Fourier arguments; Type-I-only
  sieve arguments).
