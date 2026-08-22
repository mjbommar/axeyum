# Almost all top halves: an unconditional theorem and the residual

Companion to [01-target-and-toolkit.md](01-target-and-toolkit.md) (the target),
[03-uncertainty-analogy.md](03-uncertainty-analogy.md) section 5 (the barrier),
[04-shape-verdicts.md](04-shape-verdicts.md) (the five shapes). Reproduced by
`scripts/lemire-signed-trace/lemire_almostall.py` (exact integers on the class
dumps; five mutation controls; exit 1 on any violation).

says what is not, and why this argument cannot reach it.

### 1. Setting and the three inputs

`E_ell = (1 + x F_2[x])/(x^{ell+1})`, `|E_ell| = 2^ell`, `<F>_ell = x^{deg F}F(1/x) mod
x^{ell+1}`. For monic `f` of degree `n`, `<f>_ell = 1 + a_{n-1}x + ... + a_{n-ell}x^ell`,
so `g <-> h = (a_{n-1},...,a_{n-ell})` matches classes with **top halves**. Put
`N_ell(g) = sum_{deg F = n, <F>_ell = g} Lambda(F)` (mean `2^{n-ell}`, total `2^n`) and
`S_n(chi) = sum_{deg F = n} Lambda(F) chi(<F>_ell)`.

Three inputs only. **(O)** Parseval on `E_ell`. **(W)** RH (Weil): for `chi` of conductor
`j`, `L(u,chi) = prod_{i<=j-1}(1-alpha_i u)` with `|alpha_i| in {0, sqrt 2}` and
`S_n(chi) = -sum_i alpha_i^n`, so `|S_n| <= (j-1)2^{n/2} <= (j-1)2^{ceil(n/2)}`; conductor
`1` gives `L = 1`, hence `S_n = 0`. **(C)** Exactly `2^{j-1}` characters have conductor
exactly `j`, `1 <= j <= ell`, plus the trivial one.

### 2. Theorem A (Lambda-mass, unconditional)

Let `ell >= 1`, `n in {2ell+1, 2ell+2}`, `0 < t <= 1`, and put
`eps(ell) = (ell^2 - 4 ell + 6) - 6*2^{-ell}`, `kappa_n = 2^{2 ceil(n/2) - n} in {1,2}`.
Then

```text
#{ g : |N_ell(g) - 2^{n-ell}| >= t 2^{n-ell} }  <=  kappa_n 2^{2ell-n} eps(ell) / t^2
   =  eps(ell)/t^2   (n = 2ell+1),      =  eps(ell)/(4 t^2)   (n = 2ell+2),
```

a fraction `<= eps(ell)/(t^2 2^ell)`.

*Proof.* With `D = N_ell - 2^{n-ell}`, (O) gives `sum_g D^2 = 2^{-ell} sum_{chi != 1}
|S_n(chi)|^2`. By (W) and (C),

```text
sum_{chi != 1}|S_n|^2 <= 2^{2 ceil(n/2)} sum_{j=1}^{ell} 2^{j-1}(j-1)^2 = 2^{2ceil(n/2)}A(ell),
A(ell) = sum_{i=1}^{ell-1} i^2 2^i = 2^ell(ell^2 - 4 ell + 6) - 6   (induction on ell),
```

so `sum_g D^2 <= 2^{2 ceil(n/2)} eps(ell) = kappa_n 2^n eps(ell)`; Chebyshev at threshold
`t 2^{n-ell}` finishes. QED

Using `|S_n| <= (j-1)2^{n/2}` gives `kappa_n = 1`, halving the odd-`n` constant: the
`2^{ceil(n/2)}` convention costs a factor 2 at `n = 2ell+1` and nothing at `n = 2ell+2`. At
`t = 1/2` the exceptional fraction is `4 eps 2^{-ell}` (odd `n`) and `eps 2^{-ell}` (even);
the `8 ell^2 2^{-ell}` of notes 03/04 is that to within a factor 2 (odd) / 8 (even).

The Keating--Rudnick/Sato--Tate second moment `sum_{cond=j}|S_n|^2 ~ 2^{j-1}(j-1)2^n`
would replace `A(ell)` by `2^ell(ell-2)+2`, saving a factor `~ell`. It is **not**
unconditional: KR is a `q -> infinity` theorem, and by (O) the exact second moment *is* the
quantity being bounded, so Parseval cannot supply it. Section 4 measures it at `1.00 x`
Sato--Tate -- evidence, not a theorem.

### 3. Theorem B (irreducibles, with the proper-power bookkeeping)

Let `A_n(h)` be the monic `f` of degree `n` with `(a_{n-1},...,a_{n-ell}) = h`. For
`ell >= 5` and `n in {2ell+1, 2ell+2}`,

```text
#{ h in F_2^ell : A_n(h) contains no irreducible }
   <= 4(ell^2 - 4 ell + 6) < 4 ell^2   (n = 2ell+1),
   <=  (ell^2 - 4 ell + 6) <   ell^2   (n = 2ell+2),
```

so all but a fraction `< 4 ell^2 2^{-ell}` of the `2^ell` top halves are the top half of an
irreducible of degree `n` (a positive proportion once `ell >= 9`).

*Proof.* Let `Theta(g)` be the Lambda-mass of *proper* prime powers in class `g`, so
`n I_n(g) = N_ell(g) - Theta(g)`, and globally `Theta_n = 2^n - n I_n = sum_{d|n,d<n} dI_d`.
For odd `n` every proper power is `P^k` with odd `k >= 3`, so `d <= n/3` and
`Theta_n < 2^{n/3+1}`; Markov gives
`#{g : Theta(g) >= 2^{n-ell}/2} < 2^{ell+2-2n/3} = 2^{(4-ell)/3} < 1`, i.e. that set is
**empty**. For even `n`, `Theta_n <= 2^{n/2} + 2^{n/3+1}` while `2^{n-ell}/2 = 2^{n/2}`, so
it has **at most one** element. Off that set and off Theorem A's set at `t = 1/2`,
`N_ell(g) >= 2^{n-ell}/2 > Theta(g)`, hence `I_n(g) >= 1`; adding `floor(4 eps)` (odd) or
`floor(eps) + 1` (even) gives the counts. QED

At `t = 1/4` it gives `I_n(h) >= 2^{n-ell-1}/n` for all but `<= 16 eps + 2` top halves.

### 4. Numerical verification

`lemire_almostall.py` (exact integers on the class dumps; exit 1 on any
violation) checks total mass `2^n`; `V = sum_g D^2` against `2^{2ceil(n/2)}eps` and the
sharp `2^n eps`; Chebyshev at `t in {1/4,1/2,3/4}` and at nine data-driven thresholds; the
per-conductor moments `Sigma_j = 2^j V_j - 2^{j-1}V_{j-1}` against
`2^{j-1}(j-1)^2 2^{2ceil(n/2)}` (so `Sigma_1 = 0`); the proper-power Markov count `< 2`;
and `min_g N_ell > Theta_n`, which certifies directly that **every** class holds an
irreducible. All 15 dumps pass, 74 s; five mutation controls each make it exit 1.

```text
ell  n     E   E/2^ell  actual  minN/mean  V/SatoTate
 12 25   407  9.94e-02       0     0.8728       0.971
 14 29   583  3.56e-02       0     0.9310       0.986
 14 30   146  8.91e-03       0     0.9508       1.008
 16 33   791  1.21e-02       0     0.9597       1.004
 16 34   198  3.02e-03       0     0.9702       1.002
 18 37  1031  3.93e-03       0     0.9730       1.002
 18 38   258  9.84e-04       0     0.9797       0.999
 20 41  1303  1.24e-03       0     0.9871       1.002
 20 42   326  3.11e-04       0     0.9903       1.003
 22 45  1607  3.83e-04       0     0.9928       0.999
 22 46   402  9.58e-05       0     0.9944       0.999
 23 47  1771  2.11e-04       0     0.9945       1.000
 23 48   443  5.28e-05       0     0.9961       1.001
 24 49  1943  1.16e-04       0     0.9956       1.000
 24 50   486  2.90e-05       0     0.9971       1.000
```

`E` is Theorem B's bound, `actual` the exact count with `|N - mean| >= mean/2`. (i) The
exceptional set is **empty** at every size computed, though the theorem allows 10% of
classes at `ell = 12`; the worst class is `0.3-13%` off the mean. (ii) `V/SatoTate = 1.00`
to three digits from `ell = 16` on: Weil is lossy by exactly the expected `~ell`, and
`V/Weil` runs `0.023-0.083`. (iii) Per conductor, `Sigma_2` **saturates** the sharp Weil
bound (`1.00000` at every `(ell,n)`), `Sigma_3` sits at `0.25`, and
`rms|S|/((j-1)2^{n/2}) = 1/sqrt(j-1)` to four digits at `j = 24`: Weil is attained at the
stabilizer boundary, `sqrt(j-1)`-lossy above.

### 5. The residual: Lemire is exactly "the named class is not exceptional"

Lemire's conjecture is `I_n(1) >= 1` for the identity class `g = 1` (`h = 0`): that **one
named element** lies outside Theorem B's exceptional set. Theorems A/B cannot address it,
and not for want of constants -- (O), (W), (C) are invariant under permutations of `E_ell`.
Note 03 section 5 makes this precise: there is an explicit `F >= 0` with `F(1) = 0`,
`sum F = 2^n`, Fourier coefficients equal to `N`'s at every conductor `< a`, `|F^hat|`
*inside* Weil by `~a` above that, and second moment *below* `N`'s (`0.22, 0.15, 0.12` at
`(12,25), (16,33), (20,41)`). Any argument from mass, nonnegativity, Fourier moduli and low
moments applies verbatim to `F`, which vanishes at `1`. Sharpening `eps(ell)` -- even
proving the Sato--Tate second moment -- cannot help.

Three kinds of input can address a named class:

1. **Symmetry / transitive action**: a group acting on `E_ell`, commuting with `N_ell`,
   whose orbit of `1` meets the non-exceptional set. This is now closed as a second
   barrier ([06-symmetry-barrier.md](06-symmetry-barrier.md)): every degree-preserving
   symmetry lies in the Borel `{id, f(x) -> f(x+1)}` of `PGL_2(F_2)` together with the
   Galois/Adams action, and the induced permutation has orbit of the identity of size at
   most `2 < 4 ell^2` -- translation sends class `1` to `<(1+x)^n>_ell` (equal to `1` only
   when `(1+x)^n = 1 mod x^{ell+1}`), Adams fixes `1`. The Hecke action is transitive on
   `E_ell` but shifts the degree. No symmetry helps.
2. **Structure specific to the class**: the identity class is the short interval
   `{x^n + g : deg g <= floor(n/2)}`, the locus where all odd-power Galois-ring traces
   vanish to prescribed dyadic precisions. A lower bound reading that description
   (parity-breaking sieve, Selberg-type minorant on the Witt filtration, explicit
   construction) is not blocked by the barrier.
3. **A phase-aware inequality**: a correlation among the `S_n(chi)` at frequency `n`, not a
   bound on each modulus. `(CYL)`, `(HWO)`, `(NSD)`, `(RSD)` (note 01) are the minimal
   known forms; each needs a factor `4 ell` of *aggregate* cancellation, which no
   per-character, per-orbit or per-conductor absolute value gives.

### 6. Is the "almost all" statement in print?

The method is standard -- the function-field Barban--Davenport--Halberstam / large-sieve
second moment, unconditional because RH here is Weil's theorem. The endpoint statement
(`ell = ceil(n/2)-1`, fixed `q = 2`, explicit constants) we did not find in print; treat it
as folklore made explicit, not as new. What exists:

- **Hayes (1965)**, *Trans. AMS* **117**, 101--127, and **Hsu (1996)**, *J. Number Theory*
  **61**, 85--96 (effective): pointwise asymptotics for *every* class while
  `ell <= n/2 - log_2 ell - O(1)` -- stronger in that range, failing exactly at the last
  `log_2 ell` coefficients, which is the entire Lemire gap.
- **Keating--Rudnick (2014)**, IMRN, arXiv:1204.0708: short-interval variance
  `q^{h+1}(n-h-2)`, `0 <= h <= n-4`, as `q -> infinity` -- our range, wrong limit; source
  of the Sato--Tate column.
- **Bank--Bary-Soroker--Rosenzweig (2015)**, *Duke* **164**, 277--295 (pointwise, constant
  `c(k)`, large `q`); **Pollack (2013)**, *FFA* **22** (`~sqrt n` positions, fixed `q`);
  **Ha (2016)**, arXiv:1601.06867 (`(1/4-eps)n`, `q` large); **Gao--Kuttner--Wang (2022)**,
  *FFA* **80**, 102023 and **Gorodetsky (2020)** (exact counts, `O(1)` coefficients). None
  reaches `ell ~ n/2` at `q = 2`.
- Over `Z`, Theorem A for a *single* modulus `q ~ sqrt x` is known only under GRH
  (Montgomery--Hooley); here it is unconditional because Weil replaces GRH.
