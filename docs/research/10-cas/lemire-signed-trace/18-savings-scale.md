# Savings as a dial: the `(HWO_k)` ladder, and what the proved parts actually buy

Status: research note, 2026-08-23. Lane `lemire-signed-trace`. Nothing here proves
a new case of Kaser--Lemire. What it does is (a) replace the chain's single
threshold by an exact dictionary between a *saving factor* `F` over Weil and a
*window slack* `k`, in both the crude all-characters form and the lane's own
chain; (b) work five candidate sources of an unconditional `F > 1` to a number;
and (c) show that the answer to (b) is not merely "we did not find one" but "the
moduli-only barrier of note 03 forbids one, at every `k` below the Weil ceiling,
at 22 of the 26 endpoints checked". Checker:
`scripts/lemire-signed-trace/lemire_savings_scale.py` (exact integer / `Fraction`
arithmetic; 11 named checks; 7 mutation controls, each killing exactly one; exits
nonzero on any failure). Data: `data/savings-ladder.txt`,
`data/savings-layer-aggregates.txt`.

Companion to [01-target-and-toolkit.md](01-target-and-toolkit.md) (the chain),
[05-almost-all-theorem.md](05-almost-all-theorem.md) (Parseval + Weil),
[03-uncertainty-analogy.md](03-uncertainty-analogy.md) sec. 5 (Barrier I),
[16-large-q-threshold.md](16-large-q-threshold.md) sec. 6 (the literature table).

---

## 0. Verdict up front

1. **The dictionary.** A uniform saving of a factor `F` over the Weil bound for
   the whole non-trivial character family of `E_l` yields a monic irreducible of
   degree `n` with `deg(f - x^n) <= floor(n/2) + k`, `k = ell - l`, exactly when
   `F > F_req(n, l)` with

   ```text
   F_req(n, l) = D(l) / (2^{n/2} - 2^{l - n/2} Theta^+(n,l)),   D(l) = (l-2)2^l + 2.
   ```

   `F = 1` reproduces Hayes/Weil in its sharp published form (Gao 2021,
   arXiv:2109.14154 Thm 1(b), sharpening Hsu 1996 = Cohen 2005 Thm 2.1) --- it is
   the *same inequality*, not an analogue. `k = 0` is Kaser--Lemire and needs
   `F > (ell-2)/kappa`, `kappa = 2^{n/2 - ell}`.

2. **The roadmap's `4 ell` is a factor `4 kappa` stronger than necessary**:
   `5.714x` at `n = 2ell+1` and `8.081x` at `n = 2ell+2` when `ell = 200`
   (limits `4 sqrt 2 = 5.657` and `8`). The honest `k = 0` constants at
   `ell = 200` are **`140.007`** (odd `n`) and **`99.000`** (even `n`).

3. **No unconditional `F > 1` anywhere in B1--B5.** Quantified: the layers the
   chain already proves are a `2^{-23}` fraction of the budget at `ell = 200`
   (free gain `1 + 3.0e-8`); the small-conductor `W` term is worth `1.10x`--`1.33x`
   and no more; Cauchy--Schwarz against the *unconditional* second moment gives
   `F = (ell-2)/sqrt(ell^2-4ell+6) < 1`; the trivial bound is short by a factor
   `2^{193.4}` at `ell = 200` and the population route loses to Weil by a factor
   `>= 3` at **every** layer, structurally.

4. **The smallest `k` now proved is exactly the Hayes/Weil/Gao `k`** ---
   `k = 8` at `(ell,n) = (200,401)` and `k = 7` at `(200,402)`, asymptotically
   `k = log_2(ell) - log_2(kappa) + O(1)`. This note proves no new `k`, and says
   so plainly.

5. **But `k_Weil` is not just the current record: it is the ceiling of the whole
   method class.** The moduli-only fake population of note 03 sec. 5, optimised
   over its own split parameter, exists at level `l` iff `2^{n/2 - l} <= A*(l)`,
   and that boundary coincides with the Weil boundary at 22 of 26 sampled
   endpoints (one-step gap at the other four). Everything in B1--B5 is a
   moduli-only input, so the negative result in 3 is forced, not accidental.

---

## 1. Setting and the two closed forms that do all the work

`E_j = (1 + x F_2[x])/(x^{j+1})`, `|E_j| = 2^j`,
`<F>_j = x^{deg F} F(1/x) mod x^{j+1}`,
`N_j(g) = sum_{deg F = n, <F>_j = g} Lambda(F)`,
`S_n(chi) = sum_{deg F = n} Lambda(F) chi(<F>_j)`.
`deg(f - x^n) <= n - l - 1` is `<f>_l = 1`, so with `ell = ceil(n/2) - 1` the
half-degree window is `l = ell` and **window slack `k := ell - l` is exactly the
number of extra coefficients allowed**: `<f>_{ell-k} = 1` is
`deg(f - x^n) <= floor(n/2) + k`.

Two exact facts (checked, C1):

```text
D(m) := sum_{j=1}^{m} (j-1) 2^{j-1} = (m-2) 2^m + 2        (total L-degree of
        the non-trivial characters of E_m: 2^{j-1} of conductor j, each with
        deg L = j-1 and all inverse roots of modulus sqrt 2 by Weil)

|E_l[2]| = 2^{l - floor(l/2)}      (u^2 = 1 mod x^{l+1} iff u = 1 mod x^{floor(l/2)+1};
                                    more generally E_l[2^v] = ker(E_l -> E_{floor(l/2^v)}))
```

Write `kappa = kappa(n) = 2^{n/2 - ell}`, so `kappa = sqrt 2` at `n = 2ell+1` and
`kappa = 2` at `n = 2ell+2`.

### 1.1 The proper-power ledger, exactly

**Lemma P (odd `n`).** For odd `n` and `n/3 <= l <= ell`, the only proper prime
power of degree `n` in the identity class of `E_l` is `x^n`, so
`Theta_l(1) = 1` and `n I_n(1) = N_l(1) - 1`.

*Proof.* `F = P^r`, `r | n`, `r >= 2`, so `r` is odd; `<P>_l^r = 1` with `r`
invertible on the 2-group `E_l` gives `<P>_l = 1`, i.e. `x^m P(1/x) = 1` with
`m = n/r <= n/3 <= l`; the left side has degree `<= m <= l`, so it equals `1`
identically and `P = x^m`, irreducible only for `m = 1`. QED

**Lemma P' (even `n`).** For even `n` and `n/3 <= l <= ell`,

```text
Theta_l(1) <= Theta^+(n,l) := sum_{r | n, r even, r >= 2}
                  [ 2^{max(0, n/r - floor(l/2^{v_2(r)}))}
                    + floor(l/2^{v_2(r)}) * 2^{ceil(n/(2r))} ].
```

*Proof.* Odd `r` contributes nothing by the argument of Lemma P. For
`r = 2^v r'` with `r'` odd, `<P>_l^r = 1` iff `<P>_l in E_l[2^v] =
ker(E_l -> E_j)`, `j = floor(l/2^v)`, i.e. iff `<P>_{j} = 1`; the Lambda-mass of
degree `m = n/r` in one class of `E_j` is at most `2^{m-j} + (j-2+2^{1-j})2^{m/2}`
by orthogonality plus Weil. QED

The dominant term is `r = 2`: `2^{n/2 - floor(l/2)}`, and

```text
2^l * 2^{n/2 - floor(l/2)}  =  2^{n/2} * |E_l[2]|
```

identically --- which is **exactly** Gao's `|{eps^{1/2}}| [2 | d]` correction
(sec. 2.1). Verified against exact enumeration on 22 endpoints (C11): odd `n`
gives `Theta = 1` on the nose at every one; even `n` gives e.g. `37, 76, 45, 160,
79, 288, 301, 472, 562, 1099, 932` against the bound `186, 230, 395, 517, 909,
1108, 2149, 2402, 4625, 5388, 10259`.

---

## 2. Formulation (i): the crude all-characters dictionary

Orthogonality on `E_l` gives `2^l N_l(1) = 2^n + sum_{chi != 1} S_n(chi)`, so
`N_l(1) > 0` iff `|sum_{chi != 1} S_n(chi)| < 2^n`, and Weil bounds the left side
by `2^{n/2} D(l)`.

> **Definition (AGG_k).** For `F >= 1` and `l = ell - k`,
> ```text
> (AGG_k)     | sum_{chi != 1 in dual(E_l)} S_n(chi) |  <=  (1/F) 2^{n/2} D(l).
> ```

> **Theorem 1 (the dictionary).** Let `n/3 <= l = ell - k <= ell`. If `(AGG_k)`
> holds with
> ```text
> F  >  F_req(n,l) := D(l) / ( 2^{n/2} - 2^{l - n/2} Theta^+(n,l) )
> ```
> then there is a monic irreducible `f` of degree `n` over `F_2` with
> `deg(f - x^n) <= floor(n/2) + k`.

*Proof.* `2^l N_l(1) >= 2^n - (1/F) 2^{n/2} D(l)`. An irreducible exists in the
class as soon as `N_l(1) > Theta_l(1)`, and `Theta_l(1) <= Theta^+(n,l)` by
Lemmas P/P'. So it suffices that
`2^n - (1/F) 2^{n/2} D(l) > 2^l Theta^+(n,l)`, i.e.
`F (2^{n/2} - 2^{l-n/2} Theta^+) > D(l)`. QED

The checker tests this exactly by multiplying through by `2^{n/2}` and squaring
(both sides positive), so no floating point enters any decision.

### 2.1 Sanity check at `F = 1`: this *is* Hayes/Weil, in its sharp published form

At `F = 1` Theorem 1 reads `2^{n/2} > D(l) + 2^{l-n/2} Theta^+(n,l)`, whose main
term is

```text
2^{n/2}  >  D(l) + |E_l[2]| * [2 | n].
```

That is **verbatim** the positivity condition of

> Gao, *Improved error bounds for the number of irreducible polynomials ...*,
> arXiv:2109.14154, Theorem 1(b): for `t = 0`,
> `I_q(d; eps) >= (1/|E|) q^d/d - (D + |{eps^{1/2}}| [2|d]) q^{d/2}/(|E| d)
>  + e_1(q,d) q^{d/2}/d`, with `D = sum_{chi != 1} deg L(chi)` and
> `e_1 = min(3.4 q^{-d/6}, 0.8) >= 0`,

on taking `q = 2`, `|E| = 2^l`, `d = n`, `eps = 1`, so that `D = D(l)` and
`|{1^{1/2}}| = |E_l[2]|`. The `e_1` term is nonnegative and dropped here, so our
form is (very slightly) weaker than Gao's; it is stronger than the earlier
`(l+1)`-form

> Cohen, *Explicit theorems on generator polynomials*, FFA 11 (2005), Thm 2.1
> (= Hsu, JNT 61 (1996)): `I_q(d;eps) >= q^d/(|E| d) - (l + t + 1) q^{d/2}/d`,
> positive iff `l < n/2 - log_q(l+1)`,

which is Gao's own Corollary 2. Checked (C2) on 18 endpoints and every `l` down
to `n/3`: the two booleans agree with Gao at every point, and where the `(l+1)`
form is positive ours is too. Ours is one coefficient better at
`(ell,n) = (16,33), (20,42), (50,101)` and identical elsewhere.

### 2.2 Sanity check at `k = 0`: this *is* Kaser--Lemire

`F_req(n, ell) = D(ell)/(kappa 2^{ell} - Theta^+/kappa) = (ell-2)/kappa
(1 + O(2^{-ell/2}))`. Measured (C3, `data/savings-ladder.txt`):

| `ell` | `n` | `F_req(0)` | `(ell-2)/kappa` | `4 ell` | `4 ell / F_req(0)` |
| --- | --- | --- | --- | --- | --- |
| 200 | 401 | 140.0071 | 140.0071 | 800 | 5.714 |
| 200 | 402 | 99.0000 | 99.0000 | 800 | 8.081 |
| 512 | 1025 | 360.6245 | 360.6245 | 2048 | 5.679 |
| 512 | 1026 | 255.0000 | 255.0000 | 2048 | 8.031 |
| 1024 | 2049 | 722.6631 | 722.6631 | 4096 | 5.668 |
| 1024 | 2050 | 511.0000 | 511.0000 | 4096 | 8.016 |

The ratio tends to `4 kappa` --- `4 sqrt 2 = 5.657` (odd `n`) and `8` (even `n`).

---

## 3. Formulation (ii): the lane's chain, `k`-parameterised

Fix `k >= 0`, `l = ell - k >= n/3`, a split level `4 <= a <= l` and a cutoff
`Q = 2^t`. Put

```text
C^{(k)}   = sum_{j=a}^{l} 2^{j-1} H_j(1)  =  2^l N_l(1) - 2^{a-1} N_{a-1}(1),
W^{(k)}   = 2^{n/2} D(a-1),
B^{(k)}   = 2^n - 2^l Theta^+(n,l) - W^{(k)},
Y_j       = h_{j,t} - h_{j-1,t}      (chars of conductor exactly j, order <= Q),
Sigma_low = sum_{j=a}^{l} (j-1) Y_j,   Sigma_hi = sum_{j=a}^{l} (j-1)(2^{j-1} - Y_j),
Phi_k     = Sigma_hi / ( B^{(k)}/2^{n/2} - Sigma_low ).
```

> **(REL_k)**  `C^{(k)} > -B^{(k)}`.
>
> **(HWO_k)**  `Phi_k |T_{j,s}(n)| <= #X_{j,s} (j-1) 2^{n/2}` for every
> `a <= j <= l` and every nonempty layer with `2^s > Q`.

> **Proposition 2.** `(HWO_k) => (REL_k)`.

*Proof.* `2^{j-1} H_j(1) = sum_{chi in X_j} S_n(chi) = sum_s T_{j,s}`. Bound the
layers with `2^s <= Q` by Weil (`|T_{j,s}| <= #X_{j,s}(j-1)2^{n/2}`, and
`sum_{2^s <= Q} #X_{j,s} = Y_j`) and the layers with `2^s > Q` by `(HWO_k)`:
`|C^{(k)}| <= 2^{n/2}(Sigma_low + Sigma_hi/Phi_k) = B^{(k)}` by the definition of
`Phi_k`. QED

> **Proposition 3.** `(REL_k) =>` there is a monic irreducible `f` of degree `n`
> with `deg(f - x^n) <= floor(n/2) + k`.

*Proof.* `2^{a-1} N_{a-1}(1) = 2^n + sum_{j<a} 2^{j-1}H_j(1) >= 2^n - W^{(k)}` by
Weil. Hence `2^l N_l(1) = 2^{a-1}N_{a-1}(1) + C^{(k)} > 2^n - W^{(k)} - B^{(k)}
= 2^l Theta^+(n,l)`, so `N_l(1) > Theta_l(1)` and an irreducible remains. QED

`k = 0`, `a = ell - ceil(log_2 ell) - 1`, `Q` the roadmap's cutoff, and
`B` replaced by the weaker `2^{2ell} - W` recover the roadmap's `(REL)`/`(HWO)`
verbatim. Taking `a = 4`, `Q = 1` collapses `(HWO_k)` to `(AGG_k)` with
`F = Phi_k = F_req(n,l)(1 + O(2^{-l}))`: **the two formulations agree, and the
chain's extra constants are exactly the four listed next.**

### 3.1 Where the roadmap's factor `8.08` goes (`ell = 200`, `n = 402`)

```text
4 ell                                                            =  800.000
  |  the chain's own exact requirement is only        /1.2796      625.198
  |  B = 2^{2ell} - W  ->  B = 2^n - 2^ell Theta - W  /5.7407      108.905
  |  split level a = 191  ->  a = 4                   /1.1001       99.000
  |  2^{ceil(n/2)}  ->  2^{n/2} (Weil's actual bound) /1.0000       99.000
                                                                = F_req(0)
```

and at `n = 401`: `800 -> 625.198 -> 242.301 -> 198.000 -> 140.007`, with steps
`1.2796, 2.5802, 1.2237, 1.4142`, the last being the `sqrt 2` that the
`2^{ceil(n/2)}` convention costs at odd `n` (note 05 records the same factor in
Theorem A). The four steps multiply to `4 ell / F_req(0)` exactly; every number
is reproduced and asserted by the checker (C3, C7), and the same decomposition at
`ell = 1024` reads `4096 -> 4031.890 -> 582.721 -> 511.000 -> 511.000`
(even `n`).

---

## 4. B1--B5: hunting for an unconditional `F > 1`

### B1. The low-order layers the chain already proves: worth `1 + 3.0e-8`

The chain pays every order `2^s <= Q` by Weil, `Q` = largest power of two with
`3 Q ceil(log_2 ell) <= ell`. How much of the budget is that? Exactly (C6):

```text
Y_j = h_{j,t} - h_{j-1,t} = 0                     if Q | j,
                          = 2^{j-1-floor(j/Q)}    otherwise,
```

so the *fraction* of conductor-`j` characters of order `<= Q` is `2^{-floor(j/Q)}`
--- or zero. Measured:

| `ell` | `c` | `a` | `Q` | `Sigma_low/Sigma_all` | `F` if those layers were **free** |
| --- | --- | --- | --- | --- | --- |
| 24 | 5 | 18 | 1 | `0` (no such layer exists) | `1.000000000000` |
| 50 | 6 | 43 | 2 | `2.72e-08` | `1.000000027174` |
| 200 | 8 | 191 | 8 | `2.96e-08` | `1.000000029568` |
| 1024 | 10 | 1013 | 32 | `2.33e-10` | `1.000000000233` |

**Answer: no.** Granting the already-proved layers an *infinite* saving buys
`F = 1 + 3.0e-8` at `ell = 200`, i.e. `Delta k = 4.3e-8`. This is the cheapest
possible win and it is worth nothing, for a structural reason: a character of
`E_j` picked at random has order `>= 2^{floor(log_2 j)}` with overwhelming
probability, so "low order" is an exponentially thin slice. (At `ell <= 24` the
slice is literally empty: `Q = 1`, and the only character of order `1` is
trivial.)

### B2. The small conductors (`W`): worth `1.10x`--`1.33x`, and no more

`Phi_k(a) = (D(l) - D(a-1)) / (B/2^{n/2} - Sigma_low)` is **strictly increasing**
in `a` on the admissible range (C7; because `D(l) > B/2^{n/2}`, which is the whole
problem). So the split *costs*:

| `ell` | `n` | `Phi(a = chain)` | `Phi(a = 4)` | cost |
| --- | --- | --- | --- | --- |
| 200 | 401 | 242.301 | 198.000 | `1.224x` |
| 200 | 402 | 108.905 | 99.000 | `1.100x` |
| 1024 | 2049 | 1356.158 | 1022.000 | `1.327x` |
| 1024 | 2050 | 582.721 | 511.000 | `1.140x` |

**But `a` cannot go below `4`, and that is a theorem, not a limitation of the
data.** `E_2 = (1 + xF_2[x])/x^3 = Z/4` (generated by `1+x`), its two primitive
characters have `L(u,chi) = 1 + (1 + i^{\pm1}) u`, so the single conductor-2
layer is

```text
S_n(chi) = -alpha^n  with  alpha = -(1 + i^{+-1}),  |alpha| = sqrt 2,  so
T_{2,2}(n) = S_n(chi) + S_n(chi-bar) = -2 Re(alpha^n),
|T_{2,2}(n)| = 2^{n/2 + 1} |cos(pi n / 4)|,
```

against a Weil budget `#X (j-1) 2^{n/2} = 2 * 2^{n/2}`. Hence the layer ratio is
`|cos(pi n/4)|`: **exactly `1` when `4 | n`** (Weil saturated on the nose),
`1/sqrt 2` at odd `n`, and `0` when `n = 2 mod 4` --- and then the conductor-3
quadratic layer takes over at exactly `1/2`. Verified on all 22 computed
endpoints (C7b: the worst layer over the *whole* family is `j = 2, s = 2` at odd
`n` and at `4 | n`, and `j = 3, s = 1` at `n = 2 mod 4`, with the predicted exact
numerator every time).

**Answer: `1.10x`--`1.33x`, free (it is a restatement, not a new estimate), and
then a hard stop.** Combined with B1: `1.10 x 1.00000003 = 1.10`, i.e.
`Delta k = 0.14`. **The combined bookkeeping is not worth a factor 2**, so
`k <= log_2 n - 1` is *not* reached this way.

### B3. The measured slack: measured, not provable

Note 01 / note 05 record layer ratios far inside budget (worst high layer
`0.219 x (1/4ell)` at `(22,46)`) and `V/SatoTate = 1.00` from `ell = 16` on. Is
any of it provable?

- **Cauchy--Schwarz against the unconditional second moment: `F < 1`.**
  `sum_{chi != 1}|S_n| <= sqrt((2^l - 1) sum|S_n|^2)` and (note 05 Thm A)
  `sum_{chi != 1}|S_n|^2 <= 2^n A(l)`, `A(l) = 2^l(l^2-4l+6) - 6`, so
  `sum|S_n| <= 2^l 2^{n/2} sqrt(l^2-4l+6)` and
  `F_CS = D(l)/(2^l sqrt(l^2-4l+6)) = (l-2)/sqrt(l^2-4l+6) < 1` for every `l`.
  Cauchy--Schwarz is *marginally worse* than the triangle inequality, because
  Weil already saturates the second-moment bound it is fed.
- **Against the Sato--Tate second moment: `F = sqrt(l-2)`, which is real but
  conditional.** With `sum_{cond = j}|S_n|^2 = 2^{j-1}(j-1)2^n`
  (Keating--Rudnick) one gets `sum_{chi!=1}|S_n|^2 = 2^n D(l)` and
  `F = sqrt(D(l)/2^l) = sqrt(l-2)(1+o(1))`. At `ell = 200` that is `14.07`, and
  the dictionary turns it into `k = 4` (odd `n`) / `k = 3` (even `n`) --- **half
  the Weil `k`**. It is not a theorem at `q = 2`: Keating--Rudnick is a
  `q -> infinity` statement, and by Parseval the exact second moment *is* the
  quantity being bounded, so orthogonality cannot supply it (note 05 sec. 2).
- **Per-layer.** The exact `L`-degree is already used (`D(l)` is exact, not the
  crude `(l-1)(2^l-1)`), and note 05 measures
  `rms|S|/((j-1)2^{n/2}) = 1/sqrt(j-1)` to four digits --- i.e. the *typical*
  character is `sqrt(j-1)` inside Weil, which is precisely the Sato--Tate input
  above and precisely what Cauchy--Schwarz converts into `sqrt(l-2)`, not `l-2`.

**Answer: nothing provable.** The measured slack is real and is worth exactly the
`sqrt(l)` that a second moment can carry; converting it into the `l` that
Kaser--Lemire needs is the missing phase-aware input, which is the lane's
standing diagnosis.

### B4. Non-uniform budget: the aggregate reformulation

The true requirement is **one** inequality on the total, not `47` on the pairs.
Two things follow.

**(a) The aggregate constant is `8.08x` (even `n`) / `5.71x` (odd `n`) smaller,
and `a`, `c`, `Q`, `W`, `B` all disappear.** `(AGG_k)` with
`F > F_req(n, ell-k)` is the whole hypothesis; sec. 3.1 is its accounting. At
`ell = 200` the target drops from `4 ell = 800` to `99.0` (even) / `140.0` (odd).

**(b) In the computable range the aggregate is true with room to spare while the
per-pair form is not.** Measured on 22 endpoints (C8), with
`F_agg = 2^{n/2}D(ell)/sum_{j,s}|T_{j,s}|` over **all** `(j,s)` and `F_pair` the
worst single layer:

| `ell` | `n` | `F_req(0)` | `F_agg` | `F_pair` | aggregate ok? | per-pair ok? |
| --- | --- | --- | --- | --- | --- | --- |
| 12 | 25 | 7.072 | 78.20 | 1.414 | yes | no |
| 12 | 26 | 5.294 | 83.13 | 2.000 | yes | no |
| 16 | 33 | 9.900 | 201.98 | 1.414 | yes | no |
| 16 | 34 | 7.126 | 310.27 | 2.000 | yes | no |
| 18 | 37 | 11.314 | 564.76 | 1.414 | yes | no |
| 18 | 38 | 8.079 | 471.12 | 2.000 | yes | no |

`F_agg` grows like `2^{ell/2}` (random-model prediction) while `F_req(0)` grows
like `ell/2`; `F_pair` is pinned at `sqrt 2` or `2` **forever**, by the exact
conductor-2/3 computation of B2. So the per-pair form is not a stronger version
of the right statement, it is a statement that is false at small conductors and
has to be repaired by the `a`-split; the aggregate form needs no repair.

**(c) Does the aggregate change the target at `ell = 200`? Constant, not shape.**
It lowers `Phi_0` from `800` to `99.0`/`140.0` and it legitimises subsidy (a pair
far inside budget pays for one outside it, which the measured data say happens
massively). It does **not** change what must be proved: still a factor
`~ (ell-2)/kappa` of aggregate cancellation below Weil at fixed `q = 2`, still
one uniform estimate over the same `< 8 ell^3` sparse classes, still open.

### B5. Trivial-bound crossover: never, by a factor `2^{193}`

- **Naive.** `|S_n(chi)| <= 2^n` beats Weil `(j-1)2^{n/2}` iff `j - 1 >= 2^{n/2}`.
  At `(ell,n) = (200,402)` that needs `j >= 2^{201}` against `j <= 200`: short by
  `2^{193.4}`. At `(1024,2050)`: short by `2^{1015}`. (C9.)
- **Population.** Assemble `|T_{j,s}|` from the four-population identity
  `T = h_{j,s}P_{j,s} - h_{j,s-1}P_{j,s-1} - h_{j-1,s}P_{j-1,s} + h_{j-1,s-1}P_{j-1,s-1}`.
  Every unconditional upper bound on a population `P_{j,s} = sum_{g in 2^sE_j}N_j(g)`
  is itself a Weil bound: by orthogonality
  `P_{j,s} = (|2^sE_j|/2^j)(2^n + sum_{chi in perp, chi != 1} S_n(chi))`, and
  multiplying by `h_{j,s} = 2^j/|2^sE_j|` returns an error of exactly
  `h_{j,s}(j-1)2^{n/2}(1+o(1))`. Summing the four terms gives
  `(h_{j,s}+h_{j,s-1}+h_{j-1,s}+h_{j-1,s-1})(j-1)2^{n/2}`, against Weil's
  `#X_{j,s}(j-1)2^{n/2}` with
  `#X_{j,s} = (h_{j,s}-h_{j,s-1}) - (h_{j-1,s}-h_{j-1,s-1})`. The ratio is `> 1`
  at **every** layer, and its minimum over all `(j,s)` with `191 <= j <= 200` and
  `1013 <= j <= 1024` is exactly **`3.0000`** (C9); it reaches `9` at the top
  orders. So the population route loses to Weil by a factor between `3` and `9`,
  always.

**Answer: no crossover exists.** The reason is worth stating on its own: *at
this scale there is no such thing as a trivial bound, because the mass of any
subgroup is only known to Weil accuracy.*

---

## 5. Barrier I is the exact ceiling of everything in B1--B5

Note 03 sec. 5 builds, at level `ell` and split `a`, a nonnegative `F` with the
true low-conductor Fourier data, `F(1) = 0`, `sum F = 2^n`, and
`F^hat(chi) = -c` for every conductor `>= a`, `c = m(1)/(1 - 2^{a-1-ell})`,
`m(1) = N_{a-1}(1)/2^{ell-a+1} ~ 2^{n-ell}`. The construction is legitimate as a
moduli-only counterexample precisely while `|F^hat|` stays inside Weil, i.e.
while `c <= (a-1)2^{n/2}`. Run it at level `l` and optimise over its own split:

```text
A*(l) := max_{2 <= a <= l} (a-1)(1 - 2^{a-1-l})        (attained near a = l - log_2 l)

Barrier(l)  holds  iff  2^{n/2 - l}  <=  A*(l).
```

Compare with the Weil boundary `crit(1, n, l)` of Theorem 1. Measured over 26
endpoints (C10, `data/savings-ladder.txt`):

```text
ell=200 n=401: k_Weil = 8, first k not blocked = 8   MATCH
ell=200 n=402: k_Weil = 7, first k not blocked = 7   MATCH
...
22 of 26 endpoints MATCH; the other four -- (12,26), (24,50), (100,201), (30,61) --
leave exactly ONE value of k neither blocked nor proved.
```

> **Consequence.** For every `k < k_Weil(ell,n)` (at 22 of 26 sampled endpoints;
> at the rest, for every `k < k_Weil - 1`) there is an explicit nonnegative
> function on `E_{ell-k}` with total mass `2^n`, the true Fourier data below the
> split, all higher Fourier moduli inside Weil, second moment below the truth,
> and an **empty** identity class. So **no argument from mass, nonnegativity,
> Fourier moduli, and low moments can prove any `k` below the Weil ceiling.**

Everything in B1--B5 is such an argument: B1 and B2 are budget bookkeeping on
Weil moduli, B3 is a second moment, B4 is a rearrangement of the same absolute
values, B5 is mass plus nonnegativity. The negative result of sec. 4 is therefore
forced. It also makes the residual sharp: the *only* way onto a lower rung is a
phase-aware input, exactly as note 05 sec. 5 and note 07 say.

---

## 6. The ladder

`ell = 200`. `k` is the window slack: `deg(f - x^n) <= floor(n/2) + k`.

| `F` (saving over Weil) | `k`, `n = 401` | `k`, `n = 402` | status |
| --- | --- | --- | --- |
| `(ell-2)/sqrt(ell^2-4ell+6) = 0.99997` | 8 | 7 | **known** --- Cauchy--Schwarz vs the unconditional 2nd moment; strictly worse than `F = 1` |
| `1` | **8** | **7** | **known**: Hayes 1965; sharp form Hsu 1996 = Cohen 2005 Thm 2.1; sharpest Gao 2021 Thm 1(b). *This is the smallest `k` proved.* |
| `2` | 7 | 6 | **open** --- and blocked for moduli-only methods (sec. 5) |
| `4` | 6 | 5 | open, blocked for moduli-only |
| `8` | 5 | 4 | open, blocked for moduli-only |
| `sqrt(ell-2) = 14.07` | 4 | 3 | open; **would follow** from the fixed-`q` Keating--Rudnick variance + Cauchy--Schwarz (B3). KR is `q -> infinity`. |
| `(ell-2)/8 = 24.75` | 3 | 2 | open, blocked for moduli-only |
| `(ell-2)/4 = 49.5` | 2 | 1 | open, blocked for moduli-only |
| `(ell-2)/2 = 99.00` | 1 | 1 | at `F = 99.0000` exactly, `F > F_req(0)` just fails |
| `99.01` | 1 | **0** | **= Kaser--Lemire at even `n`**: `F > (ell-2)/2 = 99.0000` |
| `0.71(ell-2) = 140.58` | **0** | 0 | **= Kaser--Lemire at odd `n`**: `F > (ell-2)/sqrt2 = 140.0071` |
| `4 ell = 800` | 0 | 0 | the roadmap's `(HWO)`; `5.71x` / `8.08x` stronger than needed |

Doubling `F` buys exactly one step of `k` while `k > 0` (checked, C3):
`k_min(F) = ceil(log_2((ell-2)/(F kappa)))` to within one.

**Smallest `k` proved: `k_Weil`.** Explicitly, `k_Weil` is the least `k` with
`2^{n/2} > D(ell-k) + |E_{ell-k}[2]|[2|n]`; asymptotically
`k_Weil = log_2(ell) - log_2(kappa) + O(1) = log_2 n - 1 + O(1)`. Values:

| `ell` | 12 | 16 | 20 | 24 | 50 | 100 | 200 | 512 | 1024 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `k_Weil`, `n = 2ell+1` | 3 | 3 | 4 | 4 | 5 | 7 | 8 | 9 | 10 |
| `k_Weil`, `n = 2ell+2` | 3 | 3 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |

This is the same `k` Hayes gave in 1965. **This note adds no rung.**

---

## 7. The literature ceiling, re-verified

Checked afresh 2026-08-23 (arXiv API sweep of `"prescribed coefficients" AND
irreducible`, newest 2023; primary reads of arXiv:2109.14154, arXiv:2109.02000,
arXiv:1911.05295; note 16 sec. 6 for the rest):

| source | prescribes | fixed `q = 2`? | reaches `k = O(1)`? |
| --- | --- | --- | --- |
| Hayes 1965 / Weil; Hsu 1996; Cohen 2005 Thm 2.1; **Gao 2021 Thm 1(b)** | top `l` coefficients | yes | no: `k = log_2 n + O(1)`, and Gao's is the sharpest form of exactly our `F = 1` |
| Gao--Kuttner--Wang, arXiv:2109.02000 | exact formulae, `O(1)` coefficients | yes | no --- fixed number of coefficients |
| Zhang--Han, arXiv:1911.05295 Thm 1.5 | AP `mod k(x)`, error `O(n^alpha) + O(q^{n/Omega(n)}/n)` | yes | **no**: `alpha = alpha(k(x))` depends on the modulus, which here grows with `n`; the statement is a fixed-modulus one and is vacuous at `k(x) = x^{ceil(n/2)}` |
| Pollack 2013 Prop. 10 | `(1/2 - eps) n` top+bottom | yes | no --- `eps` is Hayes+Weil's `log_q n` deficiency in disguise (note 16 sec. 6) |
| Pollack 2013 main thm | `(1-eps) sqrt n`, arbitrary positions | yes | no --- too few coefficients |
| Ha 2016 | `(1/4-eps)n` arbitrary positions | only `n/10` at fixed `q` | no --- `n/10 < n/2 - log_2 n` for every `n >= 8` |
| Sawin--Shusterman 2022; Sawin, Acta; Sawin--Shusterman 2025 | level of distribution | **no** (large `q`, squarefree modulus) | n/a |
| Bagshaw, arXiv:2401.10399 Cor. 2.5 | arbitrary modulus incl. `T^r` | **no** (`p` odd, `p^{l-2} > 7101`) | yes, but not at `q = 2` (note 16) |
| Gorodetsky 2020 | fixed `q`, short intervals | yes | no --- needs `k >> n loglog n / log n`, far worse than `log_2 n` |

**Verdict: at fixed `q = 2` and `l ~ n/2` prescribed *top* coefficients, nothing
in print beats `F = 1`.** Every rung of sec. 6 strictly between `F = 1` and
`F = (ell-2)/kappa` is an open theorem that nobody has, and each is additionally
blocked for the moduli-only class by sec. 5.

---

## 8. What this note changes in the chain

Nothing that is proved becomes unproved, and nothing open becomes closed. Three
statements are worth carrying into the roadmap:

1. **`(HWO)`'s constant `4 ell` can be replaced by `(ell-2)/kappa`** ---
   `140.007` at `(200,401)`, `99.000` at `(200,402)` --- provided one states the
   estimate in the aggregate form `(AGG_0)`, uses Weil's actual `2^{n/2}` rather
   than `2^{ceil(n/2)}`, and replaces the sufficient target `N_ell(1) > 2^{n-ell}
   - 2^ell` by the true one `N_ell(1) > Theta_ell(1)` with `Theta_ell(1) = 1`
   (odd `n`, Lemma P) or `<= 2^{n/2 - floor(ell/2)} + ...` (even `n`, Lemma P'
   = Gao's `|{eps^{1/2}}|` term).
2. **The estimate is a dial, and its calibration is `k = log_2((ell-2)/(F kappa))`.**
   Stating it as a threshold hides that a factor `2` of cancellation is already a
   theorem nobody has.
3. **The per-pair form cannot have `a < 4`**, because the conductor-2 layer
   satisfies `|T_{2,2}(n)| = 2^{n/2+1}|cos(pi n/4)|` and saturates Weil exactly
   whenever `4 | n`. This is a proof, not a measurement, and it is the reason the
   chain needs `W` at all.

---

## 9. Reproducibility

```sh
PY=/data0/axeyum/scratch/lemire-signed-trace-lemire-venv/bin/python
cd scripts/lemire-signed-trace
$PY lemire_savings_scale.py                 # 11 checks, ~1 s, exits nonzero on failure
$PY lemire_savings_scale.py --controls      # 7 mutation controls, each kills exactly one check
$PY lemire_savings_scale.py --regenerate --scratch <dir>   # rebuild data from exact dumps
```

`--regenerate` calls
`<snapshot>/target/release/axeyum-gf2-dump-populations <ell> <degree> 1300000000`
(the third argument is **required**; without it the binary panics and leaves a
zero-byte dump) for `8 <= ell <= 18` at both endpoints, and recomputes
`N_j(1)` for every `j`, `sum_{j,s}|T_{j,s}|` over **all** layers, the worst layer,
and the exact `Theta_ell(1)` by flint enumeration. Snapshot path overridable with
`AXEYUM_LEMIRE_SNAPSHOT`.

Controls, each verified to kill exactly one named check:

| control | mutation | kills |
| --- | --- | --- |
| M1 | off-by-one in the low-order character count `Y_{j,t}` | C6 |
| M2 | drop Gao's even-`n` two-torsion correction | C2 |
| M3 | let the `W` term be free instead of eating the budget | C7 |
| M4 | flip the moduli-only barrier inequality | C10 |
| M5 | bound the total by the worst single layer instead of summing | C8 |
| M6 | drop `kappa = 2^{n/2-ell}` from the `k = 0` requirement | C3 |
| M7 | price the population route at `#X` instead of the four `h`'s | C9 |

Anchors reproduced en route: `N_5(1) = 45`, `C_{5,11} = -608`, `B_{5,11} = 1024`;
`N_7(1) = 472`, `C_{7,16} = -4608`, `B_{7,16} = 15872` (note 01 sec. 3).

**Not established here.** (i) Any `F > 1`. (ii) The `sqrt(l-2)` rung, which needs
the Keating--Rudnick variance at fixed `q`. (iii) Whether the four one-step gaps
in sec. 5 are real or an artefact of the particular fake population --- a
different moduli-only construction might close them. (iv) The exact `Theta` for
`ell >= 19`, where the flint enumeration exceeds degree 19.
