# Conductor-graded Fourier analysis on principal-unit groups of `F_2[x]`
# -- with applications to irreducible polynomials in half-degree ray classes

Standalone research artifact of the AC-Bridge project
(`docs/research/10-cas/ac-bridge-2026-08/`), phase 3.
Assembled 2026-08-20.  Working diary: `23-artifact.md`.

**Status of this document.**  Every statement labelled **Theorem**, **Lemma**,
**Proposition** or **Corollary** below carries a complete proof written out in
this file, re-derived from scratch by the author of this artifact rather than
copied from the phase-1/2 diaries.  The one exception is Theorem 2.36, which is
proved here at `m = 3` and carries an explicit, exhibited GAP at `m >= 4`; it is
kept in the corpus because the `m = 3` statement is a genuine characteristic-free
improvement of a published lemma, and it is labelled accordingly wherever it
appears.  Statements labelled **(EVIDENCE)** are
finite computations, always with the exact program and parameters that produced
them.  Statements labelled **(CONJECTURE)** are open.  Three analytic facts are
**imported** from outside this artifact and are isolated in section 1.5; every
result that depends on one says so in its hypothesis line.

**Adversarial verification.**  A parallel phase-3 workstream
(`20-verify-chains.md`) independently re-derived the load-bearing chains and
audited every lemma in this corpus, with an explicit CONFIRMED / GAP / FALSE
verdict per claim.  This artifact has been reconciled against it.  Twenty of its
twenty-nine entries are CONFIRMED, including **both** load-bearing chains end to
end with every constant; the GAPs and FALSEs it found are incorporated here --
Theorem 2.36 is downgraded to `m = 3`, the (SUP-L) evidence is restated in
section 6.3 and table (E-1b), the (TWIST) identity is corrected, and Lemma 2.31
carries the corrected proof.  Where this artifact and the verifier reached the
same correction independently, that is said.

**What this artifact does not claim.**  It does not prove the Lemire endpoint
conjecture, and it does not prove either of the two open statements (SUP-L) and
(CDL) of section 3.  It proves that (SUP-L) with an absolute constant `K = 2`
implies the endpoint for all `ell >= 22` (odd) / `ell >= 20` (even), and that
(CDL) implies it through an exact multiplicative identity.

---

## Contents

```text
1  Setting and notation
   1.1  The group G_ell and its Witt decomposition
   1.2  The conductor filtration
   1.3  Hayes characters, the class populations, the endpoint discrepancy
   1.4  Normalizations and the four moment quantities
   1.5  Imported inputs (I1), (I2), (I3)
   1.6  Provenance table: this artifact's numbering vs the diaries
2  The proved corpus
   2.1  Endpoint sufficiency: the proper-prime-power mass and (W4-exact)
   2.2  The conductor grading: orthogonality, parity, layer energies, recursion
   2.3  The reduction chain, and the theorem "(SUP-L) with K = 2 => endpoint"
   2.4  The multiplicative dichotomy: R_0 = prod (1 + q_j)
   2.5  The convolution-order grading and its Wick total
   2.6  The dyadic autocorrelation fibre family
   2.7  Two blindness lemmas: weight-blindness and the singular-locus bound
3  The two open statements
   3.1  (SUP-L) and its evidence
   3.2  (CDL) and its evidence
4  Related work
5  Appendix: export targets for kernel admission and Lean verification
6  Honesty: what is open, the square-root barrier, and what is new
```

---

## 1  Setting and notation

Everything happens over `F_2`.  `A = F_2[x]`; `A_m` is the set of monic
polynomials of degree `m`, `|A_m| = 2^m`.  `mob` is the Moebius function of `A`
(written `mob`, not `mu`, because `mu` is reserved throughout for the class mean
`2^(n-ell)`), and `Lambda` is the von Mangoldt function
(`Lambda(P^k) = deg P` for `P` irreducible and `k >= 1`, zero otherwise).
Two standard exact facts are used freely:

```text
  sum_(F in A_m) Lambda(F)  =  2^m                       for every m >= 1,      (PNT)
  sum_(F in A_m) mob(F)     =  0                         for every m >= 2.      (MU)
```

Both are the coefficient identities of `1/zeta_A(z) = 1 - 2z` and
`z (d/dz) log zeta_A(z) = 2z/(1-2z)`, with `zeta_A(z) = 1/(1-2z)`.

### 1.1  The group `G_ell` and its Witt decomposition

Fix `ell >= 1` and put

```text
  G_ell  :=  ( F_2[t] / t^(ell+1) )^*  =  { 1 + a_1 t + ... + a_ell t^ell } ,
  |G_ell| = 2^ell .
```

(Every unit of `F_2[t]/t^(ell+1)` has constant term `1`, so the unit group is
already the principal-unit group.)  For a monic `F = x^D + a_1 x^(D-1) + ... +
a_D` define the **reciprocal truncation**

```text
  <F>  :=  ( 1 + a_1 t + a_2 t^2 + ... + a_D t^D )  mod t^(ell+1)   in G_ell .
```

Writing `F^*(t) = t^D F(1/t)` for the reciprocal, `<F> = F^* mod t^(ell+1)`, and
`(FG)^* = F^* G^*`, so

```text
  <FG> = <F> <G>                                                     (MULT)
```

for all monic `F, G`.  For `deg F <= ell` the class `<F>` records *every*
non-leading coefficient of `F`, so `F -> <F>` is a bijection from `A_d` onto

```text
  V_d  :=  { 1 + a_1 t + ... + a_d t^d }  subset  G_ell        (d <= ell),
```

and `<F> = 1` says exactly that the top `ell` non-leading coefficients of `F`
vanish -- the **Lemire shape**.

**Witt decomposition.**  `G_ell` is generated by the elements `1 + t^i` with `i`
odd, `1 <= i <= ell`, and `(1 + t^i)^(2^m) = 1 + t^(i 2^m)`, so the order of
`1 + t^i` is `2^(k_i)` with `k_i = min{ m : i 2^m > ell }`.  These generate
independently and

```text
  G_ell  ~  prod_(i odd, i <= ell)  Z / 2^(k_i) ,     sum_i k_i = ell .
```

This product decomposition is the Efron--Stein grading of `G_ell`; it is used in
this artifact only in section 2.7 and in the related-work discussion, and is
**not** the grading the main results use.

### 1.2  The conductor filtration

For `0 <= j <= ell` put

```text
  H_j  :=  { u in G_ell : u = 1 mod t^(j+1) } ,      |H_j| = 2^(ell-j) ,
```

so `H_0 = G_ell` and `H_ell = {1}`, and `G_ell / H_j ~ G_j` by truncation.  A
character `chi` of `G_ell` has **conductor level** `j`, written `lev(chi) = j`,
if `chi` is trivial on `H_j` and nontrivial on `H_(j-1)`; `lev(chi) = 0` means
`chi = 1`.  Since the characters trivial on `H_j` are exactly the characters of
`G_ell/H_j`, of which there are `2^j`,

```text
  #{ chi : lev(chi) = j }  =  2^j - 2^(j-1)  =  2^(j-1)     for 1 <= j <= ell.  (CT)
```

Because `|H_(j-1)/H_j| = 2`, a character of level exactly `j` restricts on
`H_(j-1)` to **the** unique nontrivial character `eps_J` of `H_(J-1)/H_J`
(`J = j`); this two-line observation is the entire content of the parity rule of
Theorem 2.10.

The **conductor projections** are

```text
  (P_j D)(e)  :=  2^(-(ell-j))  sum_(h in H_j)  D(e h) ,
  D_[j]       :=  P_j D  -  P_(j-1) D          (1 <= j <= ell),
```

for any `D : G_ell -> R`.  `P_j` is convolution with the normalized indicator of
`H_j`; since `(1_(H_j)/|H_j|)^(chi) = 1[chi|_(H_j) = 1]`, the projection `P_j`
kills every Fourier mode of level `> j` and fixes the rest, so `D_[j]` has
Fourier support **exactly** the level-`j` characters.  Everything in section 2.2
is a consequence of that one sentence.

`D_[j]` is computed exactly, in integers, by the **sibling recursion**

```text
  R_ell = D ,     R_(j-1)(e) = R_j(e) + R_j(e g_j) ,     g_j = 1 + t^j ,
  A_j(e) = R_j(e) - R_j(e g_j) ,                D_[j] = A_j / 2^(ell-j+1) ,
```

which is the form the machine code uses.  (`R_j` is `2^(ell-j)` times the
level-`j` coarse average; `A_j` is the level-`j` sibling difference.)

### 1.3  Hayes characters, class populations, the endpoint discrepancy

Fix an **endpoint degree**

```text
  n = 2 ell + 1   (odd endpoint)      or      n = 2 ell + 2   (even endpoint),
```

so that `ell = ceil(n/2) - 1`: the class prescribes about half the coefficients.
Put

```text
  N_n(e)  :=  sum_( F in A_n, <F> = e )  Lambda(F) ,
  mu      :=  2^(n - ell) ,          D_e := N_n(e) - mu .
```

By (PNT) and `|G_ell| = 2^ell`, `sum_e N_n(e) = 2^n = 2^ell * mu`, hence

```text
  sum_e D_e = 0 .                                                     (ZERO)
```

The characters `chi` of `G_ell`, pulled back along `F -> <F>`, are the **Hayes
characters** of this problem (Dirichlet characters ramified only at infinity,
in the "short interval" normalization).  Their sums are

```text
  S_chi  :=  sum_e D_e chi(e)  =  sum_(F in A_n) Lambda(F) chi(<F>)   (chi != 1),
  S_1    =  0    by (ZERO).
```

The middle equality holds because `sum_e mu * chi(e) = 0` for `chi != 1`.
Fourier inversion on `G_ell` reads `D_e = 2^(-ell) sum_chi S_chi conj(chi(e))`,
and Plancherel reads `sum_e D_e^2 = 2^(-ell) sum_chi |S_chi|^2`.

By (MULT), `L(chi, z) := sum_(F monic) chi(<F>) z^(deg F) = prod_P (1 - chi(<P>)
z^(deg P))^(-1)` and `S_chi = [z^n] ( z (d/dz) log L(chi,z) )`.

### 1.4  Normalizations and the four moment quantities

```text
  M_r   :=  sum_e |D_e|^r                     (r = 2, 4 are used)
  Sigma(ell)  :=  sum_(j=2)^ell 2^(j-1) (j-1)^2
  R_0   :=  2^ell M_4 / M_2^2                 (the kurtosis of the class populations)
  K_4   :=  2^ell M_4  -  3 M_2^2             (the connected fourth cumulant numerator)
  Pi_n  :=  sum_(k>=2)  sum_( P irred, k deg P = n, <P>^k = 1 )  deg P
  I_n(1):=  # { P irreducible, deg P = n, <P> = 1 }
```

`Pi_n` is the **exact** proper-prime-power von Mangoldt mass of the identity
class.  By the definition of `Lambda`,

```text
  N_n(1)  =  Pi_n  +  n I_n(1) .                                      (DAG)
```

The Lemire endpoint conjecture is the assertion `I_n(1) >= 1` for all large `n`:
a degree-`n` irreducible polynomial over `F_2` whose top `ceil(n/2) - 1`
non-leading coefficients all vanish.

**Proposition 1.1 (closed form for `Sigma`).  PROVED.**
`Sigma(ell) = 2^ell (ell^2 - 4 ell + 6) - 6` for every `ell >= 1`.

*Proof.*  Substituting `i = j-1`, `Sigma(ell) = sum_(i=1)^(ell-1) i^2 2^i`.  The
standard evaluation `sum_(i=0)^m i^2 2^i = 2^(m+1)(m^2 - 2m + 3) - 6` follows by
induction: at `m = 0` both sides are `0`, and
`2^(m+2)((m+1)^2 - 2(m+1) + 3) - 2^(m+1)(m^2-2m+3) = 2^(m+1)(2(m^2+2)-(m^2-2m+3))
= 2^(m+1)(m^2+2m+1) = (m+1)^2 2^(m+1)`.  At `m = ell-1`,
`2^ell((ell-1)^2 - 2(ell-1) + 3) - 6 = 2^ell(ell^2 - 4 ell + 6) - 6`.  QED
*(Checked by exact integer comparison for `1 <= ell <= 400`; see 23-artifact.md,
`cross2.py`.)*

### 1.5  Imported inputs

Three facts are used but **not** proved here.  Every dependent statement names
them explicitly.

> **(I1) Riemann hypothesis for function-field Dirichlet `L`-functions (Weil).**
> For `chi` a nontrivial Hayes character of conductor level `j`, `L(chi, z)` is a
> polynomial in `z` of degree at most `j - 1` whose inverse roots all have
> absolute value at most `2^(1/2)`.  Consequently
> ```text
>       |S_chi|  <=  (j - 1) 2^(n/2) .
> ```
> In particular `S_chi = 0` when `j = 1` (degree-`0` `L`-polynomial).

> **(I1') Purity at level 2.**  For `chi` of level exactly `2`, `L(chi,z)` has
> degree exactly `1` and its inverse root has absolute value exactly `2^(1/2)`,
> so `|S_chi| = 2^(n/2)` exactly.  Used *only* for the exact value of `V_2` in
> Theorem 2.11(b); no downstream result depends on it.

> **(I2) Exact conductor-level `L`-degree distribution.**  A Hayes character of
> exact level `j` over `F_2` is even and primitive of conductor `x^(j+1)`, hence
> has `L`-degree exactly `j - 1`; combined with (CT) there are exactly `2^(j-1)`
> characters of `L`-degree `j-1`.  In-tree witness:
> `axeyum_cas::gf2_hayes::binary_hayes_l_degree_distribution`.

> **(I3) Truncated Artin--Schreier kernel dimension (used only in section 2.6).**
> `dim_(F_2) ker( z -> z^2 + h z  mod x^W )` on positive-valuation classes, for
> `v = v(h)`, is `v + 1` when `2v < W` and `floor(W/2)` when `2v >= W`.
> A self-contained derivation is given in the proof of Theorem 2.24, so (I3) is
> in fact re-derived here; it is listed for traceability only.

**Interpretation.**  (I1) is the only genuinely analytic input, and it is the
standard one.  The finite-`ell` corroboration quoted below for
`M_2 <= mu Sigma(ell)` and for `V_2` was produced by
`crates/axeyum-cas/examples/acb_cab_levels.rs` against the independent CAS
routine `exact_conductor_second_moment`.

**Corollary 1.2 (Weil envelope).  PROVED given (I1), (I2).**

```text
  M_2  <=  mu * Sigma(ell) .
```

*Proof.*  By Plancherel and `S_1 = 0`, `M_2 = 2^(-ell) sum_(j=1)^ell
sum_(lev(chi) = j) |S_chi|^2`.  Level `1` contributes `0` by (I1).  Level `j >= 2`
contributes at most `2^(j-1) * ((j-1) 2^(n/2))^2 = 2^(j-1)(j-1)^2 2^n` by (I1)
and (CT).  Summing, `M_2 <= 2^(n-ell) Sigma(ell) = mu Sigma(ell)`.  QED

### 1.6  Provenance table

| here | phase-1/2 diary | diary's name |
|---|---|---|
| Proposition 1.1 | 04 | closed form of `Sigma(ell)` |
| Corollary 1.2 | 04 (from the lane) | the proved Weil envelope `M_2 <= mu Sigma` |
| Lemma 2.1 | 04 | Lemma A |
| Lemma 2.2 | 04 | Lemma B |
| Lemma 2.3 | 04 | Lemma C |
| Theorem 2.4 | 04 | Theorem (T-weak) / (W4-exact) |
| Corollary 2.5, 2.6 | 04 | Corollaries (WR), (WK) |
| Theorem 2.7 | 11 | Lemma 4, first half (orthogonality) |
| Proposition 2.8 | 05 | (WICK), here stated grading-free |
| Proposition 2.9 | 11 | Lemma 4, second half (`sum mult \|P\| = 3 M_2^2`) |
| Theorem 2.10 | 11 | Lemma 5 (parity selection rule) |
| Theorem 2.11 | 11 | Lemma 6 (Weil control of layers) |
| Theorem 2.12 | 11 | Lemma 7 (the exact `1/4` recursion) |
| Propositions 2.13-2.15 | 11 | (ENV-L), (L4-LAYER), the `L^4` step |
| Theorem 2.16 | 11 | the (SUP-L) chain and its crossovers |
| Proposition 2.17 | 11 | (SPLIT-L) |
| Proposition 2.18 | 13 | the `C_j` Parseval identity |
| Theorem 2.19 | 13 | Lemmas D1 and D2 (`R_0 = prod (1+q_j)`) |
| Theorem 2.20 | 13 | Theorem D3 (the dichotomy) |
| Corollary 2.21 | 13 | Corollary D4, (INC-CYL) |
| Proposition 2.22 | 13 | Lemma D5 |
| Theorem 2.23 | 13 | Result C4 (`E_1 = 0` at odd endpoints) |
| Lemmas 2.24-2.26 | 11 | Lemmas 1, 2, 3 (order grading) |
| Lemma 2.27 | 14 | Lemma D1 |
| Corollary 2.28 | 14 | Corollary D1a |
| Theorem 2.29 | 14 | Theorem D2 |
| Lemma 2.30 | 14 | Lemma D3 |
| Lemma 2.31 | 14 | Lemma D4 |
| Corollary 2.32 | 14 | the corollary to D3/D4 |
| Proposition 2.33 | 14 | Theorem D6 (the completion identity) |
| Model 2.34 | 14 | (R1a), the Euler-product diagonal |
| Lemma 2.35 | 02 | Lemma W  -- **renamed Lemma WB** here |
| Theorem 2.36 | 12 | Lemma W  -- **renamed Lemma SL** here |
| Proposition 3.1 | -- | **new in this artifact** |
| (SUP-L) | 11 | (SUP-L) |
| (CDL) | 13 | (CDL) |

The two diaries independently used the name "Lemma W" for unrelated statements,
and diaries 13 and 14 independently used `D1 ... D5`.  All collisions are
resolved by the numbering above.

---

## 2  The proved corpus

### 2.1  Endpoint sufficiency: the proper-prime-power mass

The point of this subsection is that a *fourth-moment* bound on the class
discrepancy implies the existence of an irreducible in the identity class, with
every constant explicit -- and that the constant is **not** `mu^4`.

**Lemma 2.1 (odd endpoint proper-power mass).  PROVED, unconditional.**
For `n = 2 ell + 1` and every `ell >= 1`, `Pi_n = 1`, the only contribution
being `F = x^n`.

*Proof.*  Let `F = P^k` with `P` irreducible, `k >= 2`, `deg F = n`, `<F> = 1`.
Put `d = deg P`, so `k d = n`.  `n` is odd, hence `k` is odd, hence `k >= 3` and
`d = n/k <= n/3 = (2 ell + 1)/3 <= ell` (the last step is `2 ell + 1 <= 3 ell`,
i.e. `ell >= 1`).

By (MULT), `<F> = <P>^k`.  `G_ell` is a group of order `2^ell` and `k` is odd,
so `gcd(k, |G_ell|) = 1` and `g -> g^k` is an automorphism of `G_ell`;
therefore `<P>^k = 1` forces `<P> = 1`.  Since `d <= ell`, the class `<P>`
records every non-leading coefficient of `P`, so `<P> = 1` forces `P = x^d`.
`x^d` is irreducible only for `d = 1`, which forces `k = n` and `F = x^n`.
Finally `<x^n> = 1` indeed and `Lambda(x^n) = deg x = 1`.  Hence `Pi_n = 1`. QED

**Lemma 2.2 (even endpoint proper-power mass).  PROVED, unconditional.**
For `n = 2 ell + 2` and every `ell >= 2`,

```text
  Pi_n  <=  P_n^sharp  :=  (ell + 1) 2^ceil(ell/2)  +  n 2^ceil((ell+1)/2) ,
```

and `P_n^sharp < mu = 2^(ell+2)` for every `ell >= 7`.

*Proof.*  Classify the contributions `F = P^k`, `k d = n`, `d = deg P`, by `k`.

*(i) `k` odd, `k >= 3`.*  `n` is even and `k` odd, so `d = n/k` is even.  Also
`d <= n/3 = (2ell+2)/3 <= ell` for `ell >= 2`.  Exactly as in Lemma 2.1,
`<P>^k = 1` with `k` odd forces `<P> = 1`, and `d <= ell` then forces `P = x^d`
with `d` even and `d >= 2`, which is not irreducible.  **This layer is empty.**

*(ii) `k = 2`, `d = ell + 1`.*  An irreducible `P` of degree `ell + 1 >= 3` is
not `x`, so `P(0) = 1`.  Two such `P` with the same class `<P>` agree in
`a_1, ..., a_ell` and both have `a_(ell+1) = P(0) = 1`, hence are equal: the map
`P -> <P>` is **injective** on this layer.  The constraint `<P>^2 = 1` says
`<P> in G_ell[2]`.  Since `G_ell ~ prod_(i odd <= ell) Z/2^(k_i)`, the
`2`-torsion subgroup has order `2^(#{i odd, i <= ell})= 2^ceil(ell/2)`.  Each
member carries Mangoldt weight `deg P = ell + 1`, so this layer contributes at
most `(ell + 1) 2^ceil(ell/2)`.

*(iii) `k` even, `k >= 4`.*  Then `d = n/k <= n/4 = (ell+1)/2`.  From
`sum_(e | d) e I_e = 2^d` (where `I_e` is the number of monic irreducibles of
degree `e`) we get `d I_d <= 2^d`, so the layer for a fixed such `k` contributes
at most `d I_d <= 2^d <= 2^ceil((ell+1)/2)`.  There are fewer than `n` values of
`k`, so all these layers together contribute at most `n 2^ceil((ell+1)/2)`.

Adding (i)-(iii) gives the bound.  For the numerical claim, since
`ceil(ell/2) <= ceil((ell+1)/2) <= (ell+2)/2`,

```text
  P_n^sharp  <=  3 (ell+1) 2^ceil((ell+1)/2)  <=  3 (ell+1) 2^((ell+2)/2) ,
```

so `P_n^sharp < 2^(ell+2)` as soon as `3(ell+1) < 2^((ell+2)/2)`.  At `ell = 8`
this reads `27 < 32`; and the right side grows by the factor `2^(1/2) = 1.414`
per unit `ell` while the left side grows by `(ell+2)/(ell+1) <= 10/9 < 1.414`,
so it holds for every `ell >= 8`.  At `ell = 7` the bound is checked directly:
`P_n^sharp = 8 * 2^4 + 16 * 2^4 = 384 < 512 = 2^9`.  QED

**Lemma 2.3 (Chebyshev at one point).  PROVED.**
`|D_1|^4 <= sum_e |D_e|^4 = M_4`; hence `M_4 < X^4` implies `|D_1| < X`.

*Proof.*  One term of a sum of nonnegative terms.  QED

**Theorem 2.4 (fourth-moment sufficiency).  PROVED, unconditional.**
If

```text
  M_4  <  ( mu - Pi_n )^4                                          (W4-exact)
```

then `I_n(1) >= 1`: there is an irreducible polynomial of degree `n` over `F_2`
whose top `ell` non-leading coefficients all vanish.

*Proof.*  Lemma 2.3 gives `|D_1| < mu - Pi_n`, so
`N_n(1) = mu + D_1 > mu - (mu - Pi_n) = Pi_n`.  By (DAG),
`n I_n(1) = N_n(1) - Pi_n > 0`, and `n > 0`.  QED

**Corollary 2.5 (usable at symbolic `ell`).  PROVED (unconditional).**
`(W4-exact)` follows from `M_4 < (mu - P_n)^4` for any valid upper bound
`P_n >= Pi_n`, in particular for

```text
  P_n = 1            (odd endpoint,  Lemma 2.1, exact),
  P_n = P_n^sharp    (even endpoint, Lemma 2.2, valid for ell >= 2; < mu for ell >= 7).
```

The explicit thresholds are `mu - P_n = 2^(ell+1) - 1` (odd) and
`mu - P_n = 2^(ell+2)(1 - theta_ell)` with `theta_ell <= 3(ell+1) 2^(-ell/2-1)`
(even).

**Corollary 2.6 (the connected form).  PROVED given (I1), (I2).**
With `Sigma(ell)` as in Proposition 1.1,

```text
  K_4  <  2^ell (mu - P_n)^4  -  3 ( mu Sigma(ell) )^2                    (WK)
```

implies `(W4-exact)`, hence `I_n(1) >= 1`.  The right-hand side is positive
exactly from `ell = 14` (odd endpoint, `P_n = 1`) and `ell = 13` (even endpoint,
`P_n = P_n^sharp`), and is then of size `~ 2^(5 ell + 4)`.

*Proof.*  By definition `2^ell M_4 = 3 M_2^2 + K_4`.  Corollary 1.2 gives
`M_2 <= mu Sigma(ell)`, so `3 M_2^2 <= 3 (mu Sigma)^2`, and (WK) yields
`2^ell M_4 < 3(mu Sigma)^2 + 2^ell(mu - P_n)^4 - 3(mu Sigma)^2 = 2^ell (mu-P_n)^4`.
Divide by `2^ell` and apply Corollary 2.5 and Theorem 2.4.  QED

> **Correction recorded.**  Diary 04 stated (WK) with a non-strict `<=`.  With
> `<=` the chain terminates in `M_4 <= (mu - P_n)^4`, which is *not* enough for
> Theorem 2.4 (equality would leave `N_n(1) >= Pi_n`, i.e. `I_n(1) >= 0`).  The
> statement above is the corrected, strict form.  The correction is cosmetic --
> for integers one may instead use the sharper `M_4 <= (mu - Pi_n - n)^4`, since
> `N_n(1)` lies in `Pi_n + n Z` -- but it must be made somewhere.

**Remark 2.6a (why the positivity-only form is insufficient).**  The weaker
hypothesis `M_4 < mu^4` gives only `N_n(1) > 0`, and `N_n(1) = 1` -- realized by
the single ramified unit `x^n` -- is consistent with `I_n(1) = 0`.  At the even
endpoint the obstruction is the `2`-torsion layer of Lemma 2.2(ii), of size
`2^ceil(ell/2)`, not a single point.  The correct constant is `1 - 2^(-(ell+1))`
(odd) and `1 - O(ell 2^(-ell/2))` (even) times `mu`.

### 2.2  The conductor grading

Throughout this subsection `D : G_ell -> Z` is any function with `sum_e D_e = 0`
(so `P_0 D = 0`), and `D_[j]` are its conductor components (section 1.2).  Since
`P_ell D = D` and `P_0 D = 0`,

```text
  D  =  sum_(j=1)^ell  D_[j]                                          (GRADE)
```

exactly.  Set `V_j := sum_e D_[j](e)^2 >= 0`.

**Theorem 2.7 (orthogonality of the conductor grading).  PROVED.**
For `j != k`, `sum_e D_[j](e) D_[k](e) = 0`.  Consequently
`sum_(j=1)^ell V_j = M_2`.

*Proof.*  `P_j` is convolution by `1_(H_j)/|H_j|`, whose Fourier transform at
`chi` is `(1/|H_j|) sum_(h in H_j) chi(h)`, equal to `1` if `chi` is trivial on
`H_j` and `0` otherwise (a nontrivial character of `H_j` sums to zero over
`H_j`).  By the convolution theorem, `(P_j D)^(chi) = S_chi * 1[lev(chi) <= j]`,
so `(D_[j])^(chi) = S_chi * 1[lev(chi) = j]`.  The Fourier supports of `D_[j]`
and `D_[k]` are therefore disjoint for `j != k`, and Plancherel gives
`sum_e D_[j] D_[k] = 2^(-ell) sum_chi (D_[j])^(chi) conj((D_[k])^(chi)) = 0`.
Summing `(GRADE)` squared against itself and using orthogonality gives
`M_2 = sum_j V_j`.  QED

Now fix a grading `D = sum_(a in I) T_a` by a finite index set `I` -- the
conductor grading `T_j = D_[j]` (`I = {1..ell}`) and the convolution-order
grading of section 2.5 are the two instances used here.  Put

```text
  C_(a,b)      :=  sum_e T_a(e) T_b(e) ,
  P_(a,b,c,d)  :=  C_(a,b) C_(c,d) + C_(a,c) C_(b,d) + C_(a,d) C_(b,c) ,
  K_(a,b,c,d)  :=  2^ell sum_e T_a T_b T_c T_d  -  P_(a,b,c,d) .
```

**Proposition 2.8 (the Wick total is grading-free).  PROVED.**
For any grading of `D`,

```text
  sum_( (a,b,c,d) in I^4 )  P_(a,b,c,d)  =  3 M_2^2 ,
  sum_( (a,b,c,d) in I^4 )  K_(a,b,c,d)  =  2^ell M_4 - 3 M_2^2  =  K_4 ,
```

both sums over **ordered** quadruples.

*Proof.*  `sum_(a,b) C_(a,b) = sum_e (sum_a T_a(e))^2 = sum_e D_e^2 = M_2`.
Each of the three terms of `P` sums over `I^4` to `(sum_(a,b) C_(a,b))^2 = M_2^2`
after relabelling, giving `3 M_2^2`.  For the second identity,
`sum_(a,b,c,d) sum_e T_a T_b T_c T_d = sum_e (sum_a T_a(e))^4 = M_4`.  QED

**Proposition 2.9 (conductor Wick pairings are nonnegative, and the absolute
Wick total is exact).  PROVED.**
In the conductor grading, `C_(j,k) = V_j 1[j = k]`, so for a cell
`(j_1 <= j_2 <= j_3 <= j_4)`

```text
  P_cell = 3 V_j^2      if j_1 = j_2 = j_3 = j_4 = j ,
  P_cell = V_j V_k      if the multiset is {j,j,k,k} with j != k ,
  P_cell = 0            in every other case ,
```

hence `P_cell >= 0` for every cell and

```text
  sum_cells mult(cell) |P_cell|  =  sum_cells mult(cell) P_cell  =  3 M_2^2
```

**exactly**, where `mult` is the number of ordered quadruples in the cell.

*Proof.*  `C_(j,k) = V_j 1[j=k]` is Theorem 2.7.  Substituting into `P` and
enumerating the five multiset patterns of a size-`4` multiset gives the display
(any pairing that puts two distinct levels together contributes `0`).  All three
listed values are `>= 0` since `V_j >= 0`.  The last line is Proposition 2.8
together with `|P_cell| = P_cell`.  QED

This is the structural separation between the two gradings, and it is worth
stating as a slogan: **in a grading that is not orthogonal, `sum |P_cell|` is a
different and much larger number than `3 M_2^2`, and the difference is an
artefact of the grading, not of the arithmetic.**  Measured in the
convolution-order grading, `sum mult |P_cell| / (3 M_2^2)` is `694` at
`ell = 8` and `11444` at `ell = 18`, growing like `2^(+0.41 ell)`
(EVIDENCE, `acb_cab_cells sweep`).

**Theorem 2.10 (parity selection rule).  PROVED.**
In the conductor grading, let `J = max(j_1, j_2, j_3, j_4)`.  Then

```text
  K_(j_1,j_2,j_3,j_4) = 0     unless  #{ i : j_i = J }  is even.
```

*Proof.*  Two parts.

*(a) The fourth-order term.*  Expand each factor by Fourier inversion,
`D_[j](e) = 2^(-ell) sum_(lev chi = j) S_chi conj(chi(e))`.  Then

```text
  sum_e prod_(i=1)^4 D_[j_i](e)
     =  2^(-4 ell) sum_(chi_1,...,chi_4)  ( prod_i S_(chi_i) )
        sum_e conj( chi_1 chi_2 chi_3 chi_4 (e) ) ,
```

with `chi_i` ranging over level-`j_i` characters.  The inner sum is `2^ell` if
`chi_1 chi_2 chi_3 chi_4 = 1` and `0` otherwise.  Restrict such a relation to
the subgroup `H_(J-1)`.  Every `chi_i` with `j_i < J` is trivial on
`H_(J-1)` (it is trivial already on `H_(j_i) supseteq H_(J-1)`).  Every `chi_i`
with `j_i = J` is trivial on `H_J` and nontrivial on `H_(J-1)`, so its
restriction to `H_(J-1)` factors through `H_(J-1)/H_J`, a group of order `2`,
and is the unique nontrivial character `eps` of that quotient.  Hence

```text
  1  =  (chi_1 chi_2 chi_3 chi_4)|_(H_(J-1))  =  eps^( #{i : j_i = J} ) ,
```

which forces `#{i : j_i = J}` to be even.  If it is odd, no quadruple
contributes and the fourth-order term vanishes.

*(b) The pairing term.*  By Proposition 2.9, `P_cell != 0` requires the multiset
`{j_1,...,j_4}` to be of the form `{j,j,j,j}` or `{j,j,k,k}`; in both cases the
number of indices equal to the maximum is `4` or `2`, i.e. even.  QED

**Consequences.**  The rule annihilates the great majority of cells: measured,
`147` of the `210` cells at `(ell,n) = (8,17)` and `6156` of the `7315` cells at
`(20,42)`, about `82%` throughout (EVIDENCE, `acb_cab_levels`, `ell = 4..20`,
both parities, reported as `odd_max_nonzero = 0` on every row).

**Theorem 2.11 (layer energies).  PROVED given (I1), (I2); part (b) also uses
(I1').**
For the endpoint discrepancy `D` of section 1.3:

```text
  (a)  V_1 = 0 ;
  (b)  V_2 = 2^(n - ell + 1)   exactly ;
  (c)  V_j <= 2^(n - ell) 2^(j-1) (j-1)^2   for every 1 <= j <= ell .
```

*Proof.*  By Theorem 2.7's proof and Plancherel restricted to the level-`j`
support, `V_j = 2^(-ell) sum_(lev chi = j) |S_chi|^2`.
(a) At level `1` the `L`-polynomial has degree `0`, so `S_chi = 0` by (I1).
(c) By (CT) there are `2^(j-1)` characters at level `j`, each with
`|S_chi| <= (j-1) 2^(n/2)` by (I1); hence
`V_j <= 2^(-ell) 2^(j-1) (j-1)^2 2^n`.
(b) At level `2` there are two characters, each with `L`-degree exactly `1` and
inverse root of absolute value exactly `2^(1/2)` by (I1'), so
`|S_chi| = 2^(n/2)` and `V_2 = 2^(-ell) * 2 * 2^n = 2^(n-ell+1)`.  QED

*Corroboration (EVIDENCE).*  `2^ell V_j` computed by the sibling recursion agrees
with the CAS routine `exact_conductor_second_moment(j, n)` -- an unrelated
algorithm using two modular character tables and CRT -- at every level of
`(8,17)` and `(9,20)`.  The measured "Weil fill" `V_j / (2^(n-ell) 2^(j-1)(j-1)^2)`
is `1.0000` at `j = 2` and never exceeds `0.62` at any other level over
`ell = 6..20`.

**Theorem 2.12 (exact recursion in `ell` at fixed `n`).  PROVED.**
Fix `n`.  Let `pi : G_ell -> G_(ell-1)` be the truncation, and write
`D^(ell)`, `D^(ell-1)` for the class discrepancies of the same degree `n` at the
two levels.  Then for every `j <= ell - 1`

```text
  D_[j]^(ell)  =  (1/2) ( D_[j]^(ell-1) o pi ) ,      V_j^(ell) = (1/2) V_j^(ell-1) ,
```

and consequently, for every cell all of whose levels are `<= ell - 1`,

```text
  K^(ell)_(j_1,j_2,j_3,j_4)  =  (1/4) K^(ell-1)_(j_1,j_2,j_3,j_4) .
```

*Proof.*  Since `mu^(ell-1) = 2 mu^(ell)` and each class of `G_(ell-1)` is the
union of the two classes above it, `D^(ell-1)(e') = sum_(pi(e) = e') D^(ell)(e)`.
For `j <= ell-1` the truncation carries `H_j^(ell)` onto `H_j^(ell-1)` with
`pi^(-1)(H_j^(ell-1)) = H_j^(ell)`, so for any `e in G_ell`

```text
  sum_(h in H_j^(ell)) D^(ell)(e h)
    =  sum_( f in pi^(-1)( pi(e) H_j^(ell-1) ) ) D^(ell)(f)
    =  sum_( f' in pi(e) H_j^(ell-1) ) D^(ell-1)(f') .
```

Dividing by `2^(ell-j)` on the left and by `2^(ell-1-j)` on the right gives
`(P_j^(ell) D^(ell))(e) = (1/2) (P_j^(ell-1) D^(ell-1))(pi(e))`, and subtracting
the same identity at `j-1` gives the first display.  Squaring and summing over
`e in G_ell` (each `e'` has two preimages) gives
`V_j^(ell) = (1/4) * 2 * V_j^(ell-1) = (1/2) V_j^(ell-1)`.

For the cell: the fourth-order term at level `ell` is
`2^ell sum_(e in G_ell) prod_i D_[j_i]^(ell)(e) = 2^ell * 2^(-4) * 2 *
sum_(e' in G_(ell-1)) prod_i D_[j_i]^(ell-1)(e') = (1/4) * 2^(ell-1)
sum_(e') prod_i D_[j_i]^(ell-1)(e')`, i.e. exactly `1/4` of the level-`(ell-1)`
fourth-order term.  Each Wick pairing is a product of two `V`'s, so it also
scales by `(1/2)^2 = 1/4`.  Hence `K` scales by `1/4`.  QED

**Reading.**  This is an *equality*, not an estimate: the entire sub-top-level
part of the conductor cell tensor at level `ell` is the level-`(ell-1)` tensor
divided by `4`, while the endpoint budget `2^ell (mu - P_n)^4` gains a factor
`2^5` per unit `ell`.  The residual family is exactly the cells with two or four
indices at the top level `ell` (counts of one and three at the top level are
excluded by Theorem 2.10).  Verified to full precision at `(8,17)` and `(12,25)`
(EVIDENCE, `acb_cab_levels`).

### 2.3  The reduction chain, and the main conditional theorem

Everything in this subsection is elementary given section 2.2.  The point is
that the conductor grading admits a chain of reductions which *ends in a
statement with no cells and no interaction between levels at all*.

Define the **conductor-absolute envelope**

```text
  U(e)  :=  sum_(j=1)^ell | D_[j](e) | ,
```

and write `||f||_4 := ( sum_e f(e)^4 )^(1/4)` for the counting-measure norm.

**Proposition 2.13 (envelope reduction).  PROVED.**
`M_4 <= sum_e U(e)^4`, so

```text
  sum_e U(e)^4  <  (mu - P_n)^4    ==>   (W4-exact)   ==>   I_n(1) >= 1 .   (ENV-L)
```

*Proof.*  By (GRADE) and the triangle inequality `|D_e| <= U(e)` pointwise;
raise to the fourth power and sum; then Corollary 2.5 and Theorem 2.4.  QED

**Proposition 2.14 (layerwise reduction).  PROVED.**

```text
  sum_(j=1)^ell || D_[j] ||_4   <   mu - P_n        ==>   (ENV-L) .        (L4-LAYER)
```

*Proof.*  Minkowski's inequality in `L^4` of the counting measure applied to
`U = sum_j |D_[j]|` gives `( sum_e U^4 )^(1/4) <= sum_j || D_[j] ||_4`.  QED

**Proposition 2.15 (`L^4` from sup and energy).  PROVED.**
For every `j`, `|| D_[j] ||_4 <= ( max_e |D_[j](e)| )^(1/2) V_j^(1/4)`.

*Proof.*  `sum_e D_[j](e)^4 <= (max_e D_[j](e)^2) sum_e D_[j](e)^2 =
(max_e |D_[j](e)|)^2 V_j`; take fourth roots.  QED

This isolates a single unproved quantity.  Write, for `1 <= j <= ell`,

```text
  kappa_j  :=  ( max_e |D_[j](e)| ) * 2^ell / ( (j-1) 2^((j-1)/2) 2^(n/2) )     (j >= 2).
```

The denominator is the **square root, in the character count**, of the trivial
triangle bound: by Fourier inversion and (I1),
`max_e |D_[j](e)| <= 2^(-ell) sum_(lev chi = j) |S_chi| <= 2^(-ell) 2^(j-1)(j-1)2^(n/2)`,
so `kappa_j <= 2^((j-1)/2)` is trivial and `kappa_j = O(1)` is the square-root
saving.

> **(SUP-L) (CONJECTURE).**  There is an absolute constant `K` such that for
> both endpoint degrees `n in {2 ell + 1, 2 ell + 2}` and every conductor level
> `2 <= j <= ell`,
> ```text
>       max_e | D_[j](e) |   <=   K (j-1) 2^((j-1)/2) 2^(n/2) / 2^ell ,
> ```
> i.e. `kappa_j <= K` uniformly in `j` and `ell`.

**Theorem 2.16 (main conditional theorem).  PROVED given (I1), (I2) and
(SUP-L).**
Assume (SUP-L) holds with constant `K`.  Then for every `ell` and both endpoint
parities,

```text
  M_4  <=  K^2 * 2^(2n - 3 ell) * T(ell)^4 ,      T(ell) := sum_(i=1)^(ell-1) i 2^(i/2) .
```

Consequently, with `K = 2`, `(W4-exact)` holds -- and therefore an irreducible
of degree `n` exists in the identity class -- for **every `ell >= 22` at the odd
endpoint and every `ell >= 20` at the even endpoint**.  With `K = 4` the
thresholds are `25` and `23`; with `K = 10^6` they are `67` and `65`.

*Proof.*  `V_1 = 0` (Theorem 2.11(a)) forces `D_[1] = 0`, so all sums start at
`j = 2`.  Combining (SUP-L) with Theorem 2.11(c) in Proposition 2.15,

```text
  || D_[j] ||_4  <=  [ K (j-1) 2^((j-1)/2) 2^(n/2) 2^(-ell) ]^(1/2)
                     * [ 2^(n-ell) 2^(j-1) (j-1)^2 ]^(1/4)
                 =   K^(1/2) (j-1) 2^((j-1)/2) 2^((2n - 3 ell)/4) ,
```

because the powers of `(j-1)` are `1/2 + 1/2 = 1`, the powers of `2^((j-1))` are
`1/4 + 1/4 = 1/2`, and the remaining exponent is
`n/4 - ell/2 + (n-ell)/4 = (2n - 3 ell)/4`.  Proposition 2.14 then gives

```text
  sum_j || D_[j] ||_4  <=  K^(1/2) 2^((2n-3ell)/4) sum_(j=2)^ell (j-1) 2^((j-1)/2)
                        =  K^(1/2) 2^((2n-3ell)/4) T(ell) ,
```

and Proposition 2.13 gives `M_4 <= (sum_j ||D_[j]||_4)^4 = K^2 2^(2n-3ell) T(ell)^4`.

At the odd endpoint `2n - 3 ell = ell + 2` and `mu - P_n = 2^(ell+1) - 1`
(Lemma 2.1), so the sufficient inequality is

```text
  K^2 2^(ell+2) T(ell)^4  <  ( 2^(ell+1) - 1 )^4 .                       (ODD)
```

At the even endpoint `2n - 3 ell = ell + 4` and `mu - P_n = 2^(ell+2) -
P_n^sharp` (Lemma 2.2), so it is

```text
  K^2 2^(ell+4) T(ell)^4  <  ( 2^(ell+2) - P_n^sharp )^4 .               (EVEN)
```

Both are explicit inequalities between integers and a square root of two.
Evaluating them in 80-digit decimal arithmetic (script `cross.py`, reproduced in
`23-artifact.md`) gives the first `ell` from which each holds for every larger
`ell`:

```text
   K        odd (ODD)     even (EVEN)
   1.6         21              19
   2.0         22              20
   2.5         23              21
   4.0         25              23
   8.0         28              25
  16.0         31              28
  64.0         36              33
  10^3         45              43
  10^6         67              65
```

QED

**Remark 2.16-tight.**  The crossovers are tight at the first level, so they
should not be quoted with slack.  At `K = 2`, odd endpoint: `ell = 21` fails
(`4.680025e6` against `4.194303e6`), `ell = 22` holds with a `0.8%` margin
(`8.318030e6 < 8.388607e6`).  Even endpoint: `ell = 19` fails by `1.9%`,
`ell = 20` holds by `9.2%`.  (Recomputed independently three times: diary 11,
this artifact's `cross.py`, and `20-verify-chains.md`; all eight entries of the
`K in {1.6, 2.0, 2.5, 4.0}` table agree.)

**Remark 2.16a (insensitivity to `K`, corrected).**  Diary 11 stated that the
crossover "moves by one level per doubling of `K`".  That is not right: the
chain gains `2^(ell/4)` per level against a cost of `K^(1/2)`, so a doubling of
`K` costs `2^(1/2)`, i.e. about **two** levels, and the `(ell-1)` drift in
`T(ell)` makes the measured cost about **three** levels (`2.0 -> 4.0` moves
`22 -> 25`).  The qualitative conclusion is unchanged and in fact stronger than
needed: even `K = 10^6` gives the endpoint from `ell = 67`, and a
`K = 2^(o(ell))` would suffice.  **The reduction is insensitive to the constant;
what it is not insensitive to is uniformity in `j`.**

**Remark 2.16b (where the finite range goes).**  For `ell <= 21` the endpoint is
not delivered by Theorem 2.16.  The lane's separately certified finite range
(degree `<= 400`, i.e. `ell <= 199`) covers those rows; that certification is
*not* re-verified in this artifact and is cited, not claimed.

**Two intermediate statements, recorded because they are strictly weaker
hypotheses that also close.**  With
`A_L := sum_(cells) mult |K_cell|` in the conductor grading:

**Proposition 2.17 (split reduction).  PROVED.**
`A_L <= R_L + 3 M_2^2` where `R_L := sum_(cells) mult |2^ell sum_e prod_i D_[j_i]|`.
*Proof.*  Triangle inequality per cell, then Proposition 2.9 for the pairing
half.  QED

The corresponding statement in the convolution-order grading is *exponentially
lossy*: the ratio `(sum mult |2^ell raw| + sum mult |P_cell|)/A` there is `8.31`
at `ell = 8` and `40.58` at `ell = 18`, growing like `2^(+0.25 ell)` (EVIDENCE,
`acb_cab_cells`).  In the conductor grading the same split costs a bounded
factor `5` to `60` over `ell = 6..20`.  This is Proposition 2.9 in action.

### 2.4  The multiplicative dichotomy: `R_0 = prod (1 + q_j)`

This subsection replaces the conductor *components* of `D` by the conductor
*cylinder masses* of `D^2`.  Assume `M_2 > 0` (otherwise `D = 0`, `M_4 = 0` and
(W4-exact) is trivial).  Write, for `0 <= j <= ell` and `b` in `G_ell/H_j`,

```text
  m_j(b)  :=  sum_( e in b H_j ) D_e^2 ,        C_j  :=  2^j sum_b m_j(b)^2 ,
  fhat(chi) := sum_e D_e^2 chi(e) ,             E_j  :=  C_j - C_(j-1) .
```

**Proposition 2.18 (`C_j` is a cumulative spectral mass).  PROVED.**

```text
  C_j  =  sum_( chi : lev(chi) <= j )  | fhat(chi) |^2 ,
  E_j  =  sum_( chi : lev(chi)  = j )  | fhat(chi) |^2 ,
```

and in particular `C_0 = M_2^2`, `C_ell = 2^ell M_4`.

*Proof.*  The pushforward of `e -> D_e^2` along `G_ell -> G_ell/H_j` is
`b -> m_j(b)`, and for `chi` trivial on `H_j` one has
`sum_b m_j(b) chi(b) = sum_e D_e^2 chi(e) = fhat(chi)`.  Parseval on the group
`G_ell/H_j` of order `2^j` gives
`sum_(chi of G_ell/H_j) |fhat(chi)|^2 = 2^j sum_b m_j(b)^2 = C_j`.  The
characters of `G_ell/H_j` are exactly those of level `<= j`.  Then
`C_0 = |fhat(1)|^2 = M_2^2` and `C_ell = 2^ell sum_e D_e^4 = 2^ell M_4`.  QED

**Theorem 2.19 (the `q`-product identity).  PROVED.**
For `1 <= j <= ell` let each level-`(j-1)` cylinder `b` split into its two
level-`j` children with masses `u_b, v_b >= 0`, `u_b + v_b = m_(j-1)(b)`, and let

```text
  t_b := ( u_b - v_b ) / m_(j-1)(b)  in [-1, 1]     (:= 0 if m_(j-1)(b) = 0) ,
  q_j := ( sum_b m_(j-1)(b)^2 t_b^2 ) / ( sum_b m_(j-1)(b)^2 )  .
```

Then

```text
  C_j / C_(j-1)  =  1 + q_j ,        0 <= q_j <= 1 ,
```

and therefore

```text
  R_0  =  2^ell M_4 / M_2^2  =  prod_(j=1)^ell ( 1 + q_j ) .            (D-PROD)
```

Equivalently `q_j = E_j / C_(j-1)`, and `C_(j-1) <= C_j <= 2 C_(j-1)`.

*Proof.*  Writing `u_b = m_b(1 + t_b)/2` and `v_b = m_b(1 - t_b)/2` with
`m_b := m_(j-1)(b)`,

```text
  u_b^2 + v_b^2  =  m_b^2 (1 + t_b^2) / 2 ,
```

so `C_j = 2^j sum_b (u_b^2 + v_b^2) = 2^(j-1) sum_b m_b^2 (1 + t_b^2)
= C_(j-1) (1 + q_j)`, using `C_(j-1) = 2^(j-1) sum_b m_b^2`.  Since
`|t_b| <= 1` we get `0 <= q_j <= 1`, i.e. `C_(j-1) <= C_j <= 2 C_(j-1)`.
`C_(j-1) >= C_0 = M_2^2 > 0`, so the ratio is defined.  Telescoping from
`C_0 = M_2^2` to `C_ell = 2^ell M_4` gives (D-PROD).  QED

*(Machine check: `acb_dic_profile` asserts `sum_b m_j(b) = M_2` at every level,
`C_0 = M_2^2`, `C_ell = 2^ell M_4`, and `C_(j-1) <= C_j <= 2 C_(j-1)` on every
one of 36 rows `ell = 2..19`, both parities, aborting the row on any violation;
a from-scratch sympy brute force over every monic polynomial reproduces every
`C_j`, `q_j` and `m_j(b)` at `(4,9)`, `(4,10)`, `(5,11)`, `(5,12)`.)*

**Theorem 2.20 (the dichotomy).  PROVED given (I1), (I2).**
Let `P_n` be a valid proper-prime-power bound and
`G := 2^ell (mu - P_n)^4 / (mu Sigma(ell))^2`.  Then **either**

```text
   (DELOC)   prod_(j=1)^ell ( 1 + q_j )  <  G ,
```

in which case `(W4-exact)` holds and `I_n(1) >= 1`; **or** for every `Q in [0,1]`
and every set `J` of conductor levels,

```text
   (INC)     #{ j in J : q_j > Q }  >=  |J|  -  ( ell - log2 G ) / ( 1 - log2(1+Q) ) .
```

*Proof.*  If (DELOC) holds then `2^ell M_4 = R_0 M_2^2 < G M_2^2 <=
G (mu Sigma(ell))^2 = 2^ell (mu - P_n)^4` by Corollary 1.2, so
`M_4 < (mu - P_n)^4`; apply Corollary 2.5 and Theorem 2.4.

Otherwise `sum_(j=1)^ell log2(1 + q_j) >= log2 G`.  Every term is in `[0,1]` by
Theorem 2.19.  Let `k := #{j in J : q_j > Q}`.  Bounding the `ell - |J|` terms
outside `J` and the `k` large terms inside `J` by `1`, and the remaining
`|J| - k` terms by `log2(1+Q)`,

```text
  log2 G  <=  (ell - |J|) + k + (|J| - k) log2(1+Q) = ell - (|J| - k)(1 - log2(1+Q)) ,
```

which rearranges to (INC).  QED

**Corollary 2.21 (the increment made concrete).  PROVED given (I1), (I2).**
Put `PR_j := M_2^2 / sum_b m_j(b)^2 = 2^j C_0 / C_j`.  Then `PR_0 = 1`,
`PR_ell = M_2^2 / M_4`, and `PR_j / PR_(j-1) = 2/(1 + q_j) in [1, 2]`, so
`PR_j` is nondecreasing.  If (DELOC) fails then at **every** level `j`

```text
   max_b m_j(b)  >=  M_2 / PR_j  >=  ( G / 2^ell ) M_2 .                 (INC-CYL)
```

*Proof.*  `PR_j/PR_(j-1) = 2 C_(j-1)/C_j = 2/(1+q_j)`, in `[1,2]` by Theorem 2.19;
`PR_ell = 2^ell M_2^2/(2^ell M_4)`.  Failure of (DELOC) means `R_0 >= G`, so
`PR_ell = 2^ell/R_0 <= 2^ell/G`, and monotonicity gives `PR_j <= 2^ell/G` for all
`j`.  Finally `sum_b m_j(b)^2 <= (max_b m_j(b)) sum_b m_j(b) = (max_b m_j(b)) M_2`,
so `M_2^2/PR_j <= (max_b m_j(b)) M_2`.  QED

Asymptotically `log2 G = ell + 2 - 4 log2 ell + o(1)`, so (INC) says that all but
`O(log ell)` conductor levels must be **maximally Haar-imbalanced**, and
(INC-CYL) says that at every level some cylinder carries a `~ 4/ell^4` share of
the whole `L^2` mass of `D`.  This is a genuine density-increment conclusion
extracted by an exact identity rather than by a hypercontractive estimate.

**Proposition 2.22 (sufficiency of a low-conductor input).  PROVED given (I1),
(I2).**
If `q_j <= Q` for every `j` in a set `J` of levels, then
`R_0 <= 2^(ell - |J|)(1+Q)^(|J|)`, so `(W4-exact)` -- hence the endpoint at that
parity -- follows as soon as

```text
   |J| ( 1 - log2(1+Q) )  >  ell - log2 G  =  4 log2 ell - 2 + o(1) .
```

Two calibrations: `q_j <= 1/2` on `ceil(9.7 log2 ell)` levels suffices;
`q_j <= 1/ell` on `ceil(4.1 log2 ell)` levels suffices.

*Proof.*  (D-PROD) with `1 + q_j <= 2` off `J` and `1 + q_j <= 1+Q` on `J`, then
Theorem 2.20's first branch.  The two calibrations absorb the `Sigma(ell)`
correction conservatively; the measured `log2 G` runs above `ell + 2 - 4 log2 ell`
(e.g. `4.63` against `4.00` at `ell = 19`), so they are safe.  QED

**Theorem 2.23 (`E_1 = 0` at odd endpoints).  PROVED, unconditional.**
Let `n = 2 ell + 1`.  Then `fhat(chi_1) = 0` for the unique level-`1` character
`chi_1`, hence `E_1 = 0` and `q_1 = 0`.  At even `n` the argument gives nothing,
and measurement shows the conclusion is false there.

*Proof.*  The substitution `sigma_0 : F(x) -> F(x+1)` is a ring automorphism of
`F_2[x]` fixing degrees, so it permutes `A_n` and preserves `Lambda`.  Write
`F = sum_(i=0)^n a_i x^(n-i)` with `a_0 = 1`; then

```text
  F(x+1)  =  sum_i a_i (x+1)^(n-i) ,     so     a'_j = sum_(i=0)^j a_i C(n-i, j-i) .
```

Thus `a'_j` depends only on `a_0, ..., a_j`.  In particular `(a'_1, ..., a'_ell)`
depends only on `(a_1, ..., a_ell)`, so `sigma_0` descends to a map
`sigma : G_ell -> G_ell` on classes, and `sigma` is an involution because
`(F(x+1))(x+1) = F(x)`.  Since `sigma_0` is a `Lambda`-preserving bijection of
`A_n` compatible with the class map,

```text
  N_n(sigma(e)) = N_n(e) ,   hence   D_(sigma(e)) = D_e   for every e.        (INV)
```

Next, `a'_1 = C(n,1) + a_1 = n + a_1 (mod 2)`.  The map `e -> a_1(e)` is a
homomorphism `G_ell -> F_2` (the `t`-coefficient of a product of principal units
is the sum of the `t`-coefficients), trivial on `H_1` and nontrivial on `G_ell`,
so `chi_1(e) := (-1)^(a_1(e))` is *the* character of exact level `1`.  For `n`
odd, `a_1(sigma(e)) = a_1(e) + 1`, i.e.

```text
  chi_1( sigma(e) )  =  - chi_1(e) .                                          (FLIP)
```

Reindexing the sum by the bijection `sigma` and using (INV) and (FLIP),

```text
  fhat(chi_1) = sum_e D_e^2 chi_1(e)
              = sum_e D_(sigma(e))^2 chi_1(sigma(e))
              = - sum_e D_e^2 chi_1(e)  =  - fhat(chi_1) ,
```

so `fhat(chi_1) = 0`.  By Proposition 2.18, `E_1 = |fhat(chi_1)|^2 = 0`, and
`q_1 = E_1/C_0 = 0`.  For `n` even, `C(n,1) = 0 (mod 2)` and (FLIP) fails.  QED

*(EVIDENCE: `E_1 = 0` exactly on all 15 odd rows `ell = 5..19` and on no even
row -- `acb_dic_profile`.  Note the same involution gives `S_(chi_1) = 0`, which
is also implied by (I1); the content of Theorem 2.23 is that it holds for the
spectrum of `D^2`, where no `L`-function argument is available.)*

**Remark.**  Theorem 2.23 supplies exactly one of the `4 log2 ell - 2` bits that
Proposition 2.22 needs, unconditionally and for free.  The even-endpoint
analogue is open; the natural candidate level is `2^(v_2(n))`, which the lane's
`translation_paired_conductor_level` isolates for the `D`-spectrum, but the
transfer to the `D^2`-spectrum needs the involution argument run at that level
and is not carried out here.

### 2.5  The convolution-order grading and why it is the wrong one

For completeness, and because it explains the cell count and the failure of the
earlier candidate bounds, here is the second grading of `D` that occurs in this
project.  For `1 <= d <= n` put

```text
  M_m(e)  :=  sum_( F in A_m, <F> = e ) mob(F) ,       A_d(e) := #{ F in A_d : <F> = e } ,
  T_d     :=  d ( A_d * M_(n-d) )     (group convolution on G_ell) .
```

**Lemma 2.24 (order-grading Fourier form).  PROVED.**
`sum_(d=0)^n T_d = N_n` pointwise, and for every character `chi`,

```text
  (T_d)^(chi)  =  d * a_d(chi) * m_(n-d)(chi) ,
  a_d(chi) := sum_(u in V_d) chi(u)  = [z^d] L(chi,z)   (d <= ell) ,
  m_j(chi) := sum_(F in A_j) mob(F) chi(<F>) = [z^j] 1/L(chi,z) .
```

*Proof.*  `Lambda = mob * deg` as Dirichlet convolutions on `A` (the coefficient
form of `-zeta'/zeta = (1/zeta)(-zeta')`), i.e.
`Lambda(F) = sum_(AB = F) mob(A) deg(B)`.  Splitting by `deg B = d` and using
(MULT),

```text
  N_n(e) = sum_(F in A_n, <F>=e) Lambda(F)
         = sum_(d=0)^n d sum_( B in A_d, A in A_(n-d), <AB> = e ) mob(A)
         = sum_(d=0)^n d (A_d * M_(n-d))(e) .
```

For `d <= ell` the map `A_d -> V_d`, `F -> <F>`, is a bijection, so
`A_d = 1_(V_d)` and `(A_d)^(chi) = a_d(chi)`.  The generating identities
`sum_F chi(<F>) z^(deg F) = L(chi,z)` and `sum_F mob(F) chi(<F>) z^(deg F) =
1/L(chi,z)` are the Euler product and its inverse.  QED

**Lemma 2.25 (order-level support).  PROVED.**
`a_d(chi) = 0` whenever `d >= lev(chi)` and `d <= ell`.  Hence `T_d` is
supported on characters of level `>= d + 1`.

*Proof.*  `V_d` is a complete set of coset representatives for `H_d` in `G_ell`
(the truncation `V_d -> G_ell/H_d` is a bijection), and for `j := lev(chi) <= d`
the composite `V_d -> G_ell/H_d -> G_ell/H_j` is surjective with all fibres of
size `2^(d-j)`.  Since `chi` is trivial on `H_j`, `chi(u)` depends only on the
image of `u` in `G_ell/H_j`, so

```text
  a_d(chi) = 2^(d-j) sum_( w in G_ell/H_j ) chibar(w) = 0 ,
```

`chibar` being the induced -- and nontrivial -- character of `G_ell/H_j`.  QED

**Lemma 2.26 (the order decomposition terminates exactly).  PROVED.**
`T_d` is a constant function for every `d >= ell`, `T_d` has mean `0` for
`1 <= d <= ell - 1`, `T_0 = 0`, and therefore

```text
  sum_(d=1)^(ell-1) T_d  =  D    exactly .
```

*Proof.*  For `d = ell`, `V_ell = G_ell` so `A_ell = 1` is constant; for
`d > ell`, `A_d(e) = 2^(d-ell)` is constant.  A constant function convolved with
anything is constant, so `T_d` is constant for `d >= ell`.  For
`1 <= d <= ell-1` the mean is `2^(-ell)(T_d)^(1) = 2^(-ell) d 2^d
sum_(F in A_(n-d)) mob(F)`, which is `0` by (MU) since `n - d >= ell + 2 >= 2`.
Summing Lemma 2.24 and subtracting means: `N_n = (constant part) +
sum_(d=1)^(ell-1) T_d`, and taking means gives `constant part = mu`.  QED

*Consequence.*  The symmetric order-cell tensor has exactly
`C(ell + 2, 4)` cells (multisets of size `4` from `{1, ..., ell-1}`).  This
identity is checked at runtime by the CAS routine
`connected_order_cumulant_report` on every row; Lemma 2.26 makes it a theorem.

**Why the order grading is the wrong one.**  Lemma 2.25 says the order grading
is the strictly lower-triangular shadow of the conductor grading: `T_d` sees only
levels `> d`.  It is *not* orthogonal, so Proposition 2.9 fails for it, and every
cellwise-absolute bound built on it pays the full non-orthogonality:
measured `sum mult |P_cell| / (3 M_2^2)` grows like `2^(+0.41 ell)`, and
`sum mult |K_cell| / M_2^2` saturates at an absolute constant `~ 1580-1900` from
`ell = 13` instead of decaying.  In the conductor grading the same quantity
`A_L / M_2^2` falls below `1` at `ell = 10` and decays like `2^(-0.46 ell)`.
(All EVIDENCE; `acb_cab_cells` and `acb_cab_levels`, `ell = 4..20`.)

### 2.6  The dyadic autocorrelation fibre family

This subsection concerns a **different object** from the rest of the artifact:
the shifted Moebius autocorrelation of a binary "short interval", which is the
input to the annihilator/energy route rather than to the fourth-moment route.
It is included because the structural lemmas below are proved, and because they
correct two published-in-tree statements.

**Setting.**  Fix `ell >= 4`, a degree `k`, and an interval degree `d` with
`1 <= d < ell`; the charter's calibration is `d = ell - 1`.  Let

```text
  Dom_k  :=  { f monic, deg f = k, f(0) = 1 } ,      |Dom_k| = 2^(k-1) ,
```

indexed by `m in [0, 2^(k-1))` via `f_m = x^k + (coefficient bits of m in
positions 1..k-1) + 1`.  For a **shift** `s in [1, 2^d)` put
`h := x * s(x)`, a nonzero polynomial with `v(h) >= 1` and `deg h <= d`
(`v` = the `x`-adic valuation), so `f_(m xor s) = f_m + h` and `f_m + h in Dom_k`.
Let `u_m := f_m mod x^(ell+1)`, a unit, and define the **inverse difference**

```text
  delta_h(f)  :=  u^(-1)  +  (u + h)^(-1)      in F_2[x]/x^(ell+1),   u = f mod x^(ell+1) .
```

An index `m` is **admissible** for `s` when `deg delta_h(f_m) <= d`.  The
**fibres** of the family are the level sets of the pair

```text
  m  ->  ( floor(m / 2^d) ,  delta_h(f_m) )
```

on the admissible set; each fibre `F` is contained in a coset
`f_m + span{ x, ..., x^d }`.  Finally set

```text
  eps(m) := mob(f_m) mob(f_m + h) in {0, +1, -1} ,       c_F := sum_(m in F) eps(m) ,
  N_points := sum_F |F| ,     N_sf := #{ m in some fibre : eps(m) != 0 } ,
  Delta := sum_F c_F ,        n_F := dim F   (when F is an affine subspace) .
```

(The equality `eps(m) = chi_8(Disc f_m * Disc f_(m+h)) = mob(f_m) mob(f_m + h)`
uses the lane's proved Stickelberger-type identity
`mob(f) = (-1)^(deg f) chi_8(Disc f)`; the two degree signs cancel.  So `c_F` is a
**restricted Moebius autocorrelation**, and its zeros are Moebius zeros, not
degenerate Gauss sums.)

**Lemma 2.27 (shift-stability).  PROVED.**
For every shift `s` and every fibre `F` of that shift, `m in F` implies
`m xor s in F`, and `eps(m xor s) = eps(m)`.

*Proof.*  `s < 2^d` touches only the low `d` bits, so
`floor(m/2^d) = floor((m xor s)/2^d)`.  And
`delta_h(f_(m xor s)) = u_(m xor s)^(-1) + u_((m xor s) xor s)^(-1) =
(u_m + h)^(-1) + u_m^(-1) = delta_h(f_m)`, the expression being symmetric in the
pair.  So the two indices have the same fibre key, and admissibility is the same
condition.  Finally `eps(m xor s) = mob(f_m + h) mob(f_m) = eps(m)`.  QED

**Corollary 2.28 (the corrected fourth-moment identity).  PROVED.**
Every `|F|` is even and every `c_F` is even, and

```text
  sum_F c_F^2  =  2 N_sf  +  Theta ,
  Theta  :=  sum_F sum_( x, y in F,  y not in {x, x xor s} ) eps(x) eps(y) .
```

*Proof.*  `m -> m xor s` is a fixed-point-free involution of `F` by Lemma 2.27
(fixed-point-free because `s != 0`), so `|F|` is even and, `eps` being constant
on its orbits, `c_F = 2 * (sum over orbit representatives)` is even.  Expanding
`c_F^2 = sum_(x,y in F) eps(x) eps(y)`, the terms `y = x` give
`eps(x)^2 = 1[eps(x) != 0]` and the terms `y = x xor s` give
`eps(x) eps(x xor s) = eps(x)^2` by Lemma 2.27; summing over all fibres each
family contributes `N_sf`.  QED

> **Correction recorded.**  Sweep-08 and the doc comment on
> `BinaryDyadicAutocorrelationFibreReport::within_fibre_off_diagonal_correlation`
> both assert `sum_F c_F^2 = N_points + (off-diagonal)`, and read `(E2')` as
> "the within-fibre off-diagonal correlation is nonpositive".  Both are wrong
> whenever `eps` vanishes anywhere, which is essentially always: the diagonal is
> `N_sf`, not `N_points`, and the `s`-partner term is *forced*, not free.  With
> the corrected identity the true off-diagonal `Theta` is **positive** on 7 of 22
> measured rows (largest: `+419144` at `(ell,k,d) = (14,16,13)`), so nonpositivity
> is not available as a hypothesis.  (EVIDENCE, `acb_gr_fibre_census`.)

**Theorem 2.29 (fibres are complete orbits of an explicit group).  PROVED.**
Fix a shift with `h != 0`, `v := v(h) >= 1`, and put `r := ell + 1`, `W := r - v`,
and `V := span_(F_2){ x, x^2, ..., x^d }`.  Then:

1. For `tau in V`, `delta_h(f + tau) = delta_h(f)` for one (equivalently, every)
   `f` **iff** `h tau (tau + h) = 0` in `F_2[x]/x^r`, equivalently iff
   `v(tau) + v(tau + h) >= W`.
2. The set `T_h := { tau in V : v(tau) + v(tau+h) >= W }` is an `F_2`-subspace
   of `V`, and the level sets of `delta_h` inside one input coset are exactly
   the cosets of `T_h`.  Hence **every fibre is a complete `T_h`-orbit**, in
   particular an affine subspace, and `n_F = dim T_h` for every fibre of that
   shift.
3. Explicitly, writing `K := { z in F_2[x]/x^W : v(z) >= 1, v(z) + v(z+h) >= W }`,

```text
   dim K  =  v + 1              if 2v < W ,
   dim K  =  floor( W / 2 )     if 2v >= W ,
```

   and if `d >= W - 1` (which holds for every `v >= 1` at the calibration
   `d = ell - 1`) then `dim T_h = dim K + (d - W + 1)`.

*Proof.*  **(1)** Write `u = f mod x^r`.  In `F_2[x]/x^r`,
`delta_h(f) = u^(-1) + (u+h)^(-1) = ((u+h) + u) / (u(u+h)) = h / (u(u+h))`, all
factors being units.  Then

```text
  (u+tau)(u+tau+h)  -  u(u+h)  =  tau^2 + h tau     (characteristic 2),
```

so `delta_h(f+tau) = delta_h(f)` iff `h ( tau^2 + h tau ) = 0` in `F_2[x]/x^r`
(cross-multiply by the four units).  Since `h = x^v * (unit)`, this says
`tau^2 + h tau = tau (tau + h) = 0` in `F_2[x]/x^W`, i.e.
`v(tau) + v(tau+h) >= W`.  The condition does not involve `f`.

**(2)** `tau -> tau^2 + h tau` is `F_2`-linear (Frobenius), so `T_h` is the
kernel of a linear map restricted to `V`, hence a subspace; and by (1) two
elements of the same input coset have the same `delta_h` iff their difference
lies in `T_h`.

**(3)** For `z != 0` with `v(z) >= 1`, three cases.
*(alpha)* `v(z) < v`: then `v(z+h) = v(z)`, so the condition is `2 v(z) >= W`.
*(beta)* `v(z) > v`: then `v(z+h) = v`, so the condition is `v(z) >= W - v`.
*(gamma)* `v(z) = v`: then `z + h` has valuation `> v`; writing `w := z + h`, the
condition is `v + v(w) >= W`, i.e. `v(w) >= W - v`.

If `2v < W` then `W - v > v`, so case *(alpha)* is empty (it would need
`v(z) >= ceil(W/2) > v`), case *(beta)* gives `{ z : v(z) >= W - v }`, a space of
dimension `#{ j : W-v <= j <= W-1 } = v`, and case *(gamma)* gives `h` plus that
same space.  Since `v(h) = v < W - v`, `h` is not in it, so
`K = { v(z) >= W-v } (+) F_2 h` and `dim K = v + 1`.

If `2v >= W` then `W - v <= v`, and one checks that `K = { z : v(z) >= ceil(W/2) }`:
every such `z` lies in *(alpha)*, *(beta)* or *(gamma)* as `v(z) <, >, = v`
(in case *(beta)*, `v(z) > v >= W - v`; in case *(gamma)*, `v(w) > v >= W-v`),
and conversely every element of *(alpha)*, *(beta)*, *(gamma)* has
`v(z) >= ceil(W/2)`.  Hence `dim K = #{ j : ceil(W/2) <= j <= W-1 } = floor(W/2)`.

For the last claim, the map `tau -> tau^2 + h tau mod x^W` factors through
`tau mod x^W`; if `d >= W-1` the reduction `V -> { z mod x^W : v(z) >= 1 }` is
onto with kernel `span{ x^j : W <= j <= d }` of dimension `d - W + 1`, so
`dim T_h = dim K + (d - W + 1)`.  At `d = ell-1` and `W = ell+1-v` this reads
`d - W + 1 = v - 1 >= 0`.  QED

*(EVIDENCE: `acb_gr_orbit_profile` computes the stabiliser by brute force and
asserts the closed form on every shift of every row `ell = 4..13`, aborting on
the first mismatch: 0 mismatches on 20 rows.  At `ell = 9, d = 8` the dimension
histogram is `2:128, 4:64, 6:56, 7:6, 8:1`, exactly reproduced by part (3).)*

**Lemma 2.30 (forced square divisibility).  PROVED.**
Let `lambda_1(f) := f(1)` and `lambda_2(f) := f'(1)` (formal derivative), both
`F_2`-linear in the coefficient vector.  If `(lambda_1, lambda_2) : T_h -> F_2^2`
is surjective, then every fibre `F` of that shift contains exactly `|F|/4`
polynomials divisible by `(x+1)^2`, each of which has `mob = 0`; consequently `F`
is not zero-free and `|c_F| <= (3/4) |F|`.

*Proof.*  Over `F_2`, `(x+1)^2 | f` iff `1` is a root of `f` of multiplicity at
least `2`, iff `f(1) = 0` and `f'(1) = 0` (if `f = (x+1)^m g` with `g(1) != 0`,
then `f' = m (x+1)^(m-1) g + (x+1)^m g'`, so `f'(1) = g(1) != 0` when `m = 1` and
`f'(1) = 0` when `m >= 2`).  Both `lambda_i` are `F_2`-linear: `lambda_1` is the
parity of the number of nonzero coefficients, `lambda_2` the parity of the
number of nonzero coefficients at odd indices.  `F` is a coset of `T_h`
(Theorem 2.29), so `(lambda_1,lambda_2)` restricted to `F` is affine with linear
part the restriction to `T_h`; if that is surjective, all four preimages have
size `|F|/4`, in particular the preimage of `(0,0)`.  A polynomial divisible by a
square has `mob = 0`.  QED

**Lemma 2.31 (surjectivity for `v >= 2`).  PROVED.**
At the calibration `d = ell - 1` with `ell >= 4`, for every shift with
`v := v(h) >= 2`, the space `T_h` contains two consecutive powers `x^j, x^(j+1)`
with `j >= 1`, and therefore `(lambda_1, lambda_2)` is surjective on `T_h`.

*Proof.*  First, two consecutive powers do the job:
`lambda_1(x^j) = lambda_1(x^(j+1)) = 1`, while exactly one of
`lambda_2(x^j) = j mod 2` and `lambda_2(x^(j+1)) = (j+1) mod 2` is `1`.  So the
two image vectors are `(1,0)` and `(1,1)`, which span `F_2^2`.

Now the containment, from Theorem 2.29(3) with `W = ell + 1 - v`.
*Case `2v < W`, i.e. `3v < ell+1`.*  Then `T_h` contains every `tau in V` with
`v(tau) >= W - v = ell + 1 - 2v` (case *(beta)*), i.e.
`span{ x^j : max(1, ell+1-2v) <= j <= ell-1 }`.  Its dimension is at least
`min(2v - 1, ell - 1) >= 3` for `v >= 2, ell >= 4`, and the powers are
consecutive.
*Case `2v >= W`.*  Then `T_h` contains every `tau in V` with
`v(tau) >= ceil(W/2) = ceil((ell+1-v)/2)`, i.e.
`span{ x^j : ceil((ell+1-v)/2) <= j <= ell-1 }`, of dimension
`ell - ceil((ell+1-v)/2)`.  For `v >= 2` this is at least
`ell - ceil((ell-1)/2) >= 2` for `ell >= 3`, and again the powers are
consecutive.  QED

**Corollary 2.32.  PROVED.**
At `d = ell-1`, `ell >= 4`: no fibre of a shift with `v(h) >= 2` is zero-free,
and every such fibre satisfies `|c_F| <= (3/4) 2^(n_F)`.  In particular a
"Gauss-sum value" `+- 2^(n_F)` is impossible for those shifts.

*(EVIDENCE, and the reason this matters.  The census `acb_gr_fibre_census`
checks Lemma 2.30 as an assertion on every fibre of dimension `>= 4` over 22
rows: **0 violations**, and the global count of square-divisible points is
exactly `N_points/4` on every row.  It also shows that all zero-free fibres over
all 22 rows have dimension exactly `2` and bilinear rank `0`, so the rank/Arf
stratification of this family has exactly one nonempty and entirely degenerate
stratum.  That is what kills the "`c_F` is a quadratic-form Gauss sum" program
`(GR-2)`--`(GR-4)` of diary 03; see section 6.)*

**Proposition 2.33 (lossless completion).  PROVED.**
At `d = ell - 1`, admissibility (`deg delta_h <= d`) is a single `F_2`-linear
condition of index two, namely the vanishing of the coefficient of `x^ell` in
`delta_h`.  Writing `b_h(f)` for that coefficient,

```text
  2 Delta  =  A + B ,
  A  :=  sum_( h != 0, deg h <= d )  sum_( f in Dom_k )                mob(f) mob(f+h) ,
  B  :=  sum_( h != 0, deg h <= d )  sum_( f in Dom_k ) (-1)^(b_h(f))  mob(f) mob(f+h) .
```

*Proof.*  `1[b = 0] = (1 + (-1)^b)/2` for `b in F_2`.  Multiply by
`mob(f) mob(f+h)` and sum over all `f in Dom_k` and all nonzero `h` of degree
`<= d`; the left side is `sum_F c_F` summed over shifts, which is `Delta`.
Since `delta_h` is constant on `T_h`-orbits (Theorem 2.29), so is `b_h`, and the
identity holds simultaneously at orbit level and at point level.  QED

*Reading.*  `A` is the **unrestricted** binary Moebius autocorrelation summed
over the shift range: the object of Chowla's conjecture for `F_2[x]`.  So the
Burgess-style completion that the earlier diaries hoped to use costs *nothing* --
but the object it completes to is a fixed-field (`q = 2`) Chowla sum, which the
published literature reaches only in the large-`q` limit (section 4).  Moreover
`sum_h |A_h| / 2^((k+d+1)/2)` grows like `2^((ell-4)/2)` (EVIDENCE, `5.4, 7.2,
10.7, 16.6, 23.3` for `ell = 9..13`), so cancellation **across** shifts is
mandatory beyond any per-shift result.

**Model 2.34 (the Euler-product diagonal).  EVIDENCE + heuristic, NOT PROVED.**
Heuristically, for a fixed shift `h`, the density in `Dom_k` of `f` with both `f`
and `f + h` squarefree is `prod_(p != x) b_p(h)` with

```text
  b_p(h)  =  1 - 2 |p|^(-2)     if p^2 does not divide h ,
  b_p(h)  =  1 - |p|^(-2)       if p^2 divides h ,
```

(the two conditions `p^2 | f` and `p^2 | f+h` are disjoint in the first case and
identical in the second).  Averaging over `h` with `Prob[p^2 | h] = |p|^(-2)`
gives `E_h[b_p] = (1 - |p|^(-2))^2`, hence a predicted mean density

```text
  prod_(p != x) ( 1 - |p|^(-2) )^2  =  ( (1/zeta_A(2)) / (1 - 1/4) )^2
                                    =  ( (1/2)/(3/4) )^2  =  4/9 ,
```

so `2 N_sf / N_points -> 8/9 = 0.8889`.  Measured: `0.8888 +- 0.0002` for
`ell >= 12` over 22 rows, and the two shift strata separate exactly as predicted
(`(x+1)^2` not dividing `h`: `0.3951`; dividing: `0.5923`; ratio `0.667`, against
the predicted `(1-2/4)/(1-1/4) = 2/3`).

**What is actually proved here** is only the `p = x + 1` factor, and exactly:
by Lemmas 2.30-2.31 the count of square-divisible points is exactly
`N_points/4` on every measured row.  The full Euler product would require (i) an
independence/sieve argument across all `p` and (ii) the equidistribution
sub-lemma "each square-divisibility condition has its full density on the
*admissible* set of each shift".  Neither is proved in this artifact.  The
consequence recorded here is only diagnostic: **the plateau at `0.889` that
earlier diaries read as evidence for `(E2')` is a forced diagonal, not a
cancellation phenomenon**, and the genuine off-diagonal `Theta` satisfies
`|Theta|/N_points <= 0.0035` for `ell >= 12` (EVIDENCE).

### 2.7  Two blindness lemmas

**Lemma 2.35 (weight-blindness; "Lemma WB").  PROVED, exact, unconditional.**
Let `G` be any finite abelian group, `M = |G|`, and for `a : Ghat -> C` put
`f_a(e) = sum_chi a_chi chi(e)`.  Normalize `||f||_p^p := E_(e in G) |f(e)|^p`.
Then

```text
   sup_( a != 0 )   || f_a ||_4 / || f_a ||_2   =   M^(1/4) ,
```

and the supremum is attained at `a = 1` (constant), where `f_a = M * 1_{e = 1}`
is a point mass.

*Proof.*  *Upper bound.*  `||f||_4^4 = E|f|^4 <= ||f||_inf^2 E|f|^2 =
||f||_inf^2 ||f||_2^2`.  By the triangle inequality and Cauchy--Schwarz,
`||f||_inf <= sum_chi |a_chi| <= M^(1/2) ( sum_chi |a_chi|^2 )^(1/2)`, and
Parseval in this normalization is `||f||_2^2 = sum_chi |a_chi|^2`.  Hence
`||f||_inf <= M^(1/2) ||f||_2` and `||f||_4^4 <= M ||f||_2^4`.
*Attainment.*  With `a = 1`, `f(e) = sum_chi chi(e) = M 1[e = 1]`, so
`||f||_2^2 = M^2/M = M` and `||f||_4^4 = M^4/M = M^3`, giving
`||f||_4/||f||_2 = (M^3)^(1/4)/M^(1/2) = M^(1/4)`.  QED

*(Equality in the Cauchy--Schwarz step forces `|a_chi|` to be constant, so the
extremizers are exactly the constant-modulus spectra whose `f_a` is supported
where `|f_a| = ||f_a||_inf`.)*

**Why this closes an entire family of routes.**  In our normalization
`R_0 = ( ||D||_4 / ||D||_2 )^4` with `M = 2^ell`, so Lemma 2.35 says
`sup R_0 = 2^ell` -- exactly the trivial bound.  Therefore **every inequality
whose hypothesis constrains only the *support* of the spectrum, or is uniform
over coefficient vectors, returns exactly the trivial bound for a full-support
family such as ours**.  That single statement subsumes the finite-field
restriction/Salem family, additive-energy-of-a-set bounds, and Rudin's
`Lambda(4)` theory as routes to `(W4-exact)`; the positive content is that any
proof must consume an arithmetic property of the *specific* vector `(S_chi)` --
which is what (I1), the conductor filtration, and (SUP-L) are.

**Theorem 2.36 (characteristic-free singular-locus bound; "Lemma SL").
PROVED for `m = 3`.  For `m >= 4` -- the only case this project uses -- the
argument has a GAP, exhibited below, and the statement is NOT claimed.**
Let `k` be algebraically closed of **any** characteristic, `m >= 3`, `n >= 4`,
`1 <= h <= n-3`, `s := n - h - 2`.  In the Hast--Matei incidence variety
`Y_(m,n,h)` (with `Z_w` the fibre of prescribed truncated coefficients, `T_s` the
locus of root tuples with at most `s` distinct entries, and
`delta := dim(T_s cap Z_w)`),

```text
  dim Sing( Y_(m,n,h) )  <=  max{  s + (m-2)(h+1) ,   s + 2 delta + (m-3)(h+1)  } .
```

In particular `codim Sing( X_(m,n,h) ) >= 2h + 3` whenever `2 delta <= h + 1`,
with no hypothesis on the characteristic.

*Proof.*  The rows of the Jacobian `J_(m,n,h)` are indexed by `(iota, j)`,
`2 <= iota <= m`, `1 <= j <= n-h-1`; row `(iota, j)` is `row_j A_1` in the
`z_1`-columns and `- row_j A_iota` in the `z_iota`-columns.  A linear dependency
with coefficient vectors `v_iota` satisfies

```text
  v_iota^T A_iota = 0  for each iota ,        ( sum_iota v_iota )^T A_1 = 0 .
```

Let `V := { iota : v_iota != 0 }` and `u := sum_(iota in V) v_iota`.  For each
`iota in V`, `A_iota` has a nonzero left kernel, so by Hast--Matei Corollary 2.4
(characteristic-free) the tuple `z_iota` has at most `n-h-2 = s` distinct
entries.  Three exhaustive cases:

* `|V| = 1`, say `V = {iota}`.  Then `u = v_iota` annihilates both `A_1` and
  `A_iota`, so `v_iota` lies in the left kernel of the concatenation
  `[A_1 | A_iota]`; the rank criterion in the proof of Hast--Matei Proposition 2.5
  (characteristic-free) then forces `#( z_1 union z_iota ) <= s`.
* `u = 0` and `|V| = 2`, say `V = {iota, iota'}`.  Then `v_iota` annihilates both
  `A_iota` and `A_(iota')`, so `#( z_iota union z_(iota') ) <= s`.
* `u != 0` with `|V| >= 2`: then `u^T A_1 = 0` with `u != 0` forces
  `z_1 in T_s`, and at least two further tuples lie in `T_s`, so **three** of the
  `m` tuples lie in `T_s` and `z_1` is one of them.
* `u = 0` with `|V| >= 3`: at least three of `z_2, ..., z_m` lie in `T_s`, and
  the condition on `A_1` is **vacuous**, so `z_1` is unconstrained.

In the first two cases some **pair** of tuples has root union of size `<= s`.
The locus of such pairs has dimension `<= s` in any characteristic: the union is
a point of the `s`-th symmetric power (dimension `s`), and each of the two tuples
is then one of finitely many multiplicity assignments on that support.  The
remaining `m-2` coordinates are free in `Z_w`, of dimension `h+1` each, giving
`s + (m-2)(h+1)`.  In the third case, fix `z_1 in T_s` (dimension `<= s`); the
other two constrained tuples lie in `T_s cap Z_w`, of dimension `<= delta` each;
the remaining `m-3` are free, giving `s + 2 delta + (m-3)(h+1)`.

**The fourth case is where the argument stops.**  With `z_1` unconstrained its
contribution is `n`, not `s`, and three of `z_2..z_m` lie in `T_s cap Z_(z_1)`,
so the component has dimension at most `n + 3 delta + (m-4)(h+1)`.  Subtracting
from `dim Y = n + (m-1)(h+1)` gives only

```text
  codim  >=  3 (h+1)  -  3 delta ,     which is >= 2h+3  iff  h >= 3 delta ,
```

**not** the advertised `2 delta <= h+1`.  For `m = 3` the case cannot arise
(`V subset {2,3}`, so `|V| <= 2`) and the proof is complete, giving the stated
bound and `codim >= 2h+3` under `2 delta <= h+1`.  For `m >= 4` it can, and no
argument is given here that the component is smaller.  QED **for `m = 3` only.**

**Scope, stated exactly.**
* The proof never mentions the characteristic and never uses Hast--Matei's
  Lemma 2.6 (their tameness lemma), which is therefore *avoidable*, not merely
  repairable.  At `delta = 0` it recovers their Theorem 2.7, and at `m = 3` it is
  complete.
* **GAP at `m >= 4`, and it bites exactly where this project needs it.**  The
  missing component needs `h >= 3 delta`.  At the odd endpoint `h = ell` and
  diary 12's own proved lower bound `delta >= ceil(ell/2) - 2` give
  `3 delta >= 1.5 ell - 6 > ell` for every `ell >= 13`, so the hypothesis
  `2 delta <= h+1` (which *is* satisfied there, `ell - 4 <= ell + 1`) does not
  cover it.  `m = 4` is the only case this project uses.  This gap was found by
  the phase-3 verifier (`20-verify-chains.md`, entry 23) after diary 12 had
  labelled the lemma PROVED; this artifact does not carry that label at `m >= 4`.
  It is a GAP and not a refutation -- the dimension count is an upper bound and
  the component may well be smaller -- but no argument for that exists here.
* **OPEN(bk):** separately, the argument uses that the root-union criterion of
  Hast--Matei Proposition 2.5, stated for `[A_1 | A_2]`, applies verbatim to
  `[A_iota | A_(iota')]` for `iota, iota' >= 2`.  It does, since the two blocks
  are structurally identical and the defining equations force equal `e_j` for
  `j <= n-h-1` between any two tuples; but this is not written out here.
* **The hypothesis `2 delta <= h+1` is satisfied at our endpoints from published
  literature** (Sawin, arXiv:1809.05137, Lemma 2.3, giving
  `delta <= floor(n/2) - floor(t/2)` at `p = 2` with `t = n-h-1`): at the odd
  endpoint for every `ell`, at the even endpoint for even `ell`, and short by one
  unit at the even endpoint for odd `ell`.
* **Even if the `m >= 4` gap were closed, it would buy nothing at `q = 2`**, and
  this is important enough to state
  here rather than only in section 6.  Even granting Theorem 2.36 and hence
  Hast--Matei Theorem 1.4 at `p = 2, m = 4`, the resulting bound is
  `E_e[D_e^4] <= C_(4,n,h) 2^(3(h+1))` with `C` ineffective and `n`-dependent,
  while `(W4-exact)` needs `C < 2` uniformly in `n`.  Every available Betti-number
  technology is exponential in the ambient dimension `4n`.  So Theorem 2.36 is a
  genuine characteristic-free improvement of a published lemma, and it is **not**
  a route to the endpoint.

---

## 3  The two open statements

Both are stated for the endpoint discrepancy `D` of section 1.3, at both
endpoint parities, and both are **open**.  All tables below are finite
computations over exact integers; the only floating point is in printed ratios.
Every table names the example program and its parameters.  A finite table is
evidence, never a theorem.

### 3.1  (SUP-L)

> **Conjecture (SUP-L).**  There is an absolute constant `K` such that for both
> endpoint degrees `n in {2 ell + 1, 2 ell + 2}`, every `ell >= 2`, and every
> conductor level `2 <= j <= ell`,
> ```text
>       max_e | D_[j](e) |   <=   K (j-1) 2^((j-1)/2) 2^(n/2) / 2^ell .
> ```

Equivalently `kappa_j <= K` with `kappa_j` as in section 2.3.  This is a
**delocalization / square-root-cancellation statement about a single conductor
layer**: the level-`j` component of `D` is not permitted to concentrate to the
full triangle bound over its `2^(j-1)` characters, only to its square root.  It
is a sup-norm statement, not a moment statement, and it has no `ell`-dependence.

By Theorem 2.16, (SUP-L) with `K = 2` implies the Lemire endpoint for every
`ell >= 22` (odd) and `ell >= 20` (even).

**Proposition 3.1 (the trivial bound, and the two levels where (SUP-L) is
already settled).  PROVED given (I1); part (b) also uses (I1').**

```text
  (a)  kappa_j  <=  2^((j-1)/2)     for every level j >= 2   (the trivial bound),
       and D_[1] = 0, so level 1 is vacuous.
  (b)  1  <=  kappa_2  <=  2^(1/2)  for every ell >= 2 and both parities.
```

*Proof.*  (a) By Fourier inversion `D_[j](e) = 2^(-ell) sum_(lev chi = j) S_chi
conj(chi(e))`, so `max_e |D_[j](e)| <= 2^(-ell) 2^(j-1) (j-1) 2^(n/2)` by (CT)
and (I1); dividing by `(j-1) 2^((j-1)/2) 2^(n/2) 2^(-ell)` gives
`kappa_j <= 2^(j-1)/2^((j-1)/2) = 2^((j-1)/2)`.  `D_[1] = 0` because `V_1 = 0`
(Theorem 2.11(a)).

(b) `G_ell/H_2` is the principal-unit group mod `t^3`, of order `4`, and
`1 + t` has order `4` in it (`(1+t)^2 = 1+t^2 != 1`), so `G_ell/H_2 ~ Z/4`.  Its
two faithful characters are the two characters of exact level `2`, and they are
complex conjugates of one another; since `D` is real, `S_(conj chi) = conj(S_chi)`.
Hence

```text
  D_[2](e)  =  2^(-ell) ( S_chi conj(chi(e)) + conj( S_chi conj(chi(e)) ) )
            =  2^(1-ell) Re( S_chi conj(chi(e)) ) .
```

`chi` takes the four values `{1, i, -1, -i}` on `G_ell`, so as `e` ranges over
`G_ell` the quantity `Re(S_chi conj(chi(e)))` takes exactly the four values
`+- Re(S_chi)`, `+- Im(S_chi)`, and

```text
  max_e |D_[2](e)|  =  2^(1-ell) max( |Re S_chi| , |Im S_chi| ) .
```

By (I1'), `|S_chi| = 2^(n/2)` exactly, and for any complex number
`|S|/2^(1/2) <= max(|Re S|,|Im S|) <= |S|`.  With `(j-1) = 1` and
`2^((j-1)/2) = 2^(1/2)` the definition of `kappa_2` gives

```text
  kappa_2 = 2^(1-ell) max(|Re S_chi|,|Im S_chi|) * 2^ell / ( 2^(1/2) 2^(n/2) )
          = 2^(1/2) * max(|Re S_chi|,|Im S_chi|) / |S_chi|   in  [1, 2^(1/2)] .
```

QED

**This is exactly what the `j = 2` row of table (E-1) below reports**
(`min = median = 1.0000`, `max = 1.4142`), so that row is a control, not
evidence.  Part (a) says that `K = 2` is *the trivial bound* at `j = 3`; see
section 6.3 for what follows from that.

**Evidence table (E-1): `kappa_j` over 341 (row, level) pairs.**
Source: `crates/axeyum-cas/examples/acb_cab_levels.rs`, subcommand `layers`,
`ell = 6..20`, both endpoint parities `n in {2ell+1, 2ell+2}`, every level
`2 <= j <= ell`.  Runs: `acb_cab_levels sweep 4 14` (1.1 s),
`sweep 15 18` (32.3 s), `sweep 19 20` (2m08, peak RSS < 700 MB).
Values of `kappa_j` grouped by level:

```text
   j   rows      min   median      max
   2     29   1.0000   1.0000   1.4142
   4     29   0.4677   0.9428   1.8994
   6     29   0.5625   0.9899   1.3562
   8     25   0.7678   1.0625   1.4601
  10     21   0.7482   1.0754   1.3581
  12     17   1.0051   1.1284   1.5146
  14     13   0.9655   1.0944   1.2281
  16      9   0.9987   1.0767   1.2478
  18      5   1.0575   1.1096   1.1741
  20      1   1.1049   1.1049   1.1049
  ---------------------------------------------------------------
  global max over all 341 pairs: 2.0000    (attained at ell=11, n=24, j=3)
  global max over j >= 6:        1.5234
```

**Range of validity of the table: `6 <= ell <= 20`, `2 <= j <= ell`, both
parities.  Nothing above `ell = 20` has been computed.**  `K = 2` covers every
measured pair.

**The table above prints even levels only, and that hides the binding row.**
By Proposition 3.1(a) the levels `j <= 3` are a-priori bounded by `2` -- so the
`2.0000` maximum, attained at `(ell,n,j) = (11,24,3)`, is the *ceiling being
attained*, not a measurement about the open regime.  The maximum over the levels
where `K = 2` is an open statement, `j >= 4`, is the number that matters:

**Evidence table (E-1b): `max_(j >= 4) kappa_j`, all levels including odd `j`.**
Source: the phase-3 verifier `20-verify-chains.md`, program `acb_ver_supl`
(an independent reimplementation, cross-validated against a sympy engine).
Range `5 <= ell <= 12`, both parities -- smaller than table (E-1)'s range, but
it is the only table that includes odd `j`.

```text
 (ell,n)     max_j kappa_j    max_(j>=4) kappa_j     attained at j
  (5,12)        1.8750             1.8750                 5
  (6,14)        1.5321             1.5321                 4
  (8,18)        1.5000             1.3637                 8
  (10,22)       1.7825             1.7825                 4
  (11,23)       1.1500             1.1500                 6
  (11,24)       2.0000             1.9922                 5
  (12,25)       1.1186             1.1186                12
  (12,26)       1.5234             1.5234                 9
```

So on the **open** part of the statement the largest measured value is
`1.9922`, at `(11,24)`, `j = 5`: a margin of **0.4%** below `K = 2`.  Diary 11's
"`K = 2` fits all measured data with a 31% margin" is `2/1.5234`, the margin over
`j >= 6` only; levels `j = 4, 5` are in neither the printed table nor that
statement, and `j = 5` is where the open-regime maximum sits.  **There is no
measured margin worth quoting for (SUP-L) with `K = 2`.**

**Evidence table (E-2): the reductions of section 2.3, measured.**
Same program.  `closure` values are the left side of each reduction divided by
the strict diary-04 budget `2^ell (mu - P_n)^4 - 3 M_2^2` (for `A_L`) or
`(mu - P_n)^4` (for the others), with `P_n` from Lemmas 2.1/2.2; `inf` marks
rows below the even-endpoint (WK) crossover `ell = 13`, where the budget is
negative and nothing can close; `n/t` means the row was not tabulated in the
phase-2 sweep.

```text
  quantity                          ell:  6      8     10     12     14     16     18     20
  A_L / budget            (odd)      0.0387 0.0383 0.0107 0.0025 0.0004 8e-05  2e-05  2e-06
  A_L / budget            (even)      n/t    inf    n/t   0.0022 0.0003 3e-05  5e-06  1e-06
  R_L + 6 M_2^2 / budget  (odd)      0.1801 0.1877 0.0963 0.0363 0.0132 0.0046 0.0015 0.00047
  R_L + 6 M_2^2 / budget  (even)     0.1015 0.0995 0.0276 0.0100 0.0034 0.0011 0.00037 0.00012
  sum_e U^4 / budget      (odd)      0.2955 0.4311 0.2153 0.1005 0.0388 0.0144 0.0048 0.00156
  sum_e U^4 / budget      (even)      inf    inf   0.6901 0.0870 0.0192 0.0051 0.0014 0.00044
  sum_j ||D_[j]||_4 / (mu-P_n) (odd) 0.841  1.061  0.933  0.787  0.627  0.493  0.376  0.284
  sum_j ||D_[j]||_4 / (mu-P_n) (even) n/t   3.049  1.291  0.790  0.536  0.383  0.278  0.207
```

Reading: the *weakest* reduction in the chain, `(L4-LAYER)`, already closes from
`ell = 10` (odd) / `ell = 11` (even) on measured data, decaying like `ell^(-1.74)`
/ `ell^(-2.55)`.  The strongest, `A_L`, closes from `ell = 4` with margin growing
like `2^(+0.46 ell)`.  Notably `A_L < M_2^2` from `ell = 10`, so the
*levelwise-absolute* bound would already imply the lane's **strong** aggregate
target `K_4 <= M_2^2`, while discarding all cross-conductor cancellation.

**Cross-validation.**  All conductor-level machinery, including `A_L` itself and
the zero-cell counts predicted by Theorem 2.10, was reproduced at `(4,9)`,
`(4,10)`, `(5,11)`, `(5,12)` by an independent sympy brute force over
`GF(2)[x]` that enumerates every monic polynomial of degree `n`, factors it, and
computes the conductor projections by direct averaging over each subgroup `H_j`
(no sibling recursion).  All fields agree exactly.

**What would falsify it.**  A single `kappa_j > 4` at large `j` moves the
crossover of Theorem 2.16 by three levels; a `kappa_j` growing in `j` (say like
`j^(1/2)` or `2^(j/4)`) kills the reduction outright, since the chain integrates
`kappa_j^(1/2)` against `2^((j-1)/2)`.  The cheapest decisive experiment is
`kappa_j` at `ell = 21..24` for large `j`, which needs no cell tensor and is
`O(ell 2^ell)`.

### 3.2  (CDL)

> **Conjecture (CDL).**  There is an absolute constant `c` such that for all
> large `ell` and both endpoint parities,
> ```text
>    sum_( chi : lev(chi) = j )  | sum_e D_e^2 chi(e) |^2   <=   M_2^2 / ell
> ```
> for every conductor level `j <= c log2 ell`.  Equivalently `q_j <= 1/ell` for
> those levels.

By Proposition 2.22 with `c >= 4.1`, (CDL) implies `(W4-exact)`, hence the
Lemire endpoint at both parities, for all `ell >= 200` -- the range below being
the lane's separately certified finite range.

A sufficient pointwise form, since there are `2^(j-1) <= ell^c / 2` characters at
level `j <= c log2 ell`:

```text
  | sum_e D_e^2 chi(e) |  <=  M_2 * ell^(-(c+2)/2)   for every chi of level <= c log2 ell.
```

**And that is a shifted second moment, not a fourth moment.**  By Fourier
inversion on `G_ell`, squaring, summing against `chi`, using orthogonality, and
`S_(psi^(-1)) = conj(S_psi)` (valid since `D` is real):

```text
  fhat(chi) = sum_e D_e^2 chi(e) = 2^(-ell) sum_psi S_psi conj( S_(psi chi^(-1)) ) .
                                                                             (TWIST)
```

At `chi = 1` the two sides are equal to `2^ell M_2` and there is no content; the
content of (CDL) is `poly(ell)` decorrelation of the Hayes character-sum family
under a *fixed low-conductor twist*.  (The inverse in `psi chi^(-1)` is not
cosmetic bookkeeping to be dropped: diary 13 printed `psi chi`, which is a
different pairing of the family, although `|fhat(chi)|` is unaffected because
the sum runs over all `psi`.  Independently caught by `20-verify-chains.md`,
entry 19.)  The unshifted case is exactly the Weil
envelope of Corollary 1.2 (equivalently Keating--Rudnick's variance); the shifted
case is the same *kind* of object -- a second moment of a family of `L`-functions
over a function field -- and not a fourth moment.  That is the whole point of
routing through (D-PROD).

**Evidence table (E-3): `q_j` at fixed low levels, odd endpoint.**
Source: `crates/axeyum-cas/examples/acb_dic_profile.rs`,
runs `acb_dic_profile 2 16` (6.9 s, 24.8 MB) and `acb_dic_profile 17 19`
(70.1 s, 180.5 MB); 36 rows `ell = 2..19`, both parities; the odd rows shown.

```text
 ell      q_2        q_4        q_6        q_8       q_10     ell * q_8
  11   9.90e-04   6.26e-03   3.20e-02   1.27e-01   3.25e-01    1.40
  13   2.63e-05   1.94e-03   9.36e-03   2.90e-02   1.02e-01    0.377
  15   6.05e-05   2.74e-04   2.17e-03   8.69e-03   3.09e-02    0.130
  17   1.02e-05   1.84e-04   6.26e-04   2.40e-03   8.74e-03    0.041
  19   4.33e-07   5.74e-06   8.74e-05   4.73e-04   1.81e-03    0.0090
```

**Range of validity: `2 <= ell <= 19`, both parities.**  `ell q_8` falls by a
factor `~2` per unit `ell`, i.e. `q_j` at a *fixed* level decays like `2^(-ell)`
against a requirement of `1/ell`: the measured margin for (CDL) is
`2^ell / ell^(c+1)` and **growing**.

**Evidence table (E-4): the imbalance profile.**
The full profile obeys a clean geometric law.  At `(ell,n) = (19,39)` the
normalized column `q_j 2^(ell-j)` reads

```text
 j          8      9     10     11     12     13     14     15     16     17     18     19
 q 2^(l-j)  0.969  1.098  0.929  1.071  1.063  0.953  1.010  0.974  0.878  0.812  0.664  0.497
```

so `q_j = (1 + o(1)) 2^(-(ell-j))` to within 10 percent over eleven levels, and
`q_ell in [0.481, 0.508]` on every odd row `ell = 9..19`.  Consequently
`sum_j q_j` is an absolute constant (`1.24` to `1.28` over `ell = 11..19`, both
parities), and `prod_j (1 + q_j) -> 3`: the Gaussian kurtosis is exactly the
value of the `q`-product for a geometric imbalance profile of ratio `2`.

**Evidence table (E-5): where the `L^2` mass of `D` lives.**
The exact fraction of `||D||_2^2` measurable at conductor codimension `<= j` is
`A_j / (2^(ell-j) M_2)` with `A_j := sum_b s_j(b)^2`, `s_j(b) := sum_(e in b H_j) D_e`.
At `(19,39)` it matches the exact-conductor law `(j-2)/(ell-2) * 2^(j-ell)` to
three digits over eighteen levels:

```text
 j            10        13        15        16        17        18        19
 measured  9.06e-4   9.95e-3   4.79e-2   1.033e-1  2.206e-1  4.725e-1  1.000
 law       9.19e-4   9.56e-3   4.78e-2   1.029e-1  2.206e-1  4.706e-1  1.000
```

Half the mass sits at the single top conductor level, a quarter one below, and
only `0.46%` lies at or below the proved Weil cutoff.  This is a *quantitative*
form of the standing top-conductor obligation, and it is why (CDL) -- which lives
at the **bottom** of the filtration -- is a genuinely different kind of
hypothesis.

**Cross-validation.**  An independent sympy brute force
(`dic_sympy_check.py`, phase 2) that enumerates every monic polynomial of degree
`n`, factors it over `GF(2)`, and rebuilds `D`, `M_2`, `M_4`, the cylinders keyed
by *polynomial truncation* (a basis-free key), `C_j`, `A_j`, `q_j` and
`max_b m_j(b)` reproduces every field exactly at `(4,9)`, `(4,10)`, `(5,11)`,
`(5,12)`.

**What would falsify it.**  A single low level `j` with `q_j` not decaying in
`ell`; or a proof that `fhat(chi)` is large for some fixed low-conductor `chi`.
Note Theorem 2.23 proves `q_1 = 0` at odd endpoints, so the first level is free.

### 3.3  Relation between the two

They are **incomparable**, deliberately.

```text
                      grading           end of it   object          needs cancellation?
 (SUP-L)     conductor filtration       every level  D_[j]           within a layer
 (CDL)       conductor filtration       BOTTOM       fhat = S * S    within a twist
```

(SUP-L) is a sup-norm statement about the `D`-spectrum, layer by layer, and asks
for square-root cancellation *in the character count*.  (CDL) is an `L^2`
statement about the `D^2`-spectrum at `poly(ell)` many low-conductor twists, and
asks for `poly(ell)` decorrelation of a shifted second moment.  Neither implies
the other.  (SUP-L) is a stronger *conclusion* (it bounds `M_4` outright);
(CDL) is a smaller *hypothesis* reaching the same endpoint through (D-PROD).
Their measured margins are of different shapes: (SUP-L)'s measured maximum sits
`0.4%` below `K = 2` on the open levels (table (E-1b)), while (CDL)'s margin
grows like `2^ell / ell^(c+1)`.

Two natural bridges between them were tested by the phase-3 verifier
(`20-verify-chains.md`, entries 28 and 29) and **REFUTED**, with witnesses:
"`q_j <= 1` implies (SUP-L) at some levels" fails with an exponential deficit
`~ ell 2^(ell/2)/(j-1)` (measured `208x` at `j = 2`, still `3.3x` at `j = ell`,
at `(11,24)`); and the best layer-to-`E_j` transfer between the two is *worse
than trivial*, because they are statements about different functions -- the
`D`-spectrum and the `D^2`-spectrum.  So the incomparability is not a
presentational choice; it is measured.

---

## 4  Related work

Every citation below was fetched and read (or, where marked, only its abstract
was fetched) during phases 1-3 of this project; none is quoted from memory.
Statements attributed to a paper are what that paper actually proves.

### 4.1  Directly comparable: higher moments in function-field short intervals

* **D. Hast, V. Matei, *Higher moments of arithmetic functions in short
  intervals: a geometric perspective*, arXiv:1604.02067**
  (<https://arxiv.org/abs/1604.02067>).  The nearest theorem in form.  Their
  Theorem 1.4 at `m = 4` is, up to the constant, exactly `(W4-exact)`.  It
  carries the hypothesis "`p > n` if `m > 2`" -- tame ramification -- which fails
  at `p = 2` for every `ell`, and their own Remark 1.5 names the missing input
  (the `S_n^m`-action on cohomology in uncomputed ranges).  Their Theorem 2.7 is
  the statement that Theorem 2.36 above replaces characteristic-freely.  Their
  asymptotics are in the `q -> infinity` limit.
* **J. Keating, Z. Rudnick**, the variance of arithmetic functions in short
  intervals over `F_q[t]` via Katz equidistribution.  The *second* moment is
  known; it is the source of the `M_2 -> (ell-1) 2^n` normalization that the
  measured data of section 3 approaches.  Fourth moments are not available at
  fixed `q`.
* **C. Yiasemides, *The Variance and Correlations of the Divisor Function in
  `F_q[T]`, and Hankel Matrices*, arXiv:2110.05959**
  (<https://arxiv.org/abs/2110.05959>).  The only exact-moment technology found
  that is native to fixed `q` (including `q = 2`), reducing moments to ranks of
  Hankel matrices over `F_q` by additive-character orthogonality.  It computes
  the *second* moment of the divisor function, not a fourth moment and not
  primes; both extensions are listed by the author as undone.  Rated in diary 02
  as the highest-value unexplored import.
* **Z. Gao, S. Kuttner, Q. Wang, *Counting irreducible polynomials with
  prescribed coefficients over a finite field*, arXiv:2109.02000**;
  **Z. Gao, *Improved error bounds ...*, arXiv:2109.14154**
  (<https://arxiv.org/abs/2109.02000>, <https://arxiv.org/abs/2109.14154>).
  The direct predecessors of the endpoint problem.  At `q = 2` and
  `ell = ceil(n/2) - 1` their main term and published absolute error are of the
  same exponential order, so they do not prove positivity at the endpoint; the
  second paper explicitly works where "the number of prescribed leading
  coefficients is slightly less than `d/2`".

### 4.2  Moebius autocorrelation at fixed `q` (section 2.6)

* **D. Carmon, *The autocorrelation of the Moebius function and Chowla's
  conjecture for the rational function field in characteristic 2*,
  arXiv:1409.3694** (<https://arxiv.org/abs/1409.3694>).  Theorem 1.1, verbatim:
  for `r > 1`, `n > 2`, `q` even, distinct `alpha_1..alpha_r` of degree `< n` and
  `eps_i in {1,2}` not all even,
  `|C(alpha_1,...,alpha_r; n)| <= r n q^(n-1/2) + (3/4)(r+3) n^2 q^(n-1)`.
  This is exactly the object `A` of Proposition 2.33, **and it is vacuous at
  `q = 2`**: the bound exceeds the trivial `q^n` once `q < (rn)^2`, and our
  regime is `q = 2` fixed with `n -> infinity`.  The theorem's limit is
  `q -> infinity` with `n` fixed, the opposite corner.
* **D. Carmon, Z. Rudnick, arXiv:1205.1599** -- same corner, any characteristic.
* **W. Sawin, M. Shusterman, *On the Chowla and twin primes conjectures over
  `F_q[T]`*, arXiv:1808.04001** (<https://arxiv.org/abs/1808.04001>).  Abstract
  fetched; it states the results hold "for finite fields satisfying a simple
  condition", and **the condition is not in the abstract**.  Whether it admits
  `q = 2` is **UNVERIFIED** here (re-checked during phase 3; still unverified).
  Do not cite it in either direction.
* **P. Kurlberg, L. Rosenzweig, *Prime and Moebius correlations for very short
  intervals in `F_q[x]`*, arXiv:1802.01215**
  (<https://arxiv.org/abs/1802.01215>).  Abstract fetched.  Two regimes, both
  with `q -> infinity`.  They also construct counterexamples exhibiting **no
  cancellation at all** in Moebius/Chowla-type sums on certain short intervals --
  directly relevant, since `A` is short-interval-shaped (`deg h <= d = ell-1`
  against `deg f = k`).

### 4.3  Hypercontractivity and global hypercontractivity (why the analytic route closes)

* **R. O'Donnell, *Analysis of Boolean Functions*, CUP 2014 / arXiv edition
  <https://arxiv.org/abs/2105.10386>, Chapter 10.**  Theorem 10.18 gives the
  sharp per-coordinate Latala--Oleszkiewicz/Wolff constant
  `rho_c(m) = sqrt( sinh(u/4)/sinh(3u/4) )`, `u = log(m-1)`, with
  `rho_c(2) = 1/sqrt3` in the limit.  Primary sources: **R. Latala,
  K. Oleszkiewicz**, GAFA Seminar Notes, Springer LNM 1745 (2000), 147-168; and
  **P. Wolff**, Studia Math. 180 (2007), 219-236 (both reached through
  O'Donnell's attribution; primary texts not fetched -- flagged).
* **Keevash, Lifshitz, Long, Minzer**, JAMS 37 (2024) 245-279,
  <https://arxiv.org/abs/1906.05568>.  Theorem 7.10 (general discrete product
  spaces via the Efron--Stein decomposition, `rho <= 1/(4 q^1.5)`) is the right
  *shape* for `G_ell` and the wrong *constant*.
* **Keller, Lifshitz, Marcus, *Sharp Hypercontractivity for Global Functions*,
  <https://arxiv.org/abs/2307.01356>.**  Theorem 1.3 and the sharp level-`d`
  Theorem 1.4.  Sharpness is in `q`, not in the absolute constant; at `q = 4`
  the noise floor `log q/(32 r q)` is *worse* than the classical `1/sqrt3`.
  Their explicit remark that on `(Z/mZ)^n` (`m` even) the tightness example is a
  junta confirms that the family is calibrated against locality, not level.
* **Green, Sawhney, *New bounds for the Furstenberg--Sarkozy theorem*,
  arXiv:2411.17448** (<https://arxiv.org/abs/2411.17448>; v2 of 10 Jan 2025
  fetched and read; the arXiv listing still shows the v1 title "Improved bounds
  for ...").  Their Theorem 1.2 is the level-inequality-or-density-increment
  dichotomy on a CRT product group, with `C_0 = 2^13`,
  `d <= 2^(-7) log(1/alpha)` and increments on progressions of density
  `2^|S| alpha`.  **It is not importable here**: our density is `alpha = 1/n`, so
  `2^(-7) log(1/alpha) < 1` for every `ell` below `e^128/2` and the admissible
  level set is empty.  The family is calibrated for sparse sets; the irreducibles
  at density `1/n` are dense on that scale.  Their Section 9 (Proposition 9.1) is
  moreover a limitation theorem for the density-increment shape in its own
  domain.  What survives, and what section 2.4 uses, is the *mechanism*: a
  dichotomy whose increment side is extracted from the failure of the level side.
  In our setting the extraction is an exact identity (Theorem 2.19) rather than a
  hypercontractive estimate, and there is no lifting loss because `G_ell` is an
  honest finite abelian product group with an exact Efron--Stein decomposition.
* Also mapped and found inapplicable (all abstracts fetched):
  Filmus--Kindler--Lifshitz--Minzer <https://arxiv.org/abs/2009.05503>,
  Keevash--Lifshitz <https://arxiv.org/abs/2307.15030>,
  Gur--Lifshitz--Liu <https://arxiv.org/abs/2111.09375>,
  Ellis--Kindler--Lifshitz <https://arxiv.org/abs/2209.04243>,
  Lifshitz--Marmor <https://arxiv.org/abs/2308.08694>.
  The non-product layer of that literature is inapplicable to us *by hypothesis*:
  their difficulty (approximate Efron--Stein decompositions) is our free
  hypothesis.

### 4.4  Support-only theories, closed by Lemma 2.35

Finite-field restriction and Salem-set theory (Mockenhaupt--Tao, Iosevich--Koh,
Lewko, Rudnev--Shkredov, Fraser); additive energy of structured sets
(Heath-Brown--Konyagin, Shkredov, Kerr--Mohammadi--Shparlinski); Sidon /
`B_2` / `Lambda(4)` harmonic analysis (Rudin, Bourgain--Lewko, Lewko--Lewko).
All of these hypothesize on the *support* of a spectrum or are uniform over
coefficient weights.  Our spectrum has full support, so by Lemma 2.35 each of
them returns exactly the trivial bound `R_0 <= 2^ell` -- not merely a lossy one.
(Lewko--Lewko's separation of the weighted `Lambda(4)` condition from the support
condition `B_2[g]` is why the correct name for the relevant hypothesis is
`Lambda(4)`, not "Sidon".)

### 4.5  `Z/2^k`-valued and Galois-ring Fourier analysis (section 2.6's dead end)

The program of reading `c_F` as a `Z/8`-valued Gauss sum with a Brown/Arf sign
was pursued in diary 03 through **L. R. Taylor, *Gauss Sums in Algebra and
Topology*** (<https://arxiv.org/abs/2208.06319>), **K.-U. Schmidt, *`Z_4`-valued
quadratic forms and quaternary sequence families*** (IEEE IT 55 (2009)),
**J. A. Wood**, and **Hammons--Kumar--Calderbank--Sloane--Sole**
(<https://arxiv.org/abs/math/0207208>).  Section 2.6 shows the program does not
apply to this family: the phase is `chi_8`-valued, not `zeta_8`-valued, so `c_F`
is a Moebius autocorrelation, and by Corollary 2.32 the alternating stratum
consists entirely of degenerate dimension-`2`, rank-`0` fibres.  The references
remain correct statements about a family that is not this one.

### 4.6  What was searched for and not found

A priority search for prior art on the headline construction was attempted in
phase 3.  The `WebSearch` budget for the session was already exhausted (200 of
200 calls) before this workstream began, so the search was performed instead
through the arXiv API.  Queries run and their results:

```text
  all:"conductor filtration" AND all:"character sums"                  -> 0 entries
  abs:"conductor" AND abs:"equidistribution" AND abs:"Dirichlet
      characters" AND abs:"function field"                             -> 0 entries
  all:"conductor" AND abs:"Hayes" AND abs:"character sums"             -> 0 entries
  abs:"dyadic martingale" AND abs:"fourth moment"                      -> 0 entries
  abs:"short interval" AND abs:"fourth moment" AND abs:"function field" -> 1 entry
                                                       (Yiasemides, 2110.05959)
  abs:"von Mangoldt" AND abs:"short intervals" AND abs:"function field" -> 2 entries
                                        (Kuperberg-Lalin 2107.01437; Hast-Matei)
  abs:"Chowla" AND abs:"function field"                                -> 10 entries,
                                        all large-q or unspecified regimes
  abs:"irreducible polynomials" AND abs:"prescribed coefficients"      -> 5 entries,
                                        Gao et al. the only endpoint-relevant ones
```

**This is a weak negative and is labelled as such.**  arXiv abstract search is
phrase-sensitive, does not cover journals-only work, and the terminology of an
independent rediscovery could differ entirely.  See section 6 for what may and
may not be concluded from it.

---

## 5  Appendix: export targets for kernel admission

The following are the results of section 2 restated in a form suitable for
admission into the Axeyum kernel: **finite, algebraic, and either
quantifier-free at fixed parameters or bounded-quantified**.  Nothing here
requires (I1), (I1') or (I2); the analytic input is confined to the statements
that are *not* exported.  **No Lean was run for this artifact.**  Each entry
states what a Lean verification of the exported artifact would actually check.

**(X1) Conductor orthogonality at fixed `ell`.**

```text
  Parameters: ell in N.
  Data:       D : Fin (2^ell) -> Int  with  sum_e D e = 0.
  Definitions: R_ell := D ;  R_(j-1) e := R_j e + R_j (e * g_j) ;
               A_j e := R_j e - R_j (e * g_j) ;  D_[j] := A_j  (unnormalized).
  Claim:      forall j k, j != k -> sum_e (A_j e) * (A_k e) = 0.
```

For each fixed `ell` this is a family of `C(ell,2)` polynomial identities in
`2^ell` integer variables.  *Lean would check:* a `ring`-normalizable identity
after unfolding the recursion, or -- better -- the general statement, whose only
content is that `A_j` and `A_k` are supported on disjoint character sets.  The
general form is worth exporting as a lemma about any finite abelian `2`-group
with a chain of subgroups, and is not specific to `F_2[x]`.

**(X2) The parity selection rule at fixed `ell`.**

```text
  Parameters: ell in N, a multiset (j1,j2,j3,j4) of levels in [1, ell].
  Hypothesis: card { i : j_i = max j } is odd.
  Claim:      2^ell * sum_e prod_i (D_[j_i] e)  -  (three Wick pairings)  =  0.
```

Quantifier-free at fixed `(ell, j1..j4)`; `C(ell+2,4)`-many instances per `ell`.
*Lean would check:* the algebraic identity.  The clean exportable core is the
group-theoretic fact behind it: **if `chi_1 chi_2 chi_3 chi_4 = 1` and each
`chi_i` restricted to a subgroup `H` is either trivial or equal to a fixed
order-`2` character `eps`, then the number of `i` with `chi_i|_H = eps` is
even.**  That is a two-line lemma about characters and is characteristic-free.

**(X3) `E_1 = 0` at odd endpoints -- the general involution lemma.**

```text
  Parameters: a finite type A, an involution s : A -> A,
              f : A -> Int, g : A -> Int.
  Hypotheses: forall a, f (s a) = f a ;   forall a, g (s a) = - g a.
  Claim:      sum a, f a * g a = 0.
```

This is the exportable core of Theorem 2.23, fully general and with no
arithmetic in it.  The instance is `A = G_ell`, `f = D^2`, `g = chi_1`, `s` the
translation involution.  *Lean would check:* the general lemma (a two-line
`Finset.sum_involution` argument), plus, at fixed `ell` and odd `n`, the two
hypotheses as decidable finite facts about the explicit coefficient transform
`a'_j = sum_(i<=j) a_i C(n-i, j-i) mod 2`.  Verifying the *arithmetic*
hypothesis `D(s e) = D(e)` from first principles would require formalizing the
`Lambda`-preserving bijection `F(x) -> F(x+1)`; a cheaper honest route is to
check it as a finite computation for each `ell` in a bounded range.

**(X4) Lemma 2.1 -- the exportable core.**

```text
  Parameters: a finite group G with |G| = 2^m, an odd integer k.
  Claim:      forall g in G, g^k = 1 -> g = 1.
```

*Lean would check:* `orderOf g` divides both `k` and `2^m`, hence divides
`gcd(k, 2^m) = 1`.  The remainder of Lemma 2.1 is then bounded arithmetic at
fixed `ell`: for each odd `k >= 3` dividing `n = 2 ell + 1`, `d = n/k <= ell`,
and `x^d` is irreducible only for `d = 1`.  The whole lemma at fixed `ell` is a
decidable statement about a finite set of divisors.

**(X5) The `q_j` bounds at a fixed level -- the exportable core.**

```text
  Parameters: a finite index set B, u v : B -> Int with u b >= 0, v b >= 0.
  Claim:      sum_b (u b + v b)^2  <=  2 * sum_b ((u b)^2 + (v b)^2)
              and  sum_b ((u b)^2 + (v b)^2)  <=  sum_b (u b + v b)^2 .
```

Equivalently `C_(j-1) <= C_j <= 2 C_(j-1)`, i.e. `0 <= q_j <= 1`.
*Lean would check:* the pointwise inequalities `u^2 + v^2 <= (u+v)^2` (needs
`u, v >= 0`) and `(u+v)^2 <= 2(u^2+v^2)` (needs nothing), then `Finset.sum_le_sum`.
This is the sharpest small export in the artifact: it is the *only* inequality in
the entire (D-PROD) machine, and everything else there is an identity.

**(X6) The grading-free Wick total (Proposition 2.8).**

```text
  Parameters: a finite index set I, a symmetric C : I -> I -> Int.
  Claim:      sum_(a,b,c,d) ( C a b * C c d + C a c * C b d + C a d * C b c )
              =  3 * ( sum_(a,b) C a b )^2 .
```

Pure algebra, no arithmetic input, no positivity.  *Lean would check:*
`Finset.sum` distributivity plus `ring`.  Together with (X5) this covers the
whole algebraic skeleton of section 2.4.

**(X7) The crossover arithmetic of Theorem 2.16.**

```text
  Parameters: K in Q, ell in N.
  Claim (odd):  K^2 * 2^(ell+2) * T(ell)^4  <  (2^(ell+1) - 1)^4 ,
                T(ell) = sum_(i=1)^(ell-1) i * 2^(i/2) .
  Claim (even): K^2 * 2^(ell+4) * T(ell)^4  <  (2^(ell+2) - P_n^sharp)^4 .
```

To avoid irrationals, export `T(ell)^4` as `(P + Q sqrt 2)^4` with `P, Q` in `Z`
computed by the obvious recursion, or export the rational upper bound
`T(ell) <= (ell-1) 2^((ell-1)/2) / (1 - 2^(-1/2))` after clearing the surd.
*Lean would check:* a bounded numeric inequality for each `ell` in `[22, N]` by
`norm_num`/`decide`, plus a monotonicity induction for `ell > N` -- the step
being that the right side gains a factor `2^4` per unit `ell` while the left
side gains `2 * ((ell)/(ell-1))^4 * 2^2 < 2^4`.

**(X8) Lemma 2.30, forced square divisibility -- the exportable core.**

```text
  Parameters: a finite-dimensional F_2-vector space T, an affine coset F = f0 + T,
              two F_2-linear functionals L1 L2 : T -> F_2 that are jointly surjective.
  Claim:      card { f in F : L1 (f - f0) = c1 and L2 (f - f0) = c2 } = card F / 4
              for each (c1, c2) in F_2^2.
```

*Lean would check:* the rank-nullity statement for the map `(L1,L2)`.  The
arithmetic instance -- `(x+1)^2 | f  <->  f(1) = 0 and f'(1) = 0` over `F_2` --
is a separate small exportable lemma about multiplicity of a root in
characteristic `2`.

**What a Lean verification would NOT establish.**  (X1)-(X8) are the *algebraic
skeleton*.  They do not touch: (I1) (the Riemann hypothesis for function-field
`L`-functions); the exact `L`-degree distribution (I2); Corollary 1.2; the
layer-energy bounds of Theorem 2.11; and of course (SUP-L) and (CDL).  A green
Lean run over the exports would certify that *the combinatorial and algebraic
reasoning in this artifact is correct*, and nothing about whether the endpoint
follows.  Anyone reading a "Lean-verified" label on this work should read that
sentence first.

---

## 6  Honesty: what is open, the square-root barrier, and what is new

### 6.1  The complete list of what is open

```text
  (SUP-L)     sup-norm of one conductor layer, absolute constant K.       OPEN
  (CDL)       q_j <= 1/ell at levels j <= c log2 ell.                     OPEN
  (W4-exact)  M_4 < (mu - Pi_n)^4 as a uniform statement.                 OPEN
  (WK)        the connected form of the same.                             OPEN
  the Lemire endpoint itself, for ell > 199.                              OPEN
  the even-endpoint analogue of Theorem 2.23 (E_1 = 0).                   OPEN
  Theorem 2.36 at m >= 4: the fourth Jacobian case (u = 0, |V| >= 3),
     which needs h >= 3 delta and therefore FAILS at the odd endpoint
     for ell >= 13.  m = 4 is the case this project uses.                 OPEN
  OPEN(bk) inside Theorem 2.36 (a separate bookkeeping step).             OPEN
  the equidistribution sub-lemma and the genuine off-diagonal of
     Model 2.34 / section 2.6.                                            OPEN
```

Nothing in this artifact proves the Lemire endpoint conjecture, and no theorem
credit is claimed for it or for any uniform estimate.  Two conditional
implications are proved: Theorem 2.16 ((SUP-L) with `K = 2` gives the endpoint
for `ell >= 22 / 20`) and Proposition 2.22 ((CDL) with `c >= 4.1` gives it for
`ell >= 200`).

### 6.2  The square-root barrier, stated precisely

At the Lemire endpoint the two natural scales **coincide**:

```text
  n - ell  =  n/2 + 1/2   (odd endpoint)      or      n/2 + 1   (even endpoint),
```

so the class mean `mu = 2^(n-ell)` and the Weil error scale `2^(n/2)` differ by a
factor `2^(1/2)` or `2`.  Two consequences, both of which cost this project
whole workstreams and should be recorded so they are not re-attempted.

**(a) RH-strength equidistribution has no margin at any conductor level.**
The extremal configuration one wants to exclude is a single-class spike: `D`
concentrated on one class at the critical height `mu`.  Its level-`j` cylinder
discrepancy is `|s_j(b_0)| = mu (1 - 2^(-j)) ~ mu`, while the proved cylinder
bound from (I1) is
`|s_j(b)| <= 2^(-j) W_j 2^(n/2)` with `W_j = (j-2) 2^j + 2`.  Excluding the spike
would need `2^(n - 2 ell + 2j) > W_j^2`, which at the odd endpoint reads
`2^(j + 1/2) > (j-2) 2^j + 2`.  **This fails for every `j >= 4` and every `ell`**
-- verified as an exact integer comparison on all 36 rows `ell = 2..19`, both
parities (`critical_spike_excluded` in `acb_dic_profile`).  No sharpening of the
low-conductor input can repair it, because the input is already sharp
(individual RH).

**(b) Therefore every surviving route asks for a saving *beyond* individual
RH.**  (SUP-L) asks for square-root cancellation **in the character count** of a
single conductor level -- a saving of `2^((j-1)/2)` over what (I1) plus the
triangle inequality gives.  (CDL) asks for `poly(ell)` decorrelation of a
shifted second moment.  Neither is implied by (I1); both are of the type that
in the function-field setting is proved by monodromy/equidistribution, and both
are currently available only in the `q -> infinity` limit (section 4).  **This is
the single sentence that describes the state of the problem.**

**(c) A related uncertainty principle, and the one escape found.**
Sweep-09's lemma says that any function measurable for the conductor-`<= a`
filtration with `a < ell` and dominated pointwise by `delta_1` is `<= 0`, so a
Beurling--Selberg minorant built from low-conductor data alone cannot give a
positive lower bound on `N_n(1)`.  Section 2.4 evades this without contradicting
it: (D-PROD) composes a *low*-conductor input (`q_j` small for `j` in some set)
**multiplicatively** with the *proved* bound `q_j <= 1` at every other level, and
positivity is extracted only at the very end by Chebyshev at one point.  No step
of that chain is a low-conductor minorant.  This inverts the sweep's conclusion
that all information must come from the top `O(log ell)` levels: (CDL) is the
first obligation in this project that lives at the **bottom** of the filtration.

### 6.3  How strong the evidence for (SUP-L) actually is

This deserves to be stated against itself, because the headline number `2.0000`
is misleading in both directions.

* **The trivial bound is `kappa_j <= 2^((j-1)/2)`** (Fourier inversion, (CT),
  (I1), triangle inequality).  So the statement `kappa_j <= 2` has **no content
  at all for `j <= 3`**, and the measured global maximum `2.0000` occurs exactly
  at `j = 3`, where it *is* the trivial bound, attained.  That row
  (`ell = 11, n = 24, j = 3`) is a point of complete failure of cancellation: all
  four level-`3` characters saturate (I1) simultaneously and align in phase at
  some class.  It is not evidence for (SUP-L); it is evidence that no cancellation
  whatsoever is available at small `j`.
* Conversely `kappa_2 in [1, sqrt2]` is a **theorem** (Proposition 3.1 below),
  so the `j = 2` row of table (E-1) also carries no information.
* The genuine evidence is the `j >= 4` part, and **it is much thinner than the
  headline suggests**.  Diary 11's per-level table prints even `j` only
  (`2, 4, 6, ..., 20`), and its quoted "31% margin" is `2/1.5234`, the margin
  over `j >= 6`.  The phase-3 verifier recomputed all levels including odd `j`
  and found `max_(j >= 4) kappa_j = 1.9922` at `(ell,n,j) = (11,24,5)` -- a
  margin of **0.4%** below `K = 2`, on the open part of the statement, inside a
  range only reaching `ell = 12`.  See table (E-1b).
* So the honest statement of the measured evidence is:
  ```text
    j <= 3 :  K = 2 is a theorem (Proposition 3.1(a)); measured kappa
              saturates the ceiling, at the identity class, at (11,24,3).
    j >= 4 :  K = 2 is open; measured max 1.9922 at (11,24,5).
              No measured margin worth quoting.
  ```
* **The measured range is `6 <= ell <= 20` for even `j` and `5 <= ell <= 12` for
  all `j`.**  The statement is uniform in `ell` and in `j`; that is not much of a
  test of a uniform statement, and the single closest measured approach to `K = 2`
  sits at an odd level that the headline table never printed.
* **Consequence for the next experiment.**  Falsification effort should go to
  `j = 4, 5` at larger `ell`, not to large `j`.  A single row with
  `kappa_5 > 2` would not kill (SUP-L) -- the crossover is insensitive to `K`
  (Remark 2.16a) -- but a `kappa_j` that *grows* with `j` or `ell` would kill the
  reduction outright.

### 6.4  What is genuinely new here, and what is repackaged

Taking the items one at a time, with the least generous reading first.

**Standard, and claimed as nothing else:**
* The exact-conductor decomposition and its orthogonality (Theorem 2.7).  This is
  ordinary Fourier analysis on a filtered finite abelian group; the proof is two
  lines and any analytic number theorist would write it down.
* Proposition 2.18 (`C_j` as a cumulative spectral mass) is Parseval on quotients,
  i.e. the dyadic-martingale square function.
* Lemma 2.35 (weight-blindness) is the classical extremality of the point mass
  for `||f||_4/||f||_2`.  Its only novelty is the *use*: it closes four literature
  families at once, and it identifies what a proof must consume.
* Lemma 2.24-2.26 (the order grading) is a routine unfolding of `Lambda = mob * deg`.

**New to this problem, elementary, and genuinely load-bearing:**
* Lemmas 2.1 and 2.2.  The emptiness of *every* odd prime-power exponent layer at
  an even endpoint is a real improvement: it replaces the in-tree bound's
  `n 2^ceil(n/3)` by `n 2^ceil((ell+1)/2)`, a factor `2^(ell/6)`, and it moves the
  even-endpoint crossover from `ell = 17` to `ell = 13`.
* Theorem 2.4 with the correct constant `mu - Pi_n`.  The point is negative -- the
  positivity-only form `M_4 < mu^4` does *not* prove irreducibility -- and it is
  the kind of correction that is worth more than a theorem.

**The candidate novel core.**  Four statements, which I believe stand or fall
together, and all four of which the phase-3 adversarial verifier independently
re-derived and marked CONFIRMED (`20-verify-chains.md`, entries 4, 5, 7, 8-10):

1. **Proposition 2.9.**  In the exact-conductor grading, every Wick pairing of the
   fourth-cumulant cell tensor is nonnegative and the absolute pairing total is
   *exactly* `3 M_2^2`.  In the convolution-order grading the same quantity is
   `694x` to `11444x` larger and grows like `2^(0.41 ell)`.  So the entire loss of
   the earlier cellwise-absolute candidates was an artefact of grading by a
   non-orthogonal family, and regrading is free.
2. **Theorem 2.10**, the parity selection rule: a conductor cell vanishes unless
   the number of indices at the maximal level is even.  It removes about 82% of
   the cells and it is a `Z/2`-selection rule with a two-line proof.
3. **Theorem 2.12**, the exact `1/4`-per-level recursion at fixed `n`.  This is an
   *equality*, not an estimate, and it says that the whole sub-top-level part of
   the problem at level `ell` is the level-`(ell-1)` problem divided by four,
   against a budget that gains `2^5` per endpoint step.
4. **Theorem 2.16**, the resulting reduction: the entire fourth-moment obligation
   collapses, with every intermediate step elementary and every constant explicit,
   to the single sup-norm statement (SUP-L) with an *absolute* constant, and the
   crossover is insensitive to that constant (`K = 10^6` still gives `ell >= 67`).

To that I would add, as separately new but narrower:

5. **Theorem 2.19 and Proposition 2.22.**  Writing the kurtosis of the class
   populations as an exact product `R_0 = prod_j (1 + q_j)` over the conductor
   filtration, with the *only* inequality in the machine being `q_j <= 1`.  This
   converts a global fourth-moment target into a statement that a `O(log ell)`
   *subset* of levels is delocalized, and it is what makes the bottom of the
   filtration usable at all (section 6.2(c)).
6. **Theorem 2.36**, a characteristic-free replacement for Hast--Matei's
   Theorem 2.7 that never uses their tameness Lemma 2.6.  **Only at `m = 3`.**
   Diary 12 labelled it PROVED for all `m`; the phase-3 verifier found a genuine
   hole in the fourth case at `m >= 4` (`u = 0`, `|V| >= 3`, where `z_1` is
   unconstrained), and `m = 4` is the only case this project uses.  So the item
   that looked like the clearest "new relative to a specific published paper"
   result is, at the parameter this project needs, **not proved**.  It would also
   buy nothing if it were, since the surrounding architecture is vacuous at fixed
   `q = 2` for reasons unrelated to tameness.

**And the caveat that governs all of the above.**  Every individual step in
items 1-5 is elementary; none would take a specialist more than an afternoon.
The claim is about the *combination*: that grading a fourth-moment problem by
exact conductor turns a hopeless cellwise-absolute bound into a nearly free one,
and that the resulting chain terminates in a single sup-norm statement with an
absolute constant.  **I did not verify that claim against the literature to the
standard this project's charter requires.**  The `WebSearch` budget for the
session was exhausted before this workstream started; the arXiv-API queries of
section 4.6 returned zero entries for the closest phrasings, but arXiv abstract
search is phrase-sensitive, misses journal-only work, and would not catch an
independent rediscovery under different terminology (for instance in the
martingale, Efron--Stein, or Katz-monodromy vocabularies).  So:

> **Priority claim, stated at the strength the evidence supports.**  The proofs
> of items 1-6 have been re-derived from scratch here and are correct.  Whether
> the *combination* is new is **UNVERIFIED**: it survived a weak arXiv-abstract
> search and the phase-1 literature sweeps (diaries 01-03, which searched
> hypercontractivity, fourth-moment/energy, and Galois-ring Fourier analysis and
> found nothing of this shape), and that is all that can honestly be said.  A
> proper priority search is a prerequisite for any external claim of novelty.

### 6.5  Things this project got wrong, recorded

Kept here because the corrections are part of the artifact's content.

* Diary 04's (WK) was stated with `<=`; it must be strict (Corollary 2.6).
* Diary 11 stated that the (SUP-L) crossover "moves by one level per doubling of
  `K`".  It moves by about three (Remark 2.16a); recomputed independently here.
* Sweep-08's identity `sum_F c_F^2 = N_points + (off-diagonal)` and the in-tree
  doc comment repeating it are wrong whenever `eps` vanishes anywhere;
  Corollary 2.28 is the corrected identity, and the "off-diagonal is nonpositive"
  reading of `(E2')` is false on 7 of 22 measured rows.
* Sweep-09's `M_4 < mu^4` proves positive Mangoldt mass, not irreducibility.
* Sweeps 07/09's growth law `M_4 ~ 0.6 ell^3 2^(3 ell)` is wrong in the exponent
  of `ell`: over `ell <= 21` the cubic normalization falls monotonically while the
  quadratic one rises toward `12 ell^2 2^(3 ell)` (odd) / `48 ell^2 2^(3 ell)`
  (even), consistent with the Gaussian plus Keating--Rudnick prediction.  The
  slack in `(W4)` is `2^ell/(0.75 ell^2)`, better than advertised.
* Diary 03's `(GR-2)` -- the reading of `c_F` as a `Z/8` Gauss sum with an Arf
  sign -- is refuted three ways in section 2.6, and the mechanism is proved
  (Lemmas 2.30-2.31): the alternating stratum of that family consists entirely of
  degenerate dimension-`2`, rank-`0` fibres, and it must.
* Green--Sawhney's Theorem 1.2 is not importable at our density (section 4.3).
* Diary 03's `(GR-1)` corollary ("the fibre family is emphatically not a union of
  complete twist orbits") is backwards: by Theorem 2.29 every fibre **is** a
  complete orbit of the genuine acting group `T_h`, and the incompleteness is an
  index-two linear selection (Proposition 2.33).
* Diary 14's Lemma D4 claims `T_h contains span{x^j : max(1, ell+1-2v) <= j <= d}`.
  That is **false** whenever `3v > ell+1`; witness `ell = 13`, `v = 5`,
  `h = x^5`, `tau = x^4`, where `v(tau) + v(tau+h) = 8 < 9 = r - v`.  The
  conclusion survives with the corrected proof of Lemma 2.31.  (Found
  independently here and by the phase-3 verifier, entry 27.)
* Diary 12's Lemma W is labelled PROVED for all `m`; it is proved at `m = 3` and
  has a GAP at `m >= 4` (Theorem 2.36's scope note).
* Diary 11's `(CAB)` and `(CAB-L)` are stated against the budget
  `2^(ell + 4(n-ell))`, which yields only `M_4 < mu^4` -- the criterion diary 04
  proved insufficient.  The fix is the one substitution
  `2^(ell+4(n-ell)) -> 2^ell (mu - P_n)^4`, and diary 11 already measures that
  column; this artifact uses only the corrected budget.
* Diary 11's per-level `kappa_j` table prints even `j` only, and its quoted "31%
  margin" is the margin over `j >= 6`.  The binding measured value is at `j = 5`
  and the margin there is `0.4%` (section 6.3, table (E-1b)).
* Diary 13's `(TWIST)` prints `S_(psi chi)`; the derivation gives
  `S_(psi chi^(-1))`.  Harmless for `|fhat(chi)|`, wrong as an identity.

### 6.6  What a referee should check first

In descending order of leverage:

1. Theorem 2.16's arithmetic.  It is the only place where a numeric crossover is
   claimed, and it was recomputed here from scratch in 80-digit decimal
   (`cross.py`), reproducing diary 11's table exactly.  Independent recomputation
   is cheap.
2. Theorem 2.10 and Proposition 2.9, which together are the reason the conductor
   grading is worth anything.  Both are short and both are machine-checked on
   every row of two independent implementations plus a sympy brute force.
3. Theorem 2.23's involution argument, which is the only *unconditional* new
   arithmetic input in the artifact.
4. Section 6.3 and table (E-1b): that the `j <= 3` part of the (SUP-L) table is
   vacuous, and that the binding measured value is `1.9922` at `(11,24,5)`,
   `0.4%` below `K = 2`.  This was reached independently here (via
   Proposition 3.1) and by the phase-3 verifier (entries 13 and 14), which is
   some comfort, but the underlying data range is small (`ell <= 12` for odd
   levels) and it is the number the whole conjecture should be judged on.
5. (I1') -- purity at level 2 -- which is used for the exact `V_2` and for
   Proposition 3.1, and which this artifact imports rather than proves.
6. Theorem 2.36's fourth case, which is the one place in the artifact where a
   diary's PROVED label was withdrawn rather than repaired.

---

*End of artifact.  Working diary, decisions and reconciliation log:
`23-artifact.md`.*


## Novelty verification addendum (2026-08-20, coordinator pass)

A dedicated triple-check (`24-novelty-check.md`) was run after assembly:
internal ledger grep, arXiv API, and arXiv full-text search with a positive
control. Outcome: the level-3 period-24/supersingular material is COVERED BY
PUBLISHED WORK — Gorodetsky (arXiv:1805.07105) and Ahmadi--Gologlu--Granger--
McGuire--Yilmaz (arXiv:1605.07229) — and any novelty claim there is
withdrawn; the sibling-difference identification is an internal rediscovery
of the lane's 2026-08-19 Haar/sibling machinery, sharpened by the exact
normalization; the conductor-grading orthogonality + parity rule +
1/4-recursion package, the q_j application, and above all the (TOP-POLY) /
(VAR-EQ) pricing of the endpoint have NO located priors (weak negatives:
WebSearch was exhausted and phrase-miss risk is demonstrated). See
`24-novelty-check.md` for the per-claim table and the searches run.


### Correction to the addendum (same day, later): Newton-over-Hodge at p=2

The suggestion above that Newton-over-Hodge at p = 2 is outside published
hypotheses is WITHDRAWN after a deeper literature pass: Liu--Wan (Alg. &
Number Theory 2009, arXiv:0802.2589, Thm 5.2) prove the T-adic Hodge bound
with no hypothesis on p, covering all p-power-conductor characters at
p = 2 for this family's monomial directions, and Davis--Wan--Xiao
(arXiv:1310.5311) carry no parity hypothesis either. The p >= 3 exclusions
are specific to the Kramer-Miller(--Upton) curve-local framework. See
`24-novelty-check.md`, correction section, for the verified quotations and
the correctly-scoped thin residual (exact level ordinarity, lattice-forced
min-slope across mixed characters, the rounded-Hodge counterexample).
