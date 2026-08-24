# AC-Bridge 21 (phase 3): the (SUP-L) assault

Charge: prove `(SUP-L)` where possible (low levels, the exact-2.0000
attainment structure, the connection to A's `1/4`-recursion and C's
`q_j <= 1`), and quantify the irreducible core.

```text
(SUP-L)   max_e |D_[j](e)|  <=  K (j-1) 2^((j-1)/2) 2^(n/2) / 2^ell
          for every conductor level j <= ell and n in {2ell+1, 2ell+2}.
```

Date opened: 2026-08-20.
Board: `10-angles-board.md`, phase-3 assignment 21.
Charter: `00-charter.md` (rules of the project apply verbatim).
Sibling audit: `20-verify-chains.md` (landed during this run; reconciled at the
end -- we agree on everything we both computed, and this file settles the
question it flagged as open).

Epistemic labels: **PROVED** (argument written out), **REFUTED** (exact
witness), **MEASURED** (finite evidence, no theorem credit), **OPEN**.

New files written by this workstream (no existing source file touched):

```text
crates/axeyum-cas/examples/acb_sup_levels.rs   the layer as a level-j sibling
                                               difference; ell-freeness control;
                                               exact kappa/flatness/fill
crates/axeyum-cas/examples/acb_sup_period.rs   the exact degree recursion, an
                                               independent second algorithm, and
                                               the supersingularity/period test
```

## Headline

1. **`(SUP-L)` carries no `ell`.** The layer is a level-`j` sibling difference
   of short-interval counts; `kappa_j` is a function of `(j, n)` alone.
2. **`(SUP-L)` at `K = 2` is REFUTED**, with exact integer witnesses at
   `(j,n) = (4,56)` and `(5,48)` -- both endpoint-admissible, both just outside
   diary 11's `ell <= 20` measurement window. Pushed further, `kappa_4` reaches
   `2.8241` and `kappa_5` reaches `3.9207`, against their proved ceilings
   `2.8284` and `4`. **No absolute `K` survives** on the evidence.
3. **`(SUP-L)` was also the wrong statement.** The chain it feeds needs the
   constant only in a top window of `~ 4 log2 ell` levels, and even there it
   needs only a **polynomial** saving over the individual Weil bound. Priced
   exactly: the `L^4` route needs `2 ell^2`; the lane's OWN Haar-triangle route
   needs `2.4 ell`. **The whole conductor-graded fourth-moment ladder asks a
   factor `ell` MORE than the route the ledger already had.**
4. Proved rungs: `j = 1` (zero), `j = 2` (`kappa_2 = sqrt 2` even / `1` odd,
   exact), `j = 3` (`kappa_3` periodic mod 24, `sup = 2` exactly). Levels
   `1,2,3` are supersingular; level `4` is not, with a 2-adic witness at `n = 14`.
5. The mechanism behind the measured `kappa ~ 1` is identified and is not
   cancellation: `kappa_j = F_j sqrt(fill_j)` with `fill_j = (1+o(1))/(j-1)`
   the **Keating--Rudnick/Katz form factor** (verified at `q = 2` fixed, where
   their theorem does not apply) and `F_j ~ 1.10 sqrt(j-1)` the Gaussian
   extreme-value constant for `2^j` samples. The two `(j-1)`s cancel.

## Log

### required reading

`00-charter.md`; `10-angles-board.md`; `11-angle-cab.md` in full (859 lines);
`13-angle-dichotomy.md` (the `q_j` machinery, Lemmas D1--D4, Result C1);
`docs/plan/status/52-gf2-lemire.md` (the proved individual Weil bound, the
exact-conductor Fourier inversion, the `ell - ceil(log2 ell)` discharge, the
buffered square-root-fibre target and its refuted coefficient-two predecessor);
`crates/axeyum-cas/examples/acb_cab_levels.rs` (the sibling recursion and the
SWAR group model reused here).

### the object, restated: `(SUP-L)` has no `ell` in it

**Lemma S1 (the layer IS a level-`j` sibling difference).  PROVED.**
Let `N_j(b)` be the von-Mangoldt-weighted count of monic degree-`n`
polynomials whose reciprocal class truncates to `b` in `E_j = (F_2[x]/x^(j+1))^*`,
let `g_j = 1 + x^j`, and put

```text
Delta_j(b) := N_j(b) - N_j(b g_j).
```

Then for every `ell >= j` and every `e in E_ell`,

```text
D_[j](e) = Delta_j(pi_j e) / 2^(ell-j+1) ,      pi_j : E_ell -> E_j.
```

*Proof.*  `P_j D(e) = 2^-(ell-j) N_j(pi_j e) - 2^(n-ell)` because the fibre of
`pi_j` is the coset `e H_j` of size `2^(ell-j)`.  Hence
`D_[j] = P_j D - P_(j-1) D = 2^-(ell-j) N_j(b) - 2^-(ell-j+1) N_(j-1)(b')`
with `b = pi_j e`, `b' = pi_(j-1) e`; and `N_(j-1)(b') = N_j(b) + N_j(b g_j)`
since the two level-`j` classes above `b'` are exactly `b` and `b g_j`.
Substituting gives `2^-(ell-j+1)(N_j(b) - N_j(b g_j))`.  QED

**Corollary S2 (`ell`-freeness).  PROVED.**

```text
kappa_j(ell,n) := max_e |D_[j](e)| 2^ell / ((j-1) 2^((j-1)/2) 2^(n/2))
                = max_b |Delta_j(b)| 2^((j-1)/2) / ((j-1) 2^(n/2))
```
is independent of `ell`.  So `(SUP-L)` is a two-parameter statement over the
pairs `(j,n)` with `n >= 2j+1` (the endpoint-admissible pairs: `n = 2ell+1` or
`2ell+2` for some `ell >= j`).

Machine control (`acb_sup_levels identity`): the full-`ell` sibling recursion of
diary 11 is run at level `ell` and compared class-by-class against the
level-`j` computation.  `A_j(e) = Delta_j(pi_j e)` on **every** class at
`(ell,n) = (6,13)` and `(11,24)`, every `j`; and the layer energy
`2^ell V_j = 2^(j-2) sum_b Delta_j(b)^2` agrees with the CAS's independent
`exact_conductor_second_moment(j,n)` at every level of both rows.

This is the reason the whole assault is affordable: the layer at level `j` costs
`O((j+n) 2^j)`, not `O(2^ell)`.  Diary 11's `ell <= 20` ceiling was an artefact
of computing the layer inside the big group.

**Lemma S3 (identification with the ledger's `H_j^*`).  PROVED (by inspection
of the definitions).**  `max_b |Delta_j(b)|` is exactly the ledger's
`maximum_sibling_difference` = `H_j^*` of the population-refinement triangle
(`gf2_hayes.rs:4956`, `:15852`).  Confirmed numerically: at `(n,j) = (40,4)`
this file computes `2112512`, the value ADR-0517 records as the exact maximum
at `(ell,n,j) = (19,40,4)`.  In these terms

```text
(SUP-L)  <=>  H_j^*  <=  K (j-1) 2^((n-j+1)/2)          for all j <= ell,
(RF)          H_j^*  <=  c  j    2^ceil((n-j)/2)        (the ledger's target, c=3)
(Weil)        H_j^*  <=  (j-1)  2^(n/2)                 PROVED (exact Fourier
                                                        inversion + individual Weil)
```

and, checking both parities of `n-j`, `(SUP-L)` at `K = 2` **implies** `(RF)`
at `c = 3` at every level, while it is **weaker** than the refuted `c = 2` for
`j >= 4` (`2 sqrt 2 (j-1)` vs `2j`).  So `(SUP-L)` at `K=2` sits strictly
between the ledger's refuted and conjectured coefficients.

### (charge 1) low levels, proved

**Lemma S4 (`j = 1`).  PROVED.**  A level-1 character has `deg L = 0`, so
`S_chi = 0` and `D_[1] = 0`.  (Diary 11 Lemma 6.)

**Lemma S5 (`j = 2`, exact).  PROVED.**  `E_2` is cyclic of order 4 generated by
`1+x`; the two level-2 characters are a conjugate pair of order 4 with
`|S_chi| = 2^(n/2)` exactly, so `Delta_2(b) = Re(conj(chi(b)) S)` up to sign and

```text
max_b |Delta_2| = 2^floor(n/2) ,    kappa_2 = sqrt 2  (n even) ,  1  (n odd).
```

Confirmed on every `n = 4..59` (`peak = 2^floor(n/2)` to the digit), and by the
independent period test below (`P = 8`, `sup kappa_2^2 = 128/64 = 2` exactly).
This is diary 20's `(K2-EXACT)`, obtained here from the other side.

**Lemma S6 (the ceiling).  PROVED.**  `kappa_j <= 2^((j-1)/2)` for every `j`, by
the triangle inequality over the `2^(j-1)` level-`j` characters plus the proved
individual Weil bound.  (Independently stated as `(CEIL)` in diary 20.)
Hence `(SUP-L)` at `K = 2` is a **theorem, with no content**, for `j <= 3`.

**Lemma S7 (`j = 3`, exact, with an exact sup).  PROVED.**
The four level-3 characters have inverse roots

```text
chi(1+x) = 1   : L = 1 + 2z + 2z^2 ,        alpha = -1 +- i        = sqrt2 e^(+-3pi i/4)
chi(1+x) = -1  : L = 1 + 2z^2 ,             alpha = +- i sqrt2     = sqrt2 e^(+-pi i/2)
chi(1+x) = +-i : L = 1 + (1+-i)z + 2(+-i)z^2, alpha = sqrt2 e^(-5pi i/12), sqrt2 e^(11pi i/12)
```

every one of which is `sqrt 2` times a root of unity of order dividing 24.
Hence `alpha^24 = 2^12` for all of them, `S_(n+24) = 2^12 S_n`, and
`kappa_3(n)` is **exactly periodic with period 24**.  Its exact sup is

```text
sup_n kappa_3(n) = 2  ,   attained exactly when 24 | n.
```

Machine proof (`acb_sup_period period 3 200`): the propagating check below finds
`P = 24` and reports `kappa_3^2 = 268435456/67108864 = 4` exactly at `n = 24`.

**The periodicity test is a proof, not a sample.**  On the level-`j` isotypic
component every character has `a_d(chi) = 0` for `d >= j` (diary 11, Lemma 2),
so `L(chi,z)` has degree `j-1` and, in the group ring of `E_j`,

```text
Delta(m) = - sum_(d=1)^(j-1) A_d * Delta(m-d) ,   m >= j,
A_d = sum_(u in V_d) u ,  V_d = { 1 + a_1 x + ... + a_d x^d }.
```

If `Delta(m+P) = 2^(P/2) Delta(m)` holds for `j-1` CONSECUTIVE `m >= j`, the
linear recursion propagates it to every larger `m`; since the endpoint range is
`n >= 2j+1 > j`, the finite check settles the whole range.  `acb_sup_period`
seeds from the CAS at `m = j .. 2j-2`, iterates in exact `BigInt`, and
cross-checks against `class_population_distribution` at every `m <= 59`
(47-57 independent agreements per level, zero mismatches) -- a second,
algorithmically disjoint computation of the same object.

**Result S8 (where supersingularity stops).  PROVED, with exact witnesses.**
Levels 1, 2, 3 are supersingular (`P = 8`, `P = 24`); levels 4, 5, 6 are not.
If every inverse root satisfied `alpha^2 = 2 zeta`, then for even `n`
`2^(j-1) Delta_j(b;n) / 2^(n/2)` would be a rational algebraic integer, i.e.
`v_2(Delta_j(b;n)) >= n/2 - (j-1)`.  Exact failures:

```text
 j = 4 , n = 14 :  Delta = 56       v_2 = 3  <  4     (8*56/2^7 = 3.5)
 j = 5 , n = 14 :  Delta = -28      v_2 = 2  <  3     (16*28/2^7 = 3.5)
 j = 6 , n = 18 :  Delta = -8       v_2 = 3  <  4     (32*8/2^9  = 0.5)
```

and the direct period search finds no `P <= 300..400` at `j = 4, 5, 6, 7`.
The ledger's supersingularity refutation at level 10 (degree-22 trace `-5120`)
is therefore not the first failure -- **level 4 already fails, at degree 14.**

Consequence for the method: the finite-period proof scheme closes `(SUP-L)`
exactly at `j <= 3`, and `j <= 3` is precisely where Lemma S6 already makes
`K = 2` vacuous.  **The proved low-level rungs contribute nothing to the
endpoint.**

### (charge 2) the attainment of 2.0000, as an exact identity

At `(j,n) = (3,24)` the sibling-difference vector is supported on ONE sibling
pair (`acb_sup_levels layer 3 24`, all eight classes printed):

```text
 b = 1        (unit 0x1) : Delta_3 = -8192
 b = 1 + x^3  (unit 0x9) : Delta_3 = +8192
 the other six classes   : Delta_3 = 0
```

`8192 = 2 . 2^12 = (j-1) 2^(n/2)`, the full triangle sum.  The exact mechanism,
derived by hand and confirmed to the digit:

* at `n = 24` all four level-3 characters have `S_chi = -2 . 2^12` -- the
  extremal Weil value, and the SAME value, because `24` is the common period of
  all four angle sets (`3pi/4`, `pi/2`, `-5pi/12`, `11pi/12`);
* the level-3 family is the coset `chi_0 . (E_3/<1+x^3>)^`, so a constant `S`
  makes `sum_chi conj(chi(b)) S` collapse by orthogonality onto the subgroup
  `<1+x^3> = H_2/H_3`, giving `Delta_3 = -8192 conj(chi_0(b))` there and `0`
  elsewhere.

So the global maximum is the **simultaneous saturation of both proved inputs**:
`fill_3 = 1` (the level energy equals the Weil envelope exactly) and `F_3 = 2`
(the layer is as concentrated as an antisymmetric vector on 8 classes can be),
and `kappa_3 = F_3 sqrt(fill_3) = 2 = 2^((3-1)/2)`, the Lemma S6 ceiling.
It is an algebraic identity, valid for every `n = 24k`, and it constrains the
open regime not at all.  Diary 20 reaches the same conclusion from the `ell = 11`
side; the two computations agree exactly (`sup_3 = 16 = 8192/2^9`, argmax = the
512 classes over `{1, 1+x^3}`).

### (charge 5 -> becomes the main result) the measurement, and the refutation

`ell`-freeness makes the table cheap.  **847 distinct `(j,n)` layers** computed
exactly, covering **345 of the 406 endpoint `(ell, level)` pairs with
`ell <= 29`** (diary 11 had 341 pairs to `ell <= 20`), plus exact recursion
scans to `n = 3000` at `j = 4, 5, 6`.

Per-level maxima over the endpoint-admissible `n <= 59`:

```text
   j    max kappa_j   at n     max on n<=4j    ceiling 2^((j-1)/2)
   2       1.4142      6          1.4142            1.4142   (proved sup)
   3       2.0000     24          1.5000            2.0000   (proved sup)
   4       2.3542     56          1.5321            2.8284
   5       2.3282     48          1.8750            4.0000
   6       1.4057     56          1.2640            5.6569
   7       1.5215     40          1.2188            8.0000
   8       1.4601     38          1.4395           11.3137
   9       1.6126     48          1.5234           16.0000
  10       1.3580     30          1.3580           22.6274
  11       1.4984     28          1.4984           32.0000
  12       1.5147     26          1.5147           45.2548
  13       1.4008     48          1.4008           64.0000
  14       1.3681     56          1.3681           90.5097
  15       1.7004     48          1.7004          128.0000
  16       1.3095     42          1.3095          181.0193
  17       1.3373     48          1.3373          256.0000
```

> **REFUTED, with exact integer witnesses.  `(SUP-L)` does not hold with
> `K = 2`.**
>
> ```text
> (j,n) = (4,56)   [ell = 27, n = 2ell+2]   H_4^* = 670 285 824
>    exact test:  H^2 . 2^(j-1) = 3 594 264 686 842 871 808
>                 K^2 (j-1)^2 2^n = 4 . 9 . 2^56 = 2 594 073 385 365 405 696
>                 EXCEEDS.        kappa_4 = 2.3542
>
> (j,n) = (5,48)   [ell = 23, n = 2ell+2]   H_5^* =  39 061 504
>    exact test:  H^2 . 2^(j-1) =    24 412 817 515 872 256
>                 K^2 (j-1)^2 2^n = 4 . 16 . 2^48 = 18 014 398 509 481 984
>                 EXCEEDS.        kappa_5 = 2.3282
> ```
>
> Both pairs are endpoint-admissible and both lie just outside diary 11's
> window (`ell <= 20` gives `n <= 42`).

Pushed to `n = 3000` by the exact recursion (`acb_sup_period scan`):

```text
 j = 4 : record kappas 1.8994 (n=40), 2.3542 (56), 2.5276 (160), 2.6987 (216),
                       2.7877 (688), 2.8020 (1536), 2.8241 (2224)
         ceiling 2^(3/2) = 2.8284   -- 99.85% of the a-priori ceiling
 j = 5 : record kappas 1.9922 (24), 2.3282 (48), 2.9273 (96), 3.3585 (120),
                       3.4023 (960), 3.9207 (1320)
         ceiling 2^2 = 4           -- 98.0% of the a-priori ceiling
 j = 6 : 2.5551 at n = 2696 (still climbing; ceiling 5.6569)
```

> **REFUTED for every `K <= 3.92` (exact witnesses), and -- on this evidence --
> for every absolute `K`.**  At fixed `j` the Frobenius angles are not rational
> multiples of `pi` (Result S8), so `n theta` equidistributes and the level-`j`
> family aligns arbitrarily close to its own triangle bound `2^((j-1)/2)`,
> which is unbounded in `j`.  The measured approach (99.85% at `j = 4`, 98.0%
> at `j = 5`) is what that predicts.  A proof that `sup_n kappa_j = 2^((j-1)/2)`
> would need a Kronecker/Weyl closure argument on the joint angle vector and is
> **OPEN**; the refutations at `K <= 3.92` are exact and unconditional.

**Every refuting witness is off-diagonal.**  `n/j` is `14` at `(4,56)`, `9.6`
at `(5,48)`, `556` at `(4,2224)`.  In the near-diagonal band the picture is
completely different, and that is the band the endpoint lives in:

```text
 max kappa_j over endpoint pairs with n = 2ell+1 / 2ell+2 and ell-w < j <= ell
   w =  6 :  1.5321   at (j,n,ell) = (4,14,6)
   w =  9 :  2.0000   at (3,24,11)   <- the PROVED j=3 ceiling
   w = 12 :  2.0000   at (3,24,11)
   w = 20 :  2.3282   at (5,48,23)
```

### (charge 3) the recursion, and what it transports

**Result S9 (the `1/4`-recursion transports `(SUP-L)` with loss exactly 1).
PROVED.**  Diary 11's Lemma 7 says `D_[j]^(ell) = (D_[j]^(ell-1) o pi)/2` at
fixed `n` for `j <= ell-1`.  Both sides of `(SUP-L)` then scale by exactly
`1/2` (the left by the layer, the right by `2^-ell`), so

```text
(SUP-L) at (ell, j, n)   <=>   (SUP-L) at (ell-1, j, n) ,   no loss, no gain.
```

This is Corollary S2 again: the recursion is the `ell`-freeness.  **Induction on
`ell` at fixed `n` is therefore the identity map on the statement and closes no
level range.**  Stepping `ell -> ell+1` introduces the two new degrees
`2ell+3, 2ell+4` and with them EVERY level `j <= ell+1` afresh, so nothing is
inherited across the step that was not already free.  Charge 3's transport
question has a clean answer and the answer is "zero, in both directions".

**Result S10 (mean square to sup: the exact decomposition).  PROVED.**
With `V_j = ||D_[j]||_2^2` and the Weil envelope of diary 11 Lemma 6,

```text
kappa_j  =  F_j . sqrt(fill_j) ,
F_j    := max_b |Delta_j(b)| / ( 2^-j sum_b Delta_j(b)^2 )^(1/2)   (flatness, >= 1)
fill_j := V_j / (2^(n-ell) 2^(j-1) (j-1)^2)                        (Weil fill, <= 1)
```

and the mean-square bound is *exactly* `(SUP-L)` at `K = 1`:
`(2^-ell sum_e D_[j]^2)^(1/2) <= (j-1) 2^((j-1)/2) 2^(n/2)/2^ell`.  So
**`(SUP-L)` says nothing more nor less than: the level-`j` layer is flat, its
sup norm within `K` of its own root-mean-square.**  The gap from mean square to
sup is the flatness `F_j`, and the trivial bound on it is `2^((j-1)/2)`
(concentration on one sibling pair) -- which is Lemma S6.

**Result S11 (`q_j <= 1` gives nothing here, and why).  Consistent with diary
20's (REL-2).**  `q_j` is built from the `D^2` spectrum on cylinders, `(SUP-L)`
from the `D` spectrum on layers; `q_j <= 1` is Cauchy--Schwarz on a two-element
split and is scale-free, whereas `kappa_j` is a normalised sup.  The
`m^2`-weighted mean-square imbalance cannot see which single class carries the
layer's peak.  Diary 20 measured the deficit (`208x` at `j=2`, `3.3x` at
`j=ell`); nothing in this file changes that verdict.

### (charge 4) the top level `j = ell`, and the honest comparison

At `j = ell` the statement reads `H_ell^* <= K (ell-1) 2^((n-ell+1)/2)`, against

```text
 the ledger's (RF), c = 3 :  H_ell^* <= 3 ell 2^ceil((n-ell)/2)   -- conjectured
 the refuted c = 2        :  H_ell^* <= 2 ell 2^ceil((n-ell)/2)   -- REFUTED at (n,j)=(40,4)
 proved individual Weil   :  H_ell^* <= (ell-1) 2^(n/2)
```

> **`(SUP-L)` at `j = ell` is NOT weaker than the lane's standing top-conductor
> obligation.  It is the SAME obligation with a slightly better constant:
> `(SUP-L)` at `K = 2` implies `(RF)` at `c = 3` at every level, and is
> implied by nothing the ledger has.**

Substituted into the ledger's own PROVED weighted-`L1` Haar triangle
`T(ell,n) = sum_j 2^(j-1) H_j^* <= 2^(2ell)`, `(SUP-L)` at `K = 2` closes the
odd endpoint from `ell = 12` and the even from `ell = 14` (exact, computed
here), one level better than `(RF)` at `c = 3` (`ell = 13` / `ell = 15` --
reproduced exactly, which validates the model of the ledger's triangle).

### the price, computed exactly: (SUP-L) over-asks by a factor `ell`

Re-derive diary 11's chain independently
(`sum_j kappa_j^(1/2) fill_j^(1/4) (j-1) 2^((j-1)/2) . 2^((2n-3ell)/4) < mu - P_n`,
Lemma A/B `P_n`, 60-digit arithmetic).  Control: with a uniform `K` it
reproduces diary 11's crossover table to the level -- `K = 1.6 -> 21/19`,
`2.0 -> 22/20`, `2.5 -> 23/21`, `4.0 -> 25/23`.

**Result S12 (the size of the gap).  MEASURED, exact.**  With ONLY proved
inputs (individual Weil, the triangle bound `kappa_j <= 2^((j-1)/2)`, and
`fill_j <= 1`) the `(L4-LAYER)` closure ratio is

```text
 ell      20      30      50     100     200     400     800
 odd    18.18   28.56   49.30  101.2   204.9   412.3   827.1    = (1.03+o(1)) ell
 even   13.20   20.22   34.86   71.53  144.9   291.5   584.9    = (0.73+o(1)) ell
```

-- **the chain misses by exactly one factor of `ell`, no more.**  The same is
true of the ledger's Haar triangle with Weil only (`1.41 (ell-1)`).  This is a
precise statement of the "one logarithm" the sweep isolates.

**Result S13 (what is actually required, per route).  MEASURED, exact.**  Take
`kappa_j <= min(K, 2^((j-1)/2))` (i.e. the proved ceiling wherever it is
better) and solve for the largest admissible `K`:

```text
                     L^4 / fourth-moment route        Haar-triangle route
  ell    K_max        saving over Weil   /ell^2     K_max        saving   /ell
   22     2.03            712            1.47        32.4          44.7   2.03
   30    15.9            1456            1.62       362            64.0   2.13
   50     5.31e3         4472            1.79         2.12e5      112     2.24
  100     4.14e10       19223            1.92         3.42e12     233     2.33
  200     1.13e25       79636            1.99         1.89e27     474     2.37
  400     3.51e54        3.24e5          2.03         1.19e57     957     2.39
```

("saving over Weil" `= 2^((ell-1)/2)/K_max` is the factor by which the top
conductor level must beat the proved individual Weil bound.)

> **The endpoint needs a POLYNOMIAL saving at the top conductor level, not an
> absolute constant:**
> ```text
>   Haar-triangle route :  H_ell^*  <=  (ell-1) 2^(n/2) / (2.4 ell)
>   L^4 route           :  H_ell^*  <=  (ell-1) 2^(n/2) / (2 ell^2)
> ```
> `(SUP-L)` with absolute `K` demands `2^((ell-1)/2)/K` -- **exponentially more
> than either route uses**, which is why it can be refuted without the endpoint
> being affected at all.
>
> And, since `2 ell^2 > 2.4 ell`: **workstream A's conductor-graded
> fourth-moment ladder asks for a factor `ell` MORE than the Haar-triangle route
> the ledger already had.**  The ladder's value is the structure it exposes
> (Lemmas 1-7, orthogonality, the parity rule), not a weakening of the
> obligation.

**Result S14 (the residual statement).**  Everything above collapses to one
line, in the ledger's own notation and with no `(SUP-L)`-style constant:

```text
(TOP-POLY)   H_j^*  <=  (j-1) 2^(n/2) / (2.4 ell)      for  ell - 4 log2 ell <= j <= ell,
             n in {2ell+1, 2ell+2},
```

the PROVED individual-Weil bound divided by `2.4 ell`.  Below that window the
proved bound already suffices (this is the ledger's own
`ell - ceil(log2 ell)` discharge, re-derived here from the fourth-moment side).
`(TOP-POLY)` implies the endpoint through the ledger's proved Haar triangle,
for all `ell` above the crossover.

### the mechanism: why `kappa_j ~ 1` in the band, and it is not cancellation

**Result S15 (the Keating--Rudnick form factor, at `q = 2`).  MEASURED.**
`fill_j . (j-1)` over all measured `n >= 2j+1`:

```text
   j        3      5      7      9     11     13     15     17     18
 mean    0.986  0.985  1.017  1.001  1.005  1.002  1.003  1.000  1.005
 range  [.5,2] [.32,2.4] [.51,1.69] [.69,1.39] [.87,1.22] [.92,1.12] [.98,1.04] [.98,1.02] [.999,1.01]
```

so `V_j = (1 + o(1)) 2^(n-ell) 2^(j-1) (j-1)` -- one factor `(j-1)` better than
the proved Weil envelope, with the spread collapsing as `j` grows.

Literature, fetched and quoted (not recalled).  Keating--Rudnick,
*The variance of the number of prime polynomials in short intervals and in
residue classes*, arXiv:1204.0708v3, Section 4 sets up exactly our object: their
involution `f^*(T) = T^(deg f) f(1/T)` (4.1), `Lambda(f^*) = Lambda(f)`
(Lemma 4.1), and (4.10) "as `B` ranges over `M_(n-h-1)`, `B^*` ranges over
`(F_q[T]/(T^(n-h)))^x`" -- i.e. our `E_j` with `j = n-h-1`, interval size
`q^(h+1) = 2^(n-j)`.  Their Theorem 2.1, verbatim:

> "Theorem 2.1. Let `h < n - 3`. Then `lim_(q->infinity) (1/q^(h+1))
> Var(nu(.;h)) = n - h - 2`."

In our dictionary `n-h-2 = j-1`, so `Var(N_j) ~ 2^(n-j)(j-1)` and, with
uncorrelated siblings, `mean_b Delta_j^2 ~ 2^(n-j+1)(j-1)`, i.e. exactly
`fill_j = 1/(j-1)`.  **The hypothesis is `q -> infinity` at fixed `n`** (their
input is Katz's equidistribution Theorem 4.2, also a `q -> infinity` statement).
Our data is `q = 2` fixed with `n -> infinity`, where the theorem does not
apply -- so Result S15 is *evidence for* the KR law in an open regime, and is
recorded as such.

**Result S16 (flatness is the Gaussian extreme-value constant).  MEASURED.**
`F_j / sqrt(j-1)`, mean over the same pairs: `1.03, 1.02, 0.99, 0.99, 1.07,
1.10, 1.06, 1.10, 1.11, 1.09, 1.09, 1.12, 1.10, 1.11, 1.11` for
`j = 4..18`.  The max of `2^j` iid Gaussians has
`E[max]/sd = sqrt(2 ln N) - (ln ln N + ln 4pi)/(2 sqrt(2 ln N))`, which at
`N = 2^18` is `4.49`, i.e. `1.089 sqrt(j-1)`.  Measured `1.109`.

> **Mechanism.**  `kappa_j = F_j sqrt(fill_j) ~ (1.10 sqrt(j-1)) . (j-1)^(-1/2)
> = 1.10`.  The measured `kappa ~ 1` of diary 11 is **not** square-root
> cancellation over the character family: it is the Keating--Rudnick variance
> `(j-1)` exactly cancelling the extreme-value growth `sqrt(j-1)` of the max
> over `2^j` classes.  That is why `kappa_j` has "no drift in `j` or in `ell`",
> and it is also why a sup over MANY `n` at fixed `j` escapes: it samples the
> extreme tail repeatedly until the algebraic ceiling `2^((j-1)/2)` is reached.

### independent verification

**(i) From-scratch sympy.**  `sympy_supl.py` shares no code, convention or
algorithm with the CAS or with either example: it enumerates every monic
polynomial of degree `n` over `GF(2)`, factors with `sympy.factor_list(...,
modulus=2)`, applies the von Mangoldt weight, bins by the reciprocal truncation
mod `x^(j+1)`, and forms the sibling difference by explicit multiplication in
the principal-unit group.

```text
SYMPY_SUPL|j=2|n=10|peak=32     |sumsq=2048  |kappa2=2048/1024    |kappa=1.414214
SYMPY_SUPL|j=3|n=12|peak=64     |sumsq=32768 |kappa2=16384/16384  |kappa=1.000000
SYMPY_SUPL|j=3|n=14|peak=128    |sumsq=49152 |kappa2=65536/65536  |kappa=1.000000
SYMPY_SUPL|j=4|n=12|peak=104    |sumsq=30848 |kappa2=86528/36864  |kappa=1.532065
SYMPY_SUPL|j=4|n=14|peak=208    |sumsq=115456|kappa2=346112/147456|kappa=1.532065
SYMPY_SUPL|j=5|n=13|peak=38     |sumsq=24704 |kappa2=23104/131072 |kappa=0.419845
SYMPY_SUPL|j=6|n=14|peak=112    |sumsq=176384|kappa2=401408/409600|kappa=0.989949
```

Every field -- peak, sum of squares, and the exact rational `kappa^2` --
agrees with `acb_sup_levels` on all seven pairs, three levels, both parities.
AGREEMENT.

**(ii) Two disjoint algorithms inside the repo.**  `acb_sup_levels` goes through
`class_population_distribution` (CRT-lifted modular transforms at level `j`);
`acb_sup_period` runs the group-ring degree recursion in `BigInt` seeded only at
`m = j..2j-2`.  They agree at every `m <= 59` for every `j = 2..7`
(47-57 checks per level, zero mismatches, fail-closed).

**(iii) Ledger cross-check.**  `H_4^*(n=40) = 2112512`, exactly the value
ADR-0517 pins as the coefficient-two refutation witness at `(19,40,4)`.
Level energies agree with `exact_conductor_second_moment` at every level of
`(6,13)` and `(11,24)`.

**(iv) Reconciliation with diary 20 (the parallel audit).**  We agree on every
overlapping quantity, from disjoint computations:  `(CEIL)` = Lemma S6;
`(K2-EXACT)` = Lemma S5; the `(11,24,3)` attainment (their `sup_3 = 16`, 512
argmax classes over two cosets of `H_3` -- exactly the preimage of my
`{1, 1+x^3}` under `pi_3`, and `8192/2^9 = 16`); their `max_(j>=4) kappa = 1.9922`
at `(11,24,5)` appears in my table as `kappa_5(24) = 1.9922`.  Their open item
-- "run E-A1 at `j = 4, 5` specifically; `acb_ver_supl` exits 3 the moment any
row produces `kappa > 2`" -- is settled here: **it happens, at `(4,56)` and
`(5,48)`**.  Their observation that diary 11's quoted "31% margin" is `2/1.5234`
over `j >= 6` only, hiding the binding rows, is confirmed and is now moot:
there is no margin, because there is no `K`.

### resource notes

```text
acb_sup_levels identity 6 13 / 11 24        < 1 s / 3 s
acb_sup_levels grid 2 17 5 59               ~ 90 s      (847 layers total)
acb_sup_levels grid 18 19 <band>            ~ 60 s per level
acb_sup_period verify/period j <= 7         < 5 s
acb_sup_period scan 4|5|6 3000              25 s / 45 s / 90 s   (peak RSS < 200 MB)
```

The level-`j` route costs `O((j+n) 2^j)`, so the binding limit is `j`, not
`ell`: `j <= 19` fits the 2 GB budget, and `n` is capped at 59 by the CAS's
signed-CRT domain (the recursion route removes that cap entirely).

## FINDINGS

### (a) Proved rungs

1. **Lemma S1/S2 (PROVED).**  `D_[j](e) = Delta_j(pi_j e)/2^(ell-j+1)` where
   `Delta_j` is the level-`j` sibling difference of short-interval Mangoldt
   counts.  Hence `kappa_j` depends on `(j,n)` only: **`(SUP-L)` has no `ell`
   in it.**  Controlled class-by-class against diary 11's own recursion.
2. **Lemma S3 (PROVED).**  `max_b |Delta_j(b)| = H_j^*`, the ledger's
   population-refinement sibling maximum.  `(SUP-L)` at `K = 2` implies the
   ledger's conjectured `(RF)` at `c = 3` at every level, and is weaker than the
   refuted `c = 2` for `j >= 4`.
3. **Lemma S4/S5 (PROVED).**  `D_[1] = 0`; `kappa_2 = sqrt2` (`n` even) / `1`
   (`n` odd) exactly, `max_b|Delta_2| = 2^floor(n/2)`.
4. **Lemma S6 (PROVED).**  `kappa_j <= 2^((j-1)/2)`, so `(SUP-L)` at `K = 2` is
   a content-free theorem for `j <= 3`.
5. **Lemma S7 (PROVED).**  Level 3 is supersingular with period 24;
   `sup_n kappa_3 = 2` exactly, attained iff `24 | n`.  The proof scheme
   (propagating period check on the order-`(j-1)` group-ring recursion) is
   general and is a proof, not a sample.
6. **Result S8 (PROVED, exact witnesses).**  Levels 4, 5, 6 are NOT
   supersingular: `v_2(Delta) < n/2 - (j-1)` at `(4,14)`, `(5,14)`, `(6,18)`.
   Level 4 fails at degree 14, long before the ledger's level-10 witness.
7. **Result S9 (PROVED).**  The `1/4`-per-level recursion transports `(SUP-L)`
   with loss exactly 1 -- it IS the `ell`-freeness -- so induction on `ell`
   closes no level range and costs nothing.
8. **Result S10 (PROVED).**  `kappa_j = F_j sqrt(fill_j)`; the `(SUP-L)`
   right-hand side at `K = 1` is exactly the Weil bound on the layer's
   root-mean-square.  `(SUP-L)` is a flatness statement.

### (b) Refuted, with exact witnesses

> **`(SUP-L)` at `K = 2` is FALSE.**  `(j,n) = (4,56)`: `H_4^* = 670285824`,
> `H^2 2^3 = 3594264686842871808 > 4 . 9 . 2^56`.  `(j,n) = (5,48)`:
> `H_5^* = 39061504`, `H^2 2^4 = 24412817515872256 > 4 . 16 . 2^48`.  Both
> endpoint-admissible (`ell = 27, 23`, even degrees), both outside diary 11's
> `ell <= 20` window.

Extended: `kappa_4 = 2.8241` at `n = 2224` and `kappa_5 = 3.9207` at `n = 1320`
(exact recursion), i.e. `99.85%` and `98.0%` of their proved ceilings.  **No
absolute `K` is supported by the evidence**; a proof that
`sup_n kappa_j = 2^((j-1)/2)` needs a Kronecker/Weyl closure argument on the
level-`j` Frobenius angles and is OPEN.

Also refuted: diary 11's "`K = 2` ... fits all measured data with a 31% margin".
The margin at `K = 2` is `0%` (attained at `j = 3`, where it is a theorem) and
negative on the open regime.

### (c) The reduced statement that remains

`(SUP-L)` should be retired and replaced.  With `kappa_j <= min(K, 2^((j-1)/2))`
and the exactly re-derived chains:

```text
                          needed saving over the PROVED individual Weil bound
                          at the top conductor level j = ell
  Haar-triangle route          2.4 ell        (the ledger's own, already proved
                                               to imply the endpoint)
  L^4 / fourth-moment route      2 ell^2      (workstream A's (CAB-L) ladder)
  (SUP-L) with absolute K      2^((ell-1)/2)/K   -- exponentially more than
                                                   either route uses
```

so the residual lemma is

> **(TOP-POLY).**  For `n in {2ell+1, 2ell+2}` and every conductor level `j`
> with `ell - 4 log2 ell <= j <= ell`,
> ```text
>       H_j^*  =  max_b |N_j(b) - N_j(b(1+x^j))|  <=  (j-1) 2^(n/2) / (2.4 ell) .
> ```
> Below that window the proved individual Weil bound already suffices.

`(TOP-POLY)` is a **polynomial** improvement of a proved bound, not an
absolute-constant delocalisation statement, and it is what both routes actually
consume.  It is also, at the top level, the same object the lane has been
attacking since the identity-path reduction -- **workstream A's ladder does not
weaken the obligation; measured exactly, it strengthens it by a factor `ell`
relative to the Haar-triangle route.**

### (d) Mechanism

`kappa_j = F_j sqrt(fill_j)` with `fill_j = (1+o(1))/(j-1)` (the
Keating--Rudnick/Katz form factor, verified at `q = 2` fixed where their
`q -> infinity` theorem does not apply) and `F_j ~ 1.10 sqrt(j-1)` (the Gaussian
extreme-value constant for `2^j` samples).  The measured `kappa ~ 1` is these
two `(j-1)`s cancelling -- **not** cancellation in the character family.  This
predicts both the flat `kappa` in the diagonal band and the escape to the
triangle ceiling off-diagonal, and both are observed.

### (e) Data

847 exact `(j,n)` layers (345 of the 406 endpoint `(ell, level)` pairs with
`ell <= 29`), plus exact recursion scans to `n = 3000` at `j = 4,5,6`; all
integers exact, all ratios printed from exact rationals.  Independently
replicated by from-scratch sympy on 7 pairs (all fields), by a second disjoint
in-repo algorithm on ~350 rows, and against the ledger's pinned
`H_4^*(19,40) = 2112512`.

### (f) Next experiments

1. **E-S1.**  Prove `sup_n kappa_j = 2^((j-1)/2)` for `j >= 4` (Kronecker
   closure of the angle vector).  This would convert the `K <= 3.92` refutation
   into "no `K` exists" and permanently close the `(SUP-L)` shape.
2. **E-S2 (highest value).**  Attack `(TOP-POLY)` directly.  It asks for a
   factor `2.4 ell` over Weil at the top conductor level -- one `L`-function
   degree's worth of saving in a family of `2^(ell-1)` characters.  The
   `fill_j = 1/(j-1)` law (S15) is exactly a factor `(j-1)` of that saving
   already present in the SECOND moment; the missing step is transferring it to
   the sup.
3. **E-S3.**  Prove the KR variance law at `q = 2` fixed, `n -> infinity`, for
   the level-`j` family.  Measured to `1.000 +- 0.02` at `j = 17`; it is the
   single input that removes `ell^(1/4)` from the `L^4` chain and `ell` from the
   sup requirement if it can be made uniform.
4. **E-S4.**  Push `j` to 22-24 in the diagonal band (needs a bigger box: the
   `2^j`-cell population table binds, not time).
5. **E-S5.**  Re-price the other resurrected candidates against `(TOP-POLY)`
   rather than against `(SUP-L)`; several were rejected for asking a constant
   where only `2.4 ell` is needed.

### Epistemic ledger for this file

**PROVED**: Lemma S1 (layer = sibling difference), S2 (`ell`-freeness),
S3 (identification with `H_j^*` and the `(RF)` comparison), S4 (`D_[1] = 0`),
S5 (`kappa_2` exactly), S6 (the ceiling `2^((j-1)/2)`), S7 (level 3
supersingular, period 24, `sup kappa_3 = 2`), S8 (levels 4,5,6 not
supersingular, 2-adic witnesses), S9 (recursion transport with loss 1),
S10 (`kappa = F sqrt(fill)`, mean-square = `(SUP-L)` at `K=1`).

**REFUTED with exact witnesses**: `(SUP-L)` at `K = 2` (`(4,56)`, `(5,48)`);
`(SUP-L)` at any `K <= 3.92` (`(4,2224)`, `(5,1320)`); diary 11's "31% margin"
at `K = 2`; the reading that the `2.0000` maximum is a measurement about
cancellation (it is the proved ceiling attained by an algebraic identity);
supersingularity of the conductor filtration at any level `>= 4`.

**MEASURED (finite evidence, no theorem credit)**: every closure ratio and
`K_max` table; the proved-only gap `(1.03) ell` / `(0.73) ell`; the required
savings `2.4 ell` / `2 ell^2`; the KR form factor `fill_j (j-1) -> 1`; the
flatness law `F_j ~ 1.10 sqrt(j-1)`; all 847 layer rows.

**EXTERNALLY REPLICATED**: seven `(j,n)` pairs by from-scratch sympy over
`GF(2)[x]` (peak, `sum Delta^2`, exact `kappa^2`); the Keating--Rudnick
Theorem 2.1 statement quoted verbatim from arXiv:1204.0708v3 with its
`q -> infinity` hypothesis recorded.

**OPEN**: `(TOP-POLY)`; `sup_n kappa_j = 2^((j-1)/2)` for `j >= 4`; the KR
variance law at fixed `q = 2`; the endpoint.

**NO THEOREM CREDIT** is claimed for Lemire's conjecture or for any uniform
estimate.
