# The Plancherel forcing test on `A_psi`: the disproof template, applied and dead

Status: research note, 2026-08-23. Exact computation plus three small proofs.
This is the first application of the Sawin sparsity+Plancherel *disproof*
template (arXiv:2209.02170, digested in
[15-arxiv-techniques-2023-2026.md](15-arxiv-techniques-2023-2026.md) sec. 2.3)
to this lane's cylinder object. The lever was listed there as "one uncounted
statistic, cheap in the existing dumps". It is now counted. **The template
cannot refute `(CYL)`, and the reason is structural, not numerical: the group
Plancherel is taken over has only `< 8 ell` elements, so the forcing can gain at
most a factor `sqrt(8 ell)` over the root-mean-square, and the root-mean-square
is `Theta(ell 2^{-ell/2})` times the `(CYL)` threshold.** Both hypotheses of the template fail
independently: the vanishing locus is *empty* at every computed size, and the
total second moment is below the target threshold-square from `ell = 22` (odd
endpoint) and `ell = 23` (even endpoint) on.

Companions: [07-covariance-phase-face.md](07-covariance-phase-face.md) (the
`A_psi` object and its covariance), [01-target-and-toolkit.md](01-target-and-toolkit.md)
(definitions, `(HWO)`, `(CYL)`), [03-uncertainty-analogy.md](03-uncertainty-analogy.md)
sec. 5 (Barrier I), [00-state-of-the-problem.md](00-state-of-the-problem.md).

Reproduce: `scripts/lemire-signed-trace/lemire_cylinder_plancherel.py`
(exits nonzero on any failed control; `--mutation-controls` verifies that each
of seven deliberate faults trips exactly one named control). Data:
`scripts/lemire-signed-trace/data/plancherel-*.txt`.

## 1. The object, and the Plancherel identity (exact)

`ell = ceil(n/2) - 1`, `c = ceil(log2 ell)`, `a = ell - c - 1`,
`K = ker(E_ell -> E_{a-1})`, `|K| = 2^{ell-a+1} = 2^{c+2}`, so

```text
ell <= 2^c < 2 ell    =>    4 ell <= |K| < 8 ell.                       (K-SIZE)
```

`K` is elementary abelian whenever `a > ell/2` (checked in code as
`CHECK_K_ELEMENTARY`), so every `psi in K^dual` is real-valued and every `A_psi`
is a rational integer. With
`N(g) = sum_{F monic, deg F = n, <F>_ell = g} Lambda(F)` and

```text
A_psi = sum_{F monic, deg F = n, <F>_{a-1} = 1} Lambda(F) psi(<F>_ell)
      = sum_{g in K} N(g) psi(g),
```

`(CYL)` is `|A_psi| < 2^{ell-1}` for every `psi != 1` (fact
`F:gf2-lemire-cylinder-twist-sup-bound`; `(CYL) => (REL) =>` Kaser--Lemire).

**Lemma 1 (Plancherel).** With `TM = sum_{psi in K^dual} |A_psi|^2`,

```text
TM  = |K| sum_{g in K} N(g)^2,                                          (P1)
A_1 = sum_{g in K} N(g) = N_{a-1}(1),                                   (P2)
NTM := sum_{psi != 1} |A_psi|^2 = TM - A_1^2
     = |K| sum_{g in K} (N(g) - A_1/|K|)^2 = |K| * SSD_id.              (P3)
```

*Proof.* `sum_psi A_psi conj(A_psi) = sum_{g,g'} N(g)N(g') sum_psi psi(g g'^{-1})`
and `sum_psi psi(u) = |K| [u = 1]` gives (P1). (P2) is `psi = 1`. For (P3),
with `m = A_1/|K|`,
`|K| sum_g (N(g) - m)^2 = |K| sum_g N(g)^2 - 2|K| m A_1 + |K|^2 m^2
= TM - 2 A_1^2 + A_1^2 = TM - A_1^2`. []

`SSD_id` in (P3) is exactly the identity-cylinder sum of squared deviations that
`scripts/lemire-signed-trace/lemire_cylinders.py` prints (its integer
"variance numerator" is `|K| * SSD_id = NTM`), and `(ICV)`, the branch's
one-sided premise, is `SSD_id < 2^{2ell-2}`. So the whole forcing argument runs
on an object the lane has been printing since note 07 without reading it this
way.

**Corollary 2 (parity).** For every `psi`,
`A_psi = A_1 - 2 sum_{g not in ker psi} N(g)`, hence `A_psi = A_1 (mod 2)`.
**If `A_1` is odd then no `A_psi` vanishes at all** -- the vanishing locus is
empty for a reason with no equidistribution content. Measured: `A_1` is odd at
`(ell,n) = (23,47)` and even at the other 25 endpoints, so this proves `Z = 0`
in one case and the computation shows `Z = 0` in all of them.

**The exact mean.** `sum_{h in E_{a-1}} N_{a-1}(h) = 2^n` exactly (the function
field prime number theorem is an identity), so the cylinder average is
`2^{n-a+1}` and `A_1` is that up to a measured relative deviation `< 5e-3` at
every endpoint (table 1).

**The exact random-model value.** By note 07, for `psi != 1`
`A_psi = 2^{-(a-1)} sum_{chi in C_psi} S_n(chi)`, `C_psi` the coset of the
conductor-`< a` characters; every `chi in C_psi` has conductor `cond(psi)`, so
`deg L(chi,T) = cond(psi) - 1` and RH plus the Sato--Tate/Keating--Rudnick
variance give `E|S_n(chi)|^2 = (cond(psi)-1) 2^n`. Uncorrelated phases across
the coset -- which is precisely note 07's measured "aggregate `C/D ~ 0`" --
then give

```text
E|A_psi|^2 = (cond(psi) - 1) 2^{n-a+1},
NTM_model  = 2^{n-a+1} * Sigma,   Sigma = sum_{psi != 1} (cond(psi) - 1).  (P4)
```

`cond(psi_u) = max_{k in supp u} k 2^{e_k(ell)-1}` (Katz's Swan conductor, note
01 sec. 2.1), and every one of the `c + 2` bit weights lies in `[a, ell]`
(Proposition 5), so `(|K|-1)(a-1) <= Sigma <= (|K|-1)(ell-1)`. Measured
`NTM / NTM_model` over the 26 endpoints: min 0.806, max 1.488, mean 1.069 over 26 endpoints. The model is right; the
residual scatter is sampling noise, because the identity cylinder supplies only
`|K| - 1 <= 127` values, whereas the all-cylinder root mean square that
`lemire_twists.py` already printed matches its (coarser) prediction to
`0.92--0.96` because it averages `2^{a-1}` cylinders.

## 2. The forcing lemma, and its ceiling

**Lemma 3 (forcing).** Let `M = max_{psi != 1} |A_psi|`, let `tau >= 0` and
`Z_tau = #{psi != 1 : |A_psi| <= tau}`. If `Z_tau <= |K| - 2` then

```text
M^2 >= (NTM - Z_tau tau^2) / (|K| - 1 - Z_tau).                          (F)
```

*Proof.* `NTM = sum_{psi != 1} |A_psi|^2 <= Z_tau tau^2 + (|K| - 1 - Z_tau) M^2`. []

At `tau = 0`, `M^2 >= NTM / (|K| - 1 - Z_0)` with `Z_0` the exact-zero count.
`(CYL)` at this `ell` is **false** as soon as the right-hand side of (F) reaches
`2^{2ell-2}`, i.e. as soon as

```text
Z_tau >= |K| - 1 - (NTM - Z_tau tau^2) / 2^{2ell-2}.                     (REFUTE)
```

**Lemma 3' (the empirical form).** Order the nontrivial values
`v_1 >= v_2 >= ... >= v_{|K|-1}`. For every `r <= |K|-1`,
`v_1^2 >= (NTM - sum_{i>r} v_i^2)/r`, which at `r = 1` is an *equality*. So the
exact-histogram version of the forcing is informative only to the extent that
the small values are known and the large ones are not; with the whole histogram
in hand it recovers the true maximum and nothing more. The honest empirical
statistic is therefore (F) maximized over the observed cuts `tau`, reported as
`best_forced` in table 3. It peaks at `1.93` times the threshold at `(12,26)`,
falls below the threshold from `ell = 13` (odd endpoint) and `ell = 16` (even
endpoint) on, and is `0.043` at `(24,49)`.

**Lemma 4 (the ceiling).** For every `tau` and every `Z_tau`, the right-hand
side of (F) is at most `NTM`. Hence

```text
max_{psi != 1} |A_psi| <= sqrt(NTM)  unconditionally,                    (CEIL)
```

and **no vanishing pattern whatever can refute `(CYL)` at a given `ell` unless
`NTM >= 2^{2ell-2}`.** []

(CEIL) is trivial -- Plancherel is an equality, so the largest a single value
can be is the whole mass -- but it is exactly the reach of the template, and it
is what nobody had evaluated.

**Proposition 5 (the template's reach is `Theta(ell^{3/2} 2^{-ell/2})`).**
Write `rms = sqrt(NTM/(|K|-1))`. By (K-SIZE),

```text
sqrt(NTM) = sqrt(|K| - 1) * rms < sqrt(8 ell) * rms:
```

so the forcing gains at most `sqrt(8 ell)` over the root mean square. For the
size of the mean square itself, substitute the model (P4). Since
`a - 1 = ell - c - 2` we have `n - a + 1 = n - ell + c + 2`, so

```text
sqrt(NTM_model) / 2^{ell-1} = sqrt(Sigma) * 2^{(n - 3 ell + c + 4)/2}.
```

Every K-bit weight lies in `[a, ell]`: a bit at odd `k` exists exactly when
`e_k(ell) > e_k(a-1)`, i.e. when some `k 2^m` lands in `(a-1, ell]`, and that
`k 2^m` **is** the weight. Hence `(|K|-1)(a-1) <= Sigma <= (|K|-1)(ell-1)`, and
with `|K| = 2^{c+2}`, `ell <= 2^c < 2 ell` and `n in {2ell+1, 2ell+2}`,

```text
8 ell^{3/2} 2^{-ell/2}  <=  sqrt(NTM_model)/2^{ell-1}  <=  32 ell^{3/2} 2^{-ell/2}.  (REACH)
```

(REACH) is asserted in code as `CHECK_REACH_BRACKET` and verified against the
exact `Sigma` for every `ell` in `11..400` at both endpoints.

So the template's absolute ceiling drops below the `(CYL)` threshold at
`ell ~ 21` and then loses a factor `sqrt 2` per unit of `ell`. At the first row
where `(HWO)`/`(CYL)` is actually claimed, `ell = 200` (`c = 8`, `n = 401`),
the exact model (P4) gives reach `3.21e-26` at `n = 401` and `4.54e-26` at
`n = 402`, inside the bracket `[1.79e-26, 7.14e-26]`: **the template is short of
refuting `(CYL)` by a factor `3e25`.** The bracket (REACH) was checked against
the exact `Sigma` at every `ell` in `plancherel-model-reach.txt`
(`12 <= ell <= 24`, then `32, 33, 48, 64, 65, 100, 128, 129, 200, 512, 1024`),
and the *measured* `sqrt(NTM)/2^{ell-1}` -- which differs from the model only by
the sampling factor `sqrt(NTM/NTM_model) in [0.90, 1.22]` -- lies inside it at
all 26 endpoints. []

**Why the reach is so small: `K` is polynomially large by construction.**
Sawin's argument works because his Plancherel group
`(1 + T^{-1}F_q[[T^{-1}]])^x / (1 + T^{-n}...)^x` has `~q^{n-1}` characters
while `Kl_k` is supported on `q^{~2n/(p^v+1)}` of them; the forcing gain is
`q^{n(1 - 2/(p^v+1))/2}`, *exponential in the parameter*. Here the group is
`E_ell / E_{a-1}`, and `a = ell - ceil(log2 ell) - 1` is chosen -- by the Haar
telescope, not by us -- so that only `c + 2 = O(log ell)` coefficients are free.
`|K| < 8 ell` is therefore not an accident of the parameters but a feature of
the reduction, and any sparsity/concentration argument on `K` is capped at
`sqrt(8 ell)`. **This alone kills the transplant, before any data.**

**Proposition 6 (the same identity in the other direction).** By (CEIL),

```text
|K| * sum_{g in K} (N(g) - A_1/|K|)^2 < 2^{2ell-2}   =>   (CYL)  =>  (REL).
```

That is: a single second-moment bound on the identity cylinder -- `(ICV)`
strengthened by the factor `|K| < 8 ell` -- implies `(CYL)` with no
per-character information at all. It is verified exactly at `ell = 22` (odd
endpoint), `23` and `24` (table 1, column `ceiling/thr < 1`). This is not a new
route to `(REL)` (unstrengthened `(ICV)` already gives `(REL)`), and it does not
evade Barrier I: note 03 sec. 5's fake population
`F = m + c(2^{a-1-ell} 1_K - delta_1)` has, for every `psi != 1`,
`A_psi(F) = -c` (the `m` term and the `1_K` term both annihilate a nontrivial
character of `K`), with `c ~ 2^{n-ell} in [2^{ell+1}, 2^{ell+2}]`. So `F`
violates `(CYL)` outright, by a factor 4 (odd `n`) to 8 (even `n`), and violates
the hypothesis of Proposition 6 by a factor `128 ell` to `512 ell`. What Proposition 6 *does* record is how much slack `(CYL)`
carries: at `ell = 24` the *entire* nontrivial second moment is already a
factor 3 to 6 below the threshold-square, and by (REACH) that factor grows like
`2^{ell}/ell^3`, so `(CYL)` is very far from tight -- the quantitative form of
note 07's "doubly-exponential margin".

## 3. The measurements

### 3.1 What was computed

Exact `Lambda`-weighted class populations from the branch CAS
(`axeyum-gf2-dump-populations <ell> <degree>`, built in the lane snapshot
`snap-lemire-signed-trace-47fd7b440`), for **every** `ell` in `12..24` and
**both** endpoints `n in {2ell+1, 2ell+2}` -- 26 dumps. `ell = 12` and every
odd `ell` in `13..21` are new to the lane's twisted-sum data:
`data/twisted-sums-ell14-24.txt` covered only the even `ell` plus `23`. Cost:
0.06 s at `ell = 12` rising to 685 s and 3.5 GB at `ell = 24`, which is the
binary's hard cap (`limits.max_ell = 24`, `max_group_order = 1 << 24`).

Every number below is an exact integer. The controls that gate the run are
listed in the script docstring; the load-bearing ones are

* `CHECK_PARSEVAL` -- (P1), with the two sides computed by *independent* routes
  (the left from the transform of the kernel built from generators, the right
  by selecting, out of all `2^ell` classes, those projecting to the identity of
  `E_{a-1}`). Plancherel is an identity for whatever vector it is handed, so it
  detects nothing unless its two sides come from different routes; this is why
  the naive form of the control survives a corrupted population and the
  two-route form does not (mutation control `perturb_population`).
* `CHECK_DIRECT_VS_WHT` -- direct `|K| x |K|` character summation against the
  fast Walsh--Hadamard butterfly.
* `CHECK_NTM_VS_SSD` -- (P3) against the cylinder sum of squared deviations.
* `CHECK_PARITY` -- Corollary 2.
* `CHECK_FORCING_SOUND` -- the forcing bound (F) never exceeds the truth.

Independent cross-check outside the script: the identity-cylinder row of
`lemire_twists.py`'s `A` matrix agrees with this script's spectrum *exactly*,
element by element, at `(14,29), (14,30), (16,33), (18,37)`, and the maxima
reproduce `data/twisted-sums-ell14-24.txt` verbatim (e.g. `640235` at
`(23,47)`, `717506` at `(24,49)`).

### 3.2 Table 1 -- the forcing test, per endpoint

`NTM = sum_{psi != 1} A_psi^2` exactly; `Z` the exact-zero count;
`M = max_{psi != 1} |A_psi|`; `forced = sqrt(NTM/(|K|-1-Z))`, the (F) bound at
`tau = 0`; `ceiling = sqrt(NTM)`, the template's absolute reach (Lemma 4);
threshold `= 2^{ell-1}`. `REFUTABLE` is `NTM >= 2^{2ell-2}`: **NO means no
vanishing pattern whatever can refute `(CYL)` at that size.**

```text
ell   n  |K|            A_1   A_1/2^(n-a+1)                      NTM  NTM/model    Z    max/thr  forced/thr  ceiling/thr  REFUTABLE
 12  25   64         525376       1.0020752                302393088    0.9069    0     2.4297      1.0698       8.4909  YES
 12  26   64        1049088       1.0004883                637024256    0.9552    0     4.0059      1.5527      12.3239  YES
 13  27   64        1043344       0.9950104                672956928    0.9181    0     1.7383      0.7979       6.3334  YES
 13  28   64        2099168       1.0009613               2181638144    1.4882    0     4.0898      1.4367      11.4033  YES
 14  29   64        2096672       0.9997711               1288331008    0.8062    0     1.3062      0.5520       4.3815  YES
 14  30   64        4198936       1.0011044               2905795008    0.9092    0     2.4189      0.8290       6.5803  YES
 15  31   64        4194084       0.9999475               3576431344    1.0336    0     1.2053      0.4599       3.6501  YES
 15  32   64        8384696       0.9995337               9523760064    1.3761    0     2.5356      0.7504       5.9564  YES
 16  33   64        8390614       1.0002391               9221902236    1.2380    0     0.9215      0.3692       2.9306  YES
 16  34   64       16771572       0.9996636              14631816304    0.9821    0     1.2083      0.4651       3.6915  YES
 17  35  128       33541376       0.9996109              59304421632    0.9244    0     0.8710      0.3297       3.7159  YES
 17  36  128       67126528       1.0002632             147464487424    1.1493    0     1.6138      0.5200       5.8595  YES
 18  37  128       67113302       1.0000661             157713451804    1.1526    0     0.8099      0.2689       3.0299  YES
 18  38  128      134207508       0.9999239             254431625072    0.9297    0     0.8716      0.3415       3.8484  YES
 19  39  128      134223376       1.0000421             384499146496    1.3226    0     0.5405      0.2099       2.3654  YES
 19  40  128      268299416       0.9994932             727856149952    1.2518    0     0.8677      0.2888       3.2545  YES
 20  41  128      268543482       1.0004024             671285094876    1.0906    0     0.4555      0.1387       1.5627  YES
 20  42  128      537055156       1.0003432            1461763190896    1.1874    0     0.6114      0.2046       2.3060  YES
 21  43  128      536814022       0.9998940            1122774352348    0.8642    0     0.2729      0.0897       1.0105  YES
 21  44  128     1073931904       1.0001770            2931813756416    1.1283    0     0.3624      0.1449       1.6329  YES
 22  45  128     1073601946       0.9998697            2812503518812    1.0284    0     0.1970      0.0710       0.7997  NO
 22  46  128     2147705892       1.0001035            5747108637168    1.0507    0     0.3002      0.1014       1.1431  YES
 23  47  128     2148019381       1.0002495            5535780638599    0.9640    0     0.1526      0.0498       0.5610  NO
 23  48  128     4294113592       0.9998012           12886963708864    1.1221    0     0.2340      0.0759       0.8559  NO
 24  49  128     4295465196       1.0001159           11122178327408    0.9245    0     0.0855      0.0353       0.3976  NO
 24  50  128     8590236226       1.0000351           26251496371452    1.0911    0     0.1458      0.0542       0.6108  NO
```

### 3.3 Table 2 -- the trend, and the extrapolation

```text
  ell     n   |K|      Sigma   model reach  measured ceiling/thr   ratio   bracket 8..32 ell^1.5 2^-ell/2
   12    25    64        636    8.9163e+00       8.4909           0.952   [5.196e+00,2.078e+01]
   12    26    64        636    1.2610e+01      12.3239           0.977   [5.196e+00,2.078e+01]
   13    27    64        699    6.6097e+00       6.3334           0.958   [4.143e+00,1.657e+01]
   13    28    64        699    9.3475e+00      11.4033           1.220   [4.143e+00,1.657e+01]
   14    29    64        762    4.8798e+00       4.3815           0.898   [3.274e+00,1.310e+01]
   14    30    64        762    6.9011e+00       6.5803           0.954   [3.274e+00,1.310e+01]
   15    31    64        825    3.5904e+00       3.6501           1.017   [2.567e+00,1.027e+01]
   15    32    64        825    5.0775e+00       5.9564           1.173   [2.567e+00,1.027e+01]
   16    33    64        888    2.6339e+00       2.9306           1.113   [2.000e+00,8.000e+00]
   16    34    64        888    3.7249e+00       3.6915           0.991   [2.000e+00,8.000e+00]
   17    35   128       1912    3.8649e+00       3.7159           0.961   [1.549e+00,6.195e+00]
   17    36   128       1912    5.4658e+00       5.8595           1.072   [1.549e+00,6.195e+00]
   18    37   128       2039    2.8222e+00       3.0299           1.074   [1.193e+00,4.773e+00]
   18    38   128       2039    3.9912e+00       3.8484           0.964   [1.193e+00,4.773e+00]
   19    39   128       2166    2.0568e+00       2.3654           1.150   [9.150e-01,3.660e+00]
   19    40   128       2166    2.9088e+00       3.2545           1.119   [9.150e-01,3.660e+00]
   20    41   128       2293    1.4964e+00       1.5627           1.044   [6.988e-01,2.795e+00]
   20    42   128       2293    2.1163e+00       2.3060           1.090   [6.988e-01,2.795e+00]
   21    43   128       2420    1.0870e+00       1.0105           0.930   [5.316e-01,2.126e+00]
   21    44   128       2420    1.5373e+00       1.6329           1.062   [5.316e-01,2.126e+00]
   22    45   128       2547    7.8856e-01       0.7997           1.014   [4.031e-01,1.612e+00]
   22    46   128       2547    1.1152e+00       1.1431           1.025   [4.031e-01,1.612e+00]
   23    47   128       2674    5.7133e-01       0.5610           0.982   [3.047e-01,1.219e+00]
   23    48   128       2674    8.0798e-01       0.8559           1.059   [3.047e-01,1.219e+00]
   24    49   128       2801    4.1347e-01       0.3976           0.962   [2.296e-01,9.186e-01]
   24    50   128       2801    5.8474e-01       0.6108           1.045   [2.296e-01,9.186e-01]
   32    65   128       3817    3.0167e-02            -               -   [2.210e-02,8.839e-02]
   32    66   128       3817    4.2662e-02            -               -   [2.210e-02,8.839e-02]
   33    67   256       7913    4.3435e-02            -               -   [1.636e-02,6.545e-02]
   33    68   256       7913    6.1426e-02            -               -   [1.636e-02,6.545e-02]
   48    97   256      11738    2.9224e-04            -               -   [1.586e-04,6.343e-04]
   48    98   256      11738    4.1329e-04            -               -   [1.586e-04,6.343e-04]
   64   129   256      15818    1.3252e-06            -               -   [9.537e-07,3.815e-06]
   64   130   256      15818    1.8741e-06            -               -   [9.537e-07,3.815e-06]
   65   131   512      32202    1.8908e-06            -               -   [6.902e-07,2.761e-06]
   65   132   512      32202    2.6740e-06            -               -   [6.902e-07,2.761e-06]
  100   201   512      50087    1.2722e-11            -               -   [7.105e-12,2.842e-11]
  100   202   512      50087    1.7991e-11            -               -   [7.105e-12,2.842e-11]
  128   257   512      64395    8.8041e-16            -               -   [6.280e-16,2.512e-15]
  128   258   512      64395    1.2451e-15            -               -   [6.280e-16,2.512e-15]
  129   259  1024     129931    1.2506e-15            -               -   [4.493e-16,1.797e-15]
  129   260  1024     129931    1.7686e-15            -               -   [4.493e-16,1.797e-15]
  200   401  1024     202564    3.2135e-26            -               -   [1.785e-26,7.140e-26]
  200   402  1024     202564    4.5446e-26            -               -   [1.785e-26,7.140e-26]
  512  1025  2048    1043981    1.1295e-72            -               -   [8.004e-73,3.202e-72]
  512  1026  2048    1043981    1.5973e-72            -               -   [8.004e-73,3.202e-72]
 1024  2049  4096    4185102   2.7620e-149            -               -   [1.955e-149,7.821e-149]
 1024  2050  4096    4185102   3.9060e-149            -               -   [1.955e-149,7.821e-149]
```

### 3.4 The vanishing locus is empty, and the small values are unstructured

`Z = 0` at all 26 endpoints, so the questions "do the vanishing `psi` form a
subgroup?" and "are they the `psi` trivial on a sub-cylinder?" are vacuous: the
set is empty. The next-best probe is the *near*-vanishing set. If the small
values were the annihilator of a sub-cylinder they would form a coset of a
subspace of `K^dual`; column `smallest_m_is_coset` tests exactly that for the
`m` smallest. Result: `m = 2` always (trivially -- any two elements are a
coset), `m = 4` once in 26 (at `(21,43)`, against a chance rate of `0.8%` per
endpoint for a random 4-set in `K^dual \ {1}` with `|K| = 128`), and never for
`m = 8` or `16`. Nor does `|A_psi|` depend monotonically on `cond(psi)`: at
`ell >= 20` the per-conductor medians scatter within a factor 2 to 4 with no
ordering by conductor (at `ell = 12` the spread is larger, but there some
conductors carry only one or two characters). There is no structure in the
small values.

```text
ell   n   Z  min|A|/rms  rms/thr  #{|A|<=1e-3 thr}  #{<=1e-2}  #{<=0.05}  best_forced/thr  Z_needed
 12  25   0      0.0347   1.0698                0          0          1          1.3224  0
 12  26   0      0.0126   1.5527                0          0          5          1.9255  0
 13  27   0      0.0135   0.7979                0          0          1          0.9910  23
 13  28   0      0.0489   1.4367                0          0          0          1.8947  0
 14  29   0      0.0062   0.5520                0          1          4          0.6903  44
 14  30   0      0.0200   0.8290                0          0          4          1.0386  20
 15  31   0      0.0372   0.4599                0          0          5          0.5755  50
 15  32   0      0.0319   0.7504                0          0          6          1.0594  28
 16  33   0      0.0081   0.3692                0          1          5          0.4665  55
 16  34   0      0.0302   0.4651                0          0          8          0.5634  50
 17  35   0      0.0210   0.3297                0          1         13          0.4201  114
 17  36   0      0.0066   0.5200                0          1         13          0.6551  93
 18  37   0      0.0179   0.2689                0          4         17          0.3343  118
 18  38   0      0.0106   0.3415                0          5         18          0.4276  113
 19  39   0      0.0106   0.2099                0          6         25          0.2620  122
 19  40   0      0.0013   0.2888                1          8         21          0.3778  117
 20  41   0      0.0130   0.1387                0          6         36          0.1827  125
 20  42   0      0.0025   0.2046                2          6         29          0.2590  122
 21  43   0      0.0032   0.0897                1         15         60          0.1171  126
 21  44   0      0.0219   0.1449                0          1         34          0.1851  125
 22  45   0      0.0003   0.0710                4         20         66          0.0909  -
 22  46   0      0.0150   0.1014                0          6         39          0.1264  126
 23  47   0      0.0113   0.0498                1         21         84          0.0644  -
 23  48   0      0.0119   0.0759                1         18         68          0.0986  -
 24  49   0      0.0098   0.0353                3         29        104          0.0432  -
 24  50   0      0.0152   0.0542                1         12         80          0.0697  -
```

## 4. The layer and conductor families (`(HWO)`): the identity exists, the quantifier does not match

The analogous identity **does** exist, for the *twisted* families. For
`g0 in E_j` put

```text
T_{j,s}(g0) = sum_{chi in X_{j,s}} conj(chi(g0)) S_n(chi),     T_{j,s}(1) = T_{j,s},
A_j(g0)     = sum_{cond chi = j}  conj(chi(g0)) S_n(chi) = 2^{j-1} H_j(g0),
```

`X_{j,s}` the exact-conductor-`j`, exact-order-`2^s` layer and
`H_j(g0) = N_j(g0) - N_j(g0(1+x^j))`.

**Lemma 7.** `sum_{g0 in E_j} |T_{j,s}(g0)|^2 = 2^j sum_{chi in X_{j,s}} |S_n(chi)|^2`,
and both sides are computable from populations alone:

```text
T_{j,s}(g0) = h_{j,s}   P_{j,s}(g0)      - h_{j,s-1}   P_{j,s-1}(g0)
            - h_{j-1,s} P_{j-1,s}(pi g0) + h_{j-1,s-1} P_{j-1,s-1}(pi g0),
sum_{chi in X_{j,s}} |S_n(chi)|^2
            = h_{j,s} Q_{j,s} - h_{j,s-1} Q_{j,s-1}
            - h_{j-1,s} Q_{j-1,s} + h_{j-1,s-1} Q_{j-1,s-1},
```

where `P_{j,s}(g0) = sum_{g in g0 2^s E_j} N_j(g)` is the twisted power-subgroup
population and `Q_{j,s} = sum over cosets C of 2^s E_j of (sum_{g in C} N_j(g))^2`.

*Proof.* `sum_{chi in ann(2^s E_j)} chi(g) = h_{j,s} [g in 2^s E_j]` gives the
twisted four-population formula, exactly as in note 01 sec. 1 with `g0 = 1`.
For the identity, `f(g0) = sum_{chi in X} S_n(chi) conj(chi(g0))` has
`sum_{g0} |f|^2 = sum_{chi,chi' in X} S conj(S') sum_{g0} (chi'/chi)(g0)
= 2^j sum_{chi in X} |S_n(chi)|^2`. The spectral side reduces to the `Q`s
because for a subgroup annihilator,
`sum_{chi in ann(H)} |S(chi)|^2 = |ann(H)| sum_{cosets C of H} (sum_{g in C} N(g))^2`. []

The same for the conductor family, where the identity closes in one line:

```text
2^{2j-2} sum_{g0 in E_j} H_j(g0)^2 = 2^j ( 2^j sum_g N_j(g)^2 - 2^{j-1} sum_h N_{j-1}(h)^2 ).
```

Both are used as hard controls (`CHECK_LAYER_PLANCHEREL`,
`CHECK_CONDUCTOR_PLANCHEREL`), and they are genuine controls because the two
sides are structurally different computations -- a sum of squares of a
four-term combination on one side, a four-term combination of sums of squares
on the other. Both hold exactly at every `(ell, n, j, s)` computed. External
cross-check: `T_{j,s}(1)` from this construction equals, *signed*, the layer sum
`T_{j,s}` printed by the lane's existing `lemire_layers.py` -- 103 layers over
`(ell,n) = (12,25), (14,30), (16,33), (18,38), (20,41)`, zero mismatches.

**But the quantifier is wrong, and that is decisive.** `(HWO)` is
`4 ell |T_{j,s}(1)| <= #X_{j,s}(j-1)2^{ceil(n/2)}` -- a statement at the single
position `g0 = 1`, the identity class, which is exactly the distinguished
position of the whole problem (notes 03 and 06). Lemma 7's forcing produces
"*some* `g0`". So it can refute only the *uniform-in-twist* strengthening of
`(HWO)`, never `(HWO)` itself. That is still worth knowing -- a violation would
say that no proof of `(HWO)` blind to the position `g0 = 1` can work, a
position-blindness barrier in the style of Barrier I -- so it was measured
anyway.

Measured (`plancherel-layers-*.txt`; every `j` in `[a, ell]`, every nonempty
layer, both endpoints):

```text
ell   n  family     #fam  zero% med  zero% max  #max>allow  #id>allow  max(forced/allow)  needed surviving (med)  id rank pct (med)
 12  25  layer       17     1.562     25.000          17          6             4.4035               1.361e+00               61.5
 12  25  conductor    6     1.611      2.344           5          2             1.4347               4.062e-01               28.6
 12  26  layer       17    12.500     50.000          17          9            10.0933               2.179e+00               32.0
 12  26  conductor    6     3.174      9.375           6          1             2.8902               7.656e-01               57.3
 13  27  layer       18     0.000      6.250          16          7             1.9366               9.301e-01               63.4
 13  27  conductor    6     0.977      1.562           5          1             1.2515               2.225e-01               42.6
 13  28  layer       18     6.641     50.000          18          7             5.0025               1.842e+00               35.6
 13  28  conductor    6     2.332      6.250           5          2             1.9089               4.441e-01               48.2
 14  29  layer       20     2.002     12.500          16          7             2.0277               5.593e-01               29.9
 14  29  conductor    6     1.086      2.734           4          1             0.7976               1.091e-01               27.3
 14  30  layer       20     4.883     28.125          20          9             7.4275               1.278e+00               54.5
 14  30  conductor    6     1.544      3.125           4          2             1.4199               2.298e-01               70.5
 15  31  layer       20     0.623      2.344          14          4             2.2481               2.328e-01               44.7
 15  31  conductor    6     0.586      0.928           3          0             0.6401               5.744e-02               66.7
 15  32  layer       20     3.662     43.750          18          7             4.8348               4.890e-01               40.5
 15  32  conductor    6     0.916      3.516           4          0             0.8411               1.234e-01               42.1
 16  33  layer       18     0.391      3.125          12          5             2.5136               1.506e-01               18.0
 16  33  conductor    6     0.378      0.647           2          0             0.4254               3.112e-02                9.0
 16  34  layer       18     2.588     34.375          15          3             2.6399               3.268e-01               44.6
 16  34  conductor    6     0.630      2.148           3          0             0.6276               6.181e-02               22.7
 17  35  layer       23     0.293      3.125          14          6             1.7872               1.250e-01               17.9
 17  35  conductor    7     0.195      0.555           2          0             0.4804               2.139e-02               33.3
 17  36  layer       23     1.709     31.250          17          6             6.7374               2.599e-01               37.3
 17  36  conductor    7     0.391      1.855           3          0             0.6838               4.221e-02               36.7
 18  37  layer       23     0.244      1.562          10          2             1.0244               4.910e-02               50.7
 18  37  conductor    7     0.146      0.331           1          0             0.3386               1.122e-02               76.8
 18  38  layer       23     1.001     12.500          14          3             2.2773               9.805e-02               36.6
 18  38  conductor    7     0.434      1.562           2          0             0.4567               2.266e-02               48.6
 19  39  layer       26     0.101      1.172          11          3             1.6258               2.953e-02               32.1
 19  39  conductor    7     0.098      0.242           0          0             0.2389               5.934e-03               60.5
 19  40  layer       26     0.693     15.625          13          8             3.0556               6.014e-02               39.0
 19  40  conductor    7     0.191      0.781           1          1             0.3488               1.170e-02               15.9
 20  41  layer       25     0.087      0.781           5          2             1.2491               1.202e-02               48.2
 20  41  conductor    7     0.096      0.191           0          0             0.1775               3.044e-03               43.7
 20  42  layer       25     0.495     12.500           9          1             1.6210               2.430e-02               49.9
 20  42  conductor    7     0.239      0.806           0          0             0.2439               6.210e-03               39.8
 21  43  layer       27     0.052      1.562           5          2             1.4882               7.158e-03               61.1
 21  43  conductor    7     0.041      0.129           0          0             0.1232               1.569e-03               31.3
 21  44  layer       27     0.439     12.500           9          5             2.2561               1.442e-02               42.6
 21  44  conductor    7     0.104      0.439           0          0             0.1754               3.173e-03               18.9
 22  45  layer       27     0.027      0.070           3          0             0.9340               4.416e-03               38.3
 22  45  conductor    7     0.043      0.096           0          0             0.0884               8.229e-04               63.5
 22  46  layer       27     0.246      6.641           5          1             1.3438               8.729e-03               51.4
 22  46  conductor    7     0.120      0.403           0          0             0.1262               1.643e-03               35.9
```

Three readings, all against the `(HWO)` allowance
`#X_{j,s}(j-1)2^{ceil(n/2)}/(4 ell)` at the twist in question.

1. **The vanishing loci are far from sparse, and they thin out as `ell` grows.**
   Median zero fraction of `T_{j,s}(.)` over `E_j`: `1.6%` at `ell = 12` down to
   `0.027%` at `(22,45)`; the maximum over layers reaches `50%`, but only in
   layers with `<= 2048` points, where the populations are small integers and
   exact cancellation is cheap. The top-conductor layers (`j = ell`) never
   exceed `12.5%`. Against that, the *required* surviving fraction -- the
   fraction of `E_j` on which the family may survive if the forcing is to reach
   the allowance at all, `mass / (allowance^2 * 2^j)` -- has median `1.36` at
   `ell = 12` and `4.4e-3` at `(22,45)`, falling like `2^{-ell}` because it is
   `~16 ell^2 / (#X_{j,s}(j-1))` and `#X` grows like `2^{ell}`. Measured
   surviving fraction: `0.9997`. So the layer forcing dies too, at rate
   `2^{-ell}` rather than the cylinder's `2^{-ell/2}` -- and at the first
   theorem row (`ell = j = 200`, `q = 16`, `d_s = 12`, `#X ~ 2^{187}`) the
   required surviving fraction is about `2^{-175}`.
2. **The uniform-in-twist `(HWO)` is false at these sizes, but so is `(HWO)`
   itself, so nothing is separated.** The forced bound alone exceeds the
   allowance in at least one layer at every `ell <= 21` (`max(forced/allowance)`
   from `10.1` at `(12,26)` down to `0.93` at `(22,45)`), and the measured
   twisted maximum exceeds it in `17` of `17` layers at `ell = 12` and `3` of
   `27` at `(22,45)`. But the *identity* exceeds it too -- in `6` of `17` layers
   at `(12,25)`, `0` of `27` at `(22,45)` -- exactly as note 01 sec. 3 already
   recorded (ratios up to `0.176` against a requirement of `1/(4 ell)`). At
   `ell <= 24` the cutoff is `Q = 1` and every layer counts as "high", so these
   sizes are not a sample of the `ell >= 200` regime and the failures are
   expected. There is no position-blindness barrier here: the family and the
   identity fail and succeed together.
3. **The identity is not anomalous among its twists.** Its rank among the `2^j`
   twisted values has median percentile between `9%` and `77%` across the 44
   `(ell, n, family)` groups, scattered with no drift -- generic. The single
   rank-1 occurrences are in `s = 1` layers at `ell <= 18`. This is the
   statistical counterpart of Barrier II: the identity class is distinguished
   arithmetically (its orbit under every available symmetry has size `<= 2`)
   and not at all statistically.

**Where the template would have room, and why it still fails.** The natural
group for the template is the *full* dual `E_ell^dual` with `2^ell` characters:
there the ceiling is `sqrt(2^ell (ell-1) 2^n) / ((ell-1) 2^{n/2}) = 2^{ell/2}/sqrt(ell-1)`,
enormous. But that requires `S_n(chi) = 0` off a sparse set, and
`S_n(chi) = -sum_i alpha_i^n` with `|alpha_i| = sqrt 2` (RH) -- vanishing needs
an exact algebraic coincidence among `n`-th powers of Weil numbers, and
Sawin's Kloosterman vanishing is a `p`-adic degeneration special to `Kl_k` with
`p | k`, with no analogue for a generic Hayes character. The measured proxy is
the layer data above: the twisted families keep `> 87%` support at every size
computed and `> 99.7%` at `ell = 22`.

## 5. Verdict

**Outcome (iii) of the three the test could have had: the statistic is not
sharp enough, and it is provably not sharp enough, for a reason that needs no
data.** Both hypotheses of the Sawin template fail here, independently:

* **Sparsity fails, totally.** `Z = #{psi != 1 : A_psi = 0} = 0` at **every one
  of the 26 endpoints** `12 <= ell <= 24`, `n in {2ell+1, 2ell+2}`. Not "small";
  zero. The smallest `|A_psi|` is `0.0003` to `0.049` of the root mean square,
  and at `(23,47)` the vanishing locus is empty *provably*, by Corollary 2,
  because `A_1 = 2148019381` is odd. The question "do the vanishing `psi` form a
  subgroup, or a sub-cylinder annihilator?" is therefore vacuous at every size
  computed: the set is empty.
* **Mass fails, and this is the decisive half.** The template's absolute
  ceiling `sqrt(NTM)/2^{ell-1}` (Lemma 4) drops below `1` at `ell = 22` (odd
  endpoint), `23` (even endpoint), and thereafter falls by `sqrt 2` per unit of
  `ell`. From `ell = 22` on, **no vanishing pattern whatsoever -- not even
  `A_psi = 0` for all but one `psi` -- can force `max |A_psi| >= 2^{ell-1}`.**
  The forcing lemma is not merely unhelpful; it is vacuous, and by Proposition
  5 it stays vacuous for every larger `ell`, by a factor `~ 2^{ell/2}/ell^{3/2}`.

The exact vanishing count that *would* refute `(CYL)`, so that this is decisive
rather than suggestive, is column `Z_needed` of table 3: it rises from `0` at
`(12,25)`, `(12,26)` and `(13,28)` -- where Plancherel alone already refutes
`(CYL)`, with no sparsity input, and the measured `max/thr` of `2.43`, `4.01`
and `4.09` confirms it directly -- through `126` of `127` at `(22,46)`, to
**impossible** at `(22,45)`,
`(23,47)`, `(23,48)`, `(24,49)`, `(24,50)`. There is nothing left to compute:
extending to `ell = 25, 30, 200` cannot change the answer, because the ceiling
is a closed form in `ell` (Proposition 5, evaluated exactly in
`plancherel-model-reach.txt`): `0.030` of the threshold at `ell = 32`,
`1.3e-6` at `ell = 64`, `3.2e-26` at `ell = 200`.

**What this does and does not say about `(CYL)`.** It does **not** prove
`(CYL)`. It says that this route to *dis*proving it is closed, and it explains
why in one sentence: `|K| < 8 ell`, so the group is polynomially small and a
concentration argument on it gains at most `sqrt(8 ell)`. It also shows -- and
this is the only positive by-product -- that `(CYL)` holds at every `ell` in
`22..24` for a reason weaker than any per-character estimate (Proposition 6:
one second-moment inequality), which quantifies how much slack the sufficient
statement carries.

## 6. Consequences for the roadmap and the public PDF

* **`(CYL)` is not refuted; nothing has to be retracted, and the PDF's finite
  claim is confirmed at six sizes it had never seen.** The fact
  `F:gf2-lemire-cylinder-twist-sup-bound` states `(CYL)` for `ell >= 200`, and
  the roadmap paper (`paper/main.tex` of the sibling repository) says: "Exact
  computation for `14 <= ell <= 24` at both endpoints finds ... `(CYL)` true
  from `ell = 16` (`n` odd) and `ell = 18` (`n` even) on". This sweep covers
  `12 <= ell <= 24`, adding `ell = 12` and the odd `ell = 13, 15, 17, 19, 21`
  that the lane had never computed, and **the claim holds exactly as stated**: the odd
  endpoints are true from `ell = 16` on (`max|A_psi|/2^{ell-1} = 0.9215,
  0.8710, 0.8099, 0.5405, 0.4555, 0.2729, 0.1970, 0.1526, 0.0855` at
  `ell = 16, ..., 24`) and the even endpoints from `ell = 18` on (`0.8716,
  0.8677, 0.6114, 0.3624, 0.3002, 0.2340, 0.1458` at `ell = 18, ..., 24`),
  with every earlier endpoint false. Two sentences can now be added to that
  paragraph: the earlier failures are *predicted*, not anomalous -- the model
  reach `Theta(ell^{3/2} 2^{-ell/2})` of Proposition 5 exceeds 1 below
  `ell ~ 21`, and the model's exact form (P4) matches the measured ceiling
  within a factor `[0.90, 1.22]` at every one of the 26 endpoints (table 2)
  -- and the Plancherel forcing can no longer
  disprove `(CYL)` at any size, whatever the vanishing locus does.
* **`(REL)` is untouched.** `(CYL) => (REL)` is one-directional, so even a
  refutation of `(CYL)` would have left `(REL)` open. No refutation occurred.
* **Two open leads should be closed rather than carried.** Note 15 sec. 2.3 and
  sec. 4, and diary Entry 5 and its addendum, all say the transplant "is one
  measurement away" and that "the lane's existing `A_psi` dumps already contain
  the vanishing locus; nobody has counted it". It is counted: the locus is
  empty at every size, and a full locus would not suffice from `ell = 22` on.
  The lever is spent -- like the Gorodetsky--Kovaleva lever before it, correct
  in its own setting and vacuous in ours, and for the same kind of reason
  (there, `~2 j ln j` single-position characters against `2^j`; here,
  `< 8 ell` characters against a `2^{ell/2}` deficit).
* **The transferable lesson.** A sparsity+Plancherel disproof gains at most the
  square root of the *size of the group Plancherel is taken over*. Before
  transplanting one, compare that square root with the ratio between the
  family's root-mean-square and the target threshold. Here the comparison is
  `sqrt(8 ell)` against a root-mean-square that is `Theta(ell 2^{-ell/2})` times
  the threshold, and it is settled at `ell ~ 21`
  with no arithmetic input at all; the same one-line test kills the transplant
  onto the layer family for a different reason (the quantifier), and would
  leave room only on the full dual `E_ell^dual`, where the required vanishing
  theorem for `S_n(chi)` contradicts RH-driven genericity.

## 7. Reproducibility

```sh
# populations (branch CAS, lane snapshot; the third argument is REQUIRED at
# ell = 24 -- the default table-cell cap rejects it and the binary then writes a
# ZERO-BYTE dump while the shell loop continues, which is how this note nearly
# reported ell = 24 from an empty file)
axeyum-gf2-dump-populations <ell> <n> [max_table_cells]   # 1300000000 at ell=24

# the statistic, its controls, and the data files
python3 lemire_cylinder_plancherel.py --dumps <dump>... --out-dir data --layers
python3 lemire_cylinder_plancherel.py --model-extrapolation --out-dir data
python3 lemire_cylinder_plancherel.py --mutation-controls --dumps <one dump>
```

Data files (`scripts/lemire-signed-trace/data/`):
`plancherel-cylinder-ell12-24.txt` (table 1),
`plancherel-model-reach.txt` (table 2, the closed-form extrapolation),
`plancherel-cylinder-forcing.txt` (table 3),
`plancherel-layers-ell12-22.txt` (table 4 and sec. 4),
`plancherel-cylinder-spectra.txt` (the full exact multiset `{A_psi}`, all
`26 * |K|` values with their Swan conductors).

The layer sweep stops at `ell = 22`: its exact controls are arbitrary-precision
sums of squares over `2^j` points and the cost is `~30 s` at `ell = 22`, `~10x`
that at `ell = 24`, for a section whose conclusion (the quantifier mismatch) is
independent of size. The cylinder statistic, which is the point of the note,
runs on all 26 endpoints in under 5 s once the dumps exist.
