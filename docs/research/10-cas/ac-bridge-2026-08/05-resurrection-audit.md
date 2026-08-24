# AC-Bridge 05: the resurrection audit

Workstream: re-measure the `ell`-scaling of every phase-erasing / aggregation
shortcut the gf2-lemire lane refuted, and re-test each one against the WEAK
sufficient target `M_4 < 2^(4(n-ell))` instead of the strong allowance
`K_4 <= M_2^2` (`R_0 <= 4`) it was originally refuted against.

Date opened: 2026-08-20.
Charter: `docs/research/10-cas/ac-bridge-2026-08/00-charter.md`.
Proposed by: sweep-09 FINDINGS (d), experiment **E3**
(`docs/research/10-cas/adhoc-blocker-sweep-2026-08-20/09-additive-combinatorics.md`).

Epistemic labels: PROVED (argument written out) / REFUTED (exact witness) /
OPEN. Finite computation is evidence, never a theorem.

## Log

### 2026-08-20T18:05 -- required reading complete

Read in order: `00-charter.md`; sweep-09 (all 722 lines); sweep `00-synthesis.md`;
`docs/plan/status/52-gf2-lemire.md` (all 759 lines, both the status block and
the landed-changes table); and the refutation sections of the canonical note
`docs/research/10-cas/lemire-half-degree-irreducibles.md` (lines 1550-1610,
2075-2110, 2760-2900, 3190-3230, 3340-3480, 3500-3545, 3820-3860), located by
`grep -n "refut\|shortfall\|misses by\|loses factor\|absolute values\|Cauchy"`.

Worktree state at open: `git status --porcelain` shows another lane holding
uncommitted edits in `crates/axeyum-cas/src/gf2.rs` and
`crates/axeyum-cas/src/gf2_hayes.rs` (it has already landed
`weak_fourth_moment_endpoint_ledger` and an `EfronSteinSpectralWeight*` pair
in the working copy, plus ADR-0563/0564 and the fact file
`F-gf2-hayes-weak-fourth-moment-endpoint-bound.json`). I write only this diary
and new `crates/axeyum-cas/examples/acb_ra_*.rs` files, per the charter.

### 2026-08-20T18:20 -- the audit's central correction: every refutation was measured against a LANE-PINNED candidate, not against what the endpoint needs

Before measuring anything I had to fix what "the allowance" is, because the
brief's phrasing ("refuted against the STRONG allowance `M_2^2`") is true for
the fourth-moment shortcuts but not for the majority of the ledger's refuted
items, which live in the identity-path / connected-trace route and were
refuted against a *different* pinned number, `2^(2ell-2)`.

There are exactly three endpoint-necessary allowances in this lane, and each
refuted shortcut is a step inside one of the three routes. Stating them
separately is the whole content of this entry.

**(W-D) direct discrepancy.**  `N_ell(1) > (proper prime powers)` is the
endpoint. Since `N_ell(1) = 2^(n-ell) + D_1`, it suffices that
`|D_1| < 2^(n-ell) - PP`.

**(W-4) fourth moment.**  `max_e |D_e|^4 <= M_4`, so (W-D) follows from

```text
M_4 < 2^(4(n-ell))          -- sweep-09 (MIN), the weak target.
```

**(W-CT) connected top-conductor trace.  PROVED here (elementary), NEW.**
Let `a` be the lane's first retained exact-conductor level
(`first_top_level`; `a = ell - ceil(log2 ell)` in the reports below) and let
`CT = 2^ell N_ell(1) - 2^(a-1) N_(a-1)(1)` be the telescoped signed trace.
Write `W(c) = (sum_(j=2)^c 2^(j-1)(j-1)) * 2^floor(n/2)` for the individual-Weil
envelope on the coarse levels, so that
`|2^(a-1) D_1^((a-1))| <= W(a-1)` (each exact-level-`j` character has an
`L`-polynomial of degree `j-1`, hence `|S_chi| <= (j-1)2^(n/2)`, and level `j`
carries `2^(j-1)` characters -- this is the lane's own proved degree
distribution). Then

```text
2^ell N_ell(1) = CT + 2^(a-1) N_(a-1)(1) >= CT + 2^n - W(a-1),
```

so the endpoint follows from

```text
|CT| < A_CT := 2^n - W(a-1) - 2^ell * PP .            (W-CT)
```

`W(a-1)/2^n` is `0.020` at `ell=8`, `0.063` at `ell=16`, and tends to `1/4`;
`2^ell PP / 2^n` is below `2%` at both endpoints for `ell >= 12` and is `0`
at the odd endpoint once `n/3 < ell`. So `A_CT` is between `0.94*2^n` and
`0.75*2^n` over the whole measured range and asymptotically.

**The lane's pinned candidate is `2^(2ell-2) = 2^n/8` (odd endpoint).**  It is
therefore **8x stricter than (W-CT)** -- and every "refuted" entry in the
ledger that compares a *square* against `connected_allowance_square` is
**64x stricter than necessary**. That factor 64 is the sole reason several of
the entries below read as three-digit refutations.

Consequence I will use throughout: I re-express each refuted shortcut as the
**bound it actually produces on the endpoint quantity**, and divide by the
endpoint-necessary allowance. A shortcut closes the endpoint at `ell` exactly
when that closure ratio is `< 1`. This is exact-integer arithmetic in every
case; only the printed ratio is floating point.

### 2026-08-20T18:35 -- tooling

Two new example files (no existing source touched):

- `crates/axeyum-cas/examples/acb_ra_scaling.rs` -- probes `core`, `cauchy`,
  `regroup`, `cumulant`, `fomenko`, `cylinder`, `triangle`, `efron`.
- `crates/axeyum-cas/examples/acb_ra_orders.rs` -- probes `mobius`,
  `topmobius`, `orbit`.

```sh
cargo build -p axeyum-cas --example acb_ra_scaling   # Finished dev profile
cargo build -p axeyum-cas --example acb_ra_orders    # Finished dev profile
```

The debug `axeyum-gf2-hayes-fourth-filtration` binary (built 14:01 today, not
rebuilt) supplied an independent second copy of `M_2`/`M_4`:

```sh
./target/debug/axeyum-gf2-hayes-fourth-filtration 9
GF2_HAYES_FOURTH_FILTRATION|status=PASS|ell=9|degree=19|...|second_moment=3339712|fourth_moment=61277466352
```

which agrees with the `core` probe's `class_population_distribution` route
(`m2=3339712`, `m4=61277466352`) at every `ell` in `3..=16`. Wall time for
the filtration binary doubles per `ell` (`ell=16` 7.93 s, `ell=17` 18.6 s,
`ell=18` 40.1 s, peak RSS 59 MB); every run in this diary stayed under
5 minutes and 2 GB.

### 2026-08-20T18:50 -- (L0) the weak-target budget, exact

`B_4(ell,n) = 2^(4(n-ell)) / M_4^true` is the multiplicative budget a
fourth-moment argument may spend. Against it, the *strong* allowance
`K_4 <= M_2^2` offers only `4/R_0 ~ 4/3`, a constant. Exact rows
(`acb_ra_scaling core`, then integer arithmetic in `python3`):

```text
 ell   n      R_0        B_4     log2 B_4      B_4/(4/3)
   8  17   2.900758     12.62      3.66            9.5
   9  19   2.812890     17.94      4.17           13.5
  12  25   3.118420     55.71      5.80           41.8
  14  29   2.993715    156.51      7.29          117.4
  16  33   3.045178    436.14      8.77          327.1
   8  18   4.001664     20.31      4.34           15.2
  12  26   3.183630    201.69      7.66          151.3
  16  34   3.036043   1753.91     10.78         1315.4
```

Fitted (log-linear over `ell=6..16`): `B_4^odd ~ 26 * 2^ell / ell^3`,
`B_4^even ~ 110 * 2^ell / ell^3`; equivalently `M_4^true/2^(4(n-ell))` decays
as `2^(-0.565 ell)` (odd) and `2^(-0.667 ell)` (even), the `ell^3` drag on a
clean `2^(-ell)` being visible exactly as sweep-09 predicted. **The weak
target is `~20 * 2^ell/ell^3` times more generous than the strong one, and
that ratio is the resurrection budget.**

### 2026-08-20T19:05 -- (S1) cellwise fourth-cumulant absolute values: RESURRECTED

The ledger entry: at `(ell,n)=(9,19)` "individual connected cells are over
thirty times larger than their signed total". Exactly: the largest weighted
cell is `397,637,434,736,640` against `|K_4 numerator| = 2,086,965,956,608`,
a factor `190.5`; the ledger's "thirty times" refers to the un-multiplied
cell `K_(7,7,7,7) = -70,637,290,307,584`, factor `33.85`. Both are the wrong
comparison. The shortcut's actual product is a bound on `M_4`:

```text
K_4 <= sum_cells |mult * connected_numerator| =: A(ell,n)
  ==>  M_4 <= (3 M_2^2 + A) / 2^ell .
```

`acb_ra_scaling cumulant 4 15` (reconstruction control
`reconstructed == direct` passed on every row):

```text
 ell   n   sum|cells| = A                     (3M_2^2+A)/2^ell / 2^(4(n-ell))
   7  15   13158446328832                          24.08
   8  17   230376139285248                         13.18
   9  19   13125241053984256                       23.37
  10  21   167845851196981248                       9.36
  11  23   6173593773349663232                     10.74
  12  25   157946261057023250432                    8.58
  13  27   3600279701752796910592                   6.11
  14  29   72482620910741465221888                  3.84
  15  31   1435571519440946522627584                2.38
   8  18   1095811544008448                          3.93
  10  22   825395049403345408                        2.88
  12  26   650391631824020488704                     2.21
  13  28   14999217840610212754432                   1.59
  14  30   289137771289401958115840                  0.958   <-- CLOSES
```

The closure ratio decays as `2^(-0.283 ell)` (odd) and `2^(-0.390 ell)`
(even). **The even endpoint already closes at `ell=14`**; the odd endpoint
extrapolates to closure near `ell=17-18` and has monotone margin growth
thereafter.

Verdict: **RESURRECTED.** Against `K_4 <= M_2^2` the shortcut is off by
`A/M_2^2 ~ 10^2..10^4` at every row and always will be; against
`M_4 < 2^(4(n-ell))` its deficit *decays exponentially* and crosses one
inside the measured range.

### 2026-08-20T19:20 -- (S2) max-to-average: RESURRECTED, with the largest margin in the audit

Ledger: "The tempting pointwise reduction `2^(ell-j) max f_e <= ell sum f_e`
is already false at the root of `(ell,n)=(8,17)`, where its exact ratio is
`6150400/693360 > 8`" -- i.e. `10.84 > ell = 8`.

That compares against the *pinned* linear ceiling `R_j(b) <= ell`, which is
itself an artefact of the `K_4 <= M_2^2` era. Under (W-4) a uniform local
ceiling `R_j(b) <= C` closes the endpoint as soon as

```text
C < C_weak(ell,n) := 2^ell * 2^(4(n-ell)) / M_2^2 ,
```

which is exact and computable. `acb_ra_scaling cylinder 4 14`, worst level
per row:

```text
 ell   n   max_b R_j(b)   max-to-average   C_weak     m2a/C_weak
   8  17      5.686           10.843        36.6        0.296
   9  19      5.917            9.023        50.5        0.179
  10  21      4.298           12.649        66.4        0.190
  12  25      6.761           14.121       173.7        0.081
  14  29      6.969           13.541       468.5        0.029
   8  18      5.791           11.791        81.3        0.145
  12  26      8.226           24.949       642.1        0.039
  14  30      7.106           15.263      1791.8        0.0085
```

The max-to-average ceiling grows like `O(ell)`; `C_weak` grows like
`2^ell/(3 ell)`. Closure ratio decays `2^(-0.398 ell)` (odd),
`2^(-0.447 ell)` (even) and is already `<1` at `ell=6`, the first row
measured. The root form of the same statement (`M_4 <= max_e D_e^2 * M_2`)
gives `0.242` at `(8,17)` down to `0.0163` at `(16,33)` and `0.0040` at
`(16,34)` -- but I flag that the root form is **circular** (it uses the very
`max|D|` being bounded), so only the *cylinder* form above is a usable proof
step, and that is the one tabulated as the verdict.

Verdict: **RESURRECTED**, margin `>34x` at `ell=14` and growing
exponentially. It was refuted only against a target that was itself `2^ell`
too strong.

### 2026-08-20T19:35 -- (S3) family Cauchy and (S8) Hast--Matei: DEAD, but by `sqrt(ell)`, not by 304x

`acb_ra_scaling cauchy 5 17` reproduces the ledger's pinned row exactly
(`ell=12`: `exact_m2=1326053720064`, `saving=304`; `n=26`: `saving=633`).
Re-expressed against (W-CT), the bound family Cauchy actually produces on
`|CT|` is:

```text
 ell   n   sqrt(Cauchy square)/A_CT
   6  13     1.110
   8  17     1.629
  10  21     1.997
  12  25     2.250
  14  29     2.522
  16  33     2.792
  17  35     2.792 (odd, last CRT-admissible row)
   8  18     1.332
  16  34     1.973
```

Growth is `ell^0.76` (odd) / `ell^0.63` (even) -- log-log fits strictly better
than log-linear (rmse `0.07` vs `0.12`). This is exactly
`sqrt((ell-1)/2)`, i.e. the Hast--Matei deficit, i.e. sweep-09's
`(LP-DEFICIT)` at `p=2`, arriving here by a third independent route.
The second-moment route itself (`|D_1| <= sqrt(M_2)`, so `M_2^2` vs
`2^(4(n-ell))`) grows as `ell^3.11` odd / `ell^2.52` even -- again the same
`sqrt(ell)` in `|D|` units.

Verdict: **DEAD (polynomially).**  The loss exceeds one at every `ell >= 6`
and grows without bound, so no `ell_0` rescues it. But the honest size of the
gap is `2.8x`, not `304x`; the ledger's number is `sqrt(64 * 304/...)`-style
inflation from comparing squares against an 8x-too-strict candidate. Recording
the true size matters because a `sqrt(ell/2)` deficit is one logarithm, and
sweep-09 identified exactly one logarithm as the whole content of the
conjecture.

### 2026-08-20T19:50 -- (S4) structural-support `L2` Cauchy: DEAD, exponentially -- the one hard confirmation

`acb_ra_scaling regroup 4 16` reproduces the ledger row at `ell=8` to the
digit (`cellwise=313952`, `orderwise=60416`, `freqwise=162672`,
`layerwise=71280`, `saving=1425` / `1483`). Against (W-CT):

```text
 ell   n   sqrt(support * freq_square_sum)/A_CT
   6  13      2.961
   8  17      4.811
  10  21      5.869
  12  25      6.374
  14  29      7.172
  15  31      8.805
  16  33     17.149
   8  18      2.454
  14  30      4.281
  16  34      7.556
```

Log-linear fit `2^(0.205 ell)` beats the log-log fit on the odd endpoint. The
slack in the CT route is `A_CT/|CT|^true`, which the same table shows grows
like `1/0.0221 = 45` at `ell=16` from `1/0.383 = 2.6` at `ell=6`, i.e. also
exponentially but at a *slower* measured rate than the Cauchy loss over the
last three rows. Structural-support Cauchy therefore consumes its own slack
and more.

Verdict: **DEAD.** The loss is exponential in `ell` with a positive exponent;
the weak target does not rescue it at any `ell_0`.

### 2026-08-20T20:05 -- (S10/S13/S14) the "absolute values across orders / layers" family: RESURRECTED

This is the ledger's ADR-0543 item ("taking orderwise absolute values is not a
justified endpoint bridge") and its relatives. All three were rejected against
`2^(2ell-2)`. Against `A_CT` (`acb_ra_scaling regroup`, and
`acb_ra_orders topmobius`, whose `abs_total` agrees with the regroup report's
`orderwise` field on every shared row -- an independent internal control):

```text
                                 closure ratio vs A_CT
 ell   n   cellwise  orderwise  frequencywise  annihilator-layerwise
   8  17    2.443      0.470        1.266            0.555
  10  21    2.918      0.807        1.322            0.477
  12  25    3.076      0.433        1.338            0.212
  14  29    3.278      0.301        1.393            0.131
  16  33    3.600      0.334        1.535            0.227
   8  18    1.616      0.170        0.801            0.273
  12  26    2.119      0.369        0.837            0.125
  16  34    2.506      0.143        1.062            0.064
```

Fits over `ell=6..16`: orderwise `2^(-0.136 ell)` odd / `2^(-0.064 ell)` even;
annihilator-layerwise `ell^-1.49` odd / `ell^-1.07` even; frequencywise
`ell^0.30` odd (creeping up, straddling 1); cellwise `ell^0.73` odd.

A fourth and simplest member, not previously separated in the ledger, is the
**identity-class Mobius convolution** taken orderwise
(`acb_ra_orders mobius 4 14`). Here the object bounded is `D_1` itself and the
allowance is the plain `2^(n-ell)`:

```text
 ell   n   sum_d d|sum_(u in V_d) M_(n-d)(u^-1)|   2^(n-ell)   ratio
   8  17                238                            512     0.465
  10  21               1627                           2048     0.794
  12  25               3495                           8192     0.427
  13  27               7721                          16384     0.471
  14  29               9750                          32768     0.298
   8  18                183                           1024     0.179
  12  26               5975                          16384     0.365
  14  30              14689                          65536     0.224
```

so the following is a *complete* sufficient statement for the endpoint, with
no cross-order cancellation required at all:

```text
(ORD)   sum_(d=1)^(ell-1) d * |sum_(u in V_d) M_(n-d)(u^(-1))| < 2^(n-ell) .
```

It holds on all 22 measured endpoint rows `4 <= ell <= 14` with the margin
improving from `~0.53` to `0.22-0.30`.

Verdicts: orderwise, annihilator-layerwise and (ORD) **RESURRECTED**;
frequencywise **UNDECIDED** (ratio `1.06-1.54`, drifting up like `ell^0.3`, and
inside the `1.33x` asymptotic tightening of `A_CT`); fully cellwise
**DEAD (polynomially)** at `3.4-3.6x`.

Caveat recorded so nobody over-reads this: these are measurements of *how much
cancellation the shortcut discards*, not proofs of a uniform bound on the
surviving absolute totals. What the resurrection buys is a strictly weaker
theorem obligation -- see FINDINGS (b).

### 2026-08-20T20:20 -- (S7) coefficient-two square-root fibre (RF): RESURRECTED

Ledger: "The coefficient three is a real reserve: the initially tested
coefficient two is false at `(ell,n,j)=(19,40,4)`, where the exact maximum
`2,112,512` exceeds `2,097,152`."  That is `c_req = 2.0146`, a refutation by
`1.5%`, against a *fixed* coefficient.

The affordable coefficient is not fixed. `(RF)` with coefficient `c` gives
triangle numerator `c * sum_j 2^(j-1) j 2^ceil((n-j)/2)`, and the endpoint
needs it below `2^(n-ell+ell) = 2^n`, i.e. `2^(2ell+1)` / `2^(2ell+2)`.
`acb_ra_scaling triangle 4 14`:

```text
 ell   n   c_req (max_j)   c_afford   margin
   8  17      1.062          1.84      1.73
  10  21      1.331          2.76      2.07
  12  25      1.389          4.40      3.17
  14  29      1.519          7.30      4.81
   8  18      1.688          2.83      1.68
  10  22      1.891          4.22      2.23
  12  26      1.964          6.71      3.42
  14  30      1.729         11.11      6.43
```

`c_afford` grows like `2^(ell/2)/ell`; `c_req` grows like `ell^0.3` at most.

Verdict: **RESURRECTED.** The refutation at `(19,40,4)` is a refutation of the
*number two*, not of the estimate. The correct statement is that the
affordable coefficient diverges exponentially, so any bound
`H_j^* <= c(ell) j 2^ceil((n-j)/2)` with `c(ell) = o(2^(ell/2)/ell)` suffices.
The same table shows the plain `L1` Haar triangle `T/2^(2ell)` falling from
`0.95` at `ell=8` to `0.29`/`0.45` at `ell=14`.

### 2026-08-20T20:35 -- (S5/S6) Fomenko packets and Galois orbits: UNDECIDED / split

`acb_ra_scaling fomenko 6 13` reproduces the ledger row exactly: at
`(ell,t,n)=(12,5,26)`, `packets=32`, `29` violate `2^13`, maximum `525056`
(coefficient `65`), packetwise absolute `6433280` against signed `933888`; and
the `t=1` row gives `256` packets, `233` violations, maximum `226816`
(coefficient `28`), absolute `15422336`. `acb_ra_orders orbit 6 12` likewise
reproduces "`(j,n)=(7,15)`, 18 of 28 orbits violate, maximum `1696 > 256`" and
"`(11,24)` order layer `663552` needs coefficient 17".

Against the per-level share `A_lvl = A_CT/(ell-a+1)` of the endpoint
allowance:

```text
 ell   n    a  #top    Fomenko t=1   Fomenko t=window   Galois order-layer
   8  17    4     5       0.862           0.542               0.088
   9  19    4     6       2.177           0.807               0.501
  10  21    5     6       2.044           0.678               0.309
  11  23    6     6       2.191           1.049               0.698
  12  25    7     6       1.940           0.679               0.082
  13  27    8     6       2.406           0.755                 --
   8  18    4     5       0.968           0.823               0.288
  10  22    5     6       1.685           0.668               0.532
  12  26    7     6       1.379           0.575               0.083
```

Verdicts: Fomenko `t=1` **DEAD (polynomially)**, ratio `1.4-2.4` and drifting
up. Fomenko at the connected window `t=ceil(log2 ell)+1` **UNDECIDED**: every
row is below one (`0.54-1.05`) but with no visible trend and with the `1.33x`
asymptotic tightening of `A_CT` still to absorb. Galois order-layer absolute
values **UNDECIDED, leaning resurrected** (`0.08-0.70`, no trend, only seven
rows). None of these is a self-contained proof step anyway -- each still needs
a per-packet / per-orbit estimate, which is the actual missing lemma; what the
re-measurement changes is the *coefficient* that estimate must achieve, from
`1` to `2^(ell/2)`-ish.

### 2026-08-20T20:50 -- (charge 4) independent sympy cross-check of a re-measured row

`sympy_check.py` (scratchpad) re-derives everything from first principles with
no CAS input: it enumerates every monic polynomial over `GF(2)`, factors it
with `sympy.factor_list(..., modulus=2)`, forms the Mangoldt and Mobius
weights, maps each polynomial to its Hayes class by reciprocal truncation
`1 + a_(n-1)x + ... + a_(n-ell)x^ell`, builds the order vectors
`T_d(e) = d sum_(u in V_d) M_(n-d)(e u^(-1))` with its own principal-unit
multiplication and inversion, and reassembles the connected-order cumulant
cells and their absolute total. Output:

```text
SYMPY|ell=4|n=9 |mean=32 |max_abs_d=13|m2=1168 |m4=149776  |k4=-1696256
SYMPY|probe=cumulant|ell=4|n=9 |cells=15|abs_total=37536256  |signed=-1696256 |agree=True
SYMPY|ell=4|n=10|mean=64 |max_abs_d=16|m2=1200 |m4=192576  |k4=-1238784
SYMPY|probe=cumulant|ell=4|n=10|cells=15|abs_total=263524608 |signed=-1238784 |agree=True
SYMPY|ell=5|n=11|mean=64 |max_abs_d=19|m2=4384 |m4=765472  |k4=-33163264
SYMPY|probe=cumulant|ell=5|n=11|cells=35|abs_total=3323332608|signed=-33163264|agree=True
SYMPY|ell=5|n=12|mean=128|max_abs_d=80|m2=23584|m4=73638400|k4=687813632
SYMPY|probe=cumulant|ell=5|n=12|cells=35|abs_total=6067424256|signed=687813632|agree=True
```

Every field agrees with the CAS `core` and `cumulant` probes, **including the
re-measured quantity itself** (`abs_total`: `37536256`, `263524608`,
`3323332608`, `6067424256`) and the cell counts. AGREEMENT, four rows, two
endpoint parities. This is external replication of the S1 row -- the single
verdict this audit's headline rests on.

### 2026-08-20T21:00 -- what I did not measure

- The **valuation envelope `2^(d+1)`** (false at `(9,12,8)`, `672 > 512`) and
  the **coefficient-one valuationwise square-root scale**. These live in
  `binary_berlekamp_annihilator_energy_report`, whose admitted work is
  `O(2^(k+d))` per row; a scaling sweep does not fit the 5-minute bound here.
  Recorded as OPEN with a sizing note in FINDINGS (d).
- The **group-ring centered-logarithm orderwise absolute values**
  (`145632` vs `32` at `(5,12)`). Note that this is a *different*
  decomposition from `identity_class_mobius_convolution` -- the latter has
  `ell-1 = 4` orders at `(5,12)` with absolute total `56`, the former has ten.
  Conflating them would have manufactured a false resurrection; I checked and
  they are distinct objects.
- `sum_chi |S_chi|` (sweep-02's full-family `L1` triangle, refuted from
  `ell=6`). Its deficit is the `p=1` case of sweep-09's `(LP-DEFICIT)` and is
  `~(ell/2)^(1/2)` against (W-D); polynomially DEAD by the same argument as
  S3, and it needs the per-character `L`-polynomial machinery to re-measure.

### 2026-08-20T21:15 -- an exact identity that makes the top candidate's obligation clean.  PROVED.

For the connected-order tensor, write `C_ab = sum_e T_a(e) T_b(e)` and
`P_(a,b,c,d) = C_ab C_cd + C_ac C_bd + C_ad C_bc` for the Wick scale of a
cell, so `K_(a,b,c,d) = 2^ell sum_e T_aT_bT_cT_d - P_(a,b,c,d)`. Then

```text
sum_(a,b,c,d) P_(a,b,c,d)  =  3 (sum_(a,b) C_ab)^2  =  3 M_2^2 ,      (WICK)
```

the sum over **ordered** quadruples, because `sum_(a,b) C_ab
= sum_e (sum_d T_d(e))^2 = sum_e D_e^2 = M_2` (the order reconstruction
`sum_d T_d = D`, which the report checks classwise). The new `kappa` probe
prints the multiplicity-weighted signed pairing total and it equals
`3 M_2^2` on every row, e.g. `(9,19)`: `pairing_signed=33461028728832`
`= 3 * 3339712^2`. Identity confirmed at 18 rows.

So the weak target `M_4 < 2^(4(n-ell))` is, after the Wick pairings are
substituted exactly, precisely

```text
sum_(a<=b<=c<=d) mult(a,b,c,d) K_(a,b,c,d) < 2^(ell+4(n-ell)) - 3 M_2^2 ,
```

and the cellwise-absolute shortcut is the triangle inequality applied to that
left side. That is the statement the S1 measurement tests, and it is the form
in which the obligation is stated in FINDINGS (b).

I also measured the *relative* per-cell version `|K_cell| <= kappa |P_cell|`.
It is **not** the right normalization: cells with a near-vanishing Wick scale
drive `max_cell |K|/|P|` to `36` at `(8,17)`, `9755` at `(9,19)` and `38472`
at `(12,26)` with no trend. The usable graded scale is the absolute pairing
total `Pabs = sum mult |P_cell|`; there
`A/Pabs = 0.230, 0.313, 0.220, 0.229` at `(8,17), (9,19), (12,25), (12,26)`
while the affordable value `(2^(ell+4(n-ell)) - 3M_2^2)/Pabs` is
`0.0161` at `(8,17)` and `0.0253` at `(12,25)` -- i.e. the uniform relative
form still misses by `14.3x` then `8.7x`. Improving, but the *sum* closes long
before the uniform relative bound does, so a proof should target the sum.

### 2026-08-20T21:25 -- last rows, and where the exact tooling stops

`cumulant` declines at `ell=16` (`ResourceLimit { resource:
"connected_order_cumulant_cells", requested: 4495376384, limit: 1600000000 }`)
-- raising the limit is a one-line caller change but the run would exceed the
5-minute bound, so `ell=15` is this audit's last cumulant row. `cauchy`
declines from `n=36` on (`exact conductor second moment ... exceeds the CRT
uniqueness range`), a genuine two-prime representation boundary, not a budget.
`regroup` reached `(17,35)`:

```text
ACB_RA|probe=regroup|ell=17|n=35|first_top=11|support=130048|trace=-247201792
  |cellwise=112415379200|orderwise=5810159616|freqwise=46993647552
  |layerwise=2555437632|freq_sq=733921279600164864
  |cauchy_sq=95444994569442240233472|allow_sq=18446744073709551616|saving=5175
```

giving, against `A_CT = 2^35 - 8194*2^17 = 33,285,996,544`: truth `0.0074`,
structural-support Cauchy `9.28`, cellwise `3.377`, orderwise `0.175`,
frequencywise `1.412`, annihilator-layerwise `0.0768`. Same verdicts, one `ell`
further out.

`cumulant` at `(15,32)`: `abs_total=5790274281755889729402368`, closure ratio
`0.5997` -- the even endpoint's second consecutive closing row.

## FINDINGS

### (a) Complete inventory of refuted phase-erasing / aggregation shortcuts

`A` = the allowance the ledger measured against. `Loss` = the ledger's own
witness. `Closure` = the same shortcut's bound divided by the
**endpoint-necessary** allowance, at the largest `ell` I reached. `Growth` =
log-linear vs log-log fit over `ell=6..16`, whichever had the smaller residual.

| # | Shortcut | Ledger witness (ell, loss) | Refuted against | Route | Closure @ max ell | Growth of closure | Verdict |
|---|---|---|---|---|---|---|---|
| S1 | cellwise fourth-cumulant absolute values | `(9,19)`: largest cell `33.85x` signed total (`190.5x` weighted) | `K_4 <= M_2^2` | (W-4) | `2.379` @ `(15,31)`; **`0.958` @ `(14,30)`, `0.600` @ `(15,32)`** | `2^(-0.283 ell)` odd, `2^(-0.390 ell)` even | **RESURRECTED** |
| S2 | max-to-average (root) `2^(ell-j) max f_e <= ell sum f_e` | `(8,17)`: `6150400/693360 = 10.84 > 8` | `R_j(b) <= ell` | (W-4) | `0.0163` @ `(16,33)`, `0.0040` @ `(16,34)` | `2^(-0.425 ell)` / `2^(-0.506 ell)` | **RESURRECTED** (root form circular; see S2b) |
| S2b | max-to-average, cylinder form, vs `C_weak = 2^ell 2^(4(n-ell))/M_2^2` | same witness | `R_j(b) <= ell` | (W-4) | `0.0289` @ `(14,29)`, `0.0085` @ `(14,30)` | `2^(-0.398 ell)` / `2^(-0.447 ell)` | **RESURRECTED** |
| S3 | family Cauchy over all top characters | `(12,25)`: `303.92`; `(12,26)`: `632.42` | `2^(2ell-2)` squared | (W-CT) | `2.79` @ `(16,33)`, `1.97` @ `(16,34)` | `ell^0.76` / `ell^0.63` | **DEAD (polynomially)** |
| S4 | structural-support `L2` Cauchy `(HC2)` | `(8,17)`: `1425`; `(8,18)`: `1483` | `2^(2ell-2)` squared | (W-CT) | `17.15` @ `(16,33)`, `9.28` @ `(17,35)` | `2^(0.205 ell)` | **DEAD (exponentially)** |
| S5 | Fomenko packetwise absolute values, `t=1` | `(12,26)`: abs `15422336` vs signed `933888`, coefficient `28` | one Weil unit per packet | (W-CT), per level | `2.41` @ `(13,27)` | `~ell^0.5`, drifting up | **DEAD (polynomially)** |
| S5b | Fomenko packetwise, connected window `t=ceil(log2 ell)+1` | `(12,26)`: abs `6433280` vs signed `933888`, coefficient `65` | one Weil unit per packet | (W-CT), per level | `0.755` @ `(13,27)`, `0.575` @ `(12,26)` | no trend, `0.54-1.05` | **UNDECIDED** |
| S6 | Galois orbit, one Weil unit per orbit | `(7,15)`: `1696 > 256`, 18/28 violate | one Weil unit per orbit | (W-CT), per level | needs coefficient `28` vs affordable `~3.6` @ `(12,26)` | linear in `ell` | **DEAD (polynomially)** |
| S6b | Galois exact-order-layer absolute values | `(11,24)`: layer `663552` needs coefficient `17` | `4(level-1)2^ceil(n/2)` | (W-CT), per level | `0.083` @ `(12,26)`, `0.698` @ `(11,23)` | no trend, `0.08-0.70` | **UNDECIDED (leaning resurrected)** |
| S7 | coefficient-two square-root fibre `(RF)` | `(19,40,4)`: `2112512 > 2097152` (`c_req = 2.015`) | fixed coefficient `2` | (W-D) via Haar triangle | `c_req 1.52` vs `c_afford 7.30` @ `(14,29)`; `1.73` vs `11.11` @ `(14,30)` | `c_afford ~ 2^(ell/2)/ell`, `c_req ~ ell^0.3` | **RESURRECTED** |
| S8 | Hast--Matei global second moment | squared ratios `(ell-1)/2` odd, `(ell-1)/4` even | `2^(2(n-ell))` | (W-D) | `49.34` @ `(16,33)` in `M_4` units | `ell^3.11` / `ell^2.52` | **DEAD (polynomially)** |
| S9 | fully cellwise absolute values in the connected Fourier regroup | `(8,17)`: `313952` vs trace `11264` | `2^(2ell-2)` | (W-CT) | `3.60` @ `(16,33)`, `3.38` @ `(17,35)` | `ell^0.73` / `ell^0.91` | **DEAD (polynomially)** |
| S10 | orderwise absolute values (ADR-0543) | `(8,17)`: `60416` vs `2^14 = 16384` | `2^(2ell-2)` | (W-CT) | `0.334` @ `(16,33)`, `0.175` @ `(17,35)` | `2^(-0.136 ell)` / `2^(-0.064 ell)` | **RESURRECTED** |
| S11 | frequencywise absolute values | `(8,17)`: `162672` vs `2^14` | `2^(2ell-2)` | (W-CT) | `1.535` @ `(16,33)`, `1.412` @ `(17,35)` | `ell^0.30` / `ell^0.54` | **UNDECIDED (near miss)** |
| S12 | provisional local ceiling `R_j(b) <= 8` | even `ell=12` row exceeds 8; `ell=15` exceeds 9 | fixed constant `8` | (W-4) | `R_j/C_weak = 0.0149` @ `(14,29)` | `2^(-0.424 ell)` | **RESURRECTED** (the constant was never the binding issue) |
| S13 | annihilator-layerwise absolute values | `(8,17)`: `71280` vs `2^14` | `2^(2ell-2)` | (W-CT) | `0.227` @ `(16,33)`, `0.0768` @ `(17,35)` | `ell^-1.49` / `ell^-1.07` | **RESURRECTED** |
| S14 | identity-class Mobius orderwise absolute values (new row) | -- (not previously separated) | -- | (W-D) | `0.298` @ `(14,29)`, `0.224` @ `(14,30)` | slowly decreasing | **RESURRECTED** |
| S15 | valuation envelope `abs <= 2^(d+1)` | `(9,12,8)`: `672 > 512` | fixed `2^(d+1)` | dyadic fibre energy | not measured | -- | **OPEN** |
| S16 | coefficient-one valuationwise square-root scale | `(10,13,9)`: `2502^2 ~ 1.49*2^(k+d)` | coefficient `1` | dyadic fibre energy | not measured | -- | **OPEN** |
| S17 | group-ring centered-logarithm orderwise absolute values | `(5,12)`: `145632` vs `32` | `2^(n-ell)` | (W-D) | not measured (distinct object from S14) | -- | **OPEN** |
| S18 | full-family `L1` triangle `sum_chi \|S_chi\|` (sweep-02) | exceeds allowance from `ell=6` | `2^(n-ell)` | (W-D) | not measured | `(ell/2)^(1/2)` by sweep-09 `(LP-DEFICIT)` | **DEAD (polynomially)** |
| S19 | single-translation pairing defect | `(9,11,8)` defect inequality fails | -- | dyadic fibre | not re-measurable at scale | -- | **OPEN** |

Controls in the same units (not shortcuts): `M_4^true/2^(4(n-ell))` decays
`2^(-0.565 ell)` / `2^(-0.667 ell)`; `|CT|^true/A_CT` decays from `0.383` at
`(6,13)` to `0.0074` at `(17,35)`. Both confirm the exponential slack that the
whole audit exploits, measured on two independent objects.

### (b) Resurrected candidates, ranked

**1. S1 -- cellwise fourth-cumulant absolute values.**  Best candidate:
non-circular, already closing, and it replaces the lane's hardest requirement
("gcd strata must be recombined across orders before absolute values") by
`~ell^4/24` independent magnitude estimates.

In the charter's notation, with `T_d(e) = d sum_(u in V_d) M_(n-d)(e u^(-1))`
the interval-order components of `D_e` (so `sum_(d=1)^(ell-1) T_d = D`),
`C_ab = sum_e T_a T_b`, `K_(a,b,c,d) = 2^ell sum_e T_aT_bT_cT_d - (C_ab C_cd +
C_ac C_bd + C_ad C_bc)`, what remains to be **PROVED** is exactly:

> **(C4-weak)**  There is an `ell_0` such that for every `ell >= ell_0` and
> both endpoint degrees `n in {2ell+1, 2ell+2}`,
> ```text
> sum_(1<=a<=b<=c<=d<=ell-1) mult(a,b,c,d) |K_(a,b,c,d)|
>       <   2^(ell + 4(n-ell))  -  3 M_2^2 .
> ```

Everything else on the path is already proved or checked in-house:
`(WICK)` `sum mult P_(a,b,c,d) = 3 M_2^2` (this diary, 21:15, verified at 18
rows); the order reconstruction `sum_d T_d = D` (report invariant);
`max_e |D_e|^4 <= M_4` (lane, proved); `M_4 = (3M_2^2 + K_4)/2^ell` (lane,
proved); `(W-4) => endpoint` after the certified degree-400 handoff
(sweep-09 `(MIN)`, and task M1 of the charter re-proves it in-house).
Note that `(C4-weak)` **takes absolute values**, so it needs no cross-order
cancellation at all -- that is the entire point of the resurrection.
Sufficient graded forms are still open: the uniform relative version
`|K_cell| <= kappa |P_cell|` currently misses by `14.3x` at `ell=8` and `8.7x`
at `ell=12` (improving), and is the wrong normalization for cells with a
near-zero Wick scale.

**2. S13 -- annihilator-layerwise absolute values.**  Closure `0.077` at
`(17,35)` with `ell^-1.49` decay; the smallest measured closure ratio of any
CT-route candidate. Obligation: a uniform bound on
`sum_(depth) |sum_(alpha in layer) F(alpha)| < A_CT`.

**3. S14 -- `(ORD)`, orderwise absolute values of the identity-class Mobius
convolution.**  The simplest sufficient statement in the whole audit:
`sum_(d=1)^(ell-1) d |sum_(u in V_d) M_(n-d)(u^(-1))| < 2^(n-ell)`.
One inequality, no conductor filtration, no connected projector, no Wick
subtraction; holds on all 22 measured rows with margin improving to `0.22`.

**4. S10 -- orderwise absolute values of the connected top trace (ADR-0543).**
Closure `0.175` at `(17,35)`. Same shape as S14 one projector further in.

**5. S7 -- `(RF)` with a growing coefficient.**  The affordable coefficient is
`~2^(ell/2)/ell`, the required one `~ell^0.3`; margin `4.8x`/`6.4x` at
`ell=14` and growing. This retires the "coefficient two vs coefficient three"
question entirely.

**6. S2b/S12 -- local cylinder concentration.**  Largest raw margin in the
audit (`34x` at `(14,29)`, `117x` at `(14,30)`, decaying `2^(-0.4 ell)`), but
the resulting obligation is a **delocalization** statement
(`max_e D_e^2 <= C(ell) M_2/2^ell` with `C(ell) = o(2^ell/ell^3)`) whose
difficulty I did not assess and which at the root is circular. Ranked below
S1 for that reason, and flagged rather than sold.

### (c) Definitively-dead confirmations

- **S4, structural-support `L2` Cauchy `(HC2)`** -- the one shortcut whose
  loss grows at a genuinely exponential rate, `2^(0.205 ell)`, faster than the
  measured slack in its own route over the last three rows. It is dead against
  the weak target at every `ell_0`. ADR-0545 stands, and now stands for the
  right reason.
- **S8, S3, S18 -- the whole moment/Cauchy ladder** (`p=1, 2, 4` on the
  character family). Loss `ell^0.5`-ish in `|D|` units at every order,
  independent of `p`, reproducing sweeps 01/03 and sweep-09's
  `(LP-DEFICIT)` from a third direction. Dead, but the honest gap is `~2.8x`
  at `ell=16`, not the `304x`/`633x` the ledger records -- that number is the
  8x-strict candidate, squared.
- **S9, fully cellwise absolute values** in the connected Fourier regroup:
  `3.4-3.6x` over the line and growing `ell^0.73`. Dead; but note it is the
  *coarsest possible* aggregation and it misses by less than a factor four.
- **S5, S6 -- one-Weil-unit-per-packet / per-orbit**: dead as stated
  (coefficient `1` is hopeless; coefficients `28`, `65`, `28` are required at
  `(12,26)`), though the *affordable* coefficient is now `~2^(ell/2)`, so the
  right reading is that these estimates need a growing coefficient rather than
  being wrong in shape.

### (d) Next experiments

1. **E-A (highest value).**  Raise `max_table_cells` in a new
   `acb_ra_*` caller and take `cumulant` to `ell = 16, 17, 18` (declined at
   `ell=16` with `requested: 4495376384`). The odd endpoint's S1 closure ratio
   is `2.379` at `ell=15` and decaying `2^(-0.283 ell)`; the predicted odd
   crossing is `ell = 17-18`. Confirming an odd-endpoint closing row would put
   both parities of the top candidate inside measured range. Cost: the work
   term is `2^ell (sum_(d<ell) 2^d + #cells)`, so `ell=18` is `~40x` `ell=15`;
   needs a fleet probe, not a 5-minute run.
2. **E-B.**  Per-cell law for `K_(a,b,c,d)`: emit the full cell table and fit
   `|K_(a,b,c,d)|` against `2^(2ell)`, against `P_(a,b,c,d)`, and against
   `(C_aa C_bb C_cc C_dd)^(1/2)`. The third is the natural "Gaussian" scale and
   is the one a proof would produce; `(WICK)` then converts a uniform constant
   into `(C4-weak)` directly. Cheap (one report, `ell <= 12`).
3. **E-C.**  Measure S15/S16 (valuation envelope `2^(d+1)`, coefficient-one
   valuationwise square root) across `(ell,k,d)` via
   `binary_berlekamp_annihilator_energy_report`, and re-test against the weak
   allowance. These are the only two inventory rows I could not size; the
   ledger's witnesses (`672 > 512`, `1.49*2^(k+d)`) are both **sub-2x**
   refutations against fixed constants, which is exactly the profile of the
   items that resurrected here.
4. **E-D.**  S17: rebuild the group-ring centered-logarithm order
   decomposition (the `145632` vs `32` row at `(5,12)`) at `ell=6..12` and test
   `sum_orders |contribution| < 2^(n-ell)`. Its `ell=5` loss is `4551x`, far
   worse than S14's `0.44`, so this is the one order-decomposition I expect to
   stay dead -- worth confirming precisely because it is the closest cousin of
   a resurrected candidate and the two are easy to conflate.
5. **E-E (control, cheap).**  Re-run every "closure ratio" in table (a) with
   `A_CT` replaced by its asymptotic floor `0.75 * 2^n` and with the exact
   proper-prime-power subtraction from the lane's own
   `weak_fourth_moment_endpoint_ledger` (`strict_irreducible_fourth_moment_threshold`
   rather than `positivity_only_fourth_moment_threshold`). None of the
   verdicts should move; S11 (`1.41-1.54`) and S5b (`0.54-1.05`) are the two
   that could, and they are the two labelled UNDECIDED for exactly that reason.
6. **E-F.**  The `efron` probe in `acb_ra_scaling.rs` is wired to the other
   lane's new `efron_stein_spectral_weight_report` and was not exercised here;
   it is sweep-09's decisive experiment **E1** for the global-hypercontractivity
   route (charter target (GHC-W)) and is now one command away.

### Epistemic ledger for this file

PROVED: `(W-CT)` with its explicit Weil and proper-power corrections (18:20);
`(WICK)` `sum mult P = 3 M_2^2` (21:15, verified at 18 rows).
MEASURED (finite evidence, no theorem credit): every closure ratio and growth
fit in table (a); all reproduce the ledger's pinned witnesses exactly where
they overlap (`(8,17)` regroup quadruple `313952/60416/162672/71280` and
savings `1425`/`1483`; `(12,25)`/`(12,26)` family-Cauchy savings `304`/`633`;
`(12,26)` Fomenko `525056`, coefficient `65`, absolute `6433280`, signed
`933888`; `(7,15)` orbit maximum `1696 > 256`; `(11,24)` order layer
coefficient `17`; `(9,19)` cumulant `-2086965956608`).
EXTERNALLY REPLICATED: the S1 row at `(4,9)`, `(4,10)`, `(5,11)`, `(5,12)` by
independent sympy brute force over `GF(2)[x]` -- all fields agree, including
`abs_total`.
OPEN: `(C4-weak)` and every other obligation in FINDINGS (b); S15, S16, S17,
S19.
NO THEOREM CREDIT is claimed for Lemire's conjecture or for any lane lemma.
A shortcut labelled RESURRECTED is a candidate for the ladder's rung L2, not a
proof: what has been refuted is its refutation.
