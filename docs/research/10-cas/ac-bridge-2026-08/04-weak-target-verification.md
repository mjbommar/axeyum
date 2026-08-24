# AC-Bridge workstream 04: making (T-weak) load-bearing

Agent field: verification of the weak fourth-moment endpoint target.
Date opened: 2026-08-20T15:55-04:00.
Worktree: `/home/mjbommar/projects/personal/axeyum-gf2-lemire`, HEAD
`6d603a3a84690cc2d6f86de7b6c75dfdaa731581`.

Epistemic labels: PROVED (argument written out here in full), REFUTED (with an
exact witness), OPEN.  Finite computation is EVIDENCE, never a theorem.  Every
number below is an exact integer produced by the repository's CAS; the only
floating point is in printed ratios and logarithms.

New files written by this workstream (examples only; no existing source file
was touched):

```text
crates/axeyum-cas/examples/acb_wt_moments.rs       exact M_2, M_4, K_4, R_0 per row
crates/axeyum-cas/examples/acb_wt_weak_target.rs   EXACT proper-power mass + I_n(1)
crates/axeyum-cas/examples/acb_wt_contractions.rs  the three fourth-order contractions
crates/axeyum-cas/examples/acb_wt_symbolic.rs      symbolic thresholds and crossovers
crates/axeyum-cas/examples/acb_wt_e2prime.rs       the sweep-08 (E2') accumulator
```

## Log

### 2026-08-20T15:55 -- required reading, and one thing already fixed in-tree

Read `00-charter.md`, sweep lane `09-additive-combinatorics.md` (all 722 lines),
sweep lane `07-coding-theory.md` (M_4 sections), sweep lane
`08-boolean-complexity.md` `[t4]`/`[t8]`, the `M_4`/`K_4`/`R_0` sections of
`docs/plan/status/52-gf2-lemire.md`, and
`docs/research/10-cas/lemire-half-degree-irreducibles.md` under
"A sufficient endpoint discrepancy lemma" (the divisor bookkeeping).

Before running anything I checked the working tree and found that the
`gf2_hayes.rs` lane has *already* landed the correction my charge anticipated:
`docs/research/09-decisions/adr-0563-retain-proper-power-margin-in-the-weak-fourth-moment-target.md`
(dated today; it landed on `main` while this workstream was running) plus
`WeakFourthMomentEndpointLedger` and
`ClassPopulationDistribution::fourth_moment_proves_identity_class_irreducible`.
That ADR already says, correctly, that sweep-09's `M_4 < mu^4` proves only
positive Mangoldt mass.  So this workstream is not "discover the correction"; it
is **independent re-derivation, exact measurement, and finding what is still
wrong or still lossy**.  Three things turned out to be, and they are the
substance of this file.

### 2026-08-20T16:05 -- notation fixed, then the implication re-proved from scratch

```text
G       = E_ell = principal units of F_2[x]/x^(ell+1),  |G| = 2^ell
n       = 2 ell + 1 (odd endpoint) or 2 ell + 2 (even endpoint)
<F>     = 1 + a_1 t + ... + a_ell t^ell  in G,  for monic
          F = x^D + a_1 x^(D-1) + ... (a_i = 0 for i > D);  <FG> = <F><G>
<F> = 1 <=> the top ell coefficients of F vanish  (the Lemire shape)
N_n(e)  = sum over monic F, deg F = n, <F> = e of Lambda(F)
mu      = 2^(n-ell),  D_e = N_n(e) - mu,  M_r = sum_e |D_e|^r
I_n(1)  = # monic irreducibles of degree n in the identity class
Pi_n    = sum_(k>=2) sum_(P irred, k deg P = n, <P>^k = 1) deg P
          (the EXACT proper-prime-power Mangoldt mass in the identity class)
Sigma(ell) = sum_(j=2)^ell 2^(j-1) (j-1)^2 = 2^ell (ell^2 - 4 ell + 6) - 6
R_0     = 2^ell M_4 / M_2^2,     K_4 = 2^ell M_4 - 3 M_2^2
```

`sum_e N_n(e) = 2^n` exactly, so `sum_e D_e = 0`; this is checked as an
invariant on every row emitted below.  By definition of `Lambda`,

```text
N_n(1) = Pi_n + n I_n(1).                                            (dagger)
```

**Lemma A (odd endpoint proper-power mass).  PROVED.**
For `n = 2 ell + 1` and `ell >= 1`, `Pi_n = 1`, contributed by `F = x^n`.

*Proof.*  A proper prime power of degree `n` is `P^k` with `k | n`, `k >= 2`.
`n` is odd, so `k` is odd and `k >= 3`, hence `d := n/k <= n/3 <= ell` for
`ell >= 1`.  Because `d <= ell`, the class `<P> = 1 + a_1 t + ... + a_d t^d`
records *every* non-leading coefficient of `P`, so `<P> = 1` forces `P = x^d`.
`G` is a 2-group and `k` is odd, so `g -> g^k` is an automorphism of `G`; hence
`<P>^k = 1 <=> <P> = 1 <=> P = x^d`.  `x^d` is irreducible only for `d = 1`,
which forces `k = n`, `F = x^n`, `Lambda(x^n) = 1`.  QED

**Lemma B (even endpoint proper-power mass).  PROVED bound.**
For `n = 2 ell + 2` and `ell >= 2`,

```text
Pi_n  <=  P_n^sharp  :=  (ell+1) 2^ceil(ell/2)  +  n 2^ceil((ell+1)/2).
```

*Proof, by the three layer types.*

1. `k` odd, `k >= 3`.  Then `d = n/k` is even (as `n` is even and `k` odd) and
   `d <= n/3 <= ell` for `ell >= 2`.  Exactly as in Lemma A, `<P>^k = 1` forces
   `P = x^d`, which is not irreducible for `d >= 2`.  **This layer is empty.**
   The in-tree bound does not use this vanishing; see 16:45 for the cost.
2. `k = 2`, `d = ell + 1`.  An irreducible of degree `ell + 1 >= 2` has
   `P(0) = 1`, and `<P>` determines `a_1, ..., a_ell` while `a_(ell+1) = P(0)`
   is then forced, so `P -> <P>` is *injective* on these irreducibles.  The
   constraint is `<P>^2 = 1`, i.e. `<P> in G[2]`, and
   `|G[2]| = |G/2G| = 2^ceil(ell/2)` (the lane's proved rank of `E_ell/2E_ell`;
   reconfirmed here from `principal_unit_structure` on every row `ell = 2..21`).
   The Mangoldt weight is `deg P = n/2 = ell + 1`.  Layer `<= (ell+1) 2^ceil(ell/2)`.
3. `k` even, `k >= 4`.  Then `d = n/k <= n/4 = (ell+1)/2`.  The number of monic
   irreducibles of degree `d` over `F_2` is at most `2^d / d`, so this layer's
   weighted mass is at most `d (2^d/d) = 2^d <= 2^ceil((ell+1)/2)`.  There are
   fewer than `n` admissible `k`, so the layers together are
   `<= n 2^ceil((ell+1)/2)`.  QED

`P_n^sharp < mu = 2^(ell+2)` holds for every `ell >= 8` by
`P_n^sharp <= 3(ell+1) 2^ceil((ell+1)/2) <= 3(ell+1) 2^((ell+2)/2) < 2^(ell+2)`
whenever `3(ell+1) < 2^(ell/2+1)` (true from `ell = 8`), and it is verified by
exact integer comparison at `ell = 7` as well (`384 < 512`).  It fails at
`ell <= 6`, which is inside the certified finite range.

**Lemma C (Chebyshev at one point).  PROVED, one line.**
`|D_1|^4 <= sum_e |D_e|^4 = M_4`.  Hence `M_4 < X^4 => |D_1| < X`.

**Theorem (T-weak), exact form.  PROVED.**

```text
M_4 < (mu - Pi_n)^4                                                   (W4-exact)
```

implies `I_n(1) >= 1`, i.e. a degree-`n` irreducible with its top `ell`
coefficients zero exists.

*Proof.*  Lemma C gives `|D_1| < mu - Pi_n`, so `N_n(1) = mu + D_1 > Pi_n`.
By `(dagger)`, `n I_n(1) = N_n(1) - Pi_n > 0`.  QED

**Corollary (usable at symbolic `ell`).  PROVED.**  Since `Pi_n <= P_n`, the
same conclusion follows from `M_4 < (mu - P_n)^4` with

```text
P_n = 1                            (odd endpoint,  Lemma A, exact)
P_n = P_n^sharp                    (even endpoint, Lemma B, ell >= 7)
```

so the explicit constants are `mu - P_n = 2^(ell+1) - 1` at the odd endpoint and
`mu - P_n = 2^(ell+2)(1 - theta_ell)` at the even endpoint with
`theta_ell <= 3(ell+1) 2^(-ell/2 - 1) -> 0`.

**Corollary (root-ratio form), PROVED given the lane's proved Weil envelope.**
The lane's proved second-moment envelope is `M_2 <= mu Sigma(ell)`.  Since
`M_4 = R_0 M_2^2 / 2^ell`,

```text
R_0 < 2^ell (mu - P_n)^4 / (mu Sigma(ell))^2                          (WR)
```

implies `(W4)`.

**Corollary (connected form) -- this is the one the ladder should carry.**
`2^ell M_4 = 3 M_2^2 + K_4 <= 3 (mu Sigma)^2 + K_4`, so

```text
K_4  <=  2^ell (mu - P_n)^4 - 3 (mu Sigma(ell))^2                     (WK)
```

implies `(W4)` **whenever the right-hand side is positive**, and the right-hand
side is `~2^(5 ell + 4)` while the lane's live target `K_4 <= M_2^2` is
`~ell^2 2^(4 ell + 2)`.  The gap is a factor `~2^(ell+2)/ell^2`.

**Labelled PROVED.**  Every step above is elementary and self-contained given
two inputs the lane already owns: `|G[2]| = 2^ceil(ell/2)` and the Weil
envelope `M_2 <= mu Sigma(ell)` (the latter only for `(WR)`/`(WK)`, not for
`(W4)` itself).  Nothing here proves `(W4)`; it proves that `(W4)` suffices.

**Correction that matters, and it is NOT the same as the ADR's.**  The
positivity-only form `M_4 < mu^4` proposed by sweep-09 is insufficient, as
ADR-0563 already says.  But the *constant below 1* my charge anticipated is not
`1 - o(1)` in general: it is `1` at the odd endpoint up to the single unit
`x^n`, and `1 - theta_ell` at the even endpoint.  The failure mode is entirely
at small `ell`, and it is a failure of the *bound on* `Pi_n`, not of the fourth
moment.  See 16:45.

### 2026-08-20T16:15 -- first data pass, exact M_2/M_4/K_4/R_0

```sh
cd /home/mjbommar/projects/personal/axeyum-gf2-lemire
cargo build --release -p axeyum-cas --example acb_wt_moments
./target/release/examples/acb_wt_moments 2 18     # 24.1 s, 49.9 MB
./target/release/examples/acb_wt_moments 19 21    # 245.4 s, 404.3 MB
```

`acb_wt_moments` recomputes `M_2`, `M_4`, the raw uncentered moments, the
cumulant and `R_0` from the population vector with its own integer loops and
then asserts agreement with `central_absolute_power_sum` and
`fourth_cumulant_numerator`; it also asserts `sum_e N_n(e) = 2^n` and checks the
closed form `Sigma(ell) = 2^ell(ell^2-4ell+6)-6` against the summation.  All
assertions passed on all 40 rows (a mismatch aborts the row with status=FAIL).

Verbatim sample:

```text
ACB_WT_MOMENTS|status=PASS|ell=9|degree=19|parity=odd|group_order=512|mean=1024|
min_population=836|max_population=1254|max_abs_deviation=230|identity_deviation=-92|
M_2=3339712|M_4=61277466352|K_4=-2086965956608|K_4_sign=-|R_0=2.812889857|...
```

This reproduces the pinned ledger `(9,19)` cumulant `-2086965956608` and the
`(9,19)`/`(9,20)` moments printed by
`./target/release/axeyum-gf2-hayes-fourth-filtration 9`.

### 2026-08-20T16:25 -- independent verification: sympy brute force, and a bug of my own

First-principles cross-check (`scratchpad/sympy_check.py`): enumerate **every**
monic polynomial of degree `n` over `GF(2)`, factor it with
`sympy.Poly(...).factor_list()` over `GF(2)`, apply the von Mangoldt weight, bin
by the top `ell` coefficients.  This shares no code, no algorithm and no
convention with the CAS.

```text
SYMPY|n=7|ell=3|total=128|expected=128|identity=22|mu=16|M_2=96|M_4=2688
SYMPY|n=8|ell=3|total=256|expected=256|identity=24|mu=32|M_2=384|M_4=73728
SYMPY|n=9|ell=4|total=512|expected=512|identity=37|mu=32|M_2=1168|M_4=149776
SYMPY|n=10|ell=4|total=1024|expected=1024|identity=76|mu=64|M_2=1200|M_4=192576
SYMPY|n=11|ell=5|total=2048|expected=2048|identity=45|mu=64|M_2=4384|M_4=765472
SYMPY|n=12|ell=5|total=4096|expected=4096|identity=160|mu=128|M_2=23584|M_4=73638400
SYMPY|n=13|ell=6|total=8192|expected=8192|identity=79|mu=128|M_2=20832|M_4=20044320
SYMPY|n=14|ell=6|total=16384|expected=16384|identity=288|mu=256|M_2=63648|M_4=194446464
```

Every one of these eight rows -- both parities, `ell = 3..6` -- agrees with the
CAS on `M_2`, `M_4` and the identity-class population, **exactly**.  Six rows
were required by my charge; eight were run.  AGREEMENT, no mismatch.

Recorded because the project law says a cross-check disagreement is a finding:
my *first* independent implementation was wrong, not the CAS.  My Rabin
irreducibility test accepted `candidate == 0` in the
`gcd(x^(2^(d/p)) - x, f) = 1` sub-test.  `candidate == 0` means `f` divides
`x^(2^(d/p)) - x`, i.e. `f` is reducible -- it is the strongest possible
rejection, and I was treating it as a pass.  It over-counted irreducibles at
composite degrees only (`deg 6: 10 vs 9`, `deg 8: 33 vs 30`), which is exactly
the kind of defect a smoke test at `deg <= 5` misses.  It was caught by the
`sum_e N_n(e) = 2^n` invariant firing at `(ell,n) = (3,8)`, not by any test I
wrote.  Both my Rust and my Python copies had it; both are fixed.

### 2026-08-20T16:40 -- the exact proper-power mass, and I_n(1) rebuilt from scratch

`acb_wt_weak_target.rs` computes, without the Hayes transform:

* `I_n(1)` by direct enumeration of the `2^(n-ell)` monic degree-`n`
  polynomials in the identity class with a Rabin irreducibility test;
* `Pi_n` **exactly**, by enumerating the irreducibles in each proper
  prime-power layer and testing `<P>^k = 1` in `E_ell`;

and then asserts the reconstruction `(dagger)`: `Pi_n + n I_n(1)` must equal the
CAS class population `counts[0]`.

```sh
./target/release/examples/acb_wt_weak_target 2 12    #  0.5 s
./target/release/examples/acb_wt_weak_target 13 18   # 34.6 s, 51 MB
./target/release/examples/acb_wt_weak_target 19 21   # 340.2 s, 404 MB
```

`reconstruction_ok=true` on **all 40 rows**, `ell = 2..21`, both parities.  This
is an independent confirmation of the CAS Hayes transform at the identity class
by a completely different algorithm, and simultaneously of `(dagger)`, of
Lemma A (`exact_proper_power_mass=1` in every odd row, as Lemma A predicts), and
of the lane's committed `Delta` table.  The odd `I_n(1)` column reproduces sweep
lane 07's independent C enumeration; the even `I_n(1)` column appears to be new.

Master table (exact integers; `Pi_n` exact, `D_1 = N_n(1) - mu`,
`slack = log2((mu-Pi_n)^4 / M_4)`):

```text
 ell   n  par   I_n(1)   Pi_n    N_n(1)      D_1  log2 M_4 log2(mu-Pi)^4   slack  W4x W4lib     R_0
   2   5  odd        1      1         6       -2     6.000        11.229   5.229    t     t  1.0000
   2   6 even        2      4        16        0     9.000        14.340   5.340    t     f  2.0000
   3   7  odd        3      1        22        6    11.392        15.628   4.235    t     t  2.3333
   3   8 even        2      8        24       -8    16.170        18.340   2.170    t     f  4.0000
   4   9  odd        4      1        37        5    17.192        19.817   2.624    t     t  1.7566
   4  10 even        7      6        76       12    17.555        23.432   5.877    t     f  2.1397
   5  11  odd        4      1        45      -19    19.546        23.909   4.363    t     t  1.2745
   5  12 even       12     16       160       32    26.134        27.229   1.095    t     f  4.2366
   6  13  odd        6      1        79      -49    24.257        27.955   3.698    t     t  2.9560
   6  14 even       19     22       288       32    27.535        31.481   3.947    t     f  3.0719
   7  15  odd       20      1       301       45    28.997        31.977   2.980    t     t  2.5846
   7  16 even       28     24       472      -40    31.054        35.723   4.669    t     f  2.7887
   8  17  odd       33      1       562       50    32.343        35.989   3.646    t     t  2.9008
   8  18 even       59     37      1099       75    35.656        39.788   4.132    t     f  4.0017
   9  19  odd       49      1       932      -92    35.835        39.994   4.160    t     t  2.8129
   9  20 even      101     76      2096       48    38.449        43.782   5.332    t     f  3.3796
  10  21  odd      100      1      2101       53    39.474        43.997   4.523    t     t  2.8835
  10  22 even      187     45      4159       63    41.649        47.936   6.287    t     f  2.7306
  11  23  odd      187      1      4302      206    42.881        47.999   5.118    t     t  2.9706
  11  24 even      320    160      7840     -352    45.223        51.886   6.663    t     f  3.1414
  12  25  odd      342      1      8551      359    46.200        51.999   5.799    t     t  3.1184
  12  26 even      640     79     16719      335    48.344        55.972   7.628    t     f  3.1836
  13  27  odd      594      1     16039     -345    49.543        56.000   6.456    t     t  2.9487
  13  28 even     1195    288     33748      980    51.595        59.949   8.354    t     f  3.0267
  14  29  odd     1099      1     31872     -896    52.710        60.000   7.290    t     t  2.9937
  14  30 even     2196    301     66181      645    54.743        63.973   9.230    t     t  2.9292
  15  31  odd     2125      1     65876      340    55.920        64.000   8.080    t     t  2.9511
  15  32 even     4024    472    129240    -1832    58.029        67.979   9.950    t     t  3.0015
  16  33  odd     4055      1    133816     2744    59.231        68.000   8.769    t     t  3.0452
  16  34 even     7713    562    262804      660    61.224        71.988  10.764    t     t  3.0360
  17  35  odd     7433      1    260156    -1988    62.351        72.000   9.649    t     t  2.9964
  17  36 even    14716   1099    530875     6587    64.423        75.988  11.565    t     t  2.9856
  18  37  odd    14195      1    525216      928    65.572        76.000  10.428    t     t  2.9627
  18  38 even    27822    932   1058168     9592    67.590        79.995  12.405    t     t  3.0157
  19  39  odd    26991      1   1052650     4074    68.775        80.000  11.225    t     t  3.0063
  19  40 even    52039   2096   2083656   -13496    70.753        83.994  13.241    t     t  2.9992
  20  41  odd    51226      1   2100267     3115    71.930        84.000  12.070    t     t  2.9988
  20  42 even    99707   2101   4189795    -4509    73.935        87.997  14.062    t     t  3.0036
  21  43  odd    97055      1   4173366   -20938    75.082        88.000  12.918    t     t  3.0023
  21  44 even   191124   4159   8413615    25007    77.092        91.997  14.905    t     t  3.0021
```

`W4x` is `(W4-exact)`; `W4lib` is the same test with the in-tree upper bound
`P_n` from `weak_fourth_moment_endpoint_ledger`.  The `D_1` column reproduces
the committed `Delta` table of `lemire-half-degree-irreducibles.md` at every
`ell = 13..21`, both parities, exactly.

**Result 1 (measurement).  `(W4-exact)` holds on every computed row --
40 of 40, `ell = 2..21`, both parities -- with exponential and monotonically
growing slack.**  The odd slack grows by `+0.830` bits per unit `ell` over the last
five odd rows; the even slack by `+0.828`.

**Result 2 (REFUTED, with witnesses).  `(W4)` stated with the repository's
current `P_n` upper bound is FALSE at even `ell = 11, 12, 13`.**  Witnesses:

```text
(ell,n)=(11,24):  M_4 = 41067019870720          library threshold = 68719476736
(ell,n)=(12,26):  M_4 = 357265460654496         library threshold = 3930163511296
(ell,n)=(13,28):  M_4 = 3400462499438720        library threshold = 68719476736
```

These are not failures of the fourth moment.  The library's `P_n` at `(13,28)`
is `32256` against `mu = 32768`, so `(mu - P_n)^4 = 512^4 = 2^36` while the
exact `(mu - Pi_n)^4 = (32768-288)^4 = 2^59.95`.  ADR-0563 records "no positive
reserve at `ell = 8,9,10`"; the failure actually continues through `ell = 13`
on the even side and the first even row that passes with the library bound is
`ell = 14`.  With `Pi_n` exact, or with `P_n^sharp` of Lemma B, every row passes.

### 2026-08-20T16:45 -- why the in-tree even bound is lossy, and by how much

The in-tree bound is
`P_n^lib = (n/2) 2^(n/2 - floor(ell/2)) + n 2^ceil(n/3)`.  Its first term is
Lemma B(2) with the factor `2` from not using `P(0) = 1`; its second term
bounds *all* `k >= 3` layers by `n 2^ceil(n/3)`, i.e. it assumes the largest
surviving layer has `deg P = n/3`.  Lemma B(1) shows the `k = 3` layer -- and
every odd `k` -- is **empty** at an even endpoint, so the largest surviving
layer has `deg P = n/4`.  The exponent is therefore `2^(n/3)` where the truth
is `2^(n/4)`: a factor `2^(n/12) = 2^(ell/6)`.

```sh
./target/release/examples/acb_wt_symbolic 2 30
```

Selected rows (the `P_lib`, `P_sharp` and threshold columns are verbatim from
`acb_wt_symbolic`; the `Pi_n(exact)` column is joined in from the
`acb_wt_weak_target` master table above, and is unavailable above `ell = 21`):

```text
 ell   n  par       P_lib   P_sharp   Pi_n(exact)   lib log2 thr  shp log2 thr
  11  24 even        7680      2304           160         36.000        50.094
  13  28 even       32256      5376           288         36.000        58.966
  17  36 even      165888     27648          1099         73.805        75.687
  21  44 even     1531904    135168          4159         90.836        91.906
  30  62 even   132055040   5079040             -        127.820       127.993
```

`P_n^sharp/Pi_n` is between 12.6 and 52.7 over `ell = 9..21` and its exponent
matches the truth: `log2 Pi_n` on the even rows grows at `+0.5` per unit `ell`,
which is Lemma B's `2^(ell/2)`.  `P_n^lib/Pi_n` grows like `2^(ell/6)`
(`368` at `ell = 21`).

**Result 3 (PROVED improvement).  Replacing the in-tree even-endpoint
proper-power bound by `P_n^sharp` of Lemma B moves the even-side crossovers
down by four levels and makes `(W4)` true on every computed row.**

### 2026-08-20T16:55 -- the exact crossovers

All by exact integer comparison in `acb_wt_symbolic`.

In each case the quantity is eventually monotone in `ell`; the value quoted is
the first `ell` **from which it holds for every larger `ell`**.  (At the odd
endpoint the two sporadic rows `ell = 2, 3` also satisfy both tests, because
`Sigma(ell)` is still tiny there; `ell = 4..14` fail.)

```text
first ell from which  R_0^suf := 2^ell (mu-P_n)^4 / (mu Sigma(ell))^2  exceeds 4
   odd endpoint                                   ell = 15   (P_n = 1, exact)
   even endpoint, in-tree P_n^lib                 ell = 17
   even endpoint, P_n^sharp (Lemma B)             ell = 13
   even endpoint, sweep-09's positivity-only mu^4 ell = 11   (not sufficient)

first ell from which  3 (mu Sigma(ell))^2 < 2^ell (mu-P_n)^4
   i.e. the PROVED Weil envelope alone discharges the entire Wick part,
   after which  K_4 <= 0  would already finish the endpoint:
   odd endpoint                                   ell = 14
   even endpoint, in-tree P_n^lib                 ell = 17
   even endpoint, P_n^sharp (Lemma B)             ell = 13
```

At the symbolic handoff, reproducing ADR-0563's numbers independently:

```text
(ell,n) = (200,401):  log2 R_0^suf = 171.482426     (both P_n agree; P_n = 1)
(ell,n) = (200,402):  log2 R_0^suf = 173.482426
(ell,n) = (400,801):  log2 R_0^suf = 367.453465
(ell,n) = (400,802):  log2 R_0^suf = 369.453465
```

Since the finite range is separately certified through degree 400 and the
crossovers are at `ell <= 17`, the small-`ell` behaviour of any `P_n` bound is
strategically irrelevant -- but it is exactly the mutation control that tells
you whether the implication code is checking what it claims, so the four-level
improvement is worth landing.

### 2026-08-20T17:05 -- how big M_4 actually is (a correction to sweeps 07 and 09)

Sweep 07 fits `M_4 ~ 0.6 ell^3 2^(3 ell)` from six rows, `ell <= 15`, and
sweep 09 inherits it.  Over `ell = 2..21`, both parities:

```text
ell   parity   M_4/(ell^2 2^(3ell))   M_4/(ell^3 2^(3ell))   M_2/(ell 2^n)
 11    odd            7.7902                 0.7082              0.8097
 15    odd            8.6090                 0.5739              0.8540
 18    odd            9.3978                 0.5221              0.8905
 21    odd            9.8304                 0.4681              0.9047
 11   even           39.5110                 3.5919              0.8866
 15   even           37.1447                 2.4763              0.8795
 18   even           38.0671                 2.1148              0.8882
 21   even           39.6063                 1.8860              0.9081
```

The cubic normalization *decreases* monotonically while the quadratic one
*increases* toward a constant.  The Gaussian model plus Keating--Rudnick
predicts exactly this: `M_2 -> (ell-1) 2^n` (the last column rises toward
`(ell-1)/ell`) and `M_4 -> 3 M_2^2 / 2^ell`, giving
`M_4 -> 12 (ell-1)^2 2^(3 ell)` at the odd endpoint and
`48 (ell-1)^2 2^(3 ell)` at the even one.  Measured limits `9.83 -> 12` and
`39.6 -> 48`, both still rising at `ell = 21`.

**Result 4 (correction, EVIDENCE).  The true growth is quadratic in `ell`, not
cubic: `M_4 ~ 12 ell^2 2^(3 ell)` (odd), `48 ell^2 2^(3 ell)` (even).  The slack
in `(W4)` is therefore `~2^(ell+4)/(12 ell^2) = 2^ell / (0.75 ell^2)`, not
`2^ell/ell^3`.**  This makes the sweeps' strategic conclusion *stronger*, not
weaker.  Measured `log2` slack at `(21,43)` is `12.918`; the model predicts
`4 ell + 4 - log2(12 ell^2) = 12.63`.

### 2026-08-20T17:15 -- task 3: which fourth-order object does the ladder need?

```sh
./target/release/examples/acb_wt_contractions 2 11    # 1.15 s
```

Three contractions of the same spectrum, exact integers:

```text
 ell   n     A = sum_chi |S_chi|^4      B = 2^(3ell) M_4        A/B      wick/2^ell M_4   proved wick excess
   8  18       1814153480830976     908399226336051200   1.997e-3           0.7497            4.42 bits
   9  19      12901272996544512    8224522311361888256   1.569e-3           1.0665            6.09 bits
  10  21     583964545144324096  819761090433371865088   7.124e-4           1.0404            6.20 bits
  11  23   24257637704590688256   69552242897967260893184 3.488e-4           1.0099            6.45 bits
  11  24  116541994584493785088  352763014577849095946240 3.304e-4           0.9550            6.11 bits
```

`A/B` falls like `~2^(-ell)`; the two fourth moments are genuinely different
tensor contractions and `A` does not bound `max_e |D_e|`.  This confirms
sweep-09's Translation 3 and the lane's `character_fourth_moment_comparison`
from an independent direction.

The answer to the charge:

1. **The implication consumes `M_4` of the CENTERED variable `D_e`, through the
   single inequality `max_e |D_e|^4 <= M_4`.**  Not `A = sum_chi |S_chi|^4`,
   which is phase-blind and a different contraction; not `K_4` directly.
2. **But `M_4` splits as `2^ell M_4 = 3 M_2^2 + K_4`, and the Wick half is
   already covered by a PROVED theorem.**  The last column above measures how
   much room the proved envelope `M_2 <= mu Sigma(ell)` leaves: it over-counts
   `2^ell M_4` by `4.4 .. 6.5` bits over `ell = 8..11`, growing slowly, while
   the `(W4)` allowance grows by a full bit per unit `ell`.  The two curves
   cross at `ell = 14` (odd) / `ell = 13` (even, Lemma B) -- the second crossover
   table above.
3. **Therefore the natural object for the ladder is the connected `K_4`, with
   target `(WK)`: `K_4 <= 2^ell (mu - P_n)^4 - 3 (mu Sigma(ell))^2`.**  Beyond
   the crossover the right-hand side is positive and of size `~2^(5 ell + 4)`,
   against the lane's live `K_4 <= M_2^2 ~ ell^2 2^(4 ell + 2)`.  **The
   connected target has the same `2^(ell+2)/ell^2` slack as the `M_4` target,
   and it is the *only* remaining open quantity** -- which the `M_4` formulation
   hides, because `M_4` mixes an already-proved half with an open half.
   Measured `K_4` is signed and small by comparison (`|K_4|/M_2^2 <= 0.38` for
   `ell >= 9` and `<= 0.27` for `ell >= 10`; `R_0` lies in `[2.93, 3.05]` for
   every `ell >= 14`), and it changes
   sign with parity at small `ell`, so no positivity can be assumed.

Recommendation for later workstreams: **target `(WK)`, state it with the proved
Weil envelope inlined, and never target `A`.**

### 2026-08-20T17:30 -- task 4: the sweep-08 (E2') accumulator, extended

The lane already exposes `(E2')` as
`BinaryDyadicAutocorrelationFibreReport::satisfies_nonpositive_within_fibre_correlation`
(`sum_F c_F^2 <= N_points`).  `acb_wt_e2prime.rs` drives it over the sweep's
`(ell,k,d) = (ell, ell+2 or ell+3, ell-1)` rows and extends them.

```sh
./target/release/examples/acb_wt_e2prime 4 9      #   1.0 s   (the sweep's 12 rows)
./target/release/examples/acb_wt_e2prime 10 13    #  66.4 s,  91 MB
./target/release/examples/acb_wt_e2prime 14 14    # 187.5 s, 354 MB
```

The twelve sweep-08 rows reproduce **exactly**: `#fib`, `pts`, `sum c^2`,
`Delta` and `sum|c|` all match, including the pinned `(9,11,8)` witness
`120680 / 130048 / -68 / 33680`.  Extension:

```text
 ell   k   d     fibres      points     sum c^2   Delta   c2/pts   c2/2^(k+d-1)  S const
   4   6   3         28         128          68      -2   0.5312        0.2656   0.2425
   5   7   4        100         576         408     -28   0.7083        0.3984   1.3862
   6   9   5        616        3840        3572     138   0.9302        0.4360   2.3090
   7   9   6       1252        8448        7904      16   0.9356        0.4824   0.1800
   8  10   7       4804       32256       27904    -128   0.8651        0.4258   0.7663
   9  11   8      18884      130048      120680     -68   0.9280        0.4604   0.1957
   9  12   8      37768      260096      233576    -236   0.8980        0.4455   0.4883
  10  12   9      75460      522240      461204    1170   0.8831        0.4398   1.7228
  10  13   9     150920     1044480      919588    -314   0.8804        0.4385   0.3274
  11  13  10     300932     2125824     1877080   -1592   0.8830        0.4475   1.1620
  11  14  10     601864     4251648     3754360     452   0.8830        0.4476   0.2333
  12  14  11    1199748     8380416     7450844    -894   0.8891        0.4441   0.3275
  12  15  11    2399496    16760832    14905072    -108   0.8893        0.4442   0.0280
  13  15  12    4798340    33669120    29953880    -948   0.8897        0.4463   0.1732
  13  16  12    9596680    67338240    60074488    8356   0.8921        0.4476   1.0781
  14  16  13   19183236   134184960   119676844   -8670   0.8919        0.4458   0.7925
  14  17  13   38366472   268369920   238505120    -136   0.8887        0.4442   0.0088
```

**Result 5 (REFUTED as a trend; EVIDENCE for `(E2')`).  The `c2/pts` ratio does
NOT keep rising and does not approach 1.**  Sweep-08's stated risk was
"`0.53 -> 0.936` over `ell = 4..9`; if it crosses 1, `(E2')` is false", and it
named the odd family `k = ell+2` as the one drifting.  Over `ell = 10..14` the
odd family reads `0.8831, 0.8830, 0.8891, 0.8897, 0.8919` and the even family
`0.8804, 0.8830, 0.8893, 0.8921, 0.8887`.  Both plateau at `0.889 +- 0.003`,
the parity split has vanished, and the `0.936` at `ell = 7` is the *maximum*
over 22 rows, not the start of a trend.  `(E2')` holds on all 22 rows with an
11% margin; `(E2)` holds with ratio in `[0.4385, 0.4476]` over `ell >= 10`;
the observed `(S)` constant never exceeds `2.31` (the `ell = 6, k = 9` row), against the `2.87`
that `(E2)` leaves room for.

This is finite evidence for a uniform statement, not a proof, but it removes the
specific falsification risk sweep-08 flagged as "the single cheapest high-value
experiment left".

### 2026-08-20T17:40 -- what I did not do

* No `Efron--Stein` weight-profile measurement (`E1` of sweep-09).  It is a
  different workstream's charge and `efron_stein_spectral_weight_report` already
  exists in tree.
* No attempt to prove `(W4)`, `(WK)` or `(E2')`.  Nothing here grants theorem
  credit for Lemire's conjecture or for any uniform estimate.
* No row above `ell = 21`: `ell = 22` needs `>5 min` and `>1.6 GB` in the
  transform, outside the charter's budget.

## FINDINGS

### (a) The verified precise statement of (T-weak), and its proof of sufficiency

**PROVED.**  With `mu = 2^(n-ell)`, `D_e = N_n(e) - mu`, `M_4 = sum_e D_e^4`, and
`Pi_n` the exact proper-prime-power Mangoldt mass in the identity class:

```text
(W4-exact)   M_4 < (mu - Pi_n)^4        ==>   I_n(1) >= 1.
```

Chain, with every constant explicit:

1. `N_n(1) = Pi_n + n I_n(1)`  (definition of `Lambda`).
2. `Pi_n = 1` at the odd endpoint `n = 2 ell + 1` (Lemma A; the sole
   contribution is `x^n`).  So the odd threshold is `(2^(ell+1) - 1)^4`.
3. `Pi_n <= (ell+1) 2^ceil(ell/2) + n 2^ceil((ell+1)/2)` at the even endpoint
   `n = 2 ell + 2`, `ell >= 2` (Lemma B; the odd-exponent layers are **empty**,
   the `k = 2` layer is injective into `G[2]` of order `2^ceil(ell/2)`, and the
   even `k >= 4` layers live at `deg P <= n/4`).  The bound is `< mu` for
   `ell >= 7`.  So the even threshold is `(2^(ell+2)(1 - theta_ell))^4` with
   `theta_ell <= 3(ell+1) 2^(-ell/2-1)`.
4. `max_e |D_e|^4 <= M_4` (Chebyshev at one point).
5. `(W4)` therefore gives `N_n(1) > Pi_n`, hence `n I_n(1) > 0`.

Sweep-09's displayed `M_4 < 2^(4(n-ell)) = mu^4` is **insufficient**: it yields
only `N_n(1) > 0`, and `N_n(1) = 1` (from `x^n`) is consistent with `I_n(1) = 0`
at the odd endpoint.  The corrected constant is *not* uniformly "below one": it
is `1 - 2^(-(ell+1))` at the odd endpoint and `1 - O(ell 2^(-ell/2))` at the
even one.  Consequences of the correction are entirely at small `ell`.

Two derived forms, both PROVED given the lane's proved envelope
`M_2 <= mu Sigma(ell)`, `Sigma(ell) = 2^ell(ell^2-4ell+6)-6`:

```text
(WR)   R_0 = 2^ell M_4/M_2^2 < 2^ell (mu - P_n)^4 / (mu Sigma(ell))^2
(WK)   K_4 = 2^ell M_4 - 3 M_2^2 <= 2^ell (mu - P_n)^4 - 3 (mu Sigma(ell))^2
```

`(WK)`'s right-hand side is positive from `ell = 14` (odd) / `ell = 13` (even,
Lemma B) and is then of size `~2^(5 ell + 4)`.

Refinement worth having, free: `N_n(1)` lies in `Pi_n + n Z`, so the *non-strict*
`M_4 <= (mu - Pi_n - n)^4` already suffices.  Reported per row as
`integral_target_holds`; it holds on every one of the 40 rows except the two
smallest, `(ell,n) = (2,5)` and `(3,8)`.

### (b) Data

Four tables above, all exact integers:

* the 40-row master table (`ell = 2..21`, both parities): `I_n(1)`, exact
  `Pi_n`, `N_n(1)`, `D_1`, `M_2`, `M_4`, `K_4`, `R_0`, and `M_4` against
  `(mu - Pi_n)^4`, `(mu - P_n^lib)^4`, `mu^4` and `2^(4 ell)`;
* `M_4` and `M_2` normalizations (17:05);
* the three fourth-order contractions and the proved-Wick excess (17:15);
* the 22-row `(E2')` table (17:30).

Headline: `(W4-exact)` holds on **40 of 40 rows** with `log2` slack rising from
`5.2` at `ell = 2` to `12.9` (odd) / `14.9` (even) at `ell = 21`, i.e.
`+0.83` bits per unit `ell` over the last five levels of each parity.  `R_0`
lies in `[2.93, 3.05]` for every `ell >= 14`.
Independent verification: eight rows against a sympy brute force over every
monic polynomial (exact agreement), and all 40 rows against a from-scratch
enumeration of `I_n(1)` and `Pi_n` reconstructing the CAS population via
`(dagger)` (exact agreement, `reconstruction_ok=true`).

### (c) Discrepancies with the sweeps' claims

1. **REFUTED (as an irreducibility criterion): sweep-09's `(MIN)`
   `M_4 < 2^(4(n-ell))`.**  It proves positive Mangoldt mass only.  Already
   caught in tree by ADR-0563; re-derived independently here, and the *reason*
   is sharper than the ADR states -- the obstruction is not "proper powers in
   general" but the single ramified unit `x^n` at the odd endpoint and the
   `2`-torsion layer at the even endpoint.
2. **REFUTED (with witnesses): sweep-09's claim that the weak form "holds with
   exponential room on every row" is false as stated for the *repository's own*
   `P_n`.**  Even rows `ell = 11, 12, 13` fail `(W4)` with the in-tree bound
   (witnesses at 16:40).  It is true with `Pi_n` exact or with `P_n^sharp`.
   ADR-0563's "no positive reserve at `ell = 8,9,10`" understates the range.
3. **Crossover values.**  Sweep-09 reports even crossover `ell = 11` (that is
   the positivity-only `mu^4` value and is not sufficient); ADR-0563 reports
   `ell = 17` (in-tree `P_n`).  With Lemma B the correct even crossover is
   `ell = 13`.  The odd crossover `ell = 15` is confirmed.
4. **Correction to the in-tree even bound (PROVED).**  `n 2^ceil(n/3)` should be
   `n 2^ceil((ell+1)/2)`: every odd prime-power exponent `k >= 3` contributes
   **zero** at an even endpoint, so the surviving layers sit at `deg P <= n/4`,
   not `n/3`.  Measured loss of the current bound: `368x` at `ell = 21`, growing
   like `2^(ell/6)`.
5. **Correction to the `M_4` growth law (EVIDENCE).**  Sweeps 07/09 use
   `M_4 ~ 0.6 ell^3 2^(3 ell)`.  Over `ell <= 21` the cubic normalization falls
   monotonically and the quadratic one rises toward the Gaussian +
   Keating--Rudnick prediction `12 ell^2 2^(3 ell)` (odd) /
   `48 ell^2 2^(3 ell)` (even).  Slack is `2^ell/(0.75 ell^2)`, better than
   advertised.
6. **REFUTED (as a trend): sweep-08's `(E2')` risk.**  The `sum c^2 / N_points`
   ratio plateaus at `0.889 +- 0.003` over `ell = 10..14` in *both* families; it
   does not approach 1.  The `0.936` the sweep read as a rising trend is the
   maximum over 22 rows.
7. **Not a discrepancy, recorded as a near-miss:** my own first Rabin
   irreducibility test was wrong at composite degrees and would have produced a
   fabricated disagreement with the CAS.  It was caught by the
   `sum_e N_n(e) = 2^n` invariant, not by a test.  The CAS was right.

### (d) Next rungs for the ladder

1. **Land Lemma B.**  Replace the even-endpoint `n 2^ceil(n/3)` term by
   `n 2^ceil((ell+1)/2)` and the `k=2` term by `(ell+1) 2^ceil(ell/2)` in
   `endpoint_proper_prime_power_upper_bound`, with the emptiness of the
   odd-exponent layers as the stated reason.  Moves the even crossover from
   `17` to `13` and makes the finite rows genuine passing controls instead of
   failures.  Owner: the `gf2_hayes.rs` lane (I must not edit that file).
   Mutation control: delete the odd-`k` emptiness and exactly the even rows
   `ell = 11,12,13` must fail.
2. **Restate the live fact as `(WK)`, not `M_4 < (mu-P_n)^4`.**  The `M_4` form
   bundles a proved half (`3 M_2^2`, discharged by the Weil envelope from
   `ell = 13/14`) with the open half.  `F:gf2-hayes-weak-fourth-moment-endpoint-bound`
   should carry `(WK)` as its statement, with `(W4)` as the derived consequence.
   This is the rung that tells later workstreams what is actually unproved.
3. **The `(E2')`+`(S)` split is now the best-supported open pair in the sweep
   set.**  `(E2')` is a pure four-point count with 22 exact rows, a stable 11%
   margin and no drift; `(S)` is an absolute-constant square-root cancellation
   with observed constant `<= 2.31` against an allowance of `2.87`.  Push
   `(E2')` to `ell = 15, 16` (about 25 min and 1.5 GB at `ell = 16`, so it needs
   a budget waiver or a sharded run) and, more importantly, attempt the proof:
   "within-fibre off-diagonal dyadic correlation is nonpositive" is an
   inclusion--exclusion/Parseval statement about affine fibres, not an
   analytic estimate.
4. **Re-audit the refuted shortcuts against `(WK)`, not against `M_2^2`**
   (sweep-09's `E3`).  The allowance is now explicitly `~2^(5 ell + 4)`; any
   shortcut whose measured loss grows polynomially in `ell` survives.  The
   `ell`-scaling of the three pinned loss factors (`1425/1483` at `ell = 8`,
   `303.92/632.42` at `ell = 12`, "thirty times the signed total" at `ell = 9`)
   is the cheap decisive measurement and is unblocked by this file's crossover
   table.
5. **Extend the exact `Pi_n` computation upward as a cheap standalone.**
   `acb_wt_weak_target` spends all its time in the Hayes transform; the
   `Pi_n`/`I_n(1)` half alone is `2^(ell+2)` irreducibility tests and reaches
   `ell = 26` in seconds.  That would give the exact even-endpoint threshold far
   beyond the transform's range and a fourth independent check of the odd
   `I_n(1)` table.

### Epistemic ledger for this file

PROVED: Lemma A; Lemma B; Lemma C; the Theorem `(W4-exact) => I_n(1) >= 1` with
all constants; the corollaries `(WR)` and `(WK)` given the lane's proved
`M_2 <= mu Sigma(ell)`; the closed form of `Sigma(ell)` (the standard
`sum_(i=0)^m i^2 2^i = 2^(m+1)(m^2-2m+3)-6` at `m = ell-1`, checked by exact
integer comparison for `2 <= ell <= 400`); the integrality refinement
`M_4 <= (mu - Pi_n - n)^4`.
REFUTED with exact witnesses: `(W4)` with the in-tree `P_n` at even
`ell = 11,12,13`; sweep-09's `mu^4` form as an irreducibility criterion;
sweep-08's `(E2')` rising-ratio risk as a trend through `ell = 14`.
EVIDENCE ONLY (40 rows, `ell = 2..21`, both parities, cross-checked against a
sympy brute force on 8 rows and an independent enumeration on all 40):
`(W4-exact)` itself; `R_0 -> 3`; `M_4 ~ 12 ell^2 2^(3 ell)`; `(E2')`, `(E2)`
and `(S)` on 22 rows.
OPEN: `(W4)`, `(WR)`, `(WK)`, `(E2')`, `(S)` as uniform statements.
NO THEOREM CREDIT is claimed for Lemire's conjecture or for any uniform
estimate.
