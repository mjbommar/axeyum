# Ad hoc blocker sweep 2026-08-20 -- lane 07: algebraic coding theory
# (weight distributions and divisibility theorems)

Agent: field specialist 07 (coding theory / divisibility).
Scope: ad hoc research challenge, deliberately OUTSIDE the roadmap, gates, and
fact-ledger rules.  This file is the only repository file this agent writes.
Everything else lives in the session scratchpad
`/tmp/claude-1000/-home-mjbommar-projects-personal-axeyum/f980d106-5a72-4c93-8c17-11101edf42d1/scratchpad`.

Epistemic convention: **PROVED** (a real proof, given here or cited with a
verified reference), **REFUTED** (with an explicit witness), **OPEN**
(conjecture / observation / finite computation).  Finite computation is
evidence, never a theorem.

---

## Log

### 2026-08-20T15:09-04:00 -- start

Diary opened.  Read, in the briefed order:
`lemire-review-2026-08-20-reaim.md`, `docs/plan/status/52-gf2-lemire.md`,
the Kerdock / second-trace / Arf / divisibility sections of
`lemire-half-degree-irreducibles.md`, and the bridges audit.

### 2026-08-20T15:15 -- fixing the coding-theoretic dictionary

Before doing anything I wrote down the translation from the lane's Hayes
language into the language of my field, because both prongs of my charge are
statements about a *code*, and the lane's notes never name it as one.

Let `n = 2*ell+1`, `m = ell+1`, and let

```text
U = (1 + x F_2[x]/x^(ell+1)),   |U| = 2^ell     (principal units, the Hayes group)
Phi : GF(2^n) -> U,   alpha |-> f*_alpha mod x^(ell+1),
      f*_alpha(x) = x^n f_alpha(1/x) = prod_(j=0)^(n-1) (1 + alpha^(2^j) x),
A_u = # Phi^(-1)(u),        N_n(1) = A_1,        Delta = A_1 - 2^(n-ell).
```

Two facts that make this a coding problem:

1. `Phi` is the *generator-matrix column map* of an explicit code.  Every
   character `chi` of `U` gives a "codeword" `c_chi = (chi(Phi(alpha)))_alpha`
   of length `2^n`, and

   ```text
   2^ell * Delta  =  sum_(chi != 1) S(chi),      S(chi) = sum_alpha chi(Phi(alpha)).
   ```

   For `chi` of order two, `S(chi) = 2^n - 2 wt(c_chi)`: an ordinary binary
   weight.  So the endpoint problem is literally a **weight-distribution
   concentration problem** for the code `C = { c_chi }`.

2. The coordinates of `Phi` are the elementary symmetric functions of the
   Frobenius conjugates, i.e. the char-poly coefficients:
   `e_i(alpha) = sum_(j_1<...<j_i) alpha^(2^(j_1)+...+2^(j_i))`.
   As a function `F_2^n -> F_2` each `e_i` is an **F_2-polynomial of algebraic
   degree exactly `i`**, because each `alpha^(2^j)` is F_2-linear in the
   coordinates.  `e_1 = Tr`, `e_2` is the lane's "second trace" quadratic form.

**Character structure (this is the "wildness").**  `U` is an abelian 2-group,
`U ~= prod_(i odd, i<=ell) Z/2^(e_i)` with `2^(e_i) * i > ell >= 2^(e_i - 1) * i`.
Order-two characters are the "tame" sector: by Newton's identities in
characteristic two (`d log f* = sum_k Tr(alpha^k) x^(k-1)`, and
`p_(2k) = p_k^2` is automatic), they are exactly

```text
chi_T(Phi(alpha)) = (-1)^(sum_(i in T) Tr(alpha^i)),   T subset {odd i, 1<=i<=ell}.
```

There are `2^ceil(ell/2) - 1` of them -- this reproduces the lane's checked
"maximal quotient `E_ell/2E_ell` has rank `ceil(ell/2)`" from the coding side.
These are codewords of a **subfield-restricted dual-BCH code** (F_2
coefficients only, not F_(2^n)).  Everything of order `>= 4` is genuinely
Witt-vector valued (`Z/2^r`-valued), i.e. this is a **Z_(2^r)-linear trace
code over a Galois ring** -- the Kerdock/Delsarte-Goethals world, not the
binary cyclic world.  That is exactly the "McEliece is tame, we are wild"
gap named in my brief, now made precise.

**L-function degrees.**  A character of exact conductor `x^(j+1)` has
`|{chi}| = 2^(j-1)` and its L-function has degree `j-1`.  Checks: `j=1`
(conductor `x^2`) gives `S = sum_alpha (-1)^(Tr alpha) = 0`, degree 0; `j=2`
(conductor `x^3`) gives the Z4 Kerdock sum, degree 1, `|S| = 2^(n/2)` exactly.
Summing, the Carlitz curve of conductor `x^(ell+1)` has

```text
2 g_ell = sum_(j=1)^(ell) 2^(j-1) (j-1) = (ell-2) 2^ell + 2.       (genus, derived)
```

Hence the pointwise Weil bound reads
`|Delta| = |a_n| / 2^ell <= 2 g_ell 2^(n/2) / 2^ell ~ sqrt(2) (ell-2) 2^ell`,
which is the lane's `ell * 2^ell` blocker, re-derived from the character count.
The whole blocker is therefore "`2 g_ell` is `ell` times `2^ell`."

---

### 2026-08-20T15:25 -- PRONG A, step 1: what does Ax-Katz actually give?

This is the first question in my charge and it has a complete, clean answer.

`N_n(1)` is the number of common zeros in `F_2^n` of the `ell` F_2-polynomials
`e_1, ..., e_ell` of degrees `1, 2, ..., ell`.  Ax-Katz gives `2^b | N` with
`b = ceil((n - sum_i d_i)/max_i d_i)`:

```text
ell=1, n=3 : degrees (1),       sum 1,  max 1, b = ceil(2/1) = 2  -> 4 | N.  N = 4.   exact
ell=2, n=5 : degrees (1,2),     sum 3,  max 2, b = ceil(2/2) = 1  -> 2 | N.  N = 6.   ok
ell=3, n=7 : degrees (1,2,3),   sum 6,  max 3, b = ceil(1/3) = 1  -> 2 | N.  N = 22.  ok
ell=4, n=9 : degrees (1,..,4),  sum 10, max 4, b = ceil(-1/4)= 0  -> nothing.  N = 37.
```

**PROVED.** For `n <= 7` the Chevalley-Warning/Ax-Katz theorem alone proves
Lemire's conjecture at the odd endpoint: `N_n(1)` is even and `N_n(1) >= 1`
(the class of `x^n`), hence `N_n(1) >= 2`, hence `I_n(1) >= 1`.  This is a
genuine, fully elementary, analysis-free proof -- of three cases.

**REFUTED, with witness.** No Ax-Katz-type argument can go further, and this
is not a defect of the chosen generators.  Ax-Katz applies to *any* defining
system, so the escape hatch is "cut the identity Hayes class out by cheaper
equations".  Any system of `r` equations of degrees `d_i` with
`sum d_i < n = 2 ell + 1` would give `2 | N`, hence the theorem.  But
`N_9(1) = 37` is **odd** (native count in the canonical note; independently
recomputed below).  So for `ell = 4` no such system exists, and the route is
closed at the fourth case.  Moreno-Moreno's p-weight-degree refinement gives
nothing extra here: we are already working over the prime field `F_2`, where
the p-weight degree coincides with the ordinary degree.

Literature checked (web, 2026-08-20):
- Moreno-Moreno improvement and its descendants:
  [Improvement to Moreno-Moreno's theorems, J. Finite Fields Appl.](https://www.sciencedirect.com/science/article/pii/S1071579712000767),
  [A partial improvement of the Ax-Katz theorem, JNT 132 (2012) 485-494](https://www.sciencedirect.com/science/article/pii/S0022314X11002277),
  [Zhu, On a theorem of Ax and Katz](https://jtnb.centre-mersenne.org/item/10.5802/jtnb.972.pdf).
- Elementary/covering-method proofs and the *exact* p-divisibility variant:
  [Castro et al., Divisibility of Exponential Sums via Elementary Methods](https://perso.telecom-paristech.fr/randriam/maths/ElemDivSub+.pdf),
  [Exact p-Divisibility of Exponential Sums via the Covering Method](https://ccom.uprrp.edu/~labemmy/Wordpress/wp-content/uploads/2022/06/CoveringFinal.pdf)
  (PDF did not render through WebFetch; cited from the search index and the
  authors' own listing, so treat the *contents* as unverified -- only the
  existence of the covering method for exact divisibility is being claimed).
- Extensions beyond fields, which is where a "Galois-ring Ax-Katz" would live:
  [Zeros of polynomials over finite Witt rings](https://arxiv.org/pdf/2310.15637),
  [Clark et al., A Generalization of the Chevalley-Warning and Ax-Katz Theorems](https://arxiv.org/abs/2208.12895),
  [On theorems of Delsarte-McEliece and Chevalley-Warning-Ax-Katz](https://link.springer.com/article/10.1007/s10623-012-9645-y).
None of these changes the arithmetic above: they all sharpen a *lower* bound
on `v_2(N)`, and at `ell = 4` the true value is `v_2(N) = 0`.

### 2026-08-20T15:35 -- PRONG A, step 2: the structural reason, stated once

The above is not bad luck.  Here is the general obstruction, which subsumes
McEliece, Ax, Adolphson-Sperber, Newton-over-Hodge, and anything else in the
divisibility family.

**PROVED (elementary).**  With `n = 2 ell + 1`:
`I_n(1) = 0  <=>  N_n(1) = 1  <=>  Delta = 1 - 2^(ell+1)  <=>  a_n = 2^ell (2^(ell+1) - 1)`,
where `a_n = -2^ell Delta` is the Frobenius trace of the Carlitz curve.
Therefore:

1. Any statement "`Delta = 0 mod 2^s`" for `s >= 1` proves the odd endpoint,
   since `1 - 2^(ell+1)` is odd.  **This is exactly the Chevalley-Warning
   shape**, and it is the *only* shape a divisibility theorem can produce,
   because divisibility theorems bound `v_2` from below.
2. `Delta` is odd at `ell = 13, 20, 24, 25, 27` (values `-345, 3115, 1651,
   -42333, 181465`).  So the statement "`2 | Delta`" is **false**, and no
   theorem of any kind will ever prove it.  **REFUTED with witness.**
3. The strongest divisibility a curve can have is supersingularity (all Newton
   slopes `1/2`), which gives `v_2(a_n) >= n/2`, hence `>= ell+1` by
   integrality, hence `2 | Delta`.  So the divisibility route needs
   **exactly** supersingularity, with zero margin -- and supersingularity is
   refuted twice over: by the lane's own exact-conductor witness (level-ten
   degree-22 relative trace `-5120`, remainder `1024` mod `2048`) and,
   independently, by every odd-`Delta` row above.
4. Characterwise divisibility is quantitatively hopeless by a factor of `ell`
   in the exponent.  The lane's own Newton audit measured minimum primitive
   slopes `1/2` (levels 2-3), `1/4` (levels 4-7), `1/8` (levels 8-10), i.e.
   roughly `2^(-ceil(log2 j))` at conductor level `j`.  That gives
   `v_2(S(chi)) >~ n/j ~ 2` at the top level, against a required aggregate
   valuation of `ell + 1`.  **All but `O(1)` of the needed 2-divisibility is
   cross-character cancellation, and exactly `ell` of it is already forced for
   free by the integrality of `N`.**  The theorem is "one bit beyond
   integrality", and nothing in the divisibility literature produces a bit
   beyond integrality.

I therefore regard **PRONG A as closed as a proof route**, with (2) and (3) as
the witnessed refutations and (4) as the quantitative reason.  What is *not*
closed is the technique that could supply an *upper* bound on a valuation:
exact evaluation.  That is Prong B, and the two prongs meet exactly here.

### 2026-08-20T15:45 -- PRONG A, step 3: is "McEliece for Artin-Schreier-Witt" in the literature?

Searched specifically for it.  Verdict: **the pieces exist, the theorem does
not, and if it did exist it would be the wrong-signed statement anyway** (see
the obstruction above).  For the record, the closest technology found, all
verified by web search on 2026-08-20:

- **T-adic exponential sums (Liu-Wan, Algebra & Number Theory 2009)** and the
  T-adic Newton-over-Hodge bound.  This is the correct uniform frame: one
  T-adic L-function specialises to *every* Artin-Schreier-Witt level at once,
  which is precisely the multi-conductor bookkeeping the lane hand-built.
  This reference is **absent from the review note's Move-1 literature list**
  and is the single most on-target item I found.
  Follow-ups: [Newton slopes for twisted Artin-Schreier-Witt towers](https://arxiv.org/pdf/1704.07017),
  [Generic Newton slopes for ASW towers in two variables](https://arxiv.org/pdf/1612.07158),
  [On slopes of L-functions of Z_p-covers of the projective line](https://arxiv.org/pdf/1701.08733).
- **Haessig, "On partial T-adic exponential sums and partial exponential sums
  with p-power conductor"**, [arXiv:2606.10041](https://arxiv.org/abs/2606.10041)
  (submitted 2026-06-08).  Verified by fetching the abstract page: it proves
  T-adic meromorphy for *partial* T-adic sums, a p-adic rationality proof for
  **all partial L-functions of characters with p-power conductor**, plus
  Newton-over-Hodge estimates.  "Characters with p-power conductor" is
  verbatim our family.  This is newer than everything in the review note and
  should be read before any further Newton-polygon work.  Caveat: I did not
  verify whether the results hold at `p = 2`; the neighbouring
  Kramer-Miller-Upton papers explicitly exclude it, and the lane already
  recorded that.
- **Blache-Ferard, p-density / generic first slope for Artin-Schreier curves**:
  [p-Density, exponential sums and Artin-Schreier curves](https://arxiv.org/abs/0812.3382),
  [Valuation of exponential sums and the generic first slope for Artin-Schreier curves, JNT (2012)](https://www.sciencedirect.com/science/article/pii/S0022314X12001382),
  [Valuations of exponential sums and Artin-Schreier curves](https://arxiv.org/pdf/1502.00969),
  [Construction of curves with a controlled first slope using p-symmetric numbers (2024)](https://arxiv.org/html/2411.01832).
  These are the sharpest available *lower* bounds on `v_2(S(chi))` for one
  variable, i.e. the "characterwise" quantity in point (4) -- they confirm the
  measured `1/2, 1/4, 1/8` pattern and confirm it is far too small.
- **McEliece proper**, for completeness: weights of a binary irreducible cyclic
  code are divisible by `2^(theta-1)` and one is not divisible by `2^theta`;
  the sharpness clause comes from Stickelberger/Gross-Koblitz.
  [Aubry-Langevin, On the weights of binary irreducible cyclic codes](https://hal.science/hal-00978908/document),
  [Calderbank-Li-Poonen, A 2-adic approach to the analysis of cyclic codes, IEEE-IT](https://ieeexplore.ieee.org/document/568706/).
  The sharpness clause is the only *upper*-bound-on-valuation mechanism in the
  classical theory, and it is powered by an **exact Gauss-sum evaluation**.
  It does not transfer: Gauss sums are multiplicative/tame; our characters are
  additive/wild, with no Stickelberger factorisation.
- **Katz (Daniel J.)**, the modern exact-valuation programme:
  [Divisibility of Weil sums of binomials](https://arxiv.org/pdf/1407.7923),
  [The p-adic valuations of Weil sums of binomials](https://arxiv.org/pdf/1608.04047),
  [survey](https://arxiv.org/pdf/1805.10452).
  Same shape: exact valuations are obtained for *binomial* phases with strong
  extra structure (three-valued families), never for a growing family of wild
  characters.

**OPEN / dead end recorded:** "McEliece for Artin-Schreier-Witt codes" does not
exist as a theorem.  More importantly, per the step-2 obstruction, if someone
proved it tomorrow it would still be the wrong-signed statement.  I recommend
the lane stop looking for it.

### 2026-08-20T15:55 -- independent recomputation of the endpoint table, and an efficiency finding

I wanted my own numbers rather than the ledger's, and discovered something
practical along the way.

The lane computes `N_n(1)` for both endpoints with the exact Hayes Fourier
transform: at `ell = 24` that cost 25m41s and 10.3 GB peak RSS on s4, plus a
1h25m C++ replay on s1.  **At the odd endpoint this is unnecessary.**  The
exact odd reduction `N = 1 + n I` means only `I_n(1)` is needed, and `I_n(1)`
is a direct enumeration over the `2^(ell+1)` monic polynomials
`x^n + (low part of degree <= ell)`, each tested for irreducibility.  That is
`2^ell` candidates with constant term one, and each test is `n` squarings mod
`f` in `__uint128_t`.

```sh
# scratchpad/lemire_odd.c  (single-threaded) and lemire_omp.c (OpenMP)
gcc -O3 -march=native -o lemire_odd lemire_odd.c && ./lemire_odd 1 16
gcc -O3 -march=native -fopenmp -o lemire_omp lemire_omp.c && ./lemire_omp 24
```

`ell = 24` completes in **2.276 s wall (37.6 s CPU, 24 threads), ~1 MB RSS**,
against 25m41s / 10.3 GB for the Hayes transform.  Roughly a 700x wall-clock
and 10000x memory improvement for the odd half of each row.  Every row this
agent computed at `13 <= ell <= 27` reproduces the committed ledger values
exactly, including `Delta_(24,49) = 1651` and the `ell = 27` stopping row
`I_55(1) = 4883944`, `N = 268616921`, and the review note's
`I_51(1) = 1315030`.  That is now a **third independent implementation** of
those rows (Rust transform, C++ transform, and this direct enumeration), with
a completely different algorithm -- it shares no code path with either.

Full table, `ell = 1..30`, `n = 2 ell + 1` (rows `25..30` and `26, 28, 29, 30`
extend the committed odd endpoint range; the ledger held `13..24` plus `27`):

```text
ell   n            I_n(1)  v2(I)      Delta  v2(D) D%8  log2|D|  ell/2
  1   3                 1    0            0    -    0     --      0.5
  2   5                 1    0           -2    1    6    1.00     1.0
  3   7                 3    0            6    1    6    2.58     1.5
  4   9                 4    2            5    0    5    2.32     2.0
  5  11                 4    2          -19    0    5    4.25     2.5
  6  13                 6    1          -49    0    7    5.61     3.0
  7  15                20    2           45    0    5    5.49     3.5
  8  17                33    0           50    1    2    5.64     4.0
  9  19                49    0          -92    2    4    6.52     4.5
 10  21               100    2           53    0    5    5.73     5.0
 11  23               187    0          206    1    6    7.69     5.5
 12  25               342    1          359    0    7    8.49     6.0
 13  27               594    1         -345    0    7    8.43     6.5
 14  29              1099    0         -896    7    0    9.81     7.0
 15  31              2125    0          340    2    4    8.41     7.5
 16  33              4055    0         2744    3    0   11.42     8.0
 17  35              7433    0        -1988    2    4   10.96     8.5
 18  37             14195    0          928    5    0    9.86     9.0
 19  39             26991    0         4074    1    2   11.99     9.5
 20  41             51226    1         3115    0    3   11.61    10.0
 21  43             97055    0       -20938    1    6   14.35    10.5
 22  45            186245    0        -7582    1    2   12.89    11.0
 23  47            358187    0        57574    1    6   15.81    11.5
 24  49            684818    1         1651    0    3   10.69    12.0
 25  51           1315030    1       -42333    0    3   15.37    12.5
 26  53           2530483    0      -102128    4    0   16.64    13.0
 27  55           4883944    3       181465    0    1   17.47    13.5
 28  57           9419359    0        32552    3    0   14.99    14.0
 29  59          18195267    0      -221070    1    2   17.75    14.5
 30  61          35200738    1      -238629    0    3   17.86    15.0
```

Two readings of this table.

**(a) The fixed-modulus congruence route is refuted statistically, not just by
one row.**  The lane refuted `(C8)` with the single row `ell = 27`,
`v_2(I) = 3`.  With thirty rows the picture is sharper: `v_2(I_n(1))` has
empirical distribution `0 x 19, 1 x 7, 2 x 3, 3 x 1` -- indistinguishable from
`P(v_2 = k) = 2^(-k-1)`, the law of a random 2-adic integer.  The expected
maximum over thirty samples is `~log2(30) = 4.9`; observed 3.  **OPEN but
strongly supported:** `v_2(I_n(1))` is unbounded and *any* fixed modulus
`2^s` fails for a `2^(-s)` proportion of `n`.  Chasing a sharper fixed
congruence than `(C8)` is chasing noise.
Corollary: the surviving honest target is an **explicit finite upper bound**
`v_2(I_n(1)) <= B(n)` for any computable `B` -- `B(n) = C log n` is the
natural conjecture -- since `I = 0` has `v_2 = infinity`.  That remains an
upper bound on a valuation, so step 2's obstruction still applies.

**(b) The truth is a full square root below what the conjecture needs.**
`log2|Delta|` tracks `ell/2 + O(log ell)`, not `ell`.  Fitting,
`|Delta| ~ sqrt(ell) 2^(ell/2)` -- exactly the random-phase prediction for a
sum of `2 g_ell ~ ell 2^ell` Weil numbers of modulus `sqrt(2)`, divided by
`2^ell`.  The conjecture asks only for `2^ell`.  **So the gap between the
truth and the requirement is `2^(ell/2)/sqrt(ell)`, an exponential margin --
and the requirement is still out of reach.**  This matters for strategy: no
amount of constant-sharpening or exponent-pair polishing is aimed at the right
thing.  The barrier is not tightness; it is that *every available method
bounds `sum |lambda^n|` rather than `|sum lambda^n|`*, and the entire
`ell -> 1` saving must come from cancellation among Frobenius angles that
nothing controls at fixed `n` (Deligne/Katz-Sarnak equidistribution is
`q -> infinity` or fixed-curve-`n -> infinity`; here the curve grows with `n`).

### 2026-08-20T16:10 -- the fibre distribution: measuring which moment closes the problem

This is the experiment I think is worth the most to the lane.  Everything in
the ledger is on the character side.  I measured the **physical side** -- the
exact Hayes fibre distribution `A_u` over all `2^ell` classes -- and compared
it against the sufficient thresholds directly.

Elementary identity used (**PROVED**, Parseval + one term):

```text
sum_(u in U) (A_u - 2^(n-ell))^2  =  2^(-ell) sum_(chi != 1) |S(chi)|^2  =: M_2 .
If N_n(1) = A_1 = 1 then the u=1 term alone forces  M_2 >= (2^(n-ell) - 1)^2 .
Hence   M_2 < (2^(n-ell) - 1)^2   ==>   Lemire at that odd n.        (L2 test)
More generally  |Delta| <= (M_2k)^(1/2k),  M_2k = sum_u (A_u - 2^(n-ell))^(2k),
so   (M_2k)^(1/2k) <= 2^ell   ==>   Lemire at that odd n.            (L2k test)
```

Computed exactly for prime `n = 2 ell + 1` by bucketing every monic degree-`n`
polynomial with constant term one by its top `ell` coefficients
(`A_u = n I_u + [u=1] + [u = class of (1+x)^n]`, valid because `n` prime means
the only proper divisor degree is one):

```sh
# scratchpad/fibers.c
gcc -O3 -march=native -fopenmp -o fibers fibers.c -lm
for e in 6 8 9 11 14 15; do ./fibers $e; done
```

```text
ell   n   mean=2^(n-ell)   minA    maxA  empty  sigma    kurtosis  sqrt(M2)/2^ell  M4^(1/4)/2^ell  M6^(1/6)/2^ell
  6  13        128           79     156     0    18.04     2.956        2.255          1.046           0.886
  8  17        512          357     646     0    52.04     2.901        3.253          1.061           0.791
  9  19       1024          836    1254     0    80.76     2.813        3.569          0.972           0.672
 11  23       4096         3496    4738     0   191.00     2.971        4.221          0.824           0.518
 14  29      32768        30508   34974     0   622.53     2.994        4.864          0.566           0.299
 15  31      65536        62155   69657     0   916.25     2.951        5.062          0.493           0.247
```

Findings, in order of importance:

1. **The pure second-moment (energy) route is FALSE, not merely lossy.**
   `sqrt(M_2)/2^ell` is `2.26, 3.25, 3.57, 4.22, 4.86, 5.06` and rising like
   `sqrt(2 ell)` (`sqrt(30) = 5.48` at `ell = 15`); the test needs `< 1`.  Equivalently `M_2 / (mean-1)^2` is
   `1.29, 2.66, 3.19, 4.46, 5.91, 6.41` where the threshold is `1`.
   **REFUTED with exact witnesses** for `ell = 6, 8, 9, 11, 14, 15`.
   The structural reason: `E|S(chi)|^2 ~ (j-1) 2^n` for a level-`j` character
   because its L-function has `j-1` eigenvalues, and averaging over the
   conductor filtration gives `M_2 ~ ((ell-2)/4) * (mean-1)^2`.  **The lane's
   measured Hast-Matei deficits `(ell-1)/2` and `(ell-1)/4` are exactly this
   mean L-degree.**  So that deficit is not a method artifact and cannot be
   optimised away; it is the average number of Frobenius eigenvalues per
   character.
2. **The fourth moment already suffices, and from a low `ell`.**
   `M_4^(1/4)/2^ell` = `1.046, 1.061, 0.972, 0.824, 0.566, 0.493` -- it crosses below
   one at `ell = 9` and then decays.  Measured growth
   `M_4 ~ 0.6 * ell^3 * 2^(3 ell)` (ratios `M_4/(ell^3 2^(3ell))` =
   `0.354, 0.634, 0.626, 0.708, 0.610, 0.574`), against a requirement of
   `M_4 <= 2^(4 ell)`.  **The `L^4` route therefore has slack `2^ell / ell^3`
   -- exponential.**  The lane's committed sufficient statement
   `M_4 <= 16 ell^5 2^(3 ell)` is itself `ell^2` weaker than the measured
   truth, so it is not a knife-edge either.  This is the strongest strategic
   signal in my sweep: **stop paying for `L^2` refinements, and note that an
   `M_4` proof may throw away a factor `2^(ell/4)` and still win.**
   The sixth moment is even more comfortable (`0.886 ... 0.247`).
3. **The fibre distribution is Gaussian.**  Kurtosis `2.81-2.99` against `3` (six rows).
   No class is empty in any computed row, and `max_u |A_u - mean|` is
   `49, 155, 230, 642, 2260, 4121` -- about `3.4-4.5 sigma`, exactly the Gaussian
   maximum over `2^ell` samples, and always well inside the required `2^ell`
   (`64, 256, 512, 2048, 16384, 32768`).  So the true statement is much stronger than
   Lemire: *every* Hayes class at the odd endpoint is within `~sqrt(ell)
   2^(ell/2)` of uniform.  The gap between provable and true is a Chebyshev
   gap: `L^2` over `2^ell` classes loses `sqrt(2^ell)`, whereas a Gaussian
   tail would only lose `sqrt(ell)`, which is far inside budget.  **The
   endpoint conjecture is exactly the statement that the wild trace code's
   weight distribution has sub-Gaussian tails rather than merely Chebyshev
   tails at one point.**

### 2026-08-20T16:30 -- PRONG B: exact enumerators, and where the refuted Kerdock claim really sits

My brief asks whether the lane's Kerdock refutation was about *pairwise rank
distribution* rather than *aggregated exact enumerators*.  Reading the ledger
text: yes, literally.  The refutation is
"28,830 pairs occupy ten types and realize every even rank from zero through
ten; five nonzero correlations have rank only two ... the raw forms are not a
uniformly high-rank Kerdock family", i.e. it is about pairwise polar ranks of
the second-trace forms attached to *polynomials* in the Moebius sieve.  It
does not by itself close an aggregated-enumerator argument, and it is indexed
differently from the character family.  So the question is live and I answered
it independently on the character side.

**Which characters have exact evaluations?**  Exactly those whose L-function
is degree `<= 1`, plus those whose phase is a quadratic form.

- Degree `<= 1`: conductor dividing `x^3`, i.e. a subgroup of **order 4**.
  The order-four character is exactly the Z4/Galois-ring Kerdock sum: with
  `k = e_1 + 2 e_2` in `Z/4` (verified directly from the group law
  `(1+x)^2 = 1+x^2`, `(1+x)^3 = 1+x+x^2 mod x^3`),
  `S = sum_alpha i^(e_1(alpha) + 2 e_2(alpha)) = sum_alpha i^(T(alpha))`
  where `T` is the Galois-ring trace of the Teichmuller lift.  `|S| = 2^(n/2)`
  exactly -- classical Kerdock.  So the Kerdock connection is real, and it is
  the `e_2` "second trace" the lane already isolated.
- Quadratic-form phases in the order-two sector: `chi_T` with
  `T subset {1} union {Gold exponents 2^k + 1 <= ell}`.  Weil sums of
  quadratic forms are exactly evaluable (`0` or `+-2^((n+s)/2)`).  There are
  `~log2(ell)` Gold exponents below `ell`, so this subfamily has size
  `O(ell)`.

**Decisive obstruction (PROVED as a counting statement, OPEN only in the sense
that "no exact evaluation is known" is a literature claim, not an impossibility
theorem):** the exactly-evaluable subfamily has size `O(ell)` -- polynomial --
out of `2^ell`.  Summing it exactly removes a `poly(ell)/2^ell` fraction of the
family and leaves a remainder of the same order.  Worse, it lies entirely in
the *low-conductor* window that the lane has **already** discharged by exact
Fourier inversion plus the individual Weil bound (every level below
`ell - ceil(log2 ell)`).  So the exact enumerators contribute nothing at all to
the surviving top-`log2(ell)` conductor window.

The reason the Delsarte-Goethals machinery does not scale up here is worth
stating precisely, because it looks like it should.  DG families have exact
weight enumerators and are *exponentially large*: `DG(m, delta)` consists of
`Tr(sum_(k=1)^(delta-1) a_k x^(2^k+1))` with `a_k in F_(2^n)`, size
`2^(n(delta-1))`.  **Our family is the F_2-rational (subfield-restricted)
sub-family**: the coefficients are forced into `F_2` because they index
characters of `U`, not field elements.  The intersection of a `2^ell`-size
F_2-rational family with an exactly-enumerated F_(2^n)-rational family is the
`2^(O(log ell))` Gold-exponent corner.  **That subfield restriction is the
structural reason Kerdock/DG exactness cannot be imported at scale**, and it
is independent of, and stronger than, the lane's pairwise-rank refutation.

Subgroup sums are the one large exact family, and they are already in use: for
any subgroup `U_j^perp` of characters of conductor dividing `x^(j+1)`,
`sum_(chi in that subgroup) S(chi) = 2^j N_j(1)` exactly.  That is the lane's
conductor filtration/telescoping, so it yields nothing new.

Literature verified for this prong (web, 2026-08-20):
[Hammons-Kumar-Calderbank-Sloane-Sole, The Z4-linearity of Kerdock, Preparata, Goethals and related codes](https://arxiv.org/abs/math/0207208)
(IEEE-IT 40 (1994) 301-319);
[Kumar-Helleseth-Calderbank, An upper bound for Weil exponential sums over Galois rings and applications, IEEE-IT March 1995](https://ieeexplore.ieee.org/document/370147/)
-- this is the correct Carlitz-Uchiyama analogue for the Z4 sector, i.e. the
`|S| <= (d-1) 2^(n/2)` bound in the Galois-ring world;
[Improved bounds on Weil sums over Galois rings and homogeneous weights (2006)](https://link.springer.com/chapter/10.1007/11779360_32);
[Z4-linear codes obtained as projections of Kerdock and Delsarte-Goethals codes](https://www.sciencedirect.com/science/article/pii/002437959500239N).
For the concentration side, the classical binomial-approximation programme for
duals of BCH codes:
[On the distance distributions of BCH codes and their duals, Des. Codes Cryptogr.](https://link.springer.com/article/10.1023/A:1011220817609)
(improves Sidelnikov and Kasami-Fujiwara-Lin via Krawtchouk estimates).
These give *binomial approximation with an error term* for the tame sector,
which is the right shape but is stated for F_(2^n)-rational duals of BCH codes,
not for the subfield-restricted wild family, and the error terms are again
`L^2`-quality.

### 2026-08-20T16:45 -- dead ends recorded honestly

- "Delta is even" -- REFUTED (`ell = 13, 20, 24, 25, 27`).
- "`v_2(I_n(1)) <= 1`" (my first candidate reformulation, before I read far
  enough) -- REFUTED at `ell = 4` (`I_9(1) = 4`, `v_2 = 2`) and again at
  `ell = 27` (`v_2 = 3`).  Recorded because it is the obvious first guess and
  the next agent should not re-derive it.
- "`Delta != 1 mod 4` universally" -- holds for every row `13 <= ell <= 26`
  but is REFUTED at `ell = 27` (`Delta = 181465 = 1 mod 8`).  A twelve-row
  pattern that dies at row thirteen; a good reminder about this problem's
  false patterns.
- "McEliece divisibility of the tame sector could force `2^(ell+1) | S`" --
  the minimum McEliece `h` for the nonzero set `{i 2^j : i odd <= ell}` is
  `>= n / max_i w_2(i) ~ 2 ell / log2(ell)`, which is *below* `ell + 1` for
  all `ell >= 4` and gets relatively worse.  So even the sharp classical
  theorem, applied to the sector where it is legal, falls short by a factor
  `log2(ell)/2` **in the exponent**.  Dead.
- Pure `L^2`/energy/Cauchy across the character family -- REFUTED with exact
  numbers above; it is false by `sqrt(2 ell)`, which is why the lane's
  measured Cauchy losses were `304` and `633` at `ell = 12`.
- Delsarte LP with subgroup-indicator test functions -- reduces exactly to the
  conductor filtration the lane already runs.  A general LP over `U` is not
  obviously more than that; I did not find a formulation that escapes the
  same characterwise input.

---

## FINDINGS

### (a) Sharpest reformulation

Three, in increasing usefulness.

1. **Coding form.** Let `C` be the length-`2^n` code whose columns are
   `Phi(alpha) in U`.  Lemire at odd `n` says `C` has **at least two zero
   columns**; `A_1 = 1` is the failure mode.  The blocker
   `|Delta| <= 2^ell` versus Weil's `ell 2^ell` is, exactly,
   `2 g_ell = (ell-2) 2^ell + 2` versus `2^ell`: the log factor **is** the
   average L-degree (= average number of Frobenius eigenvalues) over the
   conductor filtration, `(ell-2)/2`.  Nothing about the method produces it;
   it is a genus.
2. **Divisibility form (Prong A, and its own refutation).**
   `I_n(1) = 0 <=> Delta = 1 - 2^(ell+1) <=> a_n = 2^ell (2^(ell+1)-1)`.
   Any lower-bound divisibility statement that helps must give `2 | Delta`;
   that requires precisely supersingularity of the Carlitz curve and is
   **false**.  The surviving target is an *upper* bound `v_2(I_n(1)) <= B(n)`,
   which no divisibility theorem can produce -- only an exact evaluation can,
   and Prong B shows the exactly-evaluable subfamily is `poly(ell)`-sized.
3. **Moment form (recommended).**  With `M_2k = sum_u (A_u - 2^(n-ell))^(2k)`
   over the `2^ell` Hayes classes:
   `(M_2k)^(1/2k) <= 2^ell` implies the odd endpoint.  Measured:
   `k=1` is **false** by `sqrt(2 ell)`; `k=2` is **true from `ell = 9` with
   exponential slack `2^ell / ell^3`**; `k=3` is true with more.  Since the
   fibre distribution is measurably Gaussian (kurtosis `2.81-2.99`), the whole
   conjecture is "the wild trace code's weight distribution has sub-Gaussian
   rather than Chebyshev tails".

### (b) Most promising technique

**The fourth-moment / `L^4` route, which the lane already selected, is the
right one, and my measurements say it is far safer than the ledger's prose
suggests: it holds with an exponential margin `2^ell/ell^3`, and the lane's
own sufficient bound `M_4 <= 16 ell^5 2^(3 ell)` is `ell^2` weaker than the
measured truth `M_4 ~ 0.6 ell^3 2^(3 ell)`.**  Concretely, an `M_4` proof may
discard a factor `2^(ell/4)` anywhere and still close the endpoint.  Nothing
else I examined has slack of that order.

For the analytic input, the one reference class the review note is missing:
**T-adic exponential sums** (Liu-Wan, Algebra & Number Theory 2009) and
especially **Haessig, arXiv:2606.10041 (June 2026)**, which proves rationality
and Newton-over-Hodge estimates for **partial L-functions of characters with
p-power conductor** -- verbatim this family, and newer than everything cited in
the Move-1 list.  Verify the `p = 2` hypothesis first; the Kramer-Miller-Upton
line explicitly excludes it.
For the exact-evaluation sector: Kumar-Helleseth-Calderbank (IEEE-IT 1995) is
the correct Carlitz-Uchiyama analogue over Galois rings and is the right tool
for the `conductor <= x^3` layer, but only that layer.

### (c) Decisive obstructions

1. **Ax-Katz/Chevalley-Warning proves Lemire for `n <= 7` and provably no
   further** -- and not because of a bad generating set: any system with
   `sum deg < n` would give `2 | N`, and `N_9(1) = 37` is odd.  PROVED +
   REFUTED with witness.
2. **No divisibility theorem can ever help.** The only usable conclusion is
   `2 | Delta`, which is false at `ell = 13, 20, 24, 25, 27`; the only
   hypothesis strong enough to produce it is exact supersingularity, refuted
   twice.  The needed 2-divisibility is `ell + 1` while characterwise slopes
   give `~2`; exactly `ell` of the gap is free from integrality of `N`, and the
   theorem is the one remaining bit.  PROVED (as an obstruction) + REFUTED (the
   target).
3. **Fixed-modulus congruences are noise.** `v_2(I_n(1))` over `n = 3..61`
   matches the law of a random 2-adic integer (`0 x 19, 1 x 7, 2 x 3, 3 x 1`).
   Any `mod 2^s` shortcut fails for a `2^(-s)` proportion of `n`.
4. **The `L^2`/energy route is false, not lossy**, by a factor `sqrt(2 ell)`;
   the deficit equals the mean L-degree of the family and is structural.
   Exact witnesses at `ell = 6, 8, 9, 11, 14, 15`.
5. **Exact enumerators cover only a `poly(ell)`-sized subfamily** (L-degree
   `<= 1`, i.e. conductor `| x^3`, plus Gold-exponent quadratic phases), and
   that subfamily sits inside the already-discharged low-conductor window.  The
   reason Kerdock/DG exactness does not scale is that our family is the
   **F_2-rational subfamily** of an F_(2^n)-rational exactly-enumerated one.
6. **The truth is `|Delta| ~ sqrt(ell) 2^(ell/2)`, an exponential margin below
   the required `2^ell`** -- so the barrier is categorically not tightness.
   Every method bounds `sum |lambda^n|` instead of `|sum lambda^n|`, and the
   angle equidistribution that would close it is unavailable at fixed `n` for a
   curve that grows with `n`.

### (d) Concrete next experiments runnable here

1. **Retire the Hayes transform for odd endpoints.**  `scratchpad/lemire_omp.c`
   computes any odd row by direct irreducibility enumeration:
   `ell = 24` in 2.3 s / ~1 MB versus 25m41s / 10.3 GB.  Rows `25..30` are
   already computed above and rows `31..34` are hours, not days, on one host
   (`2^ell` candidates, `n <= 63` fits `__uint128_t`; past `n = 63` needs a
   two-word representation).  This is a cheap, large extension of the committed
   odd-endpoint diagnostic range and a fourth independent check of `13..27`.
2. **Extend the fibre-moment table.**  `scratchpad/fibers.c` gives exact
   `M_2, M_4, M_6`, kurtosis, `min/max A_u`, and the two sufficient-test
   ratios for prime `n = 2 ell + 1`; `ell = 15` (`n = 31`) is done (2 min, row above) and
   `ell = 18, 20, 21` (`n = 37, 41, 43`) are minutes to an hour parallel.
   Deliverable: confirm `M_4 ~ c ell^3 2^(3 ell)` and pin `c`, and confirm the
   `M_4^(1/4)/2^ell` decay, so the lane's conjectured `M_4` fact acquires a
   measured asymptotic rather than a per-row pass/fail.  Extend to the even
   endpoint (non-prime `n` needs the proper-divisor terms) for symmetry.
3. **Split `M_2` and `M_4` by conductor level** and check the prediction
   `E|S(chi)|^2 ~ (j-1) 2^n` level by level.  If it holds exactly, the
   `(ell-1)/4` deficit is *proved* rather than measured, and the `M_4` target
   can be restated as a statement about **fourth moments of Frobenius angles
   within each conductor layer** -- which is where a Katz-Sarnak-style input
   could plausibly attach.
4. **Measure the tame sector alone.**  Compute
   `#{alpha : Tr(alpha^i) = 0 for all odd i <= ell}` (the order-two /
   subfield-dual-BCH sector, `2^ceil(ell/2)` classes) and its moments.  This
   separates "the wild Witt levels are the whole difficulty" from "even the
   dual-BCH sector already exhibits the `sqrt(ell)` deficit", which decides
   whether the Krawtchouk/binomial-approximation literature for duals of BCH
   codes is worth importing at all.
5. **Read Haessig arXiv:2606.10041 at equation level for `p = 2`** and, if it
   applies, compute its Newton-over-Hodge prediction against the lane's
   already-built exact cyclotomic Newton polygons (levels 2-10 measured at
   slopes `1/2, 1/4, 1/8`).  Cheap falsification of a new bridge.

### (e) New to the ledger

- The odd-endpoint rows `ell = 26, 28, 29, 30` (and `25`) are new committed
  values: `Delta = -102128, 32552, -221070, -238629` (and `-42333`), with
  `I` as tabulated.  Rows `13..27` independently reproduced by a third,
  algorithmically disjoint implementation.
- The **700x/10000x cheaper odd-endpoint algorithm** (direct enumeration
  instead of the Hayes Fourier transform), with timings.
- The genus identity `2 g_ell = (ell-2) 2^ell + 2` derived from the character
  count, and the resulting statement that **the blocker's `log n` factor is the
  mean L-degree of the conductor filtration** -- which explains, rather than
  merely records, the lane's measured Hast-Matei deficits `(ell-1)/2` and
  `(ell-1)/4`.
- The exact fibre-moment table with the two sufficient tests: `L^2` **false**
  by `sqrt(2 ell)` (witnesses at `ell = 6, 8, 9, 11, 14, 15`), `L^4` **true from
  `ell = 9`** with measured `M_4 ~ 0.6 ell^3 2^(3 ell)` and exponential slack.
  Also: the fibre distribution is Gaussian (kurtosis `2.81-2.99`), no Hayes
  class is empty in any computed row, and `max_u |A_u - mean| ~ 3.4 sigma`.
- **Ax-Katz proves Lemire for `n <= 7`** and is sharp: `N_9(1) = 37` odd kills
  every reformulation of the system.  A small but genuinely PROVED item that
  the ledger does not contain.
- Prong A closed with the supersingularity-is-the-only-sufficient-divisibility
  argument; Prong B closed with the F_2-rational-subfamily argument, which is
  independent of and stronger than the existing pairwise-rank Kerdock
  refutation.
- Literature not previously in the lane's lists: Liu-Wan T-adic exponential
  sums; Haessig arXiv:2606.10041 (partial L-functions of characters with
  p-power conductor, June 2026); Kumar-Helleseth-Calderbank Galois-ring
  Carlitz-Uchiyama; Blache-Ferard first-slope papers; the Krawtchouk-based
  binomial-approximation line for duals of BCH codes.
