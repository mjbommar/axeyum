# Ad hoc blocker sweep 2026-08-20 -- lane 08: Boolean function analysis and circuit-complexity correlation bounds

Agent: field specialist 08 (Boolean complexity / correlation bounds).
Scope: ad hoc research challenge, explicitly OUTSIDE roadmap, gates, and the
normal fact-ledger workflow. Nothing here changes lane state. Every claim is
labelled PROVED / REFUTED (with witness) / OPEN / EVIDENCE.

Epistemic rule used throughout: **finite computation is EVIDENCE, never a
theorem.**

---

## Log

### [t0] Orientation

Read, in order:
- `docs/research/10-cas/lemire-review-2026-08-20-reaim.md` (strategy review)
- `docs/plan/status/52-gf2-lemire.md` (lane ledger)
- `docs/research/10-cas/lemire-half-degree-irreducibles.md` (canonical note)
- `docs/research/10-cas/lemire-proof-unblocking-bridges.md` (bridges audit)

Repository facts I am taking as given (all already labelled in the lane ledger):

- PROVED (lane): `mu(f) = (-1)^degree chi_8(Disc(F))` on all of `GF(2)[x]`,
  including squareful inputs (the dyadic character kills even discriminants).
  Three checked realizations: factor parity, Stickelberger--Swan mod 8, Arf of
  the second trace form.
- PROVED (lane): the unrestricted `Disc(F) mod 8` phase has **odd** coefficient
  on the full-support monomial in every degree `k` (its mod-2 reduction is the
  parity of the squarefree population `(2^k-(-1)^k)/3`, which is odd).  So the
  global multilinear degree is `k-1`, i.e. **maximal**.
- REFUTED (lane, witness `(ell,k,d)=(9,11,8)`): fibrewise quadratic phase.
  `18,884` exact affine fibres, `130,048` points, `16,587` at-most-quadratic,
  `2,297` nonquadratic holding `61,264` points, **max support degree 7 on a
  7-dimensional fibre**.
- REFUTED (lane, same witness): generalized bentness -- **0 of 18,884** fibres
  have flat primitive `Z/8` Walsh spectra.
- REFUTED (lane): fibrewise second-trace-difference rank is bounded below --
  all even ranks `0..10` occur, including rank 0 (maximal correlation).
- Measured aggregation cascade at the pinned witness:
  `33,680` (fibrewise abs) -> `16,972` -> `3,956` -> `388` -> signed `-68`.

### [t1] Literature sweep 1: the correlation-bounds wall

All sources fetched live on 2026-08-20; none from memory.

**Viola, "Correlation bounds against polynomials", survey, 14 October 2022**
(<https://www.khoury.northeastern.edu/home/viola/papers/corr-survey.pdf>;
ECCC TR22-092, <https://eccc.weizmann.ac.il/report/2022/092/>).  Text extracted
locally with `pdftotext -layout`.  The state of the art is its Equation (6):

```text
2^(-n (log n)^Omega(1) ... /d^2)  <=  Cor(mod_3, d)
                                  <=  min{ 2^(-Omega(n/2^d)), O(d/sqrt(n)) }.   (Viola (6))
```

with the two upper bounds being:

- `Cor(mod_3, d) <= O(d/sqrt n)` -- Smolensky 1987 (survey Theorem 2), the
  Razborov--Smolensky regime.  Valid at **large** degree but only *polynomially*
  small, and vacuous once `d >= sqrt n`.
- `Cor(GIP_(d+1), d) <= exp(-Omega(n/(4^d d)))` -- Babai--Nisan--Szegedy 1992
  (survey Theorem 3), improved to `exp(-Omega(n/2^d))` in Viola 2006.
  **Exponentially** small but vacuous once `d >= log_2 n`.

The survey states the wall in one line: "while we are currently unable to make
the correlation small and the degree large simultaneously ... we can make the
correlation small and the degree large separately."  And, from Ivanov--Pavlovic
--Viola (CCC 2023, arXiv:2311.09370, fetched): *"Achieving correlation less
than 1/n for polynomials of degree log n remains open, for any explicit
function."*

**The barrier is specifically about our object.**  Viola's survey, section
"Barriers": Bhowmick--Lovett, "Nonclassical polynomials as a barrier to
polynomial lower bounds", CCC 2015 (arXiv:1412.4719, ECCC TR14-175,
<https://arxiv.org/abs/1412.4719>) "show that certain long-standing correlation
bounds ... are false for a generalization of polynomials known as non-classical
polynomials.  This means that, should those strong bounds be true, the proof
cannot apply to non-classical polynomials."

A **nonclassical polynomial** over `F_2` is exactly a map `P: F_2^n -> T=R/Z`
taking values in `2^(-(k+1)) Z / Z`, with degree measured by iterated additive
derivatives; `k` is its *depth*.  A `Z/8`-valued phase is a depth-2 nonclassical
polynomial.  **The Lemire blocker phase is literally a nonclassical polynomial
of depth 2**: `chi_8(Disc(F)Disc(F+h))` is the indefinite Gauss combination of
the four primitive additive phases `zeta_8^(j r)`, `j=1,3,5,7`, i.e. of the four
depth-2 nonclassical phases `r/8, 3r/8, 5r/8, 7r/8 mod 1`.  So the class named
by the field's own barrier theorem as the reason correlation bounds stop at
logarithmic degree is precisely the class this blocker lives in.

### [t2] Literature sweep 2: what the field has, and what it does not

Verified live 2026-08-20.

| Result | Statement | Regime | Source |
|---|---|---|---|
| Smolensky 1987/93 | `Cor(mod_3, d) <= O(d/sqrt n)`, `Cor(Maj, d) <= O(d/sqrt n)` | any `d`, but only *polynomially* small; vacuous at `d >= sqrt n` | Viola survey Thms 1--2 |
| Babai--Nisan--Szegedy 1992 | `Cor(GIP_(d+1), d) <= exp(-Omega(n/(4^d d)))` | *exponentially* small; vacuous at `d >= log_2 n` | Viola survey Thm 3 |
| Viola 2006 | `exp(-Omega(n/2^d))` | same wall | Viola survey |
| Ivanov--Pavlovic--Viola, CCC 2023 | refutes the CHHLZ Fourier-concentration conjecture; exact maxima for `d=2` | `d = 2`, partial `d = 3` | arXiv:2311.09370 |
| Berger--Sah--Sawhney--Tidor 2021/22 | `U^k` inverse theorem over `F_p` needs **classical** polys iff `k <= p+1`; **nonclassical** required for `k >= p+2` | over `F_2`: classical only for `U^3` (quadratic phases) | arXiv:2107.07495, Math. Proc. Camb. Phil. Soc. 173 (2022) |
| Tidor 2021/22 | first quantitative `U^4`-inverse bounds in characteristic 2 and 3 | `U^4` only | arXiv:2109.13108, Discrete Analysis 2022 |
| Tao--Ziegler 2011 | `U^(s+1)` inverse theorem over `F_p` in low characteristic, with **nonclassical** polynomial phases | all `s`, but qualitative/ineffective | arXiv:1101.1469 |
| Bhowmick--Lovett, CCC 2015 | the barrier: the sought strong bounds are **false** for nonclassical polynomials, and the standard techniques do not distinguish them | tight at logarithmic degree | arXiv:1412.4719 |
| Kumar--Helleseth--Calderbank 1995 | Weil-type bound for exponential sums over Galois rings, `<= (d-1) sqrt(q)`-shape; tight for Kerdock and Delsarte--Goethals | Galois rings `GR(2^k, m)` | IEEE Trans. Inform. Theory 41(3):456--468 |
| Hammons--Kumar--Calderbank--Sloane--Sole 1994 | `Z_4`-linearity of Kerdock/Preparata/Goethals; exact `Z_4` quadratic Gauss-sum evaluation is the engine | quadratic `Z_4` phases | IEEE Trans. Inform. Theory 40:301--319, arXiv:math/0207208 |
| Bhrushundi--Harsha--Srinivasan, STACS 2017 | polynomial approximation over `Z/2^k Z`: agreement is **monotone increasing** in `k` | `Z/2^k` phases | arXiv:1701.06268 |
| Milicevic 2019 / Janzer 2020 / Cohen--Moshkovitz 2021 | partition rank vs analytic rank polynomially/uniformly equivalent | **tensors**, and Cohen--Moshkovitz needs the field large relative to the rank | arXiv:2102.10509 and refs therein |

Two entries deserve emphasis because they cut against the black-box route directly:

- **Bhrushundi--Harsha--Srinivasan** prove that moving from `F_2` to `Z/2^k` phases can only *help* the approximator.  Our phase is a `Z/8` phase, i.e. exactly the direction in which correlation bounds get *weaker*, not stronger.
- **Cohen--Moshkovitz / Janzer / Milicevic** polynomial bias-rank bounds are for **multilinear tensors** (and, for Cohen--Moshkovitz, over large fields).  Reducing a degree-`d` polynomial to a multilinear form needs `d < char`; in characteristic 2 with `d = 7` that reduction fails, which is precisely the low-characteristic gap Tao--Ziegler had to fill with nonclassical polynomials.  So the polynomially-bounded half of structure-vs-randomness is not available for this object at all.

### [t3] Independent reimplementation and reproduction of the pinned witness

I did **not** use repository code.  Scripts are in the session scratchpad
(`/tmp/claude-1000/-home-mjbommar-projects-personal-axeyum/f980d106-.../scratchpad/`):
`expA_phase.py`, `expA2_anf.py`, `expB_autocorr.py`, `expC_fibres.py`,
`expD_scaling.py`, `expE_signs.py`.  Integer discriminants via `sympy`,
`GF(2)` factorization written from scratch (distinct-degree via `x^(2^i) mod f`),
`Z/8` subset-Mobius transforms written from scratch.

**Command / result A1** (`python3 expA_phase.py 9`): for every monic
`f in GF(2)[x]` of degree `1..9` (1022 polynomials), `mu(f)` computed by
squarefree test plus distinct-degree factor count agrees with
`(-1)^deg chi_8(Disc(lift f))` -- **0 mismatches**.  Independent confirmation of
the lane's Swan/Stickelberger identity (finite evidence; the lane's own proof is
what carries it).

**Command / result A2** (`python3 expA2_anf.py`): on the constant-term-one slice
`f = x^k + (t<<1) + 1`, the `Z/8` ANF of `t -> Disc mod 8` has, for every
`k = 2..11`, full-support coefficient `1,3,5,7,1,3,1,7,5,3` -- **odd in every
degree** -- and **max `Z/8` support degree exactly `k-1`**, i.e. maximal.
Independent confirmation of the lane's proved full-support result.

**Command / result C** (`python3 expC_fibres.py 9 11 8`), the pinned witness
`(ell,k,d)=(9,11,8)`.  Reading the lane's filter out of
`accumulate_binary_dyadic_shift_fibres` (the fibre condition is
`(I[t] xor I[t^s]) >> (d+1) == 0`, i.e. the truncated-inverse difference must lie
in the low interval -- this is the multiplicative-coset restriction, and it is
*not* a plain autocorrelation), my from-scratch implementation returns:

```text
fibres=18884   points=130048   max fibre dim=8
at-most-quadratic fibres=16587   nonquadratic=2297 (points 61264)
max Z/8 ANF degree=7             full-degree fibres=5540
generalized-bent fibres=0
nonquadratic signed=-202         nonquadratic abs=8622
fibrewise absolute total=33680   signed off-diagonal total=-68
```

Every one of these nine integers matches the values documented in
`lemire-half-degree-irreducibles.md` and `52-gf2-lemire.md`.  I also reproduce
the documented `Delta=138` at `(ell,k,d)=(6,9,5)` -- the row the lane cites as
forcing the factor two in the connected candidate.  **The lane's checker is
confirmed by a fully independent implementation** (this is evidence about the
tool, which the repository's own CLAUDE.md warns is the thing that most often
lies here).

Dead end recorded: my first pass (`expB_autocorr.py`) computed the *unrestricted*
autocorrelation `sum_(h != 0) sum_f mu(f)mu(f+h)` and got `-314` on the same
1024-polynomial / 127-shift domain, which does **not** match the lane's `-68`.
I nearly filed that as a discrepancy.  It is not one: the lane's sum is
restricted by the inverse-coset filter above.  Noting the near-miss because the
unrestricted values coincidentally hit documented numbers at *different*
parameters (`-68` at `(k,s)=(9,6)`, `-314` at `(11,7)` and `(13,9)`), which is
exactly the shape of a false "reproduction".

### [t4] New measurement: the second moment of the fibre correlations

The lane prints `fibrewise_absolute_correlation` (the `l1` mass) and the signed
total, but **not** the `l2` mass.  That is the quantity my field cares about,
because it separates *counting* from *sign cancellation*.  Writing `c_F` for the
exact signed dyadic-character correlation of fibre `F`, and
`Delta = sum_F c_F`:

Command: `python3 expD_scaling.py` and `python3 expE_signs.py`
(both under 3 minutes, well under 2 GB).

```text
 ell   k  d    #fib       pts   Delta    sum|c|        l2   2^((k+d+1)/2)  l2/target  Delta/l2   sum c^2 / 2^(k+d-1)
   4   6  3      28       128      -2        34       8.2           32.0     0.2577    -0.243   0.263
   4   7  3      56       256     -14        90      14.0           45.3     0.3094    -1.000   0.383
   5   7  4     100       576     -28       152      20.2           64.0     0.3156    -1.386   0.399
   5   8  4     200      1152       6       306      29.7           90.5     0.3285    +0.202   0.431
   6   8  5     308      1920     -32       512      38.4          128.0     0.2997    -0.834   0.360
   6   9  5     616      3840     138      1098      59.8          181.0     0.3302    +2.309   0.436
   7   9  6    1252      8448      16      2252      88.9          256.0     0.3473    +0.180   0.482
   7  10  6    2504     16896     -96      4420     120.5          362.0     0.3328    -0.797   0.443
   8  10  7    4804     32256    -128      8236     167.0          512.0     0.3263    -0.766   0.426
   8  11  7    9608     64512    -188     17052     240.8          724.1     0.3325    -0.781   0.442
   9  11  8   18884    130048     -68     33680     347.4         1024.0     0.3392    -0.196   0.460
   9  12  8   37768    260096    -236     65808     483.3         1448.2     0.3337    -0.488   0.446
```

Three facts fall out, all **EVIDENCE, not theorems** (12 rows, `ell = 4..9`,
both endpoint parities, `k = ell+2` and `k = ell+3`, `d = ell-1`):

1. **The second moment is uniform and already meets the target.**
   `l2 / 2^((k+d+1)/2)` sits in `[0.258, 0.348]` on every row, with no drift in
   `ell` and no parity split.  Equivalently
   `sum_F c_F^2 <= 0.49 * 2^(k+d-1)` on all twelve rows.
2. **The signed total sits exactly at the independent-sign scale.**  The twelve
   values of `Delta / l2` are
   `-0.243, -1.000, -1.386, +0.202, -0.834, +2.309, +0.180, -0.797, -0.766,
    -0.781, -0.196, -0.488`, with **mean `-0.317` and sample sd `0.953`**.  An
   independent-random-sign model predicts mean `0`, sd `1`.  The data is
   indistinguishable from it at this sample size.
3. **Both ANF sectors behave the same way.**  At the pinned witness, splitting
   the 18,884 fibres by `Z/8` ANF degree:

   ```text
   quadratic (deg<=2)     16587 fibres  signed=+134  abs=25058  l2=250.9  |signed|/l2=0.534
   nonquadratic (deg>=3)   2297 fibres  signed=-202  abs= 8622  l2=240.3  |signed|/l2=0.841
   ```

   The nonquadratic sector carries **essentially half the `l2` mass** with 12% of
   the fibres, and cancels at the same scale.  So the nonquadratic sector is not
   a small perturbation to be absorbed, and it is not the obstruction either.

4. **Gauss-sum structure survives past the quadratic sector.**  Of the 12,915
   fibres with `c_F != 0`, **12,456 have `|c_F|` an exact power of two**
   (histogram of `|c_F|`: `0:5969, 2:10281, 4:1986, 6:334, 8:175, 10:67, 12:22,
   14:20, 16:14, 18:9, 20:2, 22:1, 24:2, 26:1, 34:1`).  A quadratic `Z/8` phase
   on an affine space has Gauss sum exactly `0` or `+-2^(dim - rank/2)`; the
   measurement says 96.4% of the nonzero fibre correlations have that shape even
   though only 88% of the fibres are quadratic.

#### The reformulation this buys

Because `sqrt(0.49) * 2 = 1.40 < 2`, the following is an **exact factorization of
the lane's connected candidate** into a counting half and a sign half:

```text
(E2)  sum_F c_F^2  <=  2^(k+d-1)                 [pure counting; no signs]
(S)   |sum_F c_F|  <=  2.87 * ( sum_F c_F^2 )^(1/2)   [square-root cancellation,
                                                       absolute constant]
(E2) and (S)  ==>  |Delta|^2 <= 2^(k+d+1)         [the connected candidate]
```

Measured margins: `(E2)` holds with a factor `>= 2.07` on every row; `(S)` is
satisfied with observed constant `<= 2.31`, against the `2.87` that `(E2)` leaves
room for.  So the two halves are simultaneously satisfiable on all data, and
nothing is lost in the split.

**This is the sharpest reformulation I can give.**  It changes the character of
the blocker: it is *not* "beat a termwise bound by a factor `ell`".  It is
"prove a second-moment count, and then prove that a specific family of
Arf/Gauss-sum signs cancels at the square-root scale with an absolute constant".
The first half is a counting problem (Parseval-shaped, no cancellation needed);
the second half is a Mobius-randomness statement one level down.

### [t5] BARRIER DIRECTION -- verdict

The charge was: would the needed cancellation, posed black-box for an arbitrary
degree-7 `F_2`-polynomial phase against affine structure, break the
Razborov--Smolensky-era wall?

**Answer: it is worse than that -- the black-box statement is outright FALSE,
and I can give the witness and the exact factor.**  Three levels:

1. **Black-box at the fibre level is REFUTED by a degree-**zero** witness.**
   The fibres are affine subspaces and the phases are `Z/8`-valued of ANF degree
   `<= 7`.  An adversary allowed to pick any such phase picks the *constant*
   phase `q_F == 1` on every fibre.  Then `sum_F c_F = 130,048` at the pinned
   witness, against the target `2^((k+d+1)/2) = 1024`: off by a factor
   `127 = 2^(d-1)`, asymptotically `~2^ell`.  Degree is not the operative
   constraint at all.
2. **Black-box *conditioned on the measured second moment* is still REFUTED.**
   Give the adversary `(E2)` for free and let it choose only the signs: it takes
   them all equal, giving `|sum_F c_F| = sum_F |c_F|`, which under `(E2)` can be
   as large as `sqrt(#F) * l2 = sqrt(18884) * 347.4 = 47,700` -- off by `47x`.
   **Every bit of the remaining difficulty is in the signs**, and no bound that
   is uniform over sign patterns can supply it.
3. **In the ambient view we are also far past the `log n` wall.**  The phase as
   a function on `F_2^(k-1) x F_2^d` has `n = k-1+d ~ 2 ell` variables and, by
   the full-support result I re-verified in [t3], multilinear degree `k-1 ~ ell
   ~ n/2`.  The state of the art (Viola survey Eq. (6)) gives exponentially
   small correlation only for `d << log_2 n`, and merely `O(d/sqrt n)` -- which
   is `>1` here -- for larger `d`.  For an explicit function, "correlation less
   than `1/n` at degree `log n`" is open (Ivanov--Pavlovic--Viola).  We need
   correlation `~2^(-n/2)` at degree `~n/2`.  That is not one step past the
   wall; it is the trivial-function regime.

Add the structural coincidence that makes this pointed: our phase is a **depth-2
nonclassical polynomial**, and nonclassical polynomials are precisely the class
Bhowmick--Lovett named as the barrier -- the class for which the sought strong
bounds are *false* and which the standard techniques cannot distinguish.  The
Bhrushundi--Harsha--Srinivasan monotonicity (`Z/2^k` approximation only improves
with `k`) points the same way.

**Conclusion, stated plainly: the black-box route is hopeless, and structure is
mandatory.**  The `ANF degree 7` figure is, moreover, a red herring for
technique selection: the lane's own witness has `5,540` of `18,884` fibres whose
ANF degree *equals their affine dimension*.  On those fibres the phase is an
arbitrary function of its variables, so no degree-parameterized theorem --
Razborov--Smolensky, BNS, Gowers `U^(d+1)`, bias-vs-rank -- has any content
fibrewise.

### [t6] STRUCTURE DIRECTION -- what algebraic structure actually buys

Surveying what is available, against the two halves `(E2)` and `(S)`:

- **Exact quadratic Gauss-sum evaluation over `Z/4`, `Z/8` (Galois rings).**
  This is the one technique in the neighbourhood that produces *exact values*
  rather than lossy bounds, and my measurement says it applies to 96.4% of the
  nonzero fibre correlations (powers of two).  Machinery:
  Hammons--Kumar--Calderbank--Sloane--Sole (IEEE IT 40:301--319, 1994) for the
  `Z_4` case, with the sign the Arf/Brown invariant.  **Transferable, and it is
  the right tool for `(E2)`**: exact values turn the second moment into a
  *counting* problem over `(rank, Arf)` strata.
- **Weil bounds over Galois rings** (Kumar--Helleseth--Calderbank, IEEE IT
  41(3):456--468, 1995) carry the same `(d-1) sqrt(q)` degree factor and are
  *tight* for Kerdock and Delsarte--Goethals.  So they reproduce exactly the
  factor the lane must beat.  **Not transferable to `(S)`.**
- **Kerdock-style uniform high rank.**  REFUTED for this family by the lane's
  own uncollapsed pairwise rank test (all even ranks `0..10` including rank
  zero).  My measurement is consistent: 5,969 fibres have `c_F = 0` (degenerate,
  linear part off the image) while a handful reach `|c_F| = 34` on a
  `dim <= 8` fibre.  This family is *not* a bounded-class Kerdock/DG family.
- **Sparse / few-monomial exponential-sum bounds** (Cochrane--Pinner,
  Bourgain, Shparlinski school).  REFUTED as a mechanism by the lane's exact
  spectral measurement -- all 512 characters nonzero at both native primes, for
  each of the four primitive phases.  There is no sparsity to exploit.
- **Correlation bounds for `Z/2^k` phases.**  The only quantitative statement I
  found pointing at this object is Bhrushundi--Harsha--Srinivasan's
  *monotonicity*, and it points the wrong way.
- **Multiplicative-coset structure (truncated inverse groups).**  In the
  classical setting the multiplicative analogue of what is wanted is
  Burgess-type amplification, which buys sub-Weil savings for *incomplete* sums
  only.  Our sum is complete over its fibres; Burgess has nothing to give.  What
  the coset structure *does* buy is already used: it is the filter
  `(I[t] xor I[t^s]) >> (d+1) == 0` that cuts `1024 x 255` pairs down to the
  130,048 that carry the affine fibre structure at all.

### [t7] The toy problem, in this field's normal form

> **Problem T (family of `Z/8` quadratics with Arf phases).**
> Let `P` be a finite index set.  For each `p in P` let `A_p` be an affine
> subspace of `F_2^m` and `q_p : A_p -> Z/8` a nonclassical quadratic (`Z/8` ANF
> degree `<= 2` in affine coordinates), i.e. a depth-2 nonclassical polynomial of
> degree `<= 3`.  Put
> ```text
> G(p) = sum_(x in A_p) chi_8(q_p(x))   in { 0 } union { +- 2^j },
> ```
> the sign being the Arf/Brown invariant of `q_p` and `j = dim A_p - rank(q_p)/2`.
> Prove `|sum_p G(p)| <= C ( sum_p G(p)^2 )^(1/2)` for an absolute constant `C`,
> for the Lemire family
> `P = {(shift, input coset, exact inverse difference)}`,
> `q_p(t) = Disc(F_t) Disc(F_(t+h)) mod 8`.

Status: **OPEN.**  Measured on 12 rows: `C = 2.31` suffices (mean of the signed
statistic `-0.317`, sd `0.953`).  Statement `(E2)` supplies the companion
counting bound with a factor-2 margin, and together they give the lane's
connected candidate exactly.

The reason `T` captures the blocker and is not a caricature: (a) the measured
sector split shows the quadratic sector already carries the majority of the
mass and cancels at the same scale as the whole; (b) 96.4% of nonzero `c_F` are
powers of two, so `G(p)` really does have the Gauss-sum shape; (c) the lane
proved the *sign* of a quadratic `Z/8` phase's Gauss sum is exactly the Arf
invariant of the second trace form, so `T`'s sign family is the actual object.

**Verdict on technique classes for `T`:**

| Class | Reaches `(E2)`? | Reaches `(S)`? | Why |
|---|---|---|---|
| Exact `Z/4`/`Z/8` Gauss-sum evaluation (Galois ring, Arf/Brown) | **Plausibly yes** | No | Turns the second moment into a count over `(rank, Arf)` strata; produces exact values, so no constant is lost.  Gives no information about sign *correlation* across `p`. |
| Hypercontractivity / Bonami | No | No | The `(2,4)` constant at ANF degree 7 is `3^(7/2) = 46.8`, already larger than the entire fibrewise-to-target margin `33680/1024 = 32.9` at the pinned witness.  Moment comparison never yields sign cancellation in a structured index. |
| Level-`k` inequalities | No | No | Require Fourier mass concentrated at low levels; REFUTED by the lane's exact full-support measurement (all 512 characters nonzero, conductor populations `1,1,2,4,...,256`). |
| Gowers norms + inverse theorems | No | No | Over `F_2` the inverse theorem needs nonclassical phases from `U^4` up (Berger--Sah--Sawhney--Tidor); quantitative bounds exist only for `U^4` (Tidor); degree 7 needs `U^8`, where only Tao--Ziegler's ineffective result exists.  Structurally, an inverse theorem is a dichotomy and cannot certify a constant-factor square-root bound. |
| Bias vs rank (Green--Tao, Kaufman--Lovett, Janzer/Milicevic/Cohen--Moshkovitz) | No | No | The polynomially-bounded results are for multilinear tensors, and the multilinearization step needs `deg < char`; in char 2 at degree 7 it fails, leaving only tower/Ackermann bounds.  Also REFUTED pointwise by the lane's rank-zero second-trace pairs. |
| Galois-ring Fourier analysis (Kerdock/DG) | Partially | No | Exact evaluation transfers; the Weil bound over Galois rings carries the very `(d-1)` factor to be beaten and is *tight* for Kerdock/DG. |

Nothing in my field reaches `(S)`.  `(S)` is a Mobius-randomness statement with
an absolute constant -- the same species as Chowla and as "primes in
`[x, x+sqrt x]`" -- and every tool above is lossy by an unbounded factor by
construction.  **The only route with a chance is the exact-evaluation one, and
its natural output is a renormalized instance of the same problem at half the
size** (cancel `mu` at level `n` by evaluating quadratic Gauss sums exactly, and
you are left with cancelling Arf signs over an index set of size `~2^(n/2)`).
That self-similarity, not any single missing lemma, is what I would call the
real obstruction.
### [t8] A better normalization for the counting half: `(E2')`

Command: `python3 expF_energy.py`.  Exact integer second moments:

```text
 ell  k  d    #fib      pts    sum c^2   factorization              /2^(k+d-1)   /pts
   4  6  3      28      128         68   2^2 * 17                      0.2656   0.531
   4  7  3      56      256        196   2^2 * 7^2                     0.3828   0.766
   5  7  4     100      576        408   2^3 * 3 * 17                  0.3984   0.708
   5  8  4     200     1152        884   2^2 * 13 * 17                 0.4316   0.767
   6  8  5     308     1920       1472   2^6 * 23                      0.3594   0.767
   6  9  5     616     3840       3572   2^2 * 19 * 47                 0.4360   0.930
   7  9  6    1252     8448       7904   2^5 * 13 * 19                 0.4824   0.936
   7 10  6    2504    16896      14520   2^3 * 3 * 5 * 11^2            0.4431   0.859
   8 10  7    4804    32256      27904   2^8 * 109                     0.4258   0.865
   8 11  7    9608    64512      57968   2^4 * 3623                    0.4423   0.899
   9 11  8   18884   130048     120680   2^3 * 5 * 7 * 431             0.4604   0.928
   9 12  8   37768   260096     233576   2^3 * 7 * 43 * 97             0.4455   0.898
```

The factorizations (`3623`, `431`, `109` prime) say there is **no exact closed
form** -- `(E2)` is a genuine inequality, not an identity.  But the last column
gives the natural normalization.  Since

```text
sum_F c_F^2 = N_points + sum_F sum_(x != y in F) eps(x) eps(y),
```

where `N_points` is the number of contributing `(f,h)` pairs and `eps` the dyadic
character value, the statement

```text
(E2')  sum_F c_F^2 <= N_points
```

is exactly **"the within-fibre off-diagonal correlation is non-positive"**.
It holds on all twelve rows with ratios `0.53 .. 0.936`, and it is *stronger*
than `(E2)` by a factor two because `N_points ~ 2^(k+d-2)` (measured within 5%
on every row).  `(E2')` is self-normalizing -- no exponent bookkeeping, no `ell`
dependence -- and it is a pure four-point count, the kind of statement Parseval
and inclusion--exclusion can actually deliver.  Paired with `(S)` at constant
`C <= 2^1.5 = 2.83` it still gives the connected candidate.

**Risk, stated honestly:** the `/pts` ratio drifts upward (`0.53 -> 0.936` over
`ell = 4..9`).  If it crosses `1`, `(E2')` is false and only the weaker `(E2)`
survives.  The odd family (`k = ell+2`) is the one drifting; the even family
(`k = ell+3`) looks flat at `0.86..0.93`.  Deciding this is the single cheapest
high-value experiment left, and it needs `ell = 10, 11, 12` -- out of reach for
my Python, routine for the lane's Rust report.

### [t9] Dead ends and near-misses (recorded so nobody repeats them)

1. **Unrestricted autocorrelation is the wrong object** and coincidentally
   reproduces documented numbers at the wrong parameters (see [t3]).  The
   inverse-coset filter `(I[t] xor I[t^s]) >> (d+1) == 0` is load-bearing.
2. **"ANF degree 7" is not a usable hypothesis.**  5,540 of 18,884 fibres have
   ANF degree equal to their affine dimension.  A theorem quantified over
   "degree `<= 7` phases" is a theorem about arbitrary functions on those fibres.
3. **Sparsity / low-level Fourier concentration**: refuted by the lane's exact
   full-support measurement before I started; my histogram is consistent (the
   `c_F` distribution has a long tail out to `|c_F| = 34`).
4. **Uniform Kerdock-style high rank**: refuted by the lane; 5,969 of 18,884
   fibres have `c_F = 0` (degenerate) and rank-zero pairs exist.
5. **Hypercontractivity as a route**: I checked the arithmetic rather than the
   slogan.  Bonami at ANF degree 7 costs `3^3.5 = 46.8`; the entire available
   margin at the pinned witness (`sum|c_F| / target = 33680/1024`) is `32.9`.
   One application of the tool costs more than the whole saving.
6. **Looking for an exact formula for `sum_F c_F^2`**: the prime factorizations
   kill it.  `(E2')` is the right shape instead.

---

## FINDINGS

### (a) Sharpest reformulation

The blocker factors **exactly**, with no slack lost, into a counting half and a
sign half.  With `c_F` the exact signed dyadic-character correlation of affine
fibre `F` and `Delta = sum_F c_F`:

```text
(E2')  sum_F c_F^2 <= N_points          -- the within-fibre off-diagonal
                                           correlation is non-positive.
                                           Pure four-point count, no signs.
(S)    |sum_F c_F| <= C (sum_F c_F^2)^(1/2),  C an absolute constant (C = 2.83
                                           suffices given (E2')).
(E2') and (S)  ==>  |Delta|^2 <= 2^(k+d+1)   -- the lane's connected candidate.
```

Measured on 12 rows (`ell = 4..9`, both parities): `(E2')` holds with ratios
`0.53..0.936`; `(S)` holds with observed `C <= 2.31`, and the normalized
statistic `Delta / l2` has mean `-0.317`, sd `0.953` -- **indistinguishable from
an independent-sign model**.  So the residual difficulty is not "a factor `ell`
beyond a termwise bound"; it is **square-root cancellation with an absolute
constant, in the fibre index, for a family of Arf/Gauss-sum signs**.

### (b) Most promising transferable technique

**Exact `Z/8` (Galois-ring) quadratic Gauss-sum evaluation with the Arf/Brown
sign, used to prove the counting half `(E2')` -- not to bound the signed sum.**
It is the only technique in this neighbourhood that returns *exact values*
rather than bounds with unbounded constants, and my measurement says it covers
96.4% of the nonzero fibre correlations (12,456 of 12,915 have `|c_F|` an exact
power of two).  It converts `(E2')` into a count over `(rank, Arf)` strata.

- Hammons, Kumar, Calderbank, Sloane, Sole, "The `Z_4`-linearity of Kerdock,
  Preparata, Goethals and related codes", IEEE Trans. Inform. Theory 40 (1994)
  301--319, <https://arxiv.org/abs/math/0207208>.
- Kumar, Helleseth, Calderbank, "An upper bound for Weil exponential sums over
  Galois rings and applications", IEEE Trans. Inform. Theory 41(3) (1995)
  456--468 -- **use for the exact `GR(2^k,m)` framework, not for the bound**:
  its `(d-1)sqrt(q)` degree factor is the very thing to be beaten and is tight
  for Kerdock/Delsarte--Goethals.

### (c) Decisive obstructions

1. **The black-box route is REFUTED, with witnesses, not merely blocked.**
   Fibre-level black-box: the constant phase (ANF degree **zero**) gives
   `130,048` against a target of `1024` at the pinned witness -- off by
   `2^(d-1) = 127`, asymptotically `2^ell`.  Black-box conditioned on the
   measured second moment: an all-equal sign pattern gives `47,700` against
   `1024` -- off by `47x`.  **All of the content is in the signs**, so no
   sign-uniform estimate can ever reach it.  Structure is mandatory.
2. **We are in the trivial-function regime of correlation bounds, not one step
   past the wall.**  Ambient `n = k-1+d ~ 2 ell` variables, multilinear degree
   `k-1 ~ n/2` (I independently re-verified full support for `k = 2..11`).  The
   state of the art (Viola survey Eq. (6)) is exponentially small correlation
   only for `d << log_2 n`, and `O(d/sqrt n) > 1` here otherwise; "correlation
   `< 1/n` at degree `log n`" is open for *any* explicit function.  We would
   need `~2^(-n/2)` at degree `~n/2`.
3. **The phase is a depth-2 nonclassical polynomial -- the named barrier class.**
   Bhowmick--Lovett (CCC 2015) show the sought strong bounds are *false* for
   nonclassical polynomials and that the standard techniques cannot tell them
   apart; Berger--Sah--Sawhney--Tidor show that over `F_2` the inverse theorem
   requires nonclassical phases from `U^4` upward; Bhrushundi--Harsha--
   Srinivasan show `Z/2^k` approximation only gets *better* as `k` grows.
4. **No quantitative inverse theorem exists above `U^4` over `F_2`** (Tidor
   2022 is `U^4`; degree 7 needs `U^8`, where only Tao--Ziegler's ineffective
   result exists).  And an inverse theorem is a dichotomy: structurally
   incapable of certifying a constant-factor square-root bound.
5. **The bias-vs-rank machinery's polynomially-bounded half does not exist in
   characteristic 2 at degree 7.**  Multilinearization needs `deg < char`;
   Janzer/Milicevic/Cohen--Moshkovitz are tensor statements (and the last needs
   a large field).  What remains in low characteristic is tower/Ackermann-type.
6. **Self-similarity.**  Exact evaluation of the quadratic sector does not end
   the problem: it replaces `sum mu` at level `n` by a signed sum of Arf
   invariants over an index set of size `~2^(n/2)` -- the same species of
   statement, half the size.  This, and not a missing lemma, is what I judge
   the real obstruction to be.
7. **Quantified tool cost.**  Bonami/hypercontractivity at ANF degree 7 costs
   `3^3.5 = 46.8`, exceeding the entire fibrewise-to-target margin `32.9` at the
   pinned witness.  Level-`k` inequalities are refuted by the measured full
   Fourier support.

### (d) Concrete next experiments, runnable here

1. **[highest value, cheap] Extend the `(E2')` ratio `sum_F c_F^2 / N_points` to
   `ell = 10, 11, 12`, both parities.**  My Python tops out at `ell = 9`;
   `binary_dyadic_autocorrelation_fibre_report` already computes every `c_F`, so
   this is one added accumulator (`sum c_F^2`) in the existing Rust report.  The
   ratio drifted `0.53 -> 0.936` over `ell = 4..9`; whether it crosses `1`
   decides whether `(E2')` or only `(E2)` is the right counting half.  Nothing
   else in the split can be settled without this.
2. **Print `l2` alongside `l1` in the fibre report.**  The lane currently records
   `fibrewise_absolute_correlation` and the signed total but not
   `sum_F c_F^2`; that single number is what separates the counting half from
   the sign half, and it is free.
3. **Stratify `c_F` by `(rank, Arf)` on the quadratic sector** and check whether
   `(E2')` is provable stratum by stratum -- i.e. whether the count of fibres
   with `|c_F| = 2^j` matches the Gauss-sum prediction from the rank
   distribution.  This is the direct test of whether the Galois-ring exact
   evaluation route can carry `(E2')`.
4. **Isolate the 459 fibres whose `|c_F|` is not a power of two** at the pinned
   witness.  They are the genuinely non-Gauss objects; if they are also the ones
   resisting the `(rank, Arf)` stratification, they are the precise residue of
   the problem and a much smaller target than "2,297 nonquadratic fibres".
5. **Test the sign family for multiplicativity in the normalized parameter
   `h_0/w_0 = f(f+h)`.**  If `sign(c_F)` is multiplicative (or a character) in
   that parameter, the lane's existing Witt aggregation becomes a genuine
   second-level character sum and Weil applies once more -- which is the only
   concrete mechanism I can see for `(S)`.

### (e) For the ledger

- **Independent confirmation (EVIDENCE):** a from-scratch Python/sympy
  reimplementation reproduces **all nine** documented integers of the pinned
  witness `(ell,k,d)=(9,11,8)` -- `18884 / 130048 / 16587 / 2297 / 61264 / 7 /
  0 bent / -202 / 8622 / 33680 / -68` -- and the documented `Delta = 138` at
  `(6,9,5)`.  The lane's `binary_dyadic_autocorrelation_fibre_report` is
  validated by an implementation that shares no code with it.
- **New uncredited candidate `(E2')`:** `sum_F c_F^2 <= N_points`, equivalently
  "the within-fibre off-diagonal dyadic correlation is non-positive".  Holds on
  12 measured rows with ratio `0.53..0.936`, upward-drifting.  With `(S)` at
  `C <= 2.83` it implies the existing connected candidate exactly.  **Finite
  evidence only.**
- **New measurement:** `l2 / 2^((k+d+1)/2) in [0.258, 0.348]` on all 12 rows,
  no drift, no parity split; `Delta / l2` has mean `-0.317`, sd `0.953` over the
  same rows.  The fibre signs are indistinguishable from independent signs.
- **New measurement:** 12,456 of 12,915 nonzero `|c_F|` at the pinned witness
  are exact powers of two -- Gauss-sum structure extends well past the 88%
  quadratic sector.
- **New measurement:** 5,540 of 18,884 fibres have `Z/8` ANF degree equal to
  their affine dimension.
- **Stopping result (REFUTED, with witness):** the black-box correlation-bound
  route is false, not merely unproved -- constant fibre phases give `130,048`
  vs the `1024` target at the pinned witness, and even conditioning on the
  measured second moment leaves an all-equal-sign adversary at `47,700`.
  Recommend recording this so no future lane re-opens "find a degree-7
  correlation bound".
