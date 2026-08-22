# Lemire signed-trace lane: the five "of course" shapes, verdict diary

Status: running diary, started 2026-08-22. Five Opus agents were launched,
one per candidate shape of a solution (see the end of note 03's discussion),
each required to (a) check primary literature (WebSearch + SerpAPI Scholar),
(b) test ideas exactly with our CAS/data, and (c) return a verdict with the
precise statement that would have to be proved. Entries are appended as the
reports land, so that nothing here is re-derived or re-refuted later. Scratch
files: `lemire-signed-trace.shape<k>.*` in the session scratchpad. No entry
is proof credit.

Companions: [01-target-and-toolkit.md](01-target-and-toolkit.md),
[02-mechanism-hunt.md](02-mechanism-hunt.md),
[03-uncertainty-analogy.md](03-uncertainty-analogy.md).

## Shape 1 -- a Witt-tower trace formula with a small virtual character

*Hypothesis.* `T_{j,s}` is the trace of Frobenius on a virtual representation
(alternating combination of the four ASW quotient covers) whose effective
dimension is polynomial in `j`.

*Literature leg (landed 2026-08-22, morning).*

- **Katz, IMRN 2013 (Witt vectors / Keating--Rudnick)** treats the layer sum
  explicitly: in the proof of Thm 8.1 the divided Weyl sum over all primitive
  characters is bounded by `C(p,n,Xi)/sqrt(#k)` with
  `C(p,n,Xi) = sum_i h^i_c(Prim_n (x) F_p-bar, Xi(L_univ))` -- this is
  exactly the effective dimension. Verbatim: "At present, we do not know
  uniform bounds for these sums of Betti numbers `C(p,n,Xi)` as `p` varies
  (`n` and `Xi` fixed)." **Thm 8.2** gives the only polynomial bound,
  `3 dim(Xi) #Prim_n(k)/((n-1) sqrt(#k))`, and only for `p > 2n-1`, where
  Witt characters degenerate to ordinary Artin--Schreier `L_{psi(f)}` and
  `h^1_c = Swan - rank`. So the one published polynomial effective-dimension
  bound for a layer sum lives exactly where the Witt structure collapses;
  `p = 2`, `j -> infinity` is stated as open in print. Katz IMRN 2015
  (Entin--Keating--Rudnick) repeats the obstacle and excludes `p in {2,3}`.
- **Sawin, arXiv:1805.04330** (twists by Witt-vector Dirichlet characters):
  `G_geom >= SL_N` for `d >= 4` via Guralnick--Tiep, moments `= k!`, with the
  explicit disclaimer that uniformity is not pursued and `q -> infinity` is
  required. Sawin--Shusterman arXiv:2512.24080 (Dec 2025) is fixed-`q` but
  needs large `q`, squarefree moduli, and slopes `<= 1` at infinity (ours has
  Swan `= j`): excluded on all three counts. Forey--Fresan--Kowalski--Sawin
  (quantitative sheaf theory) bounds Betti sums uniformly in the
  characteristic, but the constants depend on the ambient dimension, which
  for `Prim_j` is `Theta(j)`: cannot give polynomial-in-`j`.
- **Davis--Wan--Xiao, Math. Ann. 2016, section 1** defines the exact-order
  product `P(m,s) = prod_{m_chi = m} L(chi,s)` of degree
  `(p-1)p^{m-1}(p^{m-1}d - 1)` with Cor. 1.3 giving its slopes; Kosters--Wan
  (PAMS 2018 + corrigendum 2019) give the genus formula and, in Prop. 4.9, an
  `phi(p^j)`-weighted exact-order decomposition of the genus -- the closest
  published analogue of Moebius-over-the-tower, at the level of
  degree/genus only. **No paper states the four-term (conductor x order)
  alternating combination or treats a layer sum as a trace on a virtual
  object.**
- Effective-dimension literature: Katz "Sums of Betti numbers in arbitrary
  characteristic" (FFA 2001), Adolphson--Sperber, Bombieri are exponential in
  ambient dimension (reproduce `2^j` on `Prim_j`). No "stable cohomology of
  Artin--Schreier covers" paper exists; Bergstrom--Diaconu--Petersen--
  Westerland (arXiv:2302.07664) and Zhao Yu Ma (arXiv:2606.26440, homological
  vanishing for character sums over `F_q[t]`) are tame/Hurwitz, not wild ASW.
- The `(x,0,0,...)` tower over `F_2` (`d=1`): Kosters--Wan Example 4.10 gives
  `g_n = (4^n - 3 2^n + 2)/6 = 0,1,7,35,155,...`; DWX's exact-order degree
  `2^{m-1}(2^{m-1}-1)` cross-checks; the Newton polygon is ordinary (Wan
  arXiv:1912.01571 Ex. 5.7 via Liu--Wan Thm 2.9). No exact `L`-functions or
  point counts are tabulated anywhere (Kosters--Zhu Problem 5 asks for an
  algorithm).

*Computational leg.* Pending (effective dimension from extension-field
traces at small `(ell, n)`).

## Shape 4 -- positivity you can see

*Verdict (landed 2026-08-22): no manifest-positivity identity; one genuinely
new exact identity, one factor short, now quantified.*

- **Enabling observation.** The identity class is literally
  `{x^n + g : deg g <= floor(n/2)}`, so it can be enumerated and factored
  member by member for `ell <= 20` in seconds (`ell=20, n=42`: 4,194,304
  factorizations), reproducing the branch dumps exactly (`N_18(1) = 525216`
  at `n=37`, `N_20(1) = 2100267` at `n=41`, `N_12(1) = 8551` at `n=25`).
- **New exact identity (Chebyshev / Type-I dual).** With `h = n - ell` and
  `L_d = sum_{F in class} sum_{Q = P^k, deg Q = d, Q | F} Lambda(Q) >= 0`,
  Type-I exactness gives `L_d = 2^{n-ell}` for every `d <= h`, hence

  ```text
  sum_{d=h+1}^{n} L_d = ell 2^{n-ell}   (exact; all terms >= 0; L_n = N_ell(1)),
  N_ell(1) = 2^{n-ell} - sum_{d=h+1}^{n-1} E_d,   E_d = L_d - 2^{n-ell}.
  ```

  Verified on 36 pairs `(ell, n)`, `ell = 3..20`. It converts the needed
  lower bound into an upper bound on `ell-1` sparse-class prime counts
  (Brun--Titchmarsh-shaped). What it lacks, exactly: the target needs relative
  accuracy `1/(2(ell-1))` on the tail (measured `0.0263` at `(20,41)`,
  `0.0132` at `(20,42)`); Brun--Titchmarsh caps at constant `2`; Weil per `d`
  costs `~0.85 (ell-1)^2` against `2(ell-2)` for the bare route and `~3.1 ell`
  for the Haar telescope (loss factors: `ell=20`: 610/879 vs 36 vs 43;
  `ell=200`: 67545/95688 vs 396 vs 625). The `E_d` cancel heavily across `d`
  (`sum |E_d| / |sum E_d|` = 7.5, 35.6, 40.0 at `(12,25)`, `(18,37)`,
  `(20,41)`), which term-by-term bounds destroy.
- **Killed.** Divisor moments are prime-free: `sum_{class} d(F) = (n+1)
  2^{n-ell}` exactly, and `sum d_3(F)` is reproduced exactly from ball triple
  correlations with no primes (deviations `-4, +24, -24, +264, -96, +312` at
  `(4,9)...(9,19)`), so the explicit group-ring zeta `Z(T)` carries no
  positivity certificate beyond `T Z'/Z`. Rank test: eight exact class
  statistics over 36 rows have rank 8/8 (9/9 with constant): no relation.
  Even-endpoint square identity confirmed (8 pairs) but its odd term is
  `~2^{n/4}`. `D = N_ell(1) - 2^{n-ell}` changes sign across the dumps
  (`+359, -896, ..., +4787`), so `D` itself cannot be made nonnegative;
  `C + B` is within 1.1% of `B`, so `(REL)` has enormous absolute margin and
  the difficulty is purely the `ell` factor.
- **Literature.** No published identity writes a ray-class prime count as a
  manifestly nonnegative quantity with a usable lower bound; Oesterle/Serre
  positivity (Hallouin--Perret TAMS 2019; Beninati arXiv:2602.19781) only
  upper-bounds point counts; no Harman/Chen-type lower-bound sieve exists in
  `F_q[T]` (Hsu JNT 1996 and Bagshaw--Kerr Mathematika 2025 are
  Brun--Titchmarsh upper bounds); Ha arXiv:1601.06867 has the right shape
  with non-explicit `delta`. **New lead:** Kandhil--Languasco--Moree
  arXiv:2607.14515 (Jul 2026) beat the RH-only least-prime bound using pair
  correlation of zeros; in `F_q[t]` the pair correlation of Hayes-character
  zeros is a studied object. Also Bagshaw CJM 2026 (arXiv:2401.10399) and
  Cheng arXiv:2605.25877 (odd `q`).

## Shape 5 -- a Clifford-hierarchy cancellation theorem

*Verdict (landed 2026-08-22): no; stabilizer-type exactness stops at an
exactly located boundary, and every even moment of a post-Clifford layer is
Gaussian.*

- **Setup verified.** `S_n(chi)` computed as the exact mixed-radix DFT of the
  dumps (`ell = 12..24`); layer sums reproduce the four-population `T_{j,s}`
  to the last digit and `#X_{j,s}` matches `h_{j,s}` on every row.
- **Clifford boundary is exact and sharp.** The pure `Z/4` Teichmueller
  layer `(j,s) = (2,2)` (Kerdock form) has `S = +-2^{(n-1)/2}(1 +- i)`
  exactly, `|S| = 2^{n/2}`, `arg = +-pi/4`, attaining the KHC/Weil bound
  (ratio `1.0000`), with `T_{2,2} = +-2^{ceil(n/2)}` (odd part `1`) for odd
  `n` and `0` for even `n`. The first post-Clifford layer `(4,3)` has
  non-half-integer `log2|S|` and generic odd parts (`2^8 193`,
  `-2^10 289`, ...). Exact algebra in `Z[zeta_{2^s}]^+`: `|S|^2` leaves `Z`
  for 46,512 of 46,592 order-`>=8` characters at `(12,25),(14,29),(16,33)`;
  the 80 exceptions all lie in `(15,3)` at `(16,33)` and contribute exactly
  `0`. The stabilizer sub-family's share of the order-`<=4` layer sums falls
  to `0.06` by `j = 15`.
- **No collapse of the aggregate: moments are Gaussian.** At `(22,45)`,
  `M_2/(#X (j-1) 2^n) = 0.995..1.004`, `M_4/(2 #X ((j-1)2^n)^2) =
  0.96..0.98`, `M_6/(6 #X (.)^3) = 0.91..0.94` -- the complex-Gaussian /
  Diaconis--Shahshahani values `m!(j-1)^m`. `max|S|/((j-1)2^{ceil(n/2)})
  = 0.47..0.55` for `s >= 3`. Consequence: Hoelder from the `2m`-th moment
  gives `|T| <= (m!)^{1/2m} #X sqrt(j-1) 2^{n/2}`, strictly worse than
  Cauchy--Schwarz for `m >= 2`; Cauchy--Schwarz is short of `(HWO)` by
  `4 ell/sqrt(2(j-1))` = `13.9x` at `(22,21)` and `40.2x` at `(200,199)`;
  the truth is at the random-phase scale `|T|/sqrt(M_2) in [0.13, 2.0]`.
  The needed saving is invisible to every `|.|^{2m}`.
- **MacWilliams/Pless route is circular.** For the `Z/2^s` trace code the
  weight-one dual words with `lambda = 1` are exactly the identity-class
  elements, so the dual distance is `1` and its multiplicity is the
  conjecture's unknown; no power moment is forced from outside.
- **Literature.** Cui--Gottesman--Krishna PRA 2017 gives exactly the level
  dictionary (`zeta_{2^s}` phase of Boolean degree `d` at level `s+d-1`),
  nothing on sums. Exact aggregates exist only at degree 2: Sloane--Berlekamp
  1970 (rank counts of quadratic forms), Can--Rengaswamy--Calderbank--Pfister
  2020 (Kerdock weights / unitary 2-design), Hangleiter et al. 2024 (second
  moment of the degree-2 layer; Nechita--Singh: degree-`n` circuits have the
  same second moment). For `s >= 3` only bounds (KHC 1995, Ling--Oezbudak
  2004, Lahtonen--Ling--Sole--Zinoviev 2004). Dalzell--Harrow--Koh--La Placa,
  Quantum 2020, Thm 8: the aggregate of a complete degree-3 layer is provably
  Gaussian -- a no-collapse theorem whose numbers match our `M_4, M_6`.

## Shapes 2, 3 and the computational leg of shape 1

Pending.
