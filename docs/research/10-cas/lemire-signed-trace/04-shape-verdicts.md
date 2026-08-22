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

## Shape 3 -- an arithmetic uncertainty principle (2-adic rigidity forces archimedean decorrelation)

*Verdict (landed 2026-08-22): refuted, with a proof of the obstruction.*

- **Literature.** Every implication in the slope literature (Wan Ann. Math.
  1993, Asian J. Math. 2004; Davis--Wan--Xiao 2016; Ren--Wan--Xiao--Yu 2018;
  Kosters--Wan 2018; Kramer-Miller--Upton IMRN 2023; Liu--Wan 2009; Newton-
  over-Hodge: Adolphson--Sperber, Zhu 2004, Kramer-Miller ANT 2021) runs
  p-adic to p-adic; none states an archimedean consequence. The only real
  bridge is integrality rounding (Moreno--Moreno AJM 1995, FFA 1998;
  Litsyn--Moreno--Moreno 1994; Helleseth--Kumar--Moreno--Shanbhag IEEE-IT
  1996 for `Z_4` trace codes), whose saving is additive `< 2^v`. Canonical
  counterexample: Stickelberger/Gross--Koblitz give `v_p(g(chi)) =
  s_p(a)/(p-1)` exactly while `|g(chi)| = sqrt q` always. Uncertainty
  principles (Tao MRL 2005, Meshulam 2014, Donoho--Stark) have no Frobenius
  content and no family version; Sawin--Sutherland (murmurations) use the
  term heuristically, archimedean on both sides. Rojas-Leon--Wan Math. Ann.
  2011 is l-adic and vacuous at fixed `q = 2`.
- **Data (exact `Z[zeta_{2^S}]` arithmetic, valuation via the norm).** At
  `(5,11), (7,15), (7,16)` the Newton-polygon slope multiset is constant on
  7 of 9 exact layers (DWX arithmetic progressions, e.g. `j=4: {1/4,1/2,3/4}`,
  `j=7,s=1: {1/3 x3, 2/3 x3}`) while `log2|S_n|` inside the same layers spans
  the full Weil range (e.g. layer `(6,3)` at `(7,15)`: one NP class,
  `log2|S_n| in [6.14, 7.83]`, Weil `9.82`); variance of `log2|S_n|`
  explained by NP class: `R^2 = 0.000 / 0.077 / 0.007`, and where classes
  split, the class with more 2-adic structure has the larger mean `|S_n|`.
  For 233 high-order layers across `ell = 12..24`, `log2(Weil_layer) -
  v_2(T_{j,s})` has min `6.00`, median `23`, max `30.3` (min `16.9` for
  `s >= 5`); the rounding mechanism needs `<= 0`. Ax--Katz exponents for the
  sparse trace system are `2..11`, below the observed `v_2`; `corr(v_2,
  log2(Weil/|T|)) = -0.236`. Over 16,646,144 exact twisted cylinder sums at
  `(24,49)`: `corr(v_2(A_psi), log2|A_psi|) = +0.003`, conditional mean
  `|A_psi|` flat to 0.7% across `v_2 = 0..8`, and the `v_2` histogram halves
  exactly (random-integer law). Coset products `P_psi` (fork B): within one
  NP class `|A_psi|` still varies by `1.8..6.2x`; `corr(v(p_n), log2|A_psi|)
  = +0.30, +0.49` (wrong sign); the one large outlier is the coset carrying
  the trivial character (a main term).
- **Obstruction, as a lemma.** Product formula: for `0 != beta in
  Z[zeta_{2^S}]`, `max_sigma |sigma beta| >= 2^{v(beta)}`, and the
  conjugates of `S_n(chi)` are the `S_n(chi^u)`, which lie in the same exact
  layer -- so 2-adic divisibility of one member certifies archimedean
  largeness of another (0 violations over 285 characters). Rounding ceiling:
  `T in Z, |T| <= W, 2^v | T` gives `|T| <= 2^v floor(W/2^v)`, and a factor
  `4 ell` saving then forces `floor(W/2^v) = 0`, i.e. `T = 0`. 2-adic rigidity
  is the property of being constant on the layer; a constant separates
  nothing. The 2-adic tower is closed as a source of archimedean cancellation;
  any surviving mechanism must be phase-aware.

## Shape 2 -- horizontal Sato--Tate at fixed `F_2` via automorphy

*Verdict (landed 2026-08-22): negative; the route is circular, and two new
exact facts rule out frequency-uniform or smoothed strategies.*

- **Method.** Every Hayes character of `E_j` via FFT over `prod Z/2^{e_k}`,
  its `L`-polynomial and `j-1` inverse roots; layer Weyl sums
  `w_{j,s}(m) = sum_theta e^{i m theta}/(#X (j-1))`, so that Weil is
  `|w(n)| <= 1` and `(HWO)` is `|w_{j,s}(n)| <= 2^{ceil(n/2)-n/2}/(4 ell)`
  -- a Weyl-criterion discrepancy bound at the single frequency `n`.
  54/54 cross-checks against the four-population identity; reached
  `j = 16, s = 5` (491,520 angles).
- **New exact law (fact 1).** `T_{j,s}(m) = +#X_{j,s}` for every odd
  `m < j` (171/171 instances, `j = 4..16`, all layers); also
  `sum_{chi in X} chi(1+x) = 0`, so `|w(1)| = 1/(sqrt2 (j-1))` and
  `sup_{1 <= m < j} |w(m)| = 1/(j-1)` exactly (attained). Consequence:
  `(HWO)`'s inequality is FALSE at low frequencies (by `2 ell/(j-1)` at
  `m = 1`, by `~4x` at even `m` in order-2 layers, e.g. `(13,1)`:
  `T(12) = +64 #X`). No frequency-uniform equidistribution theorem can
  prove `(HWO)`; the target is frequency-selective and lives only at
  `m >~ j`.
- **`m = n` is not anomalous.** Over 62 layer x endpoint instances
  (`j = 6..16`), the rank-quantile of `|w(n)|` among `m in [j, 6j]` has
  median `0.496` (KS vs uniform `sqrt(N) D = 0.45`); `|w(n)| sqrt(#A)` has
  median `0.72` (Rayleigh `1.18`); the Weyl constant `(j-1)|w(n)|` has median
  `0.11`, max `1.31`. Per-case: `(7,15)` 4/11 layers satisfy `(HWO)`,
  `(9,19)` 6/14, `(11,23)` 7/17; at `j = 16, s = 5`, `(j-1)|w(23)| = 0.034`
  and for `m >= j` the angles are indistinguishable from `U(N)`.
- **Smoothing is exactly self-defeating (fact 2).** Fejer windows `H =
  3..33` about `n` reduce `|w|` by the independent-frequency prediction
  (median smoothed/prediction `0.44..0.95`), and de-smoothing costs exactly
  `H`: for the admissible Weil polynomial `Q(T) = 1 - 2^{(n+1)/2}T^n +
  2^n T^{2n}`, `|p_m|/(D 2^{m/2}) = 0` for `m != n` and `0.7071` at `m = n`,
  and the `H = 9` Fejer average is `0.0786 = 0.7071/9` exactly. Strictly
  lossy.
- **Moments price the Rankin--Selberg input.** `M_2/((j-1)2^n)` median
  `0.967` (Keating--Rudnick diagonal), `M_4/M_2^2 ~ 2` (CUE); Cauchy--Schwarz
  over the layer is short of `(HWO)` by `5.2..11.4x` at `j <= 15` and by
  `40x` (odd `n`) / `57x` (even `n`) at `ell = 200`; Hoelder with higher
  moments runs the wrong way; the hook decomposition `p_n = sum_k (-1)^k
  s_{(n-k,1^k)}` has `j-1` terms whose leading dimension is `~10^164` at
  `ell = 200`.
- **Literature (two sweeps).** Katz IMRN 2013/2015/2017 are `q -> infinity`;
  Katz, Sato--Tate in the higher dimensional case (Enseign. Math. 2013):
  packetwise equidistribution only, classical refinement false in
  equicharacteristic (Rmk 3.7); no horizontal Sato--Tate over function fields
  exists. Fixed-`q` results stop at our line: Entin GAFA 2012 (`r <= d` at
  `p = 2`, non-decaying main term), Gorodetsky 2020 (`h/n > 1/2` only up to
  `e^{O(n loglog n/log n)}`), Gorodetsky--Kovaleva (one character over all
  `M_n`, saving `1/n`, restriction to primes stated open), Fu--Lau--Li--Xi
  IMRN 2025 (`h > d/2 - 1` wall), Sawin Duke 2021 ("not yet nontrivial in
  the large `n` limit"), Sawin--Shusterman Annals 2022 and arXiv:2512.24080
  (large `q`, squarefree moduli), Kowalski's Frobenius large sieve (needs
  `L^A <= sqrt q`), Lomeli--Navarro (Sym^k cuspidality via Lafforgue adds
  nothing analytic beyond rationality + Weil II).
- **Circularity.** Weyl's criterion at frequency `n` for this family is
  literally orthogonality: `sum_{chi in X} sum_i alpha_chi^n = -sum_{deg F
  = n} Lambda(F) sum_chi chi(<F>_j)` = the four-population integer. So
  "horizontal Sato--Tate at frequency `n`" is the target restated, not an
  input; the needed automorphic object is a first-moment bound with saving
  `4 ell`, which even moments cannot deliver.

## Shape 1, computational leg

*Verdict (landed 2026-08-22): closed; no small virtual object exists, for a
structural reason, and the effective dimension is exponential in `j`.*

- **Rebuilt from scratch** in exact `Z[zeta_M]` arithmetic (generator basis,
  exact discrete log, `L(chi,T)` from degree-ball transforms); 107/107
  agreements with brute-force enumeration over `F_2` (`j = 3..7`), `F_4`,
  `F_8`; `deg L = j-1` and purity checked on every character.
- **The four covers are nested**, `B, C subset A`, `B cap C = D`, so
  `A - B - C + D` is inclusion--exclusion and equals `X_{j,s}` with
  multiplicity `+1` everywhere: `T_{j,s}(n) = -p_n(prod_{chi in X} L(chi,T))`
  and the "virtual" module is the honest `H^1_c` of the layer, pure of weight
  one, rank exactly `#X_{j,s}(j-1)`. There is no negative part; the
  alternating combination is a selector, not a source of cancellation.
- **Effective dimension (distinct eigenvalues; two independent methods --
  factoring Galois-orbit products over `Q`, and Berlekamp--Massey on the
  integer sequence `n -> T_{j,s}(n)` -- agree on every row):** `j=7,s=3`:
  172/192; `9,4`: 972/1024; `11,4`: 5004/5120; `12,4`: 11086/11264; `13,4`:
  24274/24576 (ratio 0.988); for the top order the ratio rises toward 1 and
  the absolute dimension grows by `2.19..2.33` per unit `j`, i.e.
  `~2^{j-2}(j-1)`. Worst ratio anywhere `0.50` at `(11,1)`, a layer `(HWO)`
  does not need; `(HWO)` would need `1/(4 ell) = 1/800` at `ell = 200`. The
  formal bound is *attained exactly* at `(3,1)` for `n = 8,16,...`, `(3,2)`
  for `n = 12,24,...`, `(5,1)` at `n = 24,48,...`, `(5,2)` at `n = 60,...`, so
  no dimension count below `#X(j-1)` is even true.
- **The `q` direction** has a small object (closed forms `T_{3,1}(7;q) =
  q^4(q-1)`, `T_{3,2}(7;q) = q^4(q-1)^2` with 3 eigenvalues, `T_{5,1}(11;q) =
  (-1)^r q^7(q-1)`), caused by the scaling symmetry `u(x) -> u(cx)`,
  `c in F_q^*`, which forces `(q-1)`-fold eigenvalue repetition (verified on
  48/48, 192/192, 448/448 characters at `q = 4, 8`); it delivers exactly one
  square root of `q` and is empty at `q = 2` (`F_2^* = {1}`).
- **What is true:** in the window `n in [2j, 4j]`, `max_n |T|/2^{n/2}` is
  `1.5..7.9x sqrt(formal)`: square-root cancellation over the family; the
  missing `4 ell` is `sqrt(formal)/(4 ell) ~ 2^{j/2} sqrt j/(4j)`, a
  phase-cancellation statement over `2^{j-2}` characters, not a Betti count.

## Barrier (added 2026-08-22): moduli-only proofs cannot work

A fake population `F: E_ell -> R_{>=0}` with total mass `2^n`, every
low-conductor (`< a`) Fourier coefficient equal to the truth, every
high-conductor coefficient within the Weil bound for its conductor (by a
factor `~6..13`), conductor-one coefficient `0`, second moment below the
truth (ratio `0.22, 0.15, 0.12`), and `F(1) = 0`, exists at `(12,25)`,
`(16,33)`, `(20,41)` (construction: spread the deficit `-(2^n + sum_{0 <
cond < a} N^hat)` evenly over the high-conductor characters; verified
numerically, `min F = 0`, `F(1) = 0` to float precision). Hence no argument
whose only inputs are mass, nonnegativity, the exact low-conductor
populations, per-character Weil moduli and low moments can prove `(REL)`: a
proof must use that `N` is a Lambda-weighted prime count beyond its Fourier
moduli -- the population-level form of fork B's `Q^k` obstruction and of the
uncertainty reading of note 03.

## Net of the five shapes

All five are closed. Two structural facts stand out for any future attempt:
the layer sums are *exact* main terms at every odd frequency below the
conductor (`T_{j,s}(m) = +#X` for odd `m < j`), so the target is
frequency-selective; and the stabilizer/Clifford boundary sits exactly at
Witt order `4` with quadratic phase, beyond which every even moment is
Gaussian. The missing statement is a phase-alignment (delocalization) bound
at frequency `n ~ 2j` over a complete post-Clifford layer, invisible to all
moduli and moments; the four exact structures catalogued here and in note 02
are the only non-generic inputs left.
