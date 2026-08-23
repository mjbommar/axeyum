# Lemire signed-trace lane: the open target, its restatements, and the toolkit

Status: research note, 2026-08-21. Nothing here is a proof. The lane's job is
to build a genuinely new fixed-`F_2`, growing-conductor signed-trace theorem
that closes the one open estimate in the Kaser--Lemire chain. This note is the
bottom rung: what exactly must be proved, what it is equivalent to, what the
literature and the previous lane have already closed, and which tools we have
checked are actually available and correct.

Sources of record:

- The five-page proof roadmap in the sibling repository
  `../lemire-half-degree-irreducibles/paper/main.tex` (21 Aug 2026). Its
  numbered steps 1--4 and 6 are proved; step 5, the estimate `(HWO)` (or any
  other proof of `(REL)`), is open.
- The previous lane's ledger on branch `agent/gf2/lemire-proof` (295 commits
  ahead of `main`, not merged; read with `git show`, never checked out). Its
  status file `docs/plan/status/52-gf2-lemire.md`, the expert brief
  `docs/research/10-cas/lemire-high-witt-expert-brief.md`, and the 4,894-line
  research contract `docs/research/10-cas/lemire-half-degree-irreducibles.md`
  on that branch carry the negative-route record. This lane does not repeat a
  route that ledger closed without a new input.
- A fresh primary-source sweep (2026-08-21) of Katz's Witt-vector papers,
  the Galois-ring exponential-sum literature, the Artin--Schreier--Witt Newton
  slope literature, Sawin--Shusterman (including their 2025 short-trace
  theorem), and the prescribed-coefficient literature; verdicts are in
  section 4.

## 1. The open estimate, exactly

Fix `ell >= 200` and `n in {2ell+1, 2ell+2}`. Let

```text
E_j    = (1 + x F_2[x]) / (x^{j+1}) = (F_2[x]/x^{j+1})^x,   |E_j| = 2^j,
<F>_j  = x^{deg F} F(1/x) mod x^{j+1}                    (monic F),
N_j(g) = sum_{F monic, deg F = n, <F>_j = g} Lambda(F),
H_j(b) = N_j(b) - N_j(b + x^j)        (b in E_j with x^j-coefficient 0),
C_{ell,n} = sum_{j=a}^{ell} 2^{j-1} H_j(1),   a = ell - ceil(log2 ell) - 1,
B_{ell,n} = 2^{2ell} - 2^{ceil(n/2)} sum_{1<=j<a} (j-1) 2^{j-1}  (> 0).
```

`deg(f - x^n) <= floor(n/2)` is `<f>_ell = 1`, so the conjecture asks for a
prime of degree `n` in the identity ray class of `E_ell`. The Haar telescope
and the proper-power count (proved) reduce this to

```text
(REL)   C_{ell,n} > -B_{ell,n}.
```

The order-resolved sufficient statement uses the power subgroups
`2^s E_j = {u^{2^s}} = {polynomials in x^{2^s} mod x^{j+1}}`:

```text
h_{j,s} = 2^{j - floor(j/2^s)},      P_{j,s} = sum_{g in 2^s E_j} N_j(g),
T_{j,s} = h_{j,s} P_{j,s} - h_{j,s-1} P_{j,s-1} - h_{j-1,s} P_{j-1,s} + h_{j-1,s-1} P_{j-1,s-1}
        = sum over characters chi of E_j of exact conductor j and exact order 2^s of S_n(chi),
S_n(chi) = sum_{deg F = n} Lambda(F) chi(<F>_j) = -(sum of n-th powers of the j-1 inverse roots of L(chi,T)).
```

Let `c = ceil(log2 ell)` and `Q` the largest power of two with `3cQ <= ell`.
Layers with `2^s <= Q` are paid by the individual Weil bound
`|S_n(chi)| <= (j-1) 2^{ceil(n/2)}`. The open theorem is

```text
(HWO)   4 ell |T_{j,s}(n)| <= #X_{j,s} (j-1) 2^{ceil(n/2)}
        for every a <= j <= ell and every nonempty layer with 2^s > Q,
```

and `(HWO) => (REL) =>` conjecture is proved (endpoint ledger replayed on the
branch for `200 <= ell <= 1024`). Every nonempty high layer has
`q = 2^s` not dividing `j` (else the layer is empty), so
`Delta_{j,s} = 2P_{j,s}-P_{j-1,s}` is literally the signed imbalance of the
newly exposed coefficient `x^j` over `q E_j`. The exact reduction of `(HWO)`
has a necessary conductor/order case split. Write `d_s = floor((j-1)/q)` and,
when `q/2` does not divide `j`, put `R = 2^{d_{s-1}-d_s}`.

```text
nonresonant (q/2 does not divide j):
  T_{j,s} = 2^{j-1-d_{s-1}} (R Delta_{j,s} - Delta_{j,s-1}),
  #X_{j,s} = 2^{j-1-d_{s-1}} (R-1),
  so 4 ell |R Delta_{j,s} - Delta_{j,s-1}|
       <= (R-1)(j-1) 2^{ceil(n/2)}.                         (NSD)

resonant (q/2 divides j, q does not):
  T_{j,s} = #X_{j,s} Delta_{j,s} = 2^{j-1-d_s} Delta_{j,s},
  so 4 ell |Delta_{j,s}| <= (j-1) 2^{ceil(n/2)}.             (RSD)
```

Thus only the nonresonant layers compare consecutive precisions. For
`delta_s = Delta_{j,s}/2^{d_s}`, their normalized form is

```text
4 ell |delta_s-delta_{s-1}|
  <= (1-1/R)(j-1)2^{ceil(n/2)} / 2^{d_s};
```

the factor `2^{-d_s}` is essential. The resonant layers are not an exceptional
small-level phenomenon: at the eventual first row `ell=j=200`, order `q=16`
is high, `8 | 200`, and `16` does not divide `200`. They require a direct
sparse-discrepancy estimate `(RSD)`. The remaining work is therefore a
uniform square-root-scale theorem over the polynomially many (`< 8 ell^3`)
sparse classes, with these two targets. For the top order at conductor `j`,
write `m = floor(log2 j)` and `u = 1 + x^{2^m} = (1+x)^{2^m}`. If `j` is not
a power of two, that layer is nonresonant and `(NSD)` reads
`4 ell |H_j(1) - H_j(u)| <= (j-1) 2^{ceil(n/2)}`. If `j=2^m`, it is resonant:
the direct target is instead `4 ell |H_j(1)| <= (j-1)2^{ceil(n/2)}`.

Scale check (what makes this the critical line). At `j` near `ell`, each
population in `Delta` is about `2^{n-j} ~ 2^{n/2+1}`, the Weil error per
character is `(j-1) 2^{n/2}`, and the required layer saving is a factor `4ell
~ 2n`. So the estimate demands a logarithmic saving over Weil, uniformly in
`ell`, while any random model predicts a saving of order `2^{(j-d_s)/2}`.
Three standard reductions cannot supply even the logarithm:

- Cauchy--Schwarz over the layer plus *any* second moment: rms size of
  `S_n(chi)` is `sqrt(j-1) 2^{n/2}` (Keating--Rudnick variance), so
  `|T| <= #X sqrt(j-1) 2^{n/2}` and one would need `sqrt(j-1) >= 4 ell`.
- Large sieve: modulus `2^j` against length `2^n` with `n ~ 2j` is exactly
  critical, no saving.
- Type I / Type II: Type I sums are *exact* once the free factor has degree
  `>= j` (perfect equidistribution in `E_j`), but the bilinear Type II range
  sits at `deg d ~ deg e ~ j ~ n/2` and orthogonality plus Cauchy--Schwarz
  returns error `2^{n/2} x (log factors)`, the same loss. The branch's
  characteristic-two inverse-energy bound (Bagshaw-type) is proved and does not
  change this.

The theorem must therefore use the *signs* inside the layer.

## 2. Three equivalent formulations (all checked numerically in this lane)

### 2.1 Witt / Galois-ring form

`Lambda(F_2) = 1 + x F_2[[x]]` is the big Witt ring of `F_2`, and by
Artin--Hasse (Katz, *Witt vectors and a question of Keating and Rudnick*,
IMRN 2013, Lemma 2.2) `E_j = BigWitt_j(F_2) = prod_{k odd <= j} Z/2^{e_k}`,
`e_k = floor(log2(j/k)) + 1`, with `1 - aX` going to `(a^k, 0, ...)` in the
`k`-th factor. The class of `alpha in F_{2^n}` (its characteristic polynomial
reversed) is the Witt trace of the Teichmueller lift, so with `teich(alpha)`
the Teichmueller lift in the Galois ring `GR(2^s, n)`:

```text
class(alpha) in E_j  <->  ( Tr_{GR(2^{e_k},n)/Z_{2^{e_k}}}( teich(alpha)^k ) mod 2^{e_k} )_{k odd <= j},
2^s E_j              <->  { Tr(teich(alpha)^k) = 0 mod 2^{min(s, e_k)} for all odd k <= j },
P_{j,s}              =    #{ alpha in F_{2^n} : those congruences },
N_ell(1)             =    #{ alpha : Tr(teich(alpha)^k) = 0 mod 2^{floor(log2(ell/k))+1} for all odd k <= ell }.
```

The odd endpoint (`N_ell(1) = 1 + n I_n(1)`) is then: *there is a nonzero
`alpha in F_{2^n}` all of whose odd-power Galois-ring traces vanish to the
prescribed dyadic precisions.* The characters of `E_j` are the Galois-ring
polynomial phases `zeta_{2^s}^{Tr(sum_k c_k teich(alpha)^k)}` of
Kumar--Helleseth--Calderbank, whose weighted degree is Katz's Swan conductor
`max_k k 2^{e_k - 1 - v_2(c_k)} = j`; the exact order is
`2^{max_k (e_k - v_2(c_k))}`. `scripts/lemire-signed-trace/lemire_witt.py`
constructs `GR(2^s,n)`, the Teichmueller set, and the traces, and checks that
`alpha -> class` and `alpha -> trace vector` factor through each other
bijectively; verified for `(n,j)` in `(7,3), (9,4), (11,5), (13,6), (15,7),
(16,8)`.

This is the formulation in which the high layers live: for `2^s > Q` only
`O(log ell)` odd `k` have `e_k >= s`, so `P_{j,s}` imposes full-precision
vanishing on those few low-degree traces and is otherwise the identity class.

### 2.2 Short-interval form

The identity class of `E_ell` is the short interval
`I(x^n, h) = {x^n + g : deg g < h}`, `h = n - ell = floor(n/2) + 1`, of length
`2^h in {2, 2 sqrt 2} x 2^{n/2}`. The conjecture is Legendre's conjecture over
`F_2[t]` centred at `x^n`: a prime in `[X, X + 2 sqrt X]`. The Riemann
hypothesis is a theorem here and is exactly a logarithm short; for large `q`
(Bank--Bary-Soroker--Rosenzweig, Keating--Rudnick, Katz) and for fixed large
`q` (Sawin) the interval is reachable, for `q = 2` it is not.

### 2.3 Population / nested-subgroup form

With `delta_s = Delta_{j,s} / 2^{d_s}` the per-class mean imbalance on
`2^s E_j`, `(NSD)` is `4 ell |delta_s - delta_{s-1}| <= (1 - 1/R)(j-1)
2^{ceil(n/2)}`: the mean imbalance of the new coefficient barely moves when the
power subgroup is refined one dyadic step. In Galois-ring terms the refinement
from `2^{s-1}E_j` to `2^s E_j` imposes "bit `s-1` of `Tr(teich^k)` vanishes"
for the `k` with `e_k >= s`. This is the form a direct Witt-tower argument
would attack (section 5, candidate A).

## 3. What the tools actually say (numbers, not prose)

Exact values reproduced independently by the Python anchor
(`scripts/lemire-signed-trace/lemire_anchor.py`, flint-backed, < 1 s):

```text
(ell,n) = (5,11):  N_5(1) = 45 = 1 + 11 I_11(1),  C_{5,11} = -608,   B = 1024
(ell,n) = (7,16):  N_7(1) = 472,                    C_{7,16} = -4608,  B = 15872
```

Both `C` values are the ones the branch ledger pins as its sign-boundary
regression (negative in the already-smooth odd regime). At `(5,11)` every
primitive character's `L`-polynomial, built from the Fourier transforms of the
degree balls `{g : deg g <= m}`, has all inverse roots of modulus `sqrt 2` and
its `n`-th power sum equals the direct character sum; every layer sum by
direct character summation equals the four-population integer, and the
character counts by (conductor, order) match `h_{j,s}`.

Cross-check against the branch CAS (built in a lane snapshot of
`agent/gf2/lemire-proof`, `axeyum-gf2-hayes-endpoint 12`, 0.1 s): it prints
`odd=359|even=335`, which are exactly the Python anchor's
`N_12(1) - 2^{n-12}` at `n = 25, 26` (`8551 - 8192`, `16719 - 16384`;
17 s and 37 s on 32 processes).

Calibration of the layer ratio `|T_{j,s}| / (#X (j-1) 2^{ceil(n/2)})` at
`ell = 12` (requirement `1/(4 ell) = 0.0208`; `(HWO)` is only claimed for
`ell >= 200`, so these are scale, not evidence): `n = 25` ranges `0.0009 --
0.066` over 17 layers (11 below threshold), `n = 26` ranges `0.0008 -- 0.176`
(9 below). The worst layers at this size are low order (`s = 1, 2`) at low
conductor; the top-conductor high-order layers (`j = 11, 12`, `s = 3, 4`) are
the smallest. The branch's fleet data reach `ell = 23, 24` and are the place to
look at the trend; this table is only to fix the scale.

Pure top-Witt-direction characters are not special. The Galois-ring Gauss sums
`G_s(c) = sum_{alpha in F_{2^n}} zeta_{2^s}^{c Tr(teich(alpha))}`, normalised by
`2^{n/2}`, are exactly `1` at `s = 2` (the Kerdock / `Z_4` value) and generic
for `s >= 3`: at `n = 11, s = 3` the four odd `c` give `2.948, 0.933, 0.933,
2.948` against the KHC bound `3`; at `s = 4` values range `0.12 -- 3.6` against
`7`. So there is no supersingular or otherwise rigid structure in the
Teichmueller-trace direction to exploit; the high-order cancellation must be
collective.

## 4. Literature verdicts (primary sources checked 2026-08-21)

| Source | What it gives | Verdict for fixed `q = 2`, whole layer |
| --- | --- | --- |
| Katz, IMRN 2013 (Witt vectors / Keating--Rudnick); IMRN 2015 (Entin--K--R); IMRN 2017 (Rudnick--Waxman) | Artin--Hasse splitting of `BigWitt_n`, Swan conductor `k 2^{e_k-1-v}` (Lemma 3.1), `L` of degree Swan-1 pure weight 1, `G_geom >= SL(n-1)` incl. `p = 2`, equidistribution as `q -> oo` with non-uniform Betti constant; Galois action `Lambda -> Lambda^a` only for `a` prime to `p`; super-even characters over `F_2` have order <= 2 | Structure used (sec. 2.1). No fixed-`q` estimate; constants explicitly unknown in `j`. |
| Kumar--Helleseth--Calderbank 1995; Shanbhag--K--H 1996; Ling--Oezbudak 2004/2006 | Weil bound for Galois-ring phases, weighted degree = Swan | Per-character baseline `(j-1) 2^{n/2}`; nothing on layer sums or trace distributions as precision grows with `n`. |
| Liu--Wan 2009 (T-adic); Davis--Wan--Xiao 2016; Kosters--Wan 2018; Kosters--Zhu; Kramer-Miller--Upton; Ren--Wan--Xiao--Yu; Haessig 2026 | Newton slopes of ASW towers at fixed `q`, Galois-conjugate characters share slopes, layer products in `1 + s Z[s]` | 2-adic divisibility of the integer layer sums only; the branch priced this at divisibility by 8, no archimedean credit. |
| Hayes 1965; Keating--Rudnick 2014; Gao 2021; Gao--Kuttner--Wang 2022 | Orthogonality, explicit formula, exact total `L`-degree of a layer (`d_h = 2^h`, `D = (ell-2)2^ell + 2` over `F_2`) | Main term and error of the same exponential order at the endpoint; exact degree does not remove the factor `ell-2`. |
| Gorodetsky 2020 | Fixed `q`, large `n`, intervals down to square-root scale | Error `2^{n/2-h-1} e^{O(n loglog n / log n)}` is not `o(1)` at `h = n/2`. |
| Sawin--Shusterman, Annals 2022; Sawin, Duke 2021; Inventiones 2022 | Twin primes / Chowla / square-root cancellation in short intervals for `q > 685090 p^2` (odd `p`), `q > p^2 e^2`; Duke error `3C (n+2)^{2n-h} q^{(h + ...)/2}` | Explicit Betti constants exponential in `n` swamp `2^{n/4}`; mechanism is `q^{1/2}` per variable, not available at `q = 2`. |
| Sawin--Shusterman, [*Short sums of trace functions over function fields* (arXiv:2512.24080, 2025)](https://arxiv.org/abs/2512.24080), source checked | Near-square-root short sums of trace functions for sufficiently large fixed `q`, **squarefree** moduli, slopes `<= 1`, and no Artin--Schreier factors | Excluded twice: `q=2` is not in its large-`q` regime and `x^j` is maximally non-squarefree. Its squarefree-modulus geometry cannot be specialized to the wild Witt tower. |
| Pollack 2013; Ha 2016; Tuxanidy--Wang; Granger; Ahmadi--Gologlu--Granger--McGuire--Yilmaz | `(1-eps) sqrt n` positions; `(1/4 - eps) n` positions (large `q`); exact supersingular formulas for `O(1)` leading coefficients | None reaches the half-degree endpoint; Hayes/Weil gives `ell <= n/2 - log2 n - O(1)`. |
| Gorodetsky--Kovaleva 2024; Ma--Xing 2021; Sawin wild Kloosterman 2022 | Special order-two high-conductor character; AS code distance; warning on wild cross-order cancellation | Already closed on the branch: the remaining layers have order `> Q >= 2`. |
| [D. Lemire, MathOverflow 81717 (2011)](https://mathoverflow.net/questions/81717/can-we-always-find-such-an-irreducible-polynomial-of-degree-n-where-degreepx), Arndt's table to 400 | Original question and finite range | The problem source is the MO question (23 Nov 2011). **Correction 2026-08-23:** this row previously said `arXiv:1202.4961` is "unrelated" and "must not be cited for this conjecture". That is WRONG, and notes 08/11 have the verbatim quote: Kaser--Lemire, *Strongly universal string hashing is fast*, Comput. J. 57(11) (2014), section "GF Multilinear", states "(There are such irreducible polynomials for L in {1, 2, ..., 400} and we conjecture that such a polynomial can be found for any L)". It IS the published statement of the conjecture and is cited as such in the public documents; the MO question retains priority for the question itself. The tempting degree-`<=2` construction quoted there is an integer-polynomial result, not a binary one: e.g. `x^5+x+1=(x^2+x+1)(x^3+x^2+1)` in `F_2[x]`. No 2020--2026 endpoint result found. |

## 5. Candidate mechanisms for a new theorem, and the experiment that kills each

These are the only directions that survive sections 1--4. Each is stated with
the cheapest computation that could refute it before any proof is attempted.

- **A. Witt-tower bit balance (preferred).** `(NSD)` compares consecutive
  dyadic precisions of the same Galois-ring traces. The object is the bias of
  bit `s-1` of `Tr(teich(alpha)^k)` (for the few `k` with `e_k >= s`) on the
  set cut out by the lower bits, jointly with the new coefficient `x^j`. Bits
  of a Galois-ring trace are Boolean functions of degree `2^{s-1}` built from
  the elementary symmetric functions of the Frobenius orbit (`e_1`, `e_2`,
  `e_4`, ...). A theorem here would be a fixed-`q` statement about the
  conditional distribution of one Witt digit given all lower Witt data, which
  is exactly the gap between Kerdock-level (`s = 2`, exact) and generic
  (`s >= 3`, Weil only). First experiment: tabulate `delta_s - delta_{s-1}`
  and the conditional bit biases for `ell <= 13` (Python) and `ell <= 23`
  (branch CAS), and look for any structure in `s` beyond the four-population
  identity. This is a falsification/calibration tool, not a sample of the
  asymptotic quotient geometry: for every `ell <= 24`, its cutoff is `Q=1`
  and its `q >= 8` nonresonant rows have `R <= 8`. At the first theorem row,
  `ell=200`, `Q=8`, and the first unpaid nonresonant row `(j,q)=(199,16)` has
  `d_{s-1}=24`, `d_s=12`, hence `R=4096`. Thus finite data can disprove a
  proposed fibre symmetry (and do), but cannot establish a uniform large-`R`
  conditional-balance law. Any scaled experiment must retain `(j/q,R)` and
  separately sample the direct resonant rows.
- **B. Tower relations among `chi, chi^2, chi^4, ...`.** Squaring on `E_j` is
  the Frobenius substitution `u(x) -> u(x^2)`, so `S_n(chi^2)` is the
  `F_{2^n}`-subfield part of `S_{2n}(chi)`. The ledger's Adams/Moebius
  "virtual representation" remarks point the same way. Test: compute the
  joint statistics of `(S_n(chi), S_n(chi^2), S_{2n}(chi))` over a layer.
- **C. Joint symmetry of a layer.** Only translation `f(x) -> f(x+1)` and the
  Galois action of `(Z/2^s)^x = Z/2 x Z/2^{s-2}` act; separately each is
  closed on the branch. The open question is whether the *joint* orbit
  structure gives a signed identity. Test: orbit decomposition of `T_{j,s}` at
  `ell <= 12` and a search for exact relations among orbit sums.
- **D. One-sidedness.** `(REL)` is a lower bound; the branch reduced it to a
  variance within the identity cylinder with sd `<= mean/2`, far weaker than
  square-root cancellation. A non-Fourier (sieve or pair-correlation) upper
  bound for the variance of prime counts across the `~4 ell` classes over the
  identity of `E_{a-1}` would suffice. Test: compute that variance and its
  exact decomposition into pair counts `#{(alpha, beta) : same Witt profile}`.
- **E. Virtual Betti numbers.** The four-population identity is the point
  count of a virtual variety. The branch's `(WITT-LOW)` says the geometric
  Witt sum has conductor-dependent Betti complexity; whether the *signed*
  four-term combination has polynomial virtual Betti cost is a different and
  unanswered question. Test: Betti numbers of the four sparse-trace varieties
  for tiny `(n, j)` via point counts over `F_{2^r}` (the branch's
  `axeyum-gf2-extension-trace` does the extension counting).

Anything that takes absolute values per character, per Galois orbit, per
conductor, or per convolution order is known to fail and is not a candidate.

## 6. Tooling status

- **Axeyum CAS on `main`:** `axeyum-cas` has `gfp` (prime fields), integer
  factoring, univariate and multivariate polynomial algebra, but no
  `F_2[x]`, Hayes class, or character machinery. The branch's
  `crates/axeyum-cas/src/gf2*.rs` (26,655 lines in `gf2_hayes.rs`) and 18
  `axeyum-gf2-*` binaries supply exact populations, moments, layer
  reconstructions, Galois orbits, extension traces, and endpoint ledgers up to
  `ell = 23` (NTT + CRT) or `24` (10 GiB). They build in 16 s from a lane
  snapshot (`scripts/lane-snapshot.sh agent/gf2/lemire-proof`,
  `scripts/cargo-serialized.sh build --release -p axeyum-cas --bins`). Output
  is one `KEY|k=v|...` line per endpoint; `hayes-endpoint` reports the
  discrepancy `N_ell(1) - 2^{n-ell}`, `hayes-distribution` the full class
  distribution and moments, `hayes-moments` the Fourier moments.
- **Python:** system Python 3.14 has `sympy 1.14`, `numpy`, `mpmath` and no
  `pip`; there is no `flint`, `galois`, `pari`, `sage`, or `magma` on the host.
  A `uv` venv (Python 3.12, `python-flint 0.9.0`, `sympy`, `numpy`) gives
  `nmod_poly.factor` at 8 us per degree-20 polynomial; this is the irreducible
  enumerator. Reach: all populations for `n <= 26` in under 40 s on 32
  processes; full character tables, `L`-polynomials, and layer sums for
  `j <= 12`; Galois rings `GR(2^s, n)` with Teichmueller tables for
  `n <= 20`. `sympy` alone is sufficient but ~100x slower for the
  enumeration; nothing here needs more than flint.
- **What is missing for the next rung:** a native Rust `F_2[x]` / Hayes /
  Galois-ring module on `main` (the branch's is not merged and is 866 commits
  behind), and a fast path for `ell` in `14..23` outside the branch binaries.
  Both are deferred until candidate A or B produces a statement worth a
  checker.
