# What the 2023--2026 literature has, and what it does not: an arXiv techniques sweep

Status: literature sweep, 2026-08-23. Scope: arXiv 2022-01 .. 2026-08, math.NT
and math.AG, for **techniques in the surrounding field** -- not for this exact
problem, which nobody else is working on. The question this note answers is the
one notes 00/10/13/14 leave hanging: *does anything published since the lane's
map was drawn give a lever we lack, or does it confirm that fixed `q` is
untouched?*

Two headline answers, both new relative to notes 00--14:

1. **There is a lever, and it is not cohomological.** Gorodetsky--Kovaleva
   (arXiv:2307.01344) prove an *exact* symmetry identity for von Mangoldt-weighted
   sums of the Hayes characters mod `T^{k+1}` that replaces the Weil factor `k`
   by `gcd(k, q^n - 1)`. Their characters are the level-one (order-`p`) ones, so
   the identity as stated covers exactly the layer the lane already handles --
   but the *proof* uses only that the summand is a function of `x^{-k}` on
   `F_{q^n}^*`, which is also true of the higher Witt levels. If it transplants,
   the resulting bound lands within an **absolute constant factor 4** of
   `(HWO)`, against the factor `~ell` by which every method in notes 03--09
   misses. This is the top item in the ranked list below.
2. **An `n`-independent `q`-threshold, but only at ODD `p` -- the `p = 2`
   version of this claim is WITHDRAWN.** *(Corrected 2026-08-23 by the
   verification of [note 16](16-large-q-threshold.md); the original text of this
   item asserted the threshold at `p = 2` and read the residual problem as
   "small `q`". Both are wrong.)* Bagshaw (arXiv:2401.10399) Cor. 2.5 does give
   a level of distribution `omega < 1/2 + 1/62` for von Mangoldt in progressions
   to an **arbitrary** modulus (Sawin and Sawin--Shusterman need squarefree;
   ours, `x^{ell+1}`, is the maximally non-squarefree one), for an INDIVIDUAL
   modulus, subject to `q > p^2 e^2 ((16-omega)/(16-31 omega))^2`. But his
   standing hypothesis, `Files/Intro.tex` of the source, is verbatim "We fix an
   **odd** prime power `q = p^ell`", and the `q`-condition enters only through
   Sawin--Shusterman's Mobius estimate, whose proof IS quadratic reciprocity
   (`F_q^x` needs a unique quadratic character). There is no `p = 2` analogue,
   so "at `p = 2`, `q >= 2^15`" was arithmetic on a theorem that does not exist.
   Moreover `q > 7101 p^2` means `p^{l-2} > 7101`, so **no prime field and no
   `q = p^2` qualifies at any size**; the admissible set is `O(X^{1/3})` below
   `X`, smallest member `3^11`. What survives: for `p` odd and
   `q = p^l > 961 e^2 p^2`, Kaser--Lemire holds over `F_q` for all
   `n >= n_0(q)` with `n_0` ineffective -- the first `n`-INDEPENDENT
   `q`-criterion for the full half-degree window, and it does not touch
   characteristic two. See note 16.

A third, quieter answer: the fixed-`q` wall is a *single* wall, and the sweep
identifies it. Every 2020s advance in short sums of trace functions over
`F_q[u]` carries a factor of the shape `|g|^{log_q(conductor)}`
(Sawin--Shusterman arXiv:2512.24080, Thm. 1.?; and the `q`-thresholds in
Bagshaw and in Sawin's level-of-distribution work are the same factor in
disguise). That factor is `< 1` only when `q` exceeds the sheaf complexity, and
it is *worse than trivial* at `q = 2` for every sheaf we care about. It is not
five different obstructions; it is one.

## 0. Method, queries, counts (reproducibility)

Search was through the arXiv Atom API from this host
(`https://export.arxiv.org/api/query?search_query=...&sortBy=submittedDate`),
cached under the session scratch dir
`.../lemire-signed-trace-arxiv/cache/`, with the driver `q.py` (query +
parse + filter by date) and `absget.py` (`id_list` fetch for abstracts) beside
it. Sources were pulled with `curl -sL https://arxiv.org/e-print/<id>` into
`.../lemire-signed-trace-arxiv/papers/<id>/` and expanded (all were gzipped
tarballs or single gzipped `.tex`; no PDF-only cases arose, so `pdftotext` was
never needed).

**84 distinct API queries**, yielding **1262 distinct arXiv ids**, of which
**437 are dated 2022-01 or later**. Twenty were selected for a source read.

Query list (abbreviated; `cat:math.NT` / `cat:math.AG` filters where noted):

```text
topic:   "Witt vector"+characters | "Artin-Schreier-Witt" | "Hayes characters"
         "short intervals"+"function field" | "prescribed coefficients"+irreducible
         "irreducible polynomials"+"finite field" | "arithmetic progressions"+"function fields"
         "level of distribution"+"function field" | "Dirichlet characters"+"function field"
         "Keating-Rudnick" | "super-even" | Mobius/Liouville+short intervals+FF
         "Chowla"+FF | "Hansen-Mullen" | trinomial+irreducible
         "Betti numbers"+etale/exponential sums | "characteristic cycle"+"singular support"
         "wild ramification"+"Betti numbers" | "Swan conductor"+math.AG
         "exponential sums"+cohomology+vanishing | "big monodromy" | "Legendre"+conjecture+primes
         "Cramer"+primes | "large sieve"+FF | "Kloosterman"+"Witt" | "Galois ring"+exp sums
         "trace functions"+"function fields" | "perverse sheaves"+vanishing
         "middle extension"+monodromy | "Artin-Schreier"+L-functions+moments
         equidistribution+Frobenius+"finite field" | "character sums"+cancellation+FF
         "quantitative sheaf theory" | stratification+"exponential sums"
         conductor+sheaves+bounds | uniform+"in p"+cohomology
         bilinear+FF+sums | "parity problem"+sieve | primes+"F_q[T]"
         "polynomials over finite fields"+distribution | "sum-product"+finite fields
         Mobius+randomness | "T-adic"+"exponential sums" | "Newton polygon"+"Artin-Schreier"
         "Witt vectors"+L-functions | "Artin-Schreier-Witt"+tower | "Kerdock" OR "Galois rings"
         moments+FF+"fixed q" | sparse+irreducible+FF | "Bateman-Horn"/"twin prime"+FF
         "von Mangoldt"+FF | "integral moments"+FF | "Airy sheaf" | "local systems"+"characteristic 2"
         "Mordell"+FF
authors: Sawin, Gorodetsky, Bary-Soroker, Shusterman, Entin, Rudnick, Katz_N,
         Kowalski, Forey, Perret-Gentil, Wan, Florea, Keating_J, Roditty-Gershon,
         Carmon, Andrade, Yiasemides, Bienvenu, Panario, Shuddhodan
```

Author queries as `au:Name AND cat:math.NT` (the `au:Name_I` form is unreliable
-- `au:"Sawin_W" AND cat:math.NT` returns 5 hits, `au:Sawin AND cat:math.NT`
returns 59; the initial-suffixed form silently under-returns and would have
missed every paper in the table below).

**Negative results worth recording** (empty is a real answer here, and each was
paired with a query known to return hits): `abs:"Hayes characters"` -- 0 hits,
ever. `all:"super-even"` -- 1 hit, pre-2022. `abs:"Kloosterman"+"Witt"` -- 0.
`abs:"moments"+"function field"+"fixed q"` -- 0. `all:"Keating-Rudnick"` -- 1,
pre-2022. Nobody has published on the Hayes/Witt family under that name since
2021.

## 1. Selected papers

Relevance is to **this lane's open statements** -- `(HWO)`, `(T1)`/`(T1w)`,
`(T2)`, `Type II` -- not to the field.

| # | arXiv | authors | title (short) | date | rel |
| --- | --- | --- | --- | --- | --- |
| 1 | 2307.01344 | Gorodetsky, Kovaleva | Equidistribution of high traces ... cancellation in character sums of high conductor | 2023-07 | 5 |
| 2 | 2401.10399 | Bagshaw | Bilinear Kloosterman sums in function fields and the distribution of irreducible polynomials | 2024-01 | 5 |
| 3 | 2209.02170 | Sawin | The size of wild Kloosterman sums in number fields and function fields | 2022-09 | 5 |
| 4 | 2502.11060 | Hu, Teyssier | Estimates for Betti numbers and relative Hermite--Minkowski theorem for perverse sheaves | 2025-02 | 5 |
| 5 | 2512.24080 | Sawin, Shusterman | Short sums of trace functions over function fields and their applications | 2025-12 | 4 |
| 6 | 2608.00304 | Bah, Shuddhodan | Uniform stratified vanishing and equidistribution on `G_m^d` | 2026-07 | 4 |
| 7 | 2511.09459 | Fouvry, Kowalski, Michel, Sawin | Bilinear forms with trace functions | 2025-11 | 4 |
| 8 | 2306.16487 | Florea, Jones, Lalin | Moments of Artin--Schreier L-functions | 2023-06 | 4 |
| 9 | 2605.25877 | Cheng | Banded quadratic digit functions along irreducible polynomials over finite fields | 2026-05 | 4 |
| 10 | 2202.10370 | Klurman, Mangerel, Teravainen | Beyond the Erdos discrepancy problem in function fields | 2022-02 | 4 |
| 11 | 2506.18299 | Bonolis, Kowalski, Woo (app. Forey, Fresan, Kowalski) | Stratification theorems for exponential sums in families | 2025-06 | 3 |
| 12 | 2501.12623 | Wan, Zhang | Betti number bounds for varieties and exponential sums | 2025-01 | 3 |
| 13 | 2305.03168 | Alpoge, Katz, Navarro, O'Brien, Tiep | Local systems and Suzuki groups | 2023-05 | 3 |
| 14 | 2606.10041 | Haessig | On partial T-adic exponential sums and partial exponential sums with `p`-power conductor | 2026-06 | 3 |
| 15 | 2501.04461 | Fleet | Short sums of the Liouville function over function fields | 2025-01 | 3 |
| 16 | 2411.19012 | Merai | Rudin--Shapiro function along irreducible polynomials over finite fields | 2024-11 | 3 |
| 17 | 2502.11064 | Hu, Teyssier | Characteristic cycle and wild Lefschetz theorems | 2025-02 | 2 |
| 18 | 2602.21878 | Zurbuchen | Equidistribution for Tannakian monodromy groups | 2026-02 | 2 |
| 19 | 2412.14053 | Sawin | The asymptotic in Waring's problem over function fields via a singular locus in the circle method | 2024-12 | 2 |
| 20 | 2304.05014 | Bagshaw | Bilinear forms with Kloosterman and Gauss sums in function fields | 2023-04 | 2 |

Sources were read for all twenty except #14 (abstract only; see its digest) and
#18 (abstract plus the citing discussion in #6).

## 2. Technique digests

### 2.1 arXiv:2307.01344 -- Gorodetsky--Kovaleva. The one exact fixed-`q` saving over Weil

**Objects.** For `k >= 1` and a nontrivial additive `psi: F_q -> C^x`, set
`chi_{k,psi}(f) = psi(p_{-k}(f))` for `(f,T) = 1` and `0` otherwise, where
`p_i(f) = sum_j lambda_j^i` is the `i`-th power sum of the roots. Their
Lemma (`lem:invchar`) is that `chi_{k,psi}` is a **primitive Dirichlet character
modulo `T^{k+1}`** whenever `char(F_q) nmid k` -- i.e. *exactly our family*, in
Hayes coordinates, with conductor `j+1 = k+1`.

**Main theorem (`thm:canc`).** Uniformly in `n, k >= 1`,

```text
q^{-n} sum_{f in M_{n,q}} chi_{k,psi}(f)  <<  (1 + log_q n + sqrt(log_q k)) / n.
```

So cancellation for `log k = o(n^2)`, against the Montgomery--Vaughan /
Bhowmick--Le range `log k = o(n)`, and the range is **sharp** (at
`k = prod_{i<=n}(q^i - 1)` there is no cancellation). This is unconditional and
at fixed `q`.

**The mechanism, which is the part that matters here (`lem:sym`).** Verbatim:
for any additive `psi`, any `k, n >= 1`, and `k' = gcd(k, q^n - 1)`,

```text
sum_{f in M_{n,q}} Lambda(f) chi_{k,psi}(f) = sum_{f in M_{n,q}} Lambda(f) chi_{k',psi}(f),
```

whence (`cor:sym`)

```text
| sum_{f in M_{n,q}} Lambda(f) chi_{k,psi}(f) |  <=  q^{n/2} gcd(k, q^n - 1),
```

against the Weil bound `q^{n/2} k`. The proof is three lines and uses nothing
analytic. Push forward along `Phi: F_{q^n}^x -> {f : deg f = n, Lambda(f) != 0}`,
`Phi(x) = prod_{i<n}(T - x^{q^i})`; each `f` has exactly `Lambda(f)` preimages,
so the `Lambda`-weighted sum is `sum_{x in F_{q^n}^x} psi(sum_i (x^{q^i})^{-k})`.
The summand is a function of `x^{-k}`; the endomorphisms `x -> x^k` and
`x -> x^{gcd(k,q^n-1)}` of `F_{q^n}^x` have the same kernel and image, hence hit
every element of the image equally often, hence the two sums agree.

**Why this is new here.** Note 07 states that the one exact fixed-`q` mechanism
available -- the Witt carry formula -- collapses to Weil above the Kerdock level.
Here is a *second* exact fixed-`q` mechanism, with a completely different source
(the multiplicative structure of `F_{q^n}^x`, not Witt arithmetic), and it does
not collapse: it replaces the conductor by a gcd.

**Arithmetic against `(HWO)`.** At `q = 2`, `psi` is the unique nontrivial
character of `F_2`, so `chi_{k,psi}` has order 2: as stated the identity covers
the `s = 1` layer only. Suppose it did apply to a character of exact conductor
`j` and exact order `2^s`. With `g = gcd(k, 2^n - 1)`, `k = j`, and the lane's
normalisation `|S_n(chi)| <= (j-1) 2^{ceil(n/2)}` (note 10), the per-character
sufficient form of `(HWO)` is `4 ell |S_n(chi)| <= (j-1) 2^{ceil(n/2)}`, so the
`gcd` bound suffices iff `g <= (j-1)/(4 ell)`. In the `(HWO)` range
`a <= j <= ell` we have `j/ell -> 1`, so the requirement is `g <= 1/4`:
**impossible, but short by the absolute constant 4, not by a factor `ell`.**
Every mechanism in notes 03--09 is short by `ell`. That is the entire point of
listing this first.

**Does the mechanism extend to higher Witt levels? (open, and cheap to settle.)**
The proof uses *only* that the summand is `G(x^k)` for some function `G` on
`F_{q^n}^x`. A level-`s` character supported at a single odd Witt position `k`
has, on a prime `P` with root `alpha`,
`chi(P) = psi_s(Tr_{W_s(F_{q^n})/W_s(F_q)}(w [alpha]^{-k}))` with `[.]` the
Teichmuller lift; since `[.]` is multiplicative and Frobenius-equivariant, this
*is* a function of `alpha^{-k}` and the same substitution applies verbatim. The
two things to check, both mechanical and both inside the lane's existing CAS:

* whether the exact-conductor-`j`, exact-order-`2^s` layer `X_{j,s}` contains
  enough single-position characters for a layer-sum bound (Katz's parametrisation
  `Prim_j subset prod_{k odd <= j} W_{e_k}(F_2)` says a general character is a
  *tuple*, and for a tuple the summand is a function of several `x^{-k_i}`
  simultaneously, which defeats the substitution);
* the conductor of a single-position level-`s` character (nominally
  `j = k 2^{s-1}`), against which the saving is `(j-1)/gcd(k, 2^n-1)` and can be
  **exponential in `s`**, not merely a factor `j`.

**Lemma worth lifting verbatim.** `lem:Blk`: for `L >= sqrt(log_q k)`,
`B_{L,k} := sum_{L <= d < 2L} log gcd(k, q^d - 1) << L sqrt(log k log q)`. The
proof (via `q^d - 1 = prod_{e|d} phi_e(q)` and `lem:cyc`: for fixed `a` and prime
`p`, `{n : p | phi_n(a)}` is empty or `{p^i ord_p(a) : i >= 0}`) is exactly the
tool for controlling how often the gcd saving *fails*, and the lane will need it
if the transplant works. `prop:squareroot` (appendix) is also liftable:
square-root cancellation for a general character mod `Q` in the range
`deg Q <= n^{1+o(1)}`, improving Bhowmick--Le--Liu.

**Caveat the authors state.** "We do not know if cancellation for
`log k = o(n^2)` persists if we restrict to `P_{n,q}` instead of `M_{n,q}`; the
proof of Theorem [`thm:canc`] relies on summing over *all* degree-`n`
polynomials." The `Lambda`-weighted identity `lem:sym` has no such caveat --
it *is* the prime-weighted statement -- but the sieve step around it does.

### 2.2 arXiv:2401.10399 -- Bagshaw. Level of distribution beyond `1/2` for arbitrary modulus

**Main theorems.** (i) `thm:bilinear_savings`: for coprime `a, F` with
`deg F = r`, any `n >= r*eps`, `m >= r(1/4 + eps)` and arbitrary weights,
`W_{F,a}(m,n;alpha,beta) = sum_{x_1,x_2} alpha beta e_F(a/(x_1 x_2))
<<_eps q^{m+n-r delta}` -- **no hypothesis on `q`, no hypothesis on `F`**.
(ii) `thm:mobius_r/2`: for `n > r(1/2 + eps)`,
`sum_{deg x < n} mu(x) e_F(a/x) <<_eps q^{n(1-delta)}`, again for arbitrary `q`
and arbitrary `F`. (iii) `thm:mobius_3/4` and `thm:irving` (average over `F`).
(iv) `cor:vonmangoldt`, the one that matters:

> Fix `omega < 1/2 + 1/62` and suppose `q > p^2 e^2 ((16-omega)/(16-31 omega))^2`.
> Then for any coprime `a, F` with `deg F = r` and any `n` with `r <= omega n`,
> `sum_{x in M_n, x = a mod F} Lambda(x) - q^n/phi(F) <<_omega q^{n - r(1+delta)}`
> for some `delta = delta(omega) > 0`.

**Method.** Bourgain--Garaev / Garaev / Fouvry--Shparlinski / Irving additive-energy
bounds for modular inversions in `F_q[T]`, giving bilinear Kloosterman savings for
*arbitrary* modulus, inserted into the Sawin--Shusterman level-of-distribution
machinery in place of the squarefree-modulus input. GRH in `F_q[T]` (Weil) lets
him drop the `gcd(a,F) = 1` hypothesis that the integer analogues need.

**What it gives this lane.** Our window is a single arithmetic progression:
reversing `f = x^n + g`, `deg g <= floor(n/2)`, gives `f* = x^n f(1/x)` monic of
degree `n` with `f* = 1 mod x^{ceil(n/2)}`, and `f` is irreducible iff `f*` is.
So Kaser--Lemire over `F_q` is exactly "`sum_{x in M_n, x = 1 mod T^r} Lambda(x)
> 0`" with `r = ceil(n/2)`, `F = T^r` -- and `phi(T^r) = q^{r-1}(q-1)`, so the
main term is `~ q^{n-r+1}/(q-1)` and dominates the error `q^{n-r(1+delta)}`.
Taking `omega = 1/2 + eps` with `eps -> 0` (legitimate for `n > 31`), the
hypothesis is `q > p^2 e^2 * 31^2 = 7100.9 p^2`. **Hence: the Kaser--Lemire
statement over `F_q` is a theorem for all sufficiently large `n` whenever `p`
is ODD and `q > 7101 p^2`** (implied constant depends on `omega` only; it is
not made explicit, so "sufficiently large" is not effective as written).
**`p = 2` IS EXCLUDED** -- by Bagshaw's standing hypothesis ("We fix an odd
prime power `q = p^ell`") and, more fundamentally, by mechanism: the
`q`-condition comes from Sawin--Shusterman's Mobius estimate, which is
quadratic reciprocity and has no characteristic-two form. The earlier version
of this paragraph deduced "`q >= 2^15` at `p = 2`"; that was wrong. Note also
`q > 7101 p^2` forces `p^{l-2} > 7101`, so `l >= 3`: no prime field, and no
`q = p^2`, is admissible. Smallest admissible `q` is `3^11 = 177147`. Full
verification, with the constant re-derived and an external control that
reproduces Bagshaw's own published newly-covered list exactly, is
[note 16](16-large-q-threshold.md).

**Where `q -> infinity` enters, exactly.** Not in (i)--(iii), which hold at
`q = 2`. It enters only when the Mobius bound is fed into the Sawin--Shusterman
short-sum machinery, whose savings carry the factor `|g|^{log_q(...)}` of
section 2.4. Bagshaw himself tabulates the exact `(p, l)` pairs for which his
arbitrary-modulus bound beats Sawin--Shusterman's irreducible-modulus one, and
the list starts at `p = 3`.

**Frank assessment for `(HWO)`.** No, at `q = 2`, but it *reframes* the problem:
see section 3(iii). The parts with no `q` hypothesis, (i) and (ii), are about
`e_F(a/x)` -- additive characters of the inverse -- not about multiplicative
characters mod `F`, and the classical bridge between them for prime-power
modulus is Postnikov's formula `chi(1 + pi u) = psi(a log(1 + pi u))`, whose
`p`-adic logarithm has `p` in its denominators. **That is the precise
characteristic-two obstruction to importing Bagshaw's `q`-free half:** the
Postnikov bridge does not exist in characteristic 2.

### 2.3 arXiv:2209.02170 -- Sawin. A fixed-`q` *disproof* template

**Main theorem.** An evaluation of `Kl_k(x) = sum_{prod x_i = x} psi(sum x_i)`
over `R/pi^n` for `n > 1` including the hard case `p | k`, with `v = v_p(k)`,
`k* = gcd(k, |R/pi| - 1) p^w`, and constants `c = min{s : pi^{(p^r+1)s} p^{v-r} =
0 mod pi^n for all r <= v}`. In equal characteristic `w = 0`, so `k* = gcd(k, q-1)`
-- the same gcd phenomenon as 2.1.

**The applications are what matter here.** `Kl_k(x)` **vanishes** for all but
`q^{ceil(n/(p^v+1)) + ceil((n-1)/(p^v+1)) - 1}(q-1)` values of `x`. Combined with
Plancherel on the group `G = (1 + T^{-1} F_q[[T^{-1}]])^x / (1 + T^{-n} ...)^x`
-- which fixes the *total* second moment -- the sparsity of the support forces
one value to be enormous:

* `lem:interval-lower-bound`: some short interval has
  `|sum_{f in I} d_k^{(n-2,...)}(f) - q^{(k-1)(n-2)+1}| >= q^{(k(n-3) - 2n/(p^v+1) + 1)/2}(q-1)^{(k-1)/2}`;
* `lem:epsilon-average-lb`: some `a` has
  `|sum_{chi in F_{pi,n}} chi(a) epsilon_chi^{p^v}| >= |pi|^{(1 - 1/(p^v+1)) n} C`,
  a power saving of only `1/(p^v+1)` against the trivial bound.

Conclusion, verbatim in effect: the CFKRS-type moment asymptotic "cannot hold
with `delta > 1/(p^v + 1)`" -- **certain short interval sums and certain moments
of Dirichlet `L`-functions over `F_q[u]` do not admit square-root cancellation.**

**Why this is the most under-used item in the sweep.** It is a *negative*
theorem at fixed `q`, for prime-power modulus `pi^n` -- our modulus type -- and
the mechanism is elementary: `vanishing locus is sparse` + `Plancherel fixes the
mass` => `some value is huge`. The lane has already *measured* the ingredient:
note 07 records that `C_psi/D_psi` has an "unbounded-above tail", and note 07's
`A_psi = sum_{g in K} N(g) psi(g)` satisfies `sum_psi |A_psi|^2 = |K| sum_g N(g)^2`
exactly. **The transplant is a disproof strategy, not a proof strategy, and it is
one measurement away:** if `A_psi = 0` for all but a `2^{-c}` fraction of `psi`,
then `max_psi |A_psi| >= 2^{c/2} (mean square)^{1/2}`, and if that exceeds
`2^{ell-1}` then `(CYL)` -- hence `(HWO)` in its cylinder form -- is **false**.
The lane's existing `A_psi` dumps already contain the vanishing locus; nobody has
counted it.

**Where `p` large would enter.** Nowhere: the theorem is strongest at small `p`
and small `v`, which is why it is relevant.

### 2.4 arXiv:2512.24080 -- Sawin--Shusterman. The fixed-`q` wall, stated cleanly

**Main theorem.** For a trace function `t` to squarefree modulus `g` in `F_q[u]`,
built from sheaves `F_pi` on `A^1_{F_q[u]/(pi)}` satisfying four assumptions,

```text
sum_{|f| < X} t(f)  <<  X^{1/2} |g|^{log_q(2 r(t) + c(t))},   implied constant sqrt(q),
```

with `r(t)` the rank and `c(t)` the conductor. The four assumptions: mixed of
nonpositive weights; no finitely supported sections; **geometric global monodromy
has no `L_psi(alpha x)` factor**; **slopes at infinity `<= 1`** (they call this
"the most significant/restrictive of our four assumptions ... a limitation of our
method").

**All four fail for us, and so does the modulus hypothesis.** Our modulus is
`x^{j+1}`, the *maximally* non-squarefree one; our sheaves *are*
Artin--Schreier--Witt, i.e. exactly the excluded factors; and an ASW sheaf of
level `>= 2` has `Swan_infty` divisible by `p` (Katz IMRN 2013 Lemma 3.1; see
2.13 below for the `p = 2` computation), so slopes exceed 1.

**And the bound is worse than trivial at `q = 2` regardless.** The exponent
`log_q(2r + c)` is `< 1` only for `q > 2r + c`; the authors say so explicitly
("For smaller values of `q`, or very short intervals, our bounds are worse than
trivial"). **This single factor is the fixed-`q` wall**, and it recurs, in
disguise, as the `q`-threshold in Bagshaw's `cor:vonmangoldt` and in Sawin's
`omega < 1` level-of-distribution theorem for squarefree modulus.

### 2.5 arXiv:2502.11060 -- Hu--Teyssier. Note 14 sec. 11.4's open question, answered

Note 14 sec. 11.4 names this paper "the most promising unexplored input for
`(T2)`". It is now explored. **Verdict: it does not close `(T2)`, and the reason
is computable from their own definition.**

**Theorem 1 (their `general_boundedness_Betti_Xsmooth`).** `X` proper smooth of
dimension `n` over an algebraically closed field of char `p > 0`, `D` a reduced
effective Cartier divisor, `U = X - D`. There is `fd in N[x]^{n+1}` with `fd_i`
of **degree `i`** such that for every `l != p`, every `j`, every local system `L`
on `U`,

```text
h^j(U, L)  <=  fd_{min(j, 2n-j)}(lc_D(L)) * rk(L),
```

where `lc_D(L)` is the highest logarithmic conductor at the generic points of
`D`. **Theorem 2** makes this explicit for `A^n`: `h^i(A^n, L) <= b_i(lc_H(L)) rk(L)`
for `0 <= i <= n`, with `b_0 = 1`, `b_1 = x`, and

```text
b_n(x) = sum_{i<n, i != n mod 2} (x+2) b_i(x+3) + sum_{i<n, i = n mod 2} (x+3) b_i(x)
       + sum_{i<n, i != n mod 2} b_i(x).
```

The degrees are optimal (their `sharp_degree`), and nothing depends on `p` or on
`l`. That is four properties `(T2)` wants: uniform in `p`, uniform in `l`,
**graded by cohomological degree**, and **linear in the rank**. Sawin's Lemma
2.11 (the incumbent, note 14 sec. 11.4) has none of the last two.

**The computation (done here; `ht_b.py` in the scratch dir).** Evaluating their
recursion:

```text
k        :   0     1     2      3       4        5         6          7           8
b_k(1)   :   1     1    17    184    2459    39205    733496   15815563   386910089
b_k(1) 2^{-k/2} : 1  0.71  8.5   65     615     6931     9.2e4      1.4e6       2.4e7
```

and for the ungraded total, `log2 b_n(1)/n = 3.8, 4.7, 5.2, 5.6` at
`n = 10, 20, 30, 40` against `log2 n = 3.3, 4.3, 4.9, 5.3`: **`b_n(1) = 2^{Theta(n log n)}`,
i.e. `2^{O(j log j)}` on `Prim_j`** -- the same order as Sawin's Lemma 2.11, and
short of the `~2^{j/2}` budget by an exponential, exactly as note 14 says of the
incumbent.

**The graded form does not rescue it either.** By duality on `U` the top
compactly supported groups are `h^{2n-k}_c(U,L) = h^k(U, L^v)^v`, bounded by a
polynomial of degree only `k` -- so *each individual* top Betti number is
polynomially bounded in the conductor, uniformly in `p`. But the Deligne budget
weights degree `2j - k` by `q^{-k/2}`, and the partial sums
`sum_{k <= K} b_k(1) 2^{-k/2} = 1, 1.71, 10.2, 75, 690, 7621, ...` **diverge**;
the budget needs `<= (j-1)/(4 ell) ~ 1/4`. So the graded bound fails at every
truncation.

**Frank assessment.** `Maybe`, downgraded from note 14's "most promising". It is
the right *technology* -- the first bound in print with all four properties
`(T2)` needs -- and the missing ingredient is now precisely identifiable: a
better dependence on `lc` **at the top degrees only** (their `fd_k` for `k <= 7`
have optimal *degree* but their *coefficients*, `17, 184, 2459, ...`, are what
kills the budget). That is a much sharper target than "a polynomial Betti bound".

**Lemma worth lifting.** Their `ex_1`: every `L in Loc(U)` has log conductors
bounded by `(lc_D(L) + 1) * O_D`, which is what makes Theorem 3 (families,
singular base, `l`-independent, uniform in algebraic families) usable. Theorem 3
is the version that would apply to `Prim_j` as `j` varies, if the coefficient
problem were solved.

### 2.6 arXiv:2608.00304 -- Bah--Shuddhodan. Uniform *in the characteristic*

**Theorems.** For every `d >= 1` there are nondecreasing `Phi^Delta_d, Psi_d`
such that for every `C >= 0`, **every finite field `F_q` (any characteristic)**,
every `l != char`, and every `K` (resp. perverse `A`) on `G_m^d` with Sawin
complexity `cx(K) <= C`:
`|Delta(K)(k_n)| <= Phi^Delta_d(C) q^{n(d-1)}` and
`|V_{d,i}(A)(k_n)| <= Psi_d(C) q^{n(d-i)}`, where `Delta(K)` is the
Gabber--Loeser non-isomorphism locus of forget-supports and `V_{d,i}` the
cohomology jump loci. Corollary: horizontal equidistribution on `G_m^d` for
sequences of perverse sheaves of bounded complexity with common Tannakian
monodromy group, **as the field cardinalities go to infinity with the
characteristic varying** -- settling the case Forey--Fresan--Kowalski
(arXiv:2109.11961, Rem. 4.20(2)) left open for `d >= 2`.

**Assessment: `maybe`, blocked on three counts, all dimensional.** (a) The
constants `Phi_d, Psi_d` depend on `d`; our `d = j` grows, and no growth rate is
claimed. (b) `Prim_j = G_m x A^{j-1}` is not a torus; the theory is
specifically Mellin/Gabber--Loeser on `G_m^d`. (c) The statement is about the
*generic* Kummer twist `A (x) L_chi`; the lane needs it for a *specified* sheaf
`Xi_n(L_univ)`, and "generic in `chi`" is precisely the Katz--Laumon-style
genericity that note 14 sec. 11.3 already records as useless for a specified
sheaf. What it *does* change: uniformity in `p` for vanishing statements is no
longer unavailable in principle. It is the first such theorem, and it is one
year old.

### 2.7 arXiv:2511.09459 -- Fouvry--Kowalski--Michel--Sawin. Type II under structural hypotheses

**Theorem (simplified form).** `K` the trace function of a middle-extension
sheaf pure of weight 0 on `A^1/F_q`, `q` **prime**, with geometric monodromy `G`
acting irreducibly on `C^r` and either (i) `G^0` simple, or (ii) `G` finite
quasisimple. For nonzero `b, c` and `q^delta <= M`, `MN >= q^{3/4+delta}`,
there is `eta > 0` with

```text
sum_{m ~ M} sum_{n ~ N} alpha_m beta_n K(m^b n^c)
  <<  ||alpha||_2 ||beta||_2 (MN)^{1/2 - eta}.
```

**Method.** A "soft" stratification theorem for sums of products of trace
functions (after an idea of Junyan Xu), plus a new robust Goursat--Kolchin--Ribet
criterion. The point is that the hypotheses are *qualitative* monodromy
conditions, not "this is a Kloosterman sheaf".

**Assessment for note 13's Type II face: `maybe`, and the monodromy hypothesis is
already satisfied.** Note 14 records `G_geom(L_univ) contains SL_{j-1}` for
`p = 2, j >= 4` (Katz IMRN 2013 Thm. 5.1) -- irreducible with simple identity
component, i.e. exactly hypothesis (i). And note 13 Prop. 13 puts the Type II
sum in the shape `2^{-ell} sum_chi A_M(chi) B_L(chi)`, a bilinear form in the
character aspect. The obstacles: (a) **the modulus is prime here**, ours is
`x^{ell+1}`; (b) the kernel is a trace function on `A^1` over `F_q` evaluated at
`m^b n^c`, while ours is a character of a *ray class group*; (c) the ranges are
`M, N <= q/2` with `q` the modulus size -- in our transplant `M + L = n` and
`|modulus| = 2^{ell+1} ~ 2^{n/2}`, so `2^M ~ q/2` sits exactly at the boundary,
which is at least not disqualifying.

### 2.8 arXiv:2306.16487 -- Florea--Jones--Lalin. Fixed-`q` moments, and why `q = 2` gets nothing

**Setting.** `p > 2`, `q` a power of `p` **fixed**, genus `-> infinity`: moments
of `L(u, f, psi)` over the polynomial (`p`-rank 0) Artin--Schreier family
`AS_d^0 = {f = sum a_j x^j : a_d != 0, a_j = 0 if p | j > 0}`. This is the
closest published relative of the lane's problem: a fixed-`q`, growing-conductor
moment computation for an *additive*-character family.

**Results.** `k`-th moment for `2 <= k < q^{1/2}` with error
`q^{(d/2)((k+1)/p - 1) + 2}(d+1)^k (k+2)^{(k+1)d} k^{k-1}/(1-q^{-1/2})^k`; an
exact second absolute moment with lower-order term `d q^{d/p - d/2}`, confirming
unitary symmetry.

**Where `q` enters, precisely.** Their remark: an asymptotic needs
`(k+1)(log_q(k+2) + 1/(2p)) <= 1/2 - eps`. At `q = p = 2` and `k = 1` the left
side is `2(log_2 3 + 1/4) = 3.67 > 1/2`. **At `q = 2` the method yields no
moment at all, not even the first.** Their own summary: "the greater `log_p q`
is, the more moments we can compute ... the case `q = p` would allow for a more
restricted range". They also state flatly that the techniques for the different
`p`-rank strata "do not transfer from one subfamily to the others".

**Assessment: `no` as a tool, `yes` as a calibration.** It fixes the exact price
of fixed `q` for exactly this kind of family, and the price at `q = 2` is
everything. It is the cleanest available answer to "has anyone done fixed-`q`
moments for an additive-character family": yes, for `p > 2`, and the method dies
at `p = 2`.

### 2.9 arXiv:2605.25877 -- Cheng (and 2411.19012 -- Merai). Fixed-`q` Vaughan for *quadratic* digit forms

**Theorem (Cheng, `thm:main`).** `q` odd and fixed. For a fixed symmetric Laurent
symbol `A(z) = c_0 + (1/2) sum_{l=1}^m c_l (z^l + z^{-l})` and
`Q_A(f) = sum_{j<=m} c_j sum_i f_i f_{i-j} + ell_n(f)` (arbitrary linear digit
form `ell_n`, uniformly),

```text
#{f in P(n) : Q_A(f) = gamma} = #P(n)/q + O_A(q^{19n/20 + o(n)}).
```

Merai (2411.19012) is the `m = 1` nearest-neighbour case (Rudin--Shapiro), with
exponent `27/28`.

**Method.** Vaughan's identity in `F_q[t]` reduces `sum_{f in M(n)} Lambda(f)
psi(Q_A(f))` to Type I and Type II sums; the Type II sum is handled by a **rank
argument for the Laurent symbol** (the quadratic form's Toeplitz matrix), the
Type I sum is split by the degree of the multiplier with direct rank bounds at
the ends, and the central range is handled by an **averaged rank-defect estimate**
obtained by enlarging the symbols `P g g^*` to the full linear space of
reciprocal polynomials and counting a bilinear incidence.

**Why this is the closest methodological match in the whole sweep.** At `p = 2`
the Witt coordinates make the *level-`s`* layer of our family a polynomial phase
of degree `2^{s-1}` in the coefficients of `f`: level 1 is a **linear** digit
form (Hayes), level 2 is a **quadratic** digit form -- literally Cheng's
`Q_A`. So the `s = 2` layer of `(HWO)` is, up to bookkeeping, the object Cheng
handles at fixed `q`, and by a genuinely fixed-`q` method (no `q -> infinity`
anywhere).

**Obstacles, exact.** (a) `q` odd, and not incidentally: the symbol
`A(z) = c_0 + (1/2) sum c_l(z^l + z^{-l})` **contains `1/2`**, and the Toeplitz
rank argument is a statement about a symmetric bilinear form, which degenerates
to an alternating one in characteristic 2. (b) `m` is **fixed** and the error is
`O_A`, i.e. the implied constant depends on the symbol; our band grows like `j`,
and the whole difficulty is uniformity in `j`. (c) The saving is `q^{-n/20}`,
which is a power saving against the *trivial* bound -- `(HWO)` needs a factor
`4 ell` against the *Weil* bound, which is already `q^{-n/2}`. So even a perfect
transplant addresses only the shape, not the strength.

**Assessment: `maybe` for `s = 2` only, `no` for the high-`s` layers `(HWO)`
actually needs (`2^s > Q`).** Recorded because it is the only fixed-`q`
Vaughan-plus-algebra success on irreducible polynomials in the window.

### 2.10 arXiv:2202.10370 -- Klurman--Mangerel--Teravainen. Characteristic 2 is *more* degenerate, as a theorem

**Corollary (their `short_extr`).** For completely multiplicative
`f: M -> {-1,+1}`, the short-sum discrepancy `S_f` is finite **iff** there are a
prime power `P^k`, a primitive Dirichlet character `chi` mod `P^k`, a *short
interval character* `xi`, and `j in {0,1}` with
`f(P') = chi(P') xi(P') (-1)^{j deg P'}` for all primes `P' != P`. "Moreover, if
`q` is odd, we have `xi = 1`."

**Two facts for this lane.** (1) The functions with **no** short-interval
cancellation are exactly the Dirichlet characters to **prime-power modulus** --
our family -- so our characters are the certified extremal obstruction to
short-interval cancellation, not a generic family. (2) Verbatim from their
introduction: "Over `F_q[t]` with `q` **even**, we have an interesting low
characteristic phenomenon that the set of characters with bounded discrepancy is
**somewhat larger** than in the case of `q` odd." That is an explicit,
theorem-backed statement that **characteristic two is strictly more degenerate
for this exact family** -- the class of obstructions grows, because short
interval characters `xi != 1` survive.

**Assessment: `no` as a tool; important as evidence.** It is the only paper in
the sweep that isolates a char-2 degeneracy *in our family* rather than in a
proof technique, and it points the same way as note 07's carry-collapse.

### 2.11 arXiv:2506.18299 -- Bonolis--Kowalski--Woo. The Katz--Laumon uniformity gap, half closed

Note 14 sec. 11.3 records that Katz--Laumon's Remarque 5.5.2 says they do not
know whether the exceptional hypersurface `F` can be chosen uniformly. This paper
proves that it can, **in algebraic families**: for `W -> A^r` and `f, g` on `W`,
there is one tuple `((Y_j), N, C, A, phi)` giving a KL-datum for every fibre
`V_a`, `a` outside a proper closed `A`, valid for all `p nmid N phi(a)`; plus an
analytically uniform variant. The appendix (Forey--Fresan--Kowalski, excerpted
from arXiv:2109.11961) is the readable introduction to multivariable trace
functions.

**Assessment: `no`, but the reason is now different.** The uniformity is over
the *family parameter*, not over the *characteristic*: `p nmid N` with `N`
depending on the data, so `p = 2` is excluded as soon as `N` is even, and no
control on `N` is offered. And the sums are `chi(g(x)) psi(f(x) + h.x)` --
level-one Artin--Schreier with a *generic linear twist* `h` -- so this is still
"generic in a twist", the mechanism note 14 sec. 11.3 already rules out for a
specified sheaf. What changed: "Katz--Laumon is not uniform" is no longer a
correct blanket statement, and note 14's sentence should say *which* uniformity
is missing.

### 2.12 arXiv:2501.12623 -- Wan--Zhang. Betti bounds by perverse sheaves, level one only

New upper bounds for `B_c(V, l)` for affine `V subset A^n` cut by `r` equations
of degree `<= d`, asymptotically optimal in `d` for complete intersections;
lifted to the cohomological level for exponential sums, improving Bombieri,
Adolphson--Sperber and Katz; plus upper semicontinuity of Newton polygons. They
explicitly position their results as complementary to Hu--Teyssier ("mutually
enriching").

**Assessment: `no` for `(T2)` as it stands.** Their exponential-sum bounds are
for `L_psi(f)` on affine varieties -- **level-one** Artin--Schreier -- and our
sheaves are Witt level `>= 2`. The one route in is the Liu--Wan `T`-adic
interpolation (2.14), which expresses `p`-power-conductor sums through a
one-parameter family of level-one objects; whether the Betti bound survives that
passage is not addressed by either paper.

### 2.13 arXiv:2305.03168 -- Alpoge--Katz--Navarro--O'Brien--Tiep. Char-2 Witt sheaves, in the wild

**Theorem.** For `q = 2^{2n+1}`, the local systems `F_q` on `A^1/F_2` of rank
`2^n(2^{2n+1}-1)` built in Katz's earlier work have `G_geom` equal to the Suzuki
group `Sz(q) = {}^2B_2(q)` or to `SL_D`; and `F_8` has `G_geom = {}^2B_2(8)`,
`G_arith = Aut({}^2B_2(8))` over `F_2`.

**Three technical facts worth having, all in characteristic 2 and all about
level-2 Witt sheaves.** (i) The construction is `L_{psi_2([a(x),b(x)])}` for
`psi_2([a,b]) = i^{a^2 + 2b}` on `W_2(F_2) = Z/4`, with the factorisation
`L_{psi_2([a,b])} = L_{psi_2([a,0])} (x) L_{psi(b)}` from Witt addition -- the
same decomposition the lane's carry formula uses. (ii) **Swan conductors:**
`Swan_infty(L_{psi_2([a,0])}) = p deg(a)` and `Swan_infty(L_{psi(b)}) = deg(b)`,
so a level-2 sheaf has `Swan_infty = max(p deg a, deg b)`. The first is
**divisible by `p`** -- which is exactly the hypothesis D2 failure that note 14
sec. 11.3 identifies as blocking Katz *Sommes exponentielles* 5.4.1. This paper
confirms that reading at `p = 2` explicitly. (iii) For `Swan_infty = n >= 2`,
`FT_psi(L_{psi_2([a,b])})` is an **Airy sheaf** (Such): lisse of rank `n-1`, pure
of weight one, and **all `infty`-slopes equal `n/(n-1)`** -- a single slope with
coprime numerator and denominator, i.e. totally wild and irreducible at infinity.
That is the "total wildness" input Katz 2.1.1/2.2.1 needs, realised at `p = 2`
for a level-2 Witt sheaf -- **in dimension one**. The lane needs it on `Prim_j`,
`dim = j`.

Also of note: their key trick is that the Witt vector is a function of
`x^{t(q)}`, so `F_q | G_m` descends to `G_m/F_2` -- structurally the same
`G_m`-quotient the lane's note 14 Prop. B performs.

**Assessment: `maybe`, as a source of char-2 slope computations, not as a
theorem.** It is the only recent paper computing ASW-Witt monodromy at `p = 2`.

### 2.14 arXiv:2606.10041 -- Haessig. `p`-power conductor, but `p`-adically

*Abstract only* (source pulled but not read in depth; flagged). Generalises the
Liu--Wan `T`-adic exponential sum theory -- which "interpolates all character
sums with character having `p`-power conductor", i.e. exactly our family -- to
*partial* `T`-adic sums; proves `T`-adic meromorphy, a `p`-adic proof of
rationality for all partial `L`-functions of `p`-power-conductor characters, and
Newton-over-Hodge estimates.

**Assessment: `no`, and the lane has already refuted the shape.** Newton polygons
give `p`-adic valuations of the inverse roots, hence 2-adic divisibility of
`T_{j,s}(n)`; since `T_{j,s}` is a rational integer, divisibility gives a *lower*
bound (`T = 0` or `|T| >= 2^m`), never the archimedean upper bound `(HWO)` needs.
That is note 04 shape 3 (2-adic arithmetic uncertainty), refuted there. Recorded
because it is the only 2022--2026 paper whose subject is literally
"`p`-power-conductor character sums", and because Newton-over-Hodge data for our
exact family would be new input for the *finite* checks even if not for `(HWO)`.

### 2.15 arXiv:2501.04461 -- Fleet. Matomaki--Radziwill at fixed `q`, at our scale

For fixed `q`, `h << sqrt N` with `h -> infinity` arbitrarily slowly,

```text
q^{-N} sum_{G_0 in M_N} | sum_{G in I_h(G_0)} lambda(G) |^2  <<_q  N^5 q^h / h^2,
```

by Chinis's integer argument adapted from Matomaki--Radziwill.

**Assessment: `no`, but it is the right calibration for note 13.** This is
genuine short-interval cancellation at **fixed `q`**, nontrivial once
`h > 5 log_q N` -- far shorter than our window `h ~ n/2`. It is also
mean-square, not pointwise, and it is for the **Liouville** function: the parity
problem means it detects no primes. It is the sharpest statement of what the
fixed-`q` short-interval technology can currently do, and it does not touch
`Lambda`.

### 2.16 The remaining four

* **arXiv:2502.11064 (Hu--Teyssier, wild Lefschetz).** An instance of Deligne's
  envisioned wild Lefschetz theorem via Beilinson singular support and Saito
  characteristic cycle, with new finiteness for characteristic cycles of perverse
  sheaves. Relevant only as the machinery under 2.5; note 14 sec. 11.4 already
  flags T. Saito's index formula as *downstream* of `(T1)`, and this does not
  change that.
* **arXiv:2602.21878 (Zurbuchen).** Every perverse sheaf on a connected
  commutative algebraic group over a finite field is generically unramified;
  equidistribution for Tannakian monodromy groups in new generality; a
  stratification theorem for exponential sums in families indexed by a scheme and
  the characters of the group. Same `G_m`-flavoured limitation as 2.6.
* **arXiv:2412.14053 (Sawin, Waring).** Minor arcs treated as complete
  exponential sums bounded by Katz's singular-locus dimension, estimated by
  tangent-space computations. Hypothesis throughout: `2 <= k < p`. At `p = 2`,
  vacuous -- **the same vacuity as Sawin's Lemma 5.3** (note 14 sec. 11.1), and
  from the same source (Sawin arXiv:1809.05137 Prop. 2.5). Two independent
  papers now hit the identical `p = 2` wall in the identical lemma.
* **arXiv:2304.05014 (Bagshaw, bilinear Kloosterman/Gauss in FF).** The
  technical base for 2.2; bounds on solutions of modular congruences in
  `F_q[T]`. No `q` hypothesis.

## 3. What is new since the lane's map

### (i) Results that touch fixed `q`, characteristic 2, or the Witt family directly

Five, and only five, in 2022--2026:

1. **arXiv:2307.01344** -- an exact `Lambda`-weighted identity for Dirichlet
   characters mod `T^{k+1}` at fixed `q` that improves Weil's `k` to
   `gcd(k, q^n - 1)`. *Positive.* Level one as stated.
2. **arXiv:2401.10399** -- level of distribution `> 1/2` for arbitrary
   (in particular prime-power) modulus, with an `n`-independent `q` threshold.
   *Positive, at large `q`.*
3. **arXiv:2209.02170** -- certain fixed-`q` short-interval sums and moments to
   prime-power modulus provably do **not** admit square-root cancellation, by
   sparsity of a vanishing locus plus Plancherel. *Negative, and transplantable
   as a disproof.*
4. **arXiv:2202.10370** -- at `q` **even** the class of characters with bounded
   short-interval discrepancy is strictly larger than at `q` odd. *Negative, and
   about our family specifically.*
5. **arXiv:2305.03168** -- char-2, level-2 ASW-Witt monodromy computed
   (Suzuki or `SL_D`), with the `Swan_infty = p deg a` and Airy-slope
   `n/(n-1)` facts. *Neutral; the only char-2 Witt sheaf computation in print
   since 2021.*

Everything else in the sweep either assumes `q` large, `p` large, `p` odd,
squarefree modulus, or level-one Artin--Schreier -- usually several at once.

### (ii) Techniques that could plausibly transplant, ranked

1. **The gcd symmetry (2.1), lifted from level one to Witt level `s`.**
   *Obstacle:* the substitution `x -> x^a` requires the summand to be a function
   of a *single* power `x^{-k}`; Katz's parametrisation makes a general
   exact-conductor-`j` character a tuple over the odd positions `k <= j`, and for
   a tuple the substitution is unavailable. *Why it is still first:* at `g = 1`
   the resulting bound is short of `(HWO)` by the absolute constant `4`, not by
   `ell`, and the check ("how many characters in `X_{j,s}` are single-position?
   what is their conductor?") is pure bookkeeping in the lane's existing CAS.
2. **The Sawin sparsity/Plancherel disproof (2.3), applied to `A_psi`.**
   *Obstacle:* none technical -- it needs the vanishing locus of `A_psi`, which
   the lane's note-07 dumps already contain but nobody has counted. *Risk:* it
   may refute `(CYL)`, which is a result either way, and would be the first
   evidence that the target as stated is false.
3. **Hu--Teyssier graded Betti bounds (2.5) with improved top-degree
   coefficients.** *Obstacle:* their `fd_k` have optimal degree but coefficients
   `17, 184, 2459, 39205, ...`, and `sum_k fd_k(1) 2^{-k/2}` diverges against a
   budget of `1/4`. *Why it stays high:* it is the only bound in print that is
   simultaneously uniform in `p`, uniform in `l`, graded by degree, and linear in
   the rank, and the deficiency is now a *coefficient* problem in `<= 7`
   explicit polynomials rather than an open theory.
4. **FKMS structural bilinear bounds (2.7) for the Type II face.** *Obstacle:*
   prime modulus, and a kernel that is a trace function on `A^1` rather than a
   ray-class character. *Why it is live:* the monodromy hypothesis (irreducible,
   simple identity component) is *already a theorem* for `L_univ` at `p = 2`,
   `j >= 4`.
5. **Cheng's Toeplitz-rank Vaughan (2.9) for the `s = 2` layer.** *Obstacle:*
   the symbol carries an explicit `1/2` (char `!= 2`), the band is fixed while
   ours grows like `j`, and the saving is against the trivial bound, not Weil.
6. **Bah--Shuddhodan uniform-in-`p` stratified vanishing (2.6).** *Obstacle:*
   constants depend on `d = j` with no stated growth; `Prim_j` is not `G_m^d`;
   the vanishing is generic in the Kummer twist, not for a specified sheaf.
7. **Bagshaw's `q`-free bilinear Kloosterman bounds (2.2 (i),(ii)).**
   *Obstacle:* they bound `e_F(a/x)`, additive characters of the inverse; the
   classical bridge to multiplicative characters mod `pi^n` is Postnikov's
   `chi(1+pi u) = psi(a log(1+pi u))`, and the `p`-adic log does not exist in
   characteristic 2. This is a clean, previously unrecorded statement of *why*
   the Kloosterman technology does not reach our characters at `p = 2`.

Everything below rank 7 in the sweep is `no`, with the obstacle in each case
being one of: `q` large (2.4, 2.8, most of 2.2), `p > k` or `p` odd (2.8, 2.16
Waring), squarefree modulus (2.4), or level-one Artin--Schreier (2.12, 2.11).

### (iii) Sentences in notes 00/09/10/13/14 that should change

1. **Note 14 sec. 11.4, "This is the most promising unexplored input for `(T2)`"**
   (of Hu--Teyssier arXiv:2502.11060). Change to: *explored, and it does not
   close `(T2)`*: their explicit `b_n` recursion gives `2^{Theta(n log n)}`, the
   same order as Sawin's Lemma 2.11, and the degree-graded form fails because
   `sum_k b_k(1) 2^{-k/2}` diverges (partial sums `1, 1.71, 10.2, 75, 690,
   7621`). Keep the paper, restate the target as "reduce the *coefficients* of
   `fd_k` for `k <= 7`".
2. **Note 14 sec. 11.3, the Katz--Laumon bullet** ("Katz--Laumon's own
   Remarque 5.5.2 says they do not know whether that `F` can be chosen
   uniformly"). Add: uniformity *in algebraic families* is now a theorem
   (arXiv:2506.18299); what remains missing is uniformity in the
   **characteristic** and applicability to a **specified** rather than generic
   twist.
3. **Note 09 / note 00, "Kaser--Lemire is a THEOREM for `q > n/2` (even `n`) /
   `q > (n+1)^2/4` (odd `n`)".** *(Corrected 2026-08-23, note 16.)* An
   `n`-independent companion exists but is narrower than first written: via the
   reversal duality, Bagshaw arXiv:2401.10399 Cor. 2.5 gives Kaser--Lemire over
   `F_q` for all `n >= n_0(q)` (ineffective) whenever **`p` is odd** and
   `q > 7101 p^2`, hence `l >= 3` and smallest admissible `q = 3^11`. It does
   NOT apply at `p = 2`. Since the two thresholds do not combine into an
   unconditional "all `n`" (the `n_0` is ineffective), notes 00/09 should quote
   the `n`-dependent Hsu/Cohen statement as before and add this only with its
   hypotheses attached.
4. **Note 07's wall paragraph, and note 00's "the wall (phase correlation)".**
   Both say the required fixed-`q` input is unavailable. Add the one exception:
   arXiv:2307.01344's `gcd` identity **is** a fixed-`q` saving over Weil for this
   family at level one, obtained without any monodromy input, and note 07's
   "the one exact fixed-`q` mechanism, the Witt carry formula" is no longer
   accurate as written -- there are two.
5. **Note 00's Barrier I discussion and note 07's "unbounded-above tail".**
   Add that Sawin arXiv:2209.02170 turns exactly that shape into a *theorem* in a
   neighbouring family (sparse vanishing locus + Plancherel forces a large
   value, hence no square-root cancellation), and that the same computation is
   available on the lane's own `A_psi` data.
6. **Note 13 sec. 8 (Type II transplant), "Connections to record".** Add
   arXiv:2511.09459: the structural monodromy hypothesis under which
   Polya--Vinogradov-range bilinear bounds are now available is satisfied by
   `L_univ`; the blocker is the prime modulus, not the monodromy.
7. **Note 10's question (Q3)** ("Is a fixed-`q` pair-correlation / variance
   theorem ... provable, even weakly"). Add the negative datum: at `q` **even**
   the extremal class for short-interval discrepancy is strictly larger than at
   `q` odd (arXiv:2202.10370), so a fixed-`q` statement at `p = 2` must survive a
   documented low-characteristic degeneracy that `p` odd does not have.

### (iv) Bottom line

**The 2023--2026 literature confirms that fixed `q` is untouched by the
cohomological route, and simultaneously hands the lane one lever it did not
have, one reframing, and one disproof template.**

*Untouched, cohomologically.* Every advance relevant to `(T1)`/`(T2)` -- Sawin's
Hypothesis H programme, Hu--Teyssier, Wan--Zhang, Bonolis--Kowalski--Woo,
Bah--Shuddhodan, Zurbuchen -- is either uniform in the wrong variable, generic in
a twist, restricted to level-one Artin--Schreier, or carries constants that grow
with the dimension `j`. `(T1)` remains what note 14 says it is: the
characteristic-two case of Sawin's Lemma 5.3, now confirmed to be the *same*
lemma that blocks his Waring paper (arXiv:2412.14053) at `p = 2`. `(T2)` has a
new best bound with the right *shape* and the wrong *constants*.

*The lever.* arXiv:2307.01344's `gcd(k, q^n-1)` identity is the first exact
fixed-`q` improvement over Weil for the Hayes family since the lane started, it
is proved in three lines with no geometry, and if it lifts from level one to
level `s` it lands a constant factor -- not a factor `ell` -- from `(HWO)`.
Whether it lifts is a bookkeeping question about single-position characters that
can be settled in the lane's CAS in an afternoon. **This is the single highest-value
next action from this sweep.**

*The reframing, corrected (2026-08-23, note 16).* After Bagshaw the
Kaser--Lemire statement is a theorem over `F_q` for all large `n` on a SPARSE
set of `q` -- `p` odd and `p^{l-2} > 7101`, smallest `3^11`, density
`O(X^{1/3})` -- not for "every `q >= 2^15`". Characteristic two, every prime
field, and every `q = p^2` are outside it. So the open set has NOT collapsed
to "small `q`": what is new is the first `n`-independent `q`-criterion for the
full window, which is worth recording and does not bear on `q = 2`.

*The disproof template.* Sawin's sparsity/Plancherel argument is the first
technique in the sweep that could resolve the lane's target in the **negative**,
at fixed `q`, in a prime-power-modulus family, and it needs a count the lane's
existing data already supports.

## 4. Reproducibility

Scratch dir (not in the repo):
`/tmp/claude-1000/-home-mjbommar-projects-personal-axeyum/<session>/scratchpad/lemire-signed-trace-arxiv/`
containing `q.py`, `absget.py`, `ht_b.py`, `cache/` (84 query XMLs plus
`id_list` fetches), and `papers/<arxiv-id>/` with the expanded LaTeX sources for
the papers read. The Hu--Teyssier evaluation in 2.5 is reproduced by
`python3 ht_b.py`; it implements their `defin_bi` recursion verbatim and prints
`b_n(1), b_n(2), b_n(4)` against `2^{n/2}`.

Not fetched or not read in full, and why: arXiv:2606.10041 (source pulled,
abstract-level digest only -- `T`-adic Newton-polygon machinery is a
self-contained subject and the verdict does not depend on the details);
arXiv:2602.21878 (abstract plus its treatment in arXiv:2608.00304);
MathOverflow is unreachable from this host (recorded already in the diary's first
literature check, and unchanged).

## 4. Coordinator's assessment of the lever (2026-08-23): it does not lift, and it is a known object

The sweep's rank-1 lever (2307.01344 `lem:sym`/`cor:sym`) is real and was
verified verbatim in the downloaded source. Two checks settle its reach, and
both are negative. They were the note's own "open check"; they are now closed.

**(i) Counting.** `E_j = prod_{k odd <= j} W_{e_k}(F_2) = prod_k Z/2^{e_k}`,
`e_k = floor(log2(j/k)) + 1`, `sum_k e_k = j`. A single-position ("monomial
phase") character is trivial on all but one factor, so their number is
`sum_k (2^{e_k} - 1) + 1`, and `2^{e_k} ~ 2j/k` gives `~ 2 j ln j` of them --
against `2^j` characters in the dual:

```
   j        #single-position    fraction of the dual
   24                    69     2^{-17.9}
  100                   377     2^{-91.4}
  200                   853     2^{-190.3}
 1024                  6145     2^{-1011.4}
```

A layer `X_{j,s}` has `~2^{j-1}` characters. Bounding a `2^{-1011}` fraction
of them better -- even perfectly, `|S_n(chi)| = 0` -- and the rest by Weil
leaves the layer sum exactly where Weil left it. The lever cannot bound
`T_{j,s}`, and therefore cannot give `(HWO)`.

**(ii) Mechanism: it is the Adams action, i.e. Barrier II.** The proof of
`lem:sym` reindexes `sum_{gamma in F_{q^n}^x} psi(Tr(gamma^{-k}))` by the power
map `x -> x^k`, whose image is the subgroup of index `gcd(k, q^n-1)`; hence `k`
may be replaced by `k' = gcd(k, q^n-1)`. That is exactly the power/Adams action
of [note 06](06-symmetry-barrier.md). It buys an unbounded saving there because
their phase is a SINGLE monomial `gamma^{-k}` with `log k = o(n^2)`, so the
whole phase is carried by one exponent that the power map collapses. A general
exact-conductor-`j` character has phase `psi(Tr(P(gamma)))` with `P` supported
on the odd `k <= j`; the power map moves the entire tuple at once, and note 06
measured the resulting orbit of the identity class: **size `<= 2`**. So the
general form of this symmetry is already proved insufficient, and the
single-monomial case is the sub-family where it is strong but rare.

**Consequence.** Sec. 3's "one lever ... a constant factor 4 from `(HWO)`" is
withdrawn: the factor-4 statement is correct per character and vacuous per
layer. What survives of 2307.01344 for this lane is (a) the observation that a
fixed-`q` improvement over Weil for a complete character family EXISTS at all,
which is worth knowing, and (b) their Lemma `lem:Blk` (`sum_{L<d<=2L} log
gcd(k, q^d-1)`), which is a tool for the same monomial sub-family.

The other two findings of sec. 3 are unaffected by this and remain open leads:
the Bagshaw reframing (verified 2026-08-23 in note 16 and **partly refuted**:
the threshold holds only at odd `p` with `l >= 3`, never at `p = 2`) and
Sawin's sparsity+Plancherel disproof template on the `A_psi` of note 07 (one
uncounted statistic, cheap in the existing dumps).
