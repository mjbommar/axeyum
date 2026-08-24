# AC-Bridge workstream 02: literature on additive energy, fourth moments,
# and design-type statements for structured spectra

Agent field: additive combinatorics / analytic number theory / coding theory,
literature side.  Opened 2026-08-20T16:14-04:00.

Project law (charter section "Rules", item 3) applies verbatim in this file:
**every reference is fetched from the web and quoted from what the page
actually says; nothing here is recalled from memory.**  Where a fetch failed
or an abstract did not carry the statement I need, the entry says
`UNVERIFIED` and is not used to support any conclusion.  Finite computation
is evidence, never a theorem.

Epistemic labels: PROVED (theorem with citation, or a self-contained argument
written out) / REFUTED (with witness) / OPEN.

## Notation used here

Charter notation, with one clarification that matters throughout, because the
charter and diary 09 use `M_2`, `M_4` for different (Parseval-equivalent)
objects and diary 07 for a third normalization:

```text
G      = G_ell = principal units of F_2[x]/x^(ell+1),  |G| = 2^ell
n      = 2 ell + 1 (odd endpoint) or 2 ell + 2 (even endpoint)
D_e    = N_e - 2^(n-ell)                     (class discrepancy, sum_e D_e = 0)
S_chi  = sum_e D_e chi(e)                    (Hayes character sum, S_1 = 0)
M_2    = sum_e D_e^2       ,  P_2 = sum_chi |S_chi|^2 = 2^ell M_2   (Parseval)
M_4    = sum_e D_e^4       ,  Q_4 = sum_(chi1 chi2 chi3 chi4 = 1) prod_i S_chi_i
                                 = 2^(3 ell) M_4                    (Parseval)
K_4    = 2^ell M_4 - 3 M_2^2 ,  R_0 = 2^ell M_4 / M_2^2 = 3 + K_4/M_2^2
(T-weak): M_4 < 2^(4(n-ell)).
```

The charter's "`M_2 = sum |S_chi|^2`" is diary 09's `P_2`; the charter's
"`M_4` = the product-constrained fourth moment" is diary 09's `Q_4`.  The two
normalizations differ by the fixed powers of `2^ell` shown above, so every
inequality below is stated in the `M_2`, `M_4` (physical-side) normalization
and can be transported by those identities.  I flag this because a factor
`2^(3 ell)` misplaced in `(T-weak)` would silently change the target by more
than the entire measured slack.

## Log

### 2026-08-20T16:20 -- required reading done; two arithmetic checks before any literature

Read in order: `00-charter.md` (all), sweep `00-synthesis.md` (all),
`09-additive-combinatorics.md` (all 722 lines), and the fibre/enumerator
sections of `07-coding-theory.md`.  Before opening a single paper I
re-derived the two numbers the whole charge hangs on, because a literature
review aimed at the wrong exponent is worse than none.

**Check A (PROVED, arithmetic on diary 07's own table) -- the two sweep
diaries disagree about the growth of `M_4`, and 09 is right.**

Diary 07 fits `M_4 ~ 0.6 ell^3 2^(3 ell)`; diary 09 predicts
`M_4 ~ 3 M_2^2 / 2^ell` with `M_2 ~ (ell-1) 2^n` (Keating--Rudnick), i.e.
`M_4 ~ 12 (ell-1)^2 2^(3 ell)` -- `ell^2`, not `ell^3`.  Recomputing both
normalizations from 07's six measured rows (`sqrt(M_2)/2^ell` and
`M_4^(1/4)/2^ell`, odd endpoint, `python3`):

```text
ell   M_2/2^(2ell)   M_4/2^(3ell)   M_4/ell^3   M_4/(ell-1)^2   3(M_2/2^(2ell))^2   ratio
  6      5.085           76.61        0.355         3.065            77.57         0.988
  8     10.582          324.42        0.634         6.621           335.94         0.966
  9     12.738          457.02        0.627         7.141           486.75         0.939
 11     17.817          944.15        0.709         9.441           952.32         0.991
 14     23.658         1681.46        0.613         9.949          1679.17         1.001
 15     25.624         1935.70        0.574         9.876          1969.74         0.983
```

The last column is `M_4 / (3 M_2^2 2^(-ell))`, i.e. `R_0/3`: it sits in
`[0.94, 1.00]` on every row with no trend.  The `ell^3` normalization
(column 4) has a coefficient that wanders `0.355 -> 0.709 -> 0.574` and never
settles; the `ell^2` normalization (column 5) rises monotonically toward the
predicted `12(1-1/ell)^2`.  **Conclusion: `M_4 = (3 + o(1)) M_2^2 2^(-ell)`
is the law, `M_4 ~ 12 (ell-1)^2 2^(3 ell)` is the asymptotic, and
`0.6 ell^3 2^(3 ell)` is a small-`ell` fit whose coefficient is still
moving.**  The correction matters for this workstream: it changes the
measured slack in `(T-weak)` from `2^ell/ell^3` to `2^ell/ell^2`, and every
"how much may a proof lose" statement downstream by a factor `ell`.
NEW (reconciles 07 against 09; neither diary states it).

**Check B (PROVED, given the ledger's proved inputs) -- `(T-weak)` is exactly
"beat the trivial `L^4 <= (L^2)^2` bound by a polynomial in `ell`".**

The trivial inequality `sum_e D_e^4 <= (sum_e D_e^2)^2` is `M_4 <= M_2^2`,
equivalently `R_0 <= 2^ell` (equality iff `D` is a delta -- which is exactly
the Lemire-failure configuration, so this is the sharp trivial bound).  Feed
in the *proved* Weil second-moment envelope `M_2 <= 2^(n-ell) Sigma(ell)`,
`Sigma(ell) = sum_(j=2)^ell 2^(j-1)(j-1)^2`, and note
`Sigma(ell) ~ 2^ell (ell-1)^2` (geometric, ratio 2; checked numerically:
`Sigma(200)/(2^200 * 199^2) = 0.99`).  Then

```text
(T-weak)  M_4 < 2^(4(n-ell))
   <==   R_0 <= 2^(ell + 2(n-ell)) / Sigma(ell)^2                    (SLACK, = 09)
   <==   beat the trivial R_0 <= 2^ell by the factor
             Sigma^2 / 2^(2(n-ell))  =  (ell-1)^4 / 4   (odd, n = 2ell+1)
                                     =  (ell-1)^4 / 16  (even, n = 2ell+2)
   <==   improve the trivial (4,2) norm inequality
             ||D||_4 <= 2^(ell/4) ||D||_2
         by the factor  (ell-1)/sqrt(2)  (odd)  /  (ell-1)/2  (even),
         where ||D||_p^p := 2^(-ell) sum_e |D_e|^p.
```

Numerically (exact integer `Sigma`, `python3`), the required fourth-root
gain is `5.05 / 9.25 / 14.88 / 33.96 / 69.30 / 140.01` at
`ell = 9 / 15 / 23 / 50 / 100 / 200` (odd endpoint), against
`(ell-1)/sqrt 2 = 5.66 / 9.90 / 15.56 / 34.65 / 70.00 / 140.71`.

Two consequences I did not find stated anywhere in the sweep:

1. **The `L^4` route and the triangle-inequality route need numerically the
   *same* polynomial saving.**  Diary 09's reading 2 says the endpoint is "a
   saving of `(ell-2)/sqrt 2` over the triangle inequality applied to Weil";
   Check B says `(T-weak)` is "a saving of `(ell-1)/sqrt 2` over the trivial
   `(4,2)` inequality".  They coincide because both are driven by the same
   proved `Sigma(ell)`.  So the exponential slack in `M_4` is *precisely* the
   price of Holder from `L^4` to `L^infinity`, spent and recovered; the honest
   difficulty of the endpoint is a **`poly(ell)` gain**, in whichever norm.
2. Therefore the literature I must survey is not "sharp fourth moments"
   (relative error `o(1)`) but **"fourth moments within `poly(size)` of the
   trivial bound"** -- a much larger and much cheaper body of technique.
   That reframing drives everything below and is why I searched
   divisor/quadruple-counting and design literature at all.

### 2026-08-20T16:45 -- charge 2/3: the one family where a product-constrained fourth moment is known EXACTLY at fixed q, including q = 2

This is the single most on-target reference I found, and it was not in any
sweep diary.

**Hofmann, Hoganson, Menon, Verreault, Zaman, *Moments of random
multiplicative functions over function fields*,
<https://arxiv.org/abs/2408.08309>** (Math. Proc. Cambridge Philos. Soc.;
also indexed at
<https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/abs/moments-of-random-multiplicative-functions-over-function-fields/DC5557F49E458F93E336068F74CF7FEA>).
Fetched the HTML full text <https://arxiv.org/html/2408.08309v1>; quoted
verbatim from it:

- Reduction (their eq. (2.1)):
  `E|sum_(F in M_N) f(F)|^(2k) = #{(F_1,...,F_(2k)) in M_N^(2k) :
   F_1 F_2 ... F_k = F_(k+1) ... F_(2k)}`.
  For `k = 2` this is exactly a **product-constrained fourth moment**:
  count quadruples with `F_1 F_2 = F_3 F_4`.
- **Theorem 1.3 (verbatim):** "For any prime power `q >= 2` and integer
  `N >= 1`, if `f` is a Steinhaus random multiplicative function defined over
  `F_q[t]`, then
  `E|sum_(F in M_N) f(F)|^4 = N q^(2N) (1 - 1/q) + q^(2N)`."
- Theorem 1.1 (asymptotics as `qN -> infinity`) and Theorem 1.2 (large-`q`,
  fixed `N`) express the general `2k`-th moment through `S_k(N)`, the number
  of `k x k` **magic squares** with magic constant `N`.

Why this is the right shape and where it breaks:

- **Right shape.**  It is an exact, unconditional, *fixed-q* (`q = 2`
  allowed), *all-N* evaluation of a fourth moment defined by a multiplicative
  product constraint, obtained by pure counting -- no oracle, no
  equidistribution input, no `q -> infinity`.  Mechanism: orthogonality
  collapses the moment to a lattice-point count (`F_1F_2 = F_3F_4` is
  parametrized by the divisor lattice / magic squares), and unique
  factorization in `F_q[t]` makes that count exact.
- **Relative size (this is the transferable datum).**  The second moment is
  `q^N`, so the Gaussian/Wick value for the fourth moment would be
  `2 q^(2N)`; the truth is `N q^(2N)(1-1/q) + q^(2N)`.  So the **kurtosis of
  this family is `~ N (1-1/q)`, i.e. it grows like the logarithm of the
  family size** -- the fourth moment is a `log`-power *above* Gaussian, not
  equal to it.
- **Where it breaks for us.**  Our `S_chi` are *not* the sums of a completely
  multiplicative random function over all monics; they are von
  Mangoldt-weighted sums over irreducibles in one Hayes class, and the
  quadruple constraint `chi_1 chi_2 chi_3 chi_4 = 1` lives in a *group*
  (`Ghat`), where the analogue of the divisor bound is vacuous: in any
  abelian group `#{(a,b) : a + b = c} = |G|` for every `c`.  Unique
  factorization is what makes the count exact there, and the dual of a finite
  abelian 2-group has none.  So the *method* does not transfer verbatim.
- **What does transfer, and it is worth stating as a modelling warning:**
  a "random multiplicative" model of the class discrepancy predicts
  kurtosis `~ ell`, whereas the measured kurtosis is `2.81-2.99` (07's six
  rows).  **The correct heuristic model for `D_e` is Gaussian /
  random-matrix (Keating--Rudnick, Katz monodromy), not multiplicative
  chaos.**  Both models are comfortably inside `(T-weak)` -- which needs only
  kurtosis `<= 2^ell 4/(ell-1)^4` -- and that is the encouraging reading:
  *every* comparable family whose fourth moment is unconditionally known has
  kurtosis at most a power of the log of the family size, i.e. `poly(ell)`
  here, i.e. `2^ell/poly` inside the target.

### 2026-08-20T17:00 -- charge 1/3: the classical orthogonality-trick fourth moment for character sums, and the divisor-bound family

The mechanism the sweep needs a name for is the oldest one in the subject:
**expand `|sum chi(x)|^4` by orthogonality and count solutions of a
multiplicative equation.**  Its canonical instance:

- **A. Ayyad, T. Cochrane, Z. Zheng, *The congruence `x_1 x_2 = x_3 x_4
  (mod p)`, the equation `x_1 x_2 = x_3 x_4`, and mean values of character
  sums*, J. Number Theory 59 (1996) 398-413.**  Bibliographic data verified
  by fetching the author's own publication list,
  <https://www.math.ksu.edu/~cochrane/research/research09.html>; paper PDF at
  <https://www.math.ksu.edu/~cochrane/research/xyuvmodp.pdf> (fetch returned
  an image-only/undecodable PDF, so **the exact theorem statement is
  UNVERIFIED here** -- I quote no formula from it).  The follow-up is
  **T. Cochrane, S. Shi, *The congruence `x_1 x_2 = x_3 x_4 (mod m)` and mean
  values of character sums*, J. Number Theory 130 (2010) 767-785**,
  <https://www.sciencedirect.com/science/article/pii/S0022314X09002339>
  (landing page only; ScienceDirect returned 403 on fetch).
- The modern, fully verified representative of the same technology is
  **Bourgain, Garaev, Konyagin, Shparlinski, *On congruences with products of
  variables from short intervals and applications*,
  <https://arxiv.org/abs/1203.0017>**.  Verbatim abstract: "We obtain upper
  bounds on the number of solutions to congruences of the type
  `(x_1+s)...(x_nu+s) = (y_1+s)...(y_nu+s) != 0 (mod p)` modulo a prime `p`
  with variables from some short intervals."  Their Theorem 19 (quoted from
  <https://ar5iv.labs.arxiv.org/abs/1203.0017>): "Let `nu >= 3` be fixed.
  Then `K_nu(p,h,s) <= (h^nu/p^(nu/e_nu) + 1) h^nu exp(c(nu) log h/log log h)`,
  where `e_nu = max{nu^2-2nu-2, nu^2-3nu+4}`."

  The `exp(c log h / log log h)` factor **is** the divisor bound, and it is
  exactly the "lossy but cheap" shape my charge asked me to hunt for: the
  count is obtained to within a factor that is `h^o(1)`, i.e. sub-polynomial.

**PROVED (one line) -- why this entire family gives nothing here.**  The
technology counts solutions of a multiplicative equation whose variables run
over a *sparse subset of a ring with unique factorization* (an interval in
`Z`, a box, a short interval of monics).  Our constraint is
`chi_1 chi_2 chi_3 chi_4 = 1` with the `chi_i` ranging over the **whole**
dual group `Ghat` of a finite abelian 2-group.  In any finite abelian group,
`#{(a,b) : a+b = c} = |G|` exactly, for every `c`; so the unweighted
quadruple count is `|Ghat|^3` with no cancellation available, and every
divisor-type refinement is vacuous.  All the content is in the weights
`S_chi`, never in the support.  **The orthogonality trick transfers (it is
how `Q_4` is defined), the counting half does not.**  This is the same
conclusion diary 09 reached for PFR by a different route, and it should be
recorded as closing the "quadruple-counting technology" family that my charge
item 3 asked about.

### 2026-08-20T17:15 -- charge 3: can slice rank / Croot--Lev--Pach bound the product-constrained fourth moment?  No, and the obstruction is structural, not quantitative.

Verified reference for the method's own known ceiling:
**S. Costa, M. Dalai, *A gap in the slice rank of k-tensors*,
<https://arxiv.org/abs/1905.07355>** (2019).  Verbatim abstract: "The
slice-rank method, introduced by Tao as a symmetrized version of the
polynomial method of Croot, Lev and Pach and Ellenberg and Gijswijt, has
proved to be a useful tool in a variety of combinatorial problems. Explicit
tensors have been introduced in different contexts but little is known about
the limitations of the method. In this paper, building upon a method
presented by Tao and Sawin, it is proved that the asymptotic slice rank of
any `k`-tensor in any field is either `1` or at least
`k/(k-1)^((k-1)/k)`."  And, verbatim: "This provides evidence that
straight-forward application of the method cannot give useful results in
certain problems for which non-trivial exponential bounds are already known."

Also verified as a scope statement: **L. Sauermann, *Finding solutions with
distinct variables to systems of linear equations over `F_p`*,
<https://arxiv.org/abs/2105.06863>**, which says verbatim that "all previous
combinatorial applications of the slice rank polynomial method have relied on
the slice rank of diagonal tensors".

**REFUTED (route), three independent reasons, each one line.**

1. **Wrong output type.**  Slice rank bounds `|A|` for sets `A` containing
   *no nontrivial solution* of an equation.  `(T-weak)` is an upper bound on
   a **weighted count over a full-support family**.  There is no
   solution-free hypothesis anywhere in our problem: `S_chi != 0` for
   essentially every `chi`.
2. **The unweighted problem is already sharp and already trivial.**  A subset
   of `Ghat` with no nontrivial additive quadruple is a Sidon (`B_2`) set.
   Definition verified verbatim from D. Thornburgh, *On generalizing
   cryptographic results to Sidon sets in `F_2^n`*,
   <https://arxiv.org/abs/2501.11184> (2025): "A Sidon set `S` in `F_2^n` is a
   set such that `x+y=z+w` has no solutions `x,y,z,w in S` with `x,y,z,w` all
   distinct."  The counting bound is one line and I write it out rather than
   cite it: the `binom(|A|,2)` pairwise sums are distinct and nonzero, so
   `|A|(|A|-1)/2 <= 2^m - 1`, i.e. `|A| <= 2^((m+1)/2)` in `F_2^m`; and
   graphs of APN functions give Sidon sets of size `2^(m/2)`, which is the
   connection Thornburgh's paper is about (his contribution is to increase
   "the best-known lower bound of the largest Sidon set in `F_2^(4t+1)` by 1
   for all `t >= 4`" -- i.e. the extremal problem is being fought over `+1`,
   which is exactly how little room a rank method would have).  (The sharper
   closed form `floor((1 + sqrt(2^(m+3)-7))/2)` appears in search summaries
   but I could not fetch a source carrying it: **UNVERIFIED**, and not used.)
3. **Even a maximally successful slice-rank argument is too small by
   construction.**  Applied to a `4`-variable equation over `F_2`, the
   Costa--Dalai gap caps the achievable exponential saving at
   `(2 / (4/3^(3/4)))^ell = (2/1.7548)^ell = 2^(0.189 ell)` per coordinate,
   and it would be a saving on a *set size*, not on `M_4`.  For comparison,
   `(T-weak)` needs no exponential saving at all -- it needs `poly(ell)`
   (Check B) -- so the method is simultaneously the wrong tool and pointed at
   the wrong axis.

NEW TO THE LEDGER: item 3 of my charge ("could a slice-rank argument bound
the number of solutions of `chi_1 chi_2 = chi_3 chi_4` restricted to the
Frobenius spectrum?") is answered **no**, with a cited ceiling theorem, and
should not be re-proposed.

### 2026-08-20T17:35 -- charge 1: the finite-field restriction / energy literature, and the one lemma that closes ALL of it at once

Sub-search (independent agent, WebSearch+WebFetch only, results re-checked by
me against the fetched pages it named) returned the following, which I record
because they are the exact "clean fourth-moment statements" my charge asked
for.  Everything here is a **set/support** hypothesis; that is the point.

- **Mockenhaupt--Tao, *Restriction and Kakeya phenomena for finite fields*,
  <https://arxiv.org/abs/math/0204234>, Duke Math. J. 121 (2004) 35-74**
  (<https://projecteuclid.org/euclid.dmj/1072058749>).  Their Section 5
  ("Even exponents") **Lemma 5.1**, as rendered at
  <https://ar5iv.labs.arxiv.org/html/math/0204234>:
  > "If `q = 2k` is a positive even integer, and the number of solutions to
  > `eta = xi_1 + ... + xi_k` with `xi_i in S` is bounded by `A`, then
  > `R*(2 -> 2k) <= A^(1/2k) |F|^(n/2k) |S|^(-1/2)`."

  At `k = 2` this **is** the fourth-moment/additive-energy statement: the
  `L^4` norm expands by Plancherel into the quadruple count on `S`.  Note the
  hypothesis: only that `S` is a finite **set**; the coefficient function is
  arbitrary, so the estimate is uniform over all weights.
- Successors, same shape: **Iosevich--Koh**, <https://arxiv.org/abs/0805.0814>
  (Lemma 7: `Lambda_4(E) <~ min{|E|^3, q^(-1)|E|^3 + q^((d-2)/4)|E|^(5/2) +
  q^((d-2)/2)|E|^2}` for `E` in the paraboloid, `d >= 4` even);
  **M. Lewko**, <https://arxiv.org/abs/1302.6664> (breaks Mockenhaupt--Tao's
  `18/5` for the 3-d paraboloid); **Rudnev--Shkredov**,
  <https://arxiv.org/abs/1803.11035>, Adv. Math. 339 (2018) 657-671.
- The exact `L^4`-equals-energy identity, in the modern normalization:
  **Cheong--Ge--Koh--Pham--Tran--Zhang**, <https://arxiv.org/abs/2510.26364>,
  Lemma 14 (as rendered at <https://arxiv.org/html/2510.26364v3>):
  `||Ehat||_(2k)^(2k) = q^(-d(2k)) Lambda_(2k)(E) - q^(-d(2k+1)) |E|^(2k)`,
  and their `(u,s)`-Salem definition `||Ehat||_u << q^(-d)|E|^(1-s)`.
- The `L^p`-graded framework that names the object: **J. M. Fraser, *L^p
  averages of the Fourier transform in finite fields*,
  <https://arxiv.org/abs/2407.08589>** (2024).  Definition quoted verbatim
  from <https://arxiv.org/html/2407.08589v4>: `E` is `(p,s)`-Salem if
  `||Ehat||_p <~ q^(-d)(#E)^(1-s)`, with
  `||Ehat||_p = ( q^(-d) sum_(x != 0) |Ehat(x)|^p )^(1/p)`, and
  `alpha_E(p) := sup{s : E is (p,s)-Salem}`.  Their Theorem 5.1: random sets
  of size `q^alpha` satisfy `||Xhat||_p <~ q^(-d) q^(alpha/2)`.
- Additive energy of multiplicative subgroups (charge 1a), verified:
  Heath-Brown--Konyagin's `E(Gamma) = O(|Gamma|^(5/2))` for
  `|Gamma| = O(p^(2/3))` -- restated as Theorem 1 of Shkredov,
  <https://arxiv.org/abs/1208.2344>, which improves it to
  `E(Gamma) << |Gamma|^(22/9) log|Gamma|` for `|Gamma| << p^(3/5) log^(-6/5) p`
  (independently corroborated as Lemma 26 of arXiv:2510.26364);
  Murphy--Rudnev--Shkredov--Shteinikov, <https://arxiv.org/abs/1712.00410>,
  `E(A) <<_M |A|^(49/20) log^(1/5)|A|` for `|AA| <= M|A|`, and for subgroups
  with `|Gamma| <= sqrt p`.  (Which of `22/9` and `49/20` is the current
  record for subgroups is UNVERIFIED; they are in different hypothesis
  classes.)
- Additive energy of polynomial value sets (charge 1b), verified:
  **Kerr--Mohammadi--Shparlinski, *Additive energy of polynomial images*,
  <https://arxiv.org/abs/2306.10677>**, Theorem 1.1
  `T_(f,m)(I) <= H^(3+o(1)) min{(m/H)^(-alpha_d), H^(-beta_d)}`,
  `alpha_d = 2/(d^2+d-2)`, `beta_d = 2/(d+2)`.
- Nearest named object to "additive energy of the spectrum":
  **Shkredov, *A short note on the multiplicative energy of the spectrum of a
  set*, <https://arxiv.org/abs/1805.10468>**, Theorem 1: for
  `R subset Spec_eps(A)\{0}`, `|{(x,y,z,w) in R^4 : xy = zw}| << eps^(-4)
  delta^(-1)|R|^(3/2)`.  The spectrum there is a **set** of frequencies and
  the quadruple count is **unweighted**.
- The weighted-vs-support distinction is known to be real:
  **A. Lewko and M. Lewko, *On the structure of sets of large doubling*,
  <https://arxiv.org/abs/1003.4561>**, abstract verbatim: "...enables us to
  construct **a `Lambda(4)` set which does not contain large `B_2[g]` or
  `B^o_2[g]` sets**."  `Lambda(4)` is the *weighted* condition; `B_2[g]` is
  the *support* condition.
- Explicit negative results from the same sub-search (arXiv-only, phrase
  sensitive, so weak but honest): arXiv searches for `"Sidon set of
  characters"` and for `abs:"additive energy" AND abs:"value set"` returned
  **zero** hits; no paper was found bounding
  `sum_(chi_1 chi_2 chi_3 chi_4 = 1) prod c_(chi_i)` for a weighted family.
  This agrees with diary 09's "no standard machine exists" and I did not find
  one either.

**Now the lemma that makes all of the above inapplicable at once.  I believe
this is the sharpest single statement in this file.**

> **Lemma W (weight-blindness).  PROVED, exact, unconditional.**
> Let `G` be a finite abelian group, `M = |G|`, and for `a: Ghat -> C` put
> `f_a(e) = sum_chi a_chi chi(e)`.  Normalize `||f||_p^p = E_(e in G)|f(e)|^p`.
> Then
> ```text
> sup_(a != 0)  ||f_a||_4 / ||f_a||_2  =  M^(1/4) ,
> ```
> and the supremum is attained **exactly** at `a = const`, i.e. at
> `f_a = M * delta_(e_0)` -- a point mass.
> *Proof.*  Upper bound: `||f||_4^4 <= ||f||_infinity^2 ||f||_2^2` and
> `||f||_infinity <= sum_chi |a_chi| <= M^(1/2)(sum|a_chi|^2)^(1/2) =
> M^(1/2)||f||_2` by Cauchy--Schwarz and Parseval, giving
> `||f||_4^4 <= M ||f||_2^4`.  Attainment: `a = 1` gives `f = M delta`,
> `||f||_2^2 = M`, `||f||_4^4 = M^3`, ratio `M^(1/4)`.  QED

Consequences, stated so that this whole family is closed once:

1. **Every inequality whose hypothesis mentions only the support of the
   spectrum is, for us, exactly the trivial bound -- not merely lossy, but
   *equal* to it.**  Our spectrum has full support (`S_chi != 0` for
   essentially every `chi`), so `S = Ghat`, and Lemma W says the best
   constant available uniformly over coefficient vectors is `M^(1/4) =
   2^(ell/4)`, which is precisely the trivial `R_0 <= 2^ell` of Check B.
   `(T-weak)` needs to beat that by `(ell-1)/sqrt 2`.  **A support-only
   hypothesis therefore cannot deliver even a factor `1 + epsilon`.**
2. This subsumes, with a single two-line proof and no model input: the
   Mockenhaupt--Tao/Iosevich--Koh/Lewko/Rudnev--Shkredov restriction family
   (Lemma 5.1's `A` is `|S|^(k-1)` when `S` is everything -- the estimate
   degenerates to Parseval), all `(p,s)`-Salem statements, all
   energy-of-an-algebraic-set bounds, all multiplicative-subgroup energy
   bounds, and Rudin's `Lambda(4)` theory (`Lambda(4)` is the
   uniform-over-weights condition, and the `Lambda(4)` constant of the *full*
   dual group is exactly the trivial `M^(1/4)`).
3. It also **strengthens diary 09's `L^p`-deficit finding**, which was
   PROVED-modulo-the-second-moment-model and quantified the loss as
   `(ell/2)^(p/2)`.  Lemma W needs no model and gives exact equality with the
   trivial bound.  Recommend the ledger carry Lemma W as the general
   statement and 09's deficit formula as the quantitative refinement.
4. **The positive content**: a proof of `(T-weak)` must consume a property of
   the *specific* coefficient vector `S_chi`.  The available such properties
   are exactly the arithmetic ones the lane already owns -- the Weil/Katz
   eigenvalue structure of each `S_chi`, the conductor filtration, the
   cylinder masses `B_j(b)`, integrality and the one-sided bound
   `D_e >= -2^(n-ell)`.  This is *why* the surviving route in diary 09
   (global hypercontractivity on the Witt grading) is structurally different
   from everything closed above: **"globalness" is a hypothesis on the
   function, not on its support.**  Lemma W is, in that sense, an argument
   *for* route (b), not just against the rest.

### 2026-08-20T18:10 -- charge 2: the Montgomery--Soundararajan identification, VERIFIED and REFINED (it is harder than the sweep recorded, in a way that argues even more strongly for (T-weak))

The sweep (diary 09, synthesis "Ledger corrections") records: "`K_4 <= M_2^2`
is the fixed-`q` case of Montgomery--Soundararajan (open over `Z`)".  I was
asked to verify and refine.  **Verified in substance; refined in three ways,
each of which makes the uniform target look worse and `(T-weak)` look better.**

What I could verify by fetch:

- **Montgomery--Soundararajan, *Primes in short intervals*, Comm. Math. Phys.
  252 (2004) 589-617, <https://arxiv.org/abs/math/0409258>**.  Abstract
  verbatim: "Contrary to what would be predicted on the basis of Cramer's
  model concerning the distribution of prime numbers, we develop evidence
  that the distribution of `psi(x+H) - psi(x)`, for `0 <= x <= N`, is
  approximately normal with mean `~H` and variance `~H log N/H`, when
  `N^delta <= H <= N^(1-delta)`."
- The moment form, quoted from the introduction of **Parry,
  <https://arxiv.org/html/2409.00431v2>**: the conjecture is
  `(1/N) int_1^N (psi(t) - h)^k dt ~ mu_k (h log(N/h))^(k/2)` with `mu_k` the
  standard normal moments, in the range `N^eps <= h <= N^(1-eps)`; and
  "Under the Riemann hypothesis and the Hardy--Littlewood `k`-tuple
  conjecture, Montgomery and Soundararajan proved" it.
- **UNVERIFIED and flagged:** a search summary asserted the conditional
  theorem holds only for `(log N)^(15 k^2) <= h <= N^(1/k - delta)`.  I could
  not fetch a page carrying that range (the CMP page and two arXiv HTML
  routes failed).  **It matters**: our endpoint sits at `H ~ sqrt N`
  (`n - ell ~ n/2`), which is inside the *conjecture's* range but would be
  outside a `N^(1/4)` range for `k = 4`.  Do not repeat the `N^(1/k-delta)`
  range as fact until someone reads the paper.

**Refinement 1 (verified): unconditionally over `Z`, not even the third
moment is known; the state of the art is 2024-2026 and is an average over
progressions.**  Tomos Parry, *Primes in arithmetic progressions on average
II*, <https://arxiv.org/abs/2409.00431>, abstract verbatim: "A deep
conjecture of Montgomery and Soundararajan on the distribution of prime
numbers in short intervals of length `h` says that the third moment is
bounded by `<< h^(3/2-c)` for some `c>0`. There is in the literature some
conditional evidence towards this conjecture whilst in the first article to
this series we gave the first instance of unconditional evidence in the form
of a bound corresponding to `<< h^(7/5+o(1))`. In this article we push the
exponent down to `<< h^(1+o(1))` which more or less is expected to be best
possible."  So: **third** moment, **on average over moduli**, and only since
2024.  Nothing unconditional at the **fourth**.

**Refinement 2 (verified, and this is the one the ledger should carry): on
the function-field side the fourth moment is open even in the large-`q`
limit, where the sweep's dictionary implicitly assumed it was known.**

- Keating--Rudnick, <https://arxiv.org/abs/1204.0708>, **Theorem 2.1
  verbatim**: "Let `h < n - 3`. Then `lim_(q->infinity) (1/q^(h+1))
  Var(nu(.;h)) = n - h - 2`."  This is the **variance only**, and explicitly
  `q -> infinity`.  (It does confirm diary 09's identification
  `M_2 = (ell-1) 2^n`: substituting `h = n-ell-1` gives `n-h-2 = ell-1`.)
- Rodgers, <https://arxiv.org/abs/1609.02967>, Alg. Number Th. 12 (2018)
  1243-1279: **Theorem 3.1 is a variance, not a higher moment**, verbatim
  "`Var_(f in M_n) sum_(g in I(f;h)) a(g) = q^(h+1) sum_(lambda |- n,
  lambda_1 <= n-h-2) |ahat_lambda|^2 + O(q^(h+1/2))`", with the explicit
  caveat "the result is only of interest as `q -> infinity`".  A sub-agent
  grep of the paper for "Gaussian" / "higher moment" / "central limit" found
  hits only in the bibliography.  **Diary 09 cites Rodgers as the
  general-factorization-function version of the Gaussian-moments statement;
  that is a slight over-reading -- Rodgers proves the second moment.**
- Sawin--Shusterman, Annals 196 (2022) 457-506,
  <https://arxiv.org/abs/1808.04001>, list "Calculating the variance (and
  higher moments) of the Mobius function in short intervals (and arithmetic
  progressions) over `F_q[T]`" as **future work**.

**Refinement 3 (verified): at fixed `q`, and specifically at `q = 2`, there
is essentially nothing about primes, and the two nearest results exclude us
by name.**

- Sawin--Shusterman **Theorem 1.1 verbatim**: "For an odd prime number `p`,
  and a power `q` of `p` satisfying `q > 685090 p^2`, ..." -- and their
  **Remark 1.10 verbatim**: "It would be interesting to see whether our
  results can be extended to characteristic 2".  Their smallest listed
  example is `F_(3^15)`.  `q = 2` is excluded explicitly.
- Sawin, Duke 170 (2021) 997-1026, <https://arxiv.org/abs/1809.05137>:
  Theorems 1.1/1.2 are unconditional and formally uniform in `q`, but the
  exponent carries `floor(n/p) - floor((n-h)/p)` and a factor `(n+2)^(2n-h)`,
  so they are vacuous at `p = 2` with `n` growing; square-root cancellation
  is exactly the `p > n` case.
- The only fixed-`q` **exact** moment I found that reaches `q = 2` is for the
  divisor function, not the primes: Yiasemides,
  <https://arxiv.org/abs/2110.05959>, **Theorem 1.2.1 verbatim**: "For
  `n >= 4` we have `(1/q^n) sum_(A in M_n) |Delta(A;h)|^2 =
  (q-1) q^(h-1) (n-2h-1)(n-2h)(n-2h+1)/6` for `h <= floor(n/2)-1, and 0 for
  `h >= floor(n/2)`", with the v2 note that it now holds "over a finite field
  of any prime-power order".  **Mechanism: additive-character orthogonality
  reduced to ranks of Hankel matrices over `F_q` -- no Katz, no large `q`.**
  Attributed by the author as identical to Gorodetsky's thesis result.
- Also fixed-`q`, large-degree, first moment only: Gorodetsky, Mathematika 66
  (2020) 373-394, <https://arxiv.org/abs/1810.00483>, abstract verbatim:
  "As opposed to many previous works, our results apply in the large-degree
  limit, where the base field `F_q` is fixed... based on relationships
  between certain character sums and symmetric functions... and recent bounds
  of Bhowmick, Le and Liu on character sums, which are in the spirit of the
  Drinfeld-Vladut bound."

**Net refinement, for the ledger.**  `K_4 <= M_2^2` is not merely "the
fixed-`q` case of a conjecture open over `Z`".  It is a case of a statement
that is open at **every** level of the standard difficulty ladder:
unconditional over `Z` (only the 3rd moment, on average, since 2024);
conditional over `Z` (needs RH + HL `k`-tuples); function-field large-`q`
(only the variance -- Katz-equidistribution methods have not reached the 4th
moment); function-field fixed `q` (nothing for primes); and `q = 2`
specifically (excluded by name in the one fixed-`q` prime result there is).
**Five levels, all open.**  That is the strongest possible argument for
retargeting to `(T-weak)`, and it should be recorded as a difficulty datum
rather than re-derived by the next lane.

### 2026-08-20T18:35 -- the closest published theorem to (T-weak), and exactly what is missing: Hast--Matei at m = 4

This is the most actionable finding in this file.  I fetched and verified the
statement myself at <https://ar5iv.labs.arxiv.org/html/1604.02067>.

**Hast--Matei, *Higher moments of arithmetic functions in short intervals: a
geometric perspective*, IMRN 2019 no. 21, 6554-6584,
<https://arxiv.org/abs/1604.02067>.  Theorem 1.4, verbatim as rendered:**
> "For any integers `m>=2`, `n>=4`, and `1<=h<=n-3`, there are constants
> `C_(m,n,h)` and `D_(m,n,h)` such that for every prime `p` (assuming `p>n` if
> `m>2`) and every positive integer power `q=p^r`:
> `|1/q^n sum_(f in M_n(F_q)) ( sum_(g, deg g<=h) [Lambda(f+g) - 1] )^m|
>  <= C_(m,n,h) q^((h+1)(m-1))`"
> and similarly for `mu` with `D_(m,n,h)`.

Their **Remark 1.5** (as rendered) says the `m >= 3` bound is weaker than
conjecturally optimal, that the expected order is `q^(m(h+1)/2)`, and that
the missing cancellation "should come from nontrivial `S_n^m`-action on
cohomology in ranges not yet computed".

**Translation into charter notation (PROVED, arithmetic).**  The reciprocal
dictionary makes a Hayes class the short interval `I(f;h)` with
`h = n-ell-1`, so `#I = q^(h+1) = 2^(n-ell)` and the inner sum is exactly
`D_e`.  The theorem's left side is `E_e[D_e^m]`, so with `M_m = 2^ell E_e[D_e^m]`:

```text
m = 4:  M_4 <= C_(4,n,h) * 2^ell * 2^(3(n-ell)) .
(T-weak): M_4 < 2^(4(n-ell)) .
ratio  =  C_(4,n,h) * 2^(ell - (n-ell))  =  C_(4,n,h)/2   (odd, n = 2ell+1)
                                        =  C_(4,n,h)/4   (even, n = 2ell+2).
```

> **Therefore: `(T-weak)` at the odd endpoint is *exactly* Hast--Matei's
> Theorem 1.4 at `m = 4` with the constant `C_(4,n,h) < 2` (and `< 4` at the
> even endpoint).  The published theorem already has the right shape; the
> entire remaining content is (i) the constant and (ii) the hypothesis
> `p > n`, which at `p = 2`, `n = 2 ell + 1` fails for every `ell >= 1`.**

Sanity check against measured truth, so nobody thinks `C < 2` is a knife
edge: the true `M_4 ~ 12(ell-1)^2 2^(3 ell)` (Check A) corresponds to
`C_(4,n,h) ~ 1.5 (ell-1)^2 2^(-ell)` -- **exponentially small**.  The
requirement `C < 2` therefore has the same `2^ell/poly(ell)` slack as
everything else in this project; it is not a sharp-constant problem.

Three consequences I would land in the ledger immediately:

1. **The lane's blocker now has a one-line published-literature statement:**
   "remove the tameness hypothesis `p > n` from Hast--Matei Theorem 1.4 at
   `m = 4`, with an absolute constant".  That is a far better handoff
   sentence than any of the `M_4 <= c ell^k 2^(3ell)` forms in the ledger,
   and it is the same missing ingredient diary 06 identified from the
   etale-cohomology side (wild ramification at `p = 2`).  `p > n` is exactly
   the tame-ramification hypothesis.
2. **The `m = 2` case is unconditional at `q = 2`** (the `p > n` proviso is
   only for `m > 2`), i.e. Hast--Matei already give a fixed-`q`,
   characteristic-2 variance bound `M_2 <= C_(2,n,h) 2^n` of the right order.
   Combined with Check B, the lane's proved second-moment input has a second,
   independent published source besides the Weil envelope.
3. Hast--Matei's Remark 1.5 names the missing mechanism as the
   `S_n^m`-action on cohomology -- which is diary 06's equivariant localized
   trace formula route, item C of the surviving frontier.  **Routes A and C
   of the sweep synthesis are the same route seen from two sides.**  That is
   worth recording; the sweep lists them as independent.

### 2026-08-20T18:55 -- charge 4: spectral designs, epsilon-bias, and exact fourth moments of Weil-sum families

Sub-search (independent agent; every quote below is from a page or a
`pdftotext` extraction it fetched, and the flagged items are its own honest
UNVERIFIEDs, which I have kept).

**(i) The design mechanism, exactly stated.**  The reason a "4-design"
hypothesis would give the fourth moment for free is the **Pless power moment
identity**.  Quoted verbatim (as Theorem 13, eq. (48), of D. S. Kim,
<https://arxiv.org/pdf/0807.4671>, which reproduces it): for a `q`-ary
`[n,k]` code `B` with dual weight counts `B_i^perp`,

```text
sum_(j=0)^n j^h B_j
  = sum_(j=0)^(min{n,h}) (-1)^j B_j^perp
      sum_(t=j)^h t! S(h,t) q^(k-t) (q-1)^(t-j) binom(n-j, n-t) ,
```
`S(h,t)` a Stirling number of the second kind.  **The right side involves only
`B_0^perp, ..., B_h^perp`.**  Hence (DERIVED by inspection, not quoted from a
source): if the dual distance is `>= 5` then `B_1^perp = ... = B_4^perp = 0`
and the first four power moments take exactly their binomial ("random")
values.  Companion fact, quoted verbatim from Lin--Stufken,
<https://arxiv.org/html/2505.15032v1>, Theorem 4.1: "If `C` is a `(k,N,d)_s`
linear code over `S = GF(s)` with dual distance `d^perp`, then the codewords
of `C` form the rows of an `OA(N, s^k, d^perp - 1)`" (Bose 1961; Delsarte
1973).

So the clean design-type statement is: **dual distance `>= 5` (equivalently
orthogonal-array strength `>= 4`, equivalently exact 4-wise uniformity) makes
the fourth moment exactly the random value, with no error term at all.**

Where it breaks for us, and this is decisive: our family is the
**subfield-restricted (`F_2`-rational) wild family**, and diary 07 already
proved (its 16:30 entry) that the exactly-evaluable corner has size
`O(ell)` out of `2^ell` and sits entirely inside the low-conductor window
that diary 09's uncertainty-principle lemma shows is useless.  A dual
distance `>= 5` for the wild trace code would be a statement of exactly the
kind the lane has repeatedly measured to be false at low conductor
(low-weight dual words = the Frobenius/Gold relations).  **The design route
is therefore not a route but a *diagnostic*: `(T-weak)` is precisely the
assertion that the family is an approximate strength-4 orthogonal array to
within a factor `2^ell/poly(ell)` -- an extraordinarily weak approximate
design condition.**

**(ii) `epsilon`-bias -> `k`-wise uniformity: the exact constants.**
Alon--Goldreich--Hastad--Peralta (FOCS 1990, 544-553; Random Structures
Algorithms 3 (1992) 289-304), <https://www.tau.ac.il/~nogaa/PDFS/aghp4.pdf>.
**Lemma 1 (Vazirani), verbatim:** "Let `S_n subset {0,1}^n` be a sample space
that is `eps`-biased with respect to linear tests of size at most `k`. Then
the sample space `S_n` is `(eps(1-2^(-k)), k)`-independent (in max norm), and
`eps(2^k-1)^(1/2)`-away (in `L1` norm) from `k`-wise independence."  Their own
remark, verbatim: "In the applications of the lemma we will use the bounds
`eps` and `2^(k/2) eps` respectively, since the difference is minimal."
The abelian-group version is quoted verbatim in Jalan--Moshkovitz,
<https://arxiv.org/pdf/2105.01149v1>: "Vazirani's XOR Lemma asserts that an
`eps`-biased distribution `D` is also `(eps sqrt(|G|^k), k)`-wise independent
for all `k <= n`", with `Bias(D) = max_(chi != chi_0) |E_(x~D) chi(x)|`.
Note the `sqrt(|G|^k)` amplification: for `G` of size `2^ell` and `k = 4`
this is `2^(2 ell)`, i.e. **the XOR-lemma route is exponentially lossy in
exactly our regime** -- and, unusually, `(T-weak)` has exponential slack, so
this is the one place where an exponentially lossy design lemma is *almost*
affordable.  It is not quite: the loss is `2^(2ell)` and the budget is
`2^ell`.  Recorded as a near-miss, with the exact constants, so the next lane
can check whether the group-graded version (`|G|` replaced by the individual
cyclic factor orders `2^(k_i)`) lands inside budget -- that is a real
question and it is cheap.
**"Small bias implies small fourth moment for a family of characters" as a
named theorem: NOT FOUND (UNVERIFIED that it does not exist).**

**(iii) Exact fourth moments of Weil-sum families -- and a correction to my
own charge.**  My brief said "Katz's Sato--Tate style fourth-moment
computations for Kloosterman sums are exact -- record the mechanism".  That
premise is **wrong**, and the correction is worth more than the original
claim:

- The **exactness is Salie's (1931/32) elementary recursion, not Katz's
  monodromy.**  Quoted verbatim from D. S. Kim, <https://arxiv.org/pdf/0807.4671>,
  eq. (57): `MK^h = q^2 M_(h-1) - (q-1)^(h-1) + 2(-1)^(h-1)` for `h >= 1`,
  where `M_h = |{(a_1,...,a_h) in (F_q^*)^h : sum a_j = 1 = sum a_j^(-1)}|`,
  and Kim notes "this holds for any prime power `q = p^r`".  Exact values,
  verbatim: `MK^1 = 1`, `MK^2 = p^2-p-1`, `MK^4 = 2p^3-3p^2-3p-1` for
  `p >= 3`, and **`MK^4 = 1` for `p = 2`**.  Independently confirmed with the
  same values by Garcia--Todd, <https://arxiv.org/pdf/1804.07397>.
  **Mechanism: orthogonality collapses the fourth moment to the count of
  solutions of a pair of symmetric equations (`sum a_j = 1 = sum a_j^(-1)`),
  and that count satisfies a one-step recursion.**  This is the same
  orthogonality-then-count mechanism as the 17:00 entry, and it is exact
  because the constraint set is a *variety*, not a group.
- **Katz, *Gauss Sums, Kloosterman Sums, and Monodromy Groups*, Annals of
  Math. Studies 116, Princeton 1988, <https://web.math.princeton.edu/~nmk/Katz-GKM.pdf>,
  gives equidistribution with an error, not exact moments.**  Theorem 13.5.3
  is a weak-* convergence statement as `q -> infinity`; Example 13.6 gives
  the Sato--Tate measure `(2/pi) sin^2 theta d theta` and the estimate
  `|int_0^pi (sin((n+1)theta)/sin theta) d mu(F_p)| <= (n+1) 2 sqrt p/(p-1)`.
  A full-text grep of the book for "Catalan" returns **zero** hits: the
  "moments are Catalan numbers" statement is the moment computation *of the
  limiting measure*, plus Weyl, not a theorem of the book.  **For a fixed
  `q` -- our situation -- Katz gives `O(n q^(-1/2))`, which at `q = 2` is
  worse than trivial.**
- **Daniel J. Katz, *Weil sums of binomials*, <https://arxiv.org/pdf/1805.10452>,
  Corollary 7.4**, for `W_(F,d)(a) = sum_x psi(x^d + a x)` and
  `P^(k) = sum_(a in F^*) W(a)^k`: `P^(0) = |F|-1`, `P^(1) = |F|`,
  `P^(2) = |F|^2`, `P^(3) = |F|^2 M_1`, and
  **`P^(4) = |F|^2 sum_(a in F^*) M_a^2`**, where
  `M_a = |{x in F : x^d + (1-x)^d = a}|`.
  **This is the single most structurally transferable mechanism I found**:
  moments `0,1,2` are exact and *universal* (independent of `d`, i.e. exactly
  the random values), and the **fourth moment of the character family is
  exactly a *second* moment of a difference-counting function** -- the
  differential spectrum of `x -> x^d`.  The survey says so verbatim: "the
  power moments of `W_(F,d)` are intimately connected to the differential
  spectrum of the power permutation `x -> x^d` of `F`".

### 2026-08-20T19:10 -- the transfer of that mechanism, written out: (T-weak) is a statement about the self-convolution of the spectrum

Daniel Katz's `P^(4) = |F|^2 sum_a M_a^2` is "fourth moment upstairs = second
moment of a convolution downstairs".  Written out in charter notation this is
an exact identity that I do not find in any sweep diary, and it is the
cleanest `L^2` form of `(T-weak)`:

> **Identity C (PROVED, two lines of Parseval).**  Let
> `(S * S)(chi) := sum_psi S_psi S_(chi psi^(-1))`.  Then
> ```text
> widehat(D^2)(chi) = 2^(-ell) (S * S)(chi) ,     hence
> M_4 = sum_e D_e^4 = 2^(-3 ell) || S * S ||_2^2 = 2^(-3 ell) Q_4 .
> ```
> *Proof.*  `D_e = 2^(-ell) sum_psi S_psi conj(psi(e))`, so
> `D_e^2 = 2^(-2ell) sum_(psi_1,psi_2) S_(psi_1) S_(psi_2)
> conj((psi_1 psi_2)(e))`; summing against `chi(e)` and using
> `sum_e chi conj(psi_1 psi_2) = 2^ell [psi_1 psi_2 = chi]` gives the first
> line; Parseval on `D^2` gives the second.  QED

Consequently:

```text
(T-weak)  <==>  || S * S ||_2^2  <  2^(3 ell + 4(n-ell)) .
```

This is worth stating because it changes what kind of theorem is needed.
`M_2` is an `L^2` statement about `S`; `(T-weak)` is an `L^2` statement about
`S * S`.  That is literally "one grading further", which is the gap the
charter names.  And unlike `M_4`, an `L^2` norm of a convolution is the shape
that **Young/Hausdorff--Young, Cauchy--Schwarz on the convolution structure,
and the martingale/Efron--Stein decomposition all consume natively** -- for
instance `||S*S||_2 <= ||S||_1 ||S||_2` is immediate and gives exactly the
trivial bound (consistent with Lemma W), while any improvement of Young's
inequality on this group that uses the *conductor filtration* of the
convolution would give a genuine gain.  I flag this as the single most
promising *reformulation* to hand to the hypercontractivity workstream (01),
because the Efron--Stein/Witt grading is multiplicative under convolution in
the dual, which the `M_4` form hides.

### 2026-08-20T19:25 -- dead ends recorded honestly (things I looked for and did not find)

- **A named theorem bounding `sum_(chi_1 chi_2 chi_3 chi_4 = 1) prod c_(chi_i)`
  for a weighted family of characters.**  Two independent search passes
  (mine and a sub-agent's) found none.  Nearest named objects: Rudin's
  `Lambda(4)` constant (uniform over weights -- killed by Lemma W) and
  Shkredov's multiplicative energy of a spectrum, <https://arxiv.org/abs/1805.10468>
  (support is a *set*, count is unweighted).  Honest answer to that part of my
  charge: **no such machine exists**, confirming diary 09 independently.
- **"Small bias implies small fourth moment" as a stated theorem.**  Not
  found; only the two-step `epsilon`-bias -> `k`-wise-uniformity chain, whose
  loss is `sqrt(|G|^k) = 2^(2 ell)` at `k = 4` -- outside the `2^ell` budget.
- **Kerdock codes supporting 5-designs.**  My charge implied strong design
  properties; every source fetched says **3**-designs
  (<https://arxiv.org/pdf/1811.07725> Theorem 6.1;
  <https://errorcorrectionzoo.org/c/kerdock>).  The 4-design statement belongs
  to *Preparata* minimum-weight codewords.  "Kerdock has dual distance 6,
  hence OA strength 5" is derivable from the Preparata/Kerdock formal duality
  but **no fetched source states it**; recorded as DERIVED, not quoted.
- **Delsarte--Goethals dual distance / design strength.**  UNVERIFIED; the
  sources fetched give parameters but no design statement.
- **Vinogradov mean values over function fields as a lossy quadruple-counting
  tool.**  Liu--Wooley exists (Wooley, <https://arxiv.org/abs/1708.01220>,
  says verbatim the methods "are of sufficient flexibility to be applicable in
  algebraic number fields, and in function fields"), but I could not fetch a
  statement of the function-field theorem or its characteristic restriction,
  and the object counted (solutions of a Vinogradov system in a box) is again
  a *sparse subset of a UFD*, not a full-support weighted family in a group.
  Dropped for the same reason as the divisor-bound family (17:00 entry).
- **Restriction/extension theory over finite fields as a source of a
  fourth-moment bound.**  Closed by Lemma W, which is stronger and simpler
  than diary 09's `L^p`-deficit computation.
- **Global hypercontractivity (KLLM).**  Deliberately not pursued here: it is
  workstream `01-lit-hypercontractivity.md`'s subject and duplicating it would
  waste the shared budget.  Lemma W is an argument *for* that route (its
  hypothesis is on the function, not the support) and I hand it over.

## FINDINGS

### (a) Field map -- who owns which piece of this problem

Six communities have a claim on `(T-weak)`; only two of them have hypotheses
of the right *type*.

| Community | Object it controls | Hypothesis type | Verdict here |
|---|---|---|---|
| Finite-field restriction / Salem-set theory (Mockenhaupt--Tao, Iosevich--Koh, Lewko, Rudnev--Shkredov, Fraser) | `L^4` of a Fourier transform = additive energy | **support** of the set | **Closed by Lemma W** -- for a full-support family the best uniform constant *equals* the trivial bound |
| Additive combinatorics / energy of structured sets (Heath-Brown--Konyagin, Shkredov, MRSS, Kerr--Mohammadi--Shparlinski) | `E(A)` for subgroups, value sets, varieties | **support** | Same; also our "set" is everything |
| Sidon/`B_2`/`Lambda(p)` harmonic analysis (Rudin, Bourgain--Lewko, Lewko--Lewko) | `Lambda(4)` constants, Sidonicity | **uniform over weights** | Same; and Lewko--Lewko show weighted `!=` support, so the naming in diary 09 should be `Lambda(4)`, not "Sidon" |
| Analytic number theory, moments of primes in short intervals (Montgomery--Soundararajan, Parry) | `M_k` of `psi(x+h)-psi(x)` | the **specific** arithmetic function | Right type, but open at all five difficulty levels (18:10) |
| Function-field/geometric moments (Keating--Rudnick, Rodgers, Hast--Matei, Sawin, Sawin--Shusterman) | same, over `F_q[t]`, via Katz monodromy | the **specific** function + a **tameness** hypothesis `p > n` or large `q` | **Right type, and Hast--Matei `m=4` is within a constant of `(T-weak)`** (18:35); blocked exactly at `p = 2` |
| Coding theory / design theory (Delsarte, Pless, Kerdock--Preparata, `eps`-bias) | exact moments from dual distance / OA strength | the **specific family's dual code** | Right type; our wild subfield-restricted family has low dual distance, so it gives a *diagnostic*, not a proof |

**The single organizing fact:** `(T-weak)` is a statement about **one**
coefficient vector, and every technique whose hypothesis is about a *set* or
is *uniform over coefficient vectors* returns the trivial bound exactly
(Lemma W).  That is a complete, one-proof explanation of why four of the six
communities have nothing to offer, and it subsumes three separate "closed
route" findings of the sweep (restriction, PFR, `L^p` moments).

### (b) Where the state of the art actually stands on fourth moments of structured character/spectral families

Catalogue of every family I could verify where a fourth moment of the right
relative size is **unconditionally** known, with the mechanism:

| Family | Fourth-moment status | Mechanism | Fixed `q`? `q=2`? |
|---|---|---|---|
| Kloosterman sums `sum_(a in F_q^*) K(a)^4` | **EXACT**: `2p^3-3p^2-3p-1` (`p>=3`); `=1` at `p=2` | Salie's recursion: orthogonality -> count solutions of `sum a_j = 1 = sum a_j^(-1)`; one-step recursion | yes / yes (degenerate) |
| Kloosterman angles vs Sato--Tate | **asymptotic only**, error `O(n q^(-1/2))` (Katz GKM Thm 13.5.3) | monodromy + Weyl | no (`q -> infinity`) |
| Weil sums of binomials `W_(F,d)` | `P^(0..2)` exact and *universal*; **`P^(4) = |F|^2 sum_a M_a^2`** exact but equals the differential spectrum | fourth moment upstairs = **second** moment of a difference count | yes / yes |
| Steinhaus random multiplicative over `F_q[t]` | **EXACT**: `E|sum_(M_N) f|^4 = N q^(2N)(1-1/q) + q^(2N)` | orthogonality -> count `F_1F_2 = F_3F_4`; unique factorization / magic squares | yes / yes |
| Linear code with dual distance `>= 5` | **EXACT** = binomial | Pless power moment identity + Delsarte OA strength | yes / yes |
| Character sums over boxes mod `p` | asymptotic, classical | orthogonality -> `x_1x_2 = x_3x_4` count + divisor bound | yes |
| `psi(x+h)-psi(x)` over `Z` | **open**; best unconditional is the **third** moment on average, `h^(1+o(1))` (Parry 2024/26) | -- | -- |
| `Lambda` in short intervals over `F_q[t]` | **open** even for `q -> infinity`; only the variance is proved (Keating--Rudnick, Rodgers); Hast--Matei give `q^((h+1)(m-1))` for `m>2` **only if `p > n`** | Katz equidistribution / `S_n^m`-cohomology | no; `q=2` excluded |

Two readings of this table, both load-bearing:

1. **Every family with an unconditionally known fourth moment gets it by
   orthogonality-then-counting on a constraint set that is a *variety* or a
   *UFD*, never a group.**  Salie, Daniel Katz, the function-field random
   multiplicative theorem, and Ayyad--Cochrane--Zheng are all the same
   mechanism.  Our constraint `chi_1chi_2chi_3chi_4 = 1` lives in a group, so
   the count is structureless and all content is in the weights.
2. **In every such family, the observed kurtosis is at most a power of the
   logarithm of the family size** (Kloosterman: `-> 2`; random multiplicative
   over `F_q[t]`: `~N`; our measured: `2.81-2.99`).  `(T-weak)` allows
   kurtosis up to `2^(ell+2)/(3(ell-1)^2)`.  **No known structured family
   comes within an exponential factor of violating `(T-weak)`.**  That is
   evidence, not proof, but it is the right kind of evidence and it is new to
   the ledger.

### (c) The most transferable techniques, and exactly where each breaks

Ranked by expected value to this project.

1. **Hast--Matei's geometric higher-moment method, at `m = 4`.**
   <https://arxiv.org/abs/1604.02067>, Theorem 1.4.  Transfers *completely*:
   its conclusion at `m=4` is `(T-weak)` up to the constant (`C < 2` odd,
   `< 4` even), and the truth has `C ~ 1.5(ell-1)^2 2^(-ell)`.
   **Breaks at:** the hypothesis "`p > n` if `m > 2`" -- tame ramification.
   At `p = 2`, `n = 2ell+1` it fails for every `ell`.  Their own Remark 1.5
   names the missing input: the `S_n^m`-action on cohomology in uncomputed
   ranges.  *This is the same missing lemma as sweep route C (diary 06).*
2. **"Fourth moment upstairs = second moment of a difference count"**
   (Daniel J. Katz, Cor. 7.4, <https://arxiv.org/pdf/1805.10452>).
   Transfers as an exact identity -- written out here as **Identity C**,
   `M_4 = 2^(-3ell) ||S * S||_2^2`.  **Breaks at:** it converts, it does not
   bound; the resulting `L^2`-of-a-convolution still needs an inequality.
   But it is the right *shape* for the Efron--Stein/Witt grading, because
   the grading is multiplicative under convolution -- which is why I hand it
   to workstream 01.
3. **Design / orthogonal-array exactness** (Pless identity + Delsarte;
   <https://arxiv.org/pdf/0807.4671> Thm 13, <https://arxiv.org/html/2505.15032v1>
   Thm 4.1).  Transfers as the statement that dual distance `>= 5` gives the
   fourth moment exactly.  **Breaks at:** the wild subfield-restricted family
   has low dual distance (diary 07's `O(ell)` exactly-evaluable corner, all
   of it at low conductor).  Residual value: it names `(T-weak)` as an
   *approximate strength-4* condition with `2^ell/poly` tolerance, i.e. the
   weakest approximate-design hypothesis anyone would ever state.
4. **The Hankel-rank fixed-`q` method** (Yiasemides,
   <https://arxiv.org/abs/2110.05959>; Gorodetsky's thesis).  This is the
   **only** exact-moment technology I found that is native to fixed `q`
   including `q = 2` -- no Katz, no large-`q` limit; it reduces the moment to
   ranks of Hankel matrices over `F_q` by additive-character orthogonality.
   **Breaks at:** it currently computes the **second** moment of `d_2`, not a
   fourth moment and not primes; the author lists both extensions as
   undone.  Still, it is the only fixed-`q` mechanism in the field, and the
   lane's objects (Hayes classes = short intervals, `F_2` coefficient
   vectors) are exactly the setting it was built for.  I rate this the
   highest-value *unexplored* import.
5. **Salie-type orthogonality-then-recursion** (<https://arxiv.org/pdf/0807.4671>
   eq. (57)).  Transfers whenever the constraint set is a variety with a
   recursive structure.  **Breaks at:** our constraint is a group equation
   (17:00, PROVED), so there is no variety to count on.  Recorded so it is
   not re-proposed.

Techniques that do **not** transfer, with the reason in one line each:
restriction/Salem/energy-of-sets (Lemma W); `Lambda(4)`/Sidon theory (Lemma W);
slice rank / Croot--Lev--Pach (wrong output type; Costa--Dalai ceiling;
17:15); divisor-bound quadruple counting (group, not UFD; 17:00);
`epsilon`-bias XOR lemma (`2^(2ell)` loss vs `2^ell` budget; 18:55);
Vinogradov mean values in function fields (same UFD issue, plus unverified
characteristic restriction).

### (d) Precisely-stated `L2`-rung candidate inequalities, charter notation

Normalizations: `||D||_p^p = 2^(-ell) sum_e |D_e|^p`;
`M_p = sum_e |D_e|^p`; `S = Dhat`; `Sigma(ell) = sum_(j=2)^ell 2^(j-1)(j-1)^2`;
`(S*S)(chi) = sum_psi S_psi S_(chi psi^(-1))`; `n - ell = ell+1` (odd
endpoint) or `ell+2` (even).  Each is stated so that it is machine-falsifiable
on the existing CAS rows.

- **(C1) Trivial-improvement form.**
  `R_0 = 2^ell M_4 / M_2^2 <= 2^(ell + 2(n-ell)) / Sigma(ell)^2`,
  equivalently `||D||_4 <= 2^(ell/4) * (sqrt 2/(ell-1)) * ||D||_2` (odd),
  `... * (2/(ell-1)) * ...` (even).  **Status:** implies `(T-weak)` given the
  proved Weil envelope (Check B).  Measured truth `R_0 ~ 3`, so this has
  `2^ell/poly` margin.  **This is the form I recommend the ledger carry**,
  because it exhibits the target as a `poly(ell)` improvement of a trivial
  inequality rather than as a sharp moment asymptotic.
- **(C2) Hast--Matei constant form.**
  `2^(-ell) sum_e D_e^4 <= C * 2^(3(n-ell))` with `C < 2` (odd) / `C < 4`
  (even), uniformly in `ell`.  **Status:** equivalent to `(T-weak)`; it is
  Hast--Matei Theorem 1.4 at `m=4` with an absolute constant and without the
  hypothesis `p > n`.  Truth: `C ~ 1.5(ell-1)^2 2^(-ell)`.
- **(C3) Self-convolution form (Identity C).**
  `|| S * S ||_2^2 < 2^(3 ell + 4(n-ell))`.  **Status:** *equivalent* to
  `(T-weak)` (proved identity, no loss).  Its value is that it is an `L^2`
  statement about a convolution, so it composes with the Efron--Stein/Witt
  grading, which is multiplicative under convolution, and with any
  Young-type inequality refined by the conductor filtration.
- **(C4) Approximate strength-4 (design) form.**
  Define the strength-4 defect `T_4 := Q_4 - 3 P_2^2 = 2^(2ell) K_4` (using `P_2 = 2^ell M_2`, `Q_4 = 2^(3ell) M_4`).
  Then `(T-weak)` is `T_4 < 2^(3ell + 4(n-ell)) - 3 * 2^(2ell) M_2^2`.
  **Status:** a restatement, but it is the form in which a coding-theoretic
  or design-theoretic hypothesis would be consumed (Pless identity), and it
  makes explicit that we need only *approximate* strength 4 with tolerance
  `2^ell/poly(ell)` -- versus exact strength 4, which dual distance `>= 5`
  would give.
- **(C5) Graded self-convolution (the one I would test first).**
  With the Efron--Stein/Witt weight `w(chi) = sum_(i in supp chi) k_i`,
  `k_i = min{m : i 2^m > ell}`, and `S^(=w)` the restriction of `S` to weight
  `w`, `S * S = sum_(w_1, w_2) S^(=w_1) * S^(=w_2)`, and the weight of a
  product is *sub-additive* in this grading.  Candidate:
  `|| S^(=w_1) * S^(=w_2) ||_2 <= A^((w_1+w_2)/2) ||S^(=w_1)||_2 ||S^(=w_2)||_2 * 2^(-ell/2)`
  for an absolute `A`, which by Cauchy--Schwarz over the `<= ell^2` pairs
  gives `(T-weak)` whenever `A` is below the threshold set by the measured
  mass profile `f_w`.  **Status: OPEN, and the required `A` is exactly the
  quantity diary 09's experiment E1 measures.**  I record it because it is
  the `L^2`/convolution form of 09's route (b), and an `L^2` statement about
  a convolution is a strictly easier object than an `L^4` statement about a
  function.

### (e) Ranked references (all URLs fetched today; UNVERIFIED items flagged in the log)

1. **Hast, Matei**, *Higher moments of arithmetic functions in short
   intervals: a geometric perspective*, IMRN 2019 no. 21, 6554-6584,
   <https://arxiv.org/abs/1604.02067>.  Theorem 1.4 at `m=4` **is** `(T-weak)`
   up to an absolute constant; hypothesis `p > n` is the exact blocker.
2. **Hofmann, Hoganson, Menon, Verreault, Zaman**, *Moments of random
   multiplicative functions over function fields*, MPCPS 179 (2025) 785-819,
   <https://arxiv.org/abs/2408.08309>.  Theorem 1.3: an exact
   product-constrained fourth moment at every `q >= 2` and every `N`.
3. **Daniel J. Katz**, *Weil sums of binomials: properties, applications, and
   open problems*, <https://arxiv.org/abs/1805.10452>.  Corollary 7.4:
   fourth moment of a character family = second moment of a difference count.
4. **Yiasemides**, *The variance and correlations of the divisor function in
   `F_q[T]`, and Hankel matrices*, <https://arxiv.org/abs/2110.05959>.  The
   only fixed-`q` (incl. `q=2`) exact-moment machinery in the field.
5. **Mockenhaupt, Tao**, *Restriction and Kakeya phenomena for finite fields*,
   Duke Math. J. 121 (2004) 35-74, <https://arxiv.org/abs/math/0204234>.
   Lemma 5.1 is the canonical `L^(2k)`-equals-quadruple-count statement --
   and the canonical example of a support-only hypothesis (Lemma W).
6. **D. S. Kim**, <https://arxiv.org/pdf/0807.4671> (carries both Salie's
   exact Kloosterman moment recursion, eq. (57), and the Pless power moment
   identity, Thm 13) -- two of the five mechanisms in one fetched source.
7. **Sawin, Shusterman**, *On the Chowla and twin primes conjectures over
   `F_q[T]`*, Annals 196 (2022) 457-506, <https://arxiv.org/abs/1808.04001>.
   Theorem 1.1's hypothesis `q > 685090 p^2`, `p` odd, and Remark 1.10 --
   the sharpest available statement that characteristic 2 is the frontier.
8. **Keating, Rudnick**, <https://arxiv.org/abs/1204.0708> (Thm 2.1: `M_2` is
   their variance, `q -> infinity`) and **Rodgers**,
   <https://arxiv.org/abs/1609.02967> (Thm 3.1: variance only -- *not* higher
   moments, correcting a slight over-reading in diary 09).
9. **Montgomery, Soundararajan**, <https://arxiv.org/abs/math/0409258>, with
   **Parry**, <https://arxiv.org/abs/2409.00431> for the unconditional state
   of the art (third moment, `h^(1+o(1))`, on average over moduli).
10. **Costa, Dalai**, *A gap in the slice rank of `k`-tensors*,
    <https://arxiv.org/abs/1905.07355>; **Sauermann**,
    <https://arxiv.org/abs/2105.06863> -- the ceiling on the polynomial
    method, closing charge item 3.
11. **A. Lewko, M. Lewko**, *On the structure of sets of large doubling*,
    <https://arxiv.org/abs/1003.4561> -- `Lambda(4)` (weighted) `!=` `B_2[g]`
    (support); the correct classical name for diary 09's Translation 3.
12. **Alon, Goldreich, Hastad, Peralta**,
    <https://www.tau.ac.il/~nogaa/PDFS/aghp4.pdf> (Lemma 1: `eps`-bias ->
    `eps(2^k-1)^(1/2)` from `k`-wise independence) and **Jalan, Moshkovitz**,
    <https://arxiv.org/pdf/2105.01149v1> (the abelian-group XOR lemma,
    `eps sqrt(|G|^k)`).
13. **Katz**, *Gauss Sums, Kloosterman Sums, and Monodromy Groups*, Ann. Math.
    Studies 116, <https://web.math.princeton.edu/~nmk/Katz-GKM.pdf>.  Thm
    13.5.3 / Ex. 13.6: equidistribution with `O(n q^(-1/2))`, **not** exact
    moments; "Catalan" appears zero times in the book.
14. Supporting: Shkredov <https://arxiv.org/abs/1208.2344>,
    Murphy--Rudnev--Shkredov--Shteinikov <https://arxiv.org/abs/1712.00410>,
    Kerr--Mohammadi--Shparlinski <https://arxiv.org/abs/2306.10677>,
    Iosevich--Koh <https://arxiv.org/abs/0805.0814>,
    M. Lewko <https://arxiv.org/abs/1302.6664>,
    Rudnev--Shkredov <https://arxiv.org/abs/1803.11035>,
    Fraser <https://arxiv.org/abs/2407.08589>,
    Cheong et al. <https://arxiv.org/abs/2510.26364>,
    Shkredov <https://arxiv.org/abs/1805.10468>,
    Bourgain--Garaev--Konyagin--Shparlinski <https://arxiv.org/abs/1203.0017>,
    Sawin <https://arxiv.org/abs/1809.05137>,
    Gorodetsky <https://arxiv.org/abs/1810.00483>,
    Bank--Bary-Soroker--Rosenzweig <https://arxiv.org/abs/1302.0625>,
    Lin--Stufken <https://arxiv.org/html/2505.15032v1>,
    Ding--Mesnager--Tang--Xiong <https://arxiv.org/pdf/1811.07725>,
    Garcia--Todd <https://arxiv.org/pdf/1804.07397>,
    Thornburgh <https://arxiv.org/abs/2501.11184>.

### Epistemic ledger for this file

PROVED (self-contained arguments written out above): **Lemma W**
(weight-blindness, exact, unconditional); **Identity C**
(`M_4 = 2^(-3ell)||S*S||_2^2`); **Check B** (`(T-weak)` = beat the trivial
`(4,2)` inequality by `(ell-1)/sqrt2` odd, `(ell-1)/2` even, given the proved
Weil envelope); the group-vs-UFD obstruction closing divisor-bound quadruple
counting; the three-reason refutation of the slice-rank route; the
translation of Hast--Matei Thm 1.4 at `m=4` into `C < 2` / `C < 4`.
PROVED-BY-ARITHMETIC-ON-MEASURED-DATA (evidence, not theorem): **Check A**,
`M_4 = (3+o(1)) M_2^2 2^(-ell) ~ 12(ell-1)^2 2^(3ell)`, correcting diary 07's
`0.6 ell^3 2^(3ell)`.
VERIFIED LITERATURE (fetched, quoted): everything in (e), with the specific
UNVERIFIED flags recorded inline -- Montgomery--Soundararajan's exact
conditional `h`-range; Ayyad--Cochrane--Zheng's exact theorem statement;
Pless 1963 pagination; Kerdock dual distance 6 / OA strength 5 (derived, not
quoted); Delsarte--Goethals design strength; the Liu--Wooley function-field
Vinogradov statement and its characteristic restriction.
OPEN: (C5) and the value of `A`; whether the Hankel-rank method reaches a
fourth moment; whether `C_(4,n,h)` can be made absolute at `p = 2`.
NO THEOREM CREDIT is claimed for Lemire's conjecture or for `(T-weak)`.
