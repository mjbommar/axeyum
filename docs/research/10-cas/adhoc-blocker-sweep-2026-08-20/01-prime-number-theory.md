# Ad hoc blocker sweep, 2026-08-20 -- field 01: classical prime number theory

Agent: field specialist 01 (classical analytic number theory / the `Z`-analogue).
Scope: ad hoc research challenge, explicitly OUTSIDE the Axeyum roadmap, gates,
and fact-ledger credit rules.  Nothing here is theorem evidence.  Every claim is
labelled PROVED (with argument), REFUTED (with witness), or OPEN.

Working rule for this diary: finite computation is evidence, never a theorem;
every reference carries a URL and a sentence saying what it *actually* proves as
opposed to what would have been convenient.

---

## Entry 1 (start) -- orientation and the arithmetic of the blocker

Read, in the prescribed order:

- `docs/research/10-cas/lemire-review-2026-08-20-reaim.md`
- `docs/plan/status/52-gf2-lemire.md` (head; then grepped)
- `docs/research/10-cas/lemire-half-degree-irreducibles.md` (grepped: moments,
  cumulants, Katz, Linnik--Selberg, literature boundary)
- `docs/research/10-cas/lemire-proof-unblocking-bridges.md` (executive summary,
  random-matrix section, martingale section)

### 1.1 The exact arithmetic of the gap, recomputed from the lane's own objects

Notation as in the lane: `E_ell = (1+xF_2[x]/(x^(ell+1)))^*`, `|E_ell| = 2^ell`;
`n = 2ell+1` or `2ell+2`; `S_chi(n) = sum_{deg F = n} Lambda(F) chi(F)`;
`D_e = N_n(e) - 2^(n-ell)` the Mangoldt discrepancy in class `e`;
`M_r = sum_e |D_e|^r`.

Weil/RH over function fields gives, per character, `|S_chi(n)| <= (ell-1) 2^(n/2)`
(the `L`-polynomial has degree at most `ell-1`).  Fourier inversion gives

```text
D_e = 2^(-ell) sum_(chi != 1) conj(chi)(e) S_chi(n).
```

Triangle inequality over the `2^ell - 1` nontrivial characters:

```text
|D_1| <= 2^(-ell) * 2^ell * (ell-1) * 2^(n/2) = (ell-1) 2^(n/2) ~ ell * 2^ell,
```

against the target `|D_1| < 2^(n-ell) ~ 2^ell`.  That is the one-factor-of-`ell`
(= one factor of `log n`) blocker, reproduced.  PROVED (elementary, from the
lane's identities plus Weil).

### 1.2 What the truth should be, and what that rules out

Per-character heuristic (Haar `U(N)` with `N = deg L_chi ~ ell` and trace power
`n ~ 2ell > N`): `E|Tr Theta_chi^n|^2 = N ~ ell`, so the *typical* size of
`|S_chi(n)|` is `sqrt(ell) 2^(n/2)`, not `O(2^(n/2))`.

Consequence, and this is the sharpest thing I can say from my field before any
literature:

**OBSTRUCTION (PROVED, elementary).  No absolute-value / Hoelder / moment
argument over the character family can reach the target.**  For any `r >= 1`,

```text
|Delta| = |sum_(chi != 1) S_chi(n)|
        <= (2^ell)^(1-1/r) (sum_chi |S_chi|^r)^(1/r),
```

and if the family's `|S_chi| 2^(-n/2)` behave like a Gaussian of standard
deviation `sqrt(ell)` -- which the lane's own exact data support -- then
`(sum_chi |S_chi|^r)^(1/r) ~ c_r sqrt(ell) 2^(ell/r) 2^(n/2)` and every `r`
returns the *same* bound `~ sqrt(ell) 2^ell 2^(n/2) * 2^(-ell)` in normalized
terms, i.e. `sqrt(ell) * 2^ell`.  A factor `sqrt(ell)` short, for all `r`
simultaneously.  This is exactly the lane's measured "Hast--Matei idealized
second moment misses by `(ell-1)/2`" and "Cauchy across the top family loses
`304`/`633`": the loss is not slack in the estimate, it is the true first
absolute moment of the family.  Any proof must therefore use the SIGN of
`conj(chi)(1) S_chi(n)` across the family, i.e. genuine cancellation, not size.

### 1.3 The reason the lane's fourth-moment target escapes 1.2 -- and the
### resulting correct `Z`-twin

The lane's live target is *not* the character-family sum.  It is the SPATIAL
moment `M_4 = sum_e |D_e|^4` over the `2^ell` ray classes, used through
`max_e |D_e| <= M_4^(1/4)`.  That is a different mechanism and it is not blocked
by 1.2, because it converts an average over a large family into a pointwise
bound with exponential slack:

```text
truth      M_2 ~ ell 2^n,        M_4 ~ 3 M_2^2 2^(-ell) ~ ell^2 2^(3ell),
needed     M_4 <= 2^(4ell)   (so that M_4^(1/4) <= 2^ell),
slack      2^(4ell) / (ell^2 2^(3ell)) = 2^ell / ell^2.
```

So the fourth-moment route has a FULL FACTOR `2^ell` of room over the truth,
while the character-sum route has a deficit of `sqrt(ell)`.  Everything in my
field should therefore be aimed at the moment route, not at the pointwise route.

**This changes which `Z`-technology is the right twin.**  The brief's framing
("the `Z`-twin is primes in `[x, x+sqrt(x)]`, open even under RH, because there
is no averaging") is right about the *pointwise* route and about `n`, but there
IS an averaging variable here: the `2^ell` ray classes `e`.  The precise `Z`-twin
of the live target is therefore

> the fourth moment of primes in arithmetic progressions to ONE FIXED modulus
> `q ~ sqrt(x)`, i.e. `sum_(a mod q) |psi(x;q,a) - x/phi(q)|^4`, needed only to
> within a factor `q` of its conjectured size,

and NOT "a prime in `[x, x+sqrt(x)]`".  The Barban--Davenport--Halberstam /
Hooley / Friedlander--Goldston / Montgomery--Soundararajan moment literature is
the relevant body of `Z`-technology; the Cramer / Fourier-optimization
(Carneiro--Milinovich--Soundararajan) literature governs the *pointwise* route
and, as recorded below, is provably `log`-limited.

To be pinned down by literature search, in this order:
1. exactly what is known pointwise beyond RH (and whether the `log` loss is a
   proved limitation of the explicit-formula method rather than a gap);
2. the weakest pair-correlation-strength hypothesis known to give primes in
   `[x, x + sqrt(x) o(log x)]`, and whether that chain is pointwise or
   almost-all;
3. what is known for the variance and higher moments at a SINGLE fixed modulus
   `q ~ sqrt(x)` -- the actual twin.

---

## Entry 2 -- literature sweep, part 1: the pointwise route in `Z` and its
## proved `log`-limitation

All items below were fetched and read on 2026-08-20; PDFs were converted with
`pdftotext` and quoted from the actual text, not from memory.

### 2.1 Cramer's barrier and the Fourier-optimization school

- Carneiro, Milinovich, Soundararajan, **"Fourier optimization and prime gaps"**,
  Comment. Math. Helv. 94 (2019) 533-568,
  <https://arxiv.org/abs/1708.04122>.  ACTUALLY PROVES: under RH,
  `p_(n+1) - p_n < (22/25) sqrt(p_n) log p_n` for `p_n` large.  This is a
  CONSTANT improvement on Cramer's `RH => gap << sqrt(x) log x`; the `log x`
  itself is untouched.  The whole Fourier-optimization school (Bach; Ramare--
  Saouter; Dudek `4/pi`; Lamzouri--Li--Soundararajan; Carneiro--Milinovich--
  Quesada-Herrera--Ramos <https://arxiv.org/pdf/2404.08380>) optimizes the
  bandlimited kernel in the Guinand--Weil explicit formula.  Every one of them
  produces `c * sqrt(x) * log x`, differing only in `c`.

  VERDICT for this project: this is the direct analogue of the lane's
  `abs(Delta) <= C * ell * 2^ell` column.  Optimizing the kernel is exactly what
  the lane has already done with exact conductor weights, and in `Z` it is a
  hundred years of work that has never removed the `log`.  Do not spend lane time
  reproducing it.  OPEN in `Z`, and there is no reason to expect the analogue to
  behave differently over `F_2`.

### 2.2 What pair correlation buys POINTWISE in `Z` (this is small)

- Languasco, Perelli, Zaccagnini, **"An extension of the pair-correlation
  conjecture and applications"** (arXiv:1308.3934v3),
  <https://arxiv.org/abs/1308.3934>.  Read in full.  Verified statements:
  - Heath-Brown, Acta Arith. 41 (1982) 85-99, assuming RH and
    `F(x,T) = o(T log^2 T)` uniformly for `x^eps <= T <= x`, gets
    `Delta(x) = psi(x)-x = o(x^(1/2) log^2 x)`.  That is a `o(1)` saving on the
    RH bound, NOT a `log` saving.
  - Liu--Ye claim `Delta(x) = O(x^(1/2) log^(5/4) x)` from a quantitative
    Rudnick--Sarnak pair correlation.  LPZ state verbatim that [14] "contains
    several inaccuracies (in part detected by Goldston and Chan), hence the
    results are not reliable although the general strategy is clear."
    **Do not cite Liu--Ye as a proved `log`-saving.**
  - LPZ Theorem 3 quantifies the whole chain: under RH plus
    `F(x,T,tau) << T log T` for `U <= T <= Z = x^(1/2) log^2 x`,
    `Delta(x) << x^(1/2)(log^2 U + tau^(1/2) log^(3/2) x)`.  Getting
    `Delta(x) << x^(1/2) (log log log x)^2` (Montgomery's conjectural size)
    requires `U = log log x` -- pair correlation uniform down to
    `T = log log x`, an enormous strengthening.
  - LPZ Remark 5, verbatim in substance: "in view of the classical Omega-results
    ... there are definite limitations to the uniformity ranges of the bound
    `F(x,T,tau) << T log T`", citing Maier-type oscillation.  So the strongest
    forms of the hypothesis are known FALSE.
  - LPZ Theorem 2 (pointwise, all large `x`) under H(eta):
    `psi(x+h)-psi(x) = h + O(h^(2/3) x^(eta/3+eps))` for `x^(eta+5eps) <= h <= x^(1/2)`.
    Mechanism worth naming: the `h^(1/2) -> h^(2/3)` degradation is the price of
    the **inertia (monotonicity) upgrade** from a mean-square-in-`x` bound to a
    pointwise one.  `psi` is nondecreasing, so a deficiency at one `x` forces a
    deficiency on a whole neighbourhood, which an `L^2`-in-`x` bound then
    forbids.

  VERDICT: the classical pair-correlation chain gives pointwise savings of
  `o(1)` or `log^{small}` only, and its strong forms are Omega-obstructed.
  This IS the "one log short, and the log is hard" phenomenon, confirmed
  independently of the lane's own ledger.

### 2.3 The one place in `Z` where pair correlation beats RH by a POWER

- Kandhil, Languasco, Moree, **"Pair correlation of zeros of Dirichlet
  L-functions: a possible path towards the conjectures of Chowla,
  Elliott--Halberstam and Montgomery"**, Math. Ann. 394 (2026), art. 43,
  <https://arxiv.org/abs/2411.19762>.
- Kandhil, Languasco, Moree, **"Beyond the Riemann Hypothesis bounds: A
  pair-correlation approach to the least prime in arithmetic progression and the
  smallest quadratic non-residue"**, arXiv:2607.14515, submitted 16 Jul 2026,
  <https://arxiv.org/abs/2607.14515>.  Downloaded and read in full
  (`pdftotext`).

  This pair of papers is the sharpest `Z`-side answer to the brief's question
  (1), and it is much stronger than the classical chain.  Definitions, verbatim
  in substance:

  ```text
  G_(chi1,chi2)(x,T) = sum_(|gamma_j|<=T) x^(i(gamma_1-gamma_2)) W(gamma_1-gamma_2),
                       W(u) = 4/(4+u^2),  L(1/2+i gamma_j, chi_j) = 0,
  F_k(x,T;a)         = sum_(chi1,chi2 mod k) chi1(a) conj(chi2)(a) G_(chi1,chi2)(x,T),
  Sigma(x,T,v;k,a)   = sum_(chi mod k) conj(chi)(a) sum_(|gamma|<=T) x^(i gamma) e^(i v gamma).
  ```

  - TRIVIAL BOUND (their eq. after Lemma): `F_k^+(x,T) << T (phi(k) log(kT))^2`.
  - **PROVED under GRH** ([13, Theorem 2], quoted in 2607.14515 p.6):
    `F_k(x,T) << phi(k) T log x` uniformly for `1 <= k <= x^(1-eps)` and
    `sqrt(x) <= T <= exp(sqrt(x))`.  The paper states explicitly that
    "the reduction of the exponent of `phi(k)` from `2` to `1` ... was achieved
    by exploiting the **orthogonality of Dirichlet characters** in the definition
    of `F_k`."  That is a genuine, unconditional-modulo-GRH, family-cancellation
    theorem: a saving of `phi(k) log(kT)` over trivial.
  - HYPOTHESIS 2 (unproved) extends that bound, in a WEAKENED form
    `F_k(x,T) << phi(k) T exp(c1 (log x)^c2)`, `c2 in (1/2,1)`, down to
    `exp(c1 (log x)^c2) <= T < x` and for
    `exp(c1(log x)^c2) < k <= x exp(-2c1(log x)^c2)`.
  - THEOREM 4 (GRH + Hyp. 2): `psi(x;k,a) - x/phi(k) << sqrt(x/phi(k)) exp(c1(log x)^c2)`
    uniformly in that `k`-range and for EVERY `a` -- i.e. the Montgomery /
    Friedlander--Granville conjecture, at the square-root-of-the-mean scale.
  - THEOREM 5: `p(k) = max_a p(k,a) << phi(k) exp(B (log k)^A)`, `A in (1/2,1)`.
    That is `k^(1+o(1))`, a **power** improvement over the GRH bound
    `p(k,a) <= (phi(k) log k)^2` (Lamzouri--Li--Soundararajan 2015, Math. Comp.
    84, corrigendum 86; earlier Bach--Sorenson).
  - Their Lemma 11 [13, Lemma 6] is the transfer step:
    `|Sigma^+(x,T,0) - Sigma^+(x,U,0)| << sqrt(T max_(U<=t<=T) F_k^+(x,t))`.
    Cauchy--Schwarz from the pair correlation to the twisted exponential sum over
    zeros.  Lemma 12 is its mean-square-in-`x` companion,
    `int_x^(2x) |Sigma(t,T,0)|^2 dt << x F_k(x,T)`.

  So: the weakest pair-correlation-strength hypothesis currently known to give
  the AP-analogue is **Hypothesis 2 of arXiv:2607.14515** -- and it is weaker
  than the true pair-correlation conjecture by a factor
  `exp(c1(log x)^c2) / log x`, i.e. one is allowed to miss the truth by a
  quasi-polynomial factor and still win.  That is a very forgiving conditional
  chain and is the correct template for a translation.

### 2.4 The `Z`-side Omega-obstruction, and a computation showing it does NOT
### obstruct Lemire

- Friedlander, Granville, **"Limitations to the equi-distribution of primes I"**,
  Ann. of Math. 129 (1989) 363-382.  Granville (email, quoted in 2607.14515
  p.7): their results imply

  ```text
  max_a |psi(x;k,a) - x/phi(k)| >> u^(-u) x/phi(k),   where x/k = (log x)^u.
  ```

  Consequently the `k`-uniformity in Hypothesis 2 is SHARP: replacing
  `exp(c1(log x)^c2)` by `(log x)^A` for `k <= x (log x)^(-B)` is FALSE.

  TRANSFER COMPUTATION (mine, elementary; label: PROVED as an arithmetic
  statement about the dictionary, not about Lemire).  Dictionary at the Lemire
  odd endpoint: `x <-> 2^n`, `k <-> |x^(ell+1)| = 2^(ell+1)`,
  `log x <-> n = 2ell+1`, `x/k <-> 2^ell`, `x/phi(k) <-> 2^(n-ell) = 2^(ell+1)`.
  Then `(log x)^u = x/k` gives `u = ell ln 2 / ln(2ell)`, so

  ```text
  u ln u = (ell ln2 / ln(2ell)) (ln ell - ln ln(2ell) + ln ln 2)
         = ell ln 2 (1 - lnln ell/ln ell + O(1/ln ell)),
  u^(-u)  = 2^(-ell(1-o(1))),
  u^(-u) * x/phi(k) = 2^(o(ell)).
  ```

  So the Friedlander--Granville irregularity, transported to the Lemire endpoint,
  predicts only `max_e |D_e| >> 2^(o(ell))` -- **subexponential, far below both
  the random-matrix truth `sqrt(ell) 2^(ell/2)` and the target `2^ell`.**
  CONCLUSION: the only known `Z`-side Omega-obstruction to equidistribution of
  primes in progressions does NOT obstruct Lemire's conjecture.  Lemire lives at
  `u -> infinity` (`u ~ ell/log ell`), the regime where Maier / Erdos--Rankin /
  Friedlander--Granville irregularities are negligible; Maier's phenomenon lives
  at `u` bounded.  This is a genuinely new entry for the ledger: it says the
  conjecture is on the safe side of every known counterexample construction in
  the `Z` twin, which the lane's refutation-heavy ledger did not previously
  record.

### 2.5 A `Z`-side conjecture of exactly the lane's shape that is FALSE

- Fiorilli, Martin, **"Disproving Hooley's conjecture"**, JEMS,
  <https://ems.press/journals/jems/articles/8095586>; and
  **"Disproving a weaker form of Hooley's conjecture"**, arXiv:2407.01045,
  <https://arxiv.org/abs/2407.01045>.
  ACTUALLY PROVES: Hooley's conjectured uniform variance bound
  `V(x;q) = sum_(a mod q) |psi(x;q,a) - x/phi(q)|^2 << x log q`
  is FALSE; the counterexamples occur at `q asymptotic to log log x`, and the
  weaker dampened form `G_eta(x;q) << x log q` fails in the same range.

  RELEVANCE, and its limit: this is the exact `Z`-twin of the lane's uniform
  second-moment envelope, and it is false -- but false at `q` TINY compared with
  `x`, i.e. `u = log x / log q` astronomically large in the wrong direction.
  Lemire's regime is `q = |x^(ell+1)| ~ sqrt(x)`, at the opposite end.  So this
  is a WARNING about uniform-in-modulus envelopes, not a refutation of the
  lane's `M_2`/`M_4`/`K_4` candidates (which are stated only at the endpoints
  `n = 2ell+1, 2ell+2`).  Recorded as: any future lane conjecture of the form
  "envelope `E(ell,n)` for ALL `n`" must be checked at small `n/ell`, where the
  `Z`-twin of such an envelope is known false.

---

## Entry 3 -- the translation (charge 2): the exact finite-family analogue

### 3.1 Notation, and the blocker as an exponential sum over Frobenius angles

Fix `ell`, modulus `m = x^(ell+1)`, `E_ell = (1+xF_2[x])/(m)`, `|E_ell| = 2^ell`.
Each nontrivial Hayes character `chi` has a polynomial `L`-function of degree
`d_chi <= ell-1` with inverse roots `alpha_(chi,j) = sqrt(2) e^(i theta_(chi,j))`
(Weil, PROVED).  Collect the whole family's angles:

```text
Theta      = { theta_(chi,j) : chi != 1, 1 <= j <= d_chi },
Z(ell)     = |Theta| = sum_(chi != 1) d_chi  ~  (ell-1)(2^ell - 1),
Sigma(n)   = sum_(theta in Theta) e^(i n theta).
```

Then, exactly,

```text
Delta(ell,n) = 2^ell (N_n(1) - 2^(n-ell)) = -2^(n/2) Sigma(n),
```

and the Lemire endpoint statement is

```text
|Sigma(n)| < 2^(n/2)   at n = 2ell+1 and n = 2ell+2,
```

while Weil gives only `|Sigma(n)| <= Z(ell) ~ ell 2^ell`.  Needed at
`n = 2ell+1`: `|Sigma| < 2^(ell+1/2)`.  So:

> **SHARPEST REFORMULATION (charge (a)).  Lemire's endpoint is the statement
> that a `Z(ell)`-term exponential sum over the Frobenius angles of the whole
> Hayes family beats its trivial bound by a factor `~ ell/sqrt(2) = log_2(family
> size)/sqrt 2`.  Not square-root cancellation: one logarithm.**

The `Z`-object with exactly this shape is **Gonek's exponential sum over zeros**
`Sigma(X,T) = sum_(|gamma|<=T) X^(i gamma)`, i.e. the `tau = 0` endpoint of
Languasco--Perelli--Zaccagnini's extended pair correlation
(`F(X,T,0) = |Sigma(X,T)|^2`).  In `Z`, LPZ show H(0) is *equivalent* to
Gonek's conjecture in a range.  So the `Z`-twin of the Lemire blocker is not
"primes in `[x,x+sqrt x]`" (which is the pointwise/Cramer route) but
**Gonek's conjecture, needing only a log-saving instead of square-root
cancellation.**

### 3.2 The exact pair-correlation analogue, and why it collapses at one `n`

Montgomery's `F(x,T)` has TWO independent parameters: `x` (prime-side length)
and `T` (zero-side cutoff).  All of the `Z` technology -- Montgomery's own
theorem for `T >= x`, KLM's proved `F_k(x,T) << phi(k) T log x` for
`sqrt(x) <= T <= exp(sqrt x)`, Heath-Brown's and LPZ's chains -- exploits the
mismatch between the two.

In the function field the `L`-function is a POLYNOMIAL: the explicit formula is
exact and there is no truncation.  Writing the pair correlation with the trivial
weight,

```text
F_ell(n) = sum_(theta,theta' in Theta) e^(i n (theta - theta')) = |Sigma(n)|^2,
```

so at one fixed `n` the pair-correlation function **is** the square of the
quantity to be bounded.  **DECISIVE STRUCTURAL OBSTRUCTION (PROVED, elementary):
the `Z` pair-correlation method has no content at a single `n` over `F_2`,
because the second parameter `T` does not exist.**  This, and not any weakness of
the estimates, is why the `Z` technology does not port.

Two genuine substitutes for `T` exist, and they are the only two:

**(i) `n`-averaging (the Goldston--Montgomery / Selberg-integral form).**

```text
PC_ell(N) = (1/N) sum_(n=1)^N |Sigma(n)|^2
          = Z(ell) + sum_(theta != theta') K_N(theta - theta'),
```

`K_N` a Fejer-type kernel.  Diagonal `= Z(ell) ~ ell 2^ell`; the off-diagonal is
literally a spacing statistic of the family's angles.  "Montgomery's conjecture"
here reads `PC_ell(N) << ell 2^ell`, i.e. no clustering beyond a random unitary
spectrum, and it gives `|Sigma(n)| ~ sqrt(ell) 2^(ell/2)` for TYPICAL `n` --
astronomically inside the target.  But it is an almost-all statement.  This is
the exact `FF` twin of Selberg's almost-all short-interval theorem, and of the
fact that Goldston--Montgomery is an equivalence with a MEAN-SQUARE, never with
a pointwise bound.

**(ii) the exact-conductor filtration (the correct `T`-substitute).**  Let
`Theta_j` be the angles of characters of conductor level `<= j`,
`|Theta_j| ~ j 2^j`, `Sigma_j(n) = sum_(Theta_j) e^(i n theta)`.
Then `(n, j)` is a genuine two-parameter family and
`F_ell(n,j) := |Sigma_j(n)|^2` is the honest analogue of `F(x,T)`.
**DICTIONARY ENTRY: conductor level `j` is the function-field analogue of the
height cutoff `T`.  There is no analogue of "height".**  The lane's martingale
energies `E_j` are therefore, in `Z` language, the profile of `F(x,T)` in `T` --
which is exactly the object every `Z` pair-correlation hypothesis is about.

Elementary consequence, consistent with (and confirming) the lane's own
near-endpoint theorem: grouping levels `<= J` and using Weil levelwise gives
`|Sigma_(<=J)| <~ J 2^J`, so `J = ell - log_2(1.43 ell)` already fits half the
budget `1.41 * 2^ell`.  **The entire deficit lives in the top
`ceil(log_2 ell) + 1` conductor levels.**  (The review note states the same
thing as "every conductor level below `ell - ceil(log2 ell)` is discharged by
exact Fourier inversion plus the individual Weil bound"; I re-derived it
independently and the constants agree.)

### 3.3 Why the `Z` pointwise upgrade (inertia/monotonicity) has NO analogue

LPZ Theorem 2 upgrades a mean-square-in-`x` bound to a pointwise one using that
`psi` is nondecreasing: a deficiency at one `x` propagates to a neighbourhood,
which the `L^2` bound forbids; the price is `h^(1/2) -> h^(2/3)`.

**REFUTED as a transfer.**  In Lemire the modulus is tied to the degree
(`ell = ceil(n/2) - 1`), so the family whose angles appear in `Sigma(n)` CHANGES
with `n`.  There is no monotone quantity in `n` whose increments are the
`Sigma(n)` of one fixed family.  Averaging over `n` at fixed `ell` (route (i))
is available, but the conclusion "class `1` contains a prime of SOME degree
`<= N`" is not Lemire, which fixes `n`.  This is the precise mechanism behind
the brief's "no averaging over `n`", and it is the single reason the whole `Z`
pointwise machinery is unavailable.

### 3.4 What `K_4 <= M_2^2` is, in `Z` language -- and a decisive obstruction

`M_4 = sum_e |D_e|^4` is, after expanding the class condition, a FOUR-FOLD
correlation count.  With `deg F_i = n = 2ell+1` monic and
`F_i = F_1 mod x^(ell+1)`, we get `F_i = F_1 + x^(ell+1) G_i` with
`deg G_i <= ell-1`.  Hence

```text
sum_e N_e^4 = sum_(G_2,G_3,G_4 : deg <= ell-1)
                sum_(deg F = n) Lambda(F) Lambda(F+x^(ell+1)G_2)
                                Lambda(F+x^(ell+1)G_3) Lambda(F+x^(ell+1)G_4).
```

So `M_4` / `K_4` is exactly the function-field 4-tuple Hardy--Littlewood problem
with shifts in `x^(ell+1) F_2[x]`, at `q = 2`.  That is the precise twin of
Montgomery--Soundararajan, *Primes in short intervals*, CMP 252 (2004),
<https://arxiv.org/abs/math/0409258>, who derive Gaussian moments for
`psi(x+h)-psi(x)` from the `k`-tuple conjecture with a power-saving error, and of
Bui--Keating--Smith, JLMS 94 (2016), <https://arxiv.org/abs/1506.03741>, who
prove the pair-correlation/variance equivalence in the Selberg class precisely
"because the analogue of the Hardy-Littlewood conjecture ... is not available in
general".  At `q = 2` the FF `k`-tuple/Chowla input is open: Sawin--Shusterman
require `q` large.

**DECISIVE OBSTRUCTION (PROVED, arithmetic).  No majorant/sieve upper bound can
give the fourth-moment target.**  Uncentered, `C_r = sum_e N_e^r` with
`N_e ~ 2^(n-ell) = 2^(ell+1)`, so `C_4 ~ 2^ell 2^(4ell+4) = 2^(5ell+4)`, and
`M_4 = C_4 - 4 mu C_3 + 6 mu^2 C_2 - 3 mu^4 2^ell` is a signed combination of
terms of size `2^(5ell)` whose total is `~ ell^2 2^(3ell)`.  The required
relative precision is `2^(-2ell)`.  A Selberg/Brun majorant is accurate only to a
constant factor; an absolute-value bound on the terms is `2^(2ell)` too weak.
Hence the fourth-moment route requires an ASYMPTOTIC with power-saving error --
i.e. genuinely the `q=2` Hardy--Littlewood theorem -- and not any upper-bound
sieve.  This also explains, in one line, why the lane's successive
energy/gcd-strata/absolute-value attempts all land short: they are absolute-value
arguments on a problem that needs `2^(2ell)` of relative cancellation.

### 3.5 The one published mechanism that provably beats a FAMILY trivial bound

Kandhil--Languasco--Moree [13, Theorem 2]: under GRH,
`F_k(x,T) << phi(k) T log x` for `1 <= k <= x^(1-eps)`, `sqrt(x) <= T <= exp(sqrt x)`,
against the trivial `T (phi(k) log(kT))^2`.  The saving of `phi(k) log(kT)` comes
from **character orthogonality inside the definition of `F_k`** (their words).

Regime check, which is the honest part: their proof lives where the ZERO side is
long compared with the PRIME side (`T >= sqrt(x)`).  Translate: the Hayes family
has `Z(ell) ~ ell 2^ell` zeros in total, against a prime side of length
`2^n = 2^(2ell+1) = (2^ell)^2 * 2`.  So the FF endpoint has
`prime side ~ (zero side / ell)^2`: it is deep in the `T << x` regime, exactly
where `Z` must ASSUME (Hypothesis 2) rather than prove.  **The KLM theorem is
therefore in the wrong regime, but it is the only published family-orthogonality
saving of this shape and its proof is the one thing in the `Z` literature worth
auditing line by line for an `F_2` re-derivation.**

### 3.6 A warning about importing RMT/degree-one intuition

Bui--Keating--Smith (above) find that for Selberg-class `L`-functions of degree
`>= 2` the variance of prime sums in short intervals has **two qualitatively
different regimes**, versus one regime in the degree-one (zeta) case.  The Hayes
`L`-functions here have degree `d_chi <= ell-1`, i.e. degree GROWING.  So
Goldston--Montgomery-shaped intuition, which is degree-one, is not automatically
the right model for this family.  Recorded as a caution on any future
"the RMT prediction says ..." step in this lane.

---

## Entry 4 -- bounded computations (finite evidence, NOT theorems)

Both computations below are **independent Python implementations** written from
scratch in the session scratchpad, deliberately not using `axeyum-cas`, so that
they are a genuine second opinion on the lane's Rust results rather than a
re-run of them.  Every number below is finite evidence; none of it is theorem
credit.  Scratch path (ephemeral):
`/tmp/claude-1000/-home-mjbommar-projects-personal-axeyum/f980d106-.../scratchpad/{ffl.py,sigma.py}`.
The complete algorithm is reproduced below so the diary is self-contained.

Core primitives: `GF(2)[x]` polynomials as Python ints; Rabin irreducibility
(`x^(2^n) = x mod f` and `gcd(x^(2^(n/p)) - x, f) = 1` for each prime `p | n`).

**CONTROL (passed).** Brute-force count of irreducibles of degree `n` over the
whole space, `n = 1..12`, compared against Gauss's formula
`(1/n) sum_(d|n) mu(d) 2^(n/d)`.  Exact agreement for every `n`; the assertion
is in the script and the run printed
`CONTROL ok: brute-force irreducible counts match Gauss formula for n=1..12`.
Without this the irreducibility routine would be an unverified oracle.

### 4.1 The function-field Linnik profile: how tight is Lemire, really?

Motivation from my field: in `Z`, GRH gives `p(k,a) <= (phi(k) log k)^2 ~ k^2`
while Heath-Brown conjectures `p(k,a) << k (log k)^2 = k^(1+o(1))`.  The Lemire
endpoint is exactly `norm <= |q|^2` for `q = x^(ell+1)`.  So: where does the
least prime in the class actually sit?

Definition: `L(ell) = min { n : exists irreducible f in F_2[x], deg f = n,
f = 1 mod x^(ell+1) }`.  Enumeration: candidates are
`f = x^n + 1 + x^(ell+1) g`, `deg g <= n - ell - 2`, i.e. `2^(n-ell-1)` of them.

Command: `python3 ffl.py 60` (runtime well under the 5-minute budget; peak
memory a few MB).  Result (excerpt; full table in the run):

```text
ell   L(ell)   2ell+1   L-ell        ell   L(ell)   2ell+1   L-ell
  4        6        9       2         30       35       61       5
  8       11       17       3         40       45       81       5
 13       15       27       2         44       46       89       2
 20       22       41       2         49       57       99       8
 26       28       53       2         58       60      117       2
```

For every `1 <= ell <= 60`, `L(ell) - ell` lies in `[2, 8]` and tracks
`log_2(ell) + O(1)`.

**FINDING (finite evidence, `ell <= 60`).  The true least degree is
`ell + O(log ell)`, i.e. norm `|q|^(1+o(1))` -- exactly the Heath-Brown /
Chowla shape in `Z`, and exponentially below the Lemire threshold `2ell+1`.**
At the Lemire endpoint the expected number of irreducibles in the class is
`2^(ell+1)/(2ell+1) ~ 2^ell/ell`, while ONE is needed.

Consequence for the lane's strategy, and I think this is a genuinely new ledger
entry: **Lemire's conjecture is not an extremal statement about primes.  It is a
statement about where the square-root barrier sits.**  The threshold `n ~ 2ell`
is precisely the degree at which the Weil error `ell 2^(n/2)` first approaches
the main term `2^(n-ell)` (crossover at `n = 2ell + 2 log_2 ell`), and it has
nothing to do with the actual arrival of primes in the class, which happens at
`n ~ ell + log_2 ell`.  There is an exponential margin of truth
(`~ 2^ell/ell` primes available where `1` is needed); the entire difficulty is
methodological.  Two practical corollaries:
- any future route that would prove Lemire "just barely" is suspicious --
  the truth is not barely true;
- a route that gives up an exponential factor and still lands (e.g. proving
  `|Sigma(n)| <= 2^(0.9 ell)`) is still a complete proof, so exponential-loss
  arguments are NOT automatically disqualified.  The lane's ledger has
  repeatedly discarded routes for losing polynomial factors; it should not
  discard one for losing `2^(delta ell)` with `delta < 1/2` until the arithmetic
  is checked.

### 4.2 The `n`-profile of the family exponential sum, and whether the Lemire
### endpoint is anomalous

This measures the object of Entry 3.1 directly:
`Sigma(n) = -Delta(ell,n)/2^(n/2)`, computed from
`N_n(1) = n I_n(1) + sum_(k>=2, k|n) (n/k) * #{P irreducible, deg P = n/k,
P^k = 1 mod x^(ell+1)}` -- the proper prime powers are enumerated separately and
tested, not assumed away.

Command: `python3 sigma.py 6 8` then `python3 sigma.py 10`
(each well under budget; ell=10 enumerates `2^16` candidates).

```text
ell    RMS |Sigma| over n=ell+1..2ell+6     sqrt(ell 2^ell)    2^(n/2) needed at n=2ell+1
  6                15.8                          19.6                 90.5
  8                39.0                          45.3                362.0
 10                88.2                         101.2               1448.2

endpoint values:
 ell=6 : |Sigma(13)| =  35.4 (2.24 x RMS)   |Sigma(14)| = 15.5 (0.98 x RMS)
 ell=8 : |Sigma(17)| =  34.6 (0.89 x RMS)   |Sigma(18)| = 37.0 (0.95 x RMS)
 ell=10: |Sigma(21)| =  36.8 (0.42 x RMS)   |Sigma(22)| = 31.0 (0.35 x RMS)
```

Readings, all finite evidence:

1. `RMS_n |Sigma(n)|` matches `sqrt(Z(ell)) ~ sqrt(ell 2^ell)` to within
   `10-20%` at `ell = 6, 8, 10`.  That is the **diagonal term of the
   `n`-averaged pair correlation `PC_ell(N)` of Entry 3.2(i)**, measured: the
   off-diagonal (the angle-spacing contribution) is small compared with the
   diagonal.  In `Z` language: the Montgomery-shaped statement for this family
   is numerically true in the `n`-average.
2. **The Lemire endpoints are statistically ORDINARY in the `n`-profile**
   (ratios `0.35` to `2.24`, no drift).  There is no evidence of a conspiracy at
   `n ~ 2ell`.  This is worth having: it says the difficulty is not that the
   endpoint is an exceptional `n`, and it removes one class of hypothetical
   obstruction (a systematic resonance at `n = 2 deg(modulus)`).
3. The margin `2^(n/2) / RMS` is `5.7`, `9.3`, `16.4` at `ell = 6, 8, 10` --
   growing like `2^(ell/2)/sqrt(ell)`, as the RMT/square-root picture predicts.
   Consistent with 4.1: the truth has exponential room.
4. Largest observed `|Sigma(n)|` in these windows: `240.2` at `(ell,n)=(10,24)`,
   still `6x` under the `n=24` requirement `2^12 = 4096`.  No near-miss anywhere
   in the scanned range.

Neither 4.1 nor 4.2 is a proof of anything, and both are explicitly outside the
fact-ledger.

---

## Entry 5 -- primary-source check on the one `FF` theorem that would give `M_4`

Sawin, Shusterman, **"On the Chowla and twin primes conjectures over `F_q[T]`"**,
Ann. of Math. 196 (2022) 457-506, <https://arxiv.org/abs/1808.04001>.
Downloaded and read the statements (`pdftotext -f 1 -l 4`).  Verbatim
hypotheses:

- Theorem 1.1 (twin primes, quantitative): "For an odd prime number `p`, and a
  power `q` of `p` satisfying `q > 685090 p^2` ...".
- Theorem 1.3 (Chowla `k`-point correlations, uniform in shifts): "For an odd
  prime number `p`, an integer `k >= 1`, and a power `q` of `p` satisfying
  `q > p^2 k^2 e^2` ...".
- Theorem 1.4 (Burgess-type): "for a prime power `q > e^2/eta^2`".

So the only proved `FF` `k`-point correlation theorem is excluded at `q = 2`
twice over: `p` must be odd, and `q` must exceed `685090 p^2` (resp.
`p^2 k^2 e^2`).  Note also their stated mechanism -- "in odd characteristic,
this sign [of the Moebius function] is determined by the value of the
[discriminant]" -- is the odd-characteristic ancestor of the lane's already
proved characteristic-two Stickelberger--Swan / Arf identity
`mu(f) = (-1)^deg chi_8(Disc F)`.  That is a real point of contact, but the
`q`-size hypothesis is independent of the characteristic issue and is fatal on
its own.

CONCLUSION: the `k=4` Hardy--Littlewood input identified in Entry 3.4 as
equivalent to the lane's `M_4`/`K_4` target is OPEN at `q = 2`, and the one
published route to it is quantitatively excluded, not merely uninstantiated.

---

## FINDINGS

### (a) Sharpest reformulation of the blocker in my field

The blocker is **not** the twin of "primes in `[x, x+sqrt x]`".  Written in the
`Z` dictionary it is three statements, in increasing precision:

1. **Least-prime form.**  Lemire at level `ell` is exactly
   `p(q, 1) <= |q|^2` for the fixed modulus `q = x^(ell+1)` in `F_2[x]` -- the
   function-field Linnik problem at the GRH threshold.  In `Z` the GRH bound is
   `p(k,a) <= (phi(k) log k)^2` (Lamzouri--Li--Soundararajan 2015), i.e. `k^2`
   with two logs to spare, and removing those logs is open even on GRH.
   Lemire asks for the analogue with the logs already removed.
2. **Exponential-sum form (the sharpest).**  With `Theta` the multiset of all
   `Z(ell) ~ (ell-1)(2^ell-1)` Frobenius angles of the nontrivial Hayes
   characters and `Sigma(n) = sum_(theta in Theta) e^(i n theta)`, the endpoint
   is exactly `|Sigma(n)| < 2^(n/2)` at `n = 2ell+1, 2ell+2`, while Weil gives
   only `|Sigma(n)| <= Z(ell)`.  **The requirement is to beat the trivial bound
   on an exponential sum over zeros by one factor `log(family size)` -- not by a
   square root.**  The `Z` object of this exact shape is Gonek's conjecture on
   `sum_(|gamma|<=T) X^(i gamma)`; equivalently the `tau = 0` endpoint of the
   Languasco--Perelli--Zaccagnini extended pair correlation, where
   `F(X,T,0) = |Sigma(X,T)|^2`, and LPZ show their hypothesis H(0) is
   equivalent to Gonek's conjecture in a range.
3. **Moment form.**  The lane's live target `K_4 <= M_2^2` is exactly the
   function-field 4-tuple Hardy--Littlewood problem at `q=2` with shifts in
   `x^(ell+1)F_2[x]` (Entry 3.4), i.e. the twin of Montgomery--Soundararajan's
   moment programme.

An additional exact obstruction, proved in Entry 1.2 and worth stating because it
retires a whole family of attempts: **no Hoelder/moment/absolute-value argument
over the character family can ever reach the target**, for any exponent `r`,
because the true first absolute moment per character is `sqrt(ell) 2^(n/2)` and
`2^ell` characters of that size already overshoot by `sqrt(ell)`.  Only signed
cancellation across the family can work.  The lane's measured Cauchy losses
(`304`, `633`) and the Hast--Matei `(ell-1)/2` shortfalls are this phenomenon,
not slack.

### (b) Most promising transferable technique, with citations

**Character orthogonality inside the family pair-correlation function**
(Kandhil--Languasco--Moree, Math. Ann. 394 (2026) art. 43,
<https://arxiv.org/abs/2411.19762>, Theorem 2; used again in
<https://arxiv.org/abs/2607.14515>).  Under GRH they prove
`F_k(x,T) << phi(k) T log x` for `1 <= k <= x^(1-eps)` and
`sqrt(x) <= T <= exp(sqrt x)`, against the trivial `T(phi(k) log(kT))^2` -- a
saving of `phi(k) log(kT)`, obtained, in their words, "by exploiting the
orthogonality of Dirichlet characters in the definition of `F_k`".  It is the
only published theorem I found that provably beats the trivial bound for a
*family* pair correlation, and the transfer step is elementary Cauchy--Schwarz
(their Lemma 11/12).  Downstream in `Z` it yields
`psi(x;k,a) - x/phi(k) << sqrt(x/phi(k)) exp(c(log x)^c')` for EVERY `a`
(Theorem 4) and `p(k) << phi(k) exp(B (log k)^A)`, a power improvement over GRH
(Theorem 5).  Over `F_2` we need far less than what they already prove: a
`log`-saving where they get a square-root-of-family-size saving.

Honest caveat, stated as a regime check: their proof lives at `T >= sqrt(x)`
(zero side long relative to prime side), whereas the Lemire endpoint has
`prime side ~ (zero side/ell)^2` and therefore sits in the `T << x` regime where
`Z` must ASSUME (their Hypothesis 2).  So this is a technique to audit and try
to re-derive over `F_2`, not a theorem to import.

Secondary, and cheaper: **the Goldston--Montgomery / Selberg-integral
`n`-average** (Goldston--Montgomery 1987; Bui--Keating--Smith, JLMS 94 (2016),
<https://arxiv.org/abs/1506.03741>).  Its `FF` form `PC_ell(N)` is exactly
computable and I measured it (Entry 4.2): the diagonal is `Z(ell)` and the
off-diagonal is small.  It cannot close Lemire (almost-all only) but it is the
right place to formulate and test a Montgomery-type hypothesis for this family.

### (c) Decisive obstructions found

1. **No second parameter.**  The `Z` pair-correlation method needs the
   independent pair `(x, T)`.  Over `F_q` the `L`-function is a polynomial, the
   explicit formula is exact, `T` does not exist, and the pair-correlation
   function collapses to `|Sigma(n)|^2` -- the very quantity to be bounded.
   Entry 3.2.  This is why the transfer is structurally, not quantitatively,
   blocked.  The only honest substitute is the **exact-conductor level `j`**,
   which the lane already computes (its `E_j` martingale increments ARE the
   `Z` profile of `F(x,T)` in `T`).
2. **No inertia/monotonicity upgrade.**  Every `Z` route from a mean-square to a
   pointwise statement (LPZ Theorem 2, Heath-Brown) uses monotonicity of `psi` in
   `x`.  Lemire ties the modulus to `n`, so the family changes with `n` and no
   such monotone object exists.  Entry 3.3.  This is the precise content of "no
   averaging over `n`".
3. **Sieves/majorants cannot give the fourth moment.**  `M_4` is a signed
   combination of `C_2, C_3, C_4` of size `2^(5ell)` whose total is
   `ell^2 2^(3ell)`; the needed relative precision is `2^(-2ell)`.  Any
   constant-factor majorant, and any absolute-value bound on the pieces, is
   `2^(2ell)` short.  Entry 3.4.  This retires the entire class of "bound the
   energy" attempts in one line and explains the lane's repeated near-misses.
4. **The only `FF` `k`-point correlation theorem is quantitatively excluded at
   `q=2`**: Sawin--Shusterman need `p` odd and `q > 685090 p^2` (Thm 1.1),
   `q > p^2k^2e^2` (Thm 1.3).  Entry 5.
5. **Moments cannot beat the family first absolute moment.**  Entry 1.2.
6. `Z`-side `Omega`-obstructions do NOT obstruct Lemire.  Transporting
   Friedlander--Granville's `max_a |error| >> u^(-u) x/phi(k)` to the endpoint
   gives only `max_e |D_e| >> 2^(o(ell))` (Entry 2.4), and Hooley's disproved
   variance conjecture fails at `q ~ log log x`, the opposite regime (Entry 2.5).
   Negative-of-a-negative: the conjecture is on the safe side of every known
   counterexample construction in the `Z` twin.

### (d) Concrete next experiments runnable in this repo

1. **Endpoint-vs-`n`-profile at the lane's real sizes.**  Extend Entry 4.2 to
   `ell = 12..20` with `axeyum-cas` (the class-population transform already
   exists; only the hard-coded `for degree in [2*ell+1, 2*ell+2]` in
   `crates/axeyum-cas/src/bin/axeyum-gf2-hayes-distribution.rs` restricts it to
   the endpoints).  Record `|Sigma(n)|` for `n = ell+1 .. 3ell`, its RMS, and the
   endpoint percentile.  Decides whether the endpoint stays statistically
   ordinary at scale, and gives the first measured `PC_ell(N)` off-diagonal.
   Cost: comparable to existing endpoint runs times the number of degrees.
2. **The `FF` Linnik profile `L(ell)` to `ell ~ 200`** with the Rust search
   binary (`axeyum-gf2-search`).  Cheap (`2^(L-ell) ~ 2^10` candidates per
   `ell`).  If `L(ell) - ell` stays `O(log ell)` to `ell = 200`, that is a strong,
   independently checkable statement about how much room the conjecture has, and
   it is exactly the data an outside expert asked to evaluate the reduction would
   want first.
3. **Levelwise `|Sigma_j(n)|` at the endpoint** (Entry 3.2(ii)): the exact
   conductor filtration is already implemented
   (`fourth_moment_conductor_decomposition`, `axeyum-gf2-hayes-fourth-filtration`).
   Compute the SIGNED levelwise partial sums `Sigma_j(2ell+1)`, not just the
   energies `E_j`, and check numerically whether `|Sigma_j| <= c 2^j` holds
   levelwise (the sufficient condition of Entry 3.2).  This is the direct `FF`
   analogue of "measure `F(x,T)` as a function of `T`", it is the shape of every
   `Z` pair-correlation hypothesis, and to my reading the lane currently records
   only the unsigned energies at that filtration.
4. **Audit KLM's orthogonality lemma over `F_2`.**  Read
   <https://arxiv.org/abs/2411.19762> Theorem 2 and its Lemmas 6-8 at equation
   level and write down what the `F_2` re-derivation would need; the deliverable
   is either an `F_2` lemma or an exact statement of the missing input.  Same
   discipline the lane applied to Bagshaw and to Linnik--Selberg.

### (e) New to the project's ledger

- **The `Z`-twin was mis-identified.**  The live target is a family-averaged
  moment at ONE fixed modulus `q ~ sqrt(x)` (Barban--Davenport--Halberstam /
  Hooley / Montgomery--Soundararajan territory), plus a least-prime-in-an-AP
  statement at the GRH threshold -- not "primes in `[x, x+sqrt x]`".  The
  Cramer / Fourier-optimization literature (Carneiro--Milinovich--Soundararajan,
  `22/25`) governs a route the lane should NOT invest in: a century of that work
  has only ever moved the constant in `c sqrt(x) log x`.
- **Lemire is not tight** (Entry 4.1): the least prime in the class arrives at
  degree `ell + O(log ell)`, not `2ell+1`; there are `~2^ell/ell` primes
  available where one is needed.  The endpoint is where the square-root barrier
  is, not where the primes are.  Corollary for route selection: an argument that
  loses an exponential factor `2^(delta ell)` with `delta < 1/2` can still be a
  complete proof, so such routes should not be discarded by reflex.
- **Absolute-value/moment arguments over the character family are provably
  incapable of reaching the target** (Entry 1.2), for every exponent
  simultaneously.  This is a single statement covering the Cauchy `304`/`633`
  losses, the Hast--Matei `(ell-1)/2` and `(ell-1)/4` shortfalls, and the
  Hoelder energy columns.
- **`K_4 <= M_2^2` is a 4-tuple Hardy--Littlewood statement at `q=2`**, and
  therefore cannot be reached by any majorant/sieve, because the needed relative
  precision is `2^(-2ell)` (Entry 3.4).  The one published `FF` route
  (Sawin--Shusterman) is excluded by an explicit `q > 685090 p^2` and `p` odd.
- **Dictionary entry: exact-conductor level = pair-correlation height cutoff.**
  The lane's `E_j` martingale is, in `Z` language, the `T`-profile of `F(x,T)`.
  This makes every `Z` pair-correlation hypothesis directly translatable, and it
  identifies the signed levelwise partial sums `Sigma_j(n)` (not the unsigned
  energies) as the object to measure.
- **The `Z` `Omega`-obstructions transport harmlessly** (Entry 2.4/2.5), which
  the lane's ledger did not previously record.
- **A `Z`-side conditional chain much more forgiving than the lane assumes
  exists**: Kandhil--Languasco--Moree get a POWER improvement over GRH for the
  least prime in an AP from a pair-correlation hypothesis that is allowed to miss
  the truth by `exp(c(log x)^c')`.  If an `F_2` analogue of their orthogonality
  saving can be found, the endpoint has enormous room.

### Verdict on charge (3)

**Mostly dead on arrival, for a structural reason, with one specific
exception.**  The `Z` pair-correlation technology is a two-parameter method
(`x` against `T`) and every step of it -- Montgomery's own theorem, Heath-Brown,
Goldston--Montgomery, LPZ, KLM -- exploits that second parameter, then upgrades
mean-square to pointwise using monotonicity of `psi`.  Over `F_2` at fixed `n`
both resources are absent: the `L`-functions are polynomials so there is no
height cutoff, and the modulus is tied to `n` so there is no monotone object.
What survives is (i) the conductor filtration as a `T`-substitute, which the lane
already has and which localizes the deficit to the top `~log_2 ell` levels
without closing it, and (ii) the KLM character-orthogonality saving, which is in
the wrong regime but is the only published family-cancellation theorem of the
right shape and is worth an equation-level `F_2` audit.

The specific formulation that becomes tractable at fixed `q = 2` is not a
variance or pair-correlation statement at all.  It is that `Sigma(n)` is a
RATIONAL INTEGER: `Delta(ell,n) = -2^(n/2) Sigma(n)` is integral, the eigenvalues
are Weil numbers, and there is no `Z` analogue of that at all.  My field says the
analytic side is a century-old wall in both worlds; the arithmetic side (the
2-adic valuation route, "Move 1" of the review note) is the only place where the
function field has a resource that `Z` lacks.  Entry 4.1 supports investing
there: the conjecture has exponential room, so it does not need a sharp analytic
estimate -- it needs one exact algebraic non-vanishing.
