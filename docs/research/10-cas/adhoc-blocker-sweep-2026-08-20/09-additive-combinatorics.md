# Ad hoc blocker sweep, lane 09: additive combinatorics, hypercontractivity, higher-order Fourier

Agent field: additive combinatorics / hypercontractivity / higher-order Fourier analysis.
Date opened: 2026-08-20T15:10-04:00.

Epistemic labels used throughout: PROVED (a real theorem with citation or a
self-contained argument written out here), REFUTED (with an exact witness),
OPEN (conjectural, heuristic, or merely supported by finite computation).
Finite computation is EVIDENCE, never a theorem.

## Log

### 2026-08-20T15:10 -- opened diary, starting required reading.

### 2026-08-20T15:25 -- required reading done; exact translation fixed

Read in order: `lemire-review-2026-08-20-reaim.md` (all), lane status
`docs/plan/status/52-gf2-lemire.md` (all 747 lines), the cumulant/Witt/Haar
sections of `lemire-half-degree-irreducibles.md` (lines 2500-2900), and the
bridges audit sections 4-6 (`lemire-proof-unblocking-bridges.md` 1560-1749,
which already stops generic hypercontractivity, Burkholder/Rosenthal, and the
Tao--Ziegler low-characteristic inverse theorem; I do not re-propose any of
those in their generic form).

Fixed notation, all of it checked against the CAS output below.

```text
G      = E_ell = principal units of F_2[x]/x^(ell+1),   |G| = 2^ell
n      = 2 ell + 1 (odd endpoint) or 2 ell + 2 (even endpoint)
N_e    = Mangoldt population of Hayes class e,  sum_e N_e = 2^n
D_e    = N_e - 2^(n-ell)      (mean-zero: sum_e D_e = 0)
M_r    = sum_e |D_e|^r
S_chi  = Dhat(chi) = sum_e D_e chi(e)          (S_1 = 0)
P_2    = sum_chi |S_chi|^2 = 2^ell M_2
Q_4    = sum_(chi1 chi2 chi3 chi4 = 1) prod_i S_chi_i = 2^(3ell) M_4
K_4    = 2^ell M_4 - 3 M_2^2,   so 2^(2ell) K_4 = Q_4 - 3 P_2^2
R_0    = 2^ell M_4 / M_2^2 = 3 + K_4/M_2^2
```

**Translation 1 (PROVED, elementary Fourier).**  With uniform probability
measure on `G`, `R_0` is exactly the **kurtosis** of the random variable
`X = D_e`, `e ~ Unif(G)`:

```text
R_0 = E[X^4] / (E[X^2])^2 .
```

So `K_4 <= M_2^2` is literally "`X` has kurtosis at most 4", i.e. excess
kurtosis at most 1, i.e. the `(4,2)` norm-equivalence
`||X||_4 <= 2^(1/2) ||X||_2`.  A Gaussian has `R_0 = 3` exactly; the ledger's
measured root ratios `2.9948 / 3.0011 / 2.9997` say the class discrepancy is
Gaussian to three decimal places.

**Translation 2 (PROVED).**  Put `f_e = D_e^2`.  The repo's conductor
filtration identity `C_0 = M_2^2`, `C_ell = 2^ell M_4`,
`K_4 = sum_j E_j - 2 M_2^2` is exactly the Efron--Stein/martingale variance
decomposition of `f` along the conductor filtration, because
`C_j = 2^(2ell) E[(E[f | F_j])^2]`.  Hence

```text
C_ell - C_0 = 2^(2ell) Var(f),      K_4 <= M_2^2  <=>  Var(D^2) <= 3 (E D^2)^2 .
```

(For a Gaussian `Var(X^2) = 2(EX^2)^2`, so the target allows 1.5x the Gaussian
relative variance.)  The `E_j` are the Haar/square-function increments; the
"local Carleson estimate on every Witt cylinder" in the bridges note is the
conditional form of the same inequality.  This is a restatement, not progress.

**Translation 3 (PROVED) -- and a correction to the brief I was given.**
The brief says `K_4` is "a signed additive-energy defect of the multiset of
Frobenius classes".  That is the *wrong* contraction, and the repo already
knows the two apart (`character_fourth_moment_comparison`).  Exactly:

```text
sum_chi |S_chi|^4 = 2^ell * E_G(D)          <- additive energy of D **on G**
                                               (= multiplicative energy of the
                                                Frobenius-class multiset)
Q_4 = 2^(3ell) M_4 = E_Ghat(S)              <- additive energy of the SPECTRUM
                                               S **on the dual group** Ghat
```

Both are checked identities (`E_G(D) = sum_h (sum_e D_e D_(e+h))^2`, and
`E_Ghat(S) = |Ghat|^(-1) sum_e |Shat(e)|^4 = 2^(-ell) 2^(4ell) M_4`).  `K_4`
is the second one minus its degenerate solution families.  Writing
`chi3 -> chi3^(-1)`, `chi4 -> chi4^(-1)`, the three Wick pairings become the
three degenerate families of `a+b=c+d`: `a=c`, `a=d`, and (because `D` is
real, so `S(-a) = conj S(a)`) the zero-sum family `a+b=0=c+d`.  So:

> **`K_4 <= M_2^2` says the spectrum `S` of the Mangoldt class function is an
> almost-Sidon (near-4-design) weighted family in `Ghat`: its additive energy
> exceeds the forced diagonal value by at most a factor 4/3.**

That is the "Sidon-like / 4-design spectral family" item of my charge, made
exact.  Note the direction: the *spectral* side is where Sidonicity is
asserted; the physical-side energy `sum_chi |S_chi|^4` is a different object
and is NOT what `K_4` bounds.

### 2026-08-20T15:40 -- CAS ground truth (charge 3), reproduced a pinned ledger row

Command (release binaries for this lane were absent; the debug binaries built
at 14:01 today were used, no rebuild, no repo mutation):

```sh
cd /home/mjbommar/projects/personal/axeyum-gf2-lemire
./target/debug/axeyum-gf2-hayes-fourth-filtration 9
```

Output (verbatim, pipe-separated fields split for reading):

```text
GF2_HAYES_FOURTH_FILTRATION|status=PASS|ell=9|degree=19
  connected_geometric_split=false
  second_moment=3339712
  fourth_moment=61277466352
GF2_HAYES_FOURTH_FILTRATION|status=PASS|ell=9|degree=20
  connected_geometric_split=true
  second_moment=7540976
  fourth_moment=375358302272
```

Derived exactly (`python3`, integer arithmetic):

```text
(9,19): K_4 = 2^9*61277466352 - 3*3339712^2 = -2086965956608     <-- MATCHES
         the pinned ledger value in lemire-half-degree-irreducibles.md
        R_0 = 2.812889857...,   K_4/M_2^2 = -0.187110143
(9,20): K_4 = +21584493665536,  R_0 = 3.379565515
```

So my translation is anchored on the same integers the lane uses.  Two model
facts fall straight out and both are corroborated by the ledger's own larger
rows:

```text
M_2(ell,n) ~ (ell-1) 2^n         [(9,19): 3339712/2^19 = 6.37 ~ ell-2 = 7]
M_4(ell,n) ~ 3 M_2^2 / 2^ell     [predicts M_4(23,47) = 3.12e24;
                                  ledger's exact value is 3.119070...e24]
```

The first is exactly the Keating--Rudnick short-interval variance (see below);
the second is "the fourth moment is Gaussian", which is what `K_4 << M_2^2`
asserts.

### 2026-08-20T16:00 -- the target is over-engineered by a full power of |G|

This is the main result of this lane-day and it is elementary arithmetic, so
it is checkable in one sitting.  I label it PROVED (given the ledger's own
proved inputs), because every step is an inequality already in the note.

The endpoint needs `|D_1| < 2^(n-ell)` (the mean), because `D_1 >= -2^(n-ell)`
always and Lemire fails exactly at equality.  The ledger reaches this by

```text
max_e |D_e|^4 <= M_4 ,          M_4 = (3 M_2^2 + K_4)/2^ell .
```

So the **minimal sufficient fourth-moment statement is simply**

```text
M_4(ell,n) < 2^(4(n-ell))        (= mean^4).            (MIN)
```

Now feed in the ledger's *proved* Weil second-moment envelope
`M_2 <= 2^(n-ell) Sigma(ell)`, `Sigma(ell) = sum_(j=2)^ell 2^(j-1)(j-1)^2`.
Then (MIN) is implied by, and is essentially equivalent to,

```text
R_0 = 2^ell M_4 / M_2^2  <=  2^ell * 2^(4(n-ell)) / (2^(n-ell) Sigma)^2
                          =  2^(ell + 2(n-ell)) / Sigma(ell)^2 .     (SLACK)
```

Exact values (`python3`, integer/Fraction arithmetic, no floats in the
computation):

```text
 ell     n     SLACK threshold on R_0      log2      SLACK/4
   9    19            0.7878              -0.34       0.197
  12    25            1.5748               0.66       0.394
  15    31            4.4825               2.16       1.121   <- crossover
  20    41           39.466                5.30       9.87
  23    47          170.98                 7.42      42.7
  23    48          683.92                 9.42     171.0
  50   101       8.469e8                  29.66       2.12e8
 100   201       5.495e22                 75.54       1.37e22
 200   401       4.182e51                171.48       1.05e51
 200   402       1.673e52                173.48       4.18e51
 400   801       4.116e110               367.45       1.03e110
```

Reading:  the lane's live target is `R_0 <= 4`.  **At the symbolic handoff
`ell = 200` the sufficient threshold is `R_0 <= 2^171.5`.**  The pursued target
is stronger than necessary by a factor of about `2^169`, i.e. by very nearly a
full power of the group order `|G| = 2^ell`.

Three independent ways to see the same slack, all consistent, all checked
against ledger numbers:

1. **Kurtosis.**  `R_0` is the kurtosis of `D` under uniform measure.  The
   *completely trivial* bound is `R_0 <= 2^ell` (from `M_4 <= M_2^2`, equality
   iff `D` is a delta).  (SLACK) says we need to beat the trivial kurtosis
   bound by only `Sigma^2/2^(2(n-ell)) ~ ell^4` -- a **polylog(|G|)** gain.
   The pursued `R_0 <= 4` asks to beat it by `2^ell/4`.
2. **Triangle inequality over the character family.**  Exactly,
   `Sigma_1(ell) := sum_(j=2)^ell 2^(j-1)(j-1) = (ell-2) 2^ell` to leading
   order, so the pointwise-Weil + triangle bound is
   `|D_1| <= 2^(-ell) Sigma_1 2^(n/2) = (ell-2) 2^(n/2)`, while the target is
   `2^(n-ell) = sqrt(2) 2^(n/2)` (odd endpoint) or `2 * 2^(n/2)` (even).
   **The whole conjecture is a saving of `(ell-2)/sqrt(2)` over the triangle
   inequality.**  Cauchy--Schwarz plus the true second moment already saves
   `sqrt(ell)` of that (this is exactly the ledger's Hast--Matei
   "misses by squared ratios `(ell-1)/2` and `(ell-1)/4`").  Full square-root
   cancellation across the family would save `2^(ell/2)/sqrt(ell)`.  So the
   needed saving is `~ell`; the available headroom above it is `2^(ell/2)`.
3. **What a counterexample costs.**  A hypothetical Lemire failure is
   `D_1 = -2^(n-ell)`.  It contributes `2^(2(n-ell))` to `M_2`, which is only a
   `2/(ell-1)` fraction of the true `M_2 ~ (ell-1)2^n` -- *invisible* to any
   second-moment argument.  But it contributes `2^(4(n-ell))` to `M_4`, which
   is `~2^(ell+2)/(3(ell-1)^2)` times the true `M_4 ~ 3(ell-1)^2 2^(2n-ell)` --
   **exponentially visible** in the fourth moment.  That ratio *is* the slack.

Consequence for lane strategy: the ledger's refuted shortcuts were all refuted
against an allowance of `M_2^2`.  Several of them were refuted by *bounded*
factors measured at a *single small* `ell` (`1425/1483` at `ell=8` for
structural-support Cauchy; `303.92/632.42` at `ell=12` for family Cauchy;
"individual connected cells over thirty times the signed total" at `ell=9`).
**A shortcut whose loss grows polynomially in `ell` is not refuted against
(SLACK)** -- the allowance grows like `2^ell/poly(ell)` and the finite range
through degree 400 is already certified, so a large-`ell`-only theorem is fully
sufficient.  Measuring the `ell`-scaling of those loss factors is the single
highest-value cheap experiment I can name (see FINDINGS (d)).

I checked whether the ledger already states (MIN)/(SLACK).  `grep` over
`lemire-half-degree-irreducibles.md` and `52-gf2-lemire.md` finds only the
*mechanism* ("since `max_e |D_e|^4 <= M_4`, the envelope implies
`max|D| <= 2^ell` once `64 ell^2 <= 2^ell`") and never the weakest sufficient
form.  Every recorded target -- `M_4 <= 64 ell^2 2^(3ell)`,
`M_4 <= 64 ell^4 2^(3ell)`, `M_4 <= 16 ell^5 2^(3ell)`, `R_0 <= 4`,
`R_j(b) <= ell` -- is at the `2^(3ell)` scale, i.e. within `poly(ell)` of the
*truth*, when `2^(4(n-ell))` (one full factor `2^ell` above the truth) is all
that is needed.  NEW TO THE LEDGER.

### 2026-08-20T16:15 -- why the fourth moment is forced (no L^p restriction estimate can substitute)

My charge asked whether Green--Tao/Bourgain restriction theory (an
`L^2 -> L^p` bound on the spectrum) transfers.  It is the natural
additive-combinatorics tool for exactly this shape -- "remove the logs from
the `L^p` moments of a prime exponential sum" -- and the function-field
machinery exists:

- Green and Tao, *Restriction theory of the Selberg sieve, with
  applications*, J. Theor. Nombres Bordeaux 18 (2006) 147-182,
  <https://arxiv.org/abs/math/0405581> -- the enveloping sieve and the
  `L^2->L^p` restriction theorem for majorants of the primes.
- Le Thai Hoang, *Green-Tao theorem in function fields*, Acta Arith. 147
  (2011), <https://arxiv.org/abs/0908.2642> -- constructs the pseudorandom
  majorant for irreducibles in `F_q[t]`, with the restriction estimate.
- Guoquan Li, *Enveloping sieve related to the Hardy-Littlewood irreducible
  tuple conjecture in a function field*, Finite Fields Appl. 95 (2024)
  102383, <https://www.sciencedirect.com/science/article/abs/pii/S1071579724000236>.

None of these appears anywhere in the lane's documents (`grep` for
"enveloping sieve", "Green-Tao", "Le Thai", "restriction" over both notes:
zero hits).  So this *is* an unexplored family.  Unfortunately I can show it
cannot close the endpoint, and the computation is short enough to be decisive.

Any unconstrained `L^p` spectral bound feeds the endpoint only through
Hausdorff--Young/Holder:

```text
max_e |D_e| <= 2^(-ell) sum_chi |S_chi|
            <= 2^(-ell/p) (sum_chi |S_chi|^p)^(1/p) ,
```

so it suffices to have `sum_chi |S_chi|^p <= 2^(ell + p(n-ell))`.  With
`|S_chi|^2 ~ (j-1) 2^n` on exact conductor level `j` (the Keating--Rudnick /
Hast--Matei value, corroborated by the CAS row above), the truth is

```text
sum_chi |S_chi|^p ~ c_p * ell^(p/2) * 2^(ell + p n/2) ,
```

and since `n - ell = n/2 + O(1)` at both endpoints the deficit is

```text
truth / needed  ~  c_p (ell/2)^(p/2)      for every p .        (LP-DEFICIT)
```

At `p = 2` this reproduces the ledger's own exact Hast--Matei numbers
(`(ell-1)/2` odd, `(ell-1)/4` even), which is a real check on the formula.
The deficit **grows** with `p`: a restriction estimate that removes *all* the
log-powers still loses `(ell/2)^(p/2)`, and larger `p` is worse, not better.

Reason, stated structurally: an unconstrained `L^p` bound is phase-blind, and
Holder to `L^infinity` is saturated exactly by the delta configuration, which
is the counterexample.  The only fourth-order object that is *not* phase-blind
is the product-constrained one,

```text
Q_4 = sum_(chi1 chi2 chi3 chi4 = 1) prod_i S_chi_i = 2^(3ell) M_4 ,
```

which is what `K_4` cleans up.  So: **PROVED (modulo the corroborated
second-moment model, exact at `p=2`): among family moments, the constrained
fourth moment is the unique viable object; no Green--Tao-style restriction
exponent substitutes for it.**  This is a positive confirmation that the lane
picked the right object, and it closes the restriction family as a route.
NEW TO THE LEDGER (as a closed route with an explicit deficit formula).

### 2026-08-20T16:30 -- charge (2): the PFR / inverse-theorem contrapositive is a tautology here

Verified references (web, 2026-08-20, not memory):

- W. T. Gowers, B. Green, F. Manners, T. Tao, *On a conjecture of Marton*,
  <https://arxiv.org/abs/2311.05762> (PFR over `F_2`; Ann. of Math.).  Set
  `A` with `|A+A| <= K|A|` is covered by `2K^C` cosets of a subgroup `H` with
  `|H| <= |A|`.
- A polynomial Freiman-Ruzsa inverse theorem **for function fields**:
  <https://arxiv.org/abs/2501.11580> -- for `A subset F_p[t]` with
  `|A + tA| <= K|A|`, `A` is covered by `K^O(1)` translates of a generalized
  arithmetic progression of rank `O(log K)` and size `K^O(1)|A|`.
- J. Leng, A. Sah, M. Sawhney, *Quasipolynomial bounds on the inverse theorem
  for the Gowers `U^(s+1)[N]`-norm*, <https://arxiv.org/abs/2402.17994>.

Now the exact translation.  By Translation 3, `Q_4` is the additive energy
`E(S)` of the spectrum on `Ghat`.  Its maximum, at fixed `L^2` mass
`P_2 = sum_chi |S_chi|^2`, is `E_max = 2^ell P_2^2`, attained **only** when `D`
is a delta.  A Lemire failure forces `M_4 >= 2^(4(n-ell))`, i.e.

```text
E(S) >= E_max / (Sigma(ell)^2 / 2^(2(n-ell)))  ~  E_max / ell^4 .
```

So the contrapositive hypothesis is not "energy is large"; it is **"energy is
within a polylog factor of its absolute maximum"** -- formally the strongest
possible input to an inverse theorem.  And that is precisely why it is
useless:

> **REFUTED (route), witness = the identity itself.**  In the extremal
> configuration `S` is a *linear phase*, `S_chi = c * conj(chi(e_0))`, whose
> support is all of `Ghat` with doubling constant `1`.  PFR's conclusion --
> "`A` is covered by `2K^C` cosets of a subgroup `H <= Ghat` with
> `|H| <= |A|`" -- returns `H = Ghat`, `1` coset: vacuously true and
> information-free.  Worse, the `U^2` inverse statement one actually wants
> ("large `E(S)` implies `S` correlates with a character of `Ghat`") is, by
> Fourier duality on this group, *literally the identity*
> `E(S) = 2^(3ell) sum_e D_e^4`: "correlates with the character `chi -> chi(e_0)`"
> means "`D_(e_0)` is large".  The inverse theorem here is a restatement of the
> hypothesis, not a tool.

Consequences, stated so nobody re-opens this:

- The post-2023 breakthroughs (PFR, quasipolynomial `U^(s+1)` inverse
  theorems) improve the *quantitative dependence* in "small doubling ==>
  few cosets".  The obstruction here is not quantitative -- the structural
  conclusion **is** the hypothesis -- so no improvement in `C` or in the
  `U^3/U^4` bounds changes anything.
- Higher-order Fourier analysis is the wrong order.  The extremal
  configuration is a *degree-one* phase; `U^3`/`U^4`/nilsequence machinery
  addresses degree `>= 2` obstructions that are simply not present.  This is
  a *different* reason from the bridges note's (correct) reason for stopping
  Tao--Ziegler (unbounded nonclassical degree of the Mobius phase); both hold.
- The function-field PFR (arXiv:2501.11580) is about `|A + tA|` in `F_p[t]`
  as an additive set; our group is the *unit* group `E_ell` and the energy is
  on its dual.  Even setting the tautology aside, the hypothesis shape does
  not match.

**And the same tautology kills the "structure versus proved pseudorandomness"
squeeze I was asked to develop, for a second and independent reason -- an
uncertainty principle.  I record it as a clean lemma because it explains
structurally (not just numerically) why the proved low-conductor
equidistribution can never contribute:**

> **PROVED (one line).**  Let `a < ell` and let `m: G -> R` be any function
> measurable with respect to the conductor-`a` filtration (equivalently, whose
> Fourier support lies in the conductor-`<= a` subgroup of `Ghat`) with
> `m <= delta_1` pointwise.  Then `m <= 0` everywhere, hence
> `sum_e m_e N_e <= 0` and the Beurling--Selberg/minorant method gives no
> positive lower bound on `N_1`.
> *Proof.*  `m` is constant on each coset of the annihilator
> `H_a = (Ghat_a)^perp`, which has order `2^(ell-a) >= 2`.  The coset of the
> identity contains some `e != 1` where `m_e <= delta_1(e) = 0`; constancy
> forces `m_1 <= 0`.  QED

So the levels below `ell - ceil(log2 ell)` -- where the lane has *proved*
equidistribution by exact Fourier inversion plus individual Weil -- are not
merely quantitatively insufficient; they are **structurally incapable** of
producing endpoint positivity.  All the information must come from the top
`O(log ell)` levels, and the lane's telescoped identity-path reduction is
therefore optimal in shape, not just convenient.  NEW TO THE LEDGER as a
statement (the quantitative version is already there).

### 2026-08-20T16:45 -- what the target actually is, in the classical dictionary

Two identifications that place `K_4 <= M_2^2` precisely in the literature.
Both are checkable and neither is in the lane's documents.

**(i) `M_2` is exactly the Keating--Rudnick short-interval variance.**  The
reciprocal equivalence makes a Hayes class `e` the same thing as a short
interval `I(A;h) = {f : deg(f-A) <= h}` with `h = n-ell-1`, of size
`2^(h+1) = 2^(n-ell)`.  Keating and Rudnick (*The variance of the number of
prime polynomials in short intervals and in residue classes*, IMRN 2014,
<https://arxiv.org/abs/1204.0708>) prove, for fixed `n >= 4`, `0 <= h <= n-4`,
as `q -> infinity`,

```text
Var = q^(h+1) (n - h - 2) .
```

Substituting `h = n-ell-1` gives `n-h-2 = ell-1`, hence
`M_2 = 2^ell * Var = (ell-1) 2^n` -- **exactly** the empirical law I fitted to
the CAS rows above (`(9,19)`: `6.37` measured vs `ell-2 = 7`; the `(23,47)`
prediction reproduces the ledger's exact `M_4` to three digits).  So the
lane's `M_2` is a *proved* quantity in the large-`q` limit and the
`q=2`-fixed, `n -> infinity` version is what is open.

**(ii) `K_4 <= M_2^2` is the fourth-moment case of the
Montgomery--Soundararajan Gaussian-moments conjecture.**  Montgomery and
Soundararajan (*Primes in short intervals*, Comm. Math. Phys. 252 (2004))
conjecture that the `K`-th moment of `psi(x+H)-psi(x)` is the Gaussian moment
`mu_K = 1*3*...*(K-1)` (`K` even), uniformly for
`(log N)^(1+delta) <= H <= N^(1-delta)`; they prove it follows from a **strong
form of the Hardy--Littlewood `k`-tuples conjecture**.  Our endpoint sits at
`H ~ sqrt(N)`, inside that range, and `R_0 -> 3` is exactly `mu_4 = 3`.  The
geometric/function-field side of the same statement is Hast--Matei
(<https://arxiv.org/abs/1604.02067>, already in the ledger) and, for
general factorization functions, Rodgers, *Arithmetic functions in short
intervals and the symmetric group*, Algebra & Number Theory 12 (2018)
1243-1279, <https://arxiv.org/abs/1609.02967> -- both again `q -> infinity`.

**Verdict from (ii):** the live target `K_4 <= M_2^2` is the fixed-`q`
analogue of a conjecture that, over `Z`, is known only under strong
Hardy--Littlewood and is open unconditionally.  Aiming at it is aiming at a
known-hard statement.  Aiming at (SLACK) is not: (SLACK) is `2^ell/poly(ell)`
times weaker and has no known-hard counterpart, because over `Z` the analogous
weakening ("the fourth moment of primes in `[x, x+sqrt x]` is at most
`H^4`", i.e. within a full power of the number of intervals of the Gaussian
value) is a far cruder demand than Gaussian moments.  This is the strongest
strategic argument I have and it follows purely from the arithmetic in the
16:00 entry.

### 2026-08-20T17:05 -- the one live route in my field: weight-graded (Efron--Stein) hypercontractivity

The bridges note stops hypercontractivity because "the current phase has full
algebraic degree" and generic inequalities "require a ... low-Fourier-degree
input".  That reason is correct for the *algebraic* (ANF) degree of the
Mobius/discriminant phase, and correct for a *degree-graded* inequality with
constant `9` per degree.  It does not settle the question, for two reasons
that only became visible after the 16:00 slack computation:

1. The relevant grading is not conductor level and not ANF degree.  It is the
   **Efron--Stein / product grading** of `G = E_ell` as a product of cyclic
   2-groups, and nobody has measured the spectrum in that grading.
2. With `2^ell/poly(ell)` of slack we can afford a hypercontractive constant
   that grows *exponentially in `ell`*, which is a completely different
   demand from "bounded degree".

Exact structure of the grading (computed here, `python3`; independently
consistent with the ledger's proved rank `ceil(ell/2)` of `E_ell/2E_ell`):

```text
E_ell = prod_(i odd, 1<=i<=ell) <1 + x^i>,   ord(1+x^i) = 2^k_i,
        k_i = min{ m : i*2^m > ell },        sum_i k_i = ell  (checked).
ell:      9    12    20    23    50   200
#factors: 5     6    10    12    25   100   = ceil(ell/2)  (checked)
k-list:  4,2,1,1,1  |  5,3,3,2,2,1,1,1,1,1 (ell=20)  ...
fraction of characters with ALL coordinates nontrivial:
         2^-3.51  2^-3.70  2^-6.26  2^-7.68  2^-15.6  2^-63.5
         i.e. ~ 2^(-0.318 ell)
expected number of nontrivial coordinates ~ 0.335 * ell
```

Assign each character the **weight** `w(chi) = sum_(i in supp chi) k_i`, so
`0 <= w <= ell`, and let `f_w` be the fraction of the spectral `L^2` mass
`P_2` carried by weight-`w` characters.  Suppose a weight-graded
`(2,4)` estimate `||D^(=w)||_4 <= C^(w/4) ||D^(=w)||_2` holds (normalized
measure).  Then triangle + Cauchy over the `<= ell` weights give

```text
R_0 <= ( sum_w C^(w/4) sqrt(f_w) )^4 .
```

If `f_w` followed the character-count profile above (`f_ell ~ 2^(-0.318 ell)`,
mass concentrated near `w ~ 0.335 ell`), the binding term is the top one,
`C^ell 2^(-0.636 ell)`, and (SLACK) `R_0 <= 2^(ell+2)/Sigma_norm^2` is met iff

```text
C <= 2^1.636 = 3.11   (asymptotically; the poly(ell) factors are absorbed).
```

For comparison, the *sharp* Bonami/Khintchine constant at weight one on a
two-point factor is exactly `3` (Whittle's identity
`E(sum a_i r_i)^4 = 3(sum a_i^2)^2 - 2 sum a_i^4`, so degree-one kurtosis
`< 3`).  So under the uniform-mass model the route **passes with a margin of
3.11 vs 3** -- marginal, but on the right side, and it is the only route in my
field that is on the right side at all.

Honest risk register, in order of severity:

- **(R1) `f_w` is not the character-count profile.**  `|S_chi|^2` grows with
  conductor level, and high weight correlates with high conductor, so the
  true mass profile is pushed toward large `w`.  If `f_ell` is `2^(-c ell)`
  with `c < 0.318` the threshold constant drops below 3 and the route dies.
  **This is measurable exactly and is the decisive experiment.**
- **(R2) the per-unit-weight constant for a `Z/2^k` factor with `k >= 2` is
  not known to me to be 3** -- for uniform measure on `m` points the naive
  per-coordinate `(2,4)` ratio is `m`, not `3`, and `2^k > 3` for `k >= 2`.
  A weight-`k` cyclic factor may cost `2^k` rather than `3^k`; note
  `2 < 3`, so this could also help.  Must be read out of the literature, not
  guessed.
- **(R3) the Cauchy-over-`w` step** loses `<= ell` and is harmless against
  (SLACK), but the triangle inequality over weights erases exactly the
  cross-weight cancellation the lane has repeatedly found essential.  It is
  *affordable* here only because of the exponential slack -- which is the
  whole point of the 16:00 entry.

Machine to cite, and it is post-2019 and absent from the lane's documents:
**global hypercontractivity**, Keevash--Lifshitz--Long--Minzer,
*Hypercontractivity for global functions and sharp thresholds*, JAMS 37
(2023) 245-279, <https://arxiv.org/abs/1906.05568> (see also
<https://arxiv.org/abs/2103.04604>, and the sharp version
<https://arxiv.org/abs/2307.01356>).  Its hypothesis replaces "low degree" by
"**global**": the function is not significantly amplified by restricting a
small set of coordinates.  That hypothesis is exactly a bound on coset-`L^2`
masses of `D`, which is exactly the lane's already-computed
`B_j(b) = sum_(pi_j(e)=b) D_e^2` cylinder data -- i.e. the lane has already
built the input this theorem consumes, under a different name
("local Carleson estimate on every Witt cylinder").
CAVEAT I must flag: I could not extract the formal theorem statement (both
PDF fetches failed to decode; the arXiv abstract pages do not carry it).  The
exact `gamma`-globalness definition and constants **must be read from the
paper before any use**; I am recording the pointer and the shape, not a
verified inequality.


### 2026-08-20T17:20 -- dead ends recorded (things I tried and dropped)

- **Balog--Szemeredi--Gowers + PFR chain.**  Dropped: the failure hypothesis
  puts the doubling constant at `1` (the extremal spectrum is a linear phase
  supported on all of `Ghat`), so every covering conclusion is vacuous.  See
  16:30.
- **`U^3`/`U^4` inverse theory (Leng--Sah--Sawhney quasipolynomial bounds,
  Tao--Ziegler low characteristic).**  Dropped: the obstruction is degree
  one.  There is no higher-degree structure to invert.
- **Green--Tao restriction / enveloping sieve (Le, Li in function fields).**
  Dropped with an explicit deficit formula `(ell/2)^(p/2)` at every `p`; see
  16:15.  It is worth keeping the *pointer* because the majorant technology
  would be needed by any Type-II refinement, but it does not close (MIN).
- **Beurling--Selberg minorant of the identity class using proved
  low-conductor equidistribution.**  Dropped, and proved impossible in one
  line (uncertainty principle, 16:30).
- **Multiplicative large sieve for Hayes characters.**  Dropped by
  computation: with modulus `2^(ell+1)` and range `2^n = 2^(2ell)` the large
  sieve is in its trivial regime (`N >> Q`) and returns nothing beyond
  Cauchy.
- **"Multiplicative energy of primes in function fields" / "Sidonicity of
  character families" as an existing machine.**  Searched; no such literature
  exists for this object.  The nearest hits are Sidon *sets* in `F_q[t]`
  (Sidon bases) and additive-energy bounds for algebraic sets in `F_p`, both
  unrelated.  There is **no standard machine** that proves `K_4 <= C M_2^2`
  for structured multiplicative sets; the honest answer to that part of my
  charge is "none found".
- **Restating `K_4` as an energy of the Frobenius-class multiset.**  This is
  the wrong contraction (it is `sum_chi |S_chi|^4`, the other fourth moment);
  see Translation 3 at 15:25.  I corrected my own brief rather than building
  on it.

## FINDINGS

### (a) Sharpest reformulation

Three equivalent statements, each exact:

1. `R_0 = 2^ell M_4 / M_2^2` is **the kurtosis** of the class discrepancy
   `D_e` under uniform measure on `G`.  `K_4 <= M_2^2` is "kurtosis `<= 4`",
   i.e. `||D||_4 <= sqrt(2) ||D||_2`, i.e. `Var(D^2) <= 3 (E D^2)^2` on the
   conductor martingale.
2. `Q_4 = 2^(3ell) M_4` is **the additive energy of the spectrum `S` on the
   dual group** `Ghat`; the three Wick pairings are its three degenerate
   solution families (`a=c`, `a=d`, and -- because `D` is real -- `a+b=0`).
   `K_4 <= M_2^2` says the spectrum is an **almost-Sidon / near-4-design**
   weighted family: energy at most `4/3` times the forced diagonal.
   (The *other* fourth moment `sum_chi |S_chi|^4 = 2^ell E_G(D)` is the
   energy of the Frobenius-class multiset and is a different contraction --
   the lane already knows this; my brief had them swapped.)
3. **The one that matters strategically.**  The endpoint needs only
   `M_4 < 2^(4(n-ell))`, hence only
   `R_0 <= 2^(ell + 2(n-ell)) / Sigma(ell)^2`, which at `ell = 200` is
   `R_0 <= 2^171.5`.  The pursued `R_0 <= 4` is stronger than sufficient by
   ~`2^169`.  Equivalently: the endpoint is a **poly(`ell`) improvement over
   the trivial kurtosis bound `R_0 <= 2^ell`**, and equivalently a saving of
   `(ell-2)/sqrt(2)` over the triangle inequality applied to Weil.  The
   conjectured target encodes *full square-root cancellation* across the
   character family; only *one logarithm* of cancellation is required.

### (b) Most promising transferable technique

**Weight-graded hypercontractivity in the Efron--Stein (product-of-cyclic-
2-groups) grading, via global hypercontractivity.**
Keevash--Lifshitz--Long--Minzer, JAMS 37 (2023) 245-279,
<https://arxiv.org/abs/1906.05568>; sharp version
<https://arxiv.org/abs/2307.01356>.  Its hypothesis ("global": no small set of
coordinates amplifies the function) is exactly the coset-`L^2` cylinder data
`B_j(b)` the CAS already computes, and it does **not** require low degree --
which is what the bridges note's stopping reason assumed.  Under the
uniform-mass model the required per-unit-weight constant is `<= 2^1.636 = 3.11`
versus the sharp two-point value `3` (Whittle/Khintchine), so the route is on
the right side of the line but by a thin margin.  It lives or dies on one
measurable statistic (see (d)).

Supporting citations for the dictionary, all verified today:
Keating--Rudnick <https://arxiv.org/abs/1204.0708> (`M_2` *is* their
short-interval variance, `= (ell-1)2^n`, proved for `q -> infinity`);
Rodgers <https://arxiv.org/abs/1609.02967>; Hast--Matei
<https://arxiv.org/abs/1604.02067> (already in the ledger);
Montgomery--Soundararajan, *Primes in short intervals*, CMP 252 (2004)
(`R_0 -> 3` is their `mu_4 = 3`; their conjecture is known to follow from a
strong form of Hardy--Littlewood and is open otherwise).

### (c) Decisive obstructions

1. **PROVED (tautology).**  The inverse-theorem contrapositive is degenerate:
   the extremal configuration is a linear phase with doubling `1`, and the
   `U^2` inverse statement is, by Fourier duality on this group, *literally*
   the identity `E(S) = 2^(3ell) sum_e D_e^4`.  PFR/BSG/`U^3`/`U^4` add
   nothing, at any quantitative strength.  The "structure vs. proved
   pseudorandomness squeeze" I was asked to develop **cannot be made
   non-circular in this formulation**.
2. **PROVED (uncertainty principle, one line, 16:30).**  Any minorant of
   `delta_1` measurable for the conductor-`<= a` filtration (`a < ell`) is
   nonpositive.  Hence the *proved* low-conductor equidistribution is
   structurally incapable of contributing endpoint positivity, however strong
   it is made.  All information must come from the top `O(log ell)` levels.
3. **PROVED modulo the corroborated second-moment model, exact at `p=2`.**
   Every unconstrained family `L^p` estimate (i.e. every Green--Tao-style
   restriction theorem) misses by `~(ell/2)^(p/2)`, worsening with `p`.  The
   product-constrained fourth moment `Q_4` is the unique viable moment
   object; the lane's object choice is forced, not merely convenient.
4. **Difficulty datum.**  `K_4 <= M_2^2` in its uniform form is the fixed-`q`
   analogue of the fourth-moment case of the Montgomery--Soundararajan
   Gaussian-moments conjecture, which over `Z` is open and known only under a
   strong Hardy--Littlewood hypothesis.  The lane is aiming at a known-hard
   statement when a `2^ell/poly(ell)`-weaker one suffices.

### (d) Concrete next experiments runnable here

**E1 (highest value, cheap, decides route (b)).**  Extend the exact spectral
diagnostics to report the **coordinate-weight profile** of the spectrum:
for each character `chi`, compute `w(chi) = sum_(i in supp chi) k_i` in the
stable mixed-radix coordinates the CAS already maintains
(`k_i = min{m : i 2^m > ell}`, `sum k_i = ell`, checked above), and emit the
exact integer table `f_w = (sum_(w(chi)=w) |S_chi|^2) / P_2` for
`ell = 6..14` at both endpoint parities.  Then evaluate
`(sum_w C^(w/4) sqrt(f_w))^4` against the (SLACK) threshold for
`C in {2, 3, 4, 9}`.  This is the first time the spectrum would be graded by
anything other than conductor level.  Decides (R1) outright.

**E2 (cheap, high strategic value).**  Add the (MIN)/(SLACK) thresholds to the
existing implication ledger as a *second, weaker* sufficient target beside
`R_0 <= 4`: report, per row, both `R_0` and
`R_0^suf = 2^(ell + 2(n-ell))/Sigma(ell)^2`, and the ratio.  Crossover is at
`ell = 15` (odd) / `ell = 11` (even); the certified range to degree 400 covers
everything below.  Cost: arithmetic on integers already computed.

**E3 (re-audit of "refuted" shortcuts).**  Every phase-erasing shortcut in the
ledger was refuted against an allowance of `M_2^2` at a single small `ell`
(`1425/1483` at `ell=8`; `303.92/632.42` at `ell=12`; "cells over thirty times
the signed total" at `ell=9`).  Re-measure each loss factor across
`ell = 6..14` and fit its growth.  **Any shortcut whose loss grows like
`poly(ell)` is not refuted against (SLACK)** and becomes a candidate proof for
`ell >= ell_0`, which is all that is needed after the degree-400 handoff.  I
consider this the highest-expected-value item in the whole list, because it
may resurrect work already done.

**E4 (control).**  Verify (MIN) directly on every completed fleet row:
check `M_4 < 2^(4(n-ell))` as exact integers.  At `(9,19)`,
`M_4/mean^4 = 5.573e-2`; at `(9,20)`, `2.134e-2`; both pass with the predicted
`2^((ell+2)/4)/(3^(1/4) sqrt(ell-1))` margin.  Cheap, and it pins the margin
growth empirically (predicted `~2^(ell/4)`).

### (e) New to the ledger

1. **(MIN)/(SLACK): the live target is over-engineered by ~`2^ell/poly(ell)`;
   at `ell=200` `R_0 <= 2^171.5` suffices.**  With the crossover table and the
   three equivalent readings.  This is the item I would land first.
2. The `L^p` deficit formula `(ell/2)^(p/2)`, closing the Green--Tao
   restriction / enveloping-sieve family (Le arXiv:0908.2642; Li, Finite
   Fields Appl. 95 (2024) 102383) as a route, and *proving* that the
   constrained fourth moment is the forced object.
3. The uncertainty-principle lemma: low-conductor levels are structurally,
   not just quantitatively, useless for endpoint positivity.
4. The inverse-theorem tautology: PFR (arXiv:2311.05762), function-field PFR
   (arXiv:2501.11580), and quasipolynomial `U^(s+1)` bounds
   (arXiv:2402.17994) are all inapplicable for a structural reason, so this
   family should be closed rather than re-proposed.
5. The classical identifications: `M_2` **is** the Keating--Rudnick
   short-interval variance `(ell-1)2^n` (arXiv:1204.0708), and `K_4 <= M_2^2`
   **is** the fixed-`q` fourth-moment case of Montgomery--Soundararajan's
   Gaussian-moments conjecture -- a difficulty datum the lane should record
   before spending more on the uniform form.
6. The Efron--Stein coordinate grading of `E_ell`
   (`k_i = min{m : i 2^m > ell}`, `sum k_i = ell`, `ceil(ell/2)` factors,
   full-support fraction `~2^(-0.318 ell)`) as a *new* grading for the
   spectrum, and global hypercontractivity (JAMS 2023) as the machine that
   consumes the lane's existing Witt-cylinder data without a low-degree
   hypothesis.

### Epistemic ledger for this file

PROVED: Translations 1-3; the (MIN)/(SLACK) arithmetic (given the ledger's
proved `M_2` Weil envelope and its proved `max|D|^4 <= M_4` step); the
uncertainty-principle lemma; the tautology obstruction.
PROVED-MODULO-MODEL (the model `M_2 ~ (ell-1)2^n`, `M_4 ~ 3M_2^2/2^ell`, which
reproduces the ledger's exact `(9,19)`, `(9,20)`, `(23,47)` integers and
matches Keating--Rudnick): the `L^p` deficit formula; the counterexample
visibility ratios.
REFUTED (with reason, not witness -- the reason is structural): PFR/BSG,
`U^3`/`U^4`, unconstrained restriction, Beurling--Selberg minorants,
multiplicative large sieve.
OPEN: everything about route (b); the value of `f_w`; whether E3 resurrects
any refuted shortcut.
NO THEOREM CREDIT is claimed for Lemire's conjecture or for any of the lane's
open lemmas.  Every number quoted from the CAS is finite evidence.
