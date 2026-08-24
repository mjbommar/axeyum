# Ad hoc blocker sweep 2026-08-20 -- lane 03: random matrix theory and monodromy equidistribution

Field specialist diary.  Ad hoc research challenge, explicitly OUTSIDE the
normal Axeyum roadmap / test suite / gates.  Nothing here is theorem credit;
every claim is labelled PROVED / REFUTED (with witness) / OPEN.

Agent: adhoc-blocker-sweep lane 03 (random matrix theory + monodromy).
Worktree: `/home/mjbommar/projects/personal/axeyum-gf2-lemire` (detached).
Write scope: this file only.

## The blocker in my field's exact form (restated from the brief)

There are `2^ell` unitarized Frobenius conjugacy classes `Theta_chi`, one per
wild Hayes character mod `x^(ell+1)`, `Theta_chi` of dimension roughly
`(conductor level of chi) - 1`.  Needed:

```text
abs( sum_chi Tr(Theta_chi^n) ) = O(2^ell)      at n ~ 2 ell.
```

Termwise Weil gives `ell * 2^ell` (each `abs(Tr(Theta_chi^n)) <= dim <= ell`).
So the ask is exactly one factor of `ell = log_2(family size)`: square-root-
of-family cancellation for a FIXED family, `q = 2`, no deformation parameter.

## Timestamped log

### 2026-08-20T19:08Z -- context ingested

Read: `lemire-review-2026-08-20-reaim.md` (full), `docs/plan/status/52-gf2-lemire.md`
(full, 746 lines), and the Katz/monodromy section of the canonical note
(`lemire-half-degree-irreducibles.md` lines 2790-2935).

Pre-existing lane findings that constrain everything I may propose (I will NOT
re-propose these):

- REFUTED (lane, exact witness): Katz's pointwise character fourth moment
  `sum_chi abs(S_chi)^4 = 2^ell sum_h (sum_e D_e D_(e+h))^2` is a DIFFERENT
  tensor contraction from the needed product-constrained
  `sum_(chi_1 chi_2 chi_3 chi_4 = 1) prod_i S_(chi_i) = 2^(3 ell) M_4`.
  They already differ at the level-seven odd endpoint.
- REFUTED: the (AG) cohomological budget (`H_c^i = 0` for `i > 4 ell`, total
  normalized Betti `<= ell^4`) as a universal all-level lemma -- witness
  `(ell,n,r) = (2,5,5)` needs normalized coefficient 26 vs `ell^4 = 16`; and
  the exact closed form `T_r = q^12 (q-1)(q^2-6q+6)` has normalized degree 5,
  one above the proposed degree-4 cutoff.  Level three: `T_r = q^16 (q^2-1)
  (q^4-6q^2+6)`, normalized degree 8, refuting the degree-6 cutoff and the
  "one extra q" repair (explicitly at q=128).
- REFUTED: one-Weil-unit orbit bounds at `(j,n) = (7,15)` (max `1696 > 256`,
  18 of 28 orbits violate); order-layer coefficient 17 needed at `(11,24)`.
- REFUTED (as a route): family second moment + Cauchy across the 4032 top
  characters at `ell=12` -- exact shortfalls `304` and `633` at the two
  endpoints.
- REFUTED: Hast--Matei idealized second moment `(ell-1) 2^n`; Cauchy misses by
  squared ratios `(ell-1)/2` (odd) and `(ell-1)/4` (even).
- LIVE aggregate target: `K_4 <= M_2^2`, equivalently root ratio `R_0 <= 4`
  (`R_0 = M_4/M_2^2`, so `K_4/M_2^2 = R_0 - 3`).  Verified `ell <= 22/23`;
  measured `R_0 - 3` about `-3.3e-4`, `-5.2e-3`, `+1.1e-3` at `ell = 23`.
  Implies `M_4 <= 64 ell^4 2^(3 ell)`, which closes the ledger after the
  degree-400 handoff.  Uncredited finite evidence only.
- PROVED (lane): `M_2 <= ell^2 2^n`.
- PROVED (lane): exact conductor filtration -- level `j` contributes `2^(j-1)`
  characters of degree `j-1`, so `D = sum deg = (ell-2) 2^ell + 2`.  This is
  where the fatal linear factor `ell` in the termwise Weil bound comes from.

### 2026-08-20T19:20Z -- literature sweep 1: is Katz's family OUR family?

Verified by fetching and text-extracting the primary sources (not from memory).

**Katz, "Witt Vectors and a Question of Keating and Rudnick", IMRN 2013 no. 16,
3613-3638.**  Source PDF: `https://web.math.princeton.edu/~nmk/wittchar25.pdf`
(the lane's note cites `wittchar31.pdf`; same paper, later draft).  Setup, verbatim
from the paper: `k = F_q`, `B := k[X]/(X^(n+1))`, a character
`Lambda : B^x -> C^x` is *even* if trivial on `k^x`; `B^x/k^x` is the group of
big Witt vectors mod `X^(n+1)`.  `Lambda` is *primitive* iff nontrivial on
`1 + k X^n`, and `Swan(Lambda)` is the largest `d <= n` with `Lambda` nontrivial
on `1 + k X^d`.  `L(A^1/k, L_(Lambda(1-tX)))(T)` is a polynomial of degree
`Swan(Lambda) - 1`, pure of weight one; the unitarized class is defined by
`det(1 - T theta_(k,Lambda)) = L(A^1/k, L_(Lambda(1-tX)))(T/sqrt(q))`.

**FINDING (structural identification, checked):** at `q = 2` we have `k^x = 1`,
so "even" is vacuous and `B^x/k^x = B^x` has order `2^n`.  With `n = ell` this
is *exactly* the Lemire Hayes family: `2^ell` characters, exact level `j`
carrying `2^(j-1)` characters of `L`-degree `j-1` (Swan `= j`), total degree
`D = (ell-2) 2^ell + 2`.  This reproduces the lane's proved conductor
filtration line for line.  Moreover `Lambda(P) := Lambda(P(X)/P(0) mod X^(n+1))`
is the reciprocal-truncation map, i.e. the lane's "reciprocal equivalence
(identity ray class mod `x^ceil(n/2)`)".  So Katz's papers really are about this
family, and the dictionary is exact, not analogical.

The Weil-sum side is exact too.  With `-log L = sum_m S_m T^m / m`, one has
`Tr(theta^n) = -S_n / q^(n/2)` and `S_n(Lambda) = sum_(t in F_(q^n))
Lambda(Norm(1 - tX))`.  Summing over ALL `2^ell` characters and using
orthogonality gives back `2^ell` times the Lemire count.  So the family sum is
*literally* the endpoint count -- there is no lossy step in the RMT translation.

**Theorem 1.2 / 8.1 (equidistribution).**  "Fix an integer `n >= 4`.  In any
sequence of finite fields `k_i` ... whose cardinalities `q_i` are archimedeanly
increasing to infinity, the collections `{theta_(k_i,Lambda)}_(Lambda primitive
even)` become equidistributed in `PU(n-1)^#`."  (`n >= 3` allowed if no `k_i`
has characteristic 2 or 5.)  So: **conductor FIXED, `q -> infinity`.**  Our
regime is the exact opposite: `q = 2` fixed, conductor `-> infinity`.

Katz spells out the proof mechanism and its constant:

```text
(1/#Prim_n(k_i)) sum_(Lambda in Prim_n(k_i)) Trace(Xi(theta_(k_i,Lambda)))
   is bounded by C(p,n,Xi)/sqrt(#k_i),
C(p,n,Xi) := sum_i h^i_c(Prim_n (x) F_pbar, Xi(L_univ)).
```

and then, verbatim: *"At present, we do not know uniform bounds for these sums
of Betti numbers `C(p,n,Xi)` as `p` varies (`n` and `Xi` fixed)."*  His
`p`-independent replacement is **Theorem 8.2**, and it is explicitly gated:
"Suppose `n >= 3` and `p > 2n - 1`", giving
`|sum_(Lambda in Prim_n(k)) Trace(Xi(theta))| <= 3 dim(Xi) #Prim_n(k) /
((n-1) sqrt(#k))`.  For us `p = 2`, `n = ell`, so `p > 2n-1` fails for every
`ell >= 2`: **Theorem 8.2 is unavailable at `q = 2` for structural reasons, not
by oversight.**

**Theorem 5.1 (large monodromy) IS available at `p = 2`.**  Verbatim: "Let `p`
be a prime, and `n >= 3`.  Then `G_geom` contains `SL(n-1)` except in the cases
`(p = 5, n = 3)` and `(p = 2, n = 3)`."  So for our family at `q = 2` and
`ell >= 4`, **`SL(ell-1) subset G_geom subset G_arith subset GL(ell-1)` is a
PROVED input.**  This is the one piece of the monodromy package that transfers
to `q = 2` verbatim, and it should be recorded in the ledger as proved rather
than as "expected".

**Two precision points the ledger does not currently make.**

1. The equidistribution in Theorem 1.2 is in `PU(n-1)`, **not** `U(n-1)`, and
   Katz says why: `G_arith subset {A in GL(n-1) : det(A)^(4 p^(r+1)) = 1}` for
   `p^r` the largest power of `p` at most `n`, so "the classes are not
   equidistributed as classes in `U(n-1)`, already their determinants fail to be
   equidistributed in the unit circle."  Our test function `A |-> Tr(A^m)` is a
   `U`-class function, not a `PU`-class function: `p_m` decomposes into hooks
   `s_((m-r,1^r))` whose central character is `z |-> z^m`, nontrivial on scalars
   unless `(ell-1) | m`.  So **Theorem 1.2 as stated says nothing about our
   statistic.**  What one must use instead is Theorem 5.1 (`G_geom` contains
   `SL`) plus Deligne's Weil II directly, since every hook is nontrivial on
   `SL(ell-1)` (a hook is a rectangle `(a^N)` only for a single column, i.e.
   `m = N`).  That route is available at `p = 2` -- but see the barrier below.
2. `Prim_ell(F_2)` has `2^(ell-1)` points, so the family is large **because
   `dim Prim_ell = ell` grows, not because `q` grows.**  Every Deligne-type
   bound gives a *relative* saving of `q^(-1/2)` regardless of dimension.  At
   `q = 2` that is `0.707`.  This is the whole barrier, stated in one line.

### 2026-08-20T19:26Z -- literature sweep 2: the tuple/independence results

**Katz, "Witt Vectors and a Question of Entin, Keating, and Rudnick", IMRN 2015
no. 14, 5959-5975** (`witthcharindepall20.pdf`).  Exact hypotheses, read from the
source:

| statement | tuple | hypotheses |
|---|---|---|
| Thm 1.2 | `(theta_Lambda, theta_(Lambda^2))` | `n >= 5`; characteristics `p not in {2,3}`; `q_i -> infinity` |
| Thm 1.3 | `(theta_Lambda, ..., theta_(Lambda^d))` | `n >= 5`; `p >= 2d+1`; `q_i -> infinity` |
| Thm 2.2 (monodromy) | `L^(a) (+) L^(b)` has `G_geom` containing `SL x SL` | `p` does not divide `ab(a^2-b^2)` |
| Thm 3.1 | `(theta_chi, theta_Lambda, theta_(chi Lambda))` over primitive PAIRS | `n >= 5`; `p >= 7`; `q_i -> infinity` |
| Thm 3.2 | `(theta_(chi^a Lambda^b))_((a,b) in I_d)` | `n >= 5`; `p >= 2(d+1)^2 - 1`; `q_i -> infinity` |

**FINDING.**  Theorem 3.1 is the closest published relative of the live target:
it is exactly a *constrained-triple* (convolutional 3-design) statement, the
tuple being tied by the group relation `chi . Lambda . (chi Lambda)^(-1) = 1`.
The needed `K_4` statement is its order-4 analogue.  But:
(i) every one of these excludes `p = 2` (Thm 2.2's condition `p | ab(a^2-b^2)`
fails at `p = 2` for any distinct `a,b >= 1`, since `ab(a^2-b^2)` is always even);
(ii) all of them fix `n` and send `q -> infinity`;
(iii) all of them equidistribute in `PU`, not `U`.
So no tuple-independence theorem in this line is available in our regime, and
the `p = 2` exclusion is intrinsic to the Artin-Schreier-reduction argument, not
a technical convenience.

**Sawin, "The equidistribution of L-functions of twists by Witt vector Dirichlet
characters over function fields", arXiv:1805.04330.**  Fetched abstract: it
generalizes Katz to L-functions of twists of an *arbitrary* Galois
representation by Dirichlet characters with **"conductor a fixed power of a
degree one prime"** -- that is precisely our modulus `x^(ell+1)` -- and adds
independence across different representations.  Regime: `q -> infinity`.  So the
strongest and most general form of the "design" property IS proved for exactly
our family, and its only defect for us is the limit direction.

**Keating-Rudnick, "The variance of the number of prime polynomials in short
intervals and in residue classes", IMRN 2014 no. 1, 259-288 (arXiv:1204.0708).**
Confirmed: their variance theorems are `q -> infinity` and their stated "crucial
ingredient" is Katz's equidistribution.  So the KR variance law is *not* a
theorem in our regime.

### 2026-08-20T19:31Z -- literature sweep 3: is there ANY fixed-q technology?

Three families of results run at fixed `q` with growing conductor.  All were
checked at source-abstract level.

1. **Entin, "On the distribution of zeroes of Artin-Schreier L-functions"
   (arXiv:1105.5517)** and **Bucur-David-Feigon-Lalin(-Sinha), "Distribution of
   zeta zeroes of Artin-Schreier curves" (arXiv:1111.4701).**  The latter's
   abstract, verbatim: *"We study the distribution of the zeroes of the zeta
   functions of the family of Artin-Schreier covers of the projective line over
   `F_q` when `q` is fixed and the genus goes to infinity ... the number of
   zeroes with angles in a prescribed non-trivial subinterval ... has a standard
   Gaussian distribution."*  This IS our regime (fixed `q`, wild covers, growing
   conductor), and the accompanying survey literature states the barrier
   explicitly: *"when the base finite field is fixed and the genus of the family
   goes to infinity, one cannot make use of the equidistribution results"*
   (David's 2014 Arizona Winter School notes, `swc-math.github.io/aws/2014/
   2014DavidNotes.pdf`, and the introductions of the two papers).
   Their engine is *not* geometry: it is exact independence of the values of the
   additive character at the `#P^1(F_q)` points as the defining polynomial
   varies over a family of growing degree, plus the method of moments.
   **Budget observation (mine):** that engine works while the number of free
   character coordinates exceeds the number of points being tested.  Here the
   family supplies `ell` independent Witt coordinates while `Tr(theta^n)` tests
   `2^n` points; the independence budget runs out at `n = ell` and the endpoint
   needs `n = 2 ell`.  **The Lemire endpoint sits at exactly twice the reach of
   every fixed-`q` independence method** -- the function-field mirror of
   "primes in `[x, x + sqrt(x)]`", which is the lane's own diagnosis arrived at
   from a different direction.
2. **Sawin-Forey-Fresan-Kowalski, "Quantitative sheaf theory", JAMS 36 (2023)
   653-726 (arXiv:2101.00635).**  Abstract, verbatim: complexity of `l`-adic
   complexes is continuous for the six operations and *"provides bounds for the
   sum of Betti numbers that, in many interesting cases, can be made uniform in
   the characteristic of the base field"*; applications are to **horizontal**
   equidistribution.  This is exactly the missing constant in Katz's
   `C(p,n,Xi)` -- but uniformity is in `p`, and the application is again a limit
   in a growing parameter.  It does not remove the `q^(-1/2)` factor.
3. **Bergstrom-Diaconu-Petersen-Westerland (arXiv:2302.07664) + Miller-Patzt-
   Petersen-Randal-Williams "Uniform twisted homological stability"
   (arXiv:2402.00354).**  These prove CFKRS moment predictions for quadratic
   `L`-functions over function fields **at fixed `q`**, via stable homology of
   braid groups with Schur-functor coefficients.  This is the only technology I
   found that produces *conductor-uniform* cohomological input at fixed `q`.
   Caveat recorded honestly: the theorem is stated "for all large enough prime
   powers `q`", the family is tame quadratic (Hurwitz spaces for `Z/2` covers),
   and the wild char-2 Artin-Schreier-Witt analogue does not exist.

### 2026-08-20T19:38Z -- the design translation (Diaconis-Shahshahani, Rains)

References verified: **Diaconis-Shahshahani, "On the eigenvalues of random
matrices", J. Appl. Probab. 31A (1994) 49-62** -- `(tr M, tr M^2, ..., tr M^k)`
converges to `(sqrt(1) Z_1, ..., sqrt(k) Z_k)` with `Z_j` iid standard complex
normal, by the method of moments via symmetric-function theory.  **Rains, "High
powers of random elements of compact Lie groups", Probab. Theory Related Fields
107 (1997) 219-241** -- if a Haar `U in U(N)` is raised to a power `m >= N`, the
eigenvalues of `U^m` are **exactly** `N` iid uniform points on the circle.

Two consequences for this problem.

**(R1) We are in the Rains regime, always.**  Every `theta_chi` has size
`N_chi = j_chi - 1 <= ell - 1`, and the endpoint power is `n in {2ell+1,
2ell+2}`, so `n >= 2 N_chi + 3` for every character in the family.  Hence the
Haar model for `Tr(theta_chi^n)` is *not* an asymptotic Gaussian approximation
-- it is the exact statement "sum of `N_chi` iid uniform unit vectors".  All
moments are explicit and finite-`N` exact:
`E|Tr|^2 = N`, `E|Tr|^4 = 2N^2 - N`, `E Tr = 0`.

**(R2) The required design order is `n`, not 2 or 4, so exactness is
impossible.**  `Tr(A^n)` is homogeneous of degree `n = 2ell + O(1)` in the
matrix entries, so `E_family[Tr(A^n)] = E_Haar = 0` is a `(n,0)`-design
condition.  An exact `t`-design in `U(N)` needs at least about
`binom(N^2 + t - 1, t)` elements; with `t ~ 2 ell` and `N ~ ell` that is
astronomically more than the `2^(ell-1)` members available.  **So no exact-design
mechanism can ever apply; only a one-function approximate statement can.**

**Sharpest RMT reformulation.**  Write `D_e = N_n(e) - 2^(n-ell)` (the lane's
Mangoldt discrepancy) and `w := |D_1| / 2^(n/2)`.  Then:

```text
termwise Weil (proved)        w <= ell - 2 + 2^(1-ell)
Lemire endpoint (needed)      w <  2^(n/2 - ell)  =  sqrt(2) (odd), 2 (even)
Haar/Rains model (predicted)  w ~  sqrt(ell) 2^(-ell/2)
```

So the ask is *not* square-root-of-family cancellation.  It is: **the empirical
mean of the single class function `p_n` over the family must be `O(1)` where the
trivial bound is the matrix dimension `ell`.**  Relative accuracy `O(1/ell)`,
i.e. beat trivial by exactly `log_2` of the family size.  In design language
this is a `1/dim`-accurate one-function statement, and the RMT model says the
truth is smaller than what is needed by a factor `2^(ell/2)/sqrt(ell)`.

**Is `K_4 <= M_2^2` exactly a spectral 4-design assertion?  Yes -- of the
convolutional, not the pointwise, kind.**  Using the lane's definitions
(`M_r = sum_e |D_e|^r`, `K_4 = 2^ell M_4 - 3 M_2^2`, `R_0 = 2^ell M_4/M_2^2 =
3 + K_4/M_2^2`):

- `2^ell M_2 = sum_chi |S_chi|^2` (Parseval), and
  `2^(3ell) M_4 = sum_(chi_1 chi_2 chi_3 chi_4 = 1) prod_i S_(chi_i)`, the
  identity value of the fourfold convolution on the character group.
- The `3 M_2^2` subtraction is exactly the three Wick pairings, i.e. the value
  the constrained fourth moment takes if the `S_chi` are jointly Gaussian /
  independent Haar.
- Therefore `R_0 <= 4` says: *the constrained fourth moment of the family
  exceeds the independent-Haar prediction by at most the factor `4/3`.*
  Equivalently: the discrepancy vector `(D_e)` has excess kurtosis at most 1.
  Equivalently again: `{theta_chi}` is a **4-design for the multiplicatively
  constrained quadruple statistic, up to a constant factor** -- the order-4
  analogue of Katz-EKR Theorem 3.1, which is the order-3 case and is proved for
  `p >= 7`, `q -> infinity`.

This is a different contraction from Katz's *pointwise* fourth moment
`sum_chi |S_chi|^4`, which is what large `SL` monodromy controls -- consistent
with, and now explained by, the lane's earlier exact refutation of that bridge.
Pointwise moments are moments of ONE random matrix; the target is a mixed moment
of FOUR family members tied by a group relation.  Large monodromy of the
universal sheaf gives the former for free and says nothing about the latter;
the latter needs the fibre-product monodromy over `{chi_1 chi_2 chi_3 chi_4 = 1}`,
which is what Katz's Theorem 2.2 / 3.2 style arguments construct -- and which
their proofs cannot construct at `p = 2`.

### 2026-08-20T19:44Z -- a universal Holder obstruction (PROVED, elementary)

This explains, in one line, every Cauchy/Holder shortfall in the ledger
(`304`/`633`; Hast-Matei `(ell-1)/2` and `(ell-1)/4`; the connected
high-frequency `1425`/`1483`).

**Claim (PROVED, under the Haar/Rains model for the moments only).**  Let
`A := sum_(chi != 1) Tr(theta_chi^n)`, `|family| = 2^ell`, and suppose the
family's `2k`-th *pointwise* moment matches Haar:
`sum_chi |Tr(theta_chi^n)|^(2k) = (1 + o(1)) k! ell^k 2^ell`
(true under Rains, since each term is a sum of `N ~ ell` iid uniform vectors).
Then Holder with exponents `(2k/(2k-1), 2k)` gives

```text
|A| <= (2^ell)^(1 - 1/(2k)) . (k! ell^k 2^ell)^(1/(2k))
     = (k!)^(1/(2k)) . sqrt(ell) . 2^ell.
```

The `2^ell` factors combine to exactly `2^ell` for **every** `k`, and the
surviving loss is `sqrt(ell)` for every `k`, with only the harmless constant
`(k!)^(1/(2k))` varying.  Hence:

**No increase of the moment order on the character side can ever close the
endpoint.**  `k = 1` (Cauchy) loses `sqrt(ell)`; `k = 2` (fourth moment) loses
`2^(1/4) sqrt(ell)`; `k = 8` loses `(8!)^(1/16) sqrt(ell) ~ 1.9 sqrt(ell)`.  The
loss is intrinsic: taking absolute values destroys exactly the `sqrt(family)`
worth of phase that Rains says is there, and moments cannot recover phase.
This is the RMT-side statement of the lane's standing rule "any next lemma must
retain phase alignment rather than take an absolute square across the full
character family" -- now with a proof that the rule admits no exceptions of
moment type.

Note the contrast with the lane's live route, which is NOT of this type: it uses
`|D_1| <= M_4^(1/4)` -- a max-versus-moment bound on the SPATIAL side (over the
`2^ell` ray classes), not a Holder bound on the character side.  That is why it
can work where Holder-over-characters provably cannot.  Recomputing the margin:
`R_0 <= 4` gives `M_4 <= 4 M_2^2/2^ell <= 4 ell^4 2^(3ell)` and hence
`|D_1| <= M_4^(1/4) ~ sqrt(2) ell 2^(3ell/4)`, against the requirement
`|D_1| < 2^(n-ell) ~ 2^ell`.  Margin `2^(ell/4)/(sqrt(2) ell)` -- comfortable.
So the spatial max-vs-moment route is structurally the right one, and my
obstruction does not touch it.

### 2026-08-20T19:52Z -- bounded computation: how far is the truth from the target?

Purpose: measure the actual size of the endpoint discrepancy against (i) the
proved termwise Weil bound, (ii) the Lemire requirement, (iii) the Haar/Rains
prediction.  Nothing in the ledger reports this comparison.

Method: a shaped monic `F = x^n + g` with `deg g <= n - ell - 1` is exactly a
polynomial whose reversal is `= 1 mod x^(ell+1)`, so `N_n(1) = sum_g Lambda(F)`
ranges over only `2^(n-ell)` polynomials.  `Lambda` computed exactly in
`GF(2)[x]`: strip perfect squares (all exponents even), then `P = F/gcd(F,F')`,
verify `P` irreducible by Rabin's test and `P^(n/deg P) = F`.  Pure Python,
integers as bit-masks.  No repo state touched.

Exact commands:

```sh
S=/tmp/claude-1000/-home-mjbommar-projects-personal-axeyum/f980d106-5a72-4c93-8c17-11101edf42d1/scratchpad
timeout 280 python3 $S/rmt_probe.py     # table below
timeout 280 python3 $S/rmt_var.py       # variance law
```

Result (`w = |D_1|/2^(n/2)`; `need = 2^(n/2-ell)`; Weil allows `ell-2`):

```text
ell   n   N_n(1)     mean      D_1        w     need   w/need  |D_1|/2^((n-ell)/2)
  4   9       37       32        5   0.2210   1.414   0.1562        0.884
  4  10       76       64       12   0.3750   2.000   0.1875        1.500
  5  11       45       64      -19   0.4198   1.414   0.2969        2.375
  6  13       79      128      -49   0.5414   1.414   0.3828        4.331
  8  17      562      512       50   0.1381   1.414   0.0977        2.210
 10  21     2101     2048       53   0.0366   1.414   0.0259        1.171
 12  25     8551     8192      359   0.0620   1.414   0.0438        3.966
 14  29    31872    32768     -896   0.0387   1.414   0.0273        4.950
 15  31    65876    65536      340   0.0073   1.414   0.0052        1.328
 16  33   133816   131072     2744   0.0296   1.414   0.0209        7.579
 16  34   262804   262144      660   0.0050   2.000   0.0025        1.289
```

(Full 26-row table for `4 <= ell <= 16` at both endpoints is reproduced by the
first command; every row has `N_n(1) > 0`, consistent with the certified range.)

Two measured facts:

1. **`w/need` decays geometrically** (0.156 at `ell=4` to 0.0025 at `ell=16`),
   while the best proved bound `w <= ell-2` *grows*.  The truth is inside the
   requirement by a factor that behaves like `2^(ell/2)/sqrt(ell)`, exactly the
   Rains prediction.  The conjecture is not marginally true; it is true with
   exponential room, and the entire difficulty is that no method reaches it.
2. **The Keating-Rudnick variance law holds at `q = 2`.**  Over all 26 endpoint
   rows,

   ```text
   average of D_1^2 / (ell . 2^(n-ell))     = 1.0063
   average of D_1^2 / ((ell-2) . 2^(n-ell)) = 1.3321
   average of D_1^2 / 2^(n-ell)             = 10.5592   (Poisson would be 1)
   ```

   i.e. `Var(D_1) ~ (matrix dimension) x (mean)`, which is precisely the unitary
   random-matrix / Keating-Rudnick prediction -- in the regime (`q` fixed,
   conductor growing) where **KR's theorem does not apply**.  Labelled OPEN, not
   proved: 26 exact rows are evidence, never a theorem.  But it does say the
   right model is the standard one, and that a proof of the KR variance law at
   `q = 2` would deliver exactly the "idealized second moment" the Hast-Matei
   translation assumes -- and, by the Holder obstruction above, would still lose
   `sqrt(ell)`.  So even proving the KR variance law at `q = 2` does not close
   the endpoint.  That is worth knowing before anyone invests in it.

### 2026-08-20T20:00Z -- the barrier, stated exactly, and the averaging question

**Why every geometric route dies at `q = 2`.**  The endpoint sum is a double
sum with two directions living over *different* fields:

```text
sum_(chi) Tr(theta_chi^n)   =   -2^(-n/2) sum_(chi) sum_(t in F_(2^n)) chi(Norm(1-tX))
                                            ^^^^^                ^^^^^^^^^
                                        F_2 direction        F_(2^n) direction
```

Weil already extracts *full* square-root cancellation in the `t` direction --
that is precisely the termwise bound `|S_n(chi)| <= (j-1) 2^(n/2)`.  The missing
factor `ell` must therefore come from the `chi` direction, whose field is `F_2`.
Deligne's theorem on a variety `X/F_q` of any dimension `d` gives
`|sum_(X(F_q))| <= (sum of Betti numbers) q^(d - 1/2)`: a relative saving of
`q^(-1/2)`, **independent of `d`**.  At `q = 2` that saving is `0.707`.  Better
Betti constants (quantitative sheaf theory, homological stability) improve the
constant and never the exponent.  Concretely, Katz's own Theorem 8.2 shape
closes the endpoint as soon as `sqrt(q) >~ dim(Xi) . ell`, i.e. for `q`
polynomially large in the representation size -- and never for fixed `q`.

Cohomologically sharpened: what is needed at `q = 2` is not a Betti *bound* but
near-total *vanishing*.  Writing the family sum via Weil II on `Prim_ell` (dim
`ell`), `|sum| <= sum_i h^i_c 2^(i/2)`, and the requirement `<= C 2^ell` forces

```text
h_c^(2ell) = 0   (automatic: the hook reps are nontrivial on SL(ell-1) subset G_geom)
h_c^(2ell-1) = O(1),   h_c^(2ell-j) = O(2^(j/2)).
```

`h_c^(2ell-1) = O(1)` for a sheaf of rank `ell-1` with `SL(ell-1)` monodromy on
an `ell`-dimensional base is an extremely strong demand, and it is the honest
form of what "(AG)" has to become for the FIRST moment.  I record this as the
decisive obstruction of my field: **at `q = 2` the geometric machinery must
supply vanishing, not boundedness, and no equidistribution technology supplies
vanishing.**

Equivalently, in Boolean-analysis terms: the `chi`-direction sum is an
exponential sum in `ell` variables over `F_2`.  Over a fixed field of size 2,
square-root cancellation is available only for phases of algebraic degree `<= 2`
(quadratic forms / bent functions) or for structured Gauss/Kloosterman shapes.
The lane has already measured that the relevant phase is genuinely high degree
(full-support ANF with odd top coefficient; nonquadratic fibres reaching degree
seven; zero generalized-bent fibres in the pinned witness; rank-zero
second-trace pairs killing the Kerdock model).  The Boolean and the geometric
statements of the barrier agree.

**Which average is least damaging?**

- **over `q`** -- forbidden: `q = 2` IS the theorem.  Every published
  equidistribution result for this family (Katz KR, Katz EKR, Sawin
  arXiv:1805.04330, Keating-Rudnick) secretly uses this one.
- **over the endpoint degrees `n = 2ell+1, 2ell+2`** -- **REFUTED as useful, on
  two independent grounds.**  Logically, Lemire needs *both* degrees, so an
  average is not a sufficient statement.  Probabilistically, both powers exceed
  every `N_chi`, so by Rains/Diaconis-Shahshahani the two traces are (in the
  model) independent; averaging two independent quantities buys at most
  `sqrt(2)`, against a needed factor `ell`.  My measured table agrees: the odd
  and even rows have independent-looking signs and comparable magnitudes
  (`avg D_1^2/((ell-2) mean)` is `1.567` odd vs `1.097` even).
- **over `n` more broadly** -- not available at fixed `ell`, because Lemire ties
  `ell = floor(n/2)`.  Averaging over `n` therefore means averaging over `ell`,
  i.e. delivering a density-one-in-degree result.  That is a genuine partial
  theorem (strictly stronger than the current "degrees <= 400 plus 95 infinite
  rays") and is the least damaging *external* average.  Its RMT engine would be
  a no-coincidence / linear-independence statement for the inverse roots across
  the family: `sum_(n <= T) |A_n|^2 = T . D + (off-diagonal)` with `D ~ ell
  2^ell`, giving `#{n <= T : |A_n| > 2^ell} <= T ell 2^(-ell)`.  Relevant
  published technology exists: Cha-Fiorilli-Jouve-type "generic linear
  independence of the roots of L-functions of characters over function fields"
  (arXiv:1903.05491).
- **over the conductor level `j`** -- the only *internal* average, and the one
  the lane has already selected (conductor filtration, martingale, Witt-cylinder
  `R_j(b) <= ell`).  In probabilistic language the local target is a Carleson /
  square-function condition on the conductor martingale, and the aggregate
  target `R_0 <= 4` is its root case.  I endorse this as the correct choice: it
  is the unique averaging direction that does not change the theorem being
  proved.
- **over the ray class `e`** -- forbidden: Lemire is the identity class alone.
  Note also that the family is its own Fourier dual here, so a *full* design
  statement ("all `D_e` small") is equivalent to the problem itself and adds
  nothing.  The useful content of the design framing is exactly the
  strictly-weaker aggregated moment `K_4 <= M_2^2`.


### Dead ends recorded (so they are not re-walked)

- **Katz KR Theorem 1.2 / 8.1 as a black box.**  Dead twice over: wrong limit
  (`q -> infinity`), and the statistic `Tr(A^n)` is not a `PU`-class function
  while the theorem only equidistributes in `PU`.
- **Katz KR Theorem 8.2 (the `p`-independent constant).**  Dead: hypothesis
  `p > 2n - 1` is `2 > 2 ell - 1`, false for every `ell >= 2`.
- **Katz EKR tuple independence (the natural home of a 4-design).**  Dead at
  `p = 2` for a structural reason: Theorem 2.2 needs `p` not dividing
  `ab(a^2-b^2)`, and that quantity is even for all distinct `a, b >= 1`.
- **Quantitative sheaf theory as the fix for Katz's uncontrolled `C(p,n,Xi)`.**
  It is the right tool for that constant, but the constant is not the obstacle:
  the obstacle is the exponent `q^(-1/2)` at `q = 2`.
- **Any Holder / higher-moment bound on the character side.**  Proved above to
  lose exactly `sqrt(ell)` for every moment order.
- **Averaging the two endpoint degrees.**  Refuted logically and
  probabilistically.
- **Reading `K_4 <= M_2^2` as a consequence of large `SL` monodromy.**  Already
  refuted by the lane with an exact witness; my contribution is only the reason:
  monodromy of the universal sheaf controls *pointwise* moments of one matrix,
  while `K_4` is a mixed moment of four family members tied by a group relation,
  which needs fibre-product monodromy over `{chi_1 chi_2 chi_3 chi_4 = 1}`.

## FINDINGS

### (a) Sharpest reformulation in random matrix theory

Let `Prim_ell(F_2)` be the `2^(ell-1)` primitive Hayes characters mod
`x^(ell+1)`, `theta_chi in U(j_chi - 1)` the unitarized Frobenius class, and
`n in {2ell+1, 2ell+2}`.  Then:

> **(RMT-Lemire)**  The empirical mean over the family of the single class
> function `p_n : A |-> Tr(A^n)` is `O(1)`, where the trivial bound is the
> matrix dimension `ell - 1` and the Haar value is `0`.

Three exact contextual facts make this the right frame:

1. **Rains regime.**  `n >= 2 N_chi + 3` for every member, so the Haar model is
   the *exact* finite-`N` law "`N` iid uniform phases" (Rains 1997), not an
   asymptotic approximation.  Consequently `E|Tr|^2 = N` and
   `E|Tr|^4 = 2N^2 - N` exactly, and traces at different powers `>= N` are
   independent in the model.
2. **The required design order is `n ~ 2 ell`, not 2 or 4.**  `Tr(A^n)` has
   degree `n` in the entries, so no *exact* design of size `2^(ell-1)` can
   exist; only a one-function approximate statement is possible.
3. **The needed cancellation is logarithmic, not square-root.**  Trivial is
   `ell . 2^ell`, needed is `O(2^ell)`, and the model says the truth is
   `sqrt(ell) 2^(ell/2)`.  The measured margin (26 exact endpoint rows,
   `4 <= ell <= 16`) is `w/need` falling from `0.156` to `0.0025`.

**`K_4 <= M_2^2` is exactly a convolutional 4-design assertion**: it says the
constrained fourth moment `sum_(chi_1 chi_2 chi_3 chi_4 = 1) prod S_(chi_i)`
exceeds the independent-Haar (Wick) value `3 M_2^2` by at most a factor `4/3`;
equivalently the discrepancy vector has excess kurtosis `<= 1`.  Its published
order-3 analogue is Katz-EKR Theorem 3.1 (triples `(chi, Lambda, chi Lambda)`),
proved for `p >= 7` and `q -> infinity`.  It is **not** the pointwise 4-design
that `SL`-monodromy supplies, which is the tensor-contraction mismatch the lane
already pinned exactly.

### (b) Most promising transferable technique

**Homological stability for the moduli of the family**, i.e. the
Bergstrom-Diaconu-Petersen-Westerland (arXiv:2302.07664) plus
Miller-Patzt-Petersen-Randal-Williams (arXiv:2402.00354) circle, backed by
Sawin-Forey-Fresan-Kowalski complexity bounds (JAMS 36 (2023) 653-726,
arXiv:2101.00635) for the constants.  It is the only technology I could verify
that produces **conductor-uniform cohomological input at fixed `q`** -- exactly
the gap Katz names in his own paper ("we do not know uniform bounds for these
sums of Betti numbers").  Honest caveats, which I do not want minimized: their
theorem is stated for "all large enough prime powers `q`", the family is tame
quadratic (braid groups / Hurwitz spaces for `Z/2` covers), a wild
Artin-Schreier-Witt char-2 analogue does not exist in the literature, and even
perfect Betti control leaves the `q^(-1/2)` exponent untouched.

Second, and cheaper to act on: **the fixed-`q` moment method of
Entin (arXiv:1105.5517) and Bucur-David-Feigon-Lalin-Sinha (arXiv:1111.4701)**,
which really does run at fixed `q` with growing conductor, by exact independence
of character values plus the method of moments.  Its budget runs out at `n = ell`
and the endpoint needs `n = 2 ell`; quantifying that shortfall precisely (rather
than the vague "half the randomness") is a bounded and worthwhile piece of work,
and it is the direct function-field mirror of the `[x, x+sqrt(x)]` wall.

Third, for the *density-one-in-degree* weakening: **generic linear independence
of the inverse roots** (Cha-Fiorilli-Jouve, arXiv:1903.05491) turns
`sum_(n<=T)|A_n|^2 = T . D + off-diagonal` into an exceptional-set bound.

### (c) Decisive obstructions

1. **The `q^(-1/2)` exponent.**  Deligne/Weil II on a base of dimension `d`
   gives relative saving `q^(-1/2)` *independent of `d`*.  Our family is large
   because `dim Prim_ell = ell` grows, not because `q` grows.  At `q = 2` the
   saving is `0.707` and the requirement is `1/ell`.  No Betti/complexity
   improvement changes an exponent.  Cohomologically the requirement becomes
   `h_c^(2ell-1) = O(1)` and `h_c^(2ell-j) = O(2^(j/2))` -- **vanishing, not
   boundedness**.
2. **Every equidistribution theorem for this exact family fixes the conductor
   and sends `q -> infinity`** (Katz IMRN 2013 Thm 1.2/8.1; Katz IMRN 2015
   Thms 1.2, 1.3, 3.1, 3.2; Sawin arXiv:1805.04330; Keating-Rudnick IMRN 2014).
   The survey literature states the barrier in as many words: "when the base
   finite field is fixed and the genus of the family goes to infinity, one
   cannot make use of the equidistribution results."
3. **`p = 2` is excluded by the tuple results for a structural reason**, not a
   technical one (Katz EKR Thm 2.2 needs `p` coprime to `ab(a^2-b^2)`).
4. **The universal `sqrt(ell)` Holder loss** (proved above): no moment order on
   the character side can close the endpoint, because absolute values destroy
   exactly the phase that the Rains model says carries the cancellation.
5. **Design language adds no information by itself**: the family is its own
   Fourier dual, so a full design statement is equivalent to the conjecture.
   Only the strictly weaker aggregated statement (`K_4 <= M_2^2`) has content.

What is NOT an obstruction, and should be booked as a proved asset:
**`SL(ell-1) subset G_geom` holds at `p = 2` for every `ell >= 4`** (Katz KR
Theorem 5.1, exceptions only `(p,n) = (2,3)` and `(5,3)`).

### (d) Concrete next experiments runnable here

1. **Betti stopping test for the FIRST moment, in Katz's own regime.**  The lane
   already has the `GF(2^r)` connected-trace machinery (`gf2_extension`,
   sharded).  Point it at the *first* moment: for small fixed `ell` compute
   `A_n(q) = sum_chi Tr(theta_chi^n)` over `GF(q)`, `q = 2^r`, and fit the
   `q`-degree of `A_n(q) . q^(1/2 - ell)`.  The fitted leading coefficient is a
   direct measurement of `h_c^(2ell-1)` for the Adams sheaf `psi^n L_univ`.
   **If it grows with `ell`, the geometric first-moment route is dead by
   measurement, and the lane can stop pricing (AG)-style Betti budgets.**  This
   is the cheapest decisive experiment I can name and it reuses existing code.
2. **Eigenvalue-coincidence census.**  For `ell <= 10` compute all `L`-polynomials
   and test whether distinct characters share inverse roots beyond
   Galois/conjugation-forced coincidences.  Decides whether the
   density-one-in-degree route has an off-diagonal obstruction before anyone
   invests in it.
3. **Rains-law goodness of fit.**  For `ell <= 12` compare the empirical law of
   `Tr(theta_chi^n)` over the family against the exact "sum of `N` iid uniform
   unit vectors" law (explicit Bessel-type density).  The order-4 deviation is
   exactly `K_4`; the order-6 and order-8 deviations would say whether `R_0 <= 4`
   is the first of a whole family of true design bounds or an isolated accident.
4. **Extend the margin table.**  Push the `w`, `w/need`, `|D_1|^2/(ell . mean)`
   columns from `ell <= 16` to `ell <= 22` (about `2^24` `Lambda` evaluations;
   trivial in Rust, out of reach in Python).  A drift in
   `avg D_1^2/(ell . 2^(n-ell))` away from `1` would be the first evidence that
   the Keating-Rudnick variance law fails at `q = 2`, which would be a genuine
   discovery and would also re-price the whole conjecture.
5. **Hook-by-hook decomposition.**  `p_n|_(U(N)) = sum_(r=0)^(N-1) (-1)^r
   s_((n-r,1^r))`.  Compute `sum_chi s_lambda(theta_chi)` per hook at small
   `ell`.  If the cancellation is concentrated in a few hooks, a targeted
   representation-level lemma becomes possible; if it is spread evenly, the
   Foulkes/cyclic route is confirmed as the only handle.

### (e) New to the ledger

- **PROVED input, currently under-recorded:** Katz KR Theorem 5.1 gives
  `SL(ell-1) subset G_geom subset G_arith subset GL(ell-1)` at `p = 2` for all
  `ell >= 4`; exceptions are only `(p,n) = (2,3)` and `(5,3)`.
- **Precision correction:** Katz's Theorems 1.2/8.1 equidistribute in `PU`, and
  the determinants provably do *not* equidistribute (`G_arith subset
  {det^(4 p^(r+1)) = 1}`).  `Tr(A^n)` is not a `PU`-class function, so those
  theorems do not apply to our statistic even in their own regime; only
  Theorem 5.1 plus Weil II does.
- **Exact hypothesis table** for the five Katz-EKR tuple theorems, showing
  `p = 2` excluded in every one, and Theorem 3.1 identified as the published
  order-3 case of the live order-4 target.
- **PROVED (elementary):** the universal `sqrt(ell)` Holder loss.  Explains, as
  one phenomenon, the ledger's `304`/`633`, Hast-Matei `(ell-1)/2` and
  `(ell-1)/4`, and the connected high-frequency `1425`/`1483` shortfalls, and
  proves no moment order on the character side can ever close the endpoint.
- **REFUTED (with reasons):** averaging the two endpoint degrees, on both
  logical and probabilistic grounds.
- **OPEN, new measurement:** the Keating-Rudnick variance law appears to hold at
  `q = 2` with growing conductor -- `average of D_1^2/(ell . 2^(n-ell)) = 1.0063`
  over 26 exact endpoint rows, `4 <= ell <= 16`.  Finite evidence, not a theorem.
  Note that proving it would *still not* close the endpoint, by the Holder
  obstruction.
- **New quantitative framing:** the endpoint requirement in cohomological terms
  at `q = 2` is `h_c^(2ell-1) = O(1)`, i.e. vanishing rather than a Betti bound;
  and Katz-Theorem-8.2-shaped technology closes the endpoint as soon as
  `sqrt(q) >~ dim(Xi) . ell`, hence never at fixed `q`.
- **New reformulation:** the fixed-`q` independence/CLT methods (Entin;
  Bucur-David-Feigon-Lalin-Sinha) have an independence budget that expires at
  `n = ell`, and the Lemire endpoint is at `n = 2 ell` -- exactly double.

## References (all fetched and read this session, 2026-08-20)

- N. M. Katz, *Witt Vectors and a Question of Keating and Rudnick*, IMRN 2013
  no. 16, 3613-3638.  `https://web.math.princeton.edu/~nmk/wittchar25.pdf`
  (also `wittchar31.pdf`).  Proves: Thm 5.1 `G_geom` contains `SL(n-1)` in all
  characteristics incl. 2 (`n >= 3`, exceptions `(2,3)`, `(5,3)`); Thm 1.2/8.1
  equidistribution in `PU(n-1)` for `n` fixed, `q -> infinity`; Thm 8.2 a
  `p`-independent Weyl-sum bound valid only for `p > 2n-1`.
- N. M. Katz, *Witt Vectors and a Question of Entin, Keating, and Rudnick*,
  IMRN 2015 no. 14, 5959-5975.
  `https://web.math.princeton.edu/~nmk/witthcharindepall20.pdf`.  Proves tuple
  independence; every statement needs `q -> infinity` and excludes `p = 2`.
- W. Sawin, *The equidistribution of L-functions of twists by Witt vector
  Dirichlet characters over function fields*, arXiv:1805.04330.  Our exact
  modulus ("conductor a fixed power of a degree one prime"), arbitrary Galois
  representation twists, plus independence -- in the `q -> infinity` limit.
- J. P. Keating, Z. Rudnick, *The variance of the number of prime polynomials in
  short intervals and in residue classes*, IMRN 2014 no. 1, 259-288,
  arXiv:1204.0708.  `q -> infinity`; explicitly built on Katz's equidistribution.
- A. Entin, *On the distribution of zeroes of Artin-Schreier L-functions*,
  arXiv:1105.5517.  Short-interval zero statistics agreeing with a random
  unitary model.
- A. Bucur, C. David, B. Feigon, M. Lalin (with Sinha), *Distribution of zeta
  zeroes of Artin-Schreier curves*, arXiv:1111.4701.  **`q` fixed, genus ->
  infinity**; Gaussian law for zero counts in the global and mesoscopic regimes.
  The nearest published work to our regime.
- C. David, *Curves and zeta functions over finite fields*, Arizona Winter School
  2014 notes, `https://swc-math.github.io/aws/2014/2014DavidNotes.pdf`.  States
  the barrier: fixed base field plus growing genus puts one outside Katz-Sarnak.
- W. Sawin, A. Forey, J. Fresan, E. Kowalski, *Quantitative sheaf theory*,
  J. Amer. Math. Soc. 36 (2023) 653-726, arXiv:2101.00635.  Betti bounds from
  complexity, uniform in the characteristic; applications to horizontal
  equidistribution.
- J. Bergstrom, A. Diaconu, D. Petersen, C. Westerland, *Hyperelliptic curves,
  the scanning map, and moments of families of quadratic L-functions*,
  arXiv:2302.07664; with J. Miller, P. Patzt, D. Petersen, O. Randal-Williams,
  *Uniform twisted homological stability*, arXiv:2402.00354.  CFKRS moments at
  fixed (large) `q` via stable homology -- the only conductor-uniform fixed-`q`
  cohomological technology I could verify.
- E. M. Rains, *High powers of random elements of compact Lie groups*, Probab.
  Theory Related Fields 107 (1997) 219-241.  `U^m` for `m >= N` has exactly `N`
  iid uniform eigenvalues.
- P. Diaconis, M. Shahshahani, *On the eigenvalues of random matrices*, J. Appl.
  Probab. 31A (1994) 49-62.  `(tr M, ..., tr M^k) -> (sqrt(j) Z_j)` iid normal,
  by the method of moments.
- B. Cha, D. Fiorilli, F. Jouve (and successors), *Roots of L-functions of
  characters over function fields, generic linear independence and biases*,
  arXiv:1903.05491.  Input for a density-one-in-degree weakening.
