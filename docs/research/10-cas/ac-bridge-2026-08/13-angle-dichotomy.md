# AC-Bridge workstream C: the dichotomy / delocalization angle

Phase-2 workstream **C** of the board (`10-angles-board.md`): formalize a
Green--Sawhney-style dichotomy on `G_ell`'s conductor filtration, design the
increment side to collide with a PROVED fact, keep clear of sweep-09's
uncertainty-principle lemma, and decide diary 01's open items `(L2-3)` and
`(L2-4)`.

Date opened: 2026-08-20.
Worktree: `/home/mjbommar/projects/personal/axeyum-gf2-lemire`.
Charter: `00-charter.md` (notation `G_ell`, `D_e`, `S_chi`, `M_2`, `M_4`,
`K_4`, `R_0`, `Sigma(ell)`, ladder L0..L4).

Epistemic labels are the project's: **PROVED** (argument written out here),
**REFUTED** (with an exact witness), **OPEN**.  Finite computation is evidence,
never a theorem.  Literature is fetched and quoted, never recalled.

New files written by this workstream (new examples only; no existing source
file was touched):

```text
crates/axeyum-cas/examples/acb_dic_profile.rs   conductor localization profile
crates/axeyum-cas/examples/acb_dic_support.rs   support-resolved mass (L2-3)
```

## Log

### 2026-08-20 -- required reading

Read `00-charter.md`, `10-angles-board.md`, all 949 lines of
`01-lit-hypercontractivity.md`, `04-weak-target-verification.md`, and
`../adhoc-blocker-sweep-2026-08-20/09-additive-combinatorics.md`.  Inspected
the lane machinery this workstream consumes:
`ClassPopulationDistribution::fourth_moment_conductor_decomposition`,
`::witt_cylinder_concentration`, `::efron_stein_spectral_weight_report`,
`low_conductor_weil_split`, `translation_paired_conductor_level`,
`principal_unit_structure`.

Two filtrations are in play and the whole workstream depends on not confusing
them.  Fixing names for this file:

```text
CONDUCTOR filtration (a):  G_ell -> E_j  (truncate mod x^(j+1)),
   H_j := ker,  |H_j| = 2^(ell-j),  cylinder B_j(b) = coset of H_j.
   The repo's `B_j(b)` / `witt_cylinder_concentration` /
   `fourth_moment_conductor_decomposition` all use THIS one.
   "Codimension j" = level j = 2^j cylinders.  LOW conductor = LOW codimension.
   Characters trivial on H_j = characters of conductor level <= j.

WITT / coordinate filtration (b):  G_ell = prod_(i odd<=ell) Z/2^(k_i);
   a layer is a coordinate SUBSET S.  This is the Efron--Stein grading of
   diary 01, and it is NOT the conductor filtration: H_j is a product of
   SUB-level subgroups of every coordinate at once, not a coordinate subgroup.
```

Charge item 3 (`(L2-3)`) lives in (b); charge items 2 and 4 live in (a).

### 2026-08-20 -- Green--Sawhney fetched and read from the primary text

`https://arxiv.org/pdf/2411.17448v2` downloaded (508653 bytes, 35 pages,
v2 of 10 Jan 2025) and extracted with `pdftotext -layout`.  Title in the
primary text is **"New bounds for the Furstenberg--Sarkozy theorem"** (diary
01 quotes it, via Keller--Lifshitz--Marcus, as "Improved bounds for ..." --
that is the v1 title; the arXiv listing page still shows the old one).

**Theorem 1.2, verbatim from the fetched text.**

> Set `C_0 := 2^13`.  Let `alpha in (0,1/2)` and let `X >= 1` be parameters
> with `alpha > 2X^(-1/2)`.  Let `Q` be a set of pairwise coprime positive
> integers such that `max_{q in Q} q <= X^(1/32 log(1/alpha))`.  Let
> `1 <= d <= 2^(-7) log(1/alpha)`.  Let `f : [X] -> C` be a function with such
> that `|f(x)| <= 1` for all x.  Then either
>
> `sum_{S subset Q, |S|=d} sum_{a mod prod_{q in S} q, q in S => q does not divide a} |fhat(a/prod_{q in S} q)|^2 <= alpha^2 X^2 (C_0 log(1/alpha)/d)^d`,
>
> or else for some set `S subset Q`, `1 <= |S| <= 2 log(1/alpha)`, and for some
> `r in Z`, the average of `|f(x)|` on the progression
> `P = {x in [X] : x = r (mod prod_{q in S} q)}` is greater than `2^|S| alpha`.

This confirms diary 01's transmitted statement (which came from
Keller--Lifshitz--Marcus's quotation) verbatim, including `C_0 = 2^13` and
both parameter windows.  The remark after it is also worth recording: "At the
cost of changing `C_0`, one may replace the condition of finding a progression
of density `2^|S| alpha` with a progression of density `lambda^|S| alpha` for
any fixed `lambda >= 1`."

**The mechanism, extracted (Sections 2--4), with hypotheses named.**

1. The group is `G_Q = prod_{q in Q} Z/qZ ~ Z/(prod q)Z` **by CRT** -- this is
   where pairwise coprimality is used, and it is used twice: to have a product
   group at all, and to make "restrict a coordinate" equal "pass to a
   subprogression" (their Lemma 3.2's commuting square).
2. The layering is by exact conductor: `Supp(xi) = {q : xi_q != 0 (mod q)}`,
   `|xi| = |Supp(xi)|`, and `W_d` is the level-`d` Fourier multiplier.  Their
   note in the proof of Theorem 1.2 is explicit: "the weight `d` elements
   `xi in Ghat_Q` are precisely the elements `a/prod_{q in S} q`, where
   `|S| = d` and `q in S => q` does not divide `a`."
3. The increment side is *literally the negation of a globalness hypothesis*.
   **Definition 4.1**, verbatim: "We say `f` is `(r,alpha,d)`-integer-global
   with respect to `P,Q` if, for every subprogression
   `P' = {x in P : x = a (mod prod_{q in S} q)}`, where `S subset Q` is a set
   of cardinality at most `d`, the average of `|f(x)|` on `P'` is at most
   `r^|S| alpha`."  The proof of Theorem 1.2 opens: "If `f` is not
   `(2, alpha, 2 log(1/alpha))`-integer-global then the second clause of
   Theorem 1.2 holds, so we may suppose `f` does satisfy this condition."
4. Given globalness, the level inequality is proved by **induction on `d`**,
   using (i) `D_{S,x} W_d = W_{d-r} D_{S,x}` (their Lemma 2.4), (ii) the
   *hereditary* property of integer-globalness, (iii) the lifting Lemma 3.4
   which pays `alpha^{2m} X^{-1/4}` for replacing the pushforward measure by
   Haar, and (iv) Keller--Lifshitz--Marcus global hypercontractivity as their
   Theorem 2.5, `||T_rho f||_p^p <= ||f||_2^2 gamma^(p-2)` for
   `(r,gamma)`-derivative-global `f` and `rho <= min(r^(-(p-2)/p) p^(-1), p^(-1/2))/(3 sqrt 2)`.

**The single structural fact that makes the dichotomy work**, and it is the
one that transfers: `|f| <= 1` **caps the increment**, hence caps the
codimension of the cylinder the increment can live on.  An average of `|f|`
above `2^|S| alpha` is impossible once `2^|S| alpha > 1`, so
`|S| <= log_2(1/alpha)` automatically.  Everything else in the paper is
quantitative bookkeeping around that cap.

**Section 9 is a limitation theorem and it should be read before importing
anything.**  Proposition 9.1 (verbatim hypotheses:
`exp(-(log X)^(3/4-eta)) <= alpha <= alpha_0(eta)`) constructs `f : [X] -> [0,1]`
with `E f = alpha`, at most `alpha^2 X^(3/2)/100` square differences, and *no*
subprogression longer than `X exp(-log(1/alpha)^(1/3))` on which the density
doubles.  Green and Sawhney's own reading, verbatim: "the density increment
method cannot give a bound on `s(X)` superior to
`s(X) << X exp(-c (log X)^(3/4))`".  So the dichotomy shape has a known
ceiling in its home domain; that is a warning about how much a transplant can
be expected to buy, not a refutation of the transplant.

### 2026-08-20 -- calibration: GS's theorem is VACUOUS at our density.  REFUTED as an import.

Our physical space is the `2^n` monic degree-`n` polynomials and our weight is
von Mangoldt.  The `1`-bounded function is `f = Lambda/n` (`Lambda <= n` on
degree `n`), and since `sum_F Lambda(F) = 2^n`,

```text
alpha := E_F [ Lambda(F)/n ] = 1/n = 1/(2 ell + 1)   (odd endpoint).
```

So `L := log(1/alpha) = log n ~ log(2 ell)`.  Feed that into the two parameter
windows of Theorem 1.2:

```text
level window     1 <= d <= 2^(-7) L   ->  needs L >= 128, i.e. n >= e^128
increment window 1 <= |S| <= 2L       ->  |S| <= 2 log(2 ell)
```

**REFUTED (import), witness = the parameter window.**  For every `ell` below
`e^128/2` the admissible level set is empty and Theorem 1.2 says nothing at
all.  This is not the constant `2^(-7)` being unoptimised: the *shape*
`d <= c log(1/alpha)` is intrinsic (it is what makes `(C_0 L/d)^d` a saving),
and our `1/alpha` is `n`, not `exp(poly log)`.  The global-hypercontractivity
family is calibrated for sparse sets; the irreducibles at density `1/n` are a
*dense* set on that scale.  Recorded so nobody re-imports it.

What survives is the **mechanism**, and in one respect our object is strictly
better than theirs: `G_ell` is an honest finite abelian product group, its
Efron--Stein decomposition is exact (diary 01, charge item 4), there is no
lifting loss (Lemma 3.4 is unnecessary), and the conductor layering is already
computed in tree.  Their hard hypotheses are our free ones.  So the right move
is to build the dichotomy directly rather than transplant the theorem.

### 2026-08-20 -- the dichotomy, built directly on the conductor filtration.  PROVED as an identity.

Write `f_e := D_e^2` (nonnegative, `sum_e f_e = M_2`), and for the
level-`j` cylinders

```text
m_j(b) := sum_(e in B_j(b)) D_e^2 ,      s_j(b) := sum_(e in B_j(b)) D_e ,
C_j    := 2^j sum_b m_j(b)^2 ,           A_j    := sum_b s_j(b)^2 .
```

`C_j` is the repo's cumulative conductor energy: `C_j = sum_{chi : cond(chi) <= j} |fhat(chi)|^2`
by Parseval on `E_j`, with `C_0 = M_2^2` and `C_ell = 2^ell M_4` (both
asserted by `fourth_moment_conductor_decomposition`).

**Lemma D1 (exact two-sided step).  PROVED.**  For every `j >= 1`,

```text
C_(j-1) <= C_j <= 2 C_(j-1) .
```

*Proof.*  The quotient `E_j -> E_(j-1)` is 2-to-1, so each parent cylinder `b`
at level `j-1` has exactly two children with masses `u_b, v_b >= 0`,
`u_b + v_b = m_(j-1)(b)`.  Then
`u_b^2 + v_b^2 <= (u_b+v_b)^2 = m_(j-1)(b)^2` and
`u_b^2 + v_b^2 >= (u_b+v_b)^2/2`, so
`C_j = 2^j sum_b (u_b^2+v_b^2)` lies between `2^(j-1) sum_b m_(j-1)(b)^2 = C_(j-1)`
and `2^j sum_b m_(j-1)(b)^2 = 2 C_(j-1)`.  QED

**Lemma D2 (the exact multiplicative decomposition of the kurtosis).  PROVED.**
Write the relative Haar imbalance of a parent `b` at level `j` as
`t_j(b) := (u_b - v_b)/m_(j-1)(b) in [-1,1]` and let

```text
q_j := < t_j^2 >_w ,   the m_(j-1)(b)^2-WEIGHTED mean square of t_j .
```

Then, for every `j >= 1`,

```text
C_j / C_(j-1) = 1 + q_j ,       0 <= q_j <= 1,
```

and therefore, since `C_0 = M_2^2` and `C_ell = 2^ell M_4`,

```text
R_0  =  2^ell M_4 / M_2^2  =  prod_(j=1)^ell ( 1 + q_j ) .          (D-PROD)
```

*Proof.*  With `u = m(1+t)/2`, `v = m(1-t)/2` one has
`u^2+v^2 = m^2 (1+t^2)/2`, so
`C_j = 2^j sum_b m_b^2 (1+t_b^2)/2 = C_(j-1) (1 + sum_b m_b^2 t_b^2 / sum_b m_b^2)`.
The bracket is `q_j`, in `[0,1]` because `t_b^2 <= 1`.  Telescoping gives
(D-PROD).  Equivalently `q_j = E_j / C_(j-1)` where `E_j = C_j - C_(j-1)` is the
repo's `exact_fourier_energy`, and the repo's own Haar identity
`E_j = 2^(j-1) sum_b (u_b - v_b)^2` is the same statement.  QED

(D-PROD) is the dichotomy machine.  It is exact, it needs no
hypercontractivity, no globalness, and no inequality other than `q_j <= 1`,
which is Cauchy--Schwarz on a two-element split.  Both halves are asserted on
every emitted row by `acb_dic_profile` and a violation aborts the row.

**Theorem D3 (the dichotomy, in the Green--Sawhney shape).  PROVED.**  Let
`P_n` be any valid proper-prime-power bound (Lemma A/B of diary 04) and put
`G := 2^ell (mu - P_n)^4 / (mu Sigma(ell))^2`, so that `R_0 < G` implies
`(WR)`, hence `(W4)`, hence a degree-`n` irreducible in the identity class.
Then, for every `ell` at which `G > 1`, **either**

```text
(DELOC)   prod_(j=1)^ell (1 + q_j)  <  G     [equivalently PR = M_2^2/M_4 > 2^ell/G],
```

**or** for every real `Q in [0,1]` and every set `J` of conductor levels,

```text
(INC)     #{ j in J : q_j > Q }  >  |J| - (ell - log2 G)/(1 - log2(1+Q)) .
```

*Proof.*  If (DELOC) fails then `sum_j log2(1+q_j) >= log2 G`.  Each term is at
most `1` (Lemma D1).  If at least `|J| - k` levels of `J` had `q_j <= Q` then
`sum_j log2(1+q_j) <= ell - (|J|-k)(1 - log2(1+Q))`, and combining gives
`(|J|-k)(1-log2(1+Q)) <= ell - log2 G`.  QED

Asymptotically `log2 G = ell + 2 - 4 log2 ell + o(1)` (diary 04's `(WR)`), so
the increment branch says: **all but `O(log ell)` conductor levels must be
maximally Haar-imbalanced**, i.e. at nearly every refinement of the conductor
filtration the `D^2`-mass of nearly every cylinder (weighted by `m^2`) passes
essentially entirely to one of its two children.  That is the exact analogue
of the GS increment: it is a *localization* statement, extracted from the
failure of the level branch by an exact identity rather than by
hypercontractivity.

**Corollary D4 (the increment made concrete).  PROVED.**  Define the cylinder
participation ratio `PR_j := M_2^2 / sum_b m_j(b)^2 = 2^j C_0 / C_j`.  Then
`PR_j / PR_(j-1) = 2/(1+q_j) in [1,2]`, so `PR_j` is nondecreasing,
`PR_0 = 1`, `PR_ell = PR = M_2^2/M_4`, and failure of (DELOC) forces
`PR_j <= 2^ell/G ~ ell^4/4` at **every** level `j`.  Since
`sum_b m_j(b)^2 <= (max_b m_j(b)) M_2`, failure also forces, at every level,

```text
max_b m_j(b)  >=  M_2 / PR_j  >=  (G/2^ell) M_2  ~  4 M_2 / ell^4 .   (INC-CYL)
```

At the proved Weil cutoff `j = ell - ceil(log2(ell-1)) - 2` a cylinder holds
`2^(ell-j) ~ 4 ell` classes, so (INC-CYL) reads: *some `4 ell` classes carry at
least a `4/ell^4` share of the whole `L^2` mass of the discrepancy*, against an
equidistributed share of `4 ell / 2^ell`.  That is an increment of relative
size `2^ell / ell^5` on a low-conductor cylinder -- exactly the object the
charge asked to collide with the proved Weil equidistribution.

### 2026-08-20 -- the collision: searched, and REFUTED, with an exact witness

**The proved fact to collide with.**  From `low_conductor_weil_split` and the
character-count/`L`-degree bookkeeping in tree: the `2^(i-1)` characters of
exact conductor level `i` have `L`-degree at most `i-1`, so RH for
function-field Dirichlet `L`-functions gives `|S_chi| <= (i-1) 2^(n/2)`.
Since `s_j(b) = 2^(-j) sum_{chi != 1, cond <= j} conj(chi(b)) S_chi` and
`S_1 = 0`,

```text
|s_j(b)|  <=  2^(-j) W_j 2^(n/2) ,      W_j := sum_(i=2)^j (i-1) 2^(i-1) = (j-2)2^j + 2 .   (WEIL-CYL)
```

Divided by the cylinder mean `2^(n-j)`, this is a *relative* equidistribution
statement with elevation at most `(j-2) 2^(j-n/2)`, below `1` exactly for
`j <= ell - log2 ell + O(1)`.  That is the sense in which "a cylinder of low
codimension is a low-conductor event".

**REFUTED, with an exact and machine-checked witness.**  The extremal failure
configuration is a single-class spike: `D` concentrated on one class `e_0` at
the critical height `mu = 2^(n-ell)` (this is precisely the configuration that
saturates `M_4 = mu^4` with the least `M_2`, and it is the configuration
(INC-CYL) is trying to exclude).  Its level-`j` cylinder discrepancy is
`|s_j(b_0)| = mu(1 - 2^(-j)) ~ mu`.  Compare with (WEIL-CYL) by exact integer
squares:

```text
spike excluded at level j   <=>   mu^2 2^(2j)  >  W_j^2 2^n
                            <=>   2^(n - 2 ell + 2j)  >  W_j^2
odd endpoint  (n = 2 ell+1):      2^(j + 1/2)  >  (j-2) 2^j + 2
even endpoint (n = 2 ell+2):      2^(j + 1)    >  (j-2) 2^j + 2
```

Both fail from `j = 4` onwards, for every `ell`.  `acb_dic_profile` emits
`critical_spike_excluded` per level as an exact integer comparison; over
`ell = 2..19`, both parities, **the critical spike is excluded at `j <= 3` and
at no level `j >= 4` on any row** -- in particular at no level inside the
proved Weil window once that window reaches level 4, i.e. at every
`ell >= 10` (the measured cutoffs are `1,2,3,3,4,5,6,7,8,9,10,10,11,12` for
`ell = 6..19`).

The reason is a scale coincidence and not a technical gap.  At the Lemire
endpoint `n - ell = n/2 + 1/2`, so the mean `mu = 2^(n-ell)` and the Weil error
scale `2^(n/2)` **coincide to within `sqrt 2`**.  A Weil-strength
equidistribution statement therefore has *no margin at all* against a
configuration of the critical height, at any conductor level.  Any collision
design that asks "does the increment violate low-conductor equidistribution?"
answers "no" for a reason that no sharpening of the low-conductor input can
repair, because the input is already sharp (individual RH).

Two further collision partners named in the charge, checked and dismissed:

* **Lemma A/B positivity constraints** cannot collide.  They bound `Pi_n` and
  enter only through the threshold constant `(mu - P_n)^4`, i.e. through `G`.
  They are a scalar in the inequality, not a constraint on the shape of `D`.
* **The sibling-difference / Haar identities** are not a collision partner:
  they are the *machine* (Lemma D2 is exactly the repo's
  `haar_difference_square_sum` identity read multiplicatively).  Using them
  twice would be circular.

**And the deeper reason the naive collision was never going to work**, stated
so that it is not re-attempted: the increment produced by an `L^2`-mass
extraction is a bound on `max_b m_j(b)`, a *second*-moment localization of `D`;
the proved low-conductor equidistribution bounds `max_b |s_j(b)|`, a *first*-moment
localization.  Cauchy--Schwarz relates them only as
`m_j(b) >= 2^(j-ell) s_j(b)^2`, which is the useless direction.  The two-sided
bridge is the identity

```text
fhat(chi) = sum_e D_e^2 chi(e) = 2^(-ell) sum_psi S_psi conj( S_(psi chi) ) ,   (TWIST)
```

for which individual Weil gives only `|fhat(chi)| <= 2^(-ell) sum_psi |S_psi|^2 = M_2 = fhat(1)`,
i.e. nothing.  (TWIST) is verified by Fourier inversion:
`D_e = 2^(-ell) sum_psi S_psi conj(psi(e))`, square, sum against `chi`, use
orthogonality, then `S_(psi^(-1)) = conj(S_psi)` since `D` is real.

### 2026-08-20 -- the uncertainty principle, and the escape.  Written out carefully.

Sweep-09's lemma (16:30), restated: any `m : G -> R` measurable for the
conductor-`<=a` filtration with `a < ell` and `m <= delta_1` pointwise
satisfies `m <= 0`, so a Beurling--Selberg minorant built from proved
low-conductor equidistribution gives no positive lower bound on `N_1`.  The
sweep's own conclusion was "all the information must come from the top
`O(log ell)` levels".

The charge's suggested escape is that the increment "produces an `L^2`-mass
localization, a different object".  That is true but it is **not** the escape,
because the previous entry shows the `L^2` localization has nothing proved to
collide with.  The escape that actually works is a different one, and it is
worth stating precisely because it looks at first like a violation of the
uncertainty lemma:

> **Low-conductor levels ARE usable, in multiplicative bookkeeping, because
> (D-PROD) composes a low-conductor input with a PROVED top-conductor input.**

The minorant method uses *only* the low-conductor data and asks it to produce
positivity by itself; the uncertainty lemma says it cannot.  Route (D-PROD)
uses low-conductor data (`q_j` small for `j` in some set `J`) *times* the proved
bound `q_j <= 1` at every other level (Lemma D1, which is a genuine theorem --
Cauchy--Schwarz on the binary refinement -- not a triviality of the filtration).
The product of the two is what bounds `R_0`, and positivity is only extracted
at the very end by Chebyshev at one point (`|D_1|^4 <= M_4`).  No step of that
chain is a minorant measurable at low conductor, so the lemma does not apply.

This is the one genuinely new strategic move this workstream produces, and it
inverts the sweep's conclusion: **there is a route in which the low conductor
levels carry the burden and the top levels are discharged by an already-proved
inequality.**  Everything the ledger currently carries is the other way round.

### 2026-08-20 -- measurement 1: the conductor localization profile

```sh
cargo build --release -p axeyum-cas --example acb_dic_profile
./target/release/examples/acb_dic_profile 2 16    #  6.9 s,  24.8 MB
./target/release/examples/acb_dic_profile 17 19   # 70.1 s, 180.5 MB
```

`acb_dic_profile` recomputes `m_j(b)`, `s_j(b)`, `C_j`, `A_j`, `max_b m_j(b)`
with its own mixed-radix projection and exact `BigInt`/`BigUint` arithmetic,
and asserts on every row: `sum_e D_e = 0`; `sum_b m_j(b) = M_2` at every level;
`C_0 = M_2^2`; `C_ell = 2^ell M_4`; `A_ell = M_2`; `A_0 = 0`; Lemma D1's
`C_(j-1) <= C_j <= 2 C_(j-1)`; and agreement of `C_j` and `E_j` with the
library's `fourth_moment_conductor_decomposition`.  All assertions passed on all
36 rows, `ell = 2..19`, both parities.  The `R_0` column reproduces diary 04's
master table exactly (`(9,19)`: `2.812889857`; `(19,39)`: `3.006346022`).

Summary rows (odd endpoint; `log2 G` is `failure_growth_log2`, the multiplicative
growth a failure of `(WR)` would force; `cut`/`win` are
`low_conductor_weil_split`'s cutoff and unresolved top width):

```text
 ell   n   R_0    log2 R_0   log2 G   margin   sum q_j   q_ell   cut  win  dom@cut  l2frac@cut
  11  23  2.9706   1.571      0.249   -1.322    1.2487  0.4874    5    6   1.3734   3.01e-03
  13  27  2.9487   1.560      1.115   -0.445    1.2438  0.4807    7    6   1.4593   7.52e-03
  15  31  2.9511   1.561      2.164   +0.603    1.2408  0.4865    9    6   1.7499   7.39e-03
  17  35  2.9964   1.583      3.347   +1.764    1.2625  0.5006   10    7   1.7058   3.67e-03
  18  37  2.9627   1.567      3.978   +2.411    1.2478  0.4917   11    7   1.4521   4.45e-03
  19  39  3.0063   1.588      4.630   +3.042    1.2660  0.4973   12    7   1.5186   4.62e-03
```

(The even rows behave identically with `log2 G` about 1.8 bits larger; the
crossover `log2 G > log2 R_0` is at `ell = 14` odd / `ell = 13` even, exactly
diary 04's crossovers, reproduced here from a different computation.)

**Result C1 (measurement).  The per-level Haar imbalance obeys a clean
geometric law: `q_j = (1 + o(1)) 2^(-(ell-j))` for `j <= ell-4`, saturating at
`q_ell -> 1/2`.**  At `(19,39)`, the normalized column `q_j 2^(ell-j)` reads

```text
 j        8      9     10     11     12     13     14     15     16     17     18     19
 q 2^(l-j)  0.969  1.098  0.929  1.071  1.063  0.953  1.010  0.974  0.878  0.812  0.664  0.497
```

so the law holds to within 10 percent over eleven levels, and `q_ell` sits in
`[0.481, 0.508]` on every odd row `ell = 9..19`.  Consequently `sum_j q_j` is
an **absolute constant** in `ell` (`1.24 -- 1.28` over `ell = 11..19`, both
parities), and `prod_j (1+q_j) -> 3`: the Gaussian kurtosis is exactly the
value of the `q`-product for a geometric imbalance profile of ratio 2.

**Result C2 (measurement).  The failure branch is not merely false but false at
every level.**  Failure of `(WR)` needs mean `q_j ~ 1 - O(log ell/ell)`;
measured mean `q_j = 1.27/ell`.  The gap is a factor `ell/1.27` per level and
`2^(ell+2-4log2 ell - 1.59)` in total, and it is *uniform*: at `(19,39)` no
single level even reaches `q_j = 1/2`.

**Result C3 (measurement, and it quantifies the sweep's own conclusion).  The
fraction of `D`'s `L^2` mass visible to the proved Weil window is `~1/(4 ell)`.**
The exact fraction measurable at codimension `<= j` is
`||E[D | F_j]||_2^2/||D||_2^2 = A_j / (2^(ell-j) M_2)`, and it is measured to
match the Keating--Rudnick / exact-conductor law `(j-2)/(ell-2) * 2^(j-ell)` to
three digits across eighteen levels.  At `(19,39)`:

```text
 j            10        13        15        16        17        18        19
 measured  9.06e-4   9.95e-3   4.79e-2   1.033e-1  2.206e-1  4.725e-1  1.000
 law       9.19e-4   9.56e-3   4.78e-2   1.029e-1  2.206e-1  4.706e-1  1.000
```

Half the mass sits at the single top level, a quarter one below, and only
`0.46%` of it lies at or below the Weil cutoff `j = 12`.  Note `A_j` itself is
neither a fraction nor monotone (`A_4 = 5664 > M_2 = 4384` at `(5,11)`); the
correct normalization is the one above, and the example emits it as
`l2_fraction_j`.

**Result C4 (PROVED, small, new).  `q_1 = 0` at the odd endpoint, exactly, for
every `ell`.**  Measured on all 15 odd rows `ell = 5..19` (and on no even row).
*Proof.*  `F(x) -> F(x+1)` is a Mangoldt-preserving bijection of the monic
degree-`n` polynomials.  The coefficient of `x^(n-i)` in `F(x+1)` is
`sum_{m<=i} a_m binom(n-m, i-m)`, which for `i <= ell` depends only on
`a_0..a_ell`, so it descends to a bijection `sigma` of the classes with
`N_(sigma(e)) = N_e`, hence `D_(sigma(e)) = D_e`.  For `n` odd,
`a_1(sigma(e)) = a_1(e) + binom(n,1) = a_1(e)+1`, so the level-1 character
`chi_1 = (-1)^(a_1)` satisfies `chi_1(sigma(e)) = -chi_1(e)`.  Therefore
`fhat(chi_1) = sum_e D_e^2 chi_1(e) = sum_e D_(sigma(e))^2 chi_1(sigma(e)) = -fhat(chi_1) = 0`,
so `E_1 = 0` and `q_1 = 0`.  For `n` even the shift is `binom(n,1) = 0` and the
argument gives nothing, which is exactly what the even rows show.  QED
This is the first rung of the residual ladder below, and it is free.

### 2026-08-20 -- measurement 2: `(L2-3)`, the support-resolved mass profile.  Diary 01's open item, DECIDED.

```sh
cargo build --release -p axeyum-cas --example acb_dic_support
./target/release/examples/acb_dic_support 4 15    #  2.8 s, 14.1 MB
./target/release/examples/acb_dic_support 16 18   # 38.0 s, 65.9 MB
```

`acb_dic_support` computes the **exact** support-resolved Efron--Stein masses
`mass(S) = sum_(chi : supp chi = S) |S_chi|^2` by subgroup Parseval plus
Boolean-lattice Mobius inversion in `i128`, asserts Parseval
(`sum_S mass(S) = 2^ell M_2`) and nonnegativity of every exact mass, and
cross-checks the weight-grouped totals against the library's
`efron_stein_spectral_weight_report`.  It then evaluates diary 01's `(L2-3)`
functional with the sharp Latala--Oleszkiewicz/Wolff costs
`A_S = prod_(i in S) rho_c(2^(k_i))^(-1)`,
`rho_c(m) = sqrt(sinh(u/4)/sinh(3u/4))`, `u = log(m-1)` (`rho_c(2) = 1/sqrt 3`
by the limit), and the same functional on diary 01's uniform-mass model
`f_S^unif = prod_(i in S)(2^(k_i)-1)/2^ell`.

```text
 ell   n  par   log2 (sum_S A_S sqrt f_S)^4   uniform model   measured-uniform   log2 R_0^suf
   9  19  odd            20.731                 20.769            -0.037            -0.350
  11  23  odd            25.066                 24.983            +0.083            +0.249
  13  27  odd            29.185                 29.197            -0.012            +1.115
  15  31  odd            33.463                 33.410            +0.053            +2.164
  16  33  odd            34.073                 34.058            +0.015            +2.741
  17  35  odd            37.906                 37.858            +0.048            +3.347
  18  37  odd            38.289                 38.272            +0.018            +3.978
  18  38 even            38.298                 38.272            +0.027            +5.703
```

**Result C5 (`(L2-3)` REFUTED, with exact masses; and diary 01's prediction
CONFIRMED in sign, REFUTED in magnitude).**

1. The route does not close on any row: `route_closes = false` for all 30 rows,
   `ell = 4..18`, both parities.  The measured bound grows as
   `2^(2.13 ell)` (`38.29/18 = 2.127` at `ell = 18`) against a sufficient
   `2^(ell+2-4 log2 ell)`, a shortfall of `2^(1.13 ell)`.  Diary 01 predicted
   `2^(2.15 ell)` for the support-set-graded variant *under the uniform-mass
   model*; the exact masses reproduce it to two digits.
2. Diary 01's prediction that the true profile is **worse** than the
   uniform-mass model is confirmed in direction: `measured > uniform` on 20 of
   30 rows and on every row with `ell >= 14` except `(13,27)`.  The mass does
   sit slightly more on large supports (full-support share `0.0232` vs the
   model's `0.0224` at `(18,37)`).
3. But it is refuted in magnitude, and this is the useful half: the effect is
   **`+0.02` to `+0.08` bits in total**, not per `ell`.  The uniform-mass model
   was quantitatively right.  **No refinement of the mass profile can rescue
   the hypercontractive route**, because the true profile is the model profile.
4. The coarser weight grading, with the worst support pattern per weight,
   gives `33.727` at `(18,37)` (`1.874` per unit `ell`) against the uniform
   model's `33.702` -- again a `0.025`-bit difference, and again matching
   diary 01's model table (`4 x 0.4656 = 1.862` per unit `ell` at `ell = 20`).

**Consequence for the board.**  Diary 01's item `(L2-3)` moves from OPEN to
REFUTED-with-measurement, and with it diary 01's own conditional: "If that
prediction holds, the hypercontractivity family is closed for this lane."  It
holds.  The family is closed, now on measured masses rather than on a model.

### 2026-08-20 -- independent verification: sympy brute force

`scratchpad/dic_sympy_check.py` enumerates **every** monic polynomial of degree
`n` over `GF(2)`, factors it with `sympy.Poly(..., domain=GF(2)).factor_list()`,
applies the von Mangoldt weight, bins by the top `ell` coefficients, and then
rebuilds -- sharing no code, no algorithm and no coordinate convention with the
CAS -- the class discrepancies, `M_2`, `M_4`, the conductor cylinders (keyed by
*polynomial truncation*, which is basis-free), `C_j`, `A_j`, `q_j`,
`max_b m_j(b)`, the principal-unit Witt coordinates (by explicit discrete
logarithm over the generators `1 + x^i`), the support-resolved masses, and the
`(L2-3)` functional.

```text
SYMPY_DIC|ell=4|n= 9|M_2=1168 |M_4=149776  |R_0=1.756614749|sum_q=0.670122|log2_bound=8.345310 |full_supp=0.554794521
SYMPY_DIC|ell=4|n=10|M_2=1200 |M_4=192576  |R_0=2.139733333|sum_q=0.870833|log2_bound=7.948080 |full_supp=0.606666667
SYMPY_DIC|ell=5|n=11|M_2=4384 |M_4=765472  |R_0=1.274495178|sum_q=0.256409|log2_bound=11.851865|full_supp=0.147810219
SYMPY_DIC|ell=5|n=12|M_2=23584|M_4=73638400|R_0=4.236618806|sum_q=1.748378|log2_bound=12.194935|full_supp=0.244572592
```

Every field agrees **exactly** with `acb_dic_profile` and `acb_dic_support`,
and the per-level tables agree exactly as well -- e.g. at `(4,9)`:
`C_j = 1364224, 1364224, 1401088, 1585408, 2396416`;
`A_j = 0, 0, 256, 768, 1168`;
`q_j = 0, 0, 0.027021955, 0.131554906, 0.511545293`;
`max_b m_j(b) = 1168, 584, 340, 194, 169`.
`M_2`/`M_4` also reproduce diary 04's own sympy rows.  AGREEMENT, no mismatch.

### 2026-08-20 -- the residual lemma, and what it reduces to

Combine Theorem D3 with Lemma D1 in the direction that uses the *low* levels.

**Lemma D5 (sufficiency of a low-conductor delocalization input).  PROVED.**
Let `J` be a set of conductor levels and `Q in [0,1)`.  If `q_j <= Q` for every
`j in J`, then

```text
R_0  <=  2^(ell - |J|) (1+Q)^|J| ,
```

so `(WR)` -- hence `(W4)`, hence the endpoint at that parity -- follows as soon
as `|J| (1 - log2(1+Q)) > ell - log2 G = 4 log2 ell - 2 + o(1)`.
*Proof.*  Immediate from (D-PROD) and `q_j <= 1` off `J`.  QED

Two calibrations, both with the `Sigma(ell)` correction absorbed
conservatively (measured `log2 G` runs *above* `ell+2-4log2 ell`, e.g. `4.63`
vs `4.00` at `ell = 19`):

```text
(CDL-a)   q_j <= 1/2   for  ceil(9.7 log2 ell)  levels      ==> endpoint
(CDL-b)   q_j <= 1/ell for  ceil(4.1 log2 ell)  levels      ==> endpoint
```

For `ell >= 200` -- and the finite range below is separately certified through
degree 400 -- both level counts are a vanishing fraction of `ell`.

**(CDL) [the residual lemma of this workstream], OPEN.**

> There is an absolute constant `c` such that, for all large `ell` and both
> endpoint parities, `q_j = E_j / C_(j-1) <= 1/ell` for every conductor level
> `j <= c log2 ell`; equivalently, writing `fhat(chi) = sum_e D_e^2 chi(e)`,
>
> ```text
> sum_(chi : cond(chi) = j) |fhat(chi)|^2   <=   M_2^2 / ell     for j <= c log2 ell.
> ```

Sufficient pointwise form, since there are `2^(j-1) <= ell^c/2` characters at
level `j <= c log2 ell`:

```text
|fhat(chi)|  <=  M_2 * ell^(-(c+2)/2)     for every chi of conductor level <= c log2 ell.
```

**And by (TWIST) that is a SHIFTED SECOND MOMENT, not a fourth moment:**

```text
| sum_psi S_psi conj( S_(psi chi) ) |   <=   ell^(-(c+2)/2)  sum_psi |S_psi|^2 ,
```

for the `poly(ell)` many fixed twists `chi` of conductor level `O(log ell)`.
At `chi = 1` the left side *is* the right side (`= 2^ell M_2`); the content is
`poly(ell)` decorrelation of the Hayes character-sum family under a fixed
low-conductor twist.  The unshifted case is Keating--Rudnick / the lane's
proved Weil envelope; the shifted case is the same kind of object -- a second
moment of a family of `L`-functions over a function field, computed by
monodromy/equidistribution rather than by a fourth-moment estimate.

**Measured margin for (CDL): exponential and growing.**  Under Result C1's law
`q_j ~ 2^(-(ell-j))`, the binding level `j = c log2 ell` has
`q_j ~ ell^c 2^(-ell)` against a requirement `1/ell`, i.e. a margin
`2^ell / ell^(c+1)`.  Directly measured at fixed low levels, odd endpoint:

```text
 ell      q_2        q_4        q_6        q_8       q_10     ell * q_8
  11   9.90e-04   6.26e-03   3.20e-02   1.27e-01   3.25e-01    1.40
  13   2.63e-05   1.94e-03   9.36e-03   2.90e-02   1.02e-01    0.377
  15   6.05e-05   2.74e-04   2.17e-03   8.69e-03   3.09e-02    0.130
  17   1.02e-05   1.84e-04   6.26e-04   2.40e-03   8.74e-03    0.041
  19   4.33e-07   5.74e-06   8.74e-05   4.73e-04   1.81e-03    0.0090
```

`ell q_8` falls by a factor `~2` per unit `ell`, i.e. `q_j` at fixed `j` decays
like `2^(-ell)`, exactly as Result C1's law predicts.  Contrast the top of the
filtration, where `q_ell ~ 1/2` with no margin at all.

### 2026-08-20 -- comparison with (CAB) and with the ledger's top-conductor obligations

The board's workstream A carries
`(CAB): sum_{a<=b<=c<=d} mult |K_(a,b,c,d)| < 2^(ell+4(n-ell)) - 3 M_2^2`, the
cellwise absolute connected cumulant over the **character-order** decomposition.
The ledger's standing top-conductor obligation is the `unresolved_top_levels`
half of `low_conductor_weil_split`: cancellation among the top
`ceil(log2(ell-1)) + 2` conductor levels of the **`D`-spectrum**.

```text
                    grading            end of it   object    needs cancellation?   size of the obligation
 (CAB)        character order          all cells   K_4       NO (absolute values)   every cell
 top-conductor conductor filtration    TOP         S_chi     YES (cross-level)      2^ell - 2^cutoff chars
 (CDL)        conductor filtration     BOTTOM      fhat=S*S  YES (within a twist)   <= ell^c/2 chars
```

**Verdict: incomparable, and deliberately so.**  Not "the same lemma" and not
"weaker": `(CDL)` and the top-conductor obligation live at opposite ends of the
*same* filtration and concern *different* objects (`S_psi conj(S_(psi chi))`
versus `S_chi`), and `(CDL)` and `(CAB)` use different gradings entirely.  Three
consequences worth recording:

1. `(CDL)` is the **first** obligation in this project that sits at the bottom
   of the conductor filtration.  Everything the ledger carries -- the telescoped
   identity-path reduction, the top-level square-root layer bound, the
   connected-top candidates -- lives at the top, because sweep-09's uncertainty
   lemma appeared to force that.  (D-PROD) is the mechanism that makes the
   bottom usable; the escape is spelled out above.
2. `(CDL)` demands cancellation where `(CAB)` deliberately demands none.  In
   exchange it is `2^ell/ell^c` times smaller as a set of characters, and its
   measured margin is exponential in `ell` where `(CAB)`'s closure ratio decays
   only like `2^(-0.28 ell)` (board item 5) and the top-conductor obligation has
   no measured margin at all (`q_ell -> 1/2`, the extreme of Lemma D1).
3. `(CDL)` is *not* implied by `(CAB)` nor vice versa.  `(CAB)` bounds a sum of
   absolute cell contributions to `K_4` and therefore bounds `R_0` globally --
   which would give the endpoint outright, so `(CAB)` is strictly stronger *as a
   conclusion*.  `(CDL)` is a strictly smaller *hypothesis* that reaches the
   same conclusion through (D-PROD).  A lane that fails to prove `(CAB)` loses
   nothing by also attempting `(CDL)`.

### 2026-08-20 -- what I did not do

* No proof of `(CDL)`, of `(W4)`, of `(WK)`, or of any uniform estimate.  No
  theorem credit is claimed for Lemire's conjecture or any lane lemma.
* No row above `ell = 19` for the profile (`ell = 20` needs `> 4` min and the
  charter budget is 5 min/run) and none above `ell = 18` for the
  support-resolved masses.
* No attempt at the shifted second moment itself; identifying it is the
  deliverable, evaluating it is a Katz/monodromy question and belongs with
  workstream B's machinery.
* `(L2-4)` as diary 01 posed it (an anomalous-`B_j(b)` alternative) is
  superseded rather than tested: Theorem D3 is the same dichotomy with an exact
  increment, and the collision it was designed for is refuted above.

## FINDINGS

### (a) The formalized dichotomy theorem-candidate, and its proof state per branch

**The machine, PROVED (Lemmas D1, D2).**  On the conductor filtration of
`G_ell`, with `q_j` the `m^2`-weighted mean-square relative Haar imbalance of
the `D^2`-mass at level `j`,

```text
C_j/C_(j-1) = 1 + q_j ,   0 <= q_j <= 1 ,   R_0 = 2^ell M_4/M_2^2 = prod_(j=1)^ell (1+q_j).
```

**The dichotomy, PROVED (Theorem D3).**  Either `(DELOC)` -- which is exactly
`(WR)`, hence `(W4)`, hence the endpoint -- or `(INC)`: all but
`(ell - log2 G)/(1-log2(1+Q)) = O(log ell)` conductor levels have `q_j > Q`, and
concretely `(INC-CYL)`: at *every* level some cylinder carries a `~4/ell^4`
share of `M_2`, an elevation of `2^ell/ell^5` at the Weil cutoff.

Proof state by branch:

* **Level / delocalization branch** -- OPEN, and equal to the lane's live
  target.  Its participation-ratio form is diary 01's `(L1-1)`.
* **Increment branch** -- PROVED as an implication (the extraction is an exact
  identity, not a hypercontractive estimate; no globalness hypothesis, no
  `1`-boundedness, no lifting loss).
* **The intended collision (increment vs proved low-conductor Weil
  equidistribution)** -- **REFUTED**, exact witness: the critical single-class
  spike of height `mu = 2^(n-ell)` satisfies the proved cylinder bound
  `|s_j(b)| <= 2^(-j)((j-2)2^j+2) 2^(n/2)` at every level `j >= 4`, on every row
  `ell = 2..19` and both parities, by exact integer comparison
  (`critical_spike_excluded` in `acb_dic_profile`).  Root cause: at the endpoint
  `n - ell = n/2 + 1/2`, so the mean and the Weil error scale coincide within
  `sqrt 2` and RH-strength equidistribution has zero margin against the
  critical configuration.  No sharpening of the low-conductor input repairs
  this, since the input is already sharp.
* **Green--Sawhney Theorem 1.2 as an import** -- **REFUTED**, witness: our
  density is `alpha = 1/n`, so `2^(-7) log(1/alpha) < 1` for every `ell` below
  `e^128/2` and the admissible level set is empty.  The family is calibrated
  for sparse sets; the irreducibles are dense on that scale.

### (b) Measurement tables

All from exact integers; the two examples assert Parseval, both endpoint
identities, Lemma D1, and library agreement on every row, and abort the row
otherwise.  36 rows (`ell = 2..19`) for the profile, 30 rows (`ell = 4..18`) for
the support-resolved masses, both parities.  Four tables above:

1. the conductor profile summary (`R_0`, `log2 G`, `sum q_j`, `q_ell`, cutoff,
   dominance and `L^2` fraction at the cutoff);
2. the normalized imbalance law `q_j 2^(ell-j) ~ 1` at `(19,39)`;
3. the codimension-resolved `L^2` fraction against the exact-conductor law
   `(j-2)/(ell-2) * 2^(j-ell)`, agreeing to three digits over 18 levels;
4. the `(L2-3)` support-resolved functional against the uniform-mass model.

Headline numbers:

* `q_j = (1+o(1)) 2^(-(ell-j))` for `j <= ell-4`; `q_ell in [0.481, 0.508]` on
  every odd row `ell = 9..19`; `sum_j q_j = 1.24 -- 1.28`, an absolute constant.
* Only `~1/(4 ell)` of `D`'s `L^2` mass -- `0.46%` at `ell = 19` -- is
  measurable at or below the proved Weil cutoff; half of it sits at the single
  top conductor level.
* `(L2-3)`: measured `2^(2.13 ell)` against a sufficient `2^(ell+2-4log2 ell)`;
  measured worse than the uniform-mass model by `+0.02 .. +0.08` bits **in
  total**.
* `E_1 = 0` exactly on all 15 odd rows and on no even row, as Result C4 proves.
* Independent sympy brute force over every monic polynomial: exact agreement on
  four rows, every field and every level.

### (c) The residual lemma

**(CDL), OPEN.**  For an absolute `c` and all large `ell`:
`sum_(chi : cond(chi) = j) |sum_e D_e^2 chi(e)|^2 <= M_2^2/ell` for every
conductor level `j <= c log2 ell`.  By Lemma D5 with `c >= 4.1`, `(CDL)` implies
`(WR)`, hence `(W4)`, hence the Lemire endpoint at both parities for
`ell >= 200` (the range below being finitely certified).

Its analytic content, by the verified identity
`fhat(chi) = 2^(-ell) sum_psi S_psi conj(S_(psi chi))`, is a **shifted second
moment** of the Hayes character sums at `poly(ell)` many fixed low-conductor
twists -- not a fourth moment.  The unshifted case is the lane's proved Weil
envelope.  Measured margin: `2^ell/ell^(c+1)`, growing.

Free first rung: `q_1 = 0` at the odd endpoint (Result C4, PROVED by the
translation involution `F(x) -> F(x+1)`), which is `1` of the `4 log2 ell - 2`
bits `(CDL-b)` must supply.  The even-endpoint analogue is open; the natural
candidate is the level `2^(v_2(n))` already isolated in tree as
`translation_paired_conductor_level`, but that fact is stated for the
`D`-spectrum and its transfer to the `D^2`-spectrum needs the same
involution argument run at that level.

### (d) Comparison to (CAB)

**Incomparable**, by grading, by end of the filtration, and by object; the
table in the log entry gives the three axes.  `(CAB)` is a strictly stronger
*conclusion* (it bounds `R_0` outright); `(CDL)` is a strictly smaller
*hypothesis* reaching the same endpoint through (D-PROD).  `(CAB)` needs no
cancellation but must control every cell; `(CDL)` needs cancellation but only
over `<= ell^c/2` characters, and its measured margin is exponential in `ell`
against `(CAB)`'s `2^(-0.28 ell)` closure ratio and the top-conductor
obligation's zero margin.  Recommendation for the board: keep both; they fail
independently, and `(CDL)` is the only live item that does not sit in the
top-conductor window.

### Epistemic ledger for this file

**PROVED**: Lemma D1 (`C_(j-1) <= C_j <= 2 C_(j-1)`); Lemma D2 and the exact
multiplicative kurtosis identity `R_0 = prod_j (1+q_j)`; Theorem D3 (the
dichotomy) and Corollary D4 (the exact increment, including `(INC-CYL)`);
Lemma D5 (sufficiency of a low-conductor input); the twist identity
`fhat(chi) = 2^(-ell) sum_psi S_psi conj(S_(psi chi))`; Result C4 (`E_1 = 0` at
the odd endpoint, by the translation involution); the argument that sweep-09's
uncertainty-principle lemma does not obstruct (D-PROD), because (D-PROD)
composes a low-conductor input with the PROVED top-conductor bound `q_j <= 1`
rather than building a low-conductor minorant.

**REFUTED with exact witnesses**: the intended increment/Weil collision, by the
critical single-class spike, excluded at no level `j >= 4` on any of 36 rows;
Green--Sawhney Theorem 1.2 as an importable statement at our density
`alpha = 1/n`; diary 01's `(L2-3)` as a route (measured `2^(2.13 ell)` against a
sufficient `2^(ell+2-4log2 ell)`), and with it diary 01's conditional closure
of the hypercontractivity family for this lane; diary 01's prediction that the
true support-resolved mass profile is *substantially* worse than the
uniform-mass model (it is worse, by `0.02 -- 0.08` bits in total).

**EVIDENCE ONLY** (36 profile rows `ell = 2..19` and 30 support rows
`ell = 4..18`, both parities, cross-checked against an independent sympy brute
force on four rows and against the library on every row): the geometric law
`q_j ~ 2^(-(ell-j))`; `q_ell -> 1/2`; `sum_j q_j -> ~1.26`; the exact-conductor
`L^2` mass law `(j-2)/(ell-2) 2^(j-ell)`; the exponential measured margin of
`(CDL)`.

**OPEN**: `(CDL)`; the shifted second moment
`sum_psi S_psi conj(S_(psi chi))` at low-conductor twists; the even-endpoint
analogue of Result C4; whether any collision partner exists for `(INC-CYL)` at
all.

**UNVERIFIED / POINTERS ONLY**: Keller--Lifshitz--Marcus Corollary 4.7, used by
Green--Sawhney as their Theorem 2.5 (I read it only through their restatement
and Appendix A, not from the KLM primary text); Keevash--Lifshitz--Long--Minzer
Theorem 7.10 (quoted from diary 01, itself verbatim from the JAMS text).

**NO THEOREM CREDIT** is claimed for the Lemire endpoint or for any lane lemma.
