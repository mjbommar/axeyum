# AC-Bridge phase-3 workstream 22: the (CDL) assault

Phase-3 assignment **22** of the board (`10-angles-board.md`): prove `(CDL)` --
the residual lemma of workstream C (`13-angle-dichotomy.md`) -- or its smallest
sufficient sub-form, and name the obstruction exactly if there is one.

Date opened: 2026-08-20.
Worktree: `/home/mjbommar/projects/personal/axeyum-gf2-lemire`.
Charter: `00-charter.md` (notation `G_ell`, `D_e`, `S_chi`, `M_2`, `M_4`, `K_4`,
`R_0`, `Sigma(ell)`, the ladder `L0..L4`).

Epistemic labels are the project's: **PROVED** (argument written out here),
**REFUTED** (with an exact witness), **OPEN**.  Finite computation is evidence,
never a theorem.  Literature is fetched and quoted, never recalled.

New files written by this workstream (new examples only; no existing source file
was touched):

```text
crates/axeyum-cas/examples/acb_cdl_twist.rs        exact fhat(chi) per low-conductor character
crates/axeyum-cas/examples/acb_cdl_pairs.rs        from-scratch (PAIR)/(PP)/(TWIST)/(COARSE)
crates/axeyum-cas/examples/acb_cdl_window.rs       the (CDL) supply/demand ledger, all levels
crates/axeyum-cas/examples/acb_cdl_involution.rs   the translation structure and what it kills
```

plus a session-local (not committed, per the charter's write scope)
`cdl_sympy_check.py`, the independent sympy brute force over three rows; its
algorithm is written out in full in the verification entry below, and the three
output lines it produced are quoted there (abridged; every field agrees).

## The target, restated

```text
(CDL)   sum_(cond(chi) = j) | sum_e D_e^2 chi(e) |^2  <=  M_2^2 / ell
        for every conductor level j <= 4.1 log2 ell,
```

equivalently `q_j = E_j / C_(j-1) <= 1/ell` at those levels; by Lemma D5 of
diary 13 this implies `(WR)`, hence `(W4-exact)`, hence the Lemire endpoint at
both parities.  Write

```text
T_chi := sum_(psi in dual(G_ell)) S_psi conj( S_(psi chi) ) ,   f_e := D_e^2 ,
fhat(chi) := sum_e f_e chi(e) .
```

## Log

### 2026-08-20 -- required reading

Read `00-charter.md`, `10-angles-board.md`, all 832 lines of
`13-angle-dichotomy.md`, all 715 lines of `04-weak-target-verification.md`, and
the shifted-moment / self-convolution material of
`02-lit-energy-fourth-moments.md` (Identity C at 19:10, the `(C1)..(C5)` forms,
the Hast--Matei and Sawin--Shusterman entries).  Inspected the machinery this
workstream consumes: `class_population_distribution`,
`fourth_moment_conductor_decomposition`, `principal_unit_structure`, and diary
13's `acb_dic_profile`.

The parallel auditor's `20-verify-chains.md` appeared during this run; it is
reconciled in a dedicated entry near the end.  Its Priority-2 verdict
(`(CDL) => (WR) => (W4)` CONFIRMED, the constant `4.1` CONFIRMED with `floor`)
is consistent with everything below, and the one GAP it flags in diary 13's
displayed `(TWIST)` is the same one this workstream found independently and has
now machine-checked in exact arithmetic.

### 2026-08-20 -- charge item 1: the exact polynomial-pair form of T_chi.  PROVED.

Conventions.  `S_psi := sum_e D_e psi(e)` is the *centered* Hayes sum, so
`S_1 = 0`; for `psi != 1` it agrees with `sum_(deg F = n) Lambda(F) psi(<F>)`
because `sum_e psi(e) = 0`.  `N_n(e) = mu + D_e`, `mu = 2^(n-ell)`.

**Theorem C22-1 (polynomial-pair form).  PROVED.**  For every `chi`,

```text
T_chi  =  2^ell fhat(chi^(-1)) ,                                        (T1)
```

and for every nontrivial `chi`,

```text
fhat(chi) = sum_( (F,G) : F,G monic of degree n, <F> = <G> ) Lambda(F) Lambda(G) chi(<F>)
            -  2 mu S_chi .                                             (PP)
```

The pair condition `<F> = <G>` is equivalent to `deg(F - G) <= n - ell - 1`:
`F` and `G` are two degree-`n` prime powers lying in the **same short interval
of length `2^(n-ell)`**.

*Proof of (T1).*  Expand both `S`'s and use orthogonality:
`sum_psi psi(e) conj(psi(e')) = 2^ell [e = e']`, giving
`T_chi = 2^ell sum_e D_e^2 conj(chi(e)) = 2^ell fhat(chi^(-1))`.
*Proof of (PP).*  Orthogonality on the full character group applied to the
uncentered sums `A_psi = sum_(deg F = n) Lambda(F) psi(<F>)` gives
`sum_psi A_psi conj(A_(psi chi)) = 2^ell sum_(<F> = <G>) Lambda Lambda conj(chi(<G>))`,
i.e. the double sum equals `sum_e N_n(e)^2 chi(e)` after conjugating `chi`.
Expanding `N_n = mu + D` and using `sum_e chi(e) = 0` for `chi != 1` leaves
`sum_e N_n(e)^2 chi(e) = 2 mu S_chi + fhat(chi)`.  QED

Both identities are machine-checked, exactly, in `Z[zeta_N]`:
`acb_cdl_twist` asserts `(PP)` for **every** character of conductor level
`<= 6` on every row `ell = 2..19`, both parities, and aborts the row otherwise;
`acb_cdl_pairs` re-derives everything from scratch (its own trial-division
irreducibility, its own class map by reciprocal truncation, its own principal
unit group and discrete logarithms) and additionally asserts `(T1)` by
performing the **full** dual convolution over all `2^ell` characters, and
asserts the double sum by **literal enumeration of the ordered pairs**
`(F,G)` with `<F> = <G>` (up to `5 400 264` pairs at `(9,20)`).

**Scale arithmetic, checked three independent ways (the charge asked for three).**

1. *Orthogonality range.*  The `psi`-sum in `T_chi` runs over the **entire**
   dual group `dual(G_ell)`, not over the `2^j` characters of `E_j`.  The delta
   it produces is `[e = e']` in `G_ell` -- the index-`1` condition.  The
   conductor level of `chi` enters only as a weight on the diagonal, never as a
   relaxation of the diagonal.
2. *Where an index-`2^j` condition would come from.*  Restricting the `psi`-sum
   to `cond(psi) <= j` gives `2^j [e = e' mod H_j]`, i.e. `F = G mod x^(j+1)`, a
   short interval of length `2^(n-j)`.  That restricted object is **not** a
   summand of `fhat(chi)` and does not appear anywhere in `(TWIST)`.
3. *Resolution counting.*  For `cond(chi) <= j`, `fhat(chi) = sum_b chi(b) m_j(b)`
   depends only on the `2^j` cylinder masses `m_j(b) = sum_(e in B_j(b)) D_e^2`.
   Each `m_j(b)` is a **square-then-sum**: the squares are taken at resolution
   `2^(n-ell)` and only then aggregated.  Aggregation cannot coarsen the
   resolution of terms that were already squared.  The **sum-then-square**
   object `s_j(b)^2 = (sum_(e in B_j(b)) D_e)^2` does live at resolution
   `2^(n-j)` -- and that one is the coarse object of item 2.

At the Lemire endpoint `n - ell = ell + 1` (odd) or `ell + 2` (even), so
`2^(n-ell) = sqrt(2^n) * 2^(1/2)` resp. `sqrt(2^n) * 2`.  **The constraint in
`(PP)` sits exactly at the square-root barrier, for every `chi`, at every
conductor level.**

**REFUTED (the charge's premise), with a proof rather than a witness.**  The
charge states: "The pairs are constrained by a LOW-conductor condition only --
i.e. `T_chi` counts Mangoldt pairs whose quotient lies in a HUGE subgroup (index
`2^j`).  That is a short-interval pair-correlation at scale `2^(n-j)` -- far
above the square-root barrier".  That is a conflation of the two objects
separated in items 2 and 3.  The quotient `<F G^(-1)>` in `T_chi` is constrained
to be **trivial**, i.e. to lie in the index-`2^ell` subgroup `{1}`, not in an
index-`2^j` subgroup.  There is therefore no naive Weil translation to attempt,
and the reason is **not** the scale coincidence that killed diary 13's collision
at the top of the filtration -- it is that the object was misidentified.

**And the object the charge described does exist, and IS proved.**

**Theorem C22-2 (the coarse pair correlation is unconditionally controlled).
PROVED.**  With `n_j(b) := sum_(e in B_j(b)) N_n(e)` and
`A_j := sum_b s_j(b)^2`,

```text
sum_( (F,G) : F = G mod x^(j+1) ) Lambda(F) Lambda(G)  =  sum_b n_j(b)^2
      =  2^(2 ell - j) mu^2  +  A_j ,                                   (COARSE)
A_j  =  2^(-j) sum_(1 != cond(psi) <= j) |S_psi|^2  <=  2^(n-j) Sigma_j ,
Sigma_j := sum_(i=2)^j 2^(i-1) (i-1)^2 .
```

*Proof.*  The first line is `n_j(b) = 2^(ell-j) mu + s_j(b)` squared and summed,
using `sum_b s_j(b) = 0`.  The second is Parseval on `E_j` applied to the
pushforward of `D`, followed by the proved Weil/Rhin envelope
`|S_psi| <= (cond(psi) - 1) 2^(n/2)` (see the literature entry: Rhin's theorem,
quoted verbatim there, is unconditional at fixed `q` including `q = 2`) and the
character count `2^(i-1)` at exact level `i`.  QED

Both lines are asserted exactly by `acb_cdl_pairs` and the bound by
`acb_cdl_twist`, on every row, every level `j <= 6`, both parities; zero
violations.  Measured `A_j / (2^(n-j) Sigma_j)` sits in `[8.623493e-2, 3.573375e-1]` at
`j = 6` over the 36 rows `ell = 2..19`, so the proved bound is within a small constant of
the truth for this object.

So the charge's intuition is right about *a* correlation -- it is just the
first-moment one.  `(CDL)` needs the second-moment one.

### 2026-08-20 -- charge item 2: what the proved machinery gives.  Vacuous, PROVED.

**Proposition C22-3 (the individual-Weil route to `(CDL)` is worse than
trivial, at every level).  PROVED.**  For every `chi`,

```text
|fhat(chi)|  =  2^(-ell) | sum_psi S_psi conj(S_(psi chi^(-1))) |
             <=  2^(-ell) sum_psi |S_psi| |S_(psi chi^(-1))| .
```

Every way of evaluating the right-hand side from proved inputs returns at least
`M_2`:

* Cauchy--Schwarz gives exactly `2^(-ell) sum_psi |S_psi|^2 = M_2 = fhat(1)`;
* the per-conductor Weil bound gives
  `2^(-ell) 2^n sum_psi (c(psi)-1)(c(psi chi^(-1))-1) = 2^(-ell) 2^n Sigma(ell) = mu Sigma(ell)`,
  because `c(psi chi^(-1)) = c(psi)` whenever `c(psi) > cond(chi)`;
* `L^infinity x L^1` gives `(max_psi |S_psi|) 2^(-ell) ||S||_1 <= ell^(3/2) 2^n`,
  again above `M_2 ~ (ell-1) 2^n`.

Since the lane's proved envelope is `M_2 <= mu Sigma(ell)`, the second value is
`>= M_2 = fhat(1)`, i.e. **the Weil evaluation is never better than the trivial
bound `|fhat(chi)| <= sum_e D_e^2 = M_2`, and is worse by the measured factor
`mu Sigma(ell)/M_2 ~ ell`.**  QED

(The parallel auditor reached the same conclusion by a different route -- its
best layer-to-`E_j` transfer is `|fhat(chi)| <= ell M_2`, also worse than
trivial.  Two independent constructions, same verdict.)

**Proposition C22-4 (the exact size of the gap).  PROVED.**  `(CDL)` at level
`j` is exactly `q_j <= 1/ell`, and the proved bound is Lemma D1's `q_j <= 1`.
So

> `(CDL)` is precisely a **factor-`ell` improvement of a proved inequality**,
> uniformly over the bottom `4.1 log2 ell` levels.

The measured truth is `q_j ~ 2^(-(ell-j))`, a factor `2^(ell-j)` improvement.
No exponential cancellation is being asked for anywhere: the entire content of
`(CDL)` is `poly(ell)`.

**Proposition C22-5 (even the linear term of `(PP)` overshoots).  PROVED
arithmetic.**  `(CDL)` at level `j` needs a typical
`|fhat(chi)| <= M_2 / sqrt(ell 2^(j-1))`.  The proved bound on the *linear*
term of `(PP)`, using the sharp Weil input at exact conductor `j`, is
`|2 mu S_chi| <= (j-1) 2^(n-ell+1) 2^(n/2)`, which at the odd endpoint is
`(j-1) 2^(3/2) 2^n`.  With `M_2 ~ (ell-1) 2^n` the ratio is

```text
   (proved bound on the linear term) / (per-character (CDL) budget)
      ~  2^(3/2) (j-1) 2^((j-1)/2) / sqrt(ell) ,
```

which is `18.4` at `(ell, j) = (19, 6)` and grows in `j`.  So `(PP)` cannot be
used by bounding its two halves separately even when the second half is
estimated with the sharpest proved input: the two halves must cancel against
each other.  QED

### 2026-08-20 -- the obstruction, named exactly

> **(VAR-EQ).**  Every proved input available at `q = 2` is a bound on the
> **first** moment of `D` over low-codimension cells: RH for Hayes
> `L`-functions, one `L`-function at a time (Weil/Rhin), which by Parseval
> controls `s_j(b)` and `A_j` (Theorem C22-2).  `(CDL)` is a statement about the
> **second** moment of `D` over the *same* cells: the cylinder masses
> `m_j(b) = sum_(e in B_j(b)) D_e^2`.  The passage first-moment -> second-moment
> is exactly one grading, and the trivial bound is extremal at the endpoint:
> `L^1 x L^infinity`, Cauchy--Schwarz and per-conductor Weil all return
> `fhat(1) = M_2`, because at the endpoint `|S_psi|` is essentially flat in
> `psi` at the Weil scale (`n - ell = n/2 + O(1)`).

Two sharpenings worth recording, because they say what `(CDL)` is *not*.

1. **It is not a fourth moment in disguise, per character.**  `T_chi` is
   bilinear in the family `{S_psi}` -- a shifted **second** moment, exactly as
   diary 13 says, and `(T1)` machine-confirms it.  The `D^2` weight does not
   reintroduce a fourth moment at the level of a single twist.
2. **But the level sum is a piece of the very fourth moment being targeted.**
   `E_j = sum_(cond chi = j) |fhat(chi)|^2` and `sum_(j=1)^ell E_j = C_ell - C_0
   = 2^ell M_4 - M_2^2`.  So `(CDL)` is *literally the bottom `4.1 log2 ell`
   exact-conductor layers of `M_4`*.  It is not an easier object of a different
   kind; it is the smallest identified sub-object of the same kind, and its
   advantage is quantitative only -- a factor `ell` on the smallest layers
   instead of a factor `2^ell` in total.

**The minimal toy cases.**  The charge asks for the minimal toy case if there is
an obstruction.  There are two, one per parity, and they are as small as an open
problem in this project gets.

```text
(TOY-1)  even endpoint n = 2 ell + 2, level j = 1:
         | sum_(e : a_1(e) = 0) D_e^2  -  sum_(e : a_1(e) = 1) D_e^2 |  <=  M_2 / sqrt(ell) .

(TOY-2)  odd endpoint n = 2 ell + 1, level j = 2  (level 1 is proved, Result C4):
         2 (m_2(0) - m_2(2))^2 <= M_2^2/ell   in the Z/4 coordinates of E_2.
```

`(TOY-1)` is one bit of information: split the monic degree-`n` polynomials by
the single coefficient `a_1` of `x^(n-1)`, and ask that the two halves carry the
same **variance** of `Lambda` over Hayes classes, to relative precision
`ell^(-1/2)`.  The corresponding **first**-moment statement is not merely proved
but *exact*: `S_(chi_1) = 0` identically (the level-1 Hayes `L`-function has
degree `0`), so `s_1(0) = s_1(1) = 0` and each half carries exactly `2^(n-1)` of
Mangoldt mass.  Machine-verified: `A_1 = 0` on every one of the 36 rows,
both parities.

> **That is the whole gap in one line: at level 1 the first moment is exactly
> equidistributed by a proved identity, and the second moment is completely
> open.**

### 2026-08-20 -- charge item 3: re-deriving the budget split.  Two PROVED corrections.

Lemma D5 needs a set `J` of levels with `q_j <= Q` and
`|J| (1 - log2(1+Q)) > ell - log2 G`.  Note that `J` need **not** be an initial
segment -- only its cardinality enters.

**Proposition C22-6 (hard floor on the level count).  PROVED.**  Since
`q_j >= 0`, each level of `J` contributes at most `1` bit to
`sum_(j in J) (1 - log2(1+q_j))`.  Hence **any** route through `(D-PROD)`
requires

```text
|J|  >=  ell - log2 G  =  4 log2 ell - 2 + o(1)
```

levels, no matter how strong the per-level bound is (even `q_j = 0`).  QED

So diary 13's `4.1 log2 ell` is within `2.5%` of the floor: **the constant `4.1`
cannot be meaningfully reduced by re-splitting the budget.**  This answers the
charge's item 3 in the negative for the split itself.  `(CDL-a)` (`Q = 1/2`) is
much worse, needing `9.7 log2 ell` levels, i.e. more levels than `ell` until
`ell ~ 49`; measured, `q_j <= 1/2` holds at **every** level of every row
`ell = 15..19` and the supply is still only `7.9` bits against a demand of
`12.5 .. 14.4`.

**Proposition C22-7 (where the demand actually comes from).  PROVED, and it
relocates the lever).**  Write the demand with the proved envelope and with the
true second moment:

```text
demand        = ell - log2( 2^ell (mu - P_n)^4 / (mu Sigma(ell))^2 )  =  4 log2 ell - 2 + o(1)
demand_sharp  = ell - log2( 2^ell (mu - P_n)^4 / M_2^2 )              =  2 log2(ell-1) - 2 + o(1)
```

The difference is exactly `2 log2( mu Sigma(ell) / M_2 ) ~ 2 log2 ell`: the
proved envelope `M_2 <= mu Sigma(ell) ~ ell^2 2^n` overestimates the measured
`M_2 ~ (ell-1) 2^n` by a factor `~ell`, and that factor is squared in the
budget.  Measured (exact, `acb_cdl_window`):

```text
 ell  par   demand_bits (proved envelope)   demand_bits_sharp (measured M_2)
  12  odd            11.346                        4.560
  14  odd            12.380                        5.128
  16  odd            13.259                        5.625
  18  odd            14.022                        6.005
  19  odd            14.370                        6.187
  19 even            12.541                        4.340
```

> **Consequence for the board.**  More than half of `(CDL)`'s obligation is not
> `(CDL)` at all -- it is slack in the second-moment envelope.  A proved sharp
> second moment `M_2 = O(ell 2^n)` at `q = 2` (i.e. the Keating--Rudnick
> variance constant, unproved at fixed `q`; see the literature entry) would cut
> the `(CDL)` level requirement from `~4.1 log2 ell` to `~2.05 log2 ell`, and
> the measured supply already exceeds `demand_sharp` on every odd row from
> `ell = 8` and on every row from `ell = 11` (it still fails on the even rows
> `ell = 8, 9, 10`).  That is a strictly easier and much better-studied target than
> `(CDL)` itself, and it is one grading below it.

**Correction to the statement of `(CDL)`, PROVED.**  As displayed in diary 13,
`(CDL)` reads `E_j <= M_2^2/ell`.  Used as an absolute target that form needs a
proved **lower** bound on `M_2`, and the ledger has none (the envelope is
one-sided).  Lemma D5 consumes only the ratio, so the safe statement is

```text
(CDL')   q_j = E_j / C_(j-1) <= 1/ell   for j <= 4.1 log2 ell,
```

which is self-normalizing and is implied by the displayed form (since
`C_(j-1) >= C_0 = M_2^2`).  Recommend the board carry `(CDL')`.

### 2026-08-20 -- a new proved structure at the bottom of the filtration

Result C4 of diary 13 proves `fhat(chi_1) = 0` at odd endpoints from the
bijection `F(x) -> F(x+1)`.  That bijection has a closed form on `G_ell`, and it
kills more than one character.

**Theorem C22-8 (translation structure).  PROVED.**  Let `u(t)` be the truncated
reciprocal of `F`, so `<F> = u`.  The class map induced by `F(x) -> F(x+1)` is

```text
sigma(u)(t)  =  c * tau(u)(t) ,     c := (1+t)^n mod t^(ell+1) ,
tau(u)(t)    :=  u( t / (1+t) ) mod t^(ell+1) ,
```

where `tau` is a group **automorphism** of `G_ell`, `tau o tau = id` (because
`s = t/(1+t)` satisfies `s/(1+s) = t` in characteristic 2), and
`tau(c) = c^(-1)` (because `1 + t/(1+t) = 1/(1+t)`), whence `sigma o sigma = id`.

*Proof.*  `t^n F(1/t + 1) = sum_m a_m t^m (1+t)^(n-m) = (1+t)^n * F^*(t/(1+t))`
where `F^*` is the reciprocal of `F`; truncate mod `t^(ell+1)`.  The three
identities are the displayed computations.  QED

**Corollary C22-9 (functional equation of the endpoint spectra).  PROVED.**
Since `F -> F(x+1)` is a degree- and Mangoldt-preserving bijection of the monic
degree-`n` polynomials, `D_(sigma e) = D_e`, and re-indexing gives, for every
character `chi`,

```text
fhat(chi) = chi(c) * fhat(chi o tau) ,        S_chi = chi(c) * S_(chi o tau) .
```

In particular `|fhat(chi)| = |fhat(chi o tau)|` and `|S_chi| = |S_(chi o tau)|`:
**the whole `D`- and `D^2`-spectrum is symmetric under the involution `tau` of
the dual group**, at both parities.  If `chi o tau = chi` then `chi(c)^2 = 1`
automatically (apply the equation twice, or use `tau(c) = c^(-1)`), and

```text
chi o tau = chi   and   chi(c) = -1     ==>   fhat(chi) = 0  and  S_chi = 0.
```

Result C4 is the case `chi = chi_1` at odd `n`.  QED

`acb_cdl_involution` verifies every clause exactly: the closed form
`sigma(u) = c tau(u)` for all `2^ell` classes, `tau` involutive and
multiplicative (tested against every generator and every element), `tau(c) =
c^(-1)`, `sigma` preserving the class populations, and the functional equation
`fhat(chi) = chi(c) fhat(chi o tau)` as an identity in `Z[zeta_N]` for **all**
characters of conductor level `<= 9`, on every row `ell = 2..12`, both parities.
Zero violations.

**Measured consequences (EVIDENCE, `ell = 2..12`, conductor levels `j <= 9`).**

```text
                                 j=1  j=2  j=3  j=4  j=5  j=6  j=7  j=8  j=9
 vanishing characters, odd n       1    0    1    0    2    0    4    0    8
 vanishing characters, even n      0    0    0    0    0    0    0    0    0
 tau-fixed characters (both)       1    0    2    0    4    0    8    0   16
 |dual(E_j)[2]| = 2^ceil(j/2)      2    2    4    4    8    8   16   16   32
```

* `|{chi : cond <= j, chi o tau = chi}| = 2^ceil(j/2)` exactly on every row --
  the same cardinality as the 2-torsion of `dual(E_j)`, but **not the same
  subgroup**: the example computes the subgroup generated by `{tau(g) g^(-1)}`
  and finds it differs from the squares `G^2` from `ell = 7` on
  (`commutator_is_squares=false` at `ell = 7, 8, 9`, with equal orders).  So the
  natural guess "`tau`-fixed = real character" is FALSE as a subgroup identity
  and true only as a count.
* At odd `n` exactly half of the `tau`-fixed characters vanish, giving
  `2^((j-1)/2)` vanishing characters at each odd level `j` and none at even
  levels.  As a fraction of the `2^(j-1)` characters of level `j` this is
  `2^(-(j-1)/2)`, so the mechanism supplies **one full bit at level 1 and a
  vanishing fraction thereafter**: it does not prove `q_j <= 1/ell` at any
  `j >= 2`.
* At even `n` the vanishing set is **empty at every level `j <= 9` on every row
  `ell = 2..12`**.

> **REFUTED (diary 13's open item, for this mechanism), with machine witnesses.**
> Diary 13 lists "the even-endpoint analogue of Result C4" as open and names
> `translation_paired_conductor_level` (`j = 2^(v_2(n))`) as the natural
> candidate.  The translation involution produces **no** anti-invariant
> character at an even endpoint, at any level `j <= 9`, for `ell = 2..12` --
> including the rows where `2^(v_2(n)) <= 9` (`n = 12, 20` at `ell = 5, 9`,
> level `4`; `n = 24` at `ell = 11`, level `8`).  The heuristic reason is
> visible in Corollary C22-9: `c = u^n` with `u = 1 + t`, so `chi(c) =
> chi(u)^n`, and at even `n` the sign is a square.  So `(TOY-1)` is not
> reachable by this route, and it stays the minimal open case.

### 2026-08-20 -- charge item 4: measurement

```sh
cargo build --release -p axeyum-cas --example acb_cdl_twist
cargo build --release -p axeyum-cas --example acb_cdl_pairs
cargo build --release -p axeyum-cas --example acb_cdl_window
cargo build --release -p axeyum-cas --example acb_cdl_involution
./target/release/examples/acb_cdl_twist 2 16 6        #  4.9 s
./target/release/examples/acb_cdl_twist 17 19 6       # 82.3 s
./target/release/examples/acb_cdl_twist 19 19 6       # 32.4 s, peak RSS 180.8 MB
./target/release/examples/acb_cdl_pairs 2 8           #  0.7 s   (from scratch)
./target/release/examples/acb_cdl_pairs 9 9 9         #  5.9 s   (full 2^9 dual convolution)
./target/release/examples/acb_cdl_window 8 16         #  5.9 s
./target/release/examples/acb_cdl_window 17 19        # 58.1 s
./target/release/examples/acb_cdl_involution 2 12 9   #  0.6 s
python3 cdl_sympy_check.py                            #  2.6 s (session-local)
```

All within the charter budget (`< 5 min`, `< 2 GB`).  Every example is
fail-closed: a violated identity aborts the row with `status=FAIL`.

**Table 1.  `q_j` and `ell q_j` at the bottom of the filtration, odd endpoint.**
`(CDL)` at level `j` is exactly `ell q_j <= 1`.

```text
 ell     j=1      j=2      j=3      j=4      j=5      j=6     max(ell q_j)   (CDL) at j<=6
   8   0.000    0.265    0.633    0.143    0.402    1.876       1.876            NO
   9   0.000    0.031    0.808    0.389    0.458    0.494       0.808            yes
  11   0.000    0.011    0.093    0.069    0.166    0.352       0.352            yes
  13   0.000    0.000    0.055    0.025    0.102    0.122       0.122            yes
  15   0.000    0.001    0.000    0.004    0.011    0.032       0.032            yes
  17   0.000    0.000    0.002    0.003    0.003    0.011       0.011            yes
  19   0.000    0.000    0.000    0.000    0.002    0.002       0.002            yes
```

(entries are `ell q_j`; the even endpoint behaves the same from `ell = 9`, with
`ell q_1` nonzero but small: `0.001` at `ell = 19`).

**Table 2.  The `(CDL)` margin at `j <= 6`, both parities.**  `min margin` is
`min_(j<=6) (M_2^2/ell) / E_j`, exact integers.

```text
 ell   n  par   argmin   min margin   log2 margin      ell   n  par   min margin   log2
   8  17  odd    j=6      4.472e-1       -1.16          8  18 even     3.887e-1    -1.36
   9  19  odd    j=3      1.233e+0       +0.30          9  20 even     1.188e+0    +0.25
  11  23  odd    j=6      2.753e+0       +1.46         11  24 even     4.112e+0    +2.04
  13  27  odd    j=6      8.103e+0       +3.02         13  28 even     7.925e+0    +2.99
  15  31  odd    j=6      3.076e+1       +4.94         15  32 even     3.041e+1    +4.93
  17  35  odd    j=6      9.397e+1       +6.55         17  36 even     9.137e+1    +6.51
  19  39  odd    j=5      5.430e+2       +9.08         19  40 even     4.856e+2    +8.92
```

`(CDL)` restricted to `j <= 6` holds on **every row with `ell >= 9`, both
parities**, and fails at `ell <= 8`.  The margin grows by `+0.88` bits per unit
`ell` over the odd rows `ell = 9..19` (`+1.03` over the last five).

**Table 3.  The supply/demand ledger (`acb_cdl_window`), the honest test of
`(CDL)` as a hypothesis.**  Lemma D5 needs a *set* of levels; `supply` counts
levels with `q_j <= 1/ell` and prices each at `1 - log2(1+1/ell)` bits.

```text
 ell   n  par   levels q_j<=1/ell   supply bits   demand bits   sufficient?
   9  19  odd          6              5.088         9.350           no
  12  25  odd          8              7.076        11.346           no
  14  29  odd         10              9.005        12.380           no
  16  33  odd         12             10.950        13.259           no
  17  35  odd         12             11.010        13.653           no
  18  37  odd         13             11.986        14.022           no
  19  39  odd         14             12.964        14.370           no
  19  40 even         14             12.964        12.541          YES
```

**Result 22-A (a correction to diary 13's headline, EVIDENCE).**  Diary 13
records the `(CDL)` margin as "`2^ell/ell^(c+1)`, growing".  That is correct
*per level at fixed `j`* (Tables 1 and 2 confirm it: `q_j` at fixed `j` decays
like `2^(-ell)`), but it is **not** the margin of the hypothesis.  The
hypothesis needs `4.1 log2 ell` levels, and the number of levels that actually
satisfy `q_j <= 1/ell` is `floor(ell - log2 ell) + O(1)` (measured `6` at
`ell = 9`, `8` at `ell = 12`, `12` at `ell = 16`, `14` at `ell = 19`, both
parities).  Supply first exceeds demand at

```text
 even endpoint:  ell = 19   (measured, first row with sufficient = YES)
 odd  endpoint:  ell ~ 21   (extrapolated: supply ~ ell - log2 ell - 1.44,
                             demand ~ 4 log2 ell - 2.7; crossover ell ~ 21)
```

So `(CDL)` as a whole is measurably true only from `ell ~ 19..21` upward, not
throughout the computed range, and asymptotically the surplus is
`ell - 5 log2 ell -> infinity`.  Diary 13's Lemma D5 statement ("for
`ell >= 200`") is unaffected; the headline "measured margin, growing" needs the
qualifier "per level at fixed `j`".

**Result 22-B (diary 13's pointwise sufficient form is FALSE in the computed
range).  REFUTED, with an exact witness.**  Diary 13 offers, as a sufficient
form, `|fhat(chi)| <= M_2 ell^(-(c+2)/2)` for every `chi` of level
`<= c log2 ell`, `c = 4.1` (exponent `-3.05`).  Measured maxima over
`j <= 6` alone already violate it on every row:

```text
 ell   max_(j<=6) |fhat(chi)|/M_2      requirement ell^(-3.05)      ratio
  13          4.420e-2                      4.004e-4               110.4
  15          1.446e-2                      2.588e-4                55.9
  17          6.927e-3                      1.767e-4                39.2
  19          4.915e-3                      1.258e-4                39.1
```

Witness: `(ell, n) = (19, 39)`, conductor level `j = 5`, the character attaining
`|fhat(chi)|/M_2 = 4.915288753e-3` (emitted by `acb_cdl_twist` as
`max_abs_fhat_over_M2` at `j = 5`), against a requirement of `1.258350184e-4`.
The measured maximum decays like `2^(-0.59 ell)` while the requirement decays
only polynomially, so the pointwise form becomes true around `ell ~ 26`; but it
is strictly stronger than `(CDL)` and false exactly where `(CDL)` is true.
**Do not route a proof through the pointwise form.**

**Table 4.  The coarse (proved) object, for contrast.**  `A_j` against the
proved allowance `2^(n-j) Sigma_j` of Theorem C22-2, at `j = 6`:

```text
 ell     10     12     14     16     18     19
 odd   0.127  0.225  0.162  0.204  0.242  0.252
 even  0.311  0.230  0.259  0.209  0.086  0.261
```

The first-moment object is inside its proved bound by a factor `3` to `12`,
uniformly.  The second-moment object at the same levels has **no** proved bound
better than `q_j <= 1`.  That contrast is the obstruction `(VAR-EQ)` in one
table.

### 2026-08-20 -- independent verification: sympy brute force

`cdl_sympy_check.py` (session-local) enumerates every monic polynomial of degree `n`
over `GF(2)`, factors it with `sympy.Poly(..., domain=GF(2)).factor_list()`,
applies the von Mangoldt weight, bins by the **polynomial truncation** of the
reciprocal (basis-free, sharing no coordinate convention with the CAS), and
rebuilds `M_2`, `C_j`, `E_j`, `q_j`, the level-1 and level-2 twists
`fhat(chi)`, the linear term `S_chi`, the pair form `sum_e N_e^2 chi(e)`, and a
**literal enumeration of the ordered Mangoldt pairs** with `<F> = <G>` twisted
by the level-1 character.  It asserts `(PP)` internally.

(abridged: the `C_0` column and some `q_j` columns are dropped; the raw lines
carry every field.)

```text
SYMPY_CDL|ell=4|n= 9|M_2=1168 |E_1=0      |E_2=36864    |E_3=184320   |q_2=2.702195533871e-02|q_3=1.315549059017e-01|fhat_j1/M_2=0.000000000000e+00|fhat_j2/M_2=1.162367311540e-01|literal_pair_twist_j1=0
SYMPY_CDL|ell=4|n=10|M_2=1200 |E_1=135424 |E_2=165888   |E_3=373248   |q_1=9.404444444444e-02|q_2=1.052973675658e-01|fhat_j1/M_2=3.066666666667e-01|fhat_j2/M_2=2.400000000000e-01|literal_pair_twist_j1=368
SYMPY_CDL|ell=5|n=12|M_2=23584|E_1=116294656|E_2=29001728|E_3=297472000|q_1=2.090859382623e-01|q_2=4.312526456517e-02|fhat_j1/M_2=4.572591587517e-01|fhat_j2/M_2=1.614654002714e-01|literal_pair_twist_j1=10784
```

Every field agrees with `acb_cdl_twist` **digit for digit**, including the
twelve-digit character magnitudes (`4.572591587517e-1`, `1.614654002714e-1` at
`(5,12)`; `1.162367311540e-1` at `(4,9)`), the exact integers `E_1, E_2, E_3`
and the `q_j`.  `M_2` also reproduces diary 04's sympy rows.  Three rows
cross-checked (the charge asked for two).  AGREEMENT, no mismatch.

The from-scratch Rust example `acb_cdl_pairs` is a *third* independent
implementation (own irreducibility test by trial division, own class map, own
principal-unit group, own discrete logarithms) and it verifies `(PAIR)`, `(PP)`,
`(TWIST)` and `(COARSE)` on `ell = 2..9`, both parities, with the full
`2^ell x 2^ell` dual convolution at `ell <= 9`.

### 2026-08-20 -- charge item 5: literature, fetched

A targeted sub-agent fetched primary texts (arXiv / ar5iv) for shifted
convolutions and pair correlations of `Lambda` in function fields at fixed `q`.
Its `WebSearch` quota was exhausted, so coverage is arXiv-API-complete for the
listed queries but cannot exclude non-arXiv items; that limitation is recorded
as it was reported.  Verbatim statements and the hypotheses that matter:

* **Rhin's theorem**, as quoted verbatim in Klurman--Mangerel--Teravainen
  Lemma 3.1 (<https://ar5iv.labs.arxiv.org/html/2009.13497>, cited there as
  "[30, Theorem 3]"):
  > "Let `N >= 1`.  Let `chi~` be a non-principal Hayes character.  Then
  > `sum_(G in M_N) chi~(G) Lambda(G) << cond_H(chi~) q^(N/2)`."
  **Unconditional, fixed `q`, `q = 2` included, `N -> infinity`.**  This is the
  literature form of the lane's proved Weil envelope, and it is what Theorem
  C22-2 consumes.  It is also, by Proposition C22-3, exactly what is not enough.
* **Klurman--Mangerel--Teravainen**, *Correlations of multiplicative functions
  in function fields*, <https://arxiv.org/abs/2009.13497>.  Standing assumption
  verbatim: *"Throughout this paper, the cardinality `q` of the underlying
  finite field `F_q` is fixed."*  Their Definition 1.3 is our class group:
  *"A multiplicative function `xi` ... is called a short interval character if
  there exists `nu` such that `xi(A) = xi(B)` whenever the `nu+1` highest degree
  coefficients of `A` and `B` agree."*  **But all main theorems require values
  in the closed unit disc**, so `mu` and Liouville are covered and `Lambda` is
  not, and the results are logarithmically averaged.  Verdict: fixed `q` and
  `q = 2`, right objects, **wrong function**.  They also document a genuine
  characteristic-2 pathology, verbatim: *"a low-characteristic issue emerges in
  the Matomaki--Radziwill theorem: in `F_2[t]`, for instance, a real-valued
  multiplicative function can indeed have different mean values on short and
  long intervals."*  Recorded as a standing warning for this lane.
* **Sawin--Shusterman**, *On the Chowla and twin primes conjectures over
  `F_q[T]`*, <https://arxiv.org/abs/1808.04001>, Theorem 1.1 verbatim:
  *"For an odd prime number `p`, and a power `q` of `p` satisfying
  `q > 685090 p^2` ..."*.  Fixed `q`, degree `-> infinity` -- the right limit --
  but `p` odd and `q > 2743360` at `p = 2`.  Verdict: excluded by name.
* **Gorodetsky**, *Mean values of arithmetic functions in short intervals and in
  arithmetic progressions in the large-degree limit*,
  <https://arxiv.org/abs/1810.00483>.  **Fixed `q` including `q = 2`, `n ->
  infinity`, and it covers `Lambda`.**  Theorem 1.3 verbatim:
  *"`Var(alpha; n, h) <= max_(f in M_n) |alpha(f)|^2 q^(h+1)
  e^(O_q(n log log(n+2)/log(n+2)))`"*, with the paper's own non-triviality range
  *"`limsup_(n -> infinity) (h+1)/n > 1/2`"*.  At our endpoint
  `(h+1)/n = (ell+1)/(2ell+1) -> 1/2` exactly, and the subexponential factor is
  superpolynomial in `q^n`.  Verdict: **the one fixed-`q` variance theorem for
  `Lambda`, and it is precisely vacuous at the endpoint** -- an upper bound only,
  biting at `h >= (1/2 + delta) n`.
* **Keating--Rudnick**, <https://arxiv.org/abs/1204.0708>, Theorem 2.1 verbatim:
  *"Let `h < n-3`.  Then `lim_(q -> infinity) (1/q^(h+1)) Var(nu(.,h)) = n-h-2`."*
  `q -> infinity` with `n, h` fixed.  This is the asymptotic that would give
  `M_2 ~ (ell-1) 2^n` and halve the `(CDL)` demand (Proposition C22-7); it is
  **not available at fixed `q`**.  Same for Rodgers
  (<https://arxiv.org/abs/1609.02967>, *"in the large `q` limit"*) and the
  Hall--Keating--Roditty-Gershon line.
* **Hast--Matei**, <https://arxiv.org/abs/1604.02067>, Theorem 1.4 verbatim
  confirmed, including *"(assuming `p > n` if `m > 2`)"*.  At `p = 2` only
  `m = 2` survives, with a constant `C_(2,n,h)` depending on `n`, hence useless
  as `n -> infinity`.
* **Sawin**, <https://arxiv.org/abs/1809.05137>, Theorem 1.2 verbatim confirmed,
  with the exponent `(1/2)(h + floor(n/p) - floor((n-h)/p) + 1)` and prefactor
  `3 (n+2)^(2n-h)`.  At `p = 2` the floor term eats half the saving **and** the
  prefactor `(n+2)^(1.5n)` is superpolynomial in `2^n`.  Vacuous at fixed `q`
  for every `p`, doubly so at `p = 2`.
* **Sawin**, <https://arxiv.org/abs/2102.09730> (level of distribution):
  abstract verbatim *"Each level of distribution converges to 1 as `q` goes to
  infinity"*.  `q -> infinity` by construction.
* **Sawin--Shusterman**, *Short sums of trace functions over function fields*,
  <https://arxiv.org/abs/2512.24080> (v1 2025-12-30), the newest fixed-`q`
  short-sum technology: *"For large enough (but fixed) prime powers `q` ... and
  no Artin--Schreier factors in their geometric global monodromy"*.  `q = 2`
  excluded, and the Artin--Schreier exclusion is the characteristic-`p`
  obstruction in its usual place.  Flagged as the paper to watch; it is not
  about `Lambda` in Hayes classes.
* **Baier--Bhandari**, <https://arxiv.org/abs/2208.07173>, the nearest object to
  `(CDL)` in the literature (variance of `Lambda` in short-interval-cap-
  progression, i.e. a sub-family of a short interval): `q -> infinity` with
  `n, h` fixed, standing hypothesis `Q(0) != 0`, and its actual asymptotic
  (their Theorem 4(iii)) is **conditional on their Conjecture 1**.

> **Literature verdict, and it is the load-bearing one.**  The sub-agent's
> search for `(CDL)`'s exact object -- equidistribution of the short-interval
> variance of `Lambda` across sub-families cut out by a few linear conditions on
> the top coefficients, equivalently across cosets of a small-index subgroup of
> the Hayes class group -- returned **no result at any `q`**, not at fixed `q`
> and not in the large-`q` limit.  Queries run and reviewed in full are listed
> in the agent report (the `Roditty-Gershon`, `factorization functions`,
> `short intervals + von Mangoldt + variance`, `Hayes/short interval characters`
> and `level of distribution` listings).  The agent's own note that the
> large-`q` case "is probably provable by an expert in an afternoon" from Katz
> equidistribution is its opinion and is recorded here as **UNVERIFIED**.
>
> So `(CDL)` is not merely unproved at `q = 2`; the statement one grading below
> it (the variance asymptotic) is unproved at `q = 2`, and the statement at its
> own grading is **unwritten even where the tools exist**.

### 2026-08-20 -- reconciliation with the parallel auditor (`20-verify-chains.md`)

Read on completion.  Four points of contact, no disagreement:

1. **The `(TWIST)` conjugation gap.**  The auditor flags that diary 13's
   displayed `fhat(chi) = 2^(-ell) sum_psi S_psi conj(S_(psi chi))` actually
   computes `fhat(chi^(-1))`.  This workstream derived the same correction
   independently and has now **machine-checked** the corrected form
   `T_chi = sum_psi S_psi conj(S_(psi chi)) = 2^ell fhat(chi^(-1))` as an exact
   identity in `Z[zeta_N]`, over the full dual group, on every row `ell = 2..9`
   and every character of conductor `<= 3` (`acb_cdl_pairs`, identity `(TWIST)`).
   Confirmed, harmless, and now pinned by a test rather than by a reading.
   Everything in this file uses the corrected form.
2. **`(CDL) => (WR) => (W4)` and the constant `4.1`** -- the auditor CONFIRMS
   both, including with `floor` rather than `ceil`.  Proposition C22-6 adds the
   complementary fact: `4 log2 ell - 2` is a *floor* on the level count for any
   `Q`, so `4.1` is within `2.5%` of optimal and cannot be improved by
   re-splitting.  The two results are consistent and the second explains why the
   first has so little slack.
3. **`(CDL)` and `(SUP-L)` may not borrow from each other** (auditor's REL-1 /
   REL-2, and its finding that the best layer-to-`E_j` transfer is `ell M_2`,
   worse than trivial).  Proposition C22-3 reaches the same verdict from the
   `(TWIST)` side rather than the layer side.  Two independent constructions,
   same conclusion; recorded as mutually reinforcing rather than duplicated.
4. **Result C4** -- the auditor re-derives it independently.  Theorem C22-8 and
   Corollary C22-9 generalize it (closed form, functional equation, the full
   vanishing family) and settle the even-endpoint analogue in the negative for
   this mechanism.

### 2026-08-20 -- what I did not do

* **No proof of `(CDL)`, of `(CDL')`, of `(TOY-1)`, of `(TOY-2)`, of `(WK)` or
  of any uniform estimate.**  No theorem credit is claimed for Lemire's
  conjecture or for any lane lemma.
* No row above `ell = 19` (the `ell = 20` transform is outside the charter's
  5-minute budget), none above `ell = 12` for the involution structure, none
  above `ell = 9` for the from-scratch pair/twist verification.
* No per-character data above conductor level `6` (the level-`j` character
  enumeration is `2^j` characters times `2^j` cylinders; the level *energies*
  `E_j` are cheap and are measured to `j = ell` by `acb_cdl_window`).
* No attempt to prove `|Fix(tau) cap dual(E_j)| = 2^ceil(j/2)`; it is measured
  on 22 rows and the natural guess (`tau`-fixed = real) is refuted as a subgroup
  identity from `ell = 7`.
* No attempt at the sharp second moment `M_2 = O(ell 2^n)` at `q = 2`
  (Proposition C22-7 identifies it as the higher-value target; it belongs to a
  different workstream and to the Keating--Rudnick literature).

## FINDINGS

### (a) The exact polynomial-pair form of `T_chi`, and the scale

**PROVED (Theorem C22-1, machine-checked three ways).**

```text
T_chi = sum_psi S_psi conj(S_(psi chi)) = 2^ell fhat(chi^(-1)) ,

fhat(chi) = sum_( (F,G) monic deg n, <F> = <G> ) Lambda(F) Lambda(G) chi(<F>)  -  2 mu S_chi ,
            with   <F> = <G>  <=>  deg(F - G) <= n - ell - 1 .
```

The pair constraint is `F = G` in `G_ell`, i.e. the **index-1** condition: an
ordered pair of degree-`n` prime powers in the same short interval of length
`2^(n-ell)`.  At the endpoint `2^(n-ell) = sqrt(2^n) * 2^(1/2)` (odd) or
`sqrt(2^n) * 2` (even): **exactly the square-root barrier, for every `chi`,
independently of `cond(chi)`.**

**REFUTED (the charge's premise for this assault).**  `T_chi` does *not* count
pairs whose quotient lies in an index-`2^j` subgroup, so there is no naive
translation of the lane's Weil window to attempt.  The conductor level of `chi`
weights the diagonal; it does not relax it.  Three independent checks of the
scale arithmetic are written out in the log (orthogonality range; where an
index-`2^j` condition would come from; square-then-sum versus sum-then-square).

**PROVED (Theorem C22-2), and it is the object the charge described.**  The
index-`2^j` pair correlation *does* exist, lives at scale `2^(n-j)` far above
the barrier, and **is** bounded unconditionally by the lane's proved Weil
window:

```text
sum_( F = G mod x^(j+1) ) Lambda Lambda = 2^(2 ell - j) mu^2 + A_j ,
A_j = 2^(-j) sum_(1 != cond psi <= j) |S_psi|^2 <= 2^(n-j) Sigma_j .
```

Machine-verified on all rows; measured `A_j / (2^(n-j) Sigma_j)` in
`[8.623493e-2, 3.573375e-1]` at `j = 6` over all 36 rows.  It is a **first**-moment object and carries no information about
`(CDL)`.

### (b) Proof state of `(CDL)`

**OPEN, at every level `j >= 2`, at both parities, for every `ell`.**  Nothing
in this workstream proves `(CDL)` or any sub-form of it beyond level 1 at the
odd endpoint.  What is proved is the size and the shape of the gap:

* **Proposition C22-3 (PROVED).**  The individual-Weil route is *worse than
  trivial* at every level: every evaluation of
  `|fhat(chi)| <= 2^(-ell) sum_psi |S_psi||S_(psi chi^(-1))|` from proved inputs
  returns at least `fhat(1) = M_2`, and the per-conductor Weil evaluation
  returns `mu Sigma(ell) >= M_2`, worse by the measured factor `~ell`.
* **Proposition C22-4 (PROVED).**  `(CDL)` at level `j` is exactly a
  **factor-`ell` improvement** of Lemma D1's proved `q_j <= 1`.  The whole
  content is `poly(ell)`; the measured truth is `2^(ell-j)`.
* **Proposition C22-5 (PROVED).**  Even the linear term `2 mu S_chi` of `(PP)`,
  bounded with the sharpest proved input, exceeds the per-character `(CDL)`
  budget by `2^(3/2)(j-1)2^((j-1)/2)/sqrt(ell)` (`18.4` at `(19,6)`).  The two
  halves of `(PP)` must cancel against each other; neither can be discarded.
* **Range closed: `j <= 1` at the odd endpoint only** (Result C4, re-proved and
  generalized here as Corollary C22-9), worth exactly `1` bit of the
  `4 log2 ell - 2` the budget needs.  Nothing is closed at any even endpoint,
  at any level.

### (c) The obstruction, named

> **(VAR-EQ).  Proved inputs control the FIRST moment of `D` over
> low-codimension cells; `(CDL)` is about the SECOND moment over the same
> cells.**  Weil/Rhin bounds one `L`-function at a time, which by Parseval
> controls `s_j(b)` and `A_j` exactly (Theorem C22-2).  It says nothing about
> `m_j(b) = sum_(e in B_j(b)) D_e^2`, and at the endpoint the trivial bound is
> extremal because `n - ell = n/2 + O(1)` makes `|S_psi|` flat in `psi` at the
> Weil scale.  Per character `(CDL)` is a shifted **second** moment (the `D^2`
> weight does **not** hide a fourth moment); per level it is an exact-conductor
> **layer of the very `M_4` the project targets**, since `sum_j E_j = 2^ell M_4
> - M_2^2`.  `(CDL)` is therefore the smallest identified sub-object of the same
> problem, not a different and easier problem.

**Minimal toy cases** (the charge asked for one; there is one per parity):

```text
(TOY-1)  n = 2 ell + 2:  the two halves of the family cut by the single
         coefficient a_1 of x^(n-1) carry equal VARIANCE of Lambda over Hayes
         classes to relative precision ell^(-1/2):
             | sum_(a_1 = 0) D_e^2 - sum_(a_1 = 1) D_e^2 |  <=  M_2 / sqrt(ell).
         The corresponding FIRST-moment statement is an exact proved identity
         (S_(chi_1) = 0, so both halves carry exactly 2^(n-1) of Mangoldt mass;
         A_1 = 0 machine-verified on all 36 rows).  Measured: it holds with
         margin ~ell/q_1 = 1.1e3 at ell = 19.  OPEN.

(TOY-2)  n = 2 ell + 1, level j = 2 (level 1 being proved): E_2 <= M_2^2/ell in
         the Z/4 coordinates of E_2.  OPEN.
```

### (d) The budget, re-derived

* **Proposition C22-6 (PROVED).**  Any route through `(D-PROD)` needs at least
  `ell - log2 G = 4 log2 ell - 2 + o(1)` levels, whatever `Q` is, because a
  level supplies at most one bit.  Diary 13's `4.1 log2 ell` is within `2.5%` of
  that floor: **the split cannot be usefully re-derived downward.**
* **Proposition C22-7 (PROVED, and it relocates the lever).**  Over half the
  demand is slack in the second-moment envelope, not `(CDL)`:
  `demand = 4 log2 ell - 2` with the proved `M_2 <= mu Sigma(ell)`, against
  `demand_sharp = 2 log2(ell-1) - 2` with the true `M_2` (measured `14.37` vs
  `6.19` at `ell = 19` odd).  A proved sharp second moment at `q = 2` would
  halve the `(CDL)` level requirement to `~2.05 log2 ell`, and the measured
  supply already clears `demand_sharp` on every odd row from `ell = 8` and every
  row from `ell = 11`.
* **Statement correction (PROVED).**  `E_j <= M_2^2/ell` is not usable as an
  absolute target without a proved *lower* bound on `M_2`, which the ledger
  lacks.  Carry the self-normalizing `(CDL')`: `q_j = E_j/C_(j-1) <= 1/ell`.

### (e) New proved structure (a deliverable in its own right)

**Theorem C22-8 / Corollary C22-9, PROVED and machine-checked in exact
cyclotomic arithmetic on 22 rows and 511 characters per row:**

```text
sigma(u)(t) = (1+t)^n * u(t/(1+t))  mod t^(ell+1) ,
tau(u)(t) := u(t/(1+t))  is an involutive AUTOMORPHISM of G_ell,  tau(c) = c^(-1),
fhat(chi) = chi(c) fhat(chi o tau)  and  S_chi = chi(c) S_(chi o tau)   for ALL chi,
hence  chi o tau = chi  and  chi(c) = -1   ==>   fhat(chi) = S_chi = 0 .
```

So the `D`- and `D^2`-spectra are symmetric under an explicit involution of the
dual group at **both** parities, and Result C4 is one instance.  Measured:
`|{chi : cond <= j, chi o tau = chi}| = 2^ceil(j/2)` exactly; at odd `n` exactly
half of them vanish (`2^((j-1)/2)` per odd level `j`, none at even levels); at
even `n` **none** vanish at any level `j <= 9`, `ell = 2..12` -- so diary 13's
open even-endpoint analogue of C4 is **REFUTED for this mechanism**, with
machine witnesses including the rows where `2^(v_2(n)) <= 9`.  The natural guess
`Fix(tau) = {real characters}` is refuted as a subgroup identity from `ell = 7`
(`commutator_is_squares = false`) while remaining true as a count.

### (f) Data

Four tables in the log, all from exact integers, every row fail-closed:

1. `q_j` and `ell q_j` at `j <= 6`, `ell = 4..19`, both parities;
2. the `(CDL)` margin at `j <= 6` (holds on **every row `ell >= 9`**, both
   parities; fails at `ell <= 8`; margin `+0.88` bits per unit `ell`);
3. the supply/demand ledger over the whole filtration -- `(CDL)` as a
   *hypothesis* first becomes true at `ell = 19` (even) and `ell ~ 21` (odd),
   which corrects diary 13's headline (Result 22-A);
4. the coarse first-moment object `A_j` against its proved allowance.

Plus Result 22-B: diary 13's pointwise sufficient form
`|fhat(chi)| <= M_2 ell^(-3.05)` is **REFUTED on every computed row**, witness
`(19,39)`, level `5`, `4.915288753e-3` against `1.258350184e-4`.

Verification: three independent implementations (the library-backed
`acb_cdl_twist`; the from-scratch `acb_cdl_pairs` with its own irreducibility
test, class map, group and discrete logarithms; and a sympy brute force over
every monic polynomial), agreeing digit for digit on `M_2`, `E_j`, `q_j` and the
twelve-digit character magnitudes on three rows, plus library agreement on the
conductor energies on every row.

### Epistemic ledger for this file

**PROVED**: Theorem C22-1 (the pair form `(PP)` and `T_chi = 2^ell
fhat(chi^(-1))`); the three scale checks locating the constraint at
`2^(n-ell) = sqrt(2^n) 2^(O(1))`; Theorem C22-2 (the index-`2^j` correlation and
its unconditional Weil bound `A_j <= 2^(n-j) Sigma_j`); Proposition C22-3 (the
individual-Weil route to `(CDL)` is worse than trivial at every level);
Proposition C22-4 (`(CDL)` = a factor-`ell` improvement of `q_j <= 1`);
Proposition C22-5 (the linear term of `(PP)` alone overshoots the budget);
Proposition C22-6 (the hard floor `|J| >= ell - log2 G` on the level count, so
`4.1` is near-optimal); Proposition C22-7 (the demand is dominated by the
second-moment envelope, `4 log2 ell` versus `2 log2 ell`); the statement
correction to `(CDL')`; Theorem C22-8 (`sigma = c tau`, `tau` an involutive
automorphism, `tau(c) = c^(-1)`) and Corollary C22-9 (the functional equation
`fhat(chi) = chi(c) fhat(chi o tau)` and its vanishing criterion).

**REFUTED with exact witnesses**: the charge's premise that `T_chi` is an
index-`2^j`, above-square-root pair correlation (refuted by Theorem C22-1 plus
the three scale checks, and by exhibiting the object that *is* index-`2^j`);
diary 13's pointwise sufficient form `|fhat(chi)| <= M_2 ell^(-3.05)` (witness
`(19,39)`, `j = 5`, factor `39.1`; false on every computed row); the even-
endpoint analogue of Result C4 via the translation involution (no anti-invariant
character exists at even `n`, `j <= 9`, `ell = 2..12`); the guess
`Fix(tau) = {real characters}` as a subgroup identity (`ell >= 7`).

**EVIDENCE ONLY** (36 rows `ell = 2..19` both parities for the level data, 22
rows for the involution structure, cross-checked against a sympy brute force on
three rows and a from-scratch Rust implementation on `ell <= 9`, and against the
library on every row): `(CDL)` restricted to `j <= 6` holds for every
`ell >= 9`; the margin grows `+0.88` bits per unit `ell`; `(CDL)` as a
*hypothesis* (enough levels) first holds at `ell = 19` even / `ell ~ 21` odd;
`|Fix(tau) cap dual(E_j)| = 2^ceil(j/2)`; `A_j / (2^(n-j) Sigma_j) in
[0.0862, 0.3573]` at `j = 6`.

**OPEN**: `(CDL)` / `(CDL')` at every level `j >= 2`; `(TOY-1)` and `(TOY-2)`;
the sharp second moment `M_2 = O(ell 2^n)` at `q = 2` (identified here as the
higher-value target); a proved lower bound on `M_2`.

**UNVERIFIED / POINTERS ONLY**: Sawin--Shusterman arXiv:2008.09905 (hypotheses
not extracted from the full text); Sawin's refined random matrix model
arXiv:2409.02876 (a heuristic, flagged as the right fixed-`q` comparison for
numerics); the sub-agent's opinion that the large-`q` case of `(CDL)`'s object
follows from Katz equidistribution "in an afternoon"; the completeness of the
literature sweep beyond arXiv (the sub-agent's `WebSearch` quota was exhausted).

**NO THEOREM CREDIT** is claimed for the Lemire endpoint or for any lane lemma.
