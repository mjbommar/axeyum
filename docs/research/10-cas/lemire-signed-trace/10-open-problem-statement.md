# The missing estimate, stated for a specialist

Status: open-problem statement, 2026-08-22. This is the single analytic input
that closes the Kaser--Lemire chain over `F_2`, written in the form an expert
in Katz--Sawin monodromy, Artin--Schreier--Witt towers, or function-field
pair correlation could attack. Everything upstream and downstream of it is
proved (notes 00--09, the roadmap PDF). It is a fixed-`q = 2`,
growing-conductor **first-moment** cancellation estimate for a complete family
of Witt-vector Dirichlet characters.

## Notation

`E_j = (1 + x F_2[x])/x^{j+1}`, order `2^j`; its characters are the "even"
Hayes characters mod `x^{j+1}`. For a character `chi` of exact conductor `j`
and exact order `2^s`, `L(chi, T)` is a polynomial of degree `j-1`, pure of
weight one (inverse roots `|alpha| = sqrt 2`, Weil/RH), and
`S_n(chi) = sum_{deg F = n} Lambda(F) chi(<F>_j) = - sum_i alpha_i^n`. By Katz
(Witt vectors and a question of Keating and Rudnick, IMRN 2013), the family of
such `chi` is parametrized by `Prim_j subset prod_{k odd <= j} W_{e_k}(F_2)`,
`e_k = floor(log2(j/k)) + 1`, with universal sheaf `L_univ` lisse of rank
`j-1`; `S_n(chi) = -Tr(Frob_chi^n | L_univ)`.

Let `c = ceil(log2 ell)`, `Q` the largest power of two with `3cQ <= ell`,
`a = ell - c - 1`. For `s >= 1` the exact-order layer sum is
`T_{j,s}(n) = sum_{chi of exact conductor j and exact order 2^s} S_n(chi)`,
a rational integer (four-population identity, note 01), with `#X_{j,s}` such
characters, `#X_{j,s} = 2^{j-1-d_{s-1}}(R-1)` or `2^{j-1-d_s}` per the
resonance split (note 01).

## The estimate

> **(HWO).** For every `ell >= 200`, `n in {2ell+1, 2ell+2}`, every
> `a <= j <= ell`, and every nonempty layer with `2^s > Q`,
> `4 ell |T_{j,s}(n)| <= #X_{j,s} (j-1) 2^{ceil(n/2)}`.

Equivalently (cancelling `#X_{j,s}`), a factor `4 ell` saving over the
per-character Weil bound `|S_n(chi)| <= (j-1) 2^{ceil(n/2)}`, uniformly in
`ell`, for the *signed sum* over the layer. `(HWO)` implies `(REL)` implies
Kaser--Lemire (proved, notes 00--01; endpoint ledger replayed
`200 <= ell <= 1024`).

## Three faces (all proved equivalent to (HWO) at the relevant scale)

1. **Signed trace / virtual motive.** `T_{j,s}(n) = -Tr(Frob^n | M_{j,s})`
   where `M_{j,s}` is the virtual `H^1_c` of the four ASW quotient covers,
   pure of weight one, effective rank `#X_{j,s}(j-1)` (note 04, shape 1 -- the
   rank is exponential in `j`, so a cohomology *dimension* bound gives only
   Weil; the saving must come from `Frob`-eigenvalue phase cancellation, not
   from a smaller motive).
2. **Cylinder covariance.** With `K = ker(E_ell -> E_{a-1})` and
   `A_psi = sum_{g in K} N(g) psi(g)`, `(REL)` follows from `|A_psi| < 2^{ell-1}`
   for every nontrivial `psi`; `|A_psi|^2 = D_psi + C_psi` with covariance
   `C_psi = sum_{chi != chi'} S_n(chi) conj(S_n(chi'))` over the coset. Measured
   (note 07): `C_psi/D_psi` random in aggregate, bulk-negative per `psi`,
   unbounded-above tail.
3. **Sparse discrepancy.** `T_{j,s} = h_{j-1,s} Delta_{j,s} -
   [2^{s-1} nmid j] h_{j-1,s-1} Delta_{j,s-1}`, `Delta_{j,s} = 2P_{j,s} -
   P_{j-1,s}` the signed imbalance of the coefficient of `x^j` over the sparse
   power subgroup `2^s E_j` (`< 8 ell^3` classes).

## Why the standard tools do not reach it (proved, notes 03--09)

- Per-character / per-orbit / per-conductor absolute values reintroduce the
  factor `ell` (Weil is a phase-blind sup-norm; barrier I, note 03 sec 5:
  an explicit fake population with all moduli inside Weil has empty identity
  class).
- Every even moment is at the random (Gaussian / Sato--Tate) value
  (`M_2 = 0.967`, `M_4/M_2^2 ~ 2`, note 04 shape 5), so Cauchy--Schwarz and
  higher Holder are `40x` short at `ell = 200`; the estimate is genuinely
  first-moment.
- The one exact fixed-`q` mechanism, the Witt carry
  `T_s(a+b) = T_s(a)+T_s(b) - 2T_{s-1}(ab) - ...`, gives a small inner Gauss
  sum only at the Kerdock level `s-1 = 1`; for `s >= 3` the inner sum has full
  Weil magnitude (note 07, proved).
- Symmetry (barrier II, note 06) and explicit construction (barrier III,
  note 09) cannot address the named identity class.

## The precise questions for a specialist

1. **(Q1')** Fix `p = 2`, and for the representation `Xi` picking out the
   exact-order-`2^s` layer put

   ```text
   C(2,j,Xi)     = sum_i h^i_c(Prim_j (x) F_2-bar, Xi(L_univ)),
   i_max(2,j,Xi) = max { i : h^i_c(Prim_j (x) F_2-bar, Xi(L_univ)) != 0 }.
   ```

   Is the **pair** `(i_max, C)` inside the Deligne budget, i.e. is
   `C(2,j,Xi) <= (j-1) 2^{j-1-i_max/2} / (4 ell)`?  Equivalently, writing
   `k = 2j - i_max`, do the top `k` cohomological degrees vanish with
   `k >= 2 log2(8 ell C(2,j,Xi)/(j-1))` -- a *logarithmic* number of vanishing
   top degrees once `C` is polynomial in `j`?

   A bound on the Betti sum **alone is not enough**, and the earlier form of
   this question ("a polynomial-in-`j` bound would give `(HWO)`") was wrong: if
   `i_max` is `2j`, `2j-1` or `2j-2` then the budget forces `C < 1/4`, which is
   impossible for a nonzero cohomology however good the Betti bound
   ([12-horizontal-deligne-budget.md](12-horizontal-deligne-budget.md),
   Prop. 1).  `Prim_j` is `G_m x A^{j-1}` and the trace function of
   `Xi(L_univ)` is invariant under the `G_m`-action `x -> tx` on `E_j`, so
   `i_max >= j+1` always (ibid., Prop. 2): middle concentration is unavailable,
   and the sharp target is

   * **(Q1'-a)** `H^i_c(Prim_j (x) F_2-bar, Xi(L_univ)) = 0` for `i > j+1`;
   * **(Q1'-b)** `C(2,j,Xi) <= (j-1) 2^{(j-1)/2} / (8 ell)`, which follows from
     *any* polynomial-in-`j` Betti bound.

   Katz (IMRN 2013, proof of Thm 8.1) states that even a `p`-uniform bound on
   `C(p,n,Xi)` is unknown; his Thm 8.2 gives one only for `p > 2n-1` (where the
   Witt structure degenerates to ordinary Artin--Schreier), and its proof has
   the `i_max = 2 dim - 1` shape, which Prop. 1 shows can never reach `(HWO)`.
   Nothing is known toward (Q1'-a) for this family: in the literature,
   middle-degree concentration never comes from big monodromy, and `H^{2d-1}_c`
   is controlled by no theorem we could find.
2. Does the joint monodromy of the pair `(L_univ, L_univ o [x -> x^{2^s}])`
   over `Prim_j` at `p = 2` force first-moment cancellation of the layer sum --
   a "horizontal" (conductor-aspect, fixed field) equidistribution -- rather
   than the vertical (`q -> infinity`) statements of Katz/Sawin?
3. Is a fixed-`q` pair-correlation / variance theorem for a fixed-conductor
   Hayes family provable, even weakly (a power saving `2^{-delta j}` over the
   diagonal in `C_psi`)? Its integer analogue is conditional on GRH plus a
   pair-correlation hypothesis (Kandhil--Languasco--Moree 2026); its known
   function-field analogues (Keating--Rudnick, Sawin) are all `q -> infinity`.

An affirmative answer to any one closes Kaser--Lemire over `F_2` for all `n`.
A proof must be uniform in `ell`, genuinely characteristic-two and
prime-power-modulus applicable, and first-moment (not a variance/second-moment
bound, which the data show is already at the random value and `40x` short).

## Reproducibility

Notes 00--09, note 12 (the Deligne budget behind the corrected Q1', with the
exact `q`-aspect experiment that measures `i_max` at small `(n,j)`), and
`scripts/lemire-signed-trace/` (flint-backed exact data to
`ell = 24`, cross-checked against the branch CAS and the roadmap pins); facts
`F:gf2-lemire-cylinder-twist-sup-bound` (open, the minimal sufficient
statement) and `F:gf2-lemire-cyclotomic-infinite-family` (proved).
