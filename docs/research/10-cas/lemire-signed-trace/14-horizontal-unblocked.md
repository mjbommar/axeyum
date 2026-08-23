# Is the horizontal route unblocked? The `G_m`-quotient reduction, the monodromy transition at `p = 2`, and the verdict

Status: research note, 2026-08-22. Angle **4b** of the backward-chains diary
([11-backward-chains-diary.md](11-backward-chains-diary.md)), the priority
follow-up asked for in
[12-horizontal-deligne-budget.md](12-horizontal-deligne-budget.md) sec. 9.
It (i) restates the Deligne budget in the form the `(HWO)` range actually
needs, (ii) verifies and corrects the coordinator's Leray reduction along the
`G_m`-torsor, (iii) reports a new exact engine that resolves conductor levels
`j = 4, 5, 6, 7` -- levels the window scan of note 12 could not reach -- and
(iv) locates the monodromy transition at `p = 2`.

Script: `scripts/lemire-signed-trace/lemire_horizontal_quotient.py` (nine
controls, six mutation controls, exits nonzero). Bulk engine: new Rust bin
`axeyum-lemire-lfunc` (mirrored as
`scripts/lemire-signed-trace/axeyum-lemire-lfunc.rs.txt`). Data:
`data/lfunc-dumps/` (raw engine output), `data/horizontal-lfunc-weights.txt`
(generated table).

## 0. Summary

- **The target of note 12 was set too high.** In the range `(HWO)` actually
  uses -- `a <= j <= ell` with `a = ell - ceil(log2 ell) - 1`, so
  `ell/(j-1) -> 1` -- the budget inequality `2^{k/2} >= 8 ell C/(j-1)` reads
  `k >= 6.15 + 2 log2 C`, **uniformly in `ell`** (`6.01 .. 6.15` for
  `200 <= ell <= 1024`). So what is needed is that the top **six or seven**
  cohomological degrees vanish, not concentration in degree `j+1`. Note 12
  has this in its table row (`k >= 6`) but then calls `i_max = j+1` "the sharp
  target"; `i_max = j+1` is *far* stronger than necessary once `j >= 8`.
- **What the data measure is not `i_max` but `delta`,** the top Frobenius
  **weight** minus `n`. Since `|A_r| <= C q^{w_max/2}` and `delta = w_max - n`,
  the estimate follows from `delta <= 2j - 2 log2(8 ell C/(j-1))`, and
  `delta <= i_max` always. `delta` is exactly what growth in `r` reads off.
- **The `G_m`-action is free iff `gcd(j, q-1) = 1`** -- equivalently
  `gcd(j_odd, 2^r - 1) = 1` -- **not** "when `j | q-1`" as note 12 guessed.
  Geometrically the action is free iff `j` is a power of two; otherwise the
  non-free locus has dimension `<= floor(j/3)`, which is invisible in every
  degree `>= j+1`, so the Leray reduction survives. (Proved, sec. 4; the
  mutation control `--mutate 6` kills the note-12 criterion at `(j,r) = (6,2)`.)
- **The Leray bookkeeping is verified** (sec. 5) and gives
  `H^i_c(Prim_j, F) = H^{i-1}_c(B,G) (+) H^{i-2}_c(B,G)(-1)`,
  `A_r = (q-1) sum_{b in B(F_q)} Tr(Frob_b | G)`, `C = 2 C'`,
  `i_max = i'_max + 2`. The two remaining statements are (T1) and (T2) of
  sec. 5.3; the *sufficient* weakening (T1') asks only that the top
  `7 + 2 log2 C'` degrees on `B` vanish.
- **New engine.** The `L`-function route of note 12 sec. 6, made exact in
  `Z[zeta_8]` by an explicit basis of `E_j` (sec. 3). Cost `~ j q^j log q`,
  **independent of `n`**: every `n` comes out of one run. It reproduces the
  note-12 window-scan grid on **136** overlapping `(n,j,r)` cells and every
  note-12 closed form, and reaches `(j, r_max) = (4,8), (5,6), (6,5), (7,4)`
  where the window scan stopped at `(4,6), (5,5), (6,4)`.
- **The monodromy transition is at `j_0 = 4`, and it is a THEOREM.** Katz,
  IMRN 2013, Thm. 5.1: `G_geom` contains `SL(j-1)` for every prime `p` and
  every `j >= 3` **except `(p,j) = (5,3)` and `(2,3)`** -- characteristic two
  is fully covered from `j = 4` on. Gorodetsky, FFA 56 (2019), Lemma 3.5
  settles the exception: at `(p,j) = (2,3)` the normalised eigenvalues are
  roots of unity of order dividing 24, so `G_geom` is finite. Sec. 8 confirms
  both mechanically, by an exact integer identity rather than root-finding:
  order `| 8` at `j = 2`, order `| 24` at `j = 3` for every `r <= 4`, and no
  order `<= 100` at `j = 4, r = 1` (nor `<= 24..52` at `r = 2,3,4`), none at
  `j = 6, 7`. **This corrects the diary**, which attributed the `p > 2n-1`
  hypothesis to Katz's monodromy theorem; it belongs to his Thm. 8.2, the
  Betti/Weyl-sum bound, and exists only because a uniform Betti bound is
  missing.
- **`H^{2j}_c = 0` for every `j >= 4` and `n != j-1`** (Lemma D, sec. 5.4):
  big monodromy plus the hook decomposition of the Adams operation. So the
  worst case seen at `(8,2)` and `(12,2)` -- a class of weight exactly
  `n + 2j` -- **cannot occur past the transition**, unconditionally.
- **Past the transition the maximal top-degree classes do not persist.** Nine
  of the ten cells with `j >= 4`, `n >= j` that resolve to an exact closed form
  have `delta in {j, j+1}` -- the `G_m`-forced optimum -- while every exactly
  resolved `j <= 3` cell with `n >= 2j+1` has `delta in {2j-1, 2j}`. The tenth,
  `(12,5)`, resolved only after the late `(5,7)` run (sec. 7.2 addendum), has
  `delta = 8 = j+3 = 2j-2`: above the optimum, below the `2j-1` law, and at
  `n = 0 mod 4`, the residue class that was worst at `j = 2`. At `j = 5` the two
  laws are one integer apart there, so it does not separate them. Note 12's
  own unresolved `(7,4)` is in fact `delta = j+1` with `C = 6`. On the critical
  line, `delta` regressed on `j = 2..7` has slope `1.298 +- 0.193`: the `j+1`
  law (slope 1) is within `1.5 sigma`, the `2j-1` law (slope 2) is `3.6 sigma`
  away, and the fit is biased *upward*. See sec. 7.
- **The `q = 2` data refute hypothesis (H) of note 12** and give
  `delta_1 = (1.003 +- 0.144) j + 2.3` over `14 <= j <= 24` (56 points). But a
  `q = 2` measurement bounds `i_max` from **below**, and slope 1 is also the
  square-root-cancellation value, so sec. 9 is supporting evidence, not the
  decisive part.
- **(T1) is a named open hypothesis.** The degree statement the route needs is
  Sawin's Hypothesis `H(n,r,r~,w)` (arXiv:1810.01303, ANT 14 (2020)) on the
  same space `Prim_n`, with `w = j - 6.15 - 2 log2 C` -- the *weakest*
  nontrivial case. His only unconditional input (Lemma 5.3) reads
  `w = n + 1 - ((p-2r)/p^r) n` and its proof begins "We may assume `p > 2r` as
  if `p <= 2r` then the claim ... is vacuous": **at `p = 2` it is vacuous for
  every `r`, and at `p >= 3` it already clears what we need.** The lane's
  obstruction is exactly the characteristic-two case of that lemma.
- **(T2) is short by an exponential.** The best uniform-in-`p` Betti bound on
  `Prim_j` in print (Sawin, arXiv:1810.01303, Lemma 2.11) gives
  `2^{O(j log j)}` for `Xi_n(L_univ)` on the critical line, against the
  `~2^{j/2}` the budget allows *even under full middle concentration*.
- **Verdict: ALIVE.** See sec. 10.

## 1. What angle 4 left open

Note 12 established: `Prim_j = G_m x A^{j-1}`; the trace function of
`Xi_n(L_univ)` is `G_m`-invariant, so `i_max >= j+1`; `j = 2` is solved in
closed form; the three in-range rows that both resolve and separate the shapes
(`(8,2)`, `(12,2)`, `(7,3)`) all have `i_max >= 2j-1`; `j >= 4` on the critical
line does not resolve, because the window scan costs `q^{n-j+1} = q^{j+2}`
there. The coordinator's addendum then observed that `j <= 3` sits in a
finite-monodromy regime, and that the lane's `F_2` layer data at `ell = 24` are
the size of the *alive* case.

Angle 4b answers the two questions that leaves: **do the top-degree classes
persist past the finite-monodromy regime**, and **what exactly remains to
prove**.

## 2. The budget, restated

Notation as in note 12 sec. 2. `X = Prim_j`, `R = j-1`, `M = #X(F_2) = 2^{j-1}`,
`G = 4 ell` the required saving, `C = sum_i h^i_c`, `i_max` the top
non-vanishing degree, `w_max` the top Frobenius weight actually present, and

```text
delta := w_max - n      (so delta <= i_max, by Deligne's weight bound).
```

Deligne gives `|A_r| <= C 2^{r w_max/2} = C 2^{r(n+delta)/2}`; the trivial bound
is `R M 2^{rn/2}` at `r = 1`. The saving is
`Sav = R M / (C 2^{delta/2}) = (j-1) 2^{j-1-delta/2}/C`, so

```text
(BUDGET)   4 ell <= Sav   <=>   2^{(2j-delta)/2} >= 8 ell C/(j-1)
                          <=>   delta <= 2j - 2 log2(8 ell C/(j-1)).
```

`(HWO)` is asked only for `a <= j <= ell`, `a = ell - c - 1`,
`c = ceil(log2 ell)`. Hence `ell/(j-1) <= ell/(a-1) = 1 + O(log ell / ell)`,
and the right-hand side is **`8 C` up to 6%**:

| `ell` | `j` | `C` | `k = 2j - delta` must be `>=` |
| --- | --- | --- | --- |
| 200 | 191 | 1 | 6.15 |
| 200 | 200 | 1 | 6.01 |
| 1024 | 1013 | 1 | 6.03 |
| 1024 | 1024 | 4 | 10.00 |
| 200 | 191 | 16 | 14.15 |

> **Proposition 1'.** In the `(HWO)` range, `(HWO-agg)` follows from Deligne's
> bound as soon as
>
> ```text
> delta(n,j) <= 2j - 6.15 - 2 log2 C(2,j,Xi_n),
> ```
>
> uniformly for `200 <= ell <= 1024` (and with `6.15` replaced by
> `2 log2 8 = 6` in the limit `ell -> infinity`). In particular a Betti sum
> polynomial in `j`, `C = j^A`, needs only `delta <= 2j - 6.15 - 2A log2 j`.

This is the same inequality as note 12's Proposition 1; the point is the range.
Note 12's rows "`i_max = 2j`, `2j-1`, `2j-2` are impossible" remain correct
(they are `k = 0, 1, 2`), and so does "`i_max = j+1` leaves exponential room".
What changes is the **target**: `j+1` is not the thing to prove. `2j - 7` is.

Two consequences worth stating explicitly.

- **The small rows cannot satisfy the budget whatever happens on them.** At
  `(n,j) = (7,3)`, `ell = 3` and the requirement is `k >= 2 log2(8*3*C/2)`,
  i.e. `k >= 6.9` for `C = 1`, against `2j = 6`. Even `H^*_c` concentrated in
  the *lowest* possible degree `j = 3` would give `k = 3`. So `(7,3)` is
  outside the budget for a reason that has nothing to do with its cohomology,
  and its `i_max = 2j-1` is evidence about the **shape**, not a counterexample
  to the estimate. Room first appears when `j - 1 >= 6.15 + 2 log2 C`, i.e.
  `j >= 8` for `C = 1` -- *below every `j` we can compute*.
- **`delta`, not `i_max`, is what the experiment sees, and it is also what the
  estimate needs.** A proof, though, must control one of the two: either a
  degree theorem (T1)/(T1') or a weight theorem.

## 3. Proposition A: an explicit basis of `E_j`, and why the engine is exact

> **Proposition A.** Let `q = 2^r`, `z` a generator of `F_q^*`, and for `k` odd,
> `k <= j`, `0 <= l < r`, put `h_{k,l} = 1 + z^l x^k in E_j`. Then
>
> ```text
> E_j = prod_{k odd <= j} prod_{l=0}^{r-1} <h_{k,l}>,   ord(h_{k,l}) = 2^{e_k},
> e_k = floor(log2(j/k)) + 1,   sum_{k odd <= j} e_k = j.
> ```
>
> Consequently `exponent(E_j) = 2^{floor(log2 j)+1}`; a character `chi` has
> exact conductor `j` (i.e. does not factor through `E_{j-1}`) **iff some
> exponent of `chi` in the block `k_0 := odd part of j` is odd**; and
> `#Prim_j(F_q) = q^{j-1}(q-1)` for every `q`.

*Proof.* In characteristic two `(1 + a x^k)^2 = 1 + a^2 x^{2k}`, so
`h_{k,l}^{2^i} = 1 + z^{l 2^i} x^{k 2^i}` **exactly**, and the order of
`h_{k,l}` is the least `2^{e}` with `k 2^{e} > j`, i.e. `2^{e_k}`. For
surjectivity use the filtration `U_m = 1 + x^m F_q[x] mod x^{j+1}`, whose
graded pieces `U_m/U_{m+1}` are `F_q^+`: writing `m = k 2^i` with `k` odd, the
elements `h_{k,l}^{2^i} = 1 + z^{l2^i} x^m` have `x^m`-coefficients
`{(z^l)^{2^i}}_{l<r}`, an `F_2`-basis of `F_q` because Frobenius is bijective.
Peeling `m = 1, 2, ..., j` therefore writes every `g in E_j` as a product of
the `h_{k,l}` with exponents in `Z/2^{e_k}`, and the orders multiply to
`q^{sum e_k} = q^j = #E_j`, so the product is direct. `sum_{k odd <= j} e_k =
sum_{k odd} #{i >= 0 : k2^i <= j} = #{m : 1 <= m <= j} = j`.

For the conductor: `E_{j-1} = E_j/U_j` and `U_j = {1 + cx^j}` is exactly the
image of `h_{k_0,l}^{2^{i}}`, `j = k_0 2^{i}`, `e_{k_0} = i+1`. So
`chi|_{U_j} = 1` iff `2^{i} v_{k_0,l} = 0 mod 2^{e_{k_0}}` for all `l`, iff
every `v_{k_0,l}` is even. Counting: `q^j - q^{j-1}`. QED

Proposition A is an elementary re-derivation of Katz's `Prim_j = G_m x A^{j-1}`
(note 12, Prop. 2(i)): the `k_0`-block is `W_{e_{k_0}}(F_q)`, the condition
"some exponent odd" is "the initial Witt component is a unit", and
`W_e^x = G_m x A^{e-1}`.

It is also what makes the computation exact. For `j <= 7`, `e_1 = 3`, so every
character value lies in `mu_8` and every quantity below is an element of
`Z[zeta_8] = Z[T]/(T^4+1)` computed in integer arithmetic. Control C1 of the
script verifies the orders and that the discrete logarithm is a bijection.

## 4. Proposition B: exactly when the `G_m`-action is free

`G_m` acts on `E_j` by `sigma_t : x -> tx`; on big-Witt coordinates
`g = prod_m (1 - a_m x^m)` it is `a_m -> t^m a_m` (diagonal), and it acts on
characters by `chi -> chi o sigma_t`.

> **Proposition B.** For `t in F_q^*` of order `o`:
> `#{g in E_j : sigma_t g = g} = q^{floor(j/o)}`, hence
> `#{chi : chi o sigma_t = chi} = q^{floor(j/o)}` as well, of which
> `q^{floor(j/o)-1}(q-1)` have exact conductor `j` when `o | j` and **none**
> when `o nmid j`. Therefore
>
> ```text
> the G_m-action on Prim_j(F_q) is free  <=>  gcd(j, q-1) = 1
>                                        <=>  gcd(j_odd, 2^r - 1) = 1,
> ```
>
> and over `F_2bar` the action is free iff `j` is a power of two. When it is
> not, the non-free locus `Z subset Prim_j` has `dim Z <= floor(j/3)`.

*Proof.* Fixed points: `b_m t^m = b_m` for all `m <= j`, i.e. `b_m = 0` unless
`o | m`; there are `floor(j/o)` free coordinates. For the dual, for an abelian
`A` and an automorphism `s`, `chi o s = chi` iff `chi` kills `Im(s-1)`, so the
count is `#A/#Im(s-1) = #ker(s-1)`. If `t^j != 1` then `sigma_t - 1` is
bijective on `U_j = F_q^+` (multiplication by `t^j - 1`), so `Im(sigma_t-1)`
contains `U_j` and every fixed character kills `U_j`, i.e. has conductor `< j`.
If `t^j = 1` then, comparing `#(Im(sigma_t-1) cap U_j)` computed through the
equivariant surjection `E_j -> E_{j-1}`, that intersection is trivial, so
fixed characters of exact conductor `j` exist, `q^{floor(j/o)-1}(q-1)` of them.
Finally `t^j = 1` with `t in F_q^*` iff `ord(t) | gcd(j, q-1) = gcd(j_odd,
2^r-1)` (`2^r - 1` is odd). Over `F_2bar`, `mu_j = mu_{j_odd}` is nontrivial
unless `j` is a power of two, and every stabiliser has order `o >= 3`, so
`dim Z <= max_{o >= 3, o | j_odd} floor(j/o) <= floor(j/3)`. QED

**This corrects note 12**, which wrote "a stabilizer could survive when
`j | q-1`". The correct condition is `gcd(j, q-1) > 1`, and the two differ:
at `(j,r) = (6,2)`, `j | q-1` is false but `gcd(6,3) = 3` and there really are
`q^{floor(6/3)-1}(q-1) = 12` stabilised exact-conductor characters. The
script's `--mutate 6` installs note 12's criterion and control C9 kills it on
exactly that cell.

The engine reports `free=0` at `(3, r even)`, `(5, 4 | r)`,
`(6, r even)`, `(7, 3 | r)` -- and `(q-1) | A_r` (note-12 control C5) holds on
**every** row anyway, free or not.

**The non-free locus is harmless in the degree range that matters.** With
`U = Prim_j \ Z` open and `dim Z <= floor(j/3)`, the excision sequence gives
`H^i_c(U, F) = H^i_c(Prim_j, F)` for `i > 2 floor(j/3)`, and
`2 floor(j/3) < j + 1` for every `j >= 1`. So every statement below about
degrees `>= j+1` may be made on `U`.

## 5. The Leray reduction, verified

### 5.1 Bookkeeping

Let `pi : U -> B := U/G_m` be the quotient, a `G_m`-torsor with `B` smooth of
dimension `j-1` and `#B(F_q) = #U(F_q)/(q-1)` (`= q^{j-1}` when the action is
free on all of `Prim_j`, since `H^1(F_q, G_m) = 0`).

> **Hypothesis (D).** `F := Xi_n(L_univ)|_U = pi^* G` for a virtual lisse `G`
> on `B` of virtual rank `j-1`.

(D) is **proved at `j = 2`** (note 12 sec. 6: `alpha(chi_c)` depends on
`c = (c_0,c_1)` only through the `G_m`-invariant `d = c_1/c_0^2`, and Chebotarev
determines the semisimplification). For general `j` the trace function is
`G_m`-invariant (note 12, Prop. 2(iii), proved), so `t^* F` and `F` have equal
trace functions and hence isomorphic semisimplifications; upgrading this to a
`G_m`-equivariant structure -- which is what descent needs -- is the content of
(D), and it is natural: `pr_2 : A^1 x Prim_j -> Prim_j` is `G_m`-equivariant
for the diagonal action, so (D) follows from `G_m`-equivariance of Katz's
`Lcal_univ`. **We do not prove that here.**

Under (D), with `Rpi_! Q_l = Q_l[-1] (+) Q_l(-1)[-2]` (the compactly supported
cohomology of `G_m`) and the projection formula
`Rpi_!(pi^* G) = G (x) Rpi_! Q_l`:

```text
H^i_c(U, F) = H^{i-1}_c(B, G) (+) H^{i-2}_c(B, G)(-1),                (LERAY)
A_r(n,j)    = (q-1) sum_{b in B(F_q)} Tr(Frob_b | G),
C           = 2 C',        C' := sum_i h^i_c(B, G),
i_max       = i'_max + 2,  i'_max := max{i : H^i_c(B,G) != 0}.
```

The direct sum has no cancellation, so the last line is an equality, not a
bound. The two summands differ by a Tate twist, so the top **weight** upstairs
is `2 + w'_max` where `w'_max` is the top weight on `B` -- i.e.
`delta = delta' + 2` with `delta' = w'_max - n`.

Artin vanishing on the affine `Prim_j` gives `H^i_c(Prim_j, F) = 0` for
`i < j`, hence `i'_max >= j-1` whenever the cohomology is nonzero, hence
`i_max >= j+1`: this is note 12's Prop. 2(v), re-derived, and it says the
`G_m` factor costs exactly two degrees.

### 5.2 The two small `j` as a check on the bookkeeping

- **`j = 2`, `B` a curve.** `H^i_c(B,G)` can be nonzero only for `i = 1, 2`
  (`H^0_c = 0` for a lisse sheaf on an affine curve), so `i'_max in {1,2}` and
  `i_max in {3,4} = {2j-1, 2j}`. `i_max = 4` exactly when
  `H^2_c(B,G) = G_{pi_1}(-1) != 0`, i.e. when there are geometric coinvariants.
  That is **precisely** note 12's Proposition 3: `i_max = 2j-1` for odd `n`,
  `2j` for `n = 0 mod 4`, `H^*_c = 0` for `n = 2 mod 4`, always with `C = 2`,
  i.e. `C' = 1`. Middle concentration at `j = 2` is automatic modulo
  invariants, and the coordinator's claim (2) is verified.
- **`j = 3`, `B` a surface.** Now the content of (T1) is
  `H^3_c(B,G) = H^4_c(B,G) = 0`, dually `H^0(B,G^v) = H^1(B,G^v) = 0`. At
  `(n,j) = (7,3)` note 12 measures a class of weight `n+5`, so `i_max >= 5`,
  so `i'_max >= 3`, so `H^1(B, G^v) != 0`. Sec. 8 shows why: at `j = 3` the
  geometric monodromy is **finite** (every normalised Frobenius eigenvalue is
  a 24th root of unity, at every `r <= 4`), and for a finite monodromy group
  `H^1` of a nontrivial irreducible has no reason to vanish. The coordinator's
  claim (3) is verified, mechanism included.

### 5.3 What remains, sharply

Poincare duality on the smooth `(j-1)`-fold `B` turns `H^{i'}_c(B,G)` into
`H^{2(j-1)-i'}(B, G^v)^v(-(j-1))`. Combining with (LERAY):

> **Lemma C.** Under (D), and with `k_min := min{k : H^k(B (x) F_2bar, G^v)
> != 0}`,
>
> ```text
> 2j - i_max(Prim_j, Xi_n L_univ) = k_min.
> ```

So the number `k` of vanishing top degrees that the budget of Proposition 1'
demands is **exactly the connectivity of `G^v` on `B`**: how many of
`H^0, H^1, H^2, ...` vanish. Restating Proposition 1':

> **(T1) The degree statement.** For `n in {2ell+1, 2ell+2}` and
> `a <= j <= ell`,
>
> ```text
> H^k(B (x) F_2bar, G^v) = 0   for all k <= 5.15 + 2 log2 C,
> ```
>
> i.e. `k_min >= 6.15 + 2 log2 C`. Full middle-degree concentration on `B`
> (equivalently `i_max = j+1`, the `G_m`-forced optimum) is `k_min >= j-1`,
> which is far more than is needed once `j >= 8`.

> **(T1w) The weight statement, which is what the estimate really needs.** The
> top Frobenius weight in `H^*_c(Prim_j (x) F_2bar, Xi_n L_univ)` is at most
> `n + 2j - 6.15 - 2 log2 C`; i.e. `delta <= 2j - 6.15 - 2 log2 C`.
> `delta <= i_max` always, so (T1) implies (T1w); and `delta` is exactly what
> the experiment below measures.

> **(T2) The Betti statement.** `C = 2 C' <= (j-1) 2^{j-1-i_max/2}/(4 ell)`;
> with `i_max = j+1` this is `C' <= (j-1)2^{(j-1)/2}/(16 ell)`. Under full
> concentration `C' = h^{j-1}_c(B,G) = |chi_c(B, G)|`, an Euler
> characteristic.

`B` is a smooth quasi-affine `(j-1)`-fold with `#B(F_q) = q^{j-1}` (free case)
carrying a lisse `G` of rank `j-1`. **We do not claim `B = A^{j-1}`**; that is
proved only at `j = 2`, where `B = A^1` with coordinate `d = c_1/c_0^2`.
Artin vanishing is not needed on `B`: the lower half comes from the affine
`Prim_j` upstairs.

### 5.4 `k_min >= 1` is a theorem at `p = 2`, for every `j >= 4`

> **Lemma D.** Let `j >= 4` and `n != j-1`. Then
> `H^{2j}_c(Prim_j (x) F_2bar, Xi_n(L_univ)) = 0` and
> `H^{2(j-1)}_c(B (x) F_2bar, G) = 0`; equivalently `k_min >= 1`. In
> particular the "no cancellation at all" case `i_max = 2j` seen at `(8,2)`
> and `(12,2)` **cannot occur for any `j >= 4`**, and `i_max <= 2j-1` with
> equality iff `H^1(B (x) F_2bar, G^v) != 0`.

*Proof.* `H^{2j}_c(X,F) = F_{pi_1^{geom}}(-j)` for `X` smooth of dimension `j`.
Katz, *Witt vectors and a question of Keating and Rudnick*, IMRN 2013, Thm. 5.1
(restated as his Thm. 7.1), **verbatim**: "Let `p` be a prime, and `n >= 3`.
Then `Ggeom` contains `SL(n-1)` except in the cases `(p = 5, n = 3)` and
`(p = 2, n = 3)`." His `n` is our `j`, so at `p = 2` and `j >= 4` the geometric
monodromy group of `L_univ` on `Prim_j` contains `SL_{N}`, `N = j-1`. The
`n`-th Adams operation decomposes into hooks,
`psi^n = sum_{k=0}^{N-1} (-1)^k s_{(n-k,1^k)}` (each hook once), and
`(S^lambda V)^{SL_N} != 0` only for rectangular `lambda = (m^N)`; a hook with
`k+1` rows is rectangular only if `n - k = 1` and `k+1 = N`, i.e. `n = N =
j-1`. Coinvariants for a group containing `SL_N` are a quotient of the
`SL_N`-coinvariants, hence zero for every constituent, hence zero. For `B`:
`pi_1^{geom}(U) -> pi_1^{geom}(B)` is surjective and `F = pi^* G`, so `G` and
`F` have the same monodromy image and the same (co)invariants. QED

This is the one piece of (T1) that is unconditional at `p = 2`, and it is
exactly the piece Gorodetsky--Sawin (Math. Ann. 376 (2019), arXiv:1811.04834,
proof of their Thm. 9) use: "top cohomology vanishes" is `H^{2 dim}_c` and
nothing beyond. The gap between what is proved (`k_min >= 1`) and what is
needed (`k_min >= 6.15 + 2 log2 C`) is the whole remaining problem.

## 6. The engine

**Algorithm.** For `chi` a character of `E_j`, `F -> chi(<F>_j)` is completely
multiplicative, so `L(chi,T) = sum_m c_m(chi) T^m` with
`c_m(chi) = sum_{deg F = m} chi(<F>_j)`. For `m >= j` the fibres of
`F -> <F>_j` are `q^{m-j}` cosets and `c_m = 0`; for `m < j` the map is
injective with image `V_m = {1 + b_1x + ... + b_mx^m}`, so
`c_m(chi) = sum_{v in V_m} chi(v)`. Then `e_k = (-1)^k c_k`, Newton's
identities give the power sums, `S_n(chi) = -p_n`, and
`A_r(n,j) = sum_{exact conductor j} S_n(chi)`.

Computing `c_m` for **all** `q^j` characters at once is one Fourier transform
over `E_j`; by Proposition A the group is `prod (Z/2^{e_k})^r` with all
`e_k <= 3`, so the transform is a mixed-radix DFT with 8th-root-of-unity
kernels and runs in exact `Z[zeta_8]` integer arithmetic. Cost
`~ j q^j log q` and **independent of `n`**, against `q^{n-j+1} = q^{j+2}` for
the window scan on the critical line. Memory is held down by blocking the
transform: the last radix-2 generators are split off into a `G_2` whose
character is a `+-1` sign, giving `j q^{j-1}` machine words.

**Reached cells** (24 threads, minutes each):
`j = 2: r <= 10`; `j = 3: r <= 8`; `j = 4: r <= 8`; `j = 5: r <= 7`;
`j = 6: r <= 5`; `j = 7: r <= 4`. The binding constraints are the `q^j`
character loop (time) and `j q^{j-1}` words (memory).

**Controls** (the script exits nonzero on any failure).

* `C0` the field modulus is **primitive**, checked by requiring `exp[0..q-2]`
  to be a bijection onto `F_q^*` -- not by `assert(a == 1)`, which the AES
  polynomial passes (note 12's bug).
* `C1` Proposition A: `ord(1 + z^l x^k) = 2^{e_k}` exactly (both divides and
  does not divide `2^{e_k - 1}`) and the discrete logarithm is a bijection onto
  `prod Z/2^{e_k}`.
* `C2` **Weil, per character**: `|c_{j-1}(chi)|^2 = q^{j-1}` (so `deg L = j-1`
  and all `|alpha_i| = sqrt q`) and the functional equation
  `conj(c_m(chi)) c_{j-1}(chi) = q^m c_{j-1-m}(chi)` for every `m`. Exact in
  `Z[zeta_8]`.
* `C3` `A_r(n,j)` is a rational integer (its `Z[zeta_8]` coordinates
  `1, T, T^2, T^3` beyond the first must vanish).
* `C4` `(q-1) | A_r(n,j)` -- note 12's C5, the `G_m` divisibility.
* `C5` agreement with the note-12 **window-scan** grid
  `data/horizontal-grid.txt`, an entirely different algorithm: **136**
  overlapping `(n,j,r)` cells, exact.
* `C6` agreement of the pure-Python engine with the Rust bulk engine on every
  overlapping cell.
* `C7` the note-12 closed forms: Proposition 3 (`j = 2`, all `n mod 4`),
  `A_r(7,3) = 64^r - 32^r`, `A_r(9,3) = -(q-1)q^5` (i.e. `N_3(1) = q^{n-3}`),
  and `A_r(7,4) = -(q-1)q^4(q+1)` for `3 nmid r`, `+(q-1)q^4(2q-1)` for `3|r`.
* `C8` `#Prim_j(F_q) = q^{j-1}(q-1)`.
* `C9` Proposition B: freeness matches `gcd(j_odd, 2^r-1) = 1` against a
  direct orbit computation.

**Mutation controls** (`--mutate K`), each killed by a *different* named check:
`1` `e_k` off by one -> C1; `2` wrong character weight (`zeta_16` for
`zeta_8`) -> C2; `3` drop the exact-conductor filter -> C8; `4` drop the
`(-1)^k` in `e_k = (-1)^k c_k` -> C5; `5` the AES modulus at `r = 8` -> C0;
`6` note 12's freeness criterion `j | q-1` -> C9.

A seventh, structural control is built into the Rust engine: the answer must
not depend on how the transform is blocked. Running `--g2bits b` for
`b = 0,2,4,5,6` at `(j,r) = (5,3)` gives byte-identical output. It earned its
keep immediately: with `b > r` the `k_0`-block straddles the split, the naive
conductor filter admitted conductor-`(j-1)` characters, and control C2 fired
on the first of them (`deg L < j-1`, so `|c_{j-1}|^2 != q^{j-1}`).

## 7. New cells

`delta = w_max - n` is the top Frobenius weight above `n`; `CLOSED` means an
exact fit `A_r = (q-1) q^k P_{r mod m}(q)` with integer `P`, verified on at
least one `r` beyond those used to solve. Rows marked `*` are the critical
line `n in {2j+1, 2j+2}` that `(HWO)` needs.

### 7.1 Exactly resolved cells: `j <= 3` sit at the top, `j >= 4` at `j`/`j+1`

Every `(n,j)` with `n >= j` for which the closed-form fit closes and verifies.
`delta` is exact; `C` is the number of Frobenius modes in the fit (an exact
value, not a bound, whenever the fit is over-determined).

```text
    j    n   r<=   delta        j   j+1   2j-1   2j    C     shape
    2    3    8      3          2    3     3     4     2     top
    2    4    8      4          2    3     3     4     2     top  (H^{2j}_c != 0)
    2    5 *  8      3          2    3     3     4     2     top
    2    6 *  8      A == 0 identically
    2    7    8      3          2    3     3     4     1     top
    2    8    8      4          2    3     3     4     1     top  (H^{2j}_c != 0)
    2    9    8      3          2    3     3     4     1     top
    2   11    8      3          2    3     3     4     2     top
    2   12    8      4          2    3     3     4     2     top  (H^{2j}_c != 0)
    2   13    8      3          2    3     3     4     2     top
    3    3    8      3          3    4     5     6     2     j
    3    4    8      4          3    4     5     6     2     j+1
    3    5    8      5          3    4     5     6     2     2j-1
    3    6    8      4          3    4     5     6     2     j+1
    3    7 *  8      5          3    4     5     6     1     2j-1
    3    8 *  8      6          3    4     5     6     2     2j   (H^{2j}_c != 0)
    3    9    8      3          3    4     5     6     1     j
    3   10    8      4          3    4     5     6     1     j+1
    3   11    8      5          3    4     5     6     2     2j-1
    3   12    8      6          3    4     5     6     2     2j   (H^{2j}_c != 0)
    4    7    8      5          4    5     7     8     6     j+1
    4    4    8      A == 0;   4   12    8   A == 0
    5    5    6      5          5    6     9    10     4     j
    5    6    6      6          5    6     9    10     4     j+1
    6    6    5      6          6    7    11    12     2     j
    6    8    5      6          6    7    11    12     2     j
    6    9    5      7          6    7    11    12     4     j+1
    7    7    4      7          7    8    13    14     3     j
    7    8    4      8          7    8    13    14     1     j+1
```

**Read the last column.** Every exactly resolved row with `j <= 3` and
`n >= 2j+1` sits at `2j-1` or `2j`. **Every exactly resolved row with
`j >= 4` sits at `j` or `j+1`** -- i.e. exactly the `i_max = j+1` shape, the
`G_m`-forced optimum, in nine of the ten such rows across `j = 4, 5, 6, 7`
(the exception, `(12,5)` with `delta = 8`, is discussed in the 7.2 addendum). The rows
at `j >= 4` are below the critical line (the closed-form fit needs more `r`
than the critical rows leave), but they are *exact*, and they are on the far
side of the monodromy transition of sec. 8.

`(7,4)` deserves a line of its own, because it is note 12's own unresolved row:
`A_r(7,4) = -(q-1)q^4(q+1)` for `3 nmid r` and `+(q-1)q^4(2q-1)` for `3 | r`
(reproduced here as control C7). Top weight `2*6 = 12`, `delta = 5 = j+1`,
`C = 6`. Note 12 could only say "cube roots of unity already at `(7,4)`"; the
row is in fact the good shape.

### 7.2 The critical line

`delta_r := 2 log2|A_r(n,j)|/r - n` converges to `delta` with bias
`+2 log2(C')/r`, so the entries below are, for a leading coefficient `>= 1`,
**upper** estimates that improve with `r`.

```text
   j   n      delta_r for r = 1 .. r_max                                 j+1  2j-1  2j
   2   5    1.00  2.59  2.87  2.95  2.98  2.99  3.00  3.00               3    3     4
   2   6    A == 0 identically
   3   7    3.00  4.59  4.87  4.95  4.98  4.99  5.00  5.00               4    5     6
   3   8    2.00  5.17  5.74  5.91  5.96  5.99  5.99  6.00               4    5     6
   4   9    3.64  6.01  6.19  4.96  4.92  5.03  5.07  5.56               5    7     8
   4  10    4.00  6.67  6.16  6.08  5.22  5.34  5.37  5.14               5    7     8
   5  11    3.64  7.66  7.87  7.31  7.22  7.40   7.33                     6    9    10
   5  12    6.64  7.04  7.97  7.90  8.00  7.99   8.00                     6    9    10
   6  13    9.00  7.78  8.03  8.16  8.19                                 7   11    12
   6  14    2.00  7.91  7.05  8.27  7.48                                 7   11    12
   7  15    8.05  7.92  8.75  6.09                                       8   13    14
   7  16    9.40 10.70 10.62 10.29                                       8   13    14
```

Taking the larger of the two critical `n` at the largest available `r` and
regressing on `j = 2..7`:

```text
   delta(2j+1 or 2j+2, j)  =  (1.298 +- 0.193) j + const.
```

The `j+1` law has slope 1 (within `1.5 sigma`); the `2j-1` law has slope 2,
which is **`3.6 sigma`** away. And the fitted slope is an over-estimate, because
the available `r` falls as `j` rises and the `+2 log2(C')/r` bias with it.
None of the four `j >= 4` critical rows comes near `2j-1`: at `j = 6`,
`2j-1 = 11` against a measured `8.19`; at `j = 7`, `13` against `10.29`.

**What is not claimed.** The critical rows at `j >= 4` are **not** resolved to
an exact closed form -- the affordable `r` (8, 6, 5, 4 at `j = 4, 5, 6, 7`) is
below what the fit needs when `C >= 4`, exactly as note 12 predicted. The
evidence that they are in the `j+1` shape is (i) the exactly resolved rows of
7.1 at the same `j`, (ii) the growth estimates above, and (iii) Lemma D, which
excludes `2j` outright.

**Addendum (coordinator, after the `(5,7)` run landed; `17,401 s`, the
agent's last job, `2^35` group elements).** With `r = 7` the fitter resolves
`(12,5)` to an exact closed form `delta = 8` (six modes, ONE spare point --
the weakest "exact" in this note; `delta_7 = 8.00`), and leaves `(11,5)`
unresolved (`delta_7 = 7.33`). So the even critical cell at `j = 5` sits
at `2j-2 = j+3`, not at `j+1`: it is the first resolved `j >= 4` cell above
the `G_m`-forced optimum, and it lies in the residue class `n = 0 mod 4` that
carried the `2j` classes at `j = 2`. It does not change the regression above
(its `r = 6` estimate was already `7.99`) and Lemma D still excludes `2j`; what
it does is sharpen the honest statement: at `j = 5` the critical line is NOT
yet in the `j + O(1)` shape, and the evidence for "alive" is the slope across
`j` (1.30 +- 0.19 vs 2) plus Lemma D, not any single critical cell. The
decisive computation of sec. 10 (`j = 8..10`) is therefore not optional.

## 8. The monodromy transition at `p = 2`

Two independent diagnostics, both exact.

### 8.1 Frobenius torsion (the sharp one)

For a character `chi` the normalised inverse roots `u_i = alpha_i/sqrt q` are
all `n_0`-th roots of unity **iff** `p_{n_0}(chi) = (j-1) q^{n_0/2}` -- because
`|alpha_i^{n_0}| = q^{n_0/2}` for each `i`, so equality in the triangle
inequality forces `alpha_i^{n_0} = q^{n_0/2}` for every `i`. This is an exact
integer identity, and the engine tests it for **every** character while it
computes the power sums (flag `--orders NORD`). Write `tors(j,r,NORD)` for the
fraction of `chi in Prim_j(F_q)` passing it for some even `n_0 <= NORD`.

```text
    j   r   NORD      nprim         torsion fraction   orders n_0 observed
    2   1     12           2             1.000000   {8}
    2   2     12          12             1.000000   {2,4}
    2   4     12         240             1.000000   {2,4}
    2   8     12       65280             1.000000   {2,4}
    2   9     12      261632             1.000000   {8}
    2  10     10     1047552             1.000000   {2,4}
    3   1     24           4             1.000000   {4,8,24}
    3   2     24          48             1.000000   {2,4,6,8,12}
    3   3     24         448             1.000000   {2,4,8,24}
    3   4     24        3840             1.000000   {2,4,6,8,12}
    4   1    100           8             0.000000   {}
    4   2     52         192             0.000000   {}
    4   3     34        3584             0.000000   {}
    4   4     24       61440             0.000000   {}
    5   1     24          16             0.375000   {6,8,24}
    5   2     24         768             0.250000   {4,6,8,10,12,20,24}
    5   3     24       28672             0.099609   {2,4,6,8,12,24}
    5   5     20    32505856             0.013580   {2,4,6,8,12}
    6   1     16          32             0.000000   {}
    6   2     16        3072             0.000000   {}
    6   3     16      229376             0.000000   {}
    6   4     24    15728640             0.000000   {}
    7   1     40          64             0.000000   {}
    7   2     24       12288             0.000000   {}
    7   3     16     1835008             0.000000   {}
```

Reading:

- **`j = 2`: rank one, `u in mu_8`, always.** This is note 12's Gaussian-integer
  structure (`alpha = i^k (1+i)^r`) seen from the other side.
- **`j = 3`: every normalised eigenvalue is a 24th root of unity, at every `r`
  computed.** In particular at `r = 1` two of the four characters have exact
  order 24, which is the coordinator's hand computation
  (`chi(1+x) = i` gives `L = 1 + (1+i)u + 2iu^2` and `alpha/sqrt2 =
  e^{-5 pi i/12}`) -- confirmed here mechanically and for all four characters.
  A rank-2 lisse sheaf all of whose Frobenii have finite order of bounded
  exponent is the signature of **finite** geometric monodromy.
- **`j = 4`: no character at all, for any `r <= 4`, and none of order `<= 100`
  even at `r = 1`.** The transition happens between `j = 3` and `j = 4`:
  **`j_0 = 4`.**
- `j = 5` retains a torsion sub-population whose density falls
  (`0.375, 0.250, 0.0996` at `r = 1,2,3`, roughly `q^{-1}`), which is what one
  expects of an infinite group: torsion classes exist but are thin.
- `j = 6, 7`: none.

**Operationally, "infinite" here means:** no `F_q`-point of `Prim_j` for
`q <= 2^4` has Frobenius of order dividing `2 NORD` in the unitarised sheaf. It
is not a proof that `G_geom` is infinite: we see `Frob` only at
`F_q`-points for the `q` we can afford. But `j = 3` passes the same test with
room to spare and `j = 4` fails it completely, at every `r`, so the two are on
opposite sides of a sharp line.

### 8.2 The transition is a theorem, and the computation confirms it

**Both sides of `j_0 = 4` are in print, and I had not expected that.**

> Katz, *Witt vectors and a question of Keating and Rudnick*, IMRN 2013
> (`wittchar31.pdf` on the author's page; **it is not on arXiv**), **Thm. 5.1**,
> verbatim: "Let `p` be a prime, and `n >= 3`. Then `Ggeom` contains
> `SL(n-1)` except in the cases `(p = 5, n = 3)` and `(p = 2, n = 3)`. In the
> case `(p = 5, n = 3)`, `Ggeom` is finite." (Restated as his Thm. 7.1.) His
> `n` is our `j`. **Characteristic two is fully covered for every `j >= 4`.**

> **Remark 5.2**, verbatim: "We suspect that `Ggeom` is also finite in the
> `(p = 2, n = 3)` case, but cannot prove it at present."

> Gorodetsky, *Irreducible polynomials over `F_{2^r}` with three prescribed
> coefficients*, Finite Fields Appl. **56** (2019), arXiv:1805.07105,
> **Lemma 3.5** and sec. 1.3: the roots of `L(u,chi)` for a primitive character
> mod `R_{3,q}` are `omega sqrt q` with `omega` a root of unity **of order
> dividing 24** when `q = 2^r` (and dividing 60 when `q = 5^r`); "Lemma 3.5
> confirms this suspicion", i.e. `Theta_chi^{24} = I_2` and equidistribution
> fails at `(p,j) = (2,3)`.

So: **`j_0 = 4` is a theorem**, and section 8.1 is an independent mechanical
confirmation of both halves -- Gorodetsky's 24 at `j = 3` (for every `r <= 4`,
by an exact integer identity, not by root-finding) and the failure of any
bounded order at `j >= 4`.

**This corrects the diary.** Entry 2's addendum asks "is it then big (Katz's
`p > 2n-1` theorem does not cover `p = 2`)?". The `p > 2n-1` hypothesis is in
Katz's **Thm. 8.2**, the *Betti/Weyl-sum* bound, not in the monodromy theorem;
and Thm. 8.2 exists **only** as a substitute for a missing uniform Betti bound
(sec. 11). Katz handles `p = 2` in Thm. 5.1 without reducing Witt characters to
ordinary Artin--Schreier sheaves: at `p = 2` his moment lemma 6.4(2) is
unavailable (it needs `d < p`), so he uses `NFT_3` plus a non-self-duality
argument (Lemma 6.8) and a `p`-adic valuation bound on
`sum_t Lambda(1 - tX)` (Lemma 7.3, Cor. 7.4) to exclude the finite branch.

### 8.3 Sato-Tate moments: consistent, and characteristic-free

`Tr(Frob_chi | L_univ) = -S_1(chi) = -c_1(chi)`. The engine accumulates the
exact moments `sum_chi c_1^a conj(c_1)^b` over `Prim_j(F_q)`. Measured, for
every `(j,r)` computed:

```text
M_{1,0} = q^{-1/2},   M_{2,0} = q^{-1},   M_{1,1} = 1,
M_{2,2} = 2 - q^{-1}      (j >= 3),
M_{3,3} = 6 - O(q^{-1})   (j >= 4),   5 - O(q^{-1})  (j = 3),   1  (j = 2).
```

These are exactly the Haar moments of `U(N)`, `N = j-1`: `E[tr] = E[tr^2] = 0`,
`E|tr|^2 = 1`, `E|tr|^4 = 2`, `E|tr|^6 = 3! = 6` for `N >= 3` and `5` for
`N = 2` -- consistent with `G_geom contains SL_{j-1}` and `G_arith` unitarising into
`U(N)` rather than `SU(N)` (the determinant is arithmetically nonconstant;
Katz's Remark 8.3 says `G_geom subset G_arith subset {det(A)^{4p^{r+1}} = 1}` and that he
does not know whether they are equal, which is why his equidistribution is
stated in `PU(n-1)`).

**These moments are exact combinatorial identities, valid at every `q` and in
every characteristic.** For instance
`sum_{chi in E_j^dual} |c_1(chi)|^2 = q^j #{(b,b') : 1+bx = 1+b'x} = q^{j+1}`,
and subtracting the conductor-`< j` part gives `M_{1,1} = 1` exactly; the
fourth moment counts `{b_1,b_2} = {b_3,b_4}` in `E_j` and gives
`(2q^2-q)/q^2 = 2 - 1/q` as soon as `j - 1 >= 2`; the sixth counts triples and
gives `3!` as soon as `j - 1 >= 3`. So for the **full** `Prim_j` family the
fourth-moment input to Larsen's alternative ("`M_4 = 2` implies `G_geom` finite
or containing `SL_N`", Katz Thm. 6.5(1)) is available at `p = 2` for free, and
the entire content of Katz's Thm. 5.1 at `p = 2` is the exclusion of the finite
branch. That is consistent with his proof: what fails at `p = 2` is the moment
identity for the *smaller* `NFT_d` families (Lemma 6.4(2) needs `d < p`), not
for `Prim_j` itself.

## 9. The `F_2` data: the slope is 1, not 2

The `q`-aspect measures a *geometric* invariant, but it cannot be pushed to
`j ~ 200`. The lane's own `q = 2` layer dumps can. Summing the exact-order
layers of `data/layers-ell{20,22,23,24}-n*.txt` to the conductor sums
`A_j = sum_s T_{j,s}` and putting

```text
delta_1(n,j) := 2 log2 ( |A_j| / 2^{n/2} )
```

(the `r = 1` value of the same estimator; by Deligne it is a lower bound for
`i_max + 2 log2 C`, never an upper bound), and regressing on `j` over the
**56** points with `14 <= j <= 24` from five `(ell,n)` pairs:

```text
delta_1(j) = (1.003 +- 0.144) j + 2.30,      residual sd 2.64.
```

Forcing slope 1 gives intercept `2.35`, residual sd `2.64`; forcing slope 2
gives intercept `-16.9`, residual sd `3.62`, and slope `2` is **`6.9 sigma`**
from the fit. So at `q = 2`, in the range `(HWO)` cares about, the conductor
sums behave like `delta = j + O(1)` and not like `delta = 2j + O(1)`.

Together with `delta <= 2j - 6.15 - 2 log2 C` (Prop. 1'), `delta = j + c`
satisfies the budget as soon as `j >= c + 6.15 + 2 log2 C`, i.e. for
`j >= 9` or so with `c ~ 2.3` and `C = O(1)` -- comfortably inside
`a <= j <= ell`, `ell >= 200`.

**What this does and does not show.** Three points, in order of importance.

1. **It refutes hypothesis (H) of note 12** (sec. 7 there: the semisimplification
   is geometrically `pi^*(M^{(x)n})` for a rank-one `M` on `A^1`, giving
   `i_max = 2j-1` and `C = 2` for all `j`). (H) is an exact identity
   `|A_r(n,j)| = q^{j-2}|A_r(n,2)|`, so it can be refuted at `q = 2`, and it is:
   it over-predicts by `30..100x` at `j = 18..24` (note 12 sec. 9). With (H) go
   the only concrete mechanism note 12 could propose for a *general* obstruction.
2. **A `q = 2` measurement bounds `i_max` from BELOW, never from above.**
   `delta_1 <= i_max + 2 log2 C`, so slope 1 says `i_max >= j + O(1)` --
   consistent with `i_max = j+1`, but a large `i_max` whose class happens to
   cancel at `r = 1` would be invisible. Note 12 makes exactly this point and it
   stands.
3. **Slope 1 is also the square-root-cancellation value.** Random phases over
   `(j-1)2^{j-1}` unit vectors give `|A_1|/2^{n/2} ~ sqrt((j-1)2^{j-1})`, i.e.
   `delta_1 ~ j - 1 + log2(j-1)`: at `j = 20` that is `23.2` against a measured
   `22.7` and `26.2`. So section 9 is really the statement "**at `q = 2` the
   conductor sums are of square-root size**", which notes 05 and 07 already
   report, plus the refutation of (H). The *upper* half of the argument -- that
   no class of weight near `n + 2j` exists at all -- can only come from the
   `q`-aspect, where the uncancellable factor `q-1` from `G_m` makes `delta` a
   genuine measurement. That is section 7.

## 10. Verdict

> **ALIVE.** The top-degree classes of note 12's resolved rows are a
> finite-monodromy artefact of `j <= 3` and do not persist. Past the
> transition -- which is at `j_0 = 4`, by Katz Thm. 5.1 plus Gorodetsky
> Lemma 3.5, confirmed here mechanically -- the case `i_max = 2j` is
> **impossible** (Lemma D, unconditional at `p = 2` for all `j >= 4`), and in
> every cell we can resolve, `j = 4, 5, 6, 7`, the measured top weight above
> `n` on the critical line is `j + O(1)`, never `2j - O(1)`. The Deligne budget
> in the range `(HWO)` actually uses asks only that the top `~7` degrees vanish
> (Prop. 1'), not that the cohomology concentrate in degree `j+1`.
>
> **Confidence: moderate-to-high on "not dead" (the route is not closed by any
> evidence we have, and note 12's proposed obstruction (H) is refuted);
> low-to-moderate on "provable".** What blocks it is no longer a shape question
> but two named open statements, (T1)/(T1w) and (T2), and *both* are open in
> the literature in forms strictly weaker than what we need.

Precisely what is now settled, and what is not:

| statement | status |
| --- | --- |
| `Prim_j = G_m x A^{j-1}`, `#Prim_j(F_q) = q^{j-1}(q-1)` | proved (note 12; re-proved here, Prop. A) |
| `G_m`-action free `<=> gcd(j, q-1) = 1`; non-free locus `dim <= j/3` | proved here (Prop. B); **corrects note 12** |
| `i_max >= j+1` (`G_m` costs two degrees) | proved (note 12 Prop. 2(v); re-derived, (LERAY)) |
| `2j - i_max = k_min = min{k : H^k(B, G^v) != 0}` | proved here (Lemma C), under (D) |
| `G_geom contains SL_{j-1}` at `p = 2` for `j >= 4` | **theorem** (Katz IMRN 2013, Thm. 5.1) |
| `G_geom` finite at `(p,j) = (2,3)`, eigenvalues in `mu_24` | **theorem** (Gorodetsky FFA 2019, Lemma 3.5); confirmed here |
| `H^{2j}_c = 0`, i.e. `k_min >= 1`, for `j >= 4`, `n != j-1` | **proved here** (Lemma D) |
| `k_min >= 6.15 + 2 log2 C` -- **(T1)** | **OPEN**; the `w = j - 7` case of Sawin's Hypothesis H |
| `delta <= 2j - 6.15 - 2 log2 C` -- **(T1w)** | **OPEN**; what the data measure, and what the estimate needs |
| `C <= (j-1)2^{(j-1)/2}/(8 ell)` -- **(T2)** | **OPEN**; best known bound is `2^{O(j log j)}`, short by an exponential |
| hypothesis (H) of note 12 | **refuted** (coordinator, `q = 2` layer sums; sec. 9) |

**Single most decisive next computation.** Extend the engine from `Z[zeta_8]`
to `Z[zeta_16]` -- i.e. from `j <= 7` to `j <= 15` -- and measure
`delta(2j+1, j)` and `delta(2j+2, j)` for `j = 8, 9, 10` at the largest
affordable `r` (`(8,4)`, `(9,3)`, `(10,3)` are all `q^j <= 2^{32}`, the size of
the `(4,8)` cell already run). That doubles the `j`-range over which `delta` is
a genuine measurement and directly separates `delta = j + O(1)` from
`delta = 2j - O(1)` -- the two hypotheses that decide the route. Everything
else in this note is either settled or needs a theorem, not a number.

## 11. What is known toward (T1), (T1w), (T2), and the shortest route

Sources read from primary text (author pages, arXiv, Numdam); "NOT FOUND" means
a deliberate search did not find it.

### 11.1 (T1) is a named open hypothesis

> Sawin, *A representation theory approach to integral moments of `L`-functions
> over function fields*, Algebra & Number Theory **14** (2020) 867--906,
> arXiv:1810.01303, **Hypothesis H(n,r,r~,w)**, verbatim: "We say that
> Hypothesis `H(n, r, r~, w)` is satisfied if, for all such `F`,
> `H^j_c(Prim_{n,F_qbar}, F) = 0` for all `j > n + w`."

That is our (T1) with `w = 2j - i_max` reversed: `dim Prim_n = n` (his `n` =
our `j`), so `i_max <= n + w` is `k >= n - w`, and **the budget of
Proposition 1' is exactly Hypothesis H with `w = j - 6.15 - 2 log2 C`** -- the
*weakest* nontrivial case, `w` just below the trivial `w = j`. Full middle
concentration (`i_max = j+1`) is `w = 1`. Sawin's own remark, verbatim: "the
larger `w` is, the weaker an assumption Hypothesis 1.3 is."

His main moment theorems are **conditional** on it; he writes, verbatim: "There
is also some hope for a geometric proof of this cohomological hypothesis."

The unconditional partial result is **Lemma 5.3**: `H(n, r, 1, w = n + 1 -
((p-2r)/p^r) n)` for any `n, r`. Its proof opens, verbatim: "We may assume
`p > 2r` as if `p <= 2r` then the claim follows immediately from the fact that
`H^j(Prim_{n,F_q}, F) = 0` for `j > 2n` because `dim Prim_n = n`." At `p = 2`,
`p <= 2r` for every `r >= 1`, so **Lemma 5.3 is vacuous at `p = 2`** -- while
at `p >= 3`, `r = 1`, it gives `w ~ n(1 - (p-2)/p) + 1 = 2n/p + 1`, which is
`<= n - 7` already for `p >= 3` and `n >= 24`. In other words:

> **The lane's obstruction is exactly the characteristic-two case of Sawin's
> Lemma 5.3.** For every odd `p`, the horizontal route's degree requirement is
> already a theorem in the relevant range. Kaser--Lemire is a `p = 2` question
> and this is where the two facts meet.

(Caveat: Sawin's `F` are summands of `det^{-1}(L_univ) (x) (x) Lambda^{d_i}(L_univ)`
with `0 <= d_i <= n-1`. Our `Xi_n(L_univ)` is the alternating sum of hooks
`S^{(n-k,1^k)}(L_univ)`, `n ~ 2j`, which are summands of `(x)_{i=1}^{n-k}
Lambda^{d_i}(L_univ)`, so they lie in his class only with `r ~ n ~ 2j` -- and then
`p > 2r` is out of reach anyway. The *shape* of the hypothesis, on the same
space, is identical.)

### 11.2 Big monodromy gives the top group and nothing else

Confirmed verbatim from Sawin, arXiv:1805.04330, proof of Thm. 1.3: `H^i_c` for
`i <= 2d-1` is handled by "mixed of weight `<= i + ...`", i.e. by Deligne's
bound with the Betti numbers in the implied constant, and only
`H^{2d}_c` is made to vanish, "because ... `V` has no geometric monodromy
invariants, and its top cohomology vanishes." Gorodetsky--Sawin (Math. Ann.
**376** (2019), arXiv:1811.04834, proof of Thm. 9) use the same and only the
same. **NOT FOUND:** any theorem controlling `H^{2d-1}_c(X,F)` -- equivalently
`H^1(X, F^v)` -- for a lisse sheaf with Zariski-dense monodromy on a smooth
affine `X` of dimension `>= 2` in characteristic `p`. That is precisely the
first group beyond Lemma D.

### 11.3 The middle-concentration mechanisms, and why each misses

- **Total wildness `=>` forget-supports is an isomorphism `=>` concentration.**
  Katz, *Gauss Sums, Kloosterman Sums and Monodromy Groups*, Ann. Math. Studies
  116, **2.1.1/2.2.1 and Remark 2.2.2** (also *Sommes exponentielles*,
  Asterisque 79, "Lemme Clef" (1), p. 131): exactly this mechanism, no
  restriction on `p` -- **but stated for curves.** In dimension `>= 2` the only
  verified version is Katz, *Sommes exponentielles* **5.4.1** (= Katz, *Moments,
  Monodromy, and Perversity*, Thm. 4.1.12), whose "Deligne type" hypothesis D2
  requires every pole order `e_i` to be **prime to `p`**. An
  Artin--Schreier--Witt sheaf of level `>= 2` has `Swan = m p^{r-1-d}`
  (Katz IMRN 2013, Lemma 3.1, after Brylinski), divisible by `p` exactly when
  the level exceeds one. **D2 excludes precisely our sheaves.**
- **Genericity in a twist.** Katz--Laumon, Publ. IHES **62** (1985),
  Thm. 5.4/5.5.1 and Scholie 2.3.1; Forey--Fresan--Kowalski arXiv:2109.11961
  Thm. 2.1. These give concentration for `a` outside the zero locus of a
  nonzero homogeneous `F`, and Katz--Laumon's own Remarque 5.5.2 says they do
  not know whether that `F` can be chosen uniformly. Useless for a *specified*
  sheaf.
- **Perversity of an explicit tensor construction.** Sawin--Shusterman
  arXiv:2008.09905, Lemma 3.6 + **Cor. 3.7**: `H^j_c(A^n, (x) e_i^* F_i) = 0`
  for `j not in {n, n+1}` -- i.e. `w = 1`, which would be (T1) in full -- but
  the `F_i` are required **tamely ramified at infinity**. Again the opposite of
  our situation.
- **Singular-locus dimension.** Sawin arXiv:1809.05137 Prop. 2.5 (the input to
  Sawin's Lemma 5.1/5.3 above) degrades by `floor(n/p)` and is weakest at
  `p = 2`, which is the mechanism behind the vacuity noted in 11.1.

**Shortest plausible route to (T1w)/(T1).** In order of promise:

1. **Push Sawin's Lemma 5.3 to `p = 2`.** The requirement is only
   `w <= j - 7`, and at `p >= 3` the existing lemma clears it by a wide margin.
   The loss at `p = 2` is a `floor(n/p)` in the underlying singular-locus
   estimate (Sawin 1809.05137 Prop. 2.5). This is a bounded, identified
   technical gap in one lemma, not a missing theory.
2. **A weight statement instead of a degree statement.** (T1w) is what the
   estimate needs and what the experiment measures; a purity/perversity
   argument bounding the top *weight* by `n + 2j - 7` would do, without any
   degree vanishing.
3. **Total wildness in dimension `>= 2` for ASW sheaves of level `>= 2`.** This
   would be a new theorem: the existing higher-dimensional criterion (Katz-SE
   5.4.1) is exactly blocked by `p | Swan`. Abbes--Saito / T. Saito
   characteristic-cycle technology is the natural setting.

### 11.4 (T2): the Betti sum is short by an exponential

Katz, IMRN 2013, proof of Thm. 8.1, **verbatim**: "At present, we do not know
uniform bounds for these sums of Betti numbers `C(p, n, Xi)` as `p` varies
(`n` and `Xi` fixed)." His Thm. 8.2 (`n >= 3` and `p > 2n-1`) exists **only** to
bypass that gap; its hypothesis does two jobs -- `p > n` so that the Witt
characters degenerate to ordinary Artin--Schreier sheaves `L_psi(f)`, and
`p > 2(n-1)+1` for the Lie-irreducibility input of Katz, Duke **54** (1987),
Thm. 17.

The gap has since been partly closed, **uniformly in `p`**:

> Sawin, arXiv:1810.01303, **Lemma 2.11**, verbatim: for
> `0 <= d_1, ..., d_{r+r~} <= n-1`,
> `sum_j dim H^j_c(Prim_{n,F_q}, (x)_{i<=r} Lambda^{d_i}(L) (x) (x)_{i>r}
> Lambda^{d_i}(L^v)) <= 4(2 + max(r,r~))^{n + sum d_i}`.

Nothing in it depends on `p`. **But it is not enough.** Writing a hook
`S^{(n-k,1^k)}(L_univ)` as a summand of `(x)_{i=1}^{n-k} Lambda^{d_i}(L_univ)` gives
`r = n-k`, `sum d_i = n`, hence `C = 2^{O(j log j)}` on the critical line
`n ~ 2j`. The budget allows `C <= (j-1)2^{(j-1)/2}/(8 ell) ~ 2^{j/2}` **even
under full middle concentration**. So (T2) is a genuinely separate requirement
and the best bound in print misses it by an exponential factor. Note 12's
"(Q1'-b) follows from any polynomial-in-`j` bound" is correct, and no
polynomial bound exists.

The other live route for (T2) is Hu--Teyssier, arXiv:2502.11060, which bounds
Betti numbers of **wildly ramified** local systems on a smooth proper `X` minus
a divisor `D` by a polynomial in the highest logarithmic conductor at the
generic points of `D`, times the rank, in any dimension and any characteristic.
The logarithmic conductor of an ASW character is computable from Katz's
Lemma 3.1. **This is the most promising unexplored input for (T2)** and, unlike
Katz FFA 7 (2001) Thm. 12, it is not restricted to level-one sheaves.

Under (T1), `C' = |chi_c(B,G)|` is an Euler characteristic, and the
higher-dimensional Grothendieck--Ogg--Shafarevich analogue is T. Saito's index
formula (*The characteristic cycle and the singular support of a constructible
sheaf*, Invent. Math. **207** (2017) 597--695). It computes an alternating sum,
so it becomes a Betti bound **only after** concentration is known -- i.e. it is
downstream of (T1), not an alternative to it.

## 12. Reproducibility

```sh
cd scripts/lemire-signed-trace
# all nine controls (~25 s), pure Python, independent of the Rust engine
python lemire_horizontal_quotient.py
# six mutation controls; each MUST exit nonzero, through a different named check
for k in 1 2 3 4 5 6; do python lemire_horizontal_quotient.py --mutate $k; done
# cross-check the Rust dumps and regenerate the tables
python lemire_horizontal_quotient.py --dumps data/lfunc-dumps \
    --report data/horizontal-lfunc-weights.txt
```

The Rust engine is `axeyum-lemire-lfunc` (source mirrored as
`scripts/lemire-signed-trace/axeyum-lemire-lfunc.rs.txt`; drop it into
`crates/axeyum-cas/src/bin/` of a snapshot of branch `agent/gf2/lemire-proof`
and build with
`AXEYUM_CARGO_LOCK=... scripts/cargo-serialized.sh build --release -p
axeyum-cas --bin axeyum-lemire-lfunc`). Usage
`axeyum-lemire-lfunc <j> <r> <nmax> [threads] [--orders NORD] [--g2bits B]`.
Raw dumps: `scripts/lemire-signed-trace/data/lfunc-dumps/`; generated table
`data/horizontal-lfunc-weights.txt`.

Cross-validation performed: the Python and Rust engines agree on every
overlapping cell; both agree with the note-12 **window-scan** engine
`axeyum-lemire-horizontal` (a different algorithm, `data/horizontal-grid.txt`)
on 136 `(n,j,r)` cells; the `--g2bits` blocking invariance holds byte for byte;
and every note-12 closed form is reproduced.
