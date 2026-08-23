# The horizontal Deligne budget: what a Betti bound can and cannot buy

Status: research note, 2026-08-22. Angle 4 of the backward-chains diary
([11-backward-chains-diary.md](11-backward-chains-diary.md)). It settles, as a
proposition with proof, what a cohomological bound on Katz's parameter space
`Prim_j` would have to look like in order to give `(HWO)`, corrects question
Q1 of [10-open-problem-statement.md](10-open-problem-statement.md), and
reports an exact experiment that measures the quantity the corrected question
turns on.

Companions: [01-target-and-toolkit.md](01-target-and-toolkit.md) (`E_j`,
`S_n(chi)`, `T_{j,s}`, `(HWO)`), [04-shape-verdicts.md](04-shape-verdicts.md)
shape 1 (the *curve-side* virtual motive `M_{j,s}`, whose rank is exponential
in `j` -- that is a different object from the *parameter-space* Betti numbers
here, and the two must not be confused),
[05-almost-all-theorem.md](05-almost-all-theorem.md) sections 2 and 4.
Script: `scripts/lemire-signed-trace/lemire_horizontal_weights.py`.

## 0. Summary

- The coordinator's Deligne-budget computation is **verified**, with one
  numerical correction: the trivial bound at `q = 2` is `2^{j-1}(j-1)2^{n/2}`,
  not `2^j (j-1) 2^{n/2}`, because `#Prim_j(F_q) = q^{j-1}(q-1)`, which is
  `2^{j-1}` at `q = 2`. The number of top degrees that must vanish is
  `k >= 2 log2(8 ell C/(j-1))`, not `2 log2(4 sqrt2 ell C/(j-1))`.
- **A Betti bound alone cannot give `(HWO)`.** If the cohomology reaches degree
  `2j`, `2j-1` or `2j-2`, then even `C = 1` is `8x`, `5.7x` and `4x` short.
  Note 10's Q1 ("a polynomial-in-`j` bound would give `(HWO)`") is therefore
  false as stated; Q1 is rewritten below as a question about the **pair**
  (top degree, Betti sum).
- **Middle concentration is impossible for this family** (Prop. 2). `Prim_j` is
  `G_m x A^{j-1}` over `F_2`, the trace function of `Xi_n(L_univ)` is invariant
  under the `G_m`-action `x -> tx` on `E_j` for every `n` (proved), and Kuenneth
  plus Artin vanishing then force `i_max >= j+1`. So the sharp target is
  concentration in degree `j+1`, one above the middle, with
  `C <= (j-1)2^{(j-1)/2}/(8 ell)` -- an exponential allowance that any
  polynomial Betti bound would meet.
- **The experiment says the truth is at the other end.** Measuring the growth
  of `|A_r(n,j)|` in `r` at fixed `(n,j)` reads off the largest Frobenius
  weight actually present, hence a lower bound on `i_max` -- and `i_max` and
  `C` are geometric, so this is a legitimate way to learn about the same groups
  that govern `q = 2`. Three in-range rows both resolve and separate the two
  shapes, and all three are bad: `(8,2)` and `(12,2)` have `i_max = 2j` (the
  sheaf acquires geometric coinvariants) and `(7,3)`, the one such row on the
  critical line `n = 2j+1`, has `i_max >= 2j-1` with `C = 2`. The odd-`n`,
  `j = 2` rows are exact but uninformative (`2j-1 = j+1` there), `(9,3)` points
  the other way, and `j >= 4` does not resolve within the affordable `r`. See
  sections 6 and 7.
- Verdict: **(iii) mixed, leaning dead** -- see section 7.

## 1. Setting and conventions

`q = 2^r`. `E_j = (1 + x F_q[x])/x^{j+1}`, of order `q^j`;
`<F>_j = x^{deg F} F(1/x) mod x^{j+1}` for monic `F`;

```text
N_j^{(q)}(1) = sum_{F monic, deg F = n, <F>_j = 1} Lambda(F)
```

is the Mangoldt mass of the monic degree-`n` polynomials whose top `j`
non-leading coefficients vanish (the "identity class", the short interval
`x^n + O(x^{n-j-1})`). For a character `chi` of `E_j` of exact conductor `j`,
`L(chi,T) = prod_{i<=j-1}(1 - alpha_i(chi)T)` with `|alpha_i| = sqrt q` (Weil),
and `S_n(chi) = sum_{deg F = n} Lambda(F) chi(<F>_j) = -sum_i alpha_i(chi)^n`.
Conductor `1` gives `L = 1` and `S_n = 0`.

Katz (*Witt vectors and a question of Keating and Rudnick*, IMRN 2013,
sections 3--4) parametrizes the exact-conductor-`j` characters by the
`F_q`-points of an `F_2`-scheme `Prim_j`, inside
`prod_{m odd, m <= j} W_{e(m,j)}` with `sum_m e(m,j) = j`, defined by the
condition that the initial Witt component of the distinguished factor be
invertible; and carries (his Lemma 4.1)
`L_univ := R^1(pr_2)_!(Lcal_univ)`, where `Lcal_univ` is the rank-one
Artin--Schreier--Witt sheaf on `A^1 x Prim_j` and `pr_2` the projection.
`L_univ` is lisse of rank `j-1`, pure of weight one, `R^i(pr_2)_!` vanishes for
`i != 1`, and `det(1 - T Frob_chi | L_univ) = L(chi,T)`, hence
`Tr(Frob_chi | L_univ) = -S_1(chi)`.

`Xi_n` denotes the virtual representation of `GL_{j-1}` whose character is the
`n`-th power sum (the `n`-th Adams operation `psi^n`), so `Xi_n(L_univ)` is a
virtual lisse sheaf, pure of weight `n`, of virtual rank `j-1`, with

```text
Tr(Frob_chi | Xi_n(L_univ)) = sum_i alpha_i(chi)^n = -S_n(chi).
```

The object of study is the *signed* sum over the whole conductor-`j` family,

```text
A_r(n,j) := sum_{chi in Prim_j(F_q)} S_n(chi).
```

**Fact 1 (orthogonality).** `A_r(n,j) = q^j N_j^{(q)}(1) - q^{j-1} N_{j-1}^{(q)}(1)`.

*Proof.* `sum_{chi in E_j^dual} S_n(chi) = sum_F Lambda(F) sum_chi chi(<F>_j)
= q^j N_j(1)`; subtracting the same for `E_{j-1}` (through which the
conductor-`<j` characters factor) leaves the exact-conductor-`j` ones. QED

The two means cancel (`q^j q^{n-j} = q^{j-1} q^{n-j+1} = q^n`), so `A_r` is
pure fluctuation. Its exact-order-`2^s` pieces are the `T_{j,s}` of `(HWO)`;
`A_r(n,j) = sum_s T_{j,s}(n)` at `q = 2`.

**Fact 2 (Lefschetz).**
`A_r(n,j) = -sum_i (-1)^i Tr(Frob_2^r | H^i_c(Prim_j (x) F_2bar, Xi_n L_univ))`.

**Fact 3 (trivial bound).** `|S_n(chi)| <= (j-1) q^{n/2}` and
`#Prim_j(F_q) = q^{j-1}(q-1)`, so

```text
|A_r(n,j)| <= q^{j-1}(q-1)(j-1) q^{n/2};   at q = 2:  |A_1| <= 2^{j-1}(j-1)2^{n/2}.
```

`(HWO)` asks for a factor `4 ell` saving over exactly this bound, per
exact-order layer. Its conductor-aggregate shadow -- the statement a
cohomological bound on `Prim_j` produces directly -- is

```text
(HWO-agg)   4 ell |A_1(n,j)| <= 2^{j-1} (j-1) 2^{ceil(n/2)},
            a <= j <= ell,  n in {2 ell + 1, 2 ell + 2}.
```

Everything below is stated for `(HWO-agg)`; the layer refinement replaces
`Prim_j` by the locally closed `Prim_{j,s} subset Prim_j` cut out by the
exact-order condition and `#Prim_j` by `#X_{j,s}`, and every inequality goes
through with `j` replaced by `dim Prim_{j,s} <= j`. Nothing in the argument
gets easier under that replacement.

## 2. Proposition 1: the budget

> **Proposition 1.** Let `X/F_2` be separated of finite type, `F` a virtual
> lisse `Q_l`-sheaf on `X`, pure of weight `n`, with
> `|Tr(Frob_x | F)| <= R (#k(x))^{n/2}` at every closed point. Put
> `A_r = sum_{x in X(F_{2^r})} Tr(Frob_x | F)`,
> `C = sum_i h^i_c(X (x) F_2bar, F)` and `i_max = max{i : H^i_c != 0}`
> (with `C = 0`, `A_r = 0` if the cohomology vanishes). Then
> `|A_r| <= C 2^{r(n + i_max)/2}` (Deligne), while trivially
> `|A_r| <= R #X(F_{2^r}) 2^{rn/2}`. At `r = 1`, writing `M = #X(F_2)`, the
> Deligne bound improves on the trivial one by the factor
> `Sav = R M / (C 2^{i_max/2})`. Consequently a saving of at least `G` holds
> **only if**
>
> ```text
> C <= R M / (G 2^{i_max / 2}).                                      (BUDGET)
> ```
>
> For `X = Prim_j`, `R = j-1`, `M = 2^{j-1}`, `G = 4 ell` this reads
>
> ```text
> C <= (j-1) 2^{j - 1 - i_max/2} / (4 ell),
> equivalently   i_max <= 2j - 2 - 2 log2(4 ell C / (j-1)),
> equivalently   k := 2j - i_max >= 2 log2(8 ell C / (j-1)).
> ```

*Proof.* Deligne, Weil II (Publ. IHES 52, 1980), Cor. 3.3.4: a sheaf mixed of
weight `<= n` has `H^i_c` mixed of weight `<= n + i`. So every Frobenius
eigenvalue on `H^i_c` has complex absolute value at most `2^{r(n+i)/2}`, and
summing over `i <= i_max` with multiplicity gives
`|A_r| <= (sum_i h^i_c) 2^{r(n+i_max)/2} = C 2^{r(n+i_max)/2}`. The trivial
bound is the triangle inequality on the point sum. The rest is arithmetic. QED

**Corollaries** (using `1 <= j <= ell`, so `(j-1)/ell < 1`, and `C >= 1`
whenever `H^*_c != 0`):

| `i_max` | `(BUDGET)` requires | verdict |
| --- | --- | --- |
| `2j` (top) | `C <= (j-1)/(8 ell) < 1/8` | **impossible** |
| `2j-1` | `C <= (j-1)/(4 sqrt2 ell) < 0.177` | **impossible** |
| `2j-2` | `C <= (j-1)/(4 ell) < 1/4` | **impossible** |
| `2j-k` | `2^{k/2} >= 8 ell C/(j-1)`; with `C = 1`, `j = ell`: `k >= 6` | needs `k = Theta(log(ell C))` |
| `j+1` | `C <= (j-1) 2^{(j-1)/2}/(8 ell)` | exponential room |
| `j` (middle) | `C <= (j-1) 2^{j/2}/(8 ell)` | exponential room |

So: **the Betti sum is not the binding constraint; the cohomological degree
is.** If `H^{2j}_c` or `H^{2j-1}_c` or `H^{2j-2}_c` is nonzero, no bound on
`C` -- not even `C = 1` -- gives `(HWO-agg)` through Deligne. Conversely, once
the cohomology is concentrated near the middle, *any* polynomial-in-`j` bound
on `C` suffices, with exponential margin. The dividing line sits at
`k ~ 2 log2 ell`, i.e. `i_max ~ 2j - 2 log2 ell`: a *logarithmic* number of
vanishing top degrees, which matches the logarithmic nature of the whole
Kaser--Lemire gap (note 11's literature section: the conjecture is `~log_2 n`
past Weil).

This is the correction to the coordinator's arithmetic: using
`#Prim_j(F_2) = 2^{j-1}` rather than `2^j` turns `4 sqrt2` into `8` inside the
logarithm. The qualitative conclusions are unchanged.

## 3. Proposition 2: Prim_j is `G_m x A^{j-1}`, and the middle is unreachable

> **Proposition 2.**
> (i) `Prim_j` is isomorphic, as an `F_2`-scheme, to `G_m x A^{j-1}`. In
> particular it is smooth, affine, geometrically connected, of dimension `j`,
> and `#Prim_j(F_q) = q^{j-1}(q-1)` for every `q`.
> (ii) Hence `H^i_c(Prim_j (x) F_2bar, F) = 0` for `i < j` for every lisse `F`,
> so `j <= i_max <= 2j`.
> (iii) `G_m` acts on `E_j` over `F_2` by `sigma_t : x -> t x`, and the trace
> function of `Xi_n(L_univ)` is `sigma`-invariant for every `n`. Concretely,
> `S_n(chi o sigma_t) = S_n(chi)` and `N_j(sigma_t g) = N_j(g)`.
> (iv) If the induced action of `F_q^*` on `Prim_j(F_q)` is free, then
> `(2^r - 1) | A_r(n,j)` for every `n, j, r`, and
> `A_r(n,j) = (2^r-1) B_r(n,j)` with `B_r` the sum over `Y(F_q)`,
> `Y := Prim_j/G_m = A^{j-1}`.
> (v) If moreover the semisimplified sheaf descends to `Y`, then
> `i_max = 2 + i_max(Y) >= j + 1` whenever `H^*_c != 0` -- **the cohomology is
> not concentrated in the middle degree `j`.** (Parts (i)--(iii) are
> unconditional; (iv) and (v) carry the stated hypotheses, both of which are
> proved at `j = 2` and measured for `j >= 3`.)

*Proof.* (i) Katz's definition: inside `prod_{m odd, m <= j} W_{e(m,j)}`,
`Prim_j` is the open set where the distinguished component lies in
`W_e^x subset W_e`, the locus where the initial Witt coordinate `a_0` is
invertible. As schemes `W_e = A^e` and `W_e^x = G_m x A^{e-1}`, and
`sum_m e(m,j) = j`, whence `Prim_j = G_m x A^{j-1}`. The point count follows.

(ii) `Prim_j` is smooth affine of dimension `j`; Poincare duality
(SGA 4 XVIII 3.2.5) turns `H^i_c(X,F)` into `H^{2j-i}(X, F^v)^v(-j)`, and
Artin's affine vanishing theorem (SGA 4 XIV, Cor. 3.2) kills
`H^m(X, F^v)` for `m > j`, i.e. `H^i_c(X,F) = 0` for `i < j`.

(iii) `sigma_t` is a ring automorphism of `F_q[x]/x^{j+1}` fixing the
augmentation, hence a group automorphism of `E_j = (1 + xF_q[x])/x^{j+1}`, and
it is defined over `F_2` (it is the standard `G_m`-action on the truncated
Witt/polynomial ring). For monic `F` of degree `n` put
`F_t(T) := t^n F(T/t)`, again monic of degree `n`. Then

```text
sigma_t(<F>_j)(x) = <F>_j(t x) = (tx)^n F(1/(tx)) = x^n F_t(1/x) = <F_t>_j,
```

`F -> F_t` is a bijection of the monic degree-`n` polynomials with
`Lambda(F_t) = Lambda(F)` (irreducibility is invariant under a scaling of the
variable). Hence `N_j(sigma_t g) = N_j(g)` for all `g`, and dualizing,
`S_n(chi o sigma_t) = S_n(chi)`.

(iv) If the action on `Prim_j(F_q)` is free its orbits all have `q-1`
elements, and `S_n` is constant on them by (iii). `Y(F_q) = Prim_j(F_q)/F_q^*`
because `H^1(F_q, G_m) = 0`.

(v) Kuenneth for `Prim_j = G_m x Y` with a sheaf pulled back from `Y`:
`H^i_c(G_m x Y, pr^*G) = H^1_c(G_m) (x) H^{i-1}_c(Y,G) + H^2_c(G_m) (x) H^{i-2}_c(Y,G)`
(`h^1_c(G_m) = h^2_c(G_m) = 1`, weights `0` and `2`). `Y = A^{j-1}` is affine
of dimension `j-1`, so `H^m_c(Y,G) = 0` for `m < j-1` by (ii); the top
nonvanishing degree upstairs is therefore `2` more than the top nonvanishing
degree on `Y`, which is `>= j-1`. QED

Freeness in (iv) is not automatic: in the natural coordinates `sigma_t` scales
the `m`-th Witt block by `t^m`, and a character of exact conductor `j` is only
forced to have `t^{j} = 1`, so a stabilizer could survive when `j | q-1`.
It is **proved for `j = 2`** (there `E_2 = W_2(F_q)`, characters
are `chi_c(w) = i^{tr_W(c.w)}`, `c_0 != 0`, and `sigma_t` acts by
`c -> (t c_0, t^2 c_1)`, which has trivial stabilizer). For `j >= 3` it is
**measured, not proved**: the exact divisibility `(2^r - 1) | A_r(n,j)` holds
on every one of the rows computed in section 6 (`2 <= j <= 13`,
`5 <= n <= 13`, `1 <= r <= 8`). It is also the check that caught a real bug in
the engine (a non-primitive field modulus at `r = 8`), which is the best kind
of evidence that it is not vacuous.

The pullback hypothesis in (v) is likewise **proved for `j = 2`** -- the
inverse root `alpha(chi_c)` depends on `c = (c_0,c_1)` only through the
`G_m`-invariant `d = c_1/c_0^2` (see the script's `witt_alphas`) -- and
consistent with the measured divisibility for `j >= 3`.

**Consequence for Q1.** Under (iv)--(v), line `i_max = j` of the
Proposition-1 table is empty: the family cannot have middle concentration,
because it has a `G_m` factor on which nothing cancels. The best case available
is `i_max = j+1`, and that case still has exponential room for `C`. Even if
(iv)--(v) failed for some `j`, nothing in the argument below depends on it: the
measured rows put `i_max` far *above* `j+1`, and Proposition 1 is what closes
them.

## 4. The corrected question

Note 10's Q1 asked for a uniform bound on `C(2,j,Xi) = sum_i h^i_c` and
asserted "a polynomial-in-`j` bound would give `(HWO)`". By Proposition 1 that
implication is **false** unless the cohomological degree is also controlled.
The corrected question:

> **(Q1')** Fix `p = 2`. For the layer representation `Xi` (equivalently for
> `Xi_n`, the `n`-th Adams operation, and its exact-order-`2^s` refinement),
> put
>
> ```text
> C(2,j,Xi)     = sum_i h^i_c(Prim_j (x) F_2bar, Xi(L_univ)),
> i_max(2,j,Xi) = max { i : h^i_c(Prim_j (x) F_2bar, Xi(L_univ)) != 0 }.
> ```
>
> Is the **pair** admissible, i.e. is
> `C(2,j,Xi) <= (j-1) 2^{j-1-i_max/2} / (4 ell)`? Equivalently, writing
> `k = 2j - i_max`, do the top `k` degrees vanish with
> `k >= 2 log2(8 ell C(2,j,Xi)/(j-1))` -- a *logarithmic* number of vanishing
> top degrees when `C` is polynomial?
>
> By Proposition 2(v) the extreme case `i_max = j` is unavailable. The sharp
> target is therefore
>
> * **(Q1'-a)** `H^i_c(Prim_j (x) F_2bar, Xi(L_univ)) = 0` for `i > j+1`
>   (concentration one degree above the middle, the `G_m`-forced optimum),
>   together with
> * **(Q1'-b)** `C(2,j,Xi) <= (j-1) 2^{(j-1)/2} / (8 ell)`,
>
> and (Q1'-b) follows from *any* polynomial-in-`j` bound on the Betti sum.
> Note 10's Q1 is exactly (Q1'-b); what is missing from it, and what the whole
> estimate turns on, is (Q1'-a).

## 5. What is known toward each half

Sources read from the primary text (arXiv/Numdam/author pages); "unknown" below
means a deliberate search did not find it, not that it does not exist.

**Toward (Q1'-b), the Betti sum.**

- Katz, IMRN 2013, proof of Thm. 8.1, defines exactly this `C(p,n,Xi)` and says
  verbatim: "At present, we do not know uniform bounds for these sums of Betti
  numbers `C(p, n, Xi)` as `p` varies (`n` and `Xi` fixed)." His Thm. 8.2 gives
  the only polynomial bound, `3 dim(Xi) #Prim_n(k)/((n-1) sqrt(#k))`, and only
  for `p > 2n-1`, where the Witt characters degenerate to ordinary
  Artin--Schreier sheaves `L_{psi(f)}`; `p = 2` is precisely excluded.
- Every general Betti-sum bound is exponential (or worse) in the *ambient
  dimension*, which here is `j`: Bombieri `(4d+5)^{n+r}`; Adolphson--Sperber;
  Katz, FFA 7 (2001), `3(d+2)^{n+r}`; Wan--Zhang arXiv:2501.12623 Thm. 1.3.10,
  `3^r binom(n+r,r)(2d+1)^n`. Forey--Fresan--Kowalski--Sawin, *Quantitative
  sheaf theory* (arXiv:2101.00635, JAMS 2023) is uniform in `p`, `q` and `l`,
  but its Thm. 8.1 constant is `13^n (n+2)!` in the ambient dimension, and
  Remark 8.2 says verbatim that they do not know how to improve the factorial
  growth in positive characteristic. **"Witt" does not occur in that paper**;
  its section 7.3 covers level-1 Artin--Schreier and Kummer sheaves only.
- No Betti-number bound for Artin--Schreier--**Witt** sheaves of level `>= 2`
  was found in any source. Hu--Teyssier arXiv:2502.11060 is the only framework
  covering arbitrary wild ramification; its Lemma 10.1 is again roughly
  `3^n (n-1)!` in the dimension.

**Toward (Q1'-a), the degree.**

- Artin vanishing (SGA 4 XIV Cor. 3.2, via Poincare duality) gives the lower
  half, `H^i_c = 0` for `i < j`. This is Proposition 2(ii) and is all that is
  unconditional.
- **Big monodromy never gives middle concentration.** It gives exactly one
  degree: `H^{2d}_c(X,F) = F_{pi_1^geom}(-d)`, the geometric coinvariants, so
  large `G_geom` kills the top group and nothing else. Katz's own SL(n-1)
  theorem (IMRN 2013 Thm. 5.1) is used for exactly that. Sawin,
  arXiv:1805.04330 section 6, proves `H^{2d}_c = 0` on the moduli of Witt
  Dirichlet characters for an irreducible `V` not factoring through the
  determinant -- the only moduli-space-level vanishing statement in the
  literature -- and then handles `i <= 2d-1` by Deligne weights, not vanishing.
  For `H^{2d-1}_c` **nothing** was found: Poincare duality turns it into
  `H^1(X, F^v)`, and group cohomology in degree 1 with nontrivial irreducible
  coefficients has no reason to vanish for a large monodromy group.
- The mechanisms that *do* give middle concentration in print are three, and
  none is monodromy: (a) forget-supports being an isomorphism, so Artin
  vanishing bites from both sides -- Katz--Laumon, Publ. IHES 62 (1985),
  Thm. 5.4(i)/(iii) and Thm. 5.5.1(ii) (the equicharacteristic-`p` version),
  for `L_psi(sum a_i f_i) (x) L_chi(g)` with `f` finite, and only for `a`
  **generic** (outside the zero locus of a nonzero homogeneous `F`); the
  sufficient condition for (a) is total wildness at the boundary (Katz, GKM,
  Remark 2.2.2); (b) genericity in a twisting character -- Katz--Laumon,
  Gabber--Loeser, Kraemer--Weissauer, and Forey--Fresan--Kowalski
  arXiv:2109.11961 Thm. 1, whose exceptional set has size `<< |k_n|^{d-i}`;
  (c) a bound on the dimension of a singular locus (Sawin arXiv:1809.05137
  Prop. 2.5) or perversity of an explicit tensor construction
  (Sawin--Shusterman arXiv:2008.09905 Cor. 3.7, which gives concentration in
  `{n, n+1}` -- note that this is exactly the `i_max = d+1` shape of
  Proposition 2(v)). Sawin's Prop. 2.5 vanishing range degrades by
  `floor(n/p)`, i.e. it is **weakest at `p = 2`**.
- Katz's own Thm. 8.2 method is worth reading as a cohomological statement: he
  slices `Prim_n` into `A^1`-lines, uses `h^1_c` on each line (where the other
  `h^i_c` vanish), and sums **trivially** over the remaining `n-1` dimensions.
  That is precisely the `i_max = 2 dim - 1` shape, and Proposition 1 says it
  can never reach `(HWO)`: in the notation above it delivers
  `Sav = (j-1) sqrt(q)/3`, which at `q = 2` is `0.47(j-1)` against a required
  `4 ell >= 4j` -- short by a factor `~8.5`, and unavailable at `p = 2` anyway.
- Char 2 is exceptional throughout: Katz's SL(n-1) excludes `(p,n) = (2,3)`;
  his Rudnick--Waxman paper needs a separate theorem for `p = 2`; his ASW Betti
  bound (Rudnick--Waxman paper, Lemma 5.2) assumes `p > n`; Sawin--Shusterman
  arXiv:1808.04001 assumes `p` odd.

## 6. The experiment

**Idea.** Fix `(n,j)` and vary `r`. By Fact 2, `A_r(n,j) = -sum_i (-1)^i
Tr(Frob_2^r | H^i_c)`, so the sequence `(A_r)_{r>=1}` is a Frobenius trace
sequence: it satisfies a linear recurrence whose characteristic roots are the
eigenvalues `beta`, and `|A_r| ~ C' 2^{r w/2}` with `w` the largest weight
actually present. Since `w <= n + i_max`, measuring

```text
gamma_r := log_q |A_r(n,j)| - n/2   ->   w/2,     w = 2 gamma_infinity,
```

gives `i_max >= 2 gamma_infinity` -- and, more directly, gives the true size of
`A_r`, which is what `(HWO)` is about. Middle concentration predicts
`2 gamma = j`; the `G_m`-forced optimum `j+1`; "top minus one" `2j-1`; no
cancellation `2j`. These differ by factors `q^{1/2}` each, so the `q`-aspect
resolves them while `q = 2` data cannot (note 10: at `q = 2` square-root
cancellation and random phases give the same answer).

**Engines.** All exact integer arithmetic; three implementations, never
sharing code.

1. `witt` (python, exact, `j = 2`, all `n`, `r <= 16`). Uses the Artin--Hasse
   identification `E_2 = W_2(F_q)` by `1 + u_1x + u_2x^2 <-> (u_1,u_2)` (the
   truncated product and the length-2 Witt sum agree identically), the explicit
   order-4 character `chi_c(w) = i^{tr_W(c . w)}` with `tr_W` the Witt trace to
   `W_2(F_2) = Z/4`, exact conductor 2 iff `c_0 != 0`, and
   `alpha(chi_c) = -sum_b chi_c(1 + bx)`. Substituting `u = c_0 b` gives

   ```text
   alpha_d = - sum_{u in F_q} i^{Tr(u)} (-1)^{Tr(d u^2) + e_2(u)},   d = c_1/c_0^2,
   ```

   `e_2(u) = sum_{i<k} u^{2^i+2^k}` the Witt carry -- so `alpha` depends only on
   the `G_m`-invariant `d`, one value for each of the `q` orbits, and the whole
   list is one Walsh--Hadamard transform.
2. `flint` (python-flint): direct window enumeration with `is_irreducible`,
   plus a separate exact pass over the proper prime powers `P^{n/d}`.
3. `rust` (the lane's bulk engine, `axeyum-lemire-horizontal`, 24 threads, own
   `F_{2^r}` log tables and Rabin/distinct-degree test; source mirrored at
   `scripts/lemire-signed-trace/axeyum-lemire-horizontal.rs.txt`). Same
   algorithm as `flint`, `~4e7` polynomials/s.

**Controls** (the script exits nonzero if any fails; five mutation controls
each kill it through a *named* check):

* `C1` `A_r(n,1) = 0` identically -- computed, not assumed: `N_1(1)` is
  obtained by enumerating the full `a_{n-1} = 0` window and must equal
  `q^{n-1}` (conductor-1 characters have `L = 1`).
* `C2` Weil: `|alpha_d|^2 = q` exactly for every `d` and every `r`. (This also
  pins a structural fact: the Gaussian integers of norm `2^r` are exactly the
  four `i^k (1+i)^r`, so at `j = 2` every `alpha` is one of four values.)
* `C3` `witt` and `flint` agree on `A_r(n,2)`, every overlapping `(n,r)`.
* `C4` `rust` and `flint` agree on every `N_j` in the overlap.
* `C5` `(2^r - 1) | A_r(n,j)` on every row (Proposition 2(iv)).
* `C6` at `q = 2`, `I_n(1) = (N_j(1) - Theta(1))/n` with `j = ceil(n/2)-1`
  reproduces the lane's pinned `data/irreducible-counts-n2-38.txt` for
  `3 <= n <= 28` (20 degrees).

`C5` earned its keep immediately: it flagged a wrong `r = 8` row produced by a
merely *irreducible* (not primitive) field modulus (the AES polynomial
`x^8+x^4+x^3+x+1`, in which `x` has order `51`), which silently left most of the
log table zero. `assert(x^{q-1} = 1)` does not detect that; the engine now
verifies that `exp[0..q-1]` hits every nonzero element exactly once. The bad
dump is kept, and re-running the script against it still fails with
`control C5: (q-1) does not divide A_8(7,4) = 190017374764662784` -- so the
guard is checked, not merely claimed.

> **Proposition 3 (`j = 2`, complete).** For every `n >= 1` and every
> `r >= 1`, with `q = 2^r`,
>
> ```text
> n = 2 mod 4 :  A_r(n,2) = 0;
> n odd       :  A_r(n,2) = eps^r (q^{(n+3)/2} - q^{(n+1)/2}),  eps in {+1,-1};
> n = 0 mod 4 :  A_r(n,2) = eps^r (q^{(n+4)/2} - q^{(n+2)/2}).
> ```
>
> Hence `H^*_c(Prim_2 (x) F_2bar, Xi_n L_univ)` has Betti sum `C = 2`, with
> `h^2_c = h^3_c = 1` and weights `n+1`, `n+3` for odd `n` (so
> `i_max = 3 = 2j-1`), and `h^3_c = h^4_c = 1` with weights `n+2`, `n+4` for
> `n = 0 mod 4` (so `i_max = 4 = 2j`, i.e. the sheaf has geometric
> coinvariants); the cohomology vanishes for `n = 2 mod 4`.

*Status.* Verified exactly for `1 <= n <= 12`, `1 <= r <= 16` by
Berlekamp--Massey with integral weights asserted (the script fails otherwise).
The proof reduces to one classical input. By the reduction above, `alpha` is a
Gaussian integer of norm `q = 2^r`; `Z[i]` is a PID and `(1+i)` is the only
prime over `2`, so there are exactly four such, `i^k (1+i)^r`, `k = 0..3`. So
only the four multiplicities `m_k = #{d : alpha_d = i^k (1+i)^r}` matter, and

```text
A_r(n,2) = -(q-1) (1+i)^{rn} sum_k m_k i^{nk}.
```

Measured, `m_k = q/4 + delta_k` with `delta = (+u,0,-u,0)` for even `r` and
`(+u,+u,-u,-u)` for odd `r`, `u = 2^{floor((r-2)/2)}` -- this is the classical
correlation distribution of the `Z_4`-linear Kerdock code, i.e. the evaluation
of quadratic Galois-ring Gauss sums. Substituting gives
`|sum_k m_k i^{nk}| = sqrt q` for odd `n`, `= q` for `n = 0 mod 4` and `= 0`
for `n = 2 mod 4`, which is the display. The degree assignment then follows
from Proposition 2(v) with `Y = A^1`: `h^1_c(A^1, M^{(x)n}) = 1`, weight `n+1`
for odd `n`.

Note that at `j = 2` the two competing shapes coincide (`2j-1 = j+1 = 3`), so
`j = 2` cannot by itself separate "top minus one" from the `G_m`-forced
optimum. It does settle the budget: with `i_max = 3` and `C = 2`,
`(BUDGET)` demands `C <= 1/(4 sqrt2 ell)`, and Deligne's bound is in fact
*weaker than the trivial bound* here.

**Result at `j = 2` (exact, closed form, engine `witt`, `r = 1..16`).**

```text
n mod 4 = 2 :  A_r(n,2) = 0 identically.
n odd      :  A_r(n,2) = eps^r (q^{(n+3)/2} - q^{(n+1)/2}),  eps = +-1,
              two Frobenius eigenvalues of weights n+3 and n+1;  C = 2.
n mod 4 = 0 :  A_r(n,2) = eps^r (q^{(n+4)/2} - q^{(n+2)/2}),
              weights n+4 and n+2;  C = 2.
```

Verified by Berlekamp--Massey on `A_1..A_16` for every `n <= 12`, with integral
weights asserted. So at `j = 2`: the Betti sum is `2` -- as small as it can
be -- and the top degree is `2j-1 = 3` for odd `n` and `2j = 4` for
`n = 0 mod 4`. Both are in the *impossible* rows of Proposition 1. The
`n = 2 mod 4` rows vanish identically (`H^*_c = 0`), an exact accident of the
four-value Gaussian structure, not a mechanism.

`n mod 4 = 0` is `H^{2j}_c != 0`: the sheaf acquires geometric coinvariants
because all four `alpha` values have equal `n`-th power. This is the
"no cancellation at all" row.

**Cost model, and how to push further.** The window enumeration costs
`q^{n-j+1}` polynomials, which on the critical line `n = 2j+1` is `q^{j+2}`, so
`r <= 33/(j+2)` at `~4e7` polynomials/s: `r <= 8` at `j = 2`, `6` at `j = 4`,
`4` at `j = 6`. That is the binding limit, and it is why `j >= 4` does not
resolve. **The way past it** is not a faster window scan but the `L`-function
route: for `deg F = m <= j` the map `F -> <F>_j` is injective with image
`V_m = {1 + b_1 x + ... + b_m x^m}`, so

```text
L(chi,T) = sum_{m=0}^{j-1} c_m(chi) T^m,   c_m(chi) = sum_{g in V_m} chi(g),
```

(the higher coefficients vanish by orthogonality), and `S_n` follows from
`T L'/L`. Computing `c_m` for **all** `q^j` characters at once is one Fourier
transform over the abelian 2-group `E_j = prod_{k odd <= j} Z/2^{e_k}`, so the
whole table costs `~ (j-1) q^j log q` instead of `q^{j+2}` -- at `j = 4` that
is `q^4` against `q^6`, i.e. `r <= 8` instead of `r <= 6`, and it is
independent of `n`, so every `n` comes free. The lane already has the group
structure, discrete logarithms and character enumeration at `q = 2`
(`lemire_anchor.py`); generalizing them to `F_q` is the concrete next
engineering step for anyone who wants `j = 4, 5, 6` resolved.

**Result for `j >= 3`.** See the table below (regenerated by
`lemire_horizontal_weights.py --grid-file`). Rows are marked in-range when
`j <= ceil(n/2) - 1`, the range in which the Weil bound is not already worse
than the trivial mass bound `q^n` (the `l >= ceil(n/2)` cliff of note 11's
literature section).

Only the in-range rows are shown; the full table, including `j > ceil(n/2)-1`,
is `scripts/lemire-signed-trace/data/horizontal-weights.txt`. `w_meas` is
recorded only when Berlekamp--Massey closes on the data with `2C <= R` terms
and integral weights; `C` is then the Betti sum. `sav(q=2)` is the saving over
the trivial bound achieved at `q = 2` itself.

```text
  n   j   R  rng   w_meas  i_max>=    C   shape  sav(q=2)  4ell  w_loc tail
  5   2  14  yes        3        3    2    2j-1      1.41     8    3.00   3.00   3.00
  6   2  14  yes   A == 0 identically (H^*_c vanishes; nothing to bound)
  7   2  14  yes        3        3    2    2j-1      1.41    12    3.00   3.00   3.00
  7   3   6  yes        5        5    2    2j-1      2.83    12    5.20   5.09   5.05
  8   2  14  yes        4        4    2      2j      1.00    12    4.00   4.00   4.00
  8   3   5  yes   unres.        -    -       -      4.00    12    6.89   6.40   6.19
  9   2  14  yes        3        3    2    2j-1      1.41    16    3.00   3.00   3.00
  9   3   4  yes        3        3    2       j      5.66    16    4.17   3.44   3.20
  9   4   5  yes   unres.        -    -       -      6.79    16    6.56   1.24   4.79
 10   2  14  yes   A == 0 identically (H^*_c vanishes; nothing to bound)
 10   3   2  yes   unres.        -    -       -      4.00    16    5.17
 10   4   4  yes   unres.        -    -       -      6.00    16    9.34   5.12   5.86
 11   2  14  yes        3        3    2    2j-1      1.41    20    3.00   3.00   3.00
 11   3   2  yes   unres.        -    -       -      2.83    20    6.17
 11   4   4  yes   unres.        -    -       -      4.24    20    4.81   4.09   1.08
 11   5   4  yes   unres.        -    -       -     18.10    20   11.68   8.28   5.63
 12   2  14  yes        4        4    2      2j      1.00    20    4.00   4.00   4.00
 12   5   4  yes   unres.        -    -       -      6.40    20    7.44   9.83   7.70
 13   6   4  yes   unres.        -    -       -      7.07    24    6.55   8.54   8.54
```

**Reading it.**

- Every row is divisible by `2^r - 1` (control C5), for every `(n,j,r)`
  computed -- the `G_m` factor of Proposition 2 is visible in the integers.
- `j = 2` is exact for `r <= 14` and settles into three families by
  `n mod 4`: `2j-1` (odd `n`), `2j` (`n = 0 mod 4`), identically zero
  (`n = 2 mod 4`, the only vanishing in the table). Only the middle family is
  informative about the *shape*: at `j = 2` the labels `2j-1` and `j+1` name
  the same degree `3`, so the odd-`n` rows are consistent with the
  `G_m`-forced optimum, whereas `w = 2j` forces `H^{2j}_c != 0`.
- **`(7,3)` is the decisive in-range row on the critical line `n = 2j+1`**:
  `A_r(7,3) = 64^r - 32^r` exactly for `r = 1..6`, so the two Frobenius
  eigenvalues are `2^6` and `2^5`, weights `12` and `10`, `C = 2`, and
  `i_max >= 12 - 7 = 5 = 2j-1`. By Proposition 1 no Betti bound can help there.
- `(9,3)` is the exception and it is exact: `N_3(1) = q^{n-3}` on the nose, so
  `A_r(9,3) = -A_r(9,2)` and the top weight is only `n + j`. This row is
  consistent with the good case, and it is why the resolved rows must not be
  read as a law.
- `j >= 4` does **not** resolve. Those rows carry several eigenvalues of
  comparable modulus with nontrivial phases -- at `(7,4)`, just outside the
  range, the sequence is `A_r = -(q-1)q^4 (q+1)` for `r` not divisible by `3`
  and `+(q-1)q^4(2q-1)` for `3 | r`, i.e. primitive cube roots of unity times
  `2^6` -- and the affordable `r` (at most `33/(j+2)`) is below the `2C` terms
  Berlekamp--Massey needs. The `w_loc` tails in those rows sit between `j+1`
  and `2j-2` and drift.
- The `sav(q=2)` column is the `q = 2` reality and it agrees with notes 05/07,
  not with the `q`-aspect exponent: at `(7,3)` the achieved saving is `2.83`,
  which is the random-phase value `2^{(j-1)/2} sqrt(j-1)` (`= 2.83` at
  `j = 3`), against a required `4 ell = 12`. The `G_m` factor that dominates the `q`-aspect has
  exactly one `F_2`-point, so it contributes nothing here.

## 7. Verdict

**(iii) mixed, and specifically: proved dead where it resolves, undetermined
where it does not.**

*What is proved.*

1. **The Deligne/Betti route cannot work at any `(n,j)` whose top cohomological
   degree is `>= 2j-2`.** This is Proposition 1 and needs no computation. It is
   what makes note 10's Q1 the wrong question: `C` is not the binding
   constraint.
2. **Middle concentration is unavailable for this family** (Proposition 2,
   unconditional for the geometry, conditional on freeness/descent for the
   conclusion -- proved at `j = 2`, measured for `j >= 3` by
   `(2^r-1) | A_r(n,j)` on every row): `Prim_j = G_m x A^{j-1}` and the
   `G_m`-direction contributes a full, uncancelled `#G_m(F_q) = q-1` to every
   `A_r`, pushing the top degree to at least `j+1`. So the *best possible* case is `i_max = j+1`, and even that is
   enough, with `C <= (j-1)2^{(j-1)/2}/(8 ell)` -- exponential room.
3. **At `j = 2` the cohomology is completely determined** (Proposition 3):
   `C = 2` always, `i_max = 2j-1 = 3` for odd `n`, `i_max = 2j = 4` for
   `n = 0 mod 4`, `H^*_c = 0` for `n = 2 mod 4`. **Read this carefully.** At
   `j = 2` the two shapes coincide (`2j-1 = j+1 = 3`), so the odd-`n` rows do
   *not* distinguish "top minus one" from the `G_m`-forced optimum -- they are
   consistent with the good case. The `n = 0 mod 4` rows do: a class of weight
   exactly `n + 2j` can live only in degree `2j`, so there `H^{2j}_c != 0`, one
   degree strictly above the optimum and the worst case there is.
4. **Exactly one in-range row on the critical line `n in {2j+1, 2j+2}` both
   resolves and can separate the shapes, and it is bad.** That row is
   `(n,j) = (7,3) = (2j+1, j)`: `A_r(7,3) = 64^r - 32^r` exactly for
   `r = 1..6`, so `C = 2` and the top weight is `12 = n + 2j - 1`, forcing
   `i_max >= 2j-1 = 5`, strictly above the optimum `j+1 = 4`. By Proposition 1
   no Betti bound helps at `(7,3)`. Its size is exactly
   `q^{j-1}(q-1) q^{(n-1)/2}` -- one square root of cancellation over the whole
   `j`-dimensional family and none of the Weil rank factor `(j-1)` -- which is
   also the shape of `(5,2)`, `(7,2)`, `(9,2)`, `(11,2)` and `(6,3)`.
   `(8,3) = (2j+2, j)` drifts toward `w = 2j = 6` without closing.

*What is not proved.* `j >= 4` on the critical line is **not resolved** by this
experiment. `A_r(n,j)` for `(9,4)`, `(10,4)`, `(11,5)`, `(12,5)`, `(13,6)` has
several Frobenius eigenvalues of comparable modulus with nontrivial phases
(cube roots of unity appear already at `(7,4)`), and the affordable range is
`r <= 5` or `6`: the window enumeration costs `q^{n-j+1} = q^{j+2}` at the
critical line, so `r <= 33/(j+2)`. Berlekamp--Massey needs `2C` terms and
`C > 3` is already out of reach. The local slope estimates in those rows sit
between `j+1` and `2j-2` and do not settle. **One row goes the other way:**
`(9,3)` has `N_3(1) = q^{n-3}` exactly, so `A_r(9,3) = -A_r(9,2)` and the top
weight is only `n + 3 = n + j`. That is below `n + (j+1)`, so it does not
contradict Proposition 2(v) -- a nonzero `H^{j+1}_c` may simply carry weight
lower than `n + j + 1` -- but it is exact (`r = 1..4`), it is consistent with
the good case, and it is a warning against reading the resolved rows as a law.

*Extrapolation: what is and is not justified.* The invariants `i_max` and `C`
are geometric -- they belong to `H^*_c(Prim_j (x) F_2bar, Xi_n L_univ)`, which
does not depend on `r`. So varying `r` at fixed `(n,j)` is a legitimate way to
read them off, and the conclusion "`i_max >= 2j-1` at `(7,3)`" is a statement
about the same cohomology that governs `q = 2`. What is **not** justified is
extrapolating in `j`: we see `j <= 3` resolved and `j <= 6` at all, while
`(HWO)` needs `a <= j <= ell` with `ell >= 200`. Nor should the `q`-aspect
*size* be read as a `q = 2` statement: the `G_m` factor that dominates the
`q`-aspect growth has exactly **one** `F_2`-point, so at `q = 2` it is
invisible -- and indeed at `q = 2` the measured saving over the trivial bound
(column `sav(q=2)` above) agrees with the random-phase prediction
`2^{(j-1)/2} sqrt(j-1)`, which is what notes 05 and 07 already report.

*How a general proof of the obstruction would go.* Prove the structural
hypothesis that the resolved rows satisfy:

> **(H)** There is a `G_m`-invariant morphism `pi : Prim_j -> A^1` over `F_2`
> and a rank-one lisse `M` on `A^1` such that the semisimplification of
> `Xi_n(L_univ)` is geometrically `pi^*(M^{(x)n})` tensored with a
> geometrically constant sheaf.

`(H)` is **proved for `j = 2`** (section 6: `alpha(chi_c)` depends on
`c = (c_0,c_1)` only through `d = c_1/c_0^2`, and by Chebotarev the trace
function determines the semisimplification). Under `(H)`, Kuenneth gives
`H^*_c(Prim_j, Xi_n L_univ) = H^*_c(G_m) (x) H^*_c(A^{j-2}) (x) H^*_c(A^1, M^{(x)n})`,
hence `i_max = 2 + 2(j-2) + 1 = 2j-1` exactly and `C = 2 h^1_c(A^1, M^{(x)n})`,
which is the observed `C = 2` with `h^1_c = 1`. `(H)` also predicts
`|A_r(n,j)| = q^{j-2} |A_r(n,2)|`, which holds exactly at `n = 5, 7, 11` for
`j = 2,3`, holds up to a factor `(q-1)/q` at `n = 8`, and **fails at `n = 9`** -- so `(H)` is not universal, and the honest
form of the conjecture is that it holds off a thin exceptional set of `(n,j)`.
The equivalent dual statement, for anyone who wants to attack it directly, is a
nonzero class in `H^1(Prim_j (x) F_2bar, Xi_n(L_univ)^v)`, which by Poincare
duality is `H^{2j-1}_c` up to a Tate twist.

*Bottom line for the lane.* The horizontal geometric route is not a
Betti-number problem. Whoever attacks it must produce a **degree** theorem --
concentration in degrees `<= j+1`, or at least `<= 2j - 2 log2(8 ell C/(j-1))`
-- and the literature has no mechanism that delivers one here: middle
concentration in print always comes from forget-supports being an isomorphism,
or from genericity in a twisting character, or from a singular-locus dimension
bound, never from big monodromy, and `H^{2d-1}_c` is uncontrolled. Katz's own
Thm 8.2 is the `i_max = 2 dim - 1` shape, which Proposition 1 says can never
reach `(HWO)`; and at `p = 2` it is not even available. Angle 4 therefore does
not close `(HWO)` and does not obviously fail either -- but it relocates the
question from "how big is `C`" to "how far below `2j` does the cohomology
stop", and gives the first exact answer (`2j-1`, `C = 2`) in the cases small
enough to compute.

## 8. Reproducibility

```sh
cd scripts/lemire-signed-trace
# all controls plus the table, from the committed Rust dumps (~10 s)
python lemire_horizontal_weights.py --grid-file data/horizontal-grid.txt \
    --out data/horizontal-weights.txt
python lemire_horizontal_weights.py --mutate 1          # must exit nonzero
# the deliberately kept bad dump: must exit 1 on control C5
python lemire_horizontal_weights.py \
    --grid-file data/horizontal-grid-primitivity-bug.txt
# re-run the engine itself (needs the branch snapshot build)
AXEYUM_LEMIRE_HORIZONTAL=<snapshot>/target/release/axeyum-lemire-horizontal \
  python lemire_horizontal_weights.py --grid 9:5:3,11:4:4
```

Generated table: `scripts/lemire-signed-trace/data/horizontal-weights.txt`;
Rust dumps it is read from: `data/horizontal-grid.txt` (98 runs, `n <= 13`,
`r <= 8`). Rust source mirrored at
`scripts/lemire-signed-trace/axeyum-lemire-horizontal.rs.txt`; build it inside a
snapshot of branch `agent/gf2/lemire-proof` with
`AXEYUM_CARGO_LOCK=... scripts/cargo-serialized.sh build --release -p axeyum-cas
--bin axeyum-lemire-horizontal`.

## 9. Coordinator addendum (2026-08-22): the `F_2` data at `ell = 24` vs the small rows

The resolved small rows (`j <= 3`) sit in a FINITE-MONODROMY regime and do not
extrapolate. At `j = 2`, `L_univ` has rank 1 with eigenvalue angles in the 8th
roots of unity; at `j = 3` (rank 2) a hand computation of the four exact-
conductor-3 characters over `F_2` gives eigenvalue angles in the 24th roots of
unity (e.g. `chi(1+x) = i`: `L = 1 + (1+i)u + 2i u^2`, `alpha/sqrt2 =
e^{-5 pi i/12}`). Finite monodromy forces geometric (co)invariants of
`Xi_n(L_univ)` for `n` divisible by the exponent, i.e. exactly the top-degree
classes the rows `(8,2)`, `(12,2)`, `(7,3)` exhibit. That is a small-`j`
degeneracy, not the large-`j` shape; the lane's `F_2` data say the monodromy
is Sato--Tate-like by `ell = 16` (note 05 sec. 4).

Summing the exact-order layers of `layers-ell24-n49.txt` / `-n50.txt` to the
conductor-`j` sums `A_j = sum_s T_{j,s}` and dividing by `2^{n/2}`:

```
(24,49)  j : 18     19     20     21     22     23      24
 |A_j|/2^{n/2}   3165   2712   2592   2142   1776   7190   14829
 (H) = 2^{j-2}|A(n,2)|/2^{n/2}   92682 185364 370728 741455 1.5e6 3.0e6 5.9e6
 alive size 2^{(j+1)/2}           724   1024   1448   2048   2896  4096  5793
 trivial #X (j-1)               2.2e6  4.7e6  1.0e7  2.1e7  4.4e7 9.2e7 1.9e8
(24,50)  |A_j|/2^{n/2}:  229  1175  8759  5379  7670  2263  8462
```

So at large `j` the conductor sums are `2^{(j+1)/2} x O(1..3)` -- the size of
`i_max = j+1` with `C = O(1)` -- while hypothesis (H) over-predicts by
`30..100x` and the trivial bound by `10^2..10^4`. (H) is therefore false at
large `j`, and the `F_2` data are CONSISTENT with the alive case of (Q1'):
top degrees above `j+1` absent (or cancelling) and small `C`. This is
evidence, not a theorem (it is one `r`, and cancellation between degrees at
`r = 1` is possible), but it is the opposite of "leaning dead".

**Priority follow-up (angle 4b):** (1) the `L`-function route of sec. 7 to
resolve `(2j+1, j)` for `j = 4, 5, 6` at `r` up to 7--8, which decides whether
top-degree classes persist past the finite-monodromy regime; (2) the
monodromy of `L_univ` at `p = 2` as `j` grows -- at which `j` does it stop
being finite, and is it then big? [Answered in note 14: it is a theorem --
Katz IMRN 2013 Thm 5.1 gives `G_geom` containing `SL(j-1)` at `p = 2` for every
`j >= 4` (the `p > 2n-1` hypothesis belongs only to his Betti-constant Thm
8.2), and Gorodetsky FFA 2019 Lemma 3.5 settles `(p,j) = (2,3)` as finite.]
