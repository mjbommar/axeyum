# The probabilistic face: the variance statement, four probabilistic tools, and the mechanism behind the anti-correlation

Status: research note, 2026-08-23. Lane `lemire-signed-trace`. Nothing here
proves a new case of Kaser--Lemire. What it does is (A) state the fixed-`q`
second-moment theorem that note 18 identifies as the highest-value target, in
the `j`-dependent form the data force, with its measured constant; (B) work
four probabilistic tools -- negative association, martingale concentration,
Stein/Chen--Stein, extreme-value theory -- each to a bound or an exact
obstruction; (C) **explain** note 20's unexplained anti-correlation
`r = -0.657`, quantitatively and from first principles; and (D) calibrate the
random model the lane's heuristics rest on, reporting four places it is
confirmed and six where it fails.

Checker: `scripts/lemire-signed-trace/lemire_probabilistic.py` (23 named checks,
8 mutation controls each verified to kill exactly one check; exits nonzero on
any violation; ~7 s). Data: `data/prob-variance-ladder.txt`,
`data/prob-order-statistics.txt`, `data/prob-martingale.txt`,
`data/prob-anticorrelation.txt`, `data/prob-model-calibration.txt`.

Companions: [05-almost-all-theorem.md](05-almost-all-theorem.md) (Parseval +
Weil; the `Sigma_j` ladder), [18-savings-scale.md](18-savings-scale.md) (the
`F`/`k` dial; B3), [20-almost-all-degrees.md](20-almost-all-degrees.md) (the
`d_n` decomposition, the `z` statistics, the anti-correlation),
[07-covariance-phase-face.md](07-covariance-phase-face.md) and
[17-cylinder-plancherel.md](17-cylinder-plancherel.md) (the phase face),
[03-uncertainty-analogy.md](03-uncertainty-analogy.md) sec. 5 (Barrier I),
[00-state-of-the-problem.md](00-state-of-the-problem.md).

---

## 0. Verdict up front

1. **(A) The variance statement.** What must be proved is
   `Sigma_j(n) <= C 2^{j-1}(j-1) 2^n` for an absolute `C` -- Weil's bound
   divided by `(j-1)`. The improvement over Weil **must** be `j`-dependent:
   `Sigma_2 = 2^{n+1}` **exactly** at every endpoint, so `Sigma_j <= (1-eps)`
   times Weil, uniformly in `j`, is FALSE. Measured over 242 `(ell,n,j)` rows:
   `C_j` has mean `1.000` at every fixed `j`, `sup_j C_j = 2.179`, and
   `sup_{j >= 14} C_j = 1.047`. Aggregate constant `1.0274`.
2. **(B) Four tools, four exact obstructions**, all landing on the same wall
   with the same explicit constant `(ell-1)/(2 kappa)`:
   - **negative association**: the constraint `sum_g N_ell(g) = 2^n` forces
     *exactly* `sum_{t != 0}(R(t) - 2^{2n-ell}) = -V` (new, exact, verified on
     22 dumps), but every conclusion drawn from mass + nonnegativity +
     correlation of the entries is a **cylinder-mass** statement, and Barrier I
     applies verbatim;
   - **martingale**: the Doob martingale of `N_ell(G)` along the tower has
     increments `D_j(g) = 2^{-ell} sum_{chi in X_j} S_n(chi) conj(chi(g))`; the
     top increment's Weil bound alone exceeds the entire target by
     `(ell-1)/(2 kappa)`, and **no concentration inequality can beat the largest
     increment bound**. Freedman with the true conditional variance is dominated
     by the same term. The increment bound is also **attained at `j = 2`**, so it
     admits no uniform-in-`j` improvement either;
   - **Chen--Stein**: the total-variation distance to Poisson has a **floor of
     order `1/n`**, which is not an artefact of the method (it is the true
     `Bin` vs `Poi` distance). Resolving one class in `2^ell` needs `2^{-ell}`.
     Short by `2^{18.4}` at `n = 50`, `2^{191}` at `n = 402`, `2^{1013}` at
     `n = 2050`;
   - **extreme value**: `max_g |D_g| / sd` is `0.758--1.188` times the Gumbel
     value `sqrt(2 ell log 2)` -- the class ensemble is textbook. **New
     measurement:** the identity's *rank* among the `2^ell` classes. Its
     quantile has mean `0.311` against the uniform `0.500` (`3.08` sigma low),
     and it lands in the **top 5% of classes at 6 of 22 endpoints** against
     `1.10` expected (Poisson `p = 9.7e-4`). The identity is **not** a typical
     class.
3. **(C) The anti-correlation is explained.** It is not a normalisation
   artefact (proved: the `2^{ceil(n/2)}` convention cancels exactly out of `z`),
   not a proper-power artefact (measured: `-0.661 -> -0.622` after removing the
   square mass exactly), and not the functional equation. It is the exact
   **eighth-root angle repeats**: `76--85%` of `sum_theta m_theta^2` sits on
   `theta in (1/8)Z`, dominated by `theta = 3/8, 5/8` (the two conductor-2
   Kerdock angles `alpha = -(1 -+ i)`), with `cos(2 pi * 3/8) = -1/sqrt2`.
   The lag-1 autocorrelation of `G_ell(n)` is
   `rho_1 = (sum m^2 cos 2 pi theta - m_0^2)/(sum m^2 - m_0^2)`, measured
   `-0.280 .. -0.449` and **predicted to within `0.008`** at every `ell`.
   Stronger: the sign of `z_n` is a function of `n mod 8` alone, correct at
   **42 of 45 endpoints** (`p = 4.3e-10`).
4. **(D) The model is right within a character and wrong across characters.**
   Confirmed: second, third and fourth moments over classes, and the maximum.
   Failed: the identity's rank; `Sigma_2/Sigma_1 = 18.0` at `ell = 13` and
   growing like `2^{0.50 ell}`; cross-conductor correlation of the blocks
   `g_j(n)` with mean `+0.452`; `Var(G) = 2.32 sum_j Var(g_j)`; and the
   consecutive-degree correlation itself. The model still predicts finitely many
   bad `n`, but the Gaussian exponent drops from `2^{ell}` to about
   `2^{0.33 ell}`.

---

## 1. Setting

`E_ell = (1 + x F_2[x])/x^{ell+1}`, `|E_ell| = 2^ell`, `ell = ceil(n/2)-1`,
`<F>_ell = x^{deg F}F(1/x) mod x^{ell+1}`,
`N_ell(g) = sum_{deg F = n, <F>_ell = g} Lambda(F)` (mean `2^{n-ell}`, total
`2^n`), `S_n(chi) = sum_{deg F = n} Lambda(F) chi(<F>_ell)`. `X_j` is the set of
`2^{j-1}` characters of exact conductor `j`; by Weil/Katz
`L(u,chi) = prod_{i<=j-1}(1 - alpha_i u)`, `|alpha_i| = sqrt 2`, and
`S_n(chi) = -sum_i alpha_i^n`. Write

```text
D_n = N_ell(1) - 2^{n-ell},   d_n = D_n 2^{ell-n},   V = V(ell,n) = sum_g (N_ell(g) - 2^{n-ell})^2,
Sigma_j(n) = sum_{chi in X_j} |S_n(chi)|^2,          D(ell) = sum_{j<=ell} 2^{j-1}(j-1) = (ell-2)2^ell + 2,
kappa = 2^{n/2-ell} in {sqrt 2, 2},                  sd = sqrt(2^{n-ell}(ell-2) + 2^{n-2ell+1}),  z = D_n/sd.
```

`A_ell` is the multiset of all `D(ell)` Frobenius angles `theta` of `E_ell`
(`alpha = sqrt2 e(theta)`, over all `chi != 1`), with multiplicities
`m_theta`, and

```text
G_ell(n) = sum_{theta in A_ell} e(n theta) = -2^{-n/2} sum_{chi != 1} S_n(chi),
d_n = -2^{-n/2} G_ell(n),        Sigma_1^A = sum_theta m_theta = D(ell),   Sigma_2^A = sum_theta m_theta^2.
```

`Sigma_1^A` and `Sigma_2^A` are written `Sigma1`/`Sigma2` in
`data/prob-anticorrelation.txt`; they are **not** the `Sigma_j` of note 05,
which are per-conductor second moments of `|S_n|`. Both names are the lane's;
the note keeps them apart by always writing the superscript `A` in prose.

Two engines. The branch CAS `axeyum-gf2-dump-populations <ell> <n> 1300000000`
(the third argument is **required**; without it the binary panics and leaves a
zero-byte dump) produces the exact class populations for
`12 <= ell <= 22`, both degrees. An embedded pure-Python Hayes-character engine
-- `E_j = prod_{k odd} <1+x^k>` with `ord(1+x^k) = 2^{e_k}`,
`e_k = floor(log2(j/k))+1`, exact discrete log, `c_m(chi) = sum_{v in V_m}chi(v)`
in `Z[zeta_{2^E}]`, `S_n` = the `u^n` coefficient of `u L'/L` -- runs live in every checker
invocation for `ell <= 11`. It reproduces `D_n` **exactly** at all 20 endpoints
`2 <= ell <= 11`, and reproduces note 18's independently flint-enumerated
`Theta_ell(1)` at all 11 of its even endpoints.

---

## 2. (A) The variance statement, in its correct `j`-dependent form

### 2.1 What must be proved

> **Conjecture (VAR).** There is an absolute constant `C` such that for every
> `ell >= 2`, every `n`, and every `2 <= j <= ell`,
> ```text
> Sigma_j(n) = sum_{chi in X_j} |S_n(chi)|^2  <=  C * 2^{j-1} (j-1) 2^n.
> ```

Three equivalent forms, by Parseval on `E_ell` and by summing the ladder:

```text
(VAR-agg)   sum_{chi != 1} |S_n(chi)|^2  <=  C 2^n D(ell)          [aggregate]
(VAR-class) V(ell,n) = sum_g (N_ell(g) - 2^{n-ell})^2  <=  C 2^{n-ell} D(ell)
(VAR-per-j) Sigma_j(n) <= C 2^{j-1}(j-1) 2^n                       [per conductor]
```

`(VAR-per-j) => (VAR-agg) <=> (VAR-class)`; the aggregate is what the `F`/`k`
dictionary consumes. Weil gives `Sigma_j <= 2^{j-1}(j-1)^2 2^n`, so
**`(VAR)` asks for a saving of exactly the factor `(j-1)` over Weil, at every
conductor.**

### 2.2 Why the saving must be `j`-dependent: `Sigma_2` saturates

`E_2 = Z/4`; its two primitive characters have `L(u,chi) = 1 - alpha u` with
`alpha = -(1 + i^{+-1})`, `|alpha| = sqrt 2`. Hence
`|S_n(chi)| = |alpha^n| = 2^{n/2}` **exactly**, and

```text
Sigma_2(n) = 2 * 2^n = 2^{n+1}   exactly, at every (ell, n).       [CHECK_VARIANCE_SIGMA2_SATURATES]
```

That is *both* the Weil bound `2^{j-1}(j-1)^2 2^n` and the Sato--Tate value
`2^{j-1}(j-1) 2^n` at `j = 2`, because `(j-1)^2 = (j-1) = 1` there.

> **Consequence.** Any statement of the form
> `Sigma_j <= (1 - eps) * 2^{j-1}(j-1)^2 2^n` **uniformly in `j`** is FALSE: it
> fails at `j = 2` for every `n`. The improvement over Weil cannot be a
> constant; it is `(j-1)`, and `(VAR)` is the sharp shape.

This is why note 05 section 4's "`Sigma_2` saturates the sharp Weil bound while
`rms|S|/((j-1)2^{n/2}) = 1/sqrt(j-1)` to four digits at `j = 24`" is not two
facts in tension: `sqrt(j-1)` inside Weil per character is `(j-1)` inside Weil
in the second moment, and at `j = 2` the two coincide.

### 2.3 The measured constant

`data/prob-variance-ladder.txt`: 242 rows, `12 <= ell <= 22`, both degrees, all
`1 <= j <= ell`, exact integers. `C_j := Sigma_j / (2^{j-1}(j-1)2^n)`.

```text
 j    rows   min C_j    max C_j   mean C_j          j    rows   min C_j   max C_j  mean C_j
 2      22   1.000000   1.000000  1.000000         13      20  0.915550  1.117469  0.998604
 3      22   0.500000   2.000000  0.977273         14      18  0.972234  1.047316  1.001032
 4      22   0.084641   1.983203  0.999681         16      14  0.985404  1.019592  1.003432
 5      22   0.317524   2.179314  0.964982         18      10  0.991182  1.011787  1.001994
 7      22   0.584198   1.322925  1.007999         20       6  0.998553  1.004570  1.001411
 9      22   0.693818   1.388025  0.999622         22       2  0.999152  0.999272  0.999212
11      22   0.866338   1.081786  1.003959
```

- **The mean is `1.000` at every `j`** -- Sato--Tate on the nose, to three
  digits, at fixed `q = 2`.
- The fluctuation shrinks like `2^{-(j-1)/2}`: only small `j` is noisy.
  `sup_j C_j = 2.179` at `(ell,n,j) = (17,36,5)`; `sup_{j>=12} C_j = 1.126`;
  `sup_{j>=14} C_j = 1.047`; `sup_{j>=20} C_j = 1.005`.
- Aggregate: `V 2^ell / (2^n D(ell))` runs `0.9711 .. 1.0274` over the 22
  endpoints and is within `1%` of `1` for `ell >= 16`.
- Exact Parseval control: `sum_j Sigma_j = 2^ell V` as integers, every row.

> **Stated with its constant.** `(VAR)` holds with `C = 2.20` over every
> `(ell,n,j)` computed, with `C = 1.13` restricted to `j >= 12`, and
> `(VAR-agg)` holds with `C = 1.03`. The evidence is that `C_j -> 1`; the
> conjecture needs only *some* absolute `C`.

### 2.4 What `(VAR)` buys, and what it does not

By note 18 B3, `(VAR-agg)` plus Cauchy--Schwarz gives a uniform saving
`F = sqrt(D(ell)/(C 2^ell)) = sqrt((ell-2)/C)` over Weil, and the dictionary
`k_min(F) = ceil(log_2((ell-2)/(F kappa)))` turns that into

```text
ell = 200:  F = sqrt(198) = 14.07  ->  k = 4 (n = 401),  k = 3 (n = 402),
                                       against k_Weil = 8 and 7.
```

**Half the Weil `k`, not `k = 0`.** Kaser--Lemire needs `F = (ell-2)/kappa`, a
full power of `ell`; a second moment carries `sqrt(ell)` and no more. `(VAR)` is
worth exactly one halving of the slack ladder, and it is the largest single
unconditional gain visible anywhere on the board.

### 2.5 New: `(VAR)` and Barrier I cross at exactly `k_Weil/2`

Barrier I (note 03 sec. 5) exhibits, at level `l = ell - k`, a nonnegative `F`
with the true low-conductor Fourier data, `sum F = 2^n`, `F(1) = 0`, and
`F^hat(chi) = -c` for every conductor `>= a`, `c ~ 2^{n-l}`. Its own second
moment is

```text
sum_{chi != 1} |F^hat(chi)|^2  >=  (2^l - 2^{a-1}) c^2  ~  2^{2n-l},
```

against the `(VAR-agg)` allowance `C 2^n D(l) ~ C(l-2)2^{n+l}`. So the fake
population **satisfies** `(VAR)` iff

```text
2^{n-2l} <~ C(l-2),   i.e.   kappa^2 2^{2k} <~ C(ell - k - 2),
   i.e.   k  <=  (1/2) log_2(ell) - log_2 kappa + O(1)  =  k_Weil/2 + O(1).
```

> **Proposition 1.** Barrier I's fake population is admissible precisely for
> `k <~ k_Weil/2`, and violates `(VAR)` above that. `(VAR)` therefore opens
> exactly the window `k_Weil/2 <= k < k_Weil` -- which is exactly the rung note
> 18's ladder assigns to `F = sqrt(ell-2)` (`k = 4` against `k_Weil = 8` at
> `ell = 200`), reached there by a completely different computation.

Two independent routes agreeing on the same boundary is the reason to believe
both. It also says what `(VAR)` is *not*: it does not touch `k = 0`, and Barrier
I still blocks every moduli-only argument below `k_Weil/2`.

### 2.6 Why it is open

By Parseval the exact second moment **is** `V`, so orthogonality cannot supply
`(VAR)` (note 05 sec. 2). The statement is the Keating--Rudnick short-interval
variance at **fixed** `q = 2`; KR is a `q -> infinity` theorem and every
function-field analogue in print (Katz, Sawin, Hall--Keating--Roditty-Gershon,
Roditty-Gershon, Hochfilzer) is a matrix-integral limit. Cauchy--Schwarz against
the *unconditional* second moment returns `F < 1` (note 18 B3). Nothing in the
lane's toolbox produces it.

---

## 3. (B) Four probabilistic tools

### 3.1 (i) Negative association: an exact sum rule, then Barrier I

The hard constraint `sum_g N_ell(g) = 2^n` forces negative correlation, and the
force is *exactly* computable. With `R(t) = sum_g N_ell(g)N_ell(g+t)` (`t` in
`E_ell`) and the random value `R_rand = 2^{2n-ell}`:

> **Lemma 2 (the sum rule).**
> ```text
> sum_{t != 0} ( R(t) - 2^{2n-ell} )  =  -V(ell,n)      exactly.
> ```
> *Proof.* `sum_t R(t) = (sum_g N)^2 = 2^{2n}` and `R(0) = sum_g N^2 =
> V + 2^{2n-ell}`; subtract `(2^ell - 1)2^{2n-ell}`. QED

Verified as an exact integer identity on all 22 dumps
(`CHECK_NEGATIVE_CORRELATION_SUM_RULE`). So the average connected covariance per
shift is `-V/(2^ell - 1) ~ -(ell-2)2^{n-ell}`, relatively
`-(ell-2)2^{-(n-ell)}`: negative, and doubly tiny -- which is the quantitative
form of note 07's "the mean is systematically negative (a sum-rule from
`sum N = 2^n`) but doubly tiny".

**The obstruction.** A negative-dependence structure (FKG/Harris, NA, or a
strong Rayleigh property) on the vector `(N_ell(g))_g` would yield Chernoff-type
concentration for **sums over subsets** `sum_{g in S} N_ell(g)`. Every such sum
is a *cylinder mass*, and note 18 B5 proves that every unconditional upper bound
on a cylinder mass is itself a Weil bound, losing a factor between `3` and `9`
to Weil. Worse, and decisively:

> **Proposition 3.** Any conclusion derived from (mass) + (nonnegativity) +
> (correlations of the entries, in any form) applies verbatim to Barrier I's
> `F`, which has the same total mass `2^n`, is nonnegative, has the true
> low-conductor Fourier data, second moment *below* the truth -- hence
> **more** negative correlation, by Lemma 2 -- and `F(1) = 0`. So no
> correlation inequality can prove `N_ell(1) > 0`.

Note that Lemma 2 makes this sharper than the generic Barrier-I statement:
because `F`'s second moment is measured at `0.22, 0.15, 0.12` times `N`'s (note
03 sec. 5), `F` is *less* negatively correlated in the aggregate than `N`, so an
argument of the form "the entries are so negatively correlated that no entry can
vanish" is running in the wrong direction: the more negative correlation, the
larger `V`, the *worse* the minimum. **Verdict: exact obstruction, no bound.**

### 3.2 (ii) Martingale concentration along the Witt tower

The right filtration is the tower `E_ell ->> E_{ell-1} ->> ... ->> E_1`, and the
right object is the **Doob martingale** of `N_ell(G)` for `G` uniform on
`E_ell`:

```text
M_j(g) = 2^{-(ell-j)} N_j(pi_j g),    M_ell = N_ell(G),   M_0 = 2^{n-ell},
D_j := M_j - M_{j-1} = 2^{-ell} sum_{chi in X_j} S_n(chi) conj(chi(g)),
E[D_j] = 0,    E[D_j^2] = 2^{-2ell} Sigma_j(n),    |D_j| <= b_j := 2^{j-1}(j-1) 2^{n/2-ell}.
```

The increments are literally the lane's `H_j`, and `sum_j D_j(1) = D_n`: the
martingale IS `(BLOCK)`.

> **Proposition 4 (the concentration ceiling).** For a sum with increment bounds
> `b_j`, every inequality that sees only the `b_j` -- Azuma--Hoeffding,
> Burkholder, McDiarmid -- gives a deviation bound `>= max_j b_j`, because the
> whole sum can sit in one increment. Here `b_j` grows geometrically, so
> `max_j b_j = b_ell`, and
> ```text
> b_ell / 2^{n-ell}  =  (ell - 1) / (2 kappa)      exactly.
> ```

Measured at every endpoint (`CHECK_DOOB_INCREMENT_GAP`): `3.889` at
`(12,25)`, `7.425` at `(22,45)`, and `(ell-1)/(2 kappa) = 70.36` at
`(200,401)`. Compare note 18: `F_req(0) = (ell-2)/kappa = 140.007` there. **The
top increment's Weil bound alone overshoots the entire target by a factor
`(ell-1)/(2 kappa)`, i.e. by exactly `(AGG_0)` up to a factor 2.** Concentration
adds literally nothing: one would first have to prove `(HWO)` for `j = ell`.

Freedman's inequality does not help, and the arithmetic says why. With the true
conditional variance `v = sum_j E[D_j^2] = 2^{-2ell} sum_j Sigma_j = V 2^{-ell}
~ (ell-2)2^{n-2ell}` and target `t = 2^{n-ell}`,

```text
t^2/(2v) ~ 2^{n-1}/(ell-2)   [astronomically more than the ell log 2 needed],
but   t^2 / (2(v + t b_ell/3)) ~ 3t/(2 b_ell) = 6 kappa/(ell-1)  ->  0.
```

So with the true variance a sub-Gaussian tail would give the conjecture with
room to spare; the entire failure is the `b` term, i.e. the increment bound
again. **The increment bound needed is `b_ell <~ t = 2^{n-ell}`, a factor
`(ell-1)/(2 kappa)` below Weil.**

And that bound cannot be improved uniformly in `j` either, for the same reason
as `(VAR)`:

```text
max_g |D_2(g)| / b_2  =  1  EXACTLY at every even n,  =  2^{-1/2} at every odd n
```

(`CHECK_DOOB_INCREMENT_TRUE`; the two conductor-2 characters are conjugate, so
some `g` aligns their phases). Meanwhile the *true* top increment is far inside
Weil -- `max_g|D_ell(g)|/b_ell` falls from `0.0247` at `ell = 12` to
`0.000745` at `ell = 22`, i.e. `1342x` inside Weil where only `7.4x` is needed.
The truth is fine; the provable bound is not. **Verdict: exact obstruction,
quantified; the needed increment bound is `(HWO)` itself.**

### 3.3 (iii) Stein's method / Chen--Stein: a clean impossibility

Let `W = I_n(1) = #{f in W_n irreducible}`, `W_n = {x^n + g : deg g <=
floor(n/2)}`, `|W_n| = 2^h`, `h = n - ell`. The prime number theorem for
`F_2[t]` gives `p = P(f irreducible) ~ 1/n`, so `lambda = E W ~ 2^h/n` and the
Poisson heuristic gives `P(W = 0) ~ e^{-lambda}`: at `n = 50`,
`exp(-1.3e6)`; at `n = 402`, `exp(-2^{193.4})`.

The Barbour--Holst--Janson form of Chen--Stein gives
`d_TV(W, Poi(lambda)) <= (b_1 + b_2) min(1, 1/lambda)` with
`b_1 = sum_i sum_{j in B_i} p_i p_j >= sum_i p_i^2 = 2^h/n^2`, so the best any
Stein bound can say is `d_TV <~ 2^h/(n^2 lambda) = 1/n`. And that is not slack:

> **Proposition 5 (the TV floor is real).** For independent indicators,
> `d_TV(Bin(m,p), Poi(mp)) = Theta(p)` once `mp` is large. So the true distance
> in the model is `Theta(1/n)`. No Stein bound can be smaller than the distance
> it estimates.

To conclude anything about **one named class among `2^ell`**, one needs
resolution `2^{-ell}`. The gap (`CHECK_STEIN_TV_FLOOR`):

```text
n      ell     lambda        TV floor    resolution needed   short by
50      24     2^{20.4}      2^{-5.6}    2^{-24}             2^{18.4}
402    200     2^{193.4}     2^{-8.7}    2^{-200}            2^{191.3}
2050  1024     2^{1015.0}    2^{-11.0}   2^{-1024}           2^{1013.0}
```

and short of `P(W = 0) ~ e^{-lambda}` itself by `exp(lambda)/n`, a doubly
exponential margin. **Poisson approximation quantifies the distribution; the
conjecture is a statement about the extreme lower tail, where the approximation
error exceeds the probability being approximated by `exp(lambda)/n`.** This is
an impossibility, not a difficulty: it holds for *any* Stein bound, present or
future.

One thing the Chen--Stein bookkeeping does say, and it is worth recording: the
`b_2` term is `sum_{i != j} E[X_i X_j] = ` the number of pairs of irreducibles
in the window, i.e. **the pair correlation of primes in a short interval of
`F_2[t]`** -- exactly the fixed-`q` input note 00 names as the wall and note 16
shows is unavailable at `p = 2`. Stein's method does not avoid the wall; it
renames it.

### 3.4 (iv) Extreme-value structure, and the identity's rank

`data/prob-order-statistics.txt`, 22 endpoints, exact integer order statistics
over all `2^ell` classes.

```text
 ell  n   V/SatoTate  max|D|/sd  sqrt(2 ell log2)  ratio  identity |z|  quantile   m3       m4
  12  25   0.97107      3.694        4.079         0.906     1.273       0.1965  -0.1331  3.1184
  16  33   1.00350      4.648        4.710         0.987     2.022       0.0429  +0.0074  3.0452
  17  36   1.01090      4.398        4.855         0.906     2.336       0.0194  +0.0097  2.9856
  18  38   0.99925      5.189        4.995         1.039     2.343       0.0195  +0.0068  3.0157
  19  40   0.99773      4.783        5.132         0.932     2.263       0.0236  +0.0043  2.9992
  21  43   0.99998      5.154        5.396         0.955     2.345       0.0191  -0.0037  3.0023
  22  45   0.99905      4.847        5.523         0.878     0.586       0.5580  +0.0021  3.0028
  22  46   0.99920      5.341        5.523         0.967     1.551       0.1208  +0.0024  2.9997
```

- **The ensemble is textbook.** Skewness in `[-0.133, +0.054]`, kurtosis in
  `[2.929, 3.184]` (Gaussian `0`, `3`); `max_g|D_g|/sd` is `0.758--1.188` times
  the Gumbel prediction `sqrt(2 ell log 2)` for `2^ell` Gaussians, mean `0.944`.
- **The identity is not.** Its quantile `rank/2^ell` (rank `1` = most extreme)
  has mean `0.3105` over 22 endpoints against the uniform `0.500`, low by
  `3.08` sigma; and it lands in the **top 5%** of classes at `6` endpoints
  against `1.10` expected, Poisson `p = 9.7e-4`.

> **This is the cleanest available refutation of "the identity behaves like a
> typical class".** Note 20 Prop. 7 uses that hypothesis to predict finitely
> many bad degrees; note 20 sec. 9.2 supports it with `rms z = 1.400`. But `rms
> z = 1.400` is itself the same signal: a typical class has `rms z = 1` by
> construction, and `1.400^2 = 1.96` says the identity carries twice the typical
> energy. The rank makes it non-parametric and assumption-free.

The excess is fully explained in section 4: it is the deterministic eighth-root
term, whose sign is a function of `n mod 8`.

**Verdict: no bound; but a new measurement that changes the heuristic.** The
order statistic is the right tool and it says the delocalisation hypothesis is
false as stated -- the identity is a `2`-to-`3` sigma class, not an average one.
That does not threaten the conjecture (the deviation is still `O(1)` sigma while
`2^{n-ell}/sd ~ 2^{(n-ell)/2}/sqrt(ell)` is needed), but it does mean the
"typical class" heuristic must be replaced by the atom-corrected one.

---

## 4. (C) The anti-correlation, explained

Note 20 sec. 9.2 measured, across the 23 groups `2 <= ell <= 24`, a Pearson
`r = -0.657` (Spearman `-0.617`, permutation `p = 2.6e-4`) between the two
degrees `n = 2ell+1` and `n = 2ell+2` that share `E_ell`, tried the first
Fourier coefficient `g_j(1)` of the angle multiset, found it two orders of
magnitude too small, and recorded the effect as unexplained.

### 4.1 It is not a normalisation artefact (exact)

`D_n = 2^{-ell} sum_{chi != 1}S_n(chi) = -2^{n/2-ell}G_ell(n)` and
`sd = 2^{(n-ell)/2} sqrt(ell - 2 + 2^{1-ell})`, so

```text
z_n  =  D_n / sd  =  - 2^{-ell/2} G_ell(n) / sqrt(ell - 2 + 2^{1-ell}).       (Z)
```

**The `n`-dependence cancels completely.** The prefactor depends on `ell`
alone, hence is *identical* for the two degrees of one group. Verified at all 46
endpoints to `8.3e-4` absolute (`CHECK_NORMALISATION_NOT_ARTEFACT`; the residue
is the rounding of the published `d_n` column to four digits). So

> **the `2^{ceil(n/2)}` vs `2^{n/2}` convention, and the `sqrt 2` it costs at
> odd `n`, cannot produce the correlation**: they are not in `z` at all. The
> mutation control M4 substitutes `2^{ceil(n/2)}` and kills exactly this check.

Consequently `corr(z_{2ell+1}, z_{2ell+2})` **is** the lag-1 autocorrelation of
`G_ell(n)`, and the question is entirely about the angle multiset.

### 4.2 It is not the proper-power/square mass (measured, exactly)

At even `n` the identity class carries a square term: `F = P^2` with
`deg P = n/2` and `<P>_{floor(ell/2)} = 1`, of exact Lambda-mass
`Theta^{(2)}_n(1) = N_{floor(ell/2)}(1)` at degree `n/2` -- which the embedded
engine computes exactly, reproducing all eleven of note 18 sec. 1.1's
independently flint-enumerated values (`37, 76, 45, 160, 79, 288, 301, 472, 562,
1099, 932`) and extending them to `ell = 19..24`
(`2096, 2101, 4159, 4302, 7840`, at `n = 40, 42, 44, 46, 48`), where note 18
records "not established (iv)". At odd `n`, `Theta_ell(1) = 1` (note 18 Lemma
P). Its size is `~ sd/sqrt(ell-2)`, a systematic `+0.2` to `+0.4` sigma push at
even `n` and nothing at odd `n`. Removing it exactly:

```text
20 groups, raw r = -0.6611   ->   proper-power-corrected r = -0.6215.
```

**The anti-correlation survives** (`CHECK_PROPER_POWER_NOT_ARTEFACT`).

### 4.3 The mechanism: squared multiplicities, and eighth-root angles

Treat `n` as the source of randomness. With `G(n) = sum_theta m_theta e(n theta)`
and `A_ell` closed under `theta -> -theta` with equal multiplicities,

```text
E_n[G(n)] = m_0,     E_n[G(n)G(n+k)] = sum_theta m_theta^2 cos(2 pi k theta),
rho_k  =  ( sum_theta m_theta^2 cos(2 pi k theta) - m_0^2 ) / ( sum_theta m_theta^2 - m_0^2 ).   (RHO)
```

*Proof.* In `sum_{theta,theta'} m m' e(n(theta+theta')) e(k theta')` only
`theta' = -theta` survives the average over `n`. QED

**The weight is `m^2`, not `m`.** That single point is why note 20's candidate
failed: `g_j(1) = sum_theta m_theta e(theta)` is the `m`-weighted object, and it
cancels among the many generic angles. The correlation is a variance-scale
quantity and therefore sees `m^2`, which is dominated by the few angles with
huge multiplicity. Mutation control M1 replaces `m^2` by `m` and kills exactly
`CHECK_ANTICORRELATION_MECHANISM`.

`(RHO)` is right to three decimals (`data/prob-anticorrelation.txt`; the
"empirical" column is an independent computation from the power sums, with no
angle extraction at all):

```text
ell   rho1_emp   rho1_pred    rho2_emp   rho2_pred   Sigma1^A   Sigma2^A   ratio   eighth_frac  max_mult
  8    -0.2803    -0.2833     -0.1944    -0.1931       1538       4278     2.78      0.487         25
  9    -0.3263    -0.3307     -0.1860    -0.1812       3586      16932     4.72      0.576         58
 10    -0.4191    -0.4166     -0.1139    -0.1114       8194      42234     5.15      0.669        108
 11    -0.4362    -0.4319     -0.1327    -0.1304      18434     187550    10.17      0.760        238
 12    -0.4366    -0.4289     -0.1635    -0.1611      40962     388626     9.49      0.778        340
 13    -0.4495    -0.4416     -0.1776    -0.1754      90114    1619822    17.98      0.848        716
```

Where the `m^2` mass sits (`ell = 13`, share of `Sigma_2^A`):

```text
theta   3/8     5/8     2/8     6/8     1/8     7/8   0, 4/8   outside (1/8)Z
share  0.3174  0.3174  0.0882  0.0882  0.0179  0.0179  0.0018     0.1512
cos    -.7071  -.7071  0.0000  0.0000  +.7071  +.7071
```

`theta = 3/8, 5/8` correspond to `alpha = sqrt2 e(+-3/8) = -(1 -+ i)` -- **the
two conductor-2 (Kerdock / `Z/4`) inverse roots of note 18 B2**, reproduced with
multiplicity `716` inside `E_13` and growing like `2^{0.94 ell}`. Their share
alone gives `-(0.317+0.317-0.018-0.018)/sqrt2 = -0.423` against the measured
`-0.4495`: the eighth-root atoms supply `94%` of `rho_1`
(`CHECK_EIGHTH_ROOT_MASS`). And `cos(4 pi * 3/8) = 0` while
`cos(4 pi * 2/8) = -1`, which is why `rho_2` is small and comes from the
quarter-angles instead -- predicted `-0.175`, measured `-0.178`.

The structural reason for the pile-up is the lane's own: the order-`4` layer is
supersingular (note 03 sec. 2, the Kerdock/`Z_4` row), so a positive proportion
of the inverse roots are `sqrt 2` times an eighth root of unity, *the same
finitely many values* for every conductor. Note 20 CHECK G saw the shadow of
this -- `2^{j-1}` characters realising only `252/488/994` distinct
`L`-polynomials at `j = 9,10,11`, max multiplicity `33/50/130`, and
`Sigma_2/Sigma_1 = 3.04/2.29/6.02` -- but read it as an obstacle to the large
sieve rather than as the mechanism.

### 4.4 The sharp form: a `mod 8` sign law for the identity class

Averaging `G_ell(n)` over `n` in a residue class mod `8` annihilates every angle
outside `(1/8)Z`, so

```text
P_ell(r) := lim_T (8/T) sum_{n <= T, n = r mod 8} G_ell(n)  =  sum_{s=0}^{7} m_{s/8} e(rs/8),
```

the deterministic eighth-root component of `G`. Measured for `4 <= ell <= 13`
(`data/prob-anticorrelation.txt`, columns `P0..P7`), the sign pattern is
**stable in `ell`**:

```text
r        0       1       2       3       4       5       6       7
sign  P  +       -       -       +       -       +       -       -
ell=13  +2615   -778    -618    +771    -887    +770    -614    -766
```

By `(Z)`, `sign z_n = -sign P_ell(n mod 8)`, i.e. `(-,+,+,-,+,-,+,+)` for
`n = 0..7 mod 8`.

> **Observation 6 (the `mod 8` sign law).** Over the 45 endpoints with
> `z != 0` (`2 <= ell <= 24`, both degrees), the predicted sign is correct at
> **42**. Binomial `p = 4.3e-10`. The three misses are the three smallest
> `|z|`: `(ell,n,z) = (10,21,+0.414)`, `(18,37,+0.320)`, `(20,42,-0.519)`.
> **Every endpoint with `|z| >= 0.6` obeys the law** -- the failures are exactly
> where the deterministic term is smallest against the fluctuation.

The extreme rows are exactly the ones the law predicts most strongly. Every
`ell = 3 mod 4` puts the even degree at `n = 0 mod 8`, where `P_ell(0)` is the
one large positive value: `z = -1.265, -0.789, -1.296, -1.403, -2.260, -3.328`
at `ell = 3,7,11,15,19,23` -- six of six negative and growing, and the last is
note 20's `max|z|`. Symmetrically every `ell = 1 mod 4` puts the even degree at
`n = 4 mod 8`: `z = +1.616, +0.401, +1.632, +2.349, +1.981`, five of five
positive.

### 4.5 The verdict, and why `-0.657` and `-0.44` are the same number

The sign law immediately gives the anti-correlation:

```text
ell mod 4:   0            1            2            3
(n odd, n even) mod 8:  (1,2)        (3,4)        (5,6)        (7,0)
predicted signs:        (+,+)        (-,+)        (-,+)        (+,-)
                        SAME       OPPOSITE     OPPOSITE     OPPOSITE
```

Three of four residue classes give opposite signs; with equal magnitudes that
alone is `r = -1/2`. The full `(RHO)` computation gives `-0.28` at `ell = 8`
rising to `-0.45` at `ell = 13` and (by the growth of `eighth_frac` toward
`-1/sqrt2`) tending to about `-0.5` from below.

Note 20's `r = -0.657` is a **sample** correlation from 23 single draws.
Fisher-`z` against the model value `-0.44`: `|dz|/se = 1.41` sigma, two-sided
`p = 0.16`. Consistent. Note 20's own consecutive-`ell` measurements
(`r = -0.066` odd, `-0.056` even) are also predicted: consecutive `ell` is lag
`2` in `n`, whose predicted value is `-0.13 .. -0.18`, further diluted because
the fresh top block `X_{ell+1}` contributes half the angles and shares nothing.

> **Verdict: the anti-correlation is real, not an artefact of normalisation or
> of proper powers, and it is a computable consequence of exact repeats of the
> two supersingular conductor-2 Frobenius angles across the whole character
> group.** Its ceiling is unchanged -- note 20 sec. 5 is right that even a
> perfect anti-correlation gives density `1/2`, not `o(1)` -- but it is no
> longer a mystery, and the object it exposes (a large deterministic,
> `8`-periodic component of `d_n`) is new.

---

## 5. What the sign law does and does not threaten

The eighth-root component of `d_n` is `-2^{-n/2} P_ell(n mod 8)`, with
`|P_ell| ~ 2^{0.93 ell}` (least squares over `8 <= ell <= 13`), so it
contributes `~2^{-0.07 ell}` to `d_n`. That decays, but far more slowly than the
Sato--Tate scale `sd/2^{n-ell} ~ 2^{-ell/2} sqrt(ell-2)`, at which the observed
`|z|` sits. Concretely, `|P_ell(0)| / sqrt(Sigma_1^A)` is `2.5` at `ell = 8`,
`6.1` at `ell = 11`, `8.7` at `ell = 13`: the atom term is already several times
the whole Sato--Tate scale and pulling away. Since the observed `|z|` stays
`O(1)`, the non-atomic part of `G_ell(n)` must cancel it, increasingly
precisely. That cancellation is present at every computed endpoint and is *not*
explained here (section 7). The honest statements are:

- the identity class has a **deterministic** deviation of known sign and known
  `8`-periodicity, of size `~2^{-0.07 ell}` relative to the mean;
- the conjecture needs `|d_n| < 1 - o(1)`, so the atom term is nowhere near
  threatening it at any computed `ell`, and its own decay is unconditional
  given the multiplicity growth;
- but the atom term is the reason the identity is a `2`-to-`3` sigma class
  rather than an average one, and it is the reason the two degrees of a group
  are anti-correlated.

---

## 6. (D) The random model, stated and calibrated

> **Model (IST).** For each `chi` of conductor `j`, the `j-1` Frobenius angles
> are independent and Sato--Tate/Haar distributed on the relevant compact group
> (`USp(j-1)` or `PU(j-1)` -- the choice does not affect anything below, which
> uses only `E|S_n(chi)|^2 = (j-1)2^n` and independence); angles of different
> characters are independent; the blocks `X_j` are independent across `j`.

Consequences. `E D_n = 0` and

```text
Var(D_n) = 2^{-2ell} sum_j 2^{j-1}(j-1) 2^n = 2^{n-ell}(ell-2) + 2^{n-2ell+1} = sd^2,
```

which is exactly note 20's `sd`. Gaussianity across the `2^ell` classes then
gives, for the identity,

```text
P(|D_n| >= 2^{n-ell})  <=  2 exp( - 2^{n-ell-1}/(ell-2) ),
```

summable with room to spare; and the cruder "the identity is a uniform random
class" version gives `P(1 in X_n) <= 4 ell^2 2^{-ell}`, also summable. **The
model predicts finitely many bad `n`, hence the conjecture for all large `n`.**
That is note 20 Prop. 7, and the point of this section is to say how much of it
survives contact with the data.

`data/prob-model-calibration.txt`:

```text
statistic                    model prediction         measured           verdict
2nd moment over classes      V = 2^{n-ell} D(ell)     1.0016 [.971,1.027]  CONFIRMED
3rd moment over classes      0 (Gaussian)             -0.005 [-.133,+.054] CONFIRMED
4th moment over classes      3 (Gaussian)             3.010 [2.929,3.184]  CONFIRMED
max over classes             sqrt(2 ell log 2)        0.944x [.758,1.188]  CONFIRMED
identity-class quantile      uniform on (0,1]         0.311 (3.08 sigma)   FAILS
identity in top 5%           1.10 of 22 endpoints     6                    FAILS
cross-character repeats      Sigma_2^A/Sigma_1^A = 1  17.98 at ell = 13    FAILS
block independence in j      corr(g_j,g_j') = 0       mean +0.452          FAILS
block variance additivity    Var(G) = sum_j Var(g_j)  2.321 at ell = 11    FAILS
consecutive-degree corr      0                        -0.449 (pred -0.442) FAILS
```

The pattern is sharp and worth stating as one sentence:

> **The model is right *within* a character and wrong *across* characters.**
> Within a character the angles are generic -- that is what
> `V/SatoTate = 1.00` and the Gaussian third and fourth moments measure, and it
> holds at fixed `q = 2` to three digits. Across characters there are massive
> exact coincidences: `Sigma_2^A/Sigma_1^A` grows like `2^{0.50 ell}`
> (`2.8, 4.7, 5.2, 10.2, 9.5, 18.0` at `ell = 8..13`), the blocks `g_j(n)` are
> positively correlated with mean `+0.452` and `max |r| = 0.745`, and
> `Var(G_ell) = 2.32 sum_j Var(g_j)` at `ell = 11`.

Three consequences for how the model should be used.

1. **The block-independence assumption in `(BLOCK)` is false.** Any heuristic
   that adds the variances of the `g_j` understates the aggregate variance by
   `2.3x` at `ell = 11` and by more later. The telescope itself is an identity
   and is unaffected; only the probabilistic reading of it is.
2. **The safety margin of Prop. 7 is much smaller than advertised, and still
   overwhelming.** Using the measured `Sigma_2^A ~ 2^{1.67 ell}` in place of
   the model's `Sigma_1^A`, the deviation needed at the Kaser--Lemire threshold
   is `0.34 * 2^{ell+1/2}/2^{0.835 ell} = 0.48 * 2^{0.165 ell}` standard
   deviations, so the Gaussian exponent falls from `2^{ell}/(2(ell-2))` to
   about `2^{0.33 ell}`. Summable either way -- `4.1e9` sigma at `ell = 200` --
   so the model's *conclusion* survives, but the exponent it survives on is a
   power of `2^{0.33 ell}`, not `2^{ell}`.
3. **"The identity is a typical class" should be replaced.** The correct
   heuristic is: `d_n` = a deterministic `8`-periodic atom term of size
   `~2^{-0.07 ell}` (sign known, Observation 6) plus a Sato--Tate-size
   fluctuation. Both are `o(1)`; the conjecture follows from the model exactly
   as before, but the *reason* it holds at any given `n` is not that the
   identity is average.

---

## 7. What this note does not do

- It proves no new case of Kaser--Lemire and no new rung of note 18's ladder.
  `(VAR)` is stated with a measured constant, not proved; section 2.6 says why
  Parseval cannot supply it.
- It does not explain the cancellation between the eighth-root atom term
  (`~2^{0.93 ell}`) and the rest of `G_ell(n)` at the endpoint degrees, which
  is what keeps `|d_n|` at Sato--Tate size. Whether that cancellation is
  structural or arithmetic accident is open, and it is the natural next
  question: a *lower* bound on the non-atomic part would be a genuinely new
  handle, and an upper bound on the residual would be `(HWO)`.
- The growth exponents (`Sigma_2^A ~ 2^{1.67 ell}`, `m_{3/8} ~ 2^{0.94 ell}`,
  `|P_ell(0)| ~ 2^{0.93 ell}`) are least-squares fits over `8 <= ell <= 13`
  only. The engine's cost is `2^{2ell-1}` and stops there; the CAS dumps reach
  `ell = 22` but give class populations, not angles. Treat the exponents as
  measurements with two significant digits, not as theorems.
- The sign law (Observation 6) is verified on 45 endpoints and its sign pattern
  on `4 <= ell <= 13`. It is not proved that the pattern is stable for all
  `ell`; that would follow from a lower bound on `m_{3/8}` relative to
  `m_{1/8}`, which is not attempted.
- Barrier II (symmetry) and Barrier III (construction) are untouched: nothing
  here is an argument about a group action or a construction.

---

## 8. Reproducibility

```sh
PY=/data0/axeyum/scratch/lemire-signed-trace-lemire-venv/bin/python
cd scripts/lemire-signed-trace
$PY lemire_probabilistic.py                    # 23 checks, ~7 s, nonzero on failure
$PY lemire_probabilistic.py --controls         # 8 mutation controls
$PY lemire_probabilistic.py --heavy            # live engine to ell = 13
$PY lemire_probabilistic.py --regenerate --scratch <dir> --ells 12-22
$PY lemire_probabilistic.py --regenerate-angles --heavy
$PY lemire_probabilistic.py --regenerate-calibration
```

`--regenerate` calls
`<snapshot>/target/release/axeyum-gf2-dump-populations <ell> <n> 1300000000`
(the third argument is **required**) and rebuilds `prob-variance-ladder.txt`,
`prob-order-statistics.txt`, `prob-martingale.txt` by exact integer arithmetic
on the dumps. `--regenerate-angles` uses only the embedded engine.
Snapshot path overridable with `AXEYUM_LEMIRE_SNAPSHOT`.

Mutation controls, each verified to kill exactly one named check:

| control | mutation | kills |
| --- | --- | --- |
| M1 | weight the angle multiset by `m` instead of `m^2` (note 20's rejected mechanism) | `CHECK_ANTICORRELATION_MECHANISM` |
| M2 | state `(VAR)` as a uniform-in-`j` saving over Weil instead of the Sato--Tate form | `CHECK_VARIANCE_CONJECTURE` |
| M3 | rotate the eighth-root sign pattern by one residue | `CHECK_SIGN_LAW` |
| M4 | use `2^{ceil(n/2)}` instead of `2^{n/2}` in the `z` identity | `CHECK_NORMALISATION_NOT_ARTEFACT` |
| M5 | drop the `-V` on the right of the sum rule | `CHECK_NEGATIVE_CORRELATION_SUM_RULE` |
| M6 | drop `kappa` from the martingale increment requirement | `CHECK_DOOB_INCREMENT_GAP` |
| M7 | flip the orientation of the identity's rank | `CHECK_IDENTITY_RANK` |
| M8 | skip the square-mass subtraction and the flint pins | `CHECK_PROPER_POWER_NOT_ARTEFACT` |

Anchors reproduced en route, by an engine independent of the branch CAS:
`N_5(1) = 45`, `N_7(1) = 472` (note 18); `D_n` exactly at all 20 endpoints
`2 <= ell <= 11` (note 20 CHECK A); `Theta_ell(1) = 37, 76, 45, 160, 79, 288,
301, 472, 562, 1099, 932` (note 18 C11); `V/SatoTate = 0.971, 1.004, 1.002`
at `(12,25), (16,33), (18,37)` (note 05 sec. 4); `Sigma_2` saturating Weil exactly
at every endpoint (note 05 sec. 4). Note 05's "`Sigma_3` sits at `0.25`" is
reproduced at `(12,25)` but is **not** universal: over the 22 endpoints
`Sigma_3/Weil_3` takes the five values `0.25` (7 rows), `0.375` (4), `0.625`
(8), `0.75` (2), `1.0` (1), so `C_3` runs over `[0.5, 2.0]` and that sentence
should be read as an instance, not a law.
