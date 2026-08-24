# 04 -- The tame-point weight: closed form, proof, and the theorem-candidate

Workstream 04 (NoH-p2). Date: 2026-08-20. Labels: **PROVED** (complete argument
written out here), **REFUTED (witness)**, **OPEN**.

Read in order before this file: `00-charter.md`, `10-notes-coordinator.md`
(Notes 5-7), `01-kmu-extraction.md`, `02-pulita-splitting.md` sec. 4,
`03-u2-truth.md`, `20-verify.md`.

Source fetched by me, not recalled: **KMU-I = arXiv:2110.08656v1**, Kramer-Miller
and Upton, *Newton Polygons of Sums on Curves I: Local-to-Global Theorems*
(`curl https://arxiv.org/pdf/2110.08656v1`, `pdftotext -layout`, 45 pp.). Every
KMU quotation below was re-read from that text; where my reading differs from
01's I say so.

---

## HEADLINE

**The lemma is proved.** The p = 2 tame-point estimate that KMU Remark 6.5 calls
"too low for applications to the global setting" is repaired, unconditionally,
by an elementary argument:

1. **THEOREM 1 (closed form).** The Type-2 transition coefficients are
   hypergeometric in closed form. With `p = 2`, odd tame index `e`, and
   `U_2(t^{-k}) = sum_j c_{k,j} t^{-j}`:
   - `k` even, `j = k/2 + e m`: `c_{k,j} = prod_{i=0}^{m-1}(k^2 - 4 e^2 i^2) / (e^{2m} (2m)!)`
   - `k` odd, `j = (k+e)/2 + e m`: `c_{k,j} = (k/e) prod_{i=0}^{m-1}(k^2 - e^2(2i+1)^2) / (e^{2m}(2m+1)!)`

   This is what 01 sec. 5 caveat (i) called missing ("a proof needs a closed form
   for `v_2(c_{k,j})`"). Verified by four independent routes.

2. **THEOREM 2 + LEMMA A (the tail estimate).** `v_2(c_{k,j'(k)+em}) >= m` for
   all `k >= 1, m >= 1`, with the refinement `>= m + s_2(m)` unless `k = 2 mod 4`.
   Elementary; three lines of 2-adic arithmetic from Theorem 1. This is
   20-verify sec. 3.3's "tail estimate, still open and still the hard part".

3. **THEOREM 3 (admissibility).** 20-verify's weight
   `a(k) = floor((k-1)/3) + (k mod 2)` (`a(k) = 0` for `k <= 3`) satisfies KMU's
   admissibility conditions **for all k**, with `d(k) >= 1` and `d(k) -> infinity`
   (`d(k) ~ k/6`). Proof: a three-case parity argument for the tail plus a
   six-case mod-6 identity for the leading term. Complete, below.

4. **THEOREM 4 (sharpness, exact).** `d(6) <= 1` for **every** admissible weight,
   because `k = 6` is a *self-loop* of the support map (`j'(6) + e = 6`) with
   `v_2(c_{6,1}) = 1`. Hence `max(1, gamma k)` is an achievable target **iff
   `gamma <= 1/6`**. This closes the interval 01 left at `[1/6, 1/5)` and
   20-verify sharpened to `[1/6, 2/11)`: the threshold is exactly `1/6`, and the
   witness is one coefficient.

5. **Global consumption: no other p = 2 obstruction inside KMU-I sec. 6-7.**
   Full lemma-by-lemma table in sec. 7. The strict-vs-non-strict audit the
   coordinator asked for comes out clean: the one strict inequality in the
   perturbation machinery (Def. 7.3(1)) is supplied by the margin `k/delta_P`,
   which is *p-independent*; and `d(k) >= 1` non-strict is *exactly* what
   Lemma 7.11 needs, because `I^{<r}` is defined by a strict `<`.
   The final Hodge polygon is the Kramer-Miller ramification-defined one
   (`g-1+|S|` slope-0 segments), unchanged: the `e_P`-dependence in
   `N = g-1+r_0+r_1+r_infty` cancels against Corollary 7.14's cancellation.

**Two residual gaps, both named and neither in the local estimate**: the
geometric input (Lemma B, sec. 8) and the sec. 6.2 exact sequence for a
non-eigenspace weight (sec. 7.3), the latter *asserted without proof in KMU for
their own weight* and here reduced to a bounded-difference comparison that costs
nothing for `r in [0,1]`, i.e. nothing for KMU Theorem 1.1.

---

## 0. Method and independence

Everything below is exact rational or integer arithmetic; no floating point
anywhere. The operator was **re-derived from KMU sec. 4.3 / 6.1.2, not copied
from 01**, and then checked against 01's ground truth.

Four independent routes to the coefficients `c_{k,j}`, all agreeing:

| route | what it is | file |
|---|---|---|
| R1 | triangular series solve in `x = 1/t` over `Fraction`, lowest-degree-first elimination | `op.py` |
| R2 | product/closed form (Theorem 1) | `closed.py` |
| R3 | sympy: `series`-based Puiseux expansion, different elimination, `sp.Rational` | `sym.py` |
| R4 | the hypergeometric ODE recurrence over exact `i128` rationals, in Rust | `noh_wt_certificate.rs` |

R1 reproduces 01 sec. 6b's ground truth *to the last digit*:
`U_2(t^-3) = t^-3`; `U_2(t^-6) = t^-3 + 2 t^-6`;
`U_2(t^-5) = (5/3)t^-4 + (40/81)t^-7 - (112/729)t^-10 + ...`;
`U_2(t^-4) = t^-2 + (8/9)t^-5 - (40/243)t^-8 + ...`;
`U_2(t^-7) = (7/3)t^-5 + (140/81)t^-8 - ...`;
`U_2(t^-8) = t^-4 + (32/9)t^-7 + (224/243)t^-10 - ...`.
R2 = R1 for `e = 1, 3, 5, 7` and `k <= 25`; R3 = R2 for `k <= 20, m <= 4`;
R4 = R2 for `k <= 40, m <= 10`.

**Self-checking artifact**: `crates/axeyum-cas/examples/noh_wt_certificate.rs`
(new). It asserts Theorems 1-4 and exits nonzero on any failure. Mutation-tested
both ways: replacing `a(k)` by `floor((k-1)/3)` makes it exit 1; adding 1 to the
valuation formula makes it exit 1; the unmodified file exits 0.

```sh
cargo run --release --example noh_wt_certificate -p axeyum-cas   # ~1 s
```

---

## 1. The operator, re-derived

At an auxiliary tame point `P` with `eta(P) = 1`, ramification index `e` (odd,
`e = p-1` at odd `p`, and `e = 3` the smallest admissible value at `p = 2`),
KMU sec. 4.3 gives `sigma(u_1) = (u_1+1)^p - 1` and `t^e = u_1`. At `p = 2`:

```
sigma(t)^e = sigma(u) = u^2 + 2u = t^{2e} + 2 t^e
  =>  sigma(t) = t^2 (1 + 2 x^e)^{1/e} = t^2 G,   x := 1/t,  G := (1+2x^e)^{1/e}.
```

`[E : sigma(E)] = 2`; the nontrivial conjugate of `t` over `sigma(E)` is
`t' = -sigma(t)/t` (check: `t'^e = -(t^{2e}+2t^e)/t^e = -(u+2)`, the other root
of `U^2 + 2U - sigma(u)`). Hence with `U_p = (1/p) sigma^{-1} o Tr`:

```
Tr(t^{-k}) = x^k (1 + (-1)^k G^{-k}),      sigma(t^{-j}) = x^{2j} G^{-j},
(1/2) Tr(t^{-k}) = sum_j c_{k,j} x^{2j} G^{-j}   ==>   U_2(t^{-k}) = sum_j c_{k,j} t^{-j}.
```

Support: `Tr(t^{-k})` lives in degrees `= k mod e`, `sigma(t^{-j})` in degrees
`= 2j mod e`, so `2j = k mod e`; among the admissible degrees only every other
one is even, so `j` runs over `j'(k) + e Z_{>=0}` with

> **`j'(k) = k/2` for `k` even, `j'(k) = (k+e)/2` for `k` odd.**

(For `e = 3` this is 01's "least `j >= ceil(k/2)` with `j = -k mod 3`": for `k`
odd, `j = (k+1)/2` never satisfies the congruence -- `2j = k+1 = k mod 3` fails
-- so the least admissible `j` is `(k+e)/2`, which does. **PROVED**, and it is
KMU Remark 6.5's `ell + r` with `k = 2 ell - r`.)

### THEOREM 1 (closed form). PROVED.

Put `v := 2 x^e`, `rho := (1+v)^{1/2} = e^{phi}`, and
`W := x^{2e}/(1+2x^e) = v^2/(4(1+v)) = sinh^2(phi)`. Note `W` does **not**
depend on `e`. Set `tau := phi/e`, so `W = sinh^2(e tau)` and
`(1+v)^{k/(2e)} = e^{k tau}`. Dividing the defining identity by
`x^{2 j'(k)} G^{-j'(k)}` and simplifying:

```
k even:  sum_{m>=0} c_{k, k/2 + e m}     W^m = cosh(k tau)
k odd :  sum_{m>=0} c_{k, (k+e)/2 + e m} W^m = sinh(k tau) / sinh(e tau)
```

Write `z := sinh(phi) = W^{1/2}` and `lambda := k/e`, so `k tau = lambda phi
= lambda arcsinh(z)`. Both `y = cosh(lambda arcsinh z)` and
`y = sinh(lambda arcsinh z)` satisfy

```
(1 + z^2) y'' + z y' - lambda^2 y = 0.
```

Writing `y = sum a_m z^{2m}` (even case) and `y = sum b_m z^{2m+1}` (odd case)
and reading off the coefficient of `z^{2m}`, resp. `z^{2m+1}`:

```
a_{m+1} = a_m (lambda^2 - 4m^2)      / ((2m+2)(2m+1)),   a_0 = 1
b_{m+1} = b_m (lambda^2 - (2m+1)^2)  / ((2m+3)(2m+2)),   b_0 = lambda
```

whence, with `lambda = k/e` and `sinh(lambda phi)/sinh(e tau) = y/z`,

> **`c_{k, k/2+em}     = prod_{i=0}^{m-1}(k^2 - 4 e^2 i^2)      / (e^{2m} (2m)!)`**
> **`c_{k, (k+e)/2+em} = (k/e) prod_{i=0}^{m-1}(k^2 - e^2(2i+1)^2) / (e^{2m} (2m+1)!)`**

Sanity: `3 | k` makes the product terminate (`cosh(n phi)` and
`sinh(n phi)/sinh(phi)` are Chebyshev polynomials in `W`), which is exactly why
`U_2(t^{-3}) = t^{-3}` and `U_2(t^{-6}) = t^{-3} + 2 t^{-6}` are finite.
Leading terms: `c_{k,j'(k)} = 1` (`k` even), `= k/e` (`k` odd) -- units at 2,
confirming 01's observation 3 that the estimate is sharp as stated.

---

## 2. The valuation, and LEMMA A

### THEOREM 2 (valuation identity). PROVED.

`e` is odd, hence a 2-adic unit, and drops out. Using
`v_2((2m)!) = 2m - s_2(m)` and `v_2((2m+1)!) = 2m - s_2(m)` (`s_2` = binary
digit sum; `s_2(2m) = s_2(m)`, `s_2(2m+1) = s_2(m)+1`):

> **`v_2(c_{k, j'(k)+em}) = Sigma_m(k) - 2m + s_2(m)`**, where
> `Sigma_m(k) = sum_{i=0}^{m-1} [ v_2(k - e xi_i) + v_2(k + e xi_i) ]`
> and `xi_i = 2i` (`k` even), `xi_i = 2i+1` (`k` odd).

Rewritten in the form used below, with `k = 2j` (even) and `k = 2j-e` (odd) --
i.e. indexing by `j = j'(k)`:

```
v_2(c_{2j,   m}) = sum_{i=0}^{m-1} v_2(j - e i) + sum_{i=0}^{m-1} v_2(j + e i) + s_2(m)
v_2(c_{2j-e, m}) = sum_{l=1}^{m}   v_2(j - e l) + sum_{i=0}^{m-1} v_2(j + e i) + s_2(m)
```

(Both from `k +- e xi_i = 2(j +- e i)` resp. `2(j - e(i+1))`, `2(j + e i)`.)
Verified against R1/R2/R4 for `k <= 40`, `m <= 10` and `k <= 600`, `m <= 80`.

### LEMMA A. PROVED.

> For all `k >= 1` and `m >= 1`, **`v_2(c_{k, j'(k)+em}) >= m`**. Moreover
> `v_2 >= m + s_2(m) >= m+1` when `k` is odd or `4 | k`; and
> `v_2 >= 3 floor(m/2) + s_2(m)` when `k = 2 mod 4`.

*Proof.* Take `e = 3` (any odd `e` works verbatim).

*Case `k` odd.* Then `k` and `e(2i+1)` are both odd, so `k^2` and
`e^2(2i+1)^2` are both `= 1 mod 8`, so `v_2(k^2 - e^2(2i+1)^2) >= 3`. Hence
`Sigma_m >= 3m` and `v_2 >= 3m - 2m + s_2(m) = m + s_2(m)`.

*Case `k` even.* Write `k = 2 kappa`. Then `k +- 2ei = 2(kappa +- ei)`, so
`Sigma_m = 2m + sum_{i<m} v_2(kappa^2 - e^2 i^2)` and
`v_2 = sum_{i=0}^{m-1} v_2(kappa^2 - e^2 i^2) + s_2(m)`.

 - `kappa` even (`4 | k`): for `i` odd, `kappa +- ei` is odd and the term is 0;
   for `i` even (including `i = 0`, term `2 v_2(kappa) >= 2`) both `kappa` and
   `ei` are even, so `v_2(kappa^2 - e^2 i^2) >= 2`. There are `ceil(m/2)` even
   `i` in `[0, m-1]`, so the sum is `>= 2 ceil(m/2) >= m`, giving
   `v_2 >= m + s_2(m)`.
 - `kappa` odd (`k = 2 mod 4`): for `i` even the term is 0 (`kappa +- ei` odd);
   for `i` odd both `kappa` and `ei` are odd, so as in the odd case
   `v_2(kappa^2 - e^2 i^2) >= 3`. There are `floor(m/2)` odd `i` in `[0,m-1]`,
   so `v_2 >= 3 floor(m/2) + s_2(m)`. For `m` even this is `>= 3m/2 >= m`; for
   `m` odd it is `>= 3(m-1)/2 + s_2(m) >= m` because `(m-3)/2 + s_2(m) >= 0`
   for every `m >= 1`. QED

Equality `v_2 = m` occurs only for `k = 2 mod 4, m = 1` (`v_2 = 2v_2(kappa)+1
= 1`); verified exhaustively for `k <= 600, m <= 80` (150 tight pairs, all of
that shape). **This is the tail estimate 20-verify sec. 3.3 left open.**

---

## 3. The admissibility conditions, restated from the source

KMU's construction at `eta(P) = 1` (sec. 6.1.2, 6.2, Cor. 6.8, Lemma 7.11). I
re-read each and state what the *weight* has to satisfy. `mu(P) = e_P` is the
truncation parameter -- KMU (11) and the glossary p. 42: *"if `eta(P)` in
`{0, infty}` we have `mu(P) = 0` and if `eta(P) = 1` we have `mu(P) = p-1`"*.
At `p = 2, e = 3` the corresponding value is `mu(P) = e = 3`.

With `A^{m,*}_{pi,P} := { sum_k b_k t_P^{-k} : v_pi(b_k) >= a(k)/m_P for k>0 }`:

- **(A1)** `a(k) = 0` for `k <= mu(P) = 3`. *Consumed by:* the sec. 6.2 exact
  sequence `0 -> Ltilde_pi -> Atilde^m_pi -> A^{m,tr}_pi -> 0`; `Ltilde_pi`'s
  local expansions have poles of order `<= mu(P)` only, and must lie in `A^m`.
- **(A2)** `a(k) = O(k)`. *Consumed by:* Cor. 6.7 (`union_m Vtilde^m = Vtilde^dagger`).
- **(A3)** `d(k) := min_{j in supp(k)} [ a(k) - a(j) + v_2(c_{k,j}) ] >= 1` for
  every `k > mu(P)`, and `d(k) -> infinity`. *Consumed by:* Lemma 7.11 (`d >= 1`)
  and Cor. 6.7 (divergence). See sec. 7 for the line-by-line.
- **(A4)** `a(k) >= d(k)`. *Consumed by:* the proof of Prop. 6.6(2) verbatim --
  *"The `pi`-adic valuation of the second term is at least `a(k)/m_P >= ell/m_P`"*.
- **(A5)** `d(k) >= 0` for `k <= mu(P)` (20-verify's addition). *Consumed by:*
  `Theta~`-stability of `A^{m,*}` in Cor. 6.8's integrality step.

The `1/m_P` calibration: `v_pi(c) = v_pi(p) v_2(c)` and `m_P >= m_{pi,P} =
1/v_pi(p)`, so `m_P v_pi(p) >= 1` and the `v_2` term enters with coefficient
`>= 1`. This is conservative **because `v_2(c_{k,j}) >= 0`** -- which is now a
consequence of Lemma A (`m >= 1`) plus `v_2(c_{k,j'(k)}) = 0` (`m = 0`), rather
than an assumption. Same calibration KMU use at odd `p`.

**Reduction.** Since the `m = 0` term of the min is `a(k) - a(j'(k))`, (A3) is
equivalent to the pair

> **(A3a)** `a(k) - a(j'(k)) >= 1` for `k > 3`, and `-> infinity`;
> **(A3b)** `a(j'(k) + e m) - a(j'(k)) <= v_2(c_{k,m}) + [a(k)-a(j'(k))] - 1` for `m >= 1`.

and (A3b) is implied by the cleaner **`a(j'(k)+em) - a(j'(k)) <= v_2(c_{k,m})`**,
which is what I prove.

---

## 4. THEOREM 3: the closed-form weight is admissible for all k. PROVED.

> **Weight.** `a(k) = 0` for `k <= 3`; `a(k) = floor((k-1)/3) + (k mod 2)` for
> `k >= 4`. (20-verify sec. 3.3's witness: KMU's own Remark 6.5 weight plus a
> parity indicator.)

**(A1)** holds by definition. **(A2)**: `a(k) <= (k+2)/3 = O(k)`. **(A5)**:
`a(k) = 0` for `k <= 3` gives `d(k) = 0` there, `>= 0`. **(A4)**: proved at the
end of this section.

### 4.1 The increment formula

For `n >= 4` and `m >= 1`, since `floor((n+3m-1)/3) = floor((n-1)/3) + m` and
`(n+3m) mod 2 = (n+m) mod 2`:

```
a(n+3m) - a(n) = m + [ ((n+m) mod 2) - (n mod 2) ]
               = m       if m is even
               = m + 1   if m is odd and n is even
               = m - 1   if m is odd and n is odd.
```

For `n = 2` the formula still holds (`a(2) = 0 = floor(1/3) + 0`). For `n = 3`
it does not (`a(3) = 0`, formula gives 1); `n = 3` is handled separately.

### 4.2 (A3b): the tail. PROVED.

Let `k > 3`, `j' = j'(k)`, `m >= 1`. We must show
`a(j' + 3m) - a(j') <= v_2(c_{k,m})`.

*Case `j' = 3`.* Then `k = 2j' = 6` (the odd alternative `k = 2j'-3 = 3` is
excluded by `k > mu = 3`). `c_{6,m} = 0` for `m >= 2` (Theorem 1: `3 | 6`
terminates the product at `m = 1`), so only `m = 1` is a constraint:
`a(6) - a(3) = 1 - 0 = 1` and `v_2(c_{6,1}) = v_2(2) = 1`. Equality. OK.

*Case `m` even.* Increment `= m`, and `v_2(c_{k,m}) >= m` by Lemma A. OK.

*Case `m` odd, `j'` odd.* Increment `= m - 1 < m <= v_2(c_{k,m})`. OK.

*Case `m` odd, `j'` even.* Increment `= m + 1`. The `k` with `j'(k) = j'` are
`k = 2j'` and `k = 2j'-3`. Since `j'` is even, `2j' = 0 mod 4`, and `2j'-3` is
odd. In **both** cases Lemma A's refinement applies:
`v_2(c_{k,m}) >= m + s_2(m) >= m + 1`. OK.

That is the whole proof of (A3b). QED

*(Why the parity indicator is exactly the right correction: the only place
Lemma A is tight is `k = 2 mod 4, m = 1`, i.e. `j' = k/2` **odd** -- and that is
precisely the case in which the parity indicator makes the increment go **down**
by one rather than up. The two tightnesses are complementary. That is not an
accident of the weight; it is why `floor((k-1)/3)` alone fails at `k = 5` and
`floor((k-1)/3) + (k mod 2)` does not.)*

### 4.3 (A3a): the leading term. PROVED.

Write `c := j'(k)`, so `k = 2c` (`k` even) or `k = 2c - 3` (`k` odd, `c >= 4`).
Put `c = 6q + r`, `0 <= r <= 5`. Using `floor((6q+s)/3) = 2q + floor(s/3)`:

*`k = 2c` even, `c >= 4`.* `a(2c) = floor((2c-1)/3) = 4q + floor((2r-1)/3)`
(note `2c` is even so the parity term vanishes), and
`a(c) = 2q + floor((r-1)/3) + (r mod 2)`. Hence
`d = 2q + floor((2r-1)/3) - floor((r-1)/3) - (r mod 2)`:

| `r` | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|---|
| `d` | `2q` | `2q-1` | `2q+1` | `2q` | `2q+1` | `2q+1` |

For `r in {0,1,3}` we need `q >= 1`, i.e. `c >= 6, 7, 9` respectively; the only
smaller values of `c` in those classes are `c = 3` (excluded, `c >= 4`) and
`c = 1` (excluded). For `r in {2,4,5}`, `d >= 1` for every `q >= 0`.
The remaining small cases `c = 2, 3` (i.e. `k = 4, 6`) use `a(c) = 0` by (A1):
`d(4) = a(4) - a(2) = 1` and `d(6) = a(6) - a(3) = 1`. So `d >= 1` throughout.

*`k = 2c - 3` odd, `c >= 4`.* `a(k) = floor((2c-4)/3) + 1 = 4q + floor((2r-4)/3) + 1`
and `a(c)` as above, so `d = 2q + floor((2r-4)/3) - floor((r-1)/3) - (r mod 2) + 1`:

| `r` | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|---|
| `d` | `2q` | `2q-1` | `2q+1` | `2q` | `2q+1` | `2q+1` |

Again `r in {0,1,3}` needs `q >= 1` (`c >= 6, 7, 9`), and the only `c >= 4` in
those classes with `q = 0` would be `c = 3` -- excluded. `c = 4, 5` fall in
`r = 4, 5` and give `d = 1`. So `d >= 1` throughout.

**Divergence.** In both tables `d >= 2q - 1 = 2 floor(c/6) - 1`, and
`c = j'(k) >= k/2`, so `d(k) >= 2 floor(k/12) - 1 -> infinity`; asymptotically
`d(k) ~ k/6`. QED

**(A4)** `a(k) >= d(k)`: `d(k) = a(k) - a(j'(k))` and `a >= 0`, so immediate.

### 4.4 Machine confirmation

Exact-rational sweep with the Theorem-2 valuations, `4 <= k <= 400`, full
computed support `m <= 250`: `d(k) >= 1` with **no violations**, the minimum is
attained at `m = 0` for **every** `k`, and

```
d(4..24) = 1,1,1,1,1,2,1,1,2,3,1,2,3,3,2,3,3,4,3,3,4
d(100) = 17   d(200) = 33   d(400) = 67
```

`d(4..24)` agrees with 20-verify's independently computed row. (Charge item 5
asked for `k <= 200`; this is `k <= 400`.)

---

## 5. THEOREM 4: sharpness. `gamma <= 1/6`, exactly. PROVED.

`j'(6) = 3` and `j'(6) + e = 6`: the index `k = 6` **occurs in its own support**.
The corresponding constraint in (A3) is

```
a(6) - a(6) + v_2(c_{6,1}) >= d(6),   i.e.   d(6) <= v_2(c_{6,1}) = v_2(2) = 1.
```

The weight cancels. So:

> **For every weight whatsoever, `d(6) <= 1`.** Consequently a target
> `d(k) >= max(1, gamma k)` is achievable **iff `gamma <= 1/6`**
> (`6 gamma <= 1`), and `d(k) >= max(1, k/6)` is achieved (sec. 6).

This *proves* what 01 measured as `max(1,k/5)` infeasible / `max(1,k/6)`
feasible and 20-verify sharpened to `[k/6, 2k/11)`: the threshold is the single
point `1/6`, `2/11 > 1/6` fails, and the certificate is one coefficient rather
than an LP. My own Bellman-Ford recomputation reports the infeasibility of
`max(1,k/5)` with witness edge `6 -> 6` -- the same self-loop.

Structural restatement (this is the real content of Remark 6.5): the descending
orbit of `succ = j'` has **exactly two attractors below `mu(P) = 3`**, the fixed
point `3` and the 2-cycle `{1,2}`; `k = 3` and `k = 6` sit on the fixed point.
`U_2(t^{-3}) = t^{-3}` is a genuine eigenvector of eigenvalue 1 -- which is why
`mu(P) = e_P` is not optional -- and `k = 6` is the first index above the
truncation that still sees it.

---

## 6. The extremal weight (secondary result; PROVED)

Independently of sec. 4, the *pointwise-minimal* weight for the maximal target
`d(k) >= max(1, k/6)` has a closed form. Define `succ(k) = k/2` (`k` even),
`(k+3)/2` (`k` odd), `d*(k) = 0` for `k <= 3` and `max(1, k/6)` for `k >= 4`, and

> **`a*(k) := sum_{i>=0} d*(succ^i(k))`** (the sum along the descending orbit)
> ` = (k - k_T)/3 + O(k)/2 + s(k_T)`,

where `k_T in {4,5,6}` is the first orbit element `<= 6`, `O(k)` is the number of
**odd** orbit elements strictly before it, and `s(4)=1, s(5)=2, s(6)=1`. This
reproduces 01's LP output exactly:
`a* = 0,0,0,1,2,1,19/6,7/3,5/2,11/3,5,3,9/2,11/2,5,5,13/2,11/2,49/6,7,...`,
`a*(48) = 15`, `a*(200) = 68`, `a*(k)/k -> 1/3`.

**MAIN LEMMA (PROVED).** For all `j >= 1, m >= 1`,
`a*(j+3m) - a*(j) <= R*(j,m)`, where
`R*(j,m) = sum_{i<m} v_2(j+3i) + sum_{i=1}^{m-1} v_2(j-3i) + min(v_2(j), v_2(j-3m)) + s_2(m)`
(convention `v_2(0) = +infinity`). By Theorem 2, `R*(j,m) = min` of
`v_2(c_{2j,m})` and `v_2(c_{2j-3,m})`, so the Main Lemma **is** (A3b) for `a*`.

*Proof.* Write `sigma := succ(j)`, `L(j,m) := a*(j+3m)-a*(j)`,
`Delta := d*(j+3m) - d*(j)`. Since `a*(x) = d*(x) + a*(succ x)` for **all**
`x >= 1`, and `succ(j+3m) = sigma + 3n` with

```
n = m/2      (m even, either parity of j)
n = (m+1)/2  (m odd, j even)
n = (m-1)/2  (m odd, j odd)
```

we get `L(j,m) = Delta + L(sigma, n)`. Splitting `sum_{i<m} v_2(j+3i)` and
`sum_{i=1}^{m-1} v_2(j-3i)` by the parity of `i` (odd terms in an arithmetic
progression of odd common difference contribute 0, even terms halve to the
progression at `sigma`), and using `s_2(2n) = s_2(n)`,
`s_2(2n+1) = s_2(n)+1`, `s_2(2n-1) = s_2(n) + v_2(n)`:

```
m = 2n         :  R*(j,m) >= 2n   + R*(sigma,n) = m + R*(sigma,n)
m = 2n-1, j even:  R*(j,m)  = 2n-1 + R*(sigma,n) + v_2(n) - min(v_2(sigma), v_2(sigma-3n))
                            >= m + R*(sigma,n)          [min(x,y) <= v_2(x-y) = v_2(3n)]
m = 2n+1, j odd :  R*(j,m)  = 2n+1 + R*(sigma,n) + v_2(sigma-3n) - min(...)
                            >= m + R*(sigma,n)
```

and the only analytic input is `Delta <= m`, which holds for every `j >= 1,
m >= 1` (`= m/2` for `j >= 6`; at most `m/2 + 5/6 <= m` for `j <= 5, m >= 2`;
`= 1` at `m = 1, j <= 3`). Induction on `m` closes every case except
`(j even, m = 1)`, where `n = m`; there `R*(j,1) = v_2(j)+1 = R*(sigma,1)+1`
and `Delta <= 1`, so induction on `j` closes it. QED

`s_2(2n-1) = s_2(n) + v_2(n)`: write `n = 2^w n'` with `n'` odd; then
`2n-1 = 2^{w+1}(n'-1) + (2^{w+1}-1)`, so `s_2(2n-1) = s_2(n'-1) + w + 1 =
s_2(n) + w`. (Machine-checked for `n <= 5000`.)

Machine confirmation: Main Lemma verified for `j < 400, m < 70` (min slack 0, at
`(j,m) = (1,1)`); (A3) for `a*` verified for `k <= 200`, `m < 200`, with
`d(k) = max(1, k/6)` **exactly** -- the tail is never binding.

**Why `a*` and not the sec. 4 weight for the headline**: `a*(k) - floor((k-1)/3)`
grows like `(1/2) log_2 k` (measured max `17/3` at `k = 2051` for `k <= 4000`),
whereas `a(k) - floor((k-1)/3) in {0,1}`. The bounded difference matters in
sec. 7.3. `a*` is kept because it attains the sharp constant of Theorem 4.

---

## 7. Global consumption: KMU-I sec. 6-7, lemma by lemma

Convention: **UNCHANGED** = the statement and its proof go through verbatim with
the new weight; **RESTATED** = the statement changes and the restatement is
given, with its proof; **BREAKS** = it does not go through.

| # | KMU-I item | mentions the weight? | verdict |
|---|---|---|---|
| 1 | Prop. 6.1 (wild, `eta(P) in {0,inf}`) | no (weight is `a(k)=k`) | **UNCHANGED**. Proof input is `Etilde_P in A^{p m_P}_{pi,P}`, no parity hypothesis. 03 measures the true optimum to be exactly this rate at `m = 1, 2`. |
| 2 | (17) `U_p(A^m) subset A^{m/p}` | no | **UNCHANGED** |
| 3 | Lemma 6.2 (`U_p(t^{-k}) in t^{-(ell+r)} B^m`) | eigenspace form | **RESTATED** by Theorem 1 + Lemma A. KMU cite [17, Cor. 4.7] for `R = Z_p, pi = p`; at `p = 2, e = 3` the closed form supersedes it and is proved here. |
| 4 | Def. 6.3 (`A^m = (+)_i t^{-i}B^m`, `a(k)=floor((k-1)/(p-1))`, formal basis) | yes | **RESTATED**: `A^{m,*}_{pi,P} := {sum b_k t^{-k} : v_pi(b_k) >= a(k)/m_P}` defined directly by the weight. Formal-basis property (Def. 3.7 = an isometric embedding into `b(I)` sending `e_i |-> e_i`) is immediate by construction. **Cost: the Galois eigenspace decomposition is no longer respected.** See sec. 7.2. |
| 5 | Prop. 6.4 (local estimate) | yes | **RESTATED**: `Theta~(pi^{a(k)/m_P} t^{-k}) in pi^{d(k)/m_P} A^{m,*}_{pi,P}` with `d(k) >= 1`, `d(k) ~ k/6` (Theorem 3). Proof input `Etilde_P in 1 + pi R_q` constant is unchanged and preserves `A^{m,*}` (it is a scalar unit). |
| 6 | Remark 6.5 | yes | **SUPERSEDED**. Its `d(5) = 0` was an artifact of `floor((k-1)/3)`; `floor((k-1)/3) + (k mod 2)` gives `d(5) = 1`. |
| 7 | sec. 6.2 exact sequence `0 -> Ltilde -> Atilde^m -> A^{m,tr} -> 0` | implicitly (via `A^m`) | **RESTATED, conditionally**. See sec. 7.3. Requires (A1) plus stability of `A^{m,*}` under the twist `a^{-1}`. Asserted without proof in KMU for their own weight (only Lemma 5.15, the `A^dagger` version, is proved). |
| 8 | sec. 6.2 basis `e^m_{P,k} = pi^{a(k)/m_P} e_{P,k}`, `k > mu(P)` | yes | **UNCHANGED** in form; `mu(P) = e_P = 3`. |
| 9 | Prop. 6.6(1) | no | **UNCHANGED** |
| 10 | Prop. 6.6(2) | yes | **RESTATED**: `Theta~(e^m_{P,k}) in pi^{d(k)/m_P} Vtilde^m_{pi,P}`. Proof inputs: Prop. 6.4, plus **(A4)** `a(k) >= d(k)` (proved, sec. 4), plus `Theta~(A^{m,*}) subset A^{m,*}` (from (A3): `a(k)-a(j)+m_P v_pi(p) v_2(c) >= d(k) >= 0`). |
| 11 | Cor. 6.7 (Fredholm series independent of `m`; tightness) | yes, via divergence | **UNCHANGED** given **(A2)** and `d(k) -> infinity` (proved). |
| 12 | Cor. 6.8 (Global Hodge Bound) | yes | **RESTATED** only in the `eta(P)=1` column slopes: they are `d(k) e >= e`, hence outside the `< e` truncation window, contributing **nothing** -- which is precisely the point. Integrality (`matrix has coefficients in R`) holds since `a(k)-a(j)+m_P v_pi(p) v_2(c) >= d(k) >= 1 > 0` on those columns. The stated slope multiset `{0,...,0}_r (+) (+)_{P in S} {k(p-1)/delta_P}` is **unchanged**. |
| 13 | Lemma 7.1, 7.2 (Newton-Hodge interaction) | no | **UNCHANGED**. The one strict inequality is definitional (`I^{<r}` uses a strict `<`), not consumed slack. |
| 14 | Def. 7.3 / Lemma 7.4 (perturbation) | no | **UNCHANGED**; see the strictness audit below. |
| 15 | sec. 7.2, Lemma 7.5, Def. 7.6/7.7, Prop. 7.9, Thm. 7.10 (local-to-global, `delta`-Hodge) | no | **UNCHANGED**. Purely wild-point + Dwork trace formula + Liu-Wei; no parity hypothesis, and 03 confirms the wild profile is the odd-`p` one. |
| 16 | Lemma 7.11 (`Psi'` is an `e`-perturbation of `Psi`) | **yes, decisively** | **UNCHANGED given (A3)**. This is the unique consumer of `d(k) >= 1`; see below. |
| 17 | Lemma 7.12 (Deuring-Shafarevich: `N` slope-0 segments) | via `N` | **UNCHANGED in form**, but `N = g-1+r_0+r_1+r_infty` now uses `r_1 = deg(eta)/3`. See sec. 7.4. |
| 18 | Thm. 7.13, Cor. 7.14, Cor. 7.15 (= Thm 1.1) | via `N` | **UNCHANGED**; the `e_P` dependence cancels (sec. 7.4). |

### 7.1 The strict-vs-non-strict slack audit (coordinator's addition 1)

03 warns that at `p = 2` the wild-point optimum has zero *multiplicative* slack
(odd `p` has a factor `p-1`), so any step consuming strict slack is a candidate
`p = 2` obstruction. I enumerated every strict inequality in sec. 6-7:

| where | strict? | what supplies it | `p = 2` verdict |
|---|---|---|---|
| Def. 6.3's `B^m`: `v_pi(b_k) > k/m_P` | **strict in the source** | -- | **Source infelicity, not load-bearing.** With a strict `>`, `pi^{a(k)/m_P}t^{-k}` is *not* in `A^m` and the "formal basis" claim of Def. 6.3 is literally false. KMU's own sec. 2.1 defines `A^m(b)` with `>=`. I adopt `>=` throughout; nothing downstream sees the difference (every estimate is proved coefficientwise). |
| Lemma 7.1: *"the inequality is strict for `k = n`, since `e_{j_n}` is not in `I^{<r}`"* | strict | the **definition** of `I^{<r}(Psi) = {i : v_pi psi(e_i) < r}` | **Self-supplying.** Nothing is consumed. Crucially: a column of slope *exactly* `r` is outside `I^{<r}`. |
| Def. 7.3(1): `v_pi(eps(e_i)) > v_pi(Psi(e_i))` on `I^{<r}` | **strict** | Lemma 7.11: `v_pi(eps(e^{m_e}_{P,k})) >= kp/delta_P` while `v_pi(Theta~(e^{m_e}_{P,k})) = k(p-1)/delta_P`; margin `k/delta_P > 0` | **HOLDS at `p = 2`.** The margin is `[kp - k(p-1)]/delta_P = k/delta_P`, which is **independent of `p`**. The `(p-1)` that vanishes at `p = 2` is *not* the source of this strictness. |
| Def. 7.3(2): `v_pi(eps(e_i)) >= r` off `I^{<r}` | **non-strict** | for `eta(P) = 1` columns: `v_pi(Theta~(e^{m_e}_{P,k})) >= d(k)/m_{e,P} = d(k) e >= e = r` | **HOLDS with `d(k) >= 1` non-strict.** This is the exact point of consumption. `d(k) >= 1` is *precisely* enough; no epsilon is needed, because `I^{<r}` is a strict `<` and slope `= r` is already excluded. |
| Lemma 7.4's `v_pi(eps_n) > sum v_pi Psi(e_i)` | strict | inherited from Def. 7.3(1) by induction on exterior powers | **UNCHANGED** |
| (19) `HP_pi(Theta~|V^{m_e,tr}) >= HP(delta_P)^{x v_p(q)}` | non-strict | Prop. 6.1 | **UNCHANGED**; equality is then *forced* in Thm. 7.10 by a degree count (`deg L(rho^ext_P,s) = d_P - 1`), not by slack. |

**Verdict: no step in sec. 6-7 consumes multiplicative slack that vanishes at
`p = 2`.** The only additive tightness is `d(6) = 1`, which is exactly at the
threshold and exactly sufficient.

### 7.2 The eigenspace form (risk R3): determined

The coordinator asks whether `a(k) = floor((k-1)/3) + (k mod 2)` can be realised
as an eigenspace regrading. **It cannot.** The `Gal(E/E_0) = Z/e` eigenspace
decomposition `A_{pi,P} = (+)_{i} t^{-i} R_q((u))`, `u = t^e`, gives weights that
are *affine on each residue class mod `e = 3`*, even if one allows a separate
shift `b_i` per eigenspace: `a(i + 3s) = s - b_i`. The parity indicator has
period 2, so `a` is affine on each class **mod 6**, not mod 3, and `mod 6` is
not a coarsening of `mod 3`. Concretely `a(1),a(4),a(7),a(10) = 0,1,3,3` is not
arithmetic.

A mod-6 splitting `A_{pi,P} = (+)_{r=0}^{5} t^{-r} R_q((t^6))` exists as an
`R_q((t^6))`-module decomposition, but it is **not `sigma`-equivariant**:
`sigma(t^6) = (t^6)^2 (1 + 2 t^{-3})^2` and `(1+2x^3)^2 = 1 + 4x^3 + 4x^6` has an
`x^3` term, so `sigma(R_q((t^6)))` is not inside `R_q((t^6))`. (The mod-3 one is
equivariant: `sigma(u) = u^2 + 2u`.)

**Therefore R3 does not dissolve: the exact-sequence lemma for a non-eigenspace
weight is a required lemma.** It is stated and discharged (conditionally) next.
Note that KMU use the eigenspace form for exactly two things -- defining `A^m`
and proving Lemma 6.2 -- and both are replaced here by Theorem 1, which is
basis-free.

### 7.3 The required lemma: sec. 6.2's exact sequence

> **LEMMA E (required).** With `A^{m,*}_pi` the product of the local growth
> modules above, `Atilde^{m,*}_pi = A^{m,*}_pi cap Atilde^dagger_pi` and
> `A^{m,*,tr}_pi = A^{m,*}_pi cap A^{dagger,tr}_pi`, the sequence
> `0 -> Ltilde_pi -> Atilde^{m,*}_pi -> A^{m,*,tr}_pi -> 0` is exact.

What (A1) buys, unconditionally: `L_pi = ker(pr)` consists of functions with
poles of order `<= mu(P) = 3` at the points over 1 and no poles elsewhere; since
`a(k) = 0` for `k <= 3` and the coefficients lie in `R_q`, `L_pi subset A^{m,*}_pi`
for every `m`. Likewise, lifting `x in A^{m,*,tr}_pi` through `pr` only adds
coefficients in degrees `<= mu(P)`, which the growth condition does not
constrain. So **the truncation bookkeeping is insensitive to the weight above
`mu(P)`, and (A1) is exactly the hypothesis that makes it work.**

What is *not* automatic: `Ltilde_pi = a^{-1} L_pi` rather than `L_pi`, where
`a in 1 + pi A_pi` is Prop. 5.11's twist, and `A^{m,*}_{pi,P}` is **not a ring**
(no weight satisfying (A1) can make it one: subadditivity plus `a(3) = 0` would
force `a(k+3) <= a(k)`). **KMU have the identical problem with their own weight,
and assert the sequence without proof** (Lemma 5.15 proves only the `A^dagger`
version, by reduction mod `pi`).

Two honest statements:

- **Rate equivalence.** `a(k) - floor((k-1)/3) in {0,1}` -- a *bounded*
  difference. Hence
  `pi^{1/m_P} A^m_{pi,P}(KMU) subset A^{m,*}_{pi,P} subset A^m_{pi,P}(KMU)`.
  Writing `a^{-1} = 1 + pi y`, the extra term carries a factor `pi`; if
  `m_P >= 1` that factor absorbs the extra `1/m_P` of penalty, and Lemma E for
  `a` follows from KMU's assertion for `floor((k-1)/3)`.
  In Cor. 6.8 `m_{e,P} = 1/e`, so `m_P >= 1` means `e <= 1`; and Thm. 7.13's
  proof needs `r <= e`. **So capping `e <= min(1, v_pi(p))` makes Lemma E
  conditional only on KMU's own assertion, at the cost of restricting the
  general Thm. 7.13 to `r <= 1`.** KMU **Theorem 1.1 takes `r in [0,1]`, so it
  is untouched.**
- Using the sec. 6 extremal weight `a*` instead would cost a factor
  `C_0 = sup_k a*(k)/floor((k-1)/3) = 2` (attained at `k = 5`, where
  `a(5) >= 2` is forced for *any* admissible weight) and hence
  `e <= v_pi(p)/2` -- strictly worse. This is the concrete reason to take
  20-verify's weight as the headline rather than the LP-extremal one.

**Status of Lemma E: OPEN in KMU (asserted, not proved) for every `p`; reduced
here to that same assertion, with no `p = 2`-specific loss and no loss at all
for `r in [0,1]`.** It is *not* a new obstruction created by dropping the
eigenspace form; it is a pre-existing gap of the source.

### 7.4 Exterior-power / determinant bookkeeping and the Hodge polygon identity

- **Exterior powers.** Lemma 7.4's induction
  `eps_{k+1}(e_{i_1..i_{k+1}}) = (wedge^k Psi) wedge eps(e_{i_{k+1}}) + eps_k wedge Psi'(e_{i_{k+1}})`
  and Lemma 7.1's minor bound `v_pi(J x J minor) >= v_pi det(Psi^{<r})` involve
  the weight only through the column valuations `v_pi(Psi(e_i))`. With the new
  weight the `eta(P) = 1` columns all have valuation `>= e`, so they lie outside
  `I^{<r}` for `r <= e` and enter **no** minor of `Psi^{<r}`. **UNCHANGED.**
- **Determinant / vertex loss.** Because the `eta(P)=1` columns are entirely
  outside the truncation window, they contribute neither a vertex nor a segment
  to `NP^{<r}` or `cHP^{<r}`. **The new weight introduces no constant and no
  vertex loss.** (With KMU's Remark 6.5 weight, `d(5) = 0` would have put one
  column at slope 0 inside the window -- an extra slope-0 segment, which
  Lemma 7.12 then miscounts. That is precisely why `d = 0` is *fatal* and not
  merely lossy: Lemma 7.12 pins the number of slope-0 segments at `N` via
  Deuring-Shafarevich, and Cor. 7.14 cancels exactly `r_0+r_1+r_infty-|S|` of
  them. One extra breaks the count, not a bound.)
- **The final polygon is the KM one.** With `e_P = 3` the Riemann-Hurwitz
  bookkeeping changes but cancels. KMU (8) is
  `2(g-1) + r_0 + r_1 + r_infty = deg(eta)` (I re-derived it: for a tame map
  branched only over `{0,1,infty}`, `2g-2 = -2 deg + sum_Q (deg - r_Q)`), and
  `r_1 e_P = deg(eta)`, so `e_P = 3` gives `r_1 = deg(eta)/3`.
  `D = sum_{eta(P)=1} mu(P) P` has `deg D = 3 r_1 = deg(eta)`, so Riemann-Roch
  gives `N = h^0(D) = deg(eta) + 1 - g = g - 1 + r_0 + r_1 + r_infty`, KMU (13),
  **unchanged in form.** Cor. 7.14 then cancels `r_0+r_1+r_infty-|S|` slope-0
  segments, leaving `N - (r_0+r_1+r_infty-|S|) = g - 1 + |S|` -- **exactly the
  Kramer-Miller ramification-defined count of sec. 1.2**, independent of `e_P`.
  So the target polygon is the KM one and not a weakened variant. **PROVED.**

---

## 8. LEMMA B: the geometric input (20-verify's gap, and the charge's item)

20-verify sec. 1.3 is right that 01's "the `p >= 3` hypothesis sits only in
6.1.2" understates it: KMU sec. 4.1 also uses `p >= 3`, twice -- Fulton's
theorem (Thm. 4.1) and the `(p-1)`-power map inside `eta_q`, which at `p = 2`
degenerates to the identity.

> **LEMMA B (stated; proof conditional).** Let `X` be a smooth affine curve over
> `F_q`, `q = 2^a`, with `S = Xbar \ X`. Then there is a tame Belyi map
> `eta : X -> P^1_{F_q}` (possibly after a finite extension of `F_q`) such that
> (1) `eta(P) = 0` for every `P in S`; (2) every point of `X` over `1` has
> ramification index exactly `3`.

*What is in hand.* KMU Remark 4.2, verbatim: *"In [23], Sugiyama and Yasuda
extend Fulton's result to the case `p = 2`. We have omitted this case for other
reasons (see Remark 6.5). By a recent theorem of Kedlaya-Litt-Witaszek, `eta`
exists even without extending the base field [13]."* -- so the authors regard
the char-2 tame map `eta_0` as available. Given `eta_0`, KMU's `eta_q` is
`P^1 --(q-1)--> P^1 --linear--> P^1 --(p-1)--> P^1 --linear--> P^1`. Replace the
`(p-1)`-power map by the **3-power map**. It is tame at `p = 2`
(`gcd(3,2) = 1`), it is ramified only over `0` and `infty` with index 3, and the
final linear map (fixing `infty`, swapping `0` and `1`) carries the index-3
ramification point onto `1`. The `(q-1)`-power map is tame (`q-1` odd). Hence
`eta = eta_q o eta_0` is a tame Belyi map with `eta(S) = {0}` and `e_P = 3` over
`1`, and `r_1 * 3 = deg(eta)`.

*What I did not do.* I did not fetch Sugiyama-Yasuda (Compositio 156 (2020)
325-339) or Kedlaya-Litt-Witaszek and verify their statements at source. So
Lemma B is **conditional on KMU Remark 4.2's own citation**, and the 3-power
modification is mine and elementary. Note also 20-verify's correction: "Riemann-
Hurwitz forbids `e_P = 1`" needs a genus qualifier -- with `e_P = 1` one gets
`2(g-1) + r_0 + r_infty = 0`, impossible for `g >= 1` but not for `g = 0`. Theorems 1, 2 and Lemma A are proved for **every odd `e`**; Theorem 4
generalises to a self-loop at `k = 2e` with threshold `gamma <= 1/(2e)`. Only
Theorem 3's mod-6 case analysis is specific to `e = 3`, which is the smallest
admissible index and the one Remark 6.5 uses.

---

## 9. THEOREM-CANDIDATE

> **THEOREM-CANDIDATE (Newton-over-Hodge at `p = 2`, arbitrary curve).**
> Let `q = 2^a`, let `X` be a smooth affine curve over `F_q` with smooth
> compactification `Xbar`, genus `g`, and `S = Xbar \ X`. Let
> `rho : pi_1(X) -> C^x` be a finite character of order `2^n`, `d_P` its Swan
> conductor at `P in S`, `delta_P = d_P / 2^{n-1}`, and let `pi` be a
> uniformizer of `Z_2[rho]`. Assume Lemma B (sec. 8) and that `X` is ordinary.
> Then for every `r in [0,1]`:
>
> `HP_q^{<r}(rho)` and `NP_q^{<r}(rho)` have the same terminal point **iff**
> `HP_q^{<r}(rho_P^ext)` and `NP_q^{<r}(rho_P^ext)` have the same terminal
> point for every `P in S`,
>
> where `HP_q(rho)` is the Kramer-Miller ramification-defined Hodge polygon:
> `g-1+|S|` slopes 0, `g-1+|S|` slopes 1, and `{1/d_P, ..., (d_P-1)/d_P}` for
> each `P in S`. I.e. **KMU-I Theorem 1.1 holds at `p = 2`.**

**Proof skeleton.**

| step | source | status |
|---|---|---|
| sec. 2-3 functional analysis (Fredholm/Newton/Hodge/column-Hodge, Lemmas 3.10, 3.20, 3.24, Prop. 3.13) | KMU-I verbatim | cite |
| geometry: tame Belyi `eta` with `eta(S)={0}`, `e_P = 3` over 1; `mu(P) = 3`; `N = g-1+r_0+r_1+r_infty`; RH (8), (13) | KMU-I Thm. 4.1, Prop. 4.3, Prop. 4.10, **modified** | **Lemma B** (sec. 8), conditional on KMU Rem. 4.2's citation; the bookkeeping re-derived in sec. 7.4 |
| global lifting `(A^dagger, sigma)`, `U_p`, semi-local decomposition | KMU-I sec. 4.2-4.4 verbatim | cite |
| `sigma`-modules, `delta`-overconvergence, `Etilde_P` (KM-ab Prop. 5.5), semi-local twist, Lemma 5.15 | KMU-I sec. 5 verbatim; **no parity hypothesis** (02 sec. 3.3, 03 sec. 5, both confirm) | cite |
| wild local estimate, Prop. 6.1 | KMU-I verbatim | cite |
| **tame local estimate at `eta(P)=1`** | **NEW** | **Theorems 1, 2, Lemma A, Theorem 3** (this file, sec. 1-4). Replaces Def. 6.3 / Lemma 6.2 / Prop. 6.4 / Remark 6.5. |
| sec. 6.2 exact sequence | KMU-I asserted | **Lemma E** (sec. 7.3): holds for `e <= min(1, v_pi(p))` given KMU's own assertion. Covers `r in [0,1]`. |
| Prop. 6.6, Cor. 6.7, Cor. 6.8 | KMU-I, **restated** | sec. 7 table rows 9-12; inputs (A2), (A3), (A4) all proved |
| sec. 7.1 perturbation theory (Lemmas 7.1, 7.2, 7.4) | KMU-I verbatim | cite; strictness audit sec. 7.1 |
| sec. 7.2 local-to-global, Thm. 7.10 (`delta`-Hodge) | KMU-I verbatim | cite |
| Lemma 7.11 (`Psi'` is an `e`-perturbation) | KMU-I verbatim **given (A3)** | the unique consumer of `d(k) >= 1`; sec. 7.1 |
| Lemma 7.12, Thm. 7.13, Cor. 7.14, Cor. 7.15 | KMU-I verbatim | `e_P`-dependence cancels, sec. 7.4 |

**Labelled: THEOREM-CANDIDATE, pending adversarial verification.** The parts I
claim as *proved here* are Theorems 1-4 and the Main Lemma; everything else is
either cited verbatim or restated with the restatement proved, except the two
named conditionals (Lemma B, Lemma E).

**Not claimed.** The unconditional inequality `NP_q(rho) >= HP_q(rho)` for
arbitrary curves is Kramer-Miller [16] = arXiv:2006.04936, a *different* paper
with its own global sections. Its local input is the same sec.-4 estimate
(KM-exp sec. 1.4: *"some estimates in section 4 must be modified"*), so
Theorems 1-4 are the corresponding repair there too -- **but I audited KMU-I
sec. 6-7 only, and I did not read KM 2006.04936's global sections.** That audit
is the obvious next task and is an explicit gap in this deliverable.

---

## 10. Reconciliation with the other workstreams

| claim | source | my verdict |
|---|---|---|
| `j'(k)` = least `j >= ceil(k/2)` with `j = -k mod 3`; `= ell+r` | 01 sec. 4, 20 sec. 2.3 | **CONFIRMED**, and proved in closed form: `k/2` (`k` even), `(k+3)/2` (`k` odd), for every odd `e`. |
| ground-truth rows for `U_2(t^{-k})` | 01 sec. 6b | **CONFIRMED** to the last digit by three independent routes. |
| `v_2(c_{k,j'(k)}) = 0` (estimate sharp as stated) | 01 sec. 4 | **CONFIRMED and proved**: the leading coefficient is `1` or `k/e`. |
| `max(1,k/6)` feasible, `max(1,k/5)` infeasible | 01 sec. 5 | **CONFIRMED** by my own Bellman-Ford, and **PROVED**: threshold is exactly `1/6`. |
| threshold in `[k/6, 2k/11)` | 20 sec. 3.2 | **SHARPENED to the single point `1/6`**; `2/11 > 1/6` fails by the `k=6` self-loop. |
| 01's LP-minimal weight `0,0,0,1,2,1,19/6,7/3,...,a(48)=15` | 01 sec. 5 | **REPRODUCED EXACTLY**, independently; and given a closed form (sec. 6). |
| "none of the obvious closed-form weights work" | 01 sec. 5 caveat (i) | **REFUTED**, as 20 found; and 20's witness is now **proved admissible for all `k`**. |
| coordinator's guess `v_2(c_{k,j}) = m + v_2(binom(-k/3,m))` | Note 7 (message) | **REFUTED (witness)**: correct for `k = 4` (`0,3,3`) but wrong for `k = 5` (predicts `1` at `m=1`, truth is `3`). The correct formula is Theorem 2. |
| coordinator's `m = 2|j-k|/3` | Note 7 | **REFUTED (witness)**: not an integer (`k=4, j=5` gives `2/3`). The right index is `m = (j - j'(k))/e`. |
| "the LP-minimal weight IS the shortest-path potential from `k <= 3`" | Note 7 | **CONFIRMED**, and identified in closed form: it is the sum of `max(1,k/6)` along the `succ`-orbit (sec. 6). |
| "don't hunt for a pretty closed form of `a(k)`" | Note 7 | **PARTLY REFUTED**: two closed forms exist -- 20's `floor((k-1)/3)+(k mod 2)` (which is what the proof should use) and the orbit-sum `a*` (which attains the sharp constant). |
| `p >= 3` is consumed in sec. 4.1 as well as 6.1.2 | 20 sec. 1.3 | **CONFIRMED**; addressed as Lemma B. |
| the exact requirement localizes to Lemma 7.11, with 7.12 explaining fatality | 20 sec. 2.5 / coordinator | **CONFIRMED**; sec. 7.1 and 7.4 above. |
| wild-point local analysis needs nothing new at `p = 2` | 02, 03 | **CONFIRMED** against KMU-I Prop. 6.1's proof, which uses only `Etilde_P in A^{p m_P}` and carries no parity hypothesis. |

---

## 11. Epistemic status

- **PROVED** (complete arguments in this file, plus exact machine verification):
  the closed form for `c_{k,j}` (Theorem 1, all odd `e`); the valuation identity
  (Theorem 2); Lemma A; the admissibility of
  `a(k) = floor((k-1)/3) + (k mod 2)` for all `k` with `d(k) >= 1`,
  `d(k) ~ k/6` (Theorem 3); the sharpness `gamma <= 1/6` (Theorem 4); the Main
  Lemma and the closed form for the extremal weight (sec. 6); the `e_P`-
  cancellation in the global count (sec. 7.4); `s_2(2n-1) = s_2(n)+v_2(n)`.
- **REFUTED (witness)**: the coordinator's Note-7 cost formula; the possibility
  of an eigenspace regrading realising the parity indicator (sec. 7.2);
  `d(k) >= max(1, 2k/11)`.
- **OPEN / conditional**: Lemma B (geometry -- conditional on KMU Rem. 4.2's own
  citation, which I did not fetch); Lemma E (sec. 6.2's exact sequence -- open in
  KMU for their own weight, reduced here to that same assertion with no loss for
  `r in [0,1]`); the parallel audit of KM arXiv:2006.04936's global sections,
  which is what an unconditional `NP >= HP` at `p = 2` needs.
- **NOT DONE**: I did not verify KM-ab Prop. 5.5, Liu-Wei, Deuring-Shafarevich,
  Katz-Gabber, Elkik, or the sec. 2-3 functional analysis at source; those are
  cited as KMU cite them.

---

## 12. Reproduction

```sh
cargo run --release --example noh_wt_certificate -p axeyum-cas   # ~1 s, self-checking
```

Asserts Theorems 1-4 and exits **nonzero** on any failure; mutation-tested (see
sec. 0). Session-scratchpad scripts (not committed): `op.py` (from-scratch series
solve), `closed.py` (closed form + valuation identity, cross-checked against
`op.py` for `e = 1,3,5,7`), `sym.py` (independent sympy route), `lp.py`
(Bellman-Ford feasibility over `Fraction`), `astar.py` (orbit-sum weight),
`mainlemma.py` (Main Lemma + identities), `a20.py` (Theorem 3 sweep to
`k <= 400`, `m <= 250`).
