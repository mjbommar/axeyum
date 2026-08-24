# 20 -- Adversarial verification of the NoH-p2 extraction diaries

Workstream 20 (NoH-p2), the adversarial verifier. Date: 2026-08-20.
Targets: `01-kmu-extraction.md`, `02-pulita-splitting.md`, and coordinator
Notes 1-6 in `10-notes-coordinator.md`. `04-weight-proof.md` had NOT landed at
the time of writing (directory checked twice, at start and at end), so the
priority-0 audit of its new lemma is not in this document.

Sources fetched by me, this session, never recalled (curl + pdftotext -layout,
session scratchpad `ws20/`, md5s recorded there):

- KMU-I = arXiv:2110.08656, *Newton Polygons of Sums on Curves I*.
- KM-exp = arXiv:1909.06905, *p-adic estimates of exponential sums on curves*.
- KM-ab = arXiv:2006.04936, *p-adic estimates of abelian Artin L-functions*.
- Pulita = arXiv:math/0612725v2, *Rank One Solvable p-adic Differential
  Equations ... via Lubin-Tate Groups* (id confirmed; 02's correction of the
  charter is right).
- Schmidt = arXiv:1901.05516; Kedlaya, *p-adic Differential Equations*
  (kskedlaya.org PDF).

All computation is my own, written from scratch in this session; I did not read
or reuse any script from 01/02/03. Labels: **CONFIRMED** (I re-derived it from
the sources myself), **GAP** (hole exhibited precisely), **FALSE** (witness).

---

## VERDICT TABLE

| # | claim (source) | verdict |
|---|---|---|
| 1 | `a(k)` occurs in KMU-I only in 6.1.2 / 6.2 (01) | **CONFIRMED** |
| 2 | the `p >= 3` hypothesis is consumed **only** in 6.1.2, "nothing else" (01 headline) | **GAP** -- it is also consumed in 4.1 (Thm 4.1 Fulton is p-odd; Prop 4.3(2) engineers `e_P = p-1` with the `(p-1)`-power map, which is the identity at p = 2) |
| 3 | wild-point Prop 6.1 carries no parity hypothesis, valid verbatim at p = 2 (01) | **CONFIRMED** |
| 4 | no `lambda_i` / splitting function anywhere in 6.1.2 (01) | **CONFIRMED** |
| 5 | `a(k) = floor((k-1)/e_P)` is forced by the module, not chosen (01 sec.4) | **CONFIRMED**, and sharpened (proof below) |
| 6 | Riemann-Hurwitz *forbids* `e_P = 1` at p = 2 (01 sec.4) | **GAP** -- witness `X = P^1`, `eta(x) = x^n` (n odd); excluded only for `g >= 1` |
| 7 | `e_P = 3` is the minimal admissible tame index at p = 2 (01) | **CONFIRMED** |
| 8 | successor closed form `j'(k) = least j >= ceil(k/2), j = -k mod 3` `= l+r` (01) | **CONFIRMED** numerically to k = 80 **and proved** below; `e = 5, 7` do *not* fit Remark 6.5, so `e = 3` is singled out |
| 9 | leading coefficient `c_{k,j'(k)}` is a unit (01) | **CONFIRMED** for k <= 80 |
| 10 | `d(5) = 0` is the unique violation for k <= 80 (01) | **CONFIRMED** (full support, N = 200) |
| 11 | the global argument needs exactly `d(k) >= 1` for `k > mu(P)` and `d(k) -> inf` (01 sec.3) | **CONFIRMED**, and localized more sharply (Lemma 7.11, not just Prop 6.6) |
| 12 | `max(1, k/6)` feasible, `max(1, k/5)` infeasible (01 sec.5) | **CONFIRMED** independently; sharpened: `max(1, 2k/11)` is also infeasible |
| 13 | (A1)-(A3) is the complete constraint set (01 sec.5) | **GAP (benign)** -- two constraints missing, both verified satisfied; NOT a feasible-for-a-subset artifact |
| 14 | "none of the obvious [closed-form weights] work" (01 sec.5 caveat (i)) | **FALSE** -- witness `a(k) = floor((k-1)/3) + (k mod 2)` below |
| 15 | ceiling (C1) and its proof (02 sec.4.1) | **CONFIRMED** |
| 16 | 02's quotations of Pulita Thm 2.38, eq. 2.3.9, sec.1.5.1, Thm 2.13 | **CONFIRMED** (one mis-attribution of a display number, content right) |
| 17 | KM-ab Prop 5.5's Witt splitting has no cross terms at p = 2 (02, 01) | **CONFIRMED** from the source formula |
| 18 | 02's Table B measures KM-ab's `E_r` | **GAP** -- it measures `prod_i AH(pi^{p^i} x^{p^i})`, a different object; the P3 refutation survives on the literature quote |
| 19 | (L1) `v(lambda_i) >= i v(pi)` for `AH(pi x)`, all p (Note 1/4, 02, 01) | **CONFIRMED** |
| 20 | Note 2 commutation `psi o M_{B(x^p)} = M_{B(x)} o psi` | **CONFIRMED** (and correctly recorded by 01 as inapplicable to the Type-2 operator) |
| 21 | Note 6: "order-2 has `pi = -2`" | **FALSE** -- `AH(-2) != -1`; witness below. The *valuation* claim (rate 1 at M=1, 1/2 at M=2) is **CONFIRMED** |
| 22 | 01's four ground-truth `U_2` numbers | **CONFIRMED**, reproduced exactly |
| 23 | 02's Table A / Table B / Table C(m=0) numerics | **CONFIRMED**, reproduced exactly |

**Net effect on the theorem-candidate.** The load-bearing claim survives in the
form that matters: the only broken *estimate* is 6.1.2, and its exact
requirement is `d(k) >= 1` plus divergence, nothing stronger. Two things must be
corrected before staking anything: the headline must stop saying "nothing else"
(item 2 -- the char-2 geometry is a live, unverified prerequisite, not a quoted
fact), and 01 sec.5's "no closed form works" must be withdrawn (item 14 -- there
is one, and it is KMU's own weight plus an indicator).

---

## 0. My implementation, and how it is validated

I re-derived the Type-2 operator from KMU-I sec.4.3 + 6.1.2 myself:

    u = t^e is the parameter at 1 downstairs;  sigma(u) = (u+1)^p - 1.
    p = 2:  sigma(u) = u^2 + 2u,  so sigma(t) = t^2 G,  G := (1 + 2 x^e)^{1/e},  x = 1/t.
    [E : sigma(E)] = 2.  u' = -2 - u  (the other root of Y^2 + 2Y - sigma(u)),
    so for e ODD the conjugate of t is  t' = -t G,  since (-tG)^e = -(u+2) = u'.
    Tr(t^-k) = x^k (1 + (-1)^k G^{-k}).
    U_2 = (1/2) sigma^{-1} Tr, so with U_2(t^-k) = sum_j c_{k,j} t^-j:
        (1/2) x^k (1 + (-1)^k G^{-k}) = sum_j c_{k,j} x^{2j} G^{-j},
    solved by lowest-degree-first elimination over Q (exact `Fraction`s).

Three independent validations, all passing:

1. `G^3 == 1 + 2 x^3` **exactly** as rational series, so `t' = -tG` really is
   the conjugate (this is the only step where e odd is used).
2. `U_2(sigma(t^-j)) == t^-j` for j = 0..5 (the defining adjunction).
3. **Against a proved theorem.** At `e = p - 1 = 1`, KMU-I Lemma 6.2 (= KM-exp
   Cor. 4.7 for `R = Z_p`, `pi = p`) says `U_p(t^-k) in t^-(l+r) B` with
   `k = pl + r` and `B = {sum a_n u^-n : v_p(a_n) >= max(0,-n)}`. My solver
   satisfies **both** the pole order and the growth condition for all
   `k <= 60`. It also reproduces the independent Newton's-identity values
   (`U_2(t^-1) = t^-1`, `U_2(t^-2) = t^-1 + 2t^-2`, `U_2(t^-3) = 3t^-2 + 4t^-3`,
   `U_2(t^-6) = t^-3 + 18t^-4 + 48t^-5 + 32t^-6`).

Ground truth from 01 sec.6b, reproduced term for term at `e = 3, p = 2`:

```
U_2(t^-3) = t^-3                                              (one term)
U_2(t^-4) = t^-2 + (8/9)t^-5 - (40/243)t^-8 + (512/6561)t^-11 - ...
U_2(t^-5) = (5/3)t^-4 + (40/81)t^-7 - (112/729)t^-10 + (1600/19683)t^-13 - ...
U_2(t^-6) = t^-3 + 2 t^-6                                     (two terms)
U_2(t^-7) = (7/3)t^-5 + (140/81)t^-8 - (224/729)t^-11 + ...
U_2(t^-8) = t^-4 + (32/9)t^-7 + (224/243)t^-10 - (1792/6561)t^-13 + ...
```

All four of 01's stated regression numbers, and the whole sec.4 display,
**CONFIRMED**.

---

## 1. Priority 1 -- where the parity hypothesis actually sits

### 1.1 Exhaustive sweep

KMU-I standing hypothesis, sec.1.1: "Let p be an **odd** prime and let q be a
power of p." My grep for "odd" over the whole paper returns **one** line: that
one. `p = 2` is named in exactly two places, Remark 4.2 and Remark 6.5, as 01
says.

Grep for `a(k)`: lines 1717-1750 (Def. 6.3, Prop. 6.4, Rem. 6.5) and 1771-1844
(sec.6.2 basis, Prop. 6.6(2)). **Nowhere else. CONFIRMED.**

Grep for `e_P`: lines 1060-1061 (Prop. 4.3, `e_P = p - 1`, `r_1(p-1) = deg eta`,
RH (8)) and 1147 (`t_P^{e_P} = u_Q`). **Nowhere else.**

Every other `(p-1)` in the paper is `v_pi(p)`, not a tame index, and specializes
correctly at p = 2. I checked the one that matters: Cor. 6.8's slope set is
`{k(p-1)/delta_P : 1 <= k < v_pi(p) delta_P}`; at p = 2, n = 1 the character
field is `Q_2(zeta_2) = Q_2`, so `pi = 2`, `v_pi(p) = 1 = p-1`, and the slope
set becomes exactly `{k/d_P : 1 <= k <= d_P - 1}` = `HP_q(rho_P)` of sec.1.2.
**No parity anomaly on the wild side.**

### 1.2 Prop. 6.1 (wild) at p = 2: CONFIRMED

Verbatim proof: "If `P not in S`, then `Etilde_P in 1 + pi R_q` is constant. If
`P in S`, then `Etilde_P in A^{delta_P}_{pi,P}` since `(M,phi)` is
`delta`-overconvergent. In either case `Etilde_P in A^{p m_P}_{pi,P}`. By
definition `pi^{k/m_P} t_P^{-k}` is contained in `pi^{k(p-1)/(p m_P)}
A^{p m_P}_{pi,P}`. The result follows from (17)."

The only inputs are (17) (`U_p(A^m) subset A^{m/p}`), constancy, and
`delta`-overconvergence. `delta`-overconvergence at p = 2 and any Witt length is
supplied by KM-ab Prop. 5.5, which I read at source (sec.4.3 below): no parity
hypothesis, and the estimate is a product of Artin-Hasse growth conditions.
**CONFIRMED: Prop. 6.1 is valid verbatim at p = 2.**

(One p-uniform sloppiness, not a parity issue: `B^m` is defined with a *strict*
inequality `v_pi(b_k) > k/m_P`, and Prop. 6.1's last step needs the non-strict
version. Present at every p.)

### 1.3 GAP: the "nothing else" is wrong -- sec.4.1 consumes it too

01 sec.1 concludes: *"So the entire p >= 3 hypothesis of KMU-I is the local
estimate at eta(P) = 1, section 6.1.2. Nothing else."* That is **not** what the
source supports, and 01's own sec.1 quotes the evidence against it.

(a) **Theorem 4.1 (Fulton) is a p-odd theorem.** KMU-I Remark 4.2, verbatim:
"In [23], Sugiyama and Yasuda extend Fulton's result to the case p = 2." A
result that has to be *extended* to p = 2 did not cover p = 2. KM-exp sec.1.4
is explicit about the consequence: "It is also not immediately clear that we can
find a cover eta : X -> P^1 satisfying the desired properties. To construct eta,
we use the fact that X admits a simply branched map to P^1, **which is false
when p = 2**."

(b) **Prop. 4.3(2) is engineered by a map that degenerates.** The composite is
`eta_q : P^1 --(q-1)--> P^1 --> P^1 --(p-1)--> P^1 --> P^1`, and the ramification
over the point 1 comes from the `(p-1)`-power map. At p = 2 that map is the
identity, so the construction as written yields `e_P = 1` over 1, and Prop.
4.3(2) becomes the assertion `e_P = 1` -- which (sec.2.2 below) is incompatible
with Riemann-Hurwitz for `g >= 1`. So Prop. 4.3 is not merely unproven at
p = 2; **as stated it fails.**

01 does flag this in sec.5 caveat (iii) ("plausible but unverified") and quotes
KM-exp sec.1.4 in its own sec.1. The headline contradicts the body. The correct
statement, which is what a theorem-candidate should rest on:

> `p >= 3` is consumed in exactly **two linked** places: KMU-I sec.4.1
> (Prop. 4.3(2): the tame index of `eta` over 1 is set to `p - 1`), and
> KMU-I sec.6.1.2 (the estimate, whose weight denominator *is* that index).
> Everything else in KMU-I is p-uniform. Repairing 6.1.2 therefore requires
> **also** producing the geometric input: a tame Belyi map at p = 2 with
> `eta(S) = {0}` and every point over 1 of ramification index `e` (odd,
> `e > 1`). Sugiyama-Yasuda / Kedlaya-Litt-Witaszek supply a tame Belyi map;
> they do not supply the control on `e_P` that Prop. 4.3(2) supplies at odd p.

This is a live prerequisite, not a footnote. Recommend workstream 04 state it as
an explicit hypothesis of any theorem-candidate rather than inherit 01's
"nothing else".

---

## 2. Priority 2 -- the reconstruction

### 2.1 `a(k) = floor((k-1)/e)` is forced. CONFIRMED and sharpened

01 says the weight is forced by the eigenspace form. It is, and the reason is
tighter than 01 states: with `u = t^e` and `A^m = (+)_{i} t^{-i} B^m`,
`B^m = {sum b_n u^{-n} : v_pi(b_n) > n/m_P}`, write `k = e n + i` with
`1 <= i <= e`. Then `t^{-k} = t^{-i} u^{-n}` and the required valuation is
`n/m_P`. And

    floor((k-1)/e) = floor((e n + i - 1)/e) = n + floor((i-1)/e) = n   for 1 <= i <= e.

So `a(k)` is literally the `u`-exponent, i.e. pure bookkeeping, not an estimate.
This also re-derives KMU's Prop. 6.4 identity in one line: with
`l + r - 1 = (p-1)s + w`, `0 <= w < p-1`, we get `pl + r - 1 = (p-1)(s+l) + w`,
hence `a(pl+r) - a(l+r) = l` **exactly**, for every p. **CONFIRMED.**

### 2.2 GAP: "Riemann-Hurwitz forbids `e_P = 1`" is over-stated

01 sec.4: "`p-1 = 1` is unusable: with `e_P = 1`, Riemann-Hurwitz (8)
`2(g-1) + r_0 + r_1 + r_inf = deg(eta) = r_1` forces
`2(g-1) + r_0 + r_inf = 0`, impossible".

I re-derived (8) myself (tame RH for `eta : X -> P^1` unramified outside
`{0,1,inf}`: `2g-2 = -2 deg eta + sum_{Q} (deg eta - r_Q)`, giving
`2(g-1) + r_0 + r_1 + r_inf = deg eta`). The algebra of 01's step is right, but
the conclusion is not: `r_0, r_inf >= 1` gives `2(g-1) <= -2`, i.e.

> `e_P = 1` is possible **exactly** when `g = 0` and `r_0 = r_inf = 1`.

**Witness:** `X = P^1`, `eta(x) = x^n` with n odd. This is tame at p = 2,
totally ramified over 0 and infinity (`r_0 = r_inf = 1`), and unramified over 1
with `r_1 = n = deg eta`. It satisfies (8): `2(0-1) + 1 + n + 1 = n`. So the
statement is "impossible for `g >= 1`", or "impossible whenever `|S| >= 2`"
(since `r_0 >= |S|`), not "impossible". For the arbitrary-curve target this
changes nothing, but it is presented as a proof step and it is not one.

`e_P = 3` minimal: `e_P` must be prime to p = 2 (tame) and `> 1`, so odd and
`> 1`, so `>= 3`. **CONFIRMED.**

### 2.3 The successor closed form. CONFIRMED, and now proved

01: the minimal pole of `U_2(t^-k)` at `e = 3` is the least `j >= ceil(k/2)`
with `j = -k mod 3`, and this equals Remark 6.5's `l + r` for `k = 2l - r`,
`r in {0,1}`. Verified numerically by my solver for `k <= 80`. It is also
**provable in two lines**, which I record because a theorem-candidate should not
cite a table for it:

- `k = 2c` even: `-k = -2c = c (mod 3)`, and `ceil(k/2) = c`, so `j' = c`.
  Remark 6.5 gives `l = c`, `r = 0`, `l + r = c`. Equal.
- `k = 2c - 1` odd: `-k = -2c+1 = c+1 (mod 3)`, and `ceil(k/2) = c`, so
  `j' = c + 1`. Remark 6.5 gives `l = c`, `r = 1`, `l + r = c + 1`. Equal.

**And it discriminates.** The same computation at `e = 5` gives, for k even,
`j' = c` only when `3c = 0 mod 5`; otherwise `j' > c`, which does not fit the
`k = 2l - r`, `r in {0,1}` shape of Remark 6.5. So `e = 3` is *singled out* by
Remark 6.5's own phrasing, it is not merely consistent with it. This is a
stronger argument for the identification than the four numerical matches, and 01
does not make it.

Two further confirmations I found that 01 does not use:

- `v_2(c_{k,j'(k)}) = 0` for all `k <= 80` (**CONFIRMED**, so Remark 6.5's
  estimate is sharp and `d(5) = 0` is real, not an artifact of a lossy bound).
- KMU cite `k = 5` as their failing example even though `d(3) = 0` as well
  (`U_2(t^-3) = t^-3` exactly, a genuine eigenvector). That is consistent only
  with `mu(P) >= 3`, i.e. with `mu(P) = e_P = 3`. Independent corroboration.

The one loose end: Remark 6.5 says "For `k >= 3`, define `a(k) = ...`", whereas
the analogue of Def. 6.3's "`k > p - 1`" at `e = 3` would be `k > 3`. Harmless
(it is where `a` is *defined*, not where the estimate is *needed*), but worth
knowing it is not a perfect textual match.

### 2.4 `d(5) = 0` is the unique violation. CONFIRMED

With `a(k) = floor((k-1)/3)` and the **full computed support** (N = 200, so all
`j` with `2j < 194`), `d(k) = min_j [a(k) - a(j) + v_2(c_{k,j})]`:

    d(k) = 0  exactly for k in {1, 2, 3, 5};  k <= 3 is removed by k > mu(P) = 3.
    d(4..20) = 1, 0, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 3, 3, 3

and `d(k) -> infinity` (`d(70..80) = 12,13,12,13,13,13`). The full-support value
equals the stated `a(k) - a(l+r)` in every case, i.e. the tail never binds.
**CONFIRMED, and 01's "only violation" claim holds to k = 80.**

### 2.5 What the global argument consumes. CONFIRMED, localized more sharply

01 sec.3 says the requirement is `d(k) >= 1` for `k > mu(P)` and `d(k) -> inf`,
and points at Prop. 6.6(2). That is right but the *binding* use is one section
later, and a theorem-candidate should cite the right line:

- Cor. 6.8's proof fixes `m_{e,P} = 1/e` for `eta(P) = 1`, so a column of slope
  `d(k)/m_P` has slope `d(k) * e`.
- **Lemma 7.11** (`Psi'` is an e-perturbation of `Psi`) opens with: "recall from
  the global Hodge bound that the pi-adic valuation of `Theta~(e^{m_e}_{alpha,k})`
  is **>= e** if either: `alpha = P not in S`, or `alpha = P in S` and
  `k >= e delta_P`." For `eta(P) = 1` points (which are exactly `P not in S`)
  this is `d(k) * e >= e`, i.e. **`d(k) >= 1`, and nothing more**. Confirmed.
- `d(k) -> infinity` is needed for tightness in Cor. 6.7 (`Theta~_q` completely
  continuous on `Vtilde^m_pi`), not for the bound itself.
- Why `d(k) = 0` is fatal rather than merely lossy: **Lemma 7.12** says
  "If X is ordinary, then `NP^{<r}_{pi_q}(phi)` has **N** segments of slope 0"
  (Deuring-Shafarevich), and Cor. 6.8's bound has `r = N` slope-0 segments. A
  `d(k) = 0` column inserts an `N+1`-st, so the two polygons can no longer share
  a terminal point. This is the mechanism, and 01's version of it (via the
  target's `g-1+|S|` count) is the right idea one level up.

I also checked the rank bookkeeping 01 lists as caveat (iv): `D = sum_{eta(P)=1}
mu(P) P`, `deg D = r_1 mu(P)`; with `mu(P) = e_P` and `r_1 e_P = deg eta`, RR
gives `h^0(D) = deg eta - g + 1 = g - 1 + r_0 + r_1 + r_inf = N` (13). So the
count comes out for **any** common tame index `e_P = mu(P)`, in particular
`e_P = 3`. **Caveat (iv) discharged.**

---

## 3. Priority 3 -- the feasibility computation and the constraint set

### 3.1 I enumerated the paper's constraints before looking at 01's list

What KMU actually demand of `A^m_{pi,P}` at `eta(P) = 1`, read off the paper:

- `Ltilde_pi subset Atilde^m_pi` (sec.6.2 exact sequence). `L = H^0(D)` has poles
  of order `<= mu(P)` with unit coefficients, so `a(j) = 0` for `j <= mu(P)`.
  = 01's **(A1)**.
- `union_m Vtilde^m_pi = Vtilde^dagger_pi` (Cor. 6.7), so `a(j) = O(j)`.
  = 01's **(A2)**.
- Lemma 7.11 / Cor. 6.7: `d(k) >= 1` for `k > mu(P)`, `d(k) -> inf`.
  = 01's **(A3)**.
- Prop. 6.6(2), second term: `a(k)/m_P >= d(k)/m_P`, i.e. **(A4) `a(k) >= d(k)`**.
  01 derives this in its sec.3 but **omits it from the sec.5 list**. It is
  automatic: take `j = j'(k)`, where `v_2(c_{k,j}) = 0` and `a(j) >= 0`, so
  `d(k) <= a(k)`. Benign.
- Cor. 6.8's proof ("the matrix of `Theta~` w.r.t. `B^{m_e}` has coefficients in
  R") needs `A^m` to be `Theta~`-stable, including on the part `L` kills, i.e.
  **(A5) `d(k) >= 0` for `k <= mu(P)`**. Not in 01's list. I checked it: with
  KMU's weight and with every LP solution, `d(1) = d(2) = d(3) = 0`. Satisfied.
- Surjectivity `Atilde^m -> A^{m,tr}` (01's caveat (ii), "asserted without
  proof"): the liftings are `e_{P,k} = t^-k + c_{P,k}` with `pr(c_{P,k}) = 0`,
  i.e. `c_{P,k} in L_pi`, and `L_pi subset A^m_pi` is exactly (A1). So
  **caveat (ii) reduces to (A1) and is discharged** for the local weight; I did
  not re-verify the semi-local gluing.

Three things I checked that could have been hidden constraints and are not:

- **Rational `a(k)`.** KMU write "the positive **integer** `a(k)`", and 01's LP
  weights are in `(1/6)Z`. Harmless: sec.6.1 already says "it will be convenient
  to assume that R contains an `m_P`-th root of `pi`", and replacing
  `(a, m_P)` by `(6a, 6m_P)` leaves every column valuation `d(k)/m_P` invariant
  while keeping `m >= m_pi`.
- **Non-monotone `a`.** 01's weight has `a(6) < a(5)`. Nothing breaks: `A^m` is
  only an `R_q`-module, not a ring (indeed `B^m` is not a ring even in KMU's own
  construction, since `u^-1` violates `v_pi > 1/m_P`).
- **Linear lower bound `a(k) >= c k`.** Needed so the `A^m` filtration is a
  filtration of `A^dagger`; automatic here, since `a(k) >= d(k) >= k/6` by
  induction from `a >= 0`.

**Verdict on item 13: GAP, benign.** Two constraints are missing from 01's list,
both automatic or verified. This is **not** the feasible-for-a-subset failure
mode the charge worried about; workstream 04 is not doomed on this axis. The
caveat that remains is 01's own: the system is *finite* (truncated in k and in
support), and finite feasibility is not existence.

### 3.2 Independent recomputation of the LP. CONFIRMED, and sharpened

The system is a difference-constraint system, so I solved it exactly rather than
by fixed-point iteration: for every `k > mu(P)` and every `j` in the computed
support, `a(j) - a(k) <= v_2(c_{k,j}) - D(k)`, plus `a(j) = 0` for `j <= 3` and
`a(j) >= 0`. Feasible iff no negative cycle; Bellman-Ford over `Fraction`s.

| target `D(k)` | KMAX = 40 | 48 | 60 | 80 |
|---|---|---|---|---|
| `max(1, k/4)` | infeasible | infeasible | -- | -- |
| `max(1, k/5)` | **infeasible** | **infeasible** | **infeasible** | -- |
| `max(1, 2k/11)` | **infeasible** | -- | -- | -- |
| `max(1, k/6)` | **feasible** | **feasible** | **feasible** | **feasible** |
| `max(1, k/7)` | feasible | feasible | feasible | -- |
| constant 1 | feasible | feasible | feasible | -- |

**01's item 12 CONFIRMED**, with the threshold sharpened: it lies in
`[k/6, 2k/11)`, not merely in `[k/6, k/5)`.

Truncation robustness (KMAX = 40): the verdicts are identical at support depths
`N = 100, 140, 180, 220`. My solution is the pointwise-**maximal** feasible
weight (shortest paths); 01 reports a minimal one. They are consistent -- 01's
is `<=` mine at every index I checked (`a(6) = 1 <= 7/2`, `a(8) = 7/3 <= 3`,
`a(48) = 15 <= 35/2`), and both agree on `a(1..5) = 0,0,0,1,2` and
`a(7) = 19/6`, which is strong evidence we built the same constraint system.

### 3.3 FALSE, with witness: a closed-form admissible weight exists

01 sec.5 caveat (i): *"a proof needs a closed form for `v_2(c_{k,j})` and an
explicit closed-form weight (**none of the obvious ones work**; see the table)"*.

I found one on the second try. **Witness:**

>     a(k) = 0                             for k <= 3
>     a(k) = floor((k-1)/3) + (k mod 2)    for k >= 4

i.e. **KMU's own Remark 6.5 weight plus an indicator on odd k**. Measured over
the full computed support at `N = 300` (all `j` with `2j < 292`), for every
`k` in `[4, 100]`:

- `d(k) >= 1`: **no violations**, `d(4..24) = 1,1,1,1,1,2,1,1,2,3,1,2,3,3,2,3,3,4,3,3,4`.
- `d(1) = d(2) = d(3) = 0`, so **(A5)** holds.
- `a(k) = O(k)` (`~ k/3`), so **(A2)** holds; `a(k) = 0` for `k <= 3`, so
  **(A1)** holds.
- `d(k) -> infinity`: `d(100) = 17`; asymptotically `d(k) ~ k/6`.

For contrast, the neighbours all fail: `floor((k-1)/3)` and `ceil(k/3)` and
`floor(k/3)` fail at `k = 5`; `ceil((k-1)/3)` and `floor((k+1)/3)` fail at
`k = 7`; `ceil((k-1)/3) + (k mod 2)` fails at `k = 7, 10`; the exact rationals
`(k-1)/3` and `k/3` fail at `k = 5, 7`; `k/2` fails at `k = 5`. So it is a
narrow window -- but it is nonempty, and 01's parenthetical is **FALSE**.

**Why this matters for a proof.** In every case I measured the minimum defining
`d(k)` is attained at the *leading* term `j = j'(k)`, and the tail
`a(k) - a(j) + v_2(c_{k,j})` is monotonically increasing in `j` (sampled at
`k = 4, 5, 7, 13, 25, 50` out to `j ~ 145`; e.g. at `k = 5` it runs
`1, 2, 3, 3, 5, 8, 9, 9, 9, 10, 11, 11, 15, 17, ...`). So the residual open
problem splits cleanly into:

1. **A finite arithmetic identity** (provable by cases mod 6, using sec.2.3's
   closed form for `j'(k)`): for `k >= 4`,
   `floor((k-1)/3) + (k mod 2) - floor((j'(k)-1)/3) - (j'(k) mod 2) >= 1`.
   Hand-checked on both residue branches: `k = 2c` gives `j' = c`, `k = 2c-1`
   gives `j' = c+1`.
2. **A tail estimate**, still open and still the hard part 01 identified:
   `v_2(c_{k,j}) >= a(j) - a(k) + 1` for `j > j'(k)`, which needs the closed
   form for `v_2(c_{k,j})` (a Newton-identity / symmetric-function problem, cf.
   KM-exp Cor. 4.7's induction).

That is a materially better starting point than "an LP solution exists for
k <= 48", and I recommend workstream 04 build on the closed form rather than the
LP.

**Status: the repair remains OPEN**, but the object to prove is now explicit.

---

## 4. Priority 4 -- 02's ceiling and its quotations

### 4.1 (C1). CONFIRMED

Statement: `theta(T) = 1 + sum_{k>=1} c_k T^k` a splitting function for a
character of order `p^M`, convergent on `|T| <= 1`, with `theta(a)` a primitive
`p^M`-th root of unity for some `|a| = 1`; if `v(c_k) >= rk` for all `k >= 1`
then `r <= v(zeta_{p^M} - 1) = 1/(p^{M-1}(p-1))`.

Proof audit: `theta(a) - 1 = sum_{k>=1} c_k a^k` converges (hypothesis), and
`v(c_k a^k) = v(c_k) >= rk >= r` for `k >= 1` when `r > 0`, so the ultrametric
inequality gives `v(theta(a) - 1) >= r`; `theta(a) - 1 = zeta - 1` has valuation
exactly `1/(p^{M-1}(p-1))`. If `r <= 0` the conclusion is vacuous. **The proof
is correct.** 02's own remark that (C1) caps only bounds of the shape
`v(c_k) >= rk`, and therefore does *not* cap a shifted certificate like
`floor((k-1)/3)`, is also correct and is the honest caveat.

### 4.2 Pulita quotations. CONFIRMED

I read each at source in my own pdftotext:

- **sec.1.5.1**: "The Newton polygon of P shows that P has exactly p - 1 non
  trivial zeros of value `omega = |p|^{1/(p-1)}`, and inductively `P(X) -
  pi_{j-1}` has p zeros of valuation `omega^{1/p^j}`. Hence `|pi_j| =
  omega^{1/p^j}`, for all `j >= 0`". Verbatim match.
- **Thm 2.38**: "`theta_d(lambda, a)` is a `p^{m+1}`-th root of 1 ... the image
  of 1 ... is the inverse of the unique primitive `p^{m+1}`-th root of 1, say
  `xi_m`, satisfying `|a^n pi_m - (xi_m - 1)| < |a^n pi_m|`". Verbatim match,
  and it does supply exactly the input (C1) needs: `|xi_m - 1| = |pi_m|`.
- **Prop. 2.12**: "converges **exactly** in the disk `|T| < 1` ... `Ray(L, rho)
  = rho^{p^m + 1}` ... the irregularity of L is `p^m`". Verbatim match.
- **Thm 2.13**: "`E_m(T^p)/E_m(T)` is over-convergent ... if and only if
  `|w - p| <= |p|^{m+2}`". Verbatim match -- and this is the criterion 02 used
  for its negative control, correctly.
- **eq. (2.3.9)**: minor mis-attribution. The display numbered (2.3.9) is
  `E_{m+1}(nu_0 T^n)^{-1} = 1 + pi_{m+1} nu_0 T^n + ... + (pi_{m+1} nu_0
  T^n)^{p-1}/(p-1)! mod C`; the statement 02 quotes as (2.3.9),
  `theta_d((1,0,...,0),T)^{-1} = 1 + pi_m T^n mod C`, is the **unnumbered
  sentence immediately after it** ("Since `pi_{m+1} nu_0 = p pi_{m+1} - pi_m`,
  hence ..."). The content, and 02's use of it ("the leading coefficient of the
  splitting function is exactly `pi_m`"), are correct.
- **Parity census.** My own grep of the Pulita text for `p = 2 / p > 2 /
  p != 2 / odd` returns **six** hits, at exactly the loci 02 lists (Intro 0.0.4
  about Matsuda; Cor. 4.31's `p > 2` / `p = 2` dichotomy; its proof's "is = 1 if
  and only if p = 2, and m(n) = j = 0"; the remark before Thm 4.57). Standing
  hypothesis is only "Let p > 0 be a fixed prime number". **CONFIRMED.**
- **Kedlaya**: Def. 17.1.3 ("radius of convergence `p^{(p-1)/p^2}` (exercise)"),
  Ex. 17.1.5 ("it was shown for p > 2 by Matsuda [169] by an explicit
  calculation, and for all p by Pulita [185]"), Thm 19.4.1 (`R(D^dagger(V) (x)
  F_rho) = rho^b`) all verified verbatim in the fetched book.
- 02's corrections `Q_2(sqrt(-2)) != Q_2(zeta_4)` (distinct classes in
  `Q_2^x/(Q_2^x)^2`) and "`(X+1)^2 - 1 = 2X + X^2`, so at p = 2 Dwork's and
  Matsuda's Lubin-Tate series coincide" are both **CONFIRMED**.

### 4.3 KM-ab Prop. 5.5, no cross terms at p = 2. CONFIRMED

Source, verbatim: `E_r = prod_{i=0}^{n-1} prod_{j=0}^{s_i} E([r_{i,j}] t^{-j}
gamma_{n-i})`, with `v_p(gamma_i) = 1/(p^{i-1}(p-1))`, and the proof closes
"Since `E(x) in Z_p[[x]]`, it is clear that `E_r in O_L[[pi_s t^{-1}]]`."

A literal product of rank-one Artin-Hasse factors; no parity hypothesis; the
only property of `E` used is `Z_p`-integrality. **P3 is refuted at the source,
independently of any computation.** 01's reading of the garbled `gamma`
condition is also right: the paper prints `E(gamma_n) = zeta_{p^n}^{p^{n-i}}`,
and `zeta_{p^n}^{p^{n-i}} = zeta_{p^i}`, so "`gamma_n`" is a typo for
"`gamma_i`" and the condition is `E(gamma_i) = zeta_{p^i}`.

**GAP (item 18), recorded for honesty:** 02's Table B measures
`prod_{i=0}^{m-1} AH(pi^{p^i} x^{p^i})`, which is **not** `E_r`: in `E_r` the
factors carry *distinct* torsion points `gamma_{n-i}` and *distinct* pole
degrees `t^{-j}`, not `p^i`-th powers of one variable. The verdict survives
because the literature quote carries it, and because the general lemma is
p-uniform: a product of series each satisfying `v(coeff of degree d) >= c*d`
satisfies the same. But the numerics do not measure the object they are labelled
with, and the table should say so.

---

## 5. Priority 5 -- the coordinator's notes

### 5.1 (L1). CONFIRMED; 01's one-line proof is the right one

01: `AH(x) in Z_p[[x]]` (Dwork-Dieudonne) gives `AH(pi x) = sum a_i pi^i x^i`
with `a_i in Z_p`, hence `v(lambda_i) >= i v(pi)` with equality iff `a_i` is a
unit. Correct, and it makes the product-formula rearrangement unnecessary. I
checked the coordinator's three flagged gaps anyway:

- `-mu(n)/n in Z_2` for n odd: yes.
- binomial integrality: `binom(e,k)` is an integer-valued polynomial in `e`,
  hence `Z_p`-valued on `Z_p` by density. Fine.
- product rearrangement / equality of `exp(sum_i x^{p^i}/p^i)` with
  `prod_{n odd} (1 - x^n)^{-mu(n)/n}`: I verified the identity as exact rational
  series **to degree 170** (agreement is exact), and that every coefficient of
  `AH` is 2-integral to degree 170.

### 5.2 Note 2 commutation. CONFIRMED

For `psi(sum a_n x^n) = sum a_{pn} x^n`: `psi(B(x^p) f)_n = (B(x^p)f)_{pn} =
sum_m b_m a_{pn - pm} = sum_m b_m (psi f)_{n-m} = (B psi f)_n`. Exact, for every
p. Also verified on random integer series. 01 is right that it applies to the
wild operator `sigma(t) = t^p` and **not** to the Type-2 operator
`sigma(t) = t^2 G`, so it does not touch the obstruction.

### 5.3 FALSE with witness: Note 6's "order-2 has `pi = -2`"

Note 6 asserts that at p = 2 the order-2 (M = 1) normalization is
`pi^{p-1} = pi = -2`, `v(pi) = 1`. The relation `pi^{p-1} = -p` does give
`pi = -2`. But `-2` is **not** the Artin-Hasse splitting parameter: the
splitting parameter must satisfy `AH(pi) = zeta_2 = -1`, and

    sum_{i>=0} (-2)^{2^i} / 2^i  =  -2 + 2 + 4 + 32 + 4096 + ...   (v_2 = 2)
    AH(-2) = exp(that) = 1261  (mod 2^12),      -1 = 4095  (mod 2^12).

`AH(-2) = 1 mod 4`, while `-1 = 3 mod 4`. **`AH(-2) != -1`.**

Equivalently: at p = 2 the classical *short* Dwork splitting
`theta(x) = exp(pi(x - x^p))` degenerates, since `theta(1) = exp(0) = 1`, not
`zeta_2`. The correct `pi` at M = 1 is the Hensel root of `AH(pi) = -1` in
`Q_2` (which exists because `AH(x) = 1 + x + ...` and `v(zeta_2 - 1) = 1`),
and it has `v(pi) = 1`.

**Consequence: none for the conclusion.** Note 6's load-bearing content is the
*valuation* -- rate 1 at M = 1, rate 1/2 at M = 2 -- and that is **CONFIRMED**
(`v(zeta_2 - 1) = v(-2) = 1`, `v(zeta_4 - 1) = 1/2`), consistent with the (C1)
ceiling `1/(p^{M-1}(p-1))`. Knock-on for 02: the row "Dwork short
`exp(pi(x-x^p))`" in its sec.3.4 comparison table measures the radius of a
series that is not a splitting function at p = 2; the radius number is right
(Kedlaya Def. 17.1.3 is p-uniform) and the verdict is unaffected, since
Artin-Hasse dominates it anyway.

---

## 6. Priority 6 -- numerics reproduced with my own code

Everything below is my own implementation (sec.0), independent of 01/02/03.

**01's ground truth (sec.6b).** All four reproduced exactly:
`U_2(t^-3) = t^-3`; `U_2(t^-6) = t^-3 + 2t^-6`; `U_2(t^-5) = (5/3)t^-4 +
(40/81)t^-7 - (112/729)t^-10 + ...`; and at `e = 1`,
`U_2(t^-6) = t^-3 + 18t^-4 + 48t^-5 + 32t^-6`. The rest of 01's sec.4 display
(`k = 4, 7, 8`) also matches term for term. 01's sec.6c side result (lowest pole
`= ceil(k/2)` at `e = 1`) confirmed for p = 2, `k <= 60`.

**02's Table A** (`AH(pi x)`, `pi^2 = -2`). Every row reproduced exactly:
`c_1 = pi` (v 1/2), `c_2 = -2` (v 1), `c_3 = -(4/3)pi` (v 5/2),
`c_4 = 8/3` (v 3), `c_5 = (28/15)pi` (v 5/2), `c_6 = -128/45` (v 7),
`c_7 = -(536/315)pi` (v 7/2), `c_8 = 1408/315` (v 7),
`c_9 = (9872/2835)pi` (v 9/2), `c_10 = -84032/14175` (v 6),
`c_12 = 444736/66825` (v 6), and v = 13/2, 8, 11, 12 at k = 13, 16, 22, 24.
`min_{k<=40} v(c_k)/k = 1/2`. Unit-index census to degree 160: **82 indices,
density 0.512, largest gap 6**, list beginning
`1, 2, 5, 7, 9, 12, 13, 16, 22, 24, 28, 33, 35, 36, 40, 41, 42, 43, 44, 46, 48,
49, 50, 53, 54, 57, 62`. Exact agreement on every number.

**02's Table B** (Witt levels). Reproduced digit for digit:

| m | e | v(pi_m) | min v/k | # attaining |
|---|---|---|---|---|
| 1 | 1 | 1 | 1 | 15 |
| 2 | 2 | 1/2 | 1/2 | 22 |
| 3 | 4 | 1/4 | 1/4 | 23 |

`v(c_k)/v(pi_m)` for k = 1..16 at m = 2:
`1, 4, 3, 10, 15, 6, 9, 10, 9, 10, 11, 22, 15, 16, 15, 16` -- exact match.
At m = 3: `1, 6, 3, 4, 5, 6, 7, 8, 25, 22, 19, 24, 13, 26, 23, 16` -- exact
match.

**02's Table C, m = 0 row.** `theta_0(T) = exp(-2(T^2 - T))`:
`v(theta_{2^j}) = 2, 3, 5, 9, 17` for `j = 2..6`, matching `(2^{j-2}+1)`, and
`min_{k<=64} v/k = 17/64`. Exact match. (I did not re-run the Lubin-Tate
variation table of 02 sec.3.5; that row only supports the attack-(B) no-go,
which is not load-bearing for the theorem-candidate, and Pulita Thm 2.13 --
which I verified at source -- already carries it.)

---

## 7. What I recommend workstream 04 do differently

1. **Do not inherit "the p >= 3 hypothesis is consumed only in 6.1.2."** State
   the geometric input as an explicit hypothesis of the theorem-candidate: a
   tame Belyi map `eta : X -> P^1` in characteristic 2 with `eta(S) = {0}` and
   every point over 1 of a common odd ramification index `e > 1`. Sugiyama-
   Yasuda / Kedlaya-Litt-Witaszek give a tame Belyi map; they do **not** give
   Prop. 4.3(2)'s control on `e_P`, and at p = 2 KMU's own recipe (the
   `(p-1)`-power map) produces `e_P = 1`, which Riemann-Hurwitz rules out for
   `g >= 1`.
2. **Cite Lemma 7.11, not only Prop. 6.6(2)**, for the requirement `d(k) >= 1`,
   and Lemma 7.12 (Deuring-Shafarevich, N slope-0 segments) for why `d(k) = 0`
   is fatal rather than lossy.
3. **Use the closed-form weight, not the LP.** `a(k) = floor((k-1)/3) +
   (k mod 2)` (with `a(k) = 0` for `k <= 3`) is admissible on everything I could
   measure (`k <= 100`, full support at N = 300), and reduces the open part to
   one tail estimate on `v_2(c_{k,j})`.
4. **Add (A5) to the admissibility list** (`d(k) >= 0` for `k <= mu(P)`); it is
   needed for `Theta~`-stability of `A^m` in Cor. 6.8's proof, and it happens to
   hold with equality.
5. **Do not state `Riemann-Hurwitz forbids e_P = 1`** without the genus
   qualifier.

## 8. Reproduction

Session scratchpad `ws20/` (not committed): `code/u2.py` (the Type-2 operator,
exact rationals, algorithm quoted in full in sec.0 above), `code/checks.py`
(min-pole / unit / defect audits), `code/lp.py`, `lp2.py`, `lp3.py` (exact
Bellman-Ford on the difference-constraint system), `code/closed.py`,
`code/witness.py` (the closed-form weight), `code/ah.py` (AH product identity,
Table A, the `AH(-2)` witness), `code/misc.py` (Witt tables, theta_0, Note 2),
`code/tail.py` (tail monotonicity). Total runtime well under the 5-minute /
2 GB budget; the longest single run (N = 300, k <= 100) was 48 s.

---
---

# PART TWO -- Priority-0 audit of `04-weight-proof.md`

Added 2026-08-20, after `04-weight-proof.md` (765 lines) and
`crates/axeyum-cas/examples/noh_wt_certificate.rs` (376 lines) landed. Same
rules as Part One: my own re-derivations, my own code, sources re-read at
source. My operator implementation is the one specified and validated in
sec. 0 above (three validations, including agreement with KMU Lemma 6.2 /
KM-exp Cor. 4.7 at `e = p-1 = 1`, a **proved** theorem).

## VERDICT TABLE (Part Two)

| # | claim (04) | verdict |
|---|---|---|
| P0-1 | THEOREM 1: hypergeometric closed form, both parity cases | **CONFIRMED** -- re-derived from scratch and checked against my operator for `e in {1,3,5,7}`, `k <= 25`, every `m` in support: 0 mismatches |
| P0-2 | the `W = sinh^2(e tau)` reduction and the ODE `(1+z^2)y'' + zy' - lambda^2 y = 0` | **CONFIRMED** -- both reductions and both recurrences re-derived line by line |
| P0-3 | THEOREM 2: `v_2(c) = Sigma - 2m + s_2(m)` | **CONFIRMED** (Legendre + the factorisation); machine-checked `k <= 60`, full support |
| P0-4 | LEMMA A and its mod-8 proof (all four sub-cases) | **CONFIRMED** line by line; `k <= 600, m <= 80`, 0 violations, 150 tight pairs all `k = 2 mod 4, m = 1` |
| P0-5 | THEOREM 3: the six-case mod-6 identity | **CONFIRMED** -- both tables recomputed entry by entry (one cosmetic omission, below) |
| P0-6 | THEOREM 3: the three parity tail cases + the `j' = 3` special case | **CONFIRMED** line by line; case coverage is complete |
| P0-7 | THEOREM 4: the `k = 6` self-loop, `gamma <= 1/6` exactly | **CONFIRMED**; supersedes my own LP bound `[1/6, 2/11)` |
| P0-8 | 18-row global-consumption table | **CONFIRMED** on every row I could check at source (details below) |
| P0-9 | Lemma 7.11 strictness resolution (Def. 7.3(1) margin `k/delta_P` is p-independent; `d(k) >= 1` non-strict suffices because `I^{<r}` is strict) | **CONFIRMED** verbatim |
| P0-10 | Cor. 7.14 count cancellation, `e_P`-independence | **CONFIRMED** verbatim |
| P0-11 | sec. 7.2: no eigenspace regrading realises the parity indicator | **CONFIRMED** (both halves) |
| P0-12 | **LEMMA E reduction: "no loss at all for `r in [0,1]`"** | **GAP -- the coverage claim overreaches.** The `r` capped is *pi_q*-adic; Theorem 1.1's `r` is *q*-adic; they differ by `v_pi(p) = 2^{n-1}`. See P2-6 |
| P0-13 | sec. 6: `a*` orbit-sum closed form, and the Main Lemma | **CONFIRMED** -- reproduces 01's LP weights exactly; Main Lemma verified `j < 400, m < 70`, min slack 0 at `(1,1)` |
| P0-14 | Note-7 refutation 1 (`m + v_2(binom(-k/3,m))`) | **CONFIRMED (refutation stands)** -- right for `k=4`, wrong for `k=5` and `k=7` |
| P0-15 | Note-7 refutation 2 (`m = 2|j-k|/3`) | **CONFIRMED (refutation stands)** -- `2/3` at `(k,j) = (4,5)` |
| P0-16 | the Rust certificate is self-checking and mutation-tested | **CONFIRMED** as a real gate (6 mutations tried, all exit 1), with one **wording GAP**: route R4 is not independent of R2 |

**Bottom line.** Theorems 1-4, Lemma A and the Main Lemma are correct; I could
not break any of them, and I re-derived every one. The local estimate is
repaired. **One substantive gap: the theorem-candidate's "for every `r in
[0,1]`" is supported, on 04's own Lemma-E route, only for characters of order
2 (`n = 1`); for order `2^n` the supported range is `r in [0, 2^{1-n}]`.** That
gap arises from a tension between two of 04's own results (Theorem 4 caps
`d(6) <= 1`; Lemma E needs `m_P >= 1`), so it is structural, not a slip in one
line.

---

## P2-1. THEOREM 1: re-derived, then measured

I did the derivation myself before reading 04's, and it comes out identical.

*The reduction.* With `v := 2x^e`, `G = (1+v)^{1/e}`, the defining identity
`(1/2)x^k(1 + (-1)^k G^{-k}) = sum_j c_{k,j} x^{2j}G^{-j}` has, for
`j = j'(k) + em`,

    x^{2j}(1+v)^{-j/e} = x^{2j'}(1+v)^{-j'/e} * ( x^{2e}/(1+v) )^m,

and `x^{2e}/(1+2x^e) = v^2/(4(1+v)) = sinh^2(phi)` where `e^{phi} = (1+v)^{1/2}`
(check: `sinh phi = v/(2(1+v)^{1/2})`). So `W` is the natural variable and, as
04 notes, **it does not depend on `e`**. Dividing:

- `k` even, `j' = k/2`: quotient `= (1/2)((1+v)^{k/(2e)} + (1+v)^{-k/(2e)}) = cosh(k tau)`.
- `k` odd, `j' = (k+e)/2`: quotient `= x^{-e}(1+v)^{1/2} sinh(k tau)`, and since
  `sinh(e tau) = sinh(phi) = x^e (1+v)^{-1/2}`, this is `sinh(k tau)/sinh(e tau)`.

Both **CONFIRMED**.

*The ODE.* With `z = sinh phi`, `phi = arcsinh z`, `lambda = k/e`:
`y = cosh(lambda phi)` has `y' = lambda sinh(lambda phi)/sqrt(1+z^2)` and
`(1+z^2)y'' = lambda^2 y - z y'`, i.e. `(1+z^2)y'' + zy' - lambda^2 y = 0`;
`sinh(lambda phi)` solves the same linear equation. **CONFIRMED.**

*The recurrences.* Substituting `y = sum a_m z^{2m}` and reading the coefficient
of `z^{2m}`: `2(m+1)(2m+1)a_{m+1} + [2m(2m-1) + 2m - lambda^2]a_m = 0`, and
`2m(2m-1)+2m = 4m^2`, giving `a_{m+1} = a_m(lambda^2 - 4m^2)/((2m+2)(2m+1))`,
`a_0 = 1`. Substituting `y = sum b_m z^{2m+1}`: the bracket is
`(2m+1)2m + (2m+1) = (2m+1)^2`, giving
`b_{m+1} = b_m(lambda^2-(2m+1)^2)/((2m+3)(2m+2))`, `b_0 = lambda`. Telescoping
with `prod_{i<m}(2i+2)(2i+1) = (2m)!` and `prod_{i<m}(2i+3)(2i+2) = (2m+1)!`
gives exactly 04's two products. **CONFIRMED**, both cases.

*Measured against my operator* (which never uses the closed form):

    e in {1,3,5,7},  k = 1..25,  every m in the computed support (N = 170)
    ----> 0 mismatches.

So Theorem 1 holds for `e = 1` and `e = 5, 7` as well, as 04 claims.

Two consequences 04 draws, both **CONFIRMED**: `c_{k,j'(k)} = 1` (`k` even) or
`k/e` (`k` odd), which is a 2-adic unit for odd `e` -- this *proves* what 01
and I could only measure (my Part One item 9); and `3 | k` terminates the
product (Chebyshev), which is why `U_2(t^-3)` and `U_2(t^-6)` are finite.

## P2-2. THEOREM 2 and LEMMA A

*Theorem 2.* `v_2((2m)!) = 2m - s_2(2m) = 2m - s_2(m)` and
`v_2((2m+1)!) = 2m+1 - s_2(m) - 1 = 2m - s_2(m)`; `e` odd drops out; the
numerator factors as `prod (k - e xi_i)(k + e xi_i)`. Hence
`v_2 = Sigma_m - 2m + s_2(m)` in **both** parity cases (the odd case's extra
`v_2(k/e) = 0`). **CONFIRMED.** Machine check against my operator, `k <= 60`,
full support to `N = 300`: 0 mismatches, and the "coefficient vanishes" cases
agree exactly with `c = 0`.

*Lemma A.* The four sub-cases, each re-derived:

- `k` odd: `k^2 = e^2(2i+1)^2 = 1 mod 8`, so every factor has `v_2 >= 3`,
  `Sigma_m >= 3m`, `v_2 >= m + s_2(m)`. **Correct.**
- `k = 2 kappa`: `k^2 - 4e^2i^2 = 4(kappa^2 - e^2i^2)`, so
  `v_2 = sum_{i<m} v_2(kappa^2 - e^2 i^2) + s_2(m)`. **Correct.**
- `kappa` even (`4 | k`): odd `i` give 0; even `i` (including `i = 0`, term
  `2 v_2(kappa) >= 2`) give `>= 2`; there are `ceil(m/2)` of them, so the sum is
  `>= 2 ceil(m/2) >= m`. **Correct.**
- `kappa` odd (`k = 2 mod 4`): even `i` give 0; odd `i` give `>= 3` by the same
  mod-8 argument; `floor(m/2)` of them, so `v_2 >= 3 floor(m/2) + s_2(m)`. For
  `m` even that is `>= 3m/2`; for `m` odd it is `>= m` iff
  `(m-3)/2 + s_2(m) >= 0`, which at the only doubtful point `m = 1` reads
  `-1 + 1 = 0`. **Correct** (04 states this case; I checked `m = 1` explicitly
  because it is the one that is tight).

Machine check, `k <= 600`, `m <= 80`: **0 violations of `v_2 >= m`**; **0
violations of the `m + s_2(m)` refinement** on `k` odd or `4 | k`; exactly
**150** tight pairs, **all** of shape `k = 2 mod 4, m = 1` -- 04's count and
characterisation, reproduced. **LEMMA A: CONFIRMED.**

This is the tail estimate my Part One sec. 3.3 left open. It is now closed.

## P2-3. THEOREM 3, line by line

*Increment formula.* `floor((n+3m-1)/3) = floor((n-1)/3)+m` and
`(n+3m) mod 2 = (n+m) mod 2`, so `a(n+3m)-a(n) = m + [((n+m) mod 2)-(n mod 2)]`,
`= m` (`m` even), `m+1` (`m` odd, `n` even), `m-1` (`m` odd, `n` odd).
**CONFIRMED**, including that it survives at `n = 2` (`a(2) = 0 = floor(1/3)+0`)
and fails at `n = 3` (`a(3) = 0` but the formula gives 1).

*(A3b), the tail.* Case coverage checked exhaustively. For `k > 3` the possible
`j'` are `j' = 2` (from `k = 4`), `j' = 3` (from `k = 6` only -- the odd
alternative is `k = 3`, excluded), and `j' >= 4`. So:

- `j' = 3`: only `k = 6`; `c_{6,m} = 0` for `m >= 2`, and `m = 1` gives
  `a(6)-a(3) = 1 = v_2(c_{6,1})`. Equality. **Correct**, and this is the only
  place the increment formula's failure at `n = 3` could have bitten.
- `m` even: increment `m`, Lemma A gives `>= m`. **Correct.**
- `m` odd, `j'` odd: increment `m-1 < m`. **Correct.**
- `m` odd, `j'` even: increment `m+1`; the two `k` with this `j'` are `2j'`
  (`= 0 mod 4`, since `j'` even) and `2j'-3` (odd), and Lemma A's refinement
  gives `>= m + s_2(m) >= m+1` for **both**. **Correct**, and this is the
  keystone: the two tightness sets are exactly complementary, as 04 says.

*(A3a), the mod-6 tables.* I recomputed both, entry by entry, from
`floor((6q+s)/3) = 2q + floor(s/3)`:

| `r` | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|---|
| `k = 2c` even: `d` | `2q` | `2q-1` | `2q+1` | `2q` | `2q+1` | `2q+1` |
| `k = 2c-3` odd: `d` | `2q` | `2q-1` | `2q+1` | `2q` | `2q+1` | `2q+1` |

Both **CONFIRMED**, and they are indeed identical. The `q = 0` exclusions check
out: `r in {0,1,3}` with `q = 0` means `c in {0,1,3}`, i.e. `k in {0,2,6}` (even
branch) or `k in {-3,-1,3}` (odd branch), and all are excluded by `k > 3` except
`k = 6`, which 04 handles by `a(3) = 0` from (A1), giving `d(6) = 1`. Likewise
`d(4) = a(4)-a(2) = 1`. Spot-checks: `d(8) = 2-1 = 1`, `d(10) = 3-2 = 1`,
`d(12) = 3-1 = 2`, `d(14) = 4-3 = 1`, `d(5) = 2-1 = 1`, `d(7) = 3-2 = 1`. All
match the tables.

*Divergence.* `d >= 2q-1 = 2 floor(c/6)-1` and `c = j'(k) >= k/2`, so
`d(k) >= 2 floor(k/12)-1 -> infinity`. **CONFIRMED.**

*One cosmetic imprecision.* "the only smaller values of `c` in those classes are
`c = 3` ... and `c = 1`" omits `c = 0` (`r = 0, q = 0`). It is vacuous (`k = 0`),
so nothing depends on it.

*Machine confirmation with MY operator's coefficients* (not 04's closed form),
`4 <= k <= 100`, full support at `N = 300`:

    d(k) >= 1 : no violations;  minimum attained at m = 0 for EVERY k;
    d(4..24) = 1,1,1,1,1,2,1,1,2,3,1,2,3,3,2,3,3,4,3,3,4   (= 04's row, = my Part One row)
    d(100) = 17   and   d(k) = a(k) - a(j'(k)) for every k in 4..100.

**THEOREM 3: CONFIRMED.**

## P2-4. THEOREM 4

`j'(6) = 3` and `3 + e = 6`, so `k = 6` is a self-loop of the support map; my own
operator gives `U_2(t^-6) = t^-3 + 2 t^-6` exactly, so `v_2(c_{6,1}) = 1`. The
(A3) constraint at `(k,j) = (6,6)` reads `a(6) - a(6) + 1 >= d(6)`: **the weight
cancels identically**, so `d(6) <= 1` for every weight whatsoever. Hence
`max(1, gamma k)` is achievable iff `6 gamma <= 1`. **CONFIRMED.**

This is strictly better than what I produced in Part One. My Bellman-Ford found
`max(1,2k/11)` and `max(1,k/5)` infeasible and `max(1,k/6)` feasible; Theorem 4
*explains* all three with one coefficient (`2*6/11 = 12/11 > 1`, `6/5 > 1`,
`6/6 = 1`). **My Part One item 12 ("threshold in `[1/6, 2/11)`") should be
superseded by "the threshold is exactly `1/6`".**

The orbit remark also checks: `succ(3) = 3` (fixed point) and
`succ(1) = 2, succ(2) = 1` (2-cycle), so there are exactly two attractors below
`mu(P) = 3`. **CONFIRMED.**

## P2-5. The 18-row table and the strictness audit

Rows I could check at source, all **CONFIRMED**:

- **Def. 6.3's strict `>` is a source infelicity.** I verified this at source:
  KMU sec. 2.1, for `A = R_q((t))`, defines
  `A^m(b) = {sum a_k t^{-k} : v_pi(a_k) >= (k-b)/m for k > 0}` -- **non-strict**.
  Def. 6.3's `B^m` writes `>`, and with `>` its own "formal basis" claim is
  literally false (`pi^{a(k)/m_P}t^{-k}` sits exactly on the boundary). 04's
  adoption of `>=` is the right repair, and the defect is p-uniform. (I flagged
  the same thing in Part One sec. 1.2 without tracing it to sec. 2.1.)
- **Lemma 7.1's strictness is self-supplying.** Verbatim: *"If `J != I^{<r}(Psi)`,
  then the inequality is strict for `k = n`, since `e_{j_n} not in I^{<r}(Psi)`."*
  Nothing is consumed. **CONFIRMED.**
- **Def. 7.3 verbatim**: (1) `v_pi eps(e_i) > v_pi Psi(e_i)` for `i in I^{<r}(Psi)`;
  (2) `v_pi eps(e_i) >= r` for `i not in I^{<r}(Psi)`. **CONFIRMED.**
- **The Def. 7.3(1) margin is p-independent.** Lemma 7.11 gives
  `v_pi(eps(e_{P,k})) >= kp/delta_P` against `v_pi(Theta~(e_{P,k})) = k(p-1)/delta_P`;
  margin `k/delta_P`, with no `(p-1)`. **CONFIRMED** -- this is 04's key
  observation and it is correct.
- **Def. 7.3(2) is where `d(k) >= 1` is consumed, non-strictly.** Because
  `I^{<r}(Psi) = {i : v_pi psi(e_i) < r}` uses a strict `<`, a column of slope
  *exactly* `r` is already outside `I^{<r}`, and only `>= r` is asked of it.
  With `m_{e,P} = 1/e` the slope is `d(k) e`, so `d(k) >= 1` is exactly enough.
  **CONFIRMED**, and it agrees with my own Part One sec. 2.5.
- **Cor. 7.14's cancellation, verbatim**: *"the Newton polygon `NP^{<r}_{pi_q}(phi)`
  is the concatenation of `NP^{<r}_{pi_q}(rho)` with `r_0+r_1+r_infty-|S|`
  segments of slope 0 ... The result follows by canceling out these extra
  slope-0 segments."* With Lemma 7.12's `N = g-1+r_0+r_1+r_infty`, the leftover
  is `g-1+|S|`. **CONFIRMED.** Note the `e_P`-independence needs no
  Riemann-Roch at all: `r_1` cancels identically whatever its value. (04's RR
  step is nonetheless correct: `deg D = deg eta > 2g-2` by (8), so
  `h^0(D) = deg eta - g + 1 = N`. I verified this in Part One sec. 2.5.)
- **sec. 7.2, both halves.** (i) An eigenspace regrading gives weights affine on
  each class mod 3; `a(1),a(4),a(7),a(10) = 0,1,3,3` is not arithmetic
  (differences `1,2,0`) -- and it is still not arithmetic without the (A1)
  override (`1,1,3,3`). (ii) The mod-6 splitting is not `sigma`-equivariant:
  `sigma(t^6) = t^{12}G^6 = t^{12}(1+2x^3)^2 = t^{12} + 4t^9 + 4t^6`, and `t^9`
  is not in `R_q((t^6))`; whereas `sigma(t^3) = t^6(1+2x^3) = u^2+2u` is in
  `R_q((u))`. **CONFIRMED**, so R3 really does not dissolve.
- **sec. 7.3's "no admissible weight makes `A^{m,*}` a ring".** Closure under
  multiplication needs `a(i+j) <= a(i)+a(j)`; with `a(3) = 0` that gives
  `a(k+3) <= a(k)`, contradicting `a(k) -> infinity`. **CONFIRMED.** And KMU's
  own `B^m` is not a ring either (`u^{-1}` fails `v_pi > 1/m_P`), so 04 is right
  that this is a pre-existing feature, not a new cost.

## P2-6. **GAP: the Lemma E coverage claim**

This is the one substantive finding of Part Two.

*The reduction itself is correct.* `a - a_KMU in {0,1}` gives
`pi^{1/m_P}A^m(KMU) subset A^{m,*} subset A^m(KMU)`; writing the Prop. 5.11
twist as `a^{-1} = 1 + pi y`, the extra term carries `v_pi >= 1`, which covers
the `1/m_P` penalty **iff `m_P >= 1`**. With `m_{e,P} = 1/e` that is `e <= 1`.
All **CONFIRMED**.

*What is wrong is the coverage sentence*: **"and Thm. 7.13's proof needs
`r <= e`. So capping `e <= min(1, v_pi(p))` ... restrict[s] the general Thm 7.13
to `r <= 1`. KMU Theorem 1.1 takes `r in [0,1]`, so it is untouched."**

The `r` in Thm. 7.13 / Cor. 7.14 / sec. 7.4 is the **`pi_q`-adic** truncation
parameter; Theorem 1.1's `r` is the **`q`-adic** one. They are not the same
scale. Three independent confirmations that the conversion factor is `v_pi(p)`:

1. *Definitions.* The glossary: `pi_q = pi^{v_p(q)}`. Hence
   `v_{pi_q}(x) = v_pi(x)/v_p(q) = v_pi(p) v_p(x)/v_p(q) = v_pi(p) * v_q(x)`.
2. *The same polygon, both ways.* sec. 1.2 gives `HP_q(rho^ext_P)` slopes
   `{i/d_P}`; Def. 7.7 gives `HP_{pi_q}(rho_P) = HP(delta_P)` slopes
   `{k(p-1)/delta_P}`. Ratio `= d_P(p-1)/delta_P = p^{n-1}(p-1) = v_pi(p)`.
3. *The window count.* Thm. 7.10 uses `deg L(rho^ext_P,s) = d_P - 1`; truncating
   `HP(delta_P)` at `pi_q`-slope `< e = v_pi(p)` keeps `k(p-1)/delta_P < p^{n-1}(p-1)`,
   i.e. `k < p^{n-1} delta_P = d_P`, i.e. exactly `d_P - 1` slopes -- so
   `pi_q`-adic `e = v_pi(p)` corresponds to `q`-adic `r = 1`.

Also verbatim in the source: Cor. 7.14 reads *"Let `r <= v_pi(p)`"*, and Thm.
7.13's proof reads *"Since `r <= v_pi(p)`, we may **enlarge `e`** as necessary
and assume that `r <= e`"* -- KMU **enlarge** `e` toward `v_pi(p)` precisely to
reach `q`-adic `r = 1`. 04's cap moves `e` the other way.

**Consequence.** At `p = 2` with `rho` of order `2^n`, `R = Z_2[zeta_{2^n}]` is
totally ramified of degree `2^{n-1}`, so `v_pi(p) = 2^{n-1}` and the cap
`e <= 1` covers only

>  `q`-adic `r <= 1/v_pi(p) = 2^{1-n}`.

- `n = 1` (order-2 characters): `v_pi(p) = 1`, so `e <= 1 = v_pi(p)` is **no
  restriction at all** and the theorem-candidate's `r in [0,1]` stands.
- `n = 2` (order 4): `r <= 1/2`. `n = 3`: `r <= 1/4`. And so on.

**And the cap is structural, not an artifact of `m_{e,P} = 1/e`.** For any
choice `m_{e,P} = M >= m_{pi,P}`, the `eta(P) = 1` columns have slope `d(k)/M`
and Def. 7.3(2) needs `d(k)/M >= r` for every `k > mu(P)`. **04's own Theorem 4
gives `d(6) <= 1` for every weight**, so `r <= 1/M`; and Lemma E's reduction
needs `M >= 1`. Hence `r <= 1` (`pi_q`-adic) on this route, whatever `M` is.
Theorem 4 and the Lemma E reduction are in direct tension.

**What the theorem-candidate should say.** Either (i) restrict to `r in [0,
2^{1-n}]` (which is `r in [0,1]`, i.e. everything, for order-2 characters), or
(ii) prove Lemma E rather than reduce it to KMU's assertion, or (iii) find a
reduction whose penalty is `<= 1/M` with `M` allowed below 1. On (iii) I note
without developing it that comparing `A^{m,*}` (weight `a`, parameter `m_P`)
against `A^{m'}(KMU)` (weight `a_KMU`, parameter `m'_P = m_P/2`) also gives a
containment, since `a <= 2 a_KMU` for `k >= 4`; that would relax the cap to
`e <= v_pi(p)/2`, i.e. `q`-adic `r <= 1/2` uniformly in `n`. I did not check
whether the rest of the argument survives that substitution.

This does **not** touch Theorems 1-4 or the local estimate. It touches only the
scope of the final statement in sec. 9.

## P2-7. sec. 6 (the extremal weight) and the Note-7 refutations

*The orbit sum.* `a*(k) = sum_{i>=0} d*(succ^i(k))` with `d*(k) = max(1,k/6)`
for `k >= 4`, `0` for `k <= 3`. Computed independently:

    a*(1..20) = 0,0,0,1,2,1,19/6,7/3,5/2,11/3,5,3,9/2,11/2,5,5,13/2,11/2,49/6,7
    a*(48) = 15,   a*(200) = 68,   a*(200)/200 = 0.34

which is **exactly** 01's published LP-minimal prefix and `a*(48) = 15`, and 04's
`a*(200) = 68`. The closed form `(k - k_T)/3 + O(k)/2 + s(k_T)` agrees with the
orbit sum for `7 <= k <= 400`. **CONFIRMED.** This also confirms the coordinator's
Note-7 remark that the LP-minimal weight is the shortest-path potential -- it is
the orbit sum, and my Part One Bellman-Ford solution (the pointwise-*maximal*
one) dominates it everywhere, as it must.

*The Main Lemma.* Verified `j < 400, m < 70`: **0 violations, minimum slack 0 at
`(j,m) = (1,1)`** -- 04's own reported figures. I also verified the bridging
claim that makes it (A3b): `R*(j,m) = min(v_2(c_{2j,m}), v_2(c_{2j-3,m}))`, no
mismatches for `j < 60, m < 20`. And `s_2(2n-1) = s_2(n) + v_2(n)` holds for
`n <= 5000`; the one-line proof given (`2n-1 = 2^{w+1}(n'-1) + (2^{w+1}-1)`) is
correct. **CONFIRMED.**

*Note-7 refutation 1* (`v_2(c_{k,j}) = m + v_2(binom(-k/3,m))`). My own numbers:

| `k` | truth `v_2`, `m = 0,1,2` | Note-7 guess | agree |
|---|---|---|---|
| 4 | 0, 3, 3 | 0, 3, 3 | yes |
| 5 | 0, **3**, 4 | 0, **1**, 4 | **no** |
| 7 | 0, **2**, **5** | 0, **1**, **2** | **no** |

04's witness (`k = 5`, `m = 1`: guess 1, truth 3) is exact. **The refutation
CONFIRMED**, and it fails at `k = 7` too.

*Note-7 refutation 2* (`m = 2|j-k|/3`). At `k = 4, j = 5` this is `2/3`, not an
integer. The correct index is `m = (j - j'(k))/e = (5-2)/3 = 1`. **CONFIRMED.**

*Note-7 item "don't hunt for a pretty closed form"*: 04's "PARTLY REFUTED" is
right -- two closed forms exist and I verified both.

## P2-8. The self-checking artifact

I compiled `noh_wt_certificate.rs` standalone with `rustc --edition 2024` (it
has no dependencies beyond `std`, so this is faithful) and ran it: **exit 0**,
with the counts `440 / 352 / 41600 / 397` and `150` tight Lemma-A pairs -- the
`150` matching my own independent census.

Then I mutation-tested it six ways:

| mutation | exit | caught by |
|---|---|---|
| M1 `a(k) -> floor((k-1)/3)` (04's claim) | **1** | `(A3) d(5) = 0 < 1` |
| M2 valuation formula `+1` (04's claim) | **1** | check [2] |
| M3 `j'(k)` odd branch `-> (k+1)/2` (a plausible real error) | **1** | ground-truth row `U_2(t^-3)` |
| M4 same error injected into **both** the product and the ODE route | **1** | ground truth **and** check [2] |
| M5 M4 with the ground-truth block deleted | **1** | check [2] alone |
| M6 error injected consistently into product, ODE **and** valuation | **1** | Lemma A's arithmetic (`v_2(c_{2,2}) = 1 < 2`) |

So the gate is real: the exit status depends on the finding, it asserts a
minimum number of examined pairs (`pairs >= 400`, `vpairs >= 300`,
`la >= 40_000`, `cols == 397`), and it survived every attempt I made to make it
pass over a wrong statement. **CONFIRMED as a non-vacuous checker.**

**One wording GAP.** sec. 0's table lists R4 (`noh_wt_certificate.rs`) as one of
"four independent routes" and the file's own comment calls the ODE recurrence
"an INDEPENDENT route ... [that] never forms the product above". It is not
independent: `c_ode` iterates `c *= (lambda^2 - sub)/((2i+2)(2i+1))`, which is
the same product as `c_closed` evaluated in a different association order.
Check [1] therefore verifies rational arithmetic, not mathematics. The
certificate's **only** binding to the actual operator `U_2` is the six
hard-coded ground-truth rows (11 coefficients, `k in {3,...,8}`, `m <= 2`);
breadth comes from checks [2]/[3], whose content is arithmetic. That is not
fatal -- M5/M6 show those checks do catch real errors -- but the "four
independent routes" claim should be three, and I recommend adding the series
solve (R1) to the example so the artifact itself pins the closed form to the
operator. My own operator supplies that pinning here (`e in {1,3,5,7}`,
`k <= 25`, every `m`; and `e = 3`, `k <= 60`, full support for the valuation
identity).

## P2-9. Recommendations to the coordinator

1. **Scope the theorem-candidate.** Replace "for every `r in [0,1]`" by
   "`r in [0, 2^{1-n}]` for a character of order `2^n`" (equivalently: the full
   `r in [0,1]` for order-2 characters), or prove Lemma E outright. Flag
   explicitly that this cap follows from 04's *own* Theorem 4 plus the Lemma E
   reduction, so it cannot be dodged by re-choosing `m_{e,P}`.
2. **Retire my Part One item 12's interval.** The threshold is exactly `1/6`;
   Theorem 4's one-coefficient certificate replaces the LP.
3. **Withdraw "four independent routes"** in 04 sec. 0 and in the example's
   header comment, or make R4 genuinely independent by adding the series solve.
4. Everything else in 04 that I audited stands, and Theorems 1-4 close the gap
   my Part One sec. 3.3 identified as "still open and still the hard part".

## P2-10. Reproduction (Part Two)

Scratchpad `ws20/code/` (not committed), all new this session:
`audit04.py` (Theorems 1-4 against my own operator: closed form for
`e in {1,3,5,7}`, valuation identity, Lemma A census, weight sweep, self-loop),
`audit04b.py` (orbit-sum `a*`, its closed form, the Main Lemma, `R*` vs the
valuation identity, the Note-7 witnesses); `ws20/rs/` (standalone `rustc` build
of the certificate plus the six mutants). Longest run 48 s; total well inside
the 5-minute / 2 GB budget.

---
---

# PART THREE -- Audit of `05-lemma-b-and-kmab.md`

Added 2026-08-20, after `05-lemma-b-and-kmab.md` (758 lines) landed. Sources
I fetched myself for this part: **KLW = arXiv:2010.01130** and
**SY = arXiv:1708.03036** (both new to me), plus re-reads of KM-ab
(arXiv:2006.04936) sections 1.1, 3.1, 3.4, 4.1.1, 4.2, 7.2, 7.3 and KMU-I
section 4.1. All computation below is my own, written this session.

## VERDICT TABLE (Part Three)

| # | claim (05) | verdict |
|---|---|---|
| P3-1 | Lemma B, stage-by-stage ramification bookkeeping | **CONFIRMED** -- every index re-derived independently |
| P3-2 | `z^e`'s other ramification point lands over `infinity`, where `sigma(t_P) = t_P^p` index-independently; no new Type-2 point; no collision with `S` | **CONFIRMED** from **two** sources (KMU-I sec. 4.3 and KM-ab sec. 3.4) |
| P3-3 | RH eq. (8); `r_1 e = deg(eta)`; `mu(P) = e_P = 3`; `N` unchanged | **CONFIRMED**, including the KM-ab/KMU off-by-one in the `mu` convention |
| P3-4 | the `c^{p-1} = 1` obstruction: genuinely required, and KMU-I's phrasing is genuinely wrong at every `p` | **CONFIRMED** (with one nuance: KM-exp is correct, so nothing downstream is wrong) |
| P3-5 | `3 \| q-1` is necessary for a *degree-3* auxiliary map | **CONFIRMED** by my own independent enumeration over `GF(2^a)`, `a <= 6` |
| P3-6 | base-change invariance of `NP_q`, `HP_q`, `Omega_rho` (proof, not statement) | **CONFIRMED** -- the proof is correct, including the trap it navigates; one unstated hypothesis noted |
| P3-7 | the explicit instance `eta(z) = ((1+omega)z^{q-1} + omega)^3 + 1` | **CONFIRMED** symbolically **and** numerically; every number matches |
| P3-8 | the extension-free `e = q-1` fallback | **CONFIRMED as geometry**, but it is **not** a drop-in: it moves `mu(P)` to `q-1` and voids 04's Theorem 3 |
| P3-9 | KM-ab table row 7 (Lemma 3.1) | **CONFIRMED** verbatim; KM-ab's hypothesis is *weaker* than Lemma B delivers |
| P3-10 | **KM-ab table row 11: the weight/operator dictionary `b(-k) = a_KMU(k)`** | **CONFIRMED -- the chain is NOT severed.** Same `nu`, same weight, same estimate; 04's repair transports verbatim |
| P3-11 | KM-ab rows 21/25 (Prop. 7.2/7.4): no eigenspace decomposition needed; similarity argument complete | **CONFIRMED** from source, including that only `b(n) >= m` and "slope `>= 1`" are consumed |
| P3-12 | KM-ab row 15 (`-q(e,i) <= a(p-1)`) refuted | **CONFIRMED** -- my witnesses are identical to 05's, and the weaker `<= ap` also fails |
| P3-13 | KM-ab row 16 ((18) feasibility, supplied by 05) | **CONFIRMED** -- `omega <= a(p-1)-1` verified exhaustively, and the source really does not prove it |
| P3-14 | 05's dependency graph, TARGET B line: Lemma E "with no loss for `r in [0,1]`" | **GAP (inherited)** -- 05 did not absorb Part Two; the correct bound is `r <= 2^{1-n}` |
| P3-15 | reconciliation of Part Two's cap with 05's route claim | see P3-15 below: **the cap does not touch the charter's primary target** |

**Bottom line.** Lemma B is sound; I re-derived it and could not break it. The
one thing I was most worried about -- that KM-ab's weight and operator might not
correspond to 04's -- checks out exactly, so the repair transports. And 05's
best result is one it states almost in passing: **on the KM-ab route the
Lemma E gap, and with it my Part Two coverage cap, does not arise at all.**
That moves the charter's *primary* target off the capped route entirely.

---

## P3-1. Lemma B: the bookkeeping, re-derived

I worked the composition through myself before reading 05's table. Writing
`phi = g_1 o eta_0`, `g_1 = z^{q-1}`, `g_2` linear (`1, infinity` fixed,
`0 -> c`), `g_3 = z^e`, `g_4` linear (`infinity` fixed, `0 <-> 1`):

| stage | branch locus after it | the fibre that matters |
|---|---|---|
| `eta_0` | `Branch(eta_0) u eta_0(S) subset F_q^*` (by choice of coordinate) | -- |
| `g_1` | `{1} u {0, infinity}`; `g_1` tame since `q-1` is odd, totally ramified over `0, infinity` | `phi^{-1}(0) = eta_0^{-1}(0)`, **index exactly `q-1`** because `0 not in Branch(eta_0)`; `phi(S) = {1}` |
| `g_2` | `{c, 1, infinity}`; and `0` is **not** in it, because `g_2^{-1}(0) not in {0,1,infinity}` once `c != 0` | `0` is a clean (unramified) point of `g_2 phi` |
| `g_3` | `g_3({c,1,infinity}) u {0,infinity} = {c^e, 1} u {0, infinity}`, which is `{0,1,infinity}` **iff `c^e = 1`** | `(g_3 g_2 phi)^{-1}(0) = (g_2 phi)^{-1}(0)` with index `e * 1 = e`, uniformly, `deg(g_2 phi)` of them |
| `g_4` | `{0,1,infinity}` | `S`-fibre `-> 0`; the uniform-index-`e` fibre `-> 1` |

Each index I checked myself: `e_{eta}(P) = e_{eta_0}(P)` for `P in S`;
`e_{eta}(P) = e` for every `P` over `1`; `e_{eta}(P) = e(q-1)e_{eta_0}(P)` for
`P` over `infinity`. All odd, hence tame at `p = 2`. **CONFIRMED**, and note
the two places where the construction would silently fail if `g_2` were
omitted: `0` would be a branch point of `g_2 phi`, so the fibre over the final
`1` would have *mixed* index, and Prop. 4.3(2) would be false.

The fibre over the final `0` is a genuine mixture (the `S`-points with index
`e_{eta_0}`, the `eta_0^{-1}(0)` points with index `q-1` arriving via `c`, and
`e-2` unramified sheets from the other `e`-th roots of unity). That is fine --
KMU/KM-ab ask only `eta(S) = {0}` / `tau_i in eta^{-1}({0, infinity})`, never
that the whole fibre be `S`. 05 does not spell this out; it is worth a line in
the write-up because it is the first thing a referee will check.

## P3-2. Where the second ramification point of `z^e` goes. CONFIRMED, twice

`z -> z^e` ramifies exactly at `0` and `infinity`. `g_4` fixes `infinity`, so
the second one lands over `infinity`. 05's claim that this is harmless rests on
the local Frobenius being a pure power there, and I verified that statement in
**both** papers:

- **KMU-I sec. 4.3**, verbatim: *"Evidently, if `eta(P) = 0` or `infinity` then
  `sigma(t_P) = t_P^p`. The local Frobenius for `eta(P) = 1` is more
  complicated: `sigma(t_P) = ((t_P^{p-1}+1)^p - 1)^{1/(p-1)}`."*
- **KM-ab sec. 3.4**, verbatim: *"For `Q in X` with `eta(Q) in {0, infinity}`,
  we may take the local parameter at `Q` to look like `u_Q = t^{+-1/e_Q}`,
  where `e_Q` is the ramification index at `Q`. In particular, the Frobenius
  endomorphism sends `u_Q -> u_Q^q`. If `eta(Q) = 1`, we take the local
  parameter to look like `u_Q = (t-1)^{1/(p-1)}`. Thus, the Frobenius
  endomorphism sends `u_Q -> ((u_Q^{p-1}+1)^p - 1)^{1/(p-1)}`."*

The reason is exactly as 05 says and I re-derived it: `sigma(u_0) = u_0^p` is a
pure `p`-th power, so the unique `e_P`-th root congruent to `t_P^p` mod `p` is
`t_P^p` itself, **whatever `e_P` is**. Only over `1`, where
`sigma(u_1) = (u_1+1)^p - 1` is not a pure power, does the root extraction
produce the `(1+py)^{1/e_P}` factor -- the Type-2 operator. So ramification
over `0` and `infinity` is free, and the second ramification point creates no
new Type-2 point. **CONFIRMED.** It also does not meet `S`: `S` sits over `0`.

Note the second source (KM-ab) is the stronger evidence, because it writes the
`eta(Q) in {0,infinity}` case with a *general* `e_Q` in the parameter, whereas
KMU-I's phrasing could be read as assuming `e_P = 1` there.

## P3-3. RH, `mu(P) = e_P`, and `N`

Tame Riemann-Hurwitz for a map branched only over `{0,1,infinity}`:
`2g-2 = -2 deg + sum_Q (deg - r_Q)`, i.e.
`2(g-1) + r_0 + r_1 + r_infinity = deg(eta)` -- KMU-I (8) = KM-ab (4).
**CONFIRMED** (this is the third time I have re-derived it; it is index-free).
With all points over `1` of index `e`, `r_1 e = deg(eta)`.

`mu(P) = e_P`: KMU-I Prop. 4.10's proof, verbatim, *"The kernel is precisely
the global sections of the line bundle `L(D)`, where `D = sum_{eta(P)=1}
(p-1)P`"*, so `D = eta^*(1)` exactly when `mu(P) = e_P`, whence
`deg D = deg(eta)` and (since `deg D = deg eta > 2g-2` by (8))
`N = h^0(D) = deg(eta) + 1 - g = g-1+r_0+r_1+r_infinity`. **CONFIRMED**, and
`e_P`-free.

**One convention check that 05 got right and is easy to get wrong.** KM-ab's
truncation function (33) is `mu(Q) = 1` for `eta(Q) in {0,infinity}` and
`mu(Q) = p` for `eta(Q) = 1` -- i.e. `p`, not `p-1`. KMU-I (11) has `p-1`.
They denote the same truncation (drop poles of order `<= p-1 = e_P`), one
counting the first *kept* index and the other the last *dropped* one. 05's
table renders this correctly ("`mu(Q) = p` (33), i.e. drop poles `<= p-1`").
With `e_P = 3` both read "drop poles of order `<= 3`", which is 04's (A1).

## P3-4. The `c^{p-1} = 1` obstruction. CONFIRMED, with a nuance

After `g_2` the branch locus is `{c, 1, infinity}`; after `g_3 = z^{p-1}` it is
`{c^{p-1}, 1, infinity} u {0, infinity}`. For a Belyi map one needs
`c^{p-1} in {0, 1, infinity}`, and `c not in {0, infinity}` forces
**`c^{p-1} = 1`**. KMU-I's *"a linear transformation fixing 1 and infinity and
sending 0 to any other `F_q`-rational point"* therefore over-states the freedom:
with a generic `c` the composite has a **fourth** branch point, `eta` is not
Belyi, `U = eta^{-1}(V)` is not etale over `V`, and sec. 4.2's lifting has no
basis. **CONFIRMED as a genuine requirement and a genuine misstatement.**

Two nuances 05 states but that the write-up should keep together:

- **KM-exp is correct.** Its Lemma 3.1 puts the branch points at `{1, 2,
  infinity}`, i.e. `c = 2`, and `2^{p-1} = 1` in `F_p` by Fermat with `2 != 1`
  for `p >= 3`. So nothing in the published odd-`p` mathematics is wrong; the
  defect is confined to KMU-I's paraphrase, and the repair is one word
  (`c in mu_{p-1}(F_q) \ {1}`, nonempty exactly because `p >= 3`).
- **At `p = 2` the point "2" *is* the point `0`**, so even the repaired
  placement step is empty. This is a third independent degeneration, alongside
  `z^{p-1} = id` and the RH obstruction to `e_P = 1` -- and all three are the
  single fact `mu_{p-1} = {1}`. That framing is correct and is the clearest
  statement of the geometric half of the `p = 2` problem I have seen in this
  project.

## P3-5. `3 | q-1` is necessary at degree 3. CONFIRMED independently

I did my own classification rather than re-running 05's. The theory first: a
tame degree-3 self-map of `P^1` in characteristic 2 has `sum (e-1) = 4` by RH,
and every index must be odd (`e = 2` is wild), so `e in {1,3}` and there are
exactly **two** totally ramified points; hence `h = mu o z^3 o nu` with
`mu, nu in PGL_2`. I then enumerated, over `GF(2^a)` with exact arithmetic, all
`h = mu(((z-alpha)/(z-beta))^3)` with `mu(0) = 1`, `mu(infinity) in {0,
infinity}`, and checked all five conditions Lemma B needs of the auxiliary
stage (`h(1) = 0`; `h({0,1,infinity}) subset {0,1,infinity}`; `h^{-1}(1)` a
single point `alpha` of index 3 with `alpha not in {0,1,infinity}`):

```
  a=1 q= 2  3|q-1: False  #maps=  0  alphas=[]        mu_3\{1}=[]
  a=2 q= 4  3|q-1: True   #maps=  6  alphas=[2, 3]    mu_3\{1}=[2, 3]
  a=3 q= 8  3|q-1: False  #maps=  0  alphas=[]        mu_3\{1}=[]
  a=4 q=16  3|q-1: True   #maps=  6  alphas=[6, 7]    mu_3\{1}=[6, 7]
  a=5 q=32  3|q-1: False  #maps=  0  alphas=[]        mu_3\{1}=[]
  a=6 q=64  3|q-1: True   #maps=  6  alphas=[58, 59]  mu_3\{1}=[58, 59]
```

**The degree-3 auxiliary map exists over `F_{2^a}` iff `3 | q-1` iff `a` is
even, and the ramification point over `1` is always a primitive cube root of
unity** -- 05's conclusion exactly. (My map count is 6 where 05 reports 8; that
is a normalization difference in how the Mobius factor is parametrized, and the
two load-bearing outputs -- the existence pattern and the `alpha` set -- agree
on every field.) I also confirm 05's own caveat that a *higher-degree*
auxiliary map over a field with `3 nmid q-1` is **OPEN**, and agree it is moot
given P3-6.

## P3-6. Base-change invariance. The proof is correct, and it navigates a trap

This is the load-bearing one, so I audited each half.

*Newton side.* `H^1_c(X_{F_q-bar}, F_rho)` is geometric, hence unchanged, and
`Frob_{q^m} = Frob_q^m`, so the inverse roots become `alpha_i^m`. Then
`v_{q^m}(alpha_i^m) = v_p(alpha_i^m)/v_p(q^m) = m v_p(alpha_i)/(m v_p(q))
= v_q(alpha_i)`. The multiset of normalized valuations is therefore identical
and `NP_q` is unchanged **as a polygon**. **CONFIRMED.**

*Hodge side -- and here is the trap.* `HP(rho)` has length
`2(g-1+m) + sum (s_{tau_i} - 1)` and `m` is "the number of points where `rho`
ramifies". If `m` counted **closed** points of `X/F_q`, base change would
change it (a closed point of degree `d` splits into `gcd(d,m)` points), and
`HP` would *not* be invariant. 05 asserts the multiset is indexed by the
**geometric** points and justifies it by the degree count; I checked that the
justification actually forces the reading:

    2(g-1+m) + sum_i (s_i - 1)  =  2g - 2 + m + sum_i s_i
                                =  -chi_c(U, F_rho)   (Grothendieck-Ogg-Shafarevich, rank 1)

and GOS sums over **geometric** points. So `m` is the geometric count, the
`s_i` are the geometric Swan conductors, and both are invariant under an
unramified base change. **CONFIRMED**, and the point is real: this is the one
step where a careless reading would make Lemma B's side condition *not* free.

*`Omega_rho`.* `epsilon_Q` is defined (KM-ab sec. 1.1, read at source) as the
integer in `[0, q-2]` representing `e_Q/(q-1)`, and
`omega_Q = sum` of its base-`p` digits. Over `F_{q^m}`,
`epsilon' = epsilon (q^m-1)/(q-1) = epsilon(1 + q + ... + q^{m-1})`, and since
`epsilon <= q-2 < q` the `m` summands occupy **disjoint digit blocks with no
carries**, so `epsilon'` has exactly `m` copies of `epsilon`'s digits:
`omega' = m omega`, `a' = ma`, hence
`Omega' = (1/(m a (p-1))) sum m omega = Omega`. **CONFIRMED.**

*One unstated hypothesis.* The reduction needs `rho' = rho|_{pi_1(X_{F_{q^m}})}`
to remain non-trivial, which can fail for a character pulled back from
`Gal(F_q-bar/F_q)`. It cannot fail here: `rho` is wildly ramified at some
point, and ramification is geometric. Worth one clause in the write-up.

## P3-7. The explicit instance. CONFIRMED symbolically and numerically

`eta(z) = ((1+omega)z^{q-1} + omega)^3 + 1` with `omega` a primitive cube root
of unity is exactly `g_4 g_3 g_2 g_1` with `c = omega`, `g_2(z) = (1+omega)z +
omega`, `g_4(z) = z+1`. Writing `P = (1+omega)z^{q-1} + omega`:

- `eta - 1 = P^3` in characteristic 2, and `P` is separable (`P(0) = omega != 0`
  kills the only candidate common root of `P` and `P' = (1+omega)z^{q-2}`), so
  the fibre over `1` is `q-1` distinct points **each of index exactly 3**, and
  none is `0` (`P(0) = omega`), `1` (`P(1) = 1`) or `infinity`.
- `eta = 0` iff `P in mu_3`: `P = 1` gives `z^{q-1} = 1`, i.e. `F_q^*`, which is
  where `S` sits (so `eta(S) = 0`); `P = omega` gives `z = 0` with multiplicity
  `q-1`; `P = omega^2` gives `q-1` further simple points. Hence
  `r_0 = 2q-1`.
- `eta^{-1}(infinity) = {infinity}`, index `3(q-1)`, `r_infinity = 1`.
- `sum (e-1) = 2(q-1) + (q-2) + (3(q-1)-1) = 6q-8 = 2 deg(eta) - 2`: **RH is
  saturated by the three fibres**, so there is no ramification anywhere else
  and `eta` really is Belyi.
- (8): `2(0-1) + (2q-1) + (q-1) + 1 = 3(q-1) = deg(eta)`, and `r_1 * 3 = deg`.

Machine check over `GF(4)` and `GF(16)` reproduces every number 05 reports
(`q=4`: `deg 9`, `r_0=7, r_1=3, r_inf=1`, `sum(e-1)=16=2deg-2`;
`q=16`: `deg 45`, `r_0=31, r_1=15`, `sum(e-1)=88`). **CONFIRMED.**

## P3-8. The `e = q-1` fallback: geometry CONFIRMED, but it is not free

05's observation is right and I verified it in P3-1: after Step 1 *every* point
of `phi^{-1}(0)` already has index exactly `q-1`, so deleting `g_2, g_3` and
applying `g_4` alone gives a tame Belyi map with `eta(S) = {0}` and uniform
index `q-1` over `1`, with no root-of-unity condition. **CONFIRMED** (needs
`q >= 4` so that `q-1 > 1`).

But the write-up should not present it as an equal alternative:

- `mu(P) = e_P = q-1`, so 04's (A1) becomes `a(k) = 0` for `k <= q-1` -- a much
  larger truncation, and the `N`/`D` bookkeeping changes shape (though it still
  cancels, by P3-3).
- 04's Theorems 1, 2 and Lemma A do hold for every odd `e` (I verified Theorem 1
  at `e = 1, 3, 5, 7` in Part Two), and Theorem 4's threshold generalizes to
  `1/(2e)`; but **Theorem 3's mod-6 case analysis is `e = 3`-specific** and
  would have to be redone mod `2e` -- for a field-dependent `e`, i.e. once per
  `q`. That is a research task, not a substitution.

So 05's own conclusion ("since the extension is free, take `e = 3`") is the
right call, and the fallback should be recorded as insurance, not as a route.

## P3-9 / P3-10. The KM-ab rows that carry the theorem

**Row 7, Lemma 3.1.** Verbatim at source: *"After increasing q, there exists a
tamely ramified morphism `eta : X -> P^1_{F_q}`, ramified only above 0, 1, and
`infinity`, such that `tau_1, ..., tau_m in eta^{-1}({0, infinity})` and each
`P in eta^{-1}(1)` has ramification index `p-1`. Proof. This is [15, Lemma
3.1]."* **CONFIRMED**, and note KM-ab asks only `tau_i in eta^{-1}({0,
infinity})` -- *weaker* than KMU-I's `eta(S) = {0}` and than what Lemma B
delivers. So Lemma B over-satisfies KM-ab.

**Row 11 -- the dictionary. This is the step that could have severed the chain,
and it holds exactly.** KM-ab sec. 4.2, verbatim at source:

> `nu : E^dagger -> E^dagger` sends `t` to `((t^{p-1}+1)^p - 1)^{1/(p-1)}`;
> `b(n) = floor((-n-1)/(p-1))` for `n <= -1`, `0` for `n >= 0`;
> `D = prod_{n in Z} p^{b(n)} t^n O_L`, "which we regard as a sub-`O_L`-module
> of `O_{E^dagger}`";
> **Proposition 4.2.** "For all `n in Z_{>=0}` and `0 <= k <= p-1`, we have
> `U_p(p^{b(-k-np)} t^{-k-np}) in p^n D`, `U_p(D) subset D`. Proof. See [15,
> Proposition 4.4]."

Checking the correspondence term by term against 04:

| KM-ab | KMU-I / 04 | agree? |
|---|---|---|
| `nu(t) = ((t^{p-1}+1)^p-1)^{1/(p-1)}` | KMU-I sec. 4.3's Type-2 `sigma`; 04 sec. 1; my sec. 0 | **identical** |
| `b(-K) = floor((K-1)/(p-1))` | `a_KMU(K) = floor((K-1)/(p-1))` (Def. 6.3) | **identical** under `n = -K` |
| `K = k + np`, `0 <= k <= p-1`, gain `p^n` | `K = p*ell + r`, `0 <= r < p`, gain `pi^{ell/m_P}` | **identical** (`n = ell`, `k = r`) |
| `D = prod_n p^{b(n)} t^n O_L` | `A^{m,*} = {sum b_k t^{-k} : v_pi(b_k) >= a(k)/m_P}` | **same shape**, and `D` is **coefficientwise** |
| `U_p(D) subset D` | 04's (A3) in the weak form / my (A5) | **identical** |

So **04's Lemma A and Theorem 3 transport to KM-ab sec. 4.2 verbatim**: same
operator, same weight function under `n <-> -k`, and because `D` is defined
coefficientwise a non-eigenspace weight is native there. **The chain is not
severed. CONFIRMED.**

Two further points in 04's favour that neither 04 nor 05 makes:

- KM-ab's module carries **no growth parameter and no `pi`** -- the exponents
  are plain integers `p^{b(n)}` -- so 04's conservative `m_P v_pi(p) >= 1`
  calibration is not merely conservative here, it is exact: the requirement is
  literally `d(k) >= 1` in `v_p`.
- 04's weight `a(k) = floor((k-1)/3) + (k mod 2)` is **integer-valued**, so
  `p^{a(k)}` lives in `O_L` with no base change. The sec.-6 extremal weight
  `a*` is not (it takes values in `(1/6)Z`), and would need one. Another reason
  to make the parity-indicator weight the headline.

**Row 21 / Row 25 -- Prop. 7.2 and Prop. 7.4.** Read at source:

- **Prop. 7.2** ("`pr(V^_0) = O_R^trun`; both kernels have dimension
  `a(g-1+r_0+r_1+r_infinity - Omega_rho)`") is proved via **Lemma 7.3** by
  reduction modulo `m`: *"Let `M` be the reduction of `M` modulo `m`. By Lemma
  7.3 and (24) we may prove the corresponding result for the map [...]"*. The
  weight (`x_i = p^{b(n)}`) **does not appear in Prop. 7.2 at all**. So the
  Riemann-Roch / exact-sequence step really is carried out on the unweighted
  space. **CONFIRMED.**
- **Prop. 7.4** (`det(1-sU_p C|V) = det(1-sU_p C|G^con_E)`): the two bases are
  `G^r = {y_i e_i}` (orthonormal in `V`) and `G^con = {x_i e_i}` (formal basis
  of `V^con`), and the change of basis is **diagonal**, `x_i/y_i`. The source's
  one-line justification ("the matrices [...] are similar") is complete once
  one observes that every principal minor of a matrix is invariant under
  diagonal conjugation (`M'_{ij} = (x_j/x_i) M_{ij}`, and the `x` factors cancel
  in any determinant), so the Fredholm series agree coefficient by coefficient.
  This holds **for any weight**, provided both operators are nuclear -- which is
  Lemma 6.12's `lim col_i = infinity`, i.e. 04's `d(k) -> infinity`.
  **CONFIRMED, and complete.**
- The source itself confirms `G^con` is a formal basis *by construction*:
  *"From the definition of `O_R^con` we see that `G^con = {x_i e_i}` is a formal
  basis of `V^con`. Indeed, we just selected the `x_i` appropriately for each
  summand."* So KMU-I Def. 6.3's "formal basis" worry (04 table row 4) has no
  analogue here either.
- **sec. 7.2 case (II)**, verbatim, is the exact consumer: *"Write `n = k+pm`
  [...] From the definition of `b(n)` in sec. 4.2, we know **`b(n) >= m`**,
  which implies `v(x_i e_i) in p^m O_R^con` [...] `col >= m`"*, and later
  *"When `Q` is from case (II) **each slope in `P_Q` is at least one**."*
  So KM-ab consumes precisely 04's **(A4)** `a(k) >= d(k)` and **(A3)**
  `d(k) >= 1`, and nothing about the multiset's shape. **CONFIRMED** -- an
  independent second witness for what I established in Part One sec. 2.5 on the
  KMU-I side.

**Row 15.** My own sweep (`p in {2,3,5}`, `a <= 6`, all `epsilon in [0,q-2]`,
all `j`) reproduces 05's witnesses exactly:

```
  first violation of -q <= a(p-1):  p=2 a=3 eps=3 j=1  -q=4 > 3
                                    p=3 a=2 eps=5 j=1  -q=5 > 4
  first violation of -q <= a*p   :  p=2 a=4 eps=7 j=3  -q=9 > 8
```

The true bound is `-q(e,j) <= (p-1) a(a+1)/2`, which equals `a(p-1)` only for
`a = 1`. **REFUTATION CONFIRMED**, `p`-uniform, and vacuous for 2-power `rho`
(`epsilon = 0` makes every digit zero, hence `q(e,j) = 0`).

**Row 16.** KM-ab sec. 1.1 at source: `epsilon_Q` is "the unique integer between
`0` and `q-2`" and `omega_Q` is "the sum of the `p`-adic digits of
`epsilon_Q`". Since the only `epsilon <= p^a - 1` with digit sum `a(p-1)` is
`p^a-1 = q-1`, which is excluded, `omega <= a(p-1) - 1`. Exhaustive check
(`p in {2,3,5}`, `a <= 6`): **0 violations**. So (18) is satisfiable by taking
`s_Q` small, and 05 is right both that the source omits the argument and that
the argument is easy. **CONFIRMED.**

## P3-11. Two small corrections to 05

- **KLW Theorem 9.3(a)**: 05 quotes *"then X descends to `F_p-bar`"*; the source
  says *"then X descends to `F_p`"*. Transcription slip; 05 uses (b) and
  Theorems 1.2/7.6, so nothing depends on it. I verified all of KLW Theorems
  1.1, 1.2, 7.6, 9.3 and the proof of 9.3(b) verbatim, and SY Theorem 1.1
  verbatim. 05's characterization is right: **SY** is over an algebraically
  closed field, and **KLW Theorem 1.2/7.6** is what supplies the finite-field
  statement KMU Theorem 4.1 needs.
- **The `<1`-to-full-polygon step.** 05 sec. 2.3(a) describes it as "the
  `p`-uniform reflection argument (Euler-Poincare + Poincare duality, KM-ab
  Remark 1.2)". KM-ab's own sec. 7.3 does it more cheaply, by a degree count
  alone: *"From the Euler-Poincare formula we know `L(rho,s)` has degree
  `2(g-1+m) + sum (s_{tau_i} - 1)`. This accounts for the remaining slope one
  segments."* Duality appears only in Remark 1.2, for endpoint equality. Both
  work; the source's is simpler and should be the one quoted.

## P3-12. **Reconciliation with Part Two's coverage cap (charge item 3)**

05 sec. 2.3(b) settles more than it claims, and it resolves my Part Two finding
for the charter's primary target. Stated exactly, so the write-up can quote it:

### TARGET A -- `NP_q(rho) >= HP_q(rho)`, via KM-ab. **No cap.**

> For `q = 2^a`, `X/F_q` a smooth affine curve, `rho` a non-trivial character
> of `pi_1(X)` of **any** 2-power order `2^n`: the full `q`-adic Newton polygon
> of `L(rho, s)` lies above the Kramer-Miller ramification-defined Hodge
> polygon `HP(rho) = {0}^{g-1+m} (+) {1}^{g-1+m} (+) (+)_i {1/s_i, ...,
> (s_i-1)/s_i}`. **No truncation, no restriction on `n`.**

Why the cap does not apply: my Part Two cap came from 04's Lemma E reduction,
which needs `m_{e,P} >= 1` in **KMU-I's growth-tuple formalism** and therefore
`e <= 1`, which in turn caps the `pi_q`-adic truncation parameter. **KM-ab has
no such formalism at the Type-2 points**: `D = prod_n p^{b(n)} t^n O_L` carries
no radius parameter, the exponents are integers, the Riemann-Roch step
(Prop. 7.2) is weight-free, and the weight enters only through a diagonal
similarity (Prop. 7.4). There is no free parameter for Lemma E to constrain,
and the requirement consumed in sec. 7.2 case (II) is the absolute statement
`d(k) >= 1` in `v_p`. **So Lemma E does not arise and neither does the cap.**
Ingredients: KM-ab's `p`-uniform machinery + **Lemma B** + **04's Lemma A /
Theorems 1-3** transported through the row-11 dictionary. That is the
charter's *primary* target, and it is uncapped.

### TARGET B -- KMU-I Theorem 1.1 (the contact / terminal-point criterion), via KMU-I. **Capped.**

> Under 04's Lemma E reduction, the criterion is supported for `q`-adic
> `r in [0, 2^{1-n}]` for a character of order `2^n` -- i.e. the **full**
> `r in [0,1]` for order-2 characters, `r <= 1/2` at order 4, `r <= 1/4` at
> order 8.

The cap is structural (Part Two, P2-6): it follows from 04's own Theorem 4
(`d(6) <= 1` for every weight) together with Lemma E's `m_P >= 1`. To remove
it one must either prove Lemma E outright, or re-run KMU-I sec. 6.2 and all of
sec. 7 in KM-ab's coefficientwise formulation. 05 sec. 2.3(b) correctly
identifies the second option as available in principle, but **nobody has done
it**: KMU-I's perturbation machinery (Lemmas 7.1-7.4, 7.11, Cor. 7.14) is built
on the `B^{m_e}` basis and the tuple `m_e`, and transporting it is a research
task, not a citation. This is the charter's *stretch* goal.

### The one correction 05 needs

05's sec. 3 dependency graph, TARGET B line, reads *"04 reduces it to KMU's own
assertion with no loss for `r in [0,1]`"*. That repeats 04 sec. 7.3's
normalization error verbatim -- 05's reading list stops at `20-verify` sec. 1.3
and 2.2, i.e. Part One, so Part Two's correction was not absorbed. **The line
should read `r <= 2^{1-n}`.** Everything else in 05's dependency graph is
consistent with what I verified.

## P3-13. Reproduction (Part Three)

Scratchpad `ws20/code/audit05.py` (exact `GF(2^a)` arithmetic and polynomial
arithmetic written from scratch: the degree-3 auxiliary-map classification for
`a <= 6`, the KM-ab row-15 and row-16 sweeps for `p in {2,3,5}`, `a <= 6`) and
`ws20/code/inst.py` (the explicit Lemma-B instance over `F_4` and `F_16`).
PDFs newly fetched into `ws20/`: `2010.01130` (KLW), `1708.03036` (SY). All
runs completed in seconds, well inside the budget.
