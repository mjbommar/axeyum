# 01 -- KMU equation-level extraction: what is actually missing at p = 2

Workstream 01 (NoH-p2). Date: 2026-08-20. Sources fetched (curl + pdftotext,
session scratchpad `pdf/`), never recalled:

- KMU-I = arXiv:2110.08656v1, Kramer-Miller--Upton, *Newton Polygons of Sums on
  Curves I: Local-to-Global Theorems* (16 Oct 2021).
- KM-exp = arXiv:1909.06905, Kramer-Miller, *p-adic estimates of exponential
  sums on curves* (= [17] of KMU-I; ANT 15 (2021) 141-171).
- KM-ab = arXiv:2006.04936, Kramer-Miller, *p-adic estimates of abelian Artin
  L-functions on curves* (= [16] of KMU-I).
- Schmidt = arXiv:1901.05516, M. Schmidt, *T-adic exponential sums over
  affinoids* (JNT 2023).

## HEADLINE (read this first)

**The coordinator's obstruction analysis is REFUTED, with a witness.** The
p = 2 loss in KMU-I Remark 6.5 has nothing to do with the Artin-Hasse /
Dwork splitting function, nothing to do with the wild points, and nothing to
do with Witt length. It lives at the *auxiliary tame points of the Belyi map*
`eta : X -> P^1` lying over `1`, where the local Frobenius structure
`E~_P` is a **constant** (KMU-I Prop. 6.4 proof: "The claim follows since
`E~_P in 1 + pi R_q`"), because those points are **not** in `S` and the
character `rho` is unramified there. No `lambda_i` appears anywhere in
section 6.1.2.

**Reconstructed mechanism (four independent numerical matches, below).**
`a(k) = floor((k-1)/3)` is KMU's general weight `floor((k-1)/(p-1))` with
`p-1` replaced by the *tame ramification index* `e_P` of `eta` over the point
`1`, at the value `e_P = 3`. At p odd KMU force `e_P = p-1` (Prop. 4.3(2));
at p = 2 that value is `1`, which Riemann-Hurwitz forbids, so the smallest
admissible tame index is `3`. Every number in Remark 6.5 -- the weight
`floor((k-1)/3)`, the target pole `ell+r` with `k = 2 ell - r`, and the
slope-0 defect exactly at `k = 5` -- is reproduced from that single input.

**And it looks repairable.** With the same geometry (`e_P = 3`, `mu(P) = 3`)
but a *different weight function* on the same local module, the slope-0 defect
disappears: there is an admissible `a` with
`d(k) = min_j [a(k) - a(j) + v_2(c_{k,j})] >= max(1, k/6)` for all `k > 3`
(computed and re-verified with full support for `k <= 48`), whereas KMU's
`floor((k-1)/3)` gives `d(5) = 0`. `d(k) >= 1` is exactly what the global
argument needs (section 3 below) and `d(k) -> infinity` is what nuclearity
needs. **Status: OPEN (strong numerical evidence, not a proof).** The rate is
capped: `max(1, k/5)` is infeasible, `max(1, k/6)` is feasible.

---

## 1. Where the p = 2 exclusion actually sits

KMU-I standing hypothesis, section 1.1, verbatim: *"Let p be an odd prime and
let q be a power of p."* Exactly two places in the paper mention p = 2:

Remark 4.2 (p. 20), verbatim:
> "In [23], Sugiyama and Yasuda extend Fulton's result to the case p = 2. We
> have omitted this case for other reasons (see Remark 6.5). By a recent
> theorem of Kedlaya-Litt-Witaszek, eta exists even without extending the base
> field [13]."

Remark 6.5 (p. 33), verbatim (the OCR of the display is normalised here; the
displayed estimate is `U_p(pi^{a(k)/m_P} t_P^{-k}) in pi^{(a(k)-a(ell+r))/m_P}
A^m_{pi,P}`):
> "Suppose that p = 2. For k >= 3, define a(k) = floor((k-1)/3). A similar
> construction provides a submodule A^m_{pi,P} subset A^dagger_{pi,P} with the
> following property: Let k = 2 ell - r with r = 0 or 1. Then
> U_p(pi^{a(k)/m_P} t_P^{-k}) in pi^{(a(k)-a(ell+r))/m_P} A^m_{pi,P}.
> This estimate is too low for applications to the global setting. For example,
> if k = 5 = 2 * 3 - 1, then a(k) - a(ell+r) = 0, and this contributes an extra
> segment of slope 0 in the global Hodge bound below."

So the *entire* p >= 3 hypothesis of KMU-I is the local estimate at
`eta(P) = 1`, section 6.1.2. Nothing else.

The predecessor paper is explicit that this is the only gap. KM-exp section
1.4, verbatim:
> "Finally, we mention our requirement that p >= 3. When p = 2 it is likely
> that the methods in this paper still work. The main difficulty is that some
> estimates in section 4 must be modified. It is also not immediately clear
> that we can find a cover eta : X -> P^1_{F_q} satisfying the desired
> properties. To construct eta, we use the fact that X admits a simply branched
> map to P^1_{F_q}, which is false when p = 2. However, upcoming work of Kiran
> Kedlaya, Daniel Litt, and Jakub Witaszek provides a Belyi map in this case.
> This should [be] enough to handle the p = 2 case."

"some estimates in section 4" = KM-exp section 4.3 ("Type 2"), i.e. exactly
KMU-I section 6.1.2. The geometric ingredient is now in hand (KLW; also
Sugiyama-Yasuda, Belyi in char 2, Compositio 156 (2020) 325-339).

## 2. The two local cases, stated exactly

`eta : X -> P^1` is a tame Belyi map (KMU-I Prop. 4.3) with
(1) `eta(P) = 0` for every `P in S` (the ramification locus of `rho`), and
(2) `eta(P) = 1  =>  e_P = p - 1`. `S_eta = eta^{-1}({0,1,infinity})`.
`Theta~ = U_p o E~ : A^dagger_pi -> A^dagger_pi` (section 5.5), where `U_p =
(1/p) sigma^{-1} o Tr` (Def. 4.9) and `E~ = (E~_P)` is a `delta`-Frobenius
structure (Def. 5.9). The tuple `m_pi` (section 6.1) is
`m_{pi,P} = delta_P / p` for `P in S`; `= 0` for `P not in S`, `eta(P) in
{0,inf}`; `= 1/v_pi(p)` for `eta(P) = 1`.

### 2a. Wild case, `eta(P) = 0` or `infinity` -- WORKS AT p = 2 UNCHANGED

`sigma(t_P) = t_P^p`, so (KMU-I (17)) `U_p(t_P^k) = t_P^{k/p}` if `p | k`, else
`0`, and `U_p(A^m_{pi,P}) subset A^{m/p}_{pi,P}` with
`A^m_{pi,P} = A^{m_P}_{pi,P}` the plain growth-condition space (weight
`a(k) = k`).

**Proposition 6.1** (verbatim): "Suppose that `eta(P) = 0` or `infinity`, and
that `m >= m_pi`. Then `Theta~(pi^{k/m_P} t_P^{-k}) in pi^{k(p-1)/(p m_P)}
A^{p m_P}_{pi,P}`."

Proof input: `E~_P in A^{p m_P}_{pi,P}` -- for `P in S` because `(M,phi)` is
`delta`-overconvergent, for `P not in S` because `E~_P in 1 + pi R_q` is
constant. **No parity hypothesis is used or available to be used.** This is the
case that carries the Swan conductor, the character, and the splitting
function, and it is fine at p = 2.

### 2b. Tame auxiliary case, `eta(P) = 1` -- THE ONLY BROKEN ESTIMATE

Here `P not in S`, so `E~_P` is a constant in `1 + pi R_q`. Set `u_P =
t_P^{p-1}` (the pullback of the base parameter at the point `1`),
`B_{pi,P} = R_q((u_P))`; `A_{pi,P} = (+)_{i} t_P^{-i} B_{pi,P}` is the
`Gal(E/E_0) = Z/(p-1)` eigenspace decomposition. Growth module
`B^m_{pi,P} = { sum b_k u^{-k} : v_pi(b_k) > k/m_P for all k > 0 }` and
`A^m_{pi,P} = (+)_i t_P^{-i} B^m_{pi,P}` (Def. 6.3).

**Lemma 6.2** (verbatim): "Suppose that `m >= m_pi`. Let `k = p ell + r in Z`
with `0 <= r < p`. Then `U_p(t^{-k}) in t^{-(ell+r)} B^m_{pi,P}`."
(Proof: "For `R = Z_p` and `pi = p`, this is [17, Corollary 4.7].")

**Definition 6.3**: `a(k) = floor((k-1)/(p-1))` for `k > p-1`; then
`{ pi^{a(k)/m_P} t_P^{-k} }` is a formal basis of `A^m_{pi,P}`.

**Proposition 6.4** (verbatim): "Suppose `eta(P) = 1` and that `m >= m_pi`.
Then for each `k = p ell + r > p - 1`, we have
`Theta~(pi^{a(k)/m_P} t_P^{-k}) in pi^{ell/m_P} A^m_{pi,P}`."
Proof: "Observe that `a(k) - a(ell+r) = ell`."

The underlying local Frobenius (KMU-I section 4.3): `sigma(u_0) = u_0^p`,
`sigma(u_infinity) = u_infinity^p`, `sigma(u_1) = (u_1+1)^p - 1`, and for
`P` over `1` with `t_P^{e_P} = u_1`,
`sigma(t_P) = ((t_P^{p-1}+1)^p - 1)^{1/(p-1)}`
(the pdftotext rendering mangles the radical index and the sign; the form is
pinned by the proof of KM-exp Lemma 4.5, which factors
`t^{-(p-1)p}((t^{p-1}+1)^p - 1) = 1 + p y` and concludes
`t^{-p} t^nu = (1+py)^{1/(p-1)}`, i.e. **no** `p^{-1}` prefactor, and
`t^nu = t^p mod p`).

`mu(P)` (KMU-I (11) and the glossary, verbatim): "`mu(P) = 0` if `Q = 0` or
`infinity`, `= p-1` if `Q = 1`". Its role: `A^tr_P` drops all `t^{-k}` with
`k <= mu(P)`; the kernel of `pr` is `L = H^0(D)`,
`D = sum_{eta(P)=1} (p-1) P`, free of rank `N = g - 1 + r_0 + r_1 + r_inf`
(Prop. 4.10 + (13)). Riemann-Hurwitz (8): `2(g-1) + r_0 + r_1 + r_inf =
deg(eta)`, and `r_1 (p-1) = deg(eta)`. **So `mu(P) = e_P`, and this is the
structural constraint that makes the count come out.**

## 3. What the global argument actually consumes (charge item 1b)

The local estimate feeds in at exactly one place, **Proposition 6.6(2)**
(verbatim): "If `eta(P) = 1`, then for all `k = p ell + r > p-1` with
`0 <= r < p`, `Theta~(e^m_{P,k}) in pi^{ell/m_P} V~^m_{pi,P}`." Its proof uses
two things: Prop. 6.4, and `a(k)/m_P >= ell/m_P`, i.e. **`a(k) >= d(k)`**.

Then **Corollary 6.8 (Global Hodge Bound)**: with `m_{e,P} = delta_P/p`
(`P in S`), `1/(pe)` (`P not in S`, `eta(P) in {0,inf}`), `1/e`
(`eta(P) = 1`), the polygon `NP^{< v_pi(p)}_{pi_q}(Theta_q | V^dagger_pi)`
lies above the polygon with slope multiset
`{0,...,0}_r  (+)  (+)_{P in S} { k(p-1)/delta_P : 1 <= k < e delta_P }`,
"upon taking the limit `e -> v_pi(p)`".

**Therefore the exact requirement on the `eta(P) = 1` columns is:**

> `d(k) := a(k) - a(ell+r)` must satisfy `d(k) >= 1` for every `k > mu(P)`,
> and `d(k) -> infinity`.

Reason: the column slope is `d(k)/m_{e,P} = d(k) * e`, and only slopes
`< v_pi(p)` (`= e` in the limit) enter the truncated polygon. `d(k) >= 1`
puts every such column at slope `>= v_pi(p)`, i.e. above the whole truncation
window; `d(k) = 0` inserts a slope-0 segment, which is fatal because the
target `HP_q(rho)` has a *prescribed* number `g - 1 + |S|` of slope-0
segments (section 1.2). `d(k) -> infinity` is needed for tightness /
complete continuity (Cor. 6.7). The main theorem's truncation parameter is
`r in [0,1]` (Thm 1.1), and the local Hodge slopes at `P in S` are
`{1/d_P, ..., (d_P-1)/d_P} subset (0,1)` -- so nothing beyond `slope >= 1` is
ever asked of the `eta(P) = 1` columns.

**Answers to the charge's phrasing.** It is *not* `floor((k-1)/2)`-per-se and
*not* `(k-1)(p-1)/p` that is needed. The need is a pure positivity-plus-
divergence condition, `d(k) >= 1` and `d(k) -> inf`, and it is independent of
the Swan conductor `delta_P`, of the Witt length `n`, and of the point's
ramification data -- those enter only the `eta(P) = 0` columns, through
`delta_P = d_P / p^{n-1}` and the slope list `k(p-1)/delta_P`. At p odd KMU
achieve `d(k) = ell = floor(k/p)`, which is massively more than needed; the
p = 2 construction of Remark 6.5 achieves `d(5) = 0`, which is less than
needed, and it is the only violation (section 5).

## 4. Reconstruction of Remark 6.5: `3 = e_P`, not `3 = 1/decay-rate`

Claim: KMU's p = 2 "similar construction" is section 6.1.2 with the tame index
over `1` taken to be `e_P = 3` (`p-1 = 1` is unusable: with `e_P = 1`,
Riemann-Hurwitz (8) `2(g-1) + r_0 + r_1 + r_inf = deg(eta) = r_1` forces
`2(g-1) + r_0 + r_inf = 0`, impossible; and `3` is the smallest tame index
`> 1` at `p = 2`). Then `a(k) = floor((k-1)/e_P) = floor((k-1)/3)` is
Definition 6.3 verbatim, and `mu(P) = e_P = 3`.

Evidence -- I built the operator from scratch and compared. Setup: `u = t^e`,
`nu(u) = (1+u)^p - 1 = u^2 + 2u`, `nu(t) = t^2 G` with
`G = (1 + 2 x^e)^{1/e}`, `x = 1/t`; the nontrivial conjugate of `t` over
`nu(E)` is `t' = -nu(t)/t = -t G` (check `t'^3 = -nu(u)/u = -2-u = u'`), so
`Tr(t^{-k}) = x^k (1 + (-1)^k G^{-k})` and `U_2(t^{-k}) = (1/2) nu^{-1}(Tr)`
is found by solving `sum_j c_{k,j} x^{2j} G^{-j} = (1/2) x^k (1 + (-1)^k
G^{-k})` from the lowest degree up. Control: at `e = 1` this reproduces, to
the last digit, the independent Newton's-identity computation from the
minimal polynomial `X^2 + 2X - s` of `t` over `Q(s)`, `s = t^2 + 2t`
(`U_2(t^{-1}) = t^{-1}`, `U_2(t^{-2}) = t^{-1} + 2t^{-2}`,
`U_2(t^{-3}) = 3t^{-2} + 4t^{-3}`, ...).

At `e = 3`, `p = 2` the computation gives (exact rationals):

```
U_2(t^-3) = t^-3                                     (exactly one term)
U_2(t^-4) = t^-2 + (8/9) t^-5 - (40/243) t^-8 + ...
U_2(t^-5) = (5/3) t^-4 + (40/81) t^-7 - (112/729) t^-10 + ...
U_2(t^-6) = t^-3 + 2 t^-6                            (exactly two terms)
U_2(t^-7) = (7/3) t^-5 + (140/81) t^-8 - ...
U_2(t^-8) = t^-4 + (32/9) t^-7 + (224/243) t^-10 - ...
```

Four independent matches with Remark 6.5, all verified for `k = 3..48`:

1. **Minimal pole order.** The lowest pole occurring in `U_2(t^{-k})` is
   exactly Remark 6.5's `ell + r` (`k = 2 ell - r`, `r in {0,1}`). Closed
   form: it is the least `j >= ceil(k/2)` with `j = -k mod 3`. (The residue
   rule is forced: `U_p` is `nu^{-1}`-semilinear and
   `nu(t^{-i}) = t^{-pi} G^i`, so `U_2` maps the `chi^{-i}` eigenspace to
   the `chi^{-i'}` one with `p i' = i mod e`, i.e. `i' = -i mod 3`.)
2. **The weight.** `a(k) = floor((k-1)/3)` is Definition 6.3 at `e = 3`.
3. **The leading coefficient is a unit** (`v_2(c_{k,ell+r}) = 0` for all
   `k <= 48`), so there is no hidden gain hiding behind the pole-order
   statement -- the estimate is sharp as stated.
4. **The defect.** `d(k) = a(k) - a(ell+r) = 0` occurs at `k = 3` and `k = 5`
   only, in `k <= 80`; `k = 3` is removed by `k > mu(P) = 3`, leaving exactly
   the `k = 5` that KMU cite. (`U_2(t^{-3}) = t^{-3}` exactly, a genuine
   eigenvector of eigenvalue 1 -- which is why `mu(P) = e_P` is not optional.)

Verdict on the reconstruction: **PROVED as a quantitative match** (the numbers
are not quoted from KMU, they are recomputed and agree on every entry checked);
KMU nowhere state `e_P = 3`, so the identification itself remains an inference,
labelled **OPEN-but-overdetermined**.

### 4a. Consequence: the loss is not a "decay rate" at all

If one insists on reading `a(k) = floor((k-1)/3)` as "decay rate `1/3` per
degree", the correct reading of the `1/3` is `1/e_P`, a *tame ramification
index of an auxiliary map*, not a p-adic decay of any series. At p odd the same
number is `1/(p-1)`, and it likewise has nothing to do with the splitting
function: it is `1/e_P` with `e_P = p - 1`.

## 5. Does a better lattice repair it? (numerical, OPEN)

Fix `p = 2`, `e_P = 3`, `mu(P) = 3`. Replace Definition 6.3's weight by an
arbitrary `a : Z_{>0} -> Q_{>=0}` and set
`A^m = { sum b_j t^{-j} : v_pi(b_j) >= a(j)/m_P }`. Admissibility:

- **(A1)** `a(j) = 0` for `j <= mu(P) = 3` -- otherwise `L = H^0(D)` is not
  inside `A^m` and the exact sequence `0 -> L~ -> A~^m -> A^{m,tr} -> 0` of
  section 6.2 breaks. (KMU's own weight satisfies this: `floor((k-1)/(p-1))
  = 0` for `k <= p-1`.)
- **(A2)** `a(j) = O(j)` -- otherwise `union_m V~^m = V~^dagger` fails
  (Cor. 6.7).
- **(A3)** `d(k) := min_j [ a(k) - a(j) + v_2(c_{k,j}) ] >= 1` for `k > 3`,
  and `d(k) -> infinity`. (This is the section-3 requirement; the scaling by
  `m_P` is exactly absorbed by `m_P >= m_{pi,P} = 1/v_pi(p)`, since
  `v_pi(c) = v_pi(p) v_2(c)` and `v_pi(p) m_P >= 1` -- the same calibration
  KMU use at p odd.)

Results (exact rational arithmetic; `d` minimised over the full computed
support, weights obtained by monotone fixed-point iteration of the constraint
system, then re-verified independently on `k <= 48` against the full support):

| weight `a` | `d(4)` | `d(5)` | `min_k d` | verdict |
|---|---|---|---|---|
| `floor((k-1)/3)` (KMU Remark 6.5) | 1 | **0** | 0 | fails (A3) |
| `floor((k-1)/2)` | 1 | 1 | 1 | fails (A1): `a(3) = 1 != 0` |
| `max(0,k-3)` (rate 1 in `t`) | -- | -- | -54 | fails (A3) badly |
| `max(0,k-3)/2` | 1/2 | 1/2 | 1/2 | fails (A3) |
| LP-minimal for `d(k) >= max(1, k/5)` | -- | -- | -- | **infeasible** |
| LP-minimal for `d(k) >= max(1, k/6)` | 1 | 2 | 1 | **feasible** |

The feasible weight begins
`a = 0, 0, 0, 1, 2, 1, 19/6, 7/3, 5/2, 11/3, 5, 3, 9/2, 11/2, 5, 5, ...`
with `a(48) = 15` (`a(k)/k -> ~0.31`, so (A2) holds, and the rate is
essentially the same `~1/3` as KMU's -- it is the *shape*, not the rate, that
matters). Tightest slack 0, at `k = 4, j = 2`.

**So: `d(5) = 0` is an artifact of the choice `a(k) = floor((k-1)/3)`, not of
the operator.** Note the KMU weight is *forced* only if one insists on the
eigenspace form `A^m = (+)_i t^{-i} B^m` with `B^m` a rate-1 condition in
`u`; dropping that form (keeping the same ambient module and the same
`sigma`) is what buys the repair. This is the concrete content of attack (C)
in the charter, and it is now a finite, checkable statement rather than a
search.

**Caveats, stated plainly.** (i) numerical for `k <= 96` with support
truncation, not a proof -- a proof needs a closed form for `v_2(c_{k,j})` and
an explicit closed-form weight (none of the obvious ones work; see the table);
(ii) I have not re-checked that the exact sequence `0 -> L~ -> A~^m ->
A^{m,tr} -> 0` at section 6.2 (asserted there without proof for `A^m`, only
proved for `A^dagger` in Lemma 5.15) survives a non-eigenspace weight beyond
(A1); (iii) the geometric input -- a tame Belyi map at p = 2 with
`eta(P) = 0` on `S` and `e_P = 3` over `1`, obtained by replacing the
`(p-1)`-power map in KMU Prop. 4.3's `eta_q` by the 3-power map -- is
plausible (3 is tame at p = 2, KLW/Sugiyama-Yasuda supply the base map) but
unverified; (iv) the global bookkeeping `N = g-1+r_0+r_1+r_inf` versus the
target's `g-1+|S|` slope-0 segments must be re-derived with `e_P = 3`.

## 6. Implementable specification of `U_2` (charge item 2, handoff to 03)

Two different operators are needed; **the one that matters for Remark 6.5 is
6b, not 6a.** Both are exact finite computations over `Q` (no p-adic
approximation needed; take `v_2` of exact rationals).

### 6a. Wild point (`P in S`, `eta(P) = 0`) -- where the character lives

Module: `A^{m_P}_{pi,P}`, basis `{ pi^{k/m_P} t^{-k} }_{k>0}`, weight
`a(k) = k`, `m_P = delta_P / p`.
Operator: `Theta~ = U_p o (multiplication by E~_P)` with
`U_p(t^k) = t^{k/p}` if `p | k`, else `0`.
`E~_P` is given in closed form by **KM-ab Proposition 5.5** (verbatim
statement: "Assume `Im(psi) = Z/p^n Z`. Let `K` be the fixed field of
`ker(psi)` and let `s` be the Swan conductor of `psi`. We assume that
`pi_s in O_E`. Then there exists a p-Frobenius structure `E_r` of `psi` such
that `E_r in O_L[[pi_s t^{-1}]]` and `E_r = 1 mod m`."), constructed as

```
        r(t) = sum_{i=0}^{n-1} sum_{j=0}^{s_i} [r_{i,j} t^{-j}] p^i  in W_n(F_q[t^-1]),
        s    = min_{i=0}^{n-1} { p^{n-i} s_i }            (the Swan conductor)
        E_r  = prod_{i=0}^{n-1} prod_{j=0}^{s_i} E( [r_{i,j}] t^{-j} gamma_{n-i} )
```

with `E(x)` the Artin-Hasse exponential, `[.]` Teichmuller, and
`v_p(gamma_i) = 1 / ( p^{i-1} (p-1) )`; `gamma_i in Z_p[zeta_{p^n}]` is
characterised by `E(gamma_i) = zeta_{p^i}` (the pdftotext rendering of this
one condition is garbled -- "`E(gamma_n) = zeta_{p^n}^{p^{n-i}}`" -- but the
stated valuation `1/(p^{i-1}(p-1))` pins it, and only the valuation is used).
The **only** property of `E` used in the proof is `E(x) in Z_p[[x]]`.

Toy examples over `F_2` as requested:
- *Witt length 1, Swan conductor 1*: `y^2 - y = r_1 t^{-1}`,
  `E~_P = E(r_1^ t^{-1} gamma_1)`, `v_2(gamma_1) = 1/(p-1) = 1`.
  Weight `a(k) = k`, `m_P = delta_P/p = 1/2`, column valuation
  `k(p-1)/(p m_P) = k` (Prop. 6.1).
- *Witt length 1, Swan conductor 2*: **does not exist at p = 2.** The Swan
  conductor of an Artin-Schreier character is prime to `p`, so at `p = 2`,
  `m = 1` the possible values are `d = 1, 3, 5, ...`. Use `d = 3`:
  `E~_P = E(r_1^ t^{-1} gamma_1) E(r_3^ t^{-3} gamma_1)`, `delta_P = 3`.
  (Recording this because the charter asked for `s = 2`; workstream 03 should
  not spend time on an empty case.)
- *Witt length 2, `p = 2`*: `E~_P = prod_{j<=s_0} E([r_{0,j}]t^{-j} gamma_2)
  * prod_{j<=s_1} E([r_{1,j}]t^{-j} gamma_1)`, `v_2(gamma_2) = 1/2`,
  `v_2(gamma_1) = 1`, `delta_P = d_P/p^{n-1} = s/2`.

### 6b. Tame auxiliary point over `1` (`eta(P) = 1`) -- the actual gap

Inputs: `p = 2`, tame index `e` (`= p-1` at p odd; `= 3` at p = 2).
`E~_P` is a constant in `1 + pi R_q` and can be taken `= 1`.

```
x       := 1/t                                        (formal variable)
G       := (1 + 2 x^e)^(1/e)                          (binomial series, exact Q)
Tr_k    := x^k * ( 1 + (-1)^k * G^(-k) )              (= Tr_{E/nu(E)}(t^-k))
basis_j := x^(p j) * G^(-j)                           (= nu(t^-j))
solve   (1/2) * Tr_k = sum_j c_{k,j} * basis_j        (lowest-degree-first
                                                       elimination; the least
                                                       occurring degree is
                                                       always even, = 2 j'(k))
U_2(t^-k) = sum_j c_{k,j} t^-j
```

Facts to check on the way (all confirmed here):
- `j'(k) := min support = least j >= ceil(k/2) with j = -k mod e`; for `e = 3`
  this equals `ell + r` where `k = 2 ell - r`, `r in {0,1}`.
- `v_2(c_{k,j'(k)}) = 0` always.
- control at `e = 1`: `U_2(t^{-k}) = (1/2)(-1)^k p_k(s -> t)/t^k` where
  `p_k = -2 p_{k-1} + s p_{k-2}`, `p_0 = 2`, `p_1 = -2` (`s = t^2 + 2t`);
  in that case `v_2(c_{k,j}) = 2j - k - 1 + v_2((k/j) binom(j, k-j))`.
- decay `d(k) = min_j [a(k) - a(j) + v_2(c_{k,j})]`; the target is
  `d(k) >= 1` for all `k > mu(P) = e`, and `d(k) -> infinity`.

Ground truth for regression (exact): `U_2(t^{-3}) = t^{-3}`;
`U_2(t^{-6}) = t^{-3} + 2 t^{-6}`; `U_2(t^{-5}) = (5/3) t^{-4} + (40/81)
t^{-7} - (112/729) t^{-10} + ...`; at `e = 1`, `U_2(t^{-6}) = t^{-3} +
18 t^{-4} + 48 t^{-5} + 32 t^{-6}`.

Scripts used (session scratchpad, not committed): `updwork.py` (Newton's
identities, general `p`, `e = 1`), `type2_e.py` (general `e`, `p = 2`),
`lp2.py` (weight feasibility).

### 6c. A side result worth recording

At `e = 1` (i.e. an *unramified* point over `1`), the estimate is clean at
**every** prime: `U_p(t^{-k})` has lowest pole exactly `ceil(k/p)` and
satisfies `v_p(b_n) >= n` in `t^{-ceil(k/p)} * B`, `B = {sum b_n t^{-n} :
v_p(b_n) >= n}` -- verified for `p = 2, 3, 5` and `k <= 120`. So the
Type-2 estimate is *not* intrinsically harder at p = 2; it is the enforced
`e_P > 1` (via Riemann-Hurwitz) that creates the eigenspace congruence
`j = -k mod e` and with it the near-fixed-points of `k -> j'(k)`.

## 7. Verdicts on the coordinator's analysis (charge item 3)

- **Charter claim** ("`pi^2/2 = -1`, `pi^4/4 = 1` are units, so the single-pi
  grading cannot certify better than ~1/3 per degree, the exact source of
  `a(k) = floor((k-1)/3)`"): **REFUTED.** Witness: KMU-I section 6.1.2 is the
  case `P not in S`, where `E~_P` is a *constant* (Def. 5.9(1), and the proof
  of Prop. 6.4 ends "since `E~_P in 1 + pi R_q`"). No splitting function, no
  `lambda_i`, no `pi`-grading of a series enters the derivation of `a(k)`.
  The `3` is `e_P`, a tame ramification index (section 4).
- **Coordinator Note 1 self-correction** (those units live in the exponent,
  `lambda_2 = -2`, `v = 1 = 2 v(pi)`): **CORRECT**, and it is the right
  correction.
- **Lemma-candidate (L1)** (`v(lambda_i) >= i v(pi)` for `theta(x) =
  AH(pi x)`, all `p`): **PROVED, and trivially so.** `AH(x) in Z_p[[x]]`
  (Dwork/Dieudonne), hence `AH(pi x) = sum a_i pi^i x^i` with `a_i in Z_p`,
  hence `v(lambda_i) = v(a_i) + i v(pi) >= i v(pi)`, with equality iff `a_i`
  is a unit. No product-formula rearrangement is needed. The coordinator's
  numerical confirmation (equality at `i = 0,1,2,5,7,9,...`) is consistent.
- **But (L1) gives no leverage**, because it is *exactly* the property KM
  already use: KM-exp Prop. 5.5 and KM-ab Prop. 5.5 both conclude with the
  words "Since `E(x) in Z_p[[x]], it is clear that `E_r in ...`". The
  splitting function is already used at its optimal rate. Re-running the
  local construction with a "rate-1/2 coefficient bound" changes **nothing**:
  `a(k)` in Remark 6.5 is not a function of any coefficient bound. The exact
  dependence the charge asks for is: a per-degree rate `c` on the splitting
  function enters only via `delta_P` in `m_{pi,P} = delta_P/p` at the *wild*
  points, and thence only into the Hodge slopes `k(p-1)/delta_P` -- which are
  the *target*, not a loss.
- **Prediction P3** ("the real loss lives in the `m >= 2` Witt cross terms"):
  **REFUTED.** KM-ab Prop. 5.5's `E_r` is a *literal product* of rank-one
  Artin-Hasse factors indexed by `(i, j)` (Witt level, pole degree). There
  are no cross terms; the estimate is a product of growth conditions and uses
  only `E(x) in Z_p[[x]]` plus `v_p(gamma_i) = 1/(p^{i-1}(p-1))`. The
  statement carries no parity hypothesis and holds verbatim at `p = 2`.
- **Prediction P2** ("`a_true(k)` at `m = 1` supports `floor(k/2)`-type rates
  on the plain monomial basis after diagonal rescaling"): **not the right
  question**, but the analogous true statement at the point that matters is
  section 5: at `e = 3, p = 2` the achievable `d(k)` after diagonal rescaling
  is `~k/6` (and `k/5` is infeasible), which is more than the `d(k) >= 1` the
  global argument needs.
- **Note 2 (even-part commutation trick)**: correct as stated for
  `psi o M_{B(x^2)} = M_{B(x)} o psi`, but it acts on the wild-point operator
  (6a), which is not where the obstruction is. Recorded as unused.

## 8. Schmidt transplant (charge item 4)

Setting (section 1): `P_1 = infinity`, `P_2 = 0`, `P_3..P_ell in F_q`,
`f(x) = sum_j sum_{i<=d_j} a_{ij}/(x - P_j^)^i`, "Let `p` be a prime" -- **no
parity hypothesis anywhere.** Weighted basis `W^pi_{ij} = pi^{i/d_j} (x) B_{ij}`
(Def. 6.4) -- i.e. structurally the same device as KMU's
`pi^{a(k)/m_P} t^{-k}`, with `a(i) = i` and `m = d_j`.

The section 6 estimates, verbatim:

- **Proposition 6.8**: `ord_pi C_{(ij),(nk)} >= (p n - i)/d_k` for `k = 1, 2`;
  for `k >= 3`, `>= (n-i)/d_k` if `j = k`, `(n+i)/d_k` if `j != 1, k = 1`,
  `n/d_k` if `j != k, k != 1`, "and equality holds when `d_k | (n-i)`,
  `d_k | (n+i)` or `d_k | n` respectively".
- **Theorem 6.9**: with `D_{(ij),(nk)} = pi^{i/d_j - n/d_k} C_{(ij),(nk)}`:
  `ord_pi D >= (p-1)n/d_k` for `k = 1, 2`; **`ord_pi D >= 0` for `k >= 3`,
  with equality when `d_k | (n-i)` and `j = k`**; and, for real `c > 0`,
  `ord_{pi^{1/c}, p} D >= (n-1)(p-1)c/d_k` if `d_k >= c(p-1)`, else `n-1`.
- **Corollary 6.10**: "Neither `alpha_1` nor `alpha_a` are `pi`-adically
  completely continuous operators, but for `c > 0`, they are both
  `(pi^{1/c}, p)`-adically completely continuous."
- **Theorem 7.2 / 1.1**: the `(pi^{1/c},p)`-adic Newton polygon of
  `C_f(s,pi)` lies above `HP_c = (+)_k HP_c^k`,
  `HP_c^k` with vertices `{(n, a(p-1)n(n-1) c / (2 d_k))}`,
  `0 < c <= 1/(p-1)`.

**What the bigrading buys**: exactly the removal of a family of columns whose
valuation is 0 in the single (`pi`) grading -- the finite poles `k >= 3`,
where Theorem 6.9 gives `ord_pi D >= 0` *with equality*. Re-grading by
`(pi^{1/c}, p)` converts those into `(n-1)(p-1)c/d_k -> infinity` and restores
complete continuity.

**Does it imply the KMU-needed estimate at p = 2? NO -- and the gap is
categorical, not quantitative.** Schmidt's `alpha` is the Dwork operator
twisted by the *splitting function* at the *poles* of `f`; restricted to a
formal disk at a pole it is the analogue of KMU's `eta(P) = 0` case
(section 2a), which already works at every `p` (Prop. 6.1, no parity
hypothesis). It says nothing at all about the Type-2 operator
`(1/p) sigma^{-1} Tr` for `sigma(t) = ((t^{e}+1)^p - 1)^{1/e}` at an
auxiliary tame point where the character is *trivial*. There is no local
module of Schmidt's to substitute for `A_{pi,P}` at `eta(P) = 1`, because his
geometry (`P^1` affinoid) has no such point: the whole Belyi-map apparatus,
and with it section 6.1.2, exists only because KMU work over an arbitrary
curve.

**What does transplant is the method, and it is the same move as section 5.**
Both failures are "a family of columns has valuation 0 in the grading you
chose"; Schmidt cures it by refining the grading (`pi` -> `(pi^{1/c}, p)`
with a free rate parameter `c`), and the section-5 repair cures KMU's by
refining the weight `a(k)` (equivalently, the lattice) on the same module.
The exact statement of the residual gap for attack (A):

> Schmidt supplies no estimate for `(1/p) sigma^{-1} Tr_{E/sigma(E)}` on
> `R_q((t))` when `sigma` is the Type-2 lift; his Theorem 6.9 governs
> `U_p o (splitting function)` for `sigma(t) = t^p`. Attack (A) as written --
> "transplant its bigraded local module into KMU's local-to-global glue,
> replacing `A_{pi,P}`" -- has no target to replace, and should be
> **retired in favour of attack (C)**, which section 5 has now reduced to a
> single finite question.

## 9. Needed-vs-available table at p = 2 (charge deliverable (a))

| local datum | what the global argument needs | what is available at p = 2 | gap |
|---|---|---|---|
| `eta(P) = 0, infinity`, `P in S` (wild) | column valuation `k(p-1)/(p m_P)`, `m_P = delta_P/p`, giving slopes `k(p-1)/delta_P` | KMU-I Prop. 6.1, proof uses only `E~_P in A^{p m_P}`; KM-ab Prop. 5.5 supplies `E~_P` at any `p`, any Witt length | **NONE** |
| `eta(P) = 0`, `P not in S` | same | same, `E~_P` constant | **NONE** |
| `eta(P) = 1` (tame auxiliary) | `d(k) >= 1` for all `k > mu(P)`, `d(k) -> inf` | Remark 6.5: `d(k) = a(k) - a(ell+r)` with `a = floor((k-1)/3)`; `d(5) = 0` | **one column, `k = 5`** |
| geometry | tame Belyi `eta` with `eta(S) = 0`, `e_P` tame over `1` | KLW / Sugiyama-Yasuda give the base map; `e_P = 3` via a 3-power map | unverified, believed routine |
| lattice | any admissible weight with (A1)-(A3) | numerically exists with `d(k) >= max(1, k/6)`; `max(1,k/5)` infeasible | **proof missing** |

## 10. Handoffs

- **to 03 (critical)**: implement 6b, not 6a. The object to measure is the
  Type-2 operator at `p = 2, e = 3`, and the question is not "what is the true
  spectrum" but "is there an admissible weight (A1)-(A3), in closed form,
  with `d(k) >= 1` and `d(k) -> infinity`". Ground truth and the algorithm are
  in section 6b; the LP is in section 5. Also worth running: `e = 5, 7` (any
  odd tame index is allowed) -- if some `e` makes a closed-form weight
  obvious, that is the cheapest path to a proof.
- **to 02**: (L1) is true and one-line (section 7) but is not the lever;
  Pulita's Lubin-Tate exponentials will not help either, for the same reason
  -- the broken estimate contains no splitting function. Suggest 02 redirect
  to the closed form of `v_2(c_{k,j})` for the Type-2 operator (a symmetric-
  function / Newton-identity problem, cf. KM-exp Cor. 4.7's induction), which
  is what a proof in section 5 needs.
- **to the coordinator**: attack (A) should be retired (section 8); attack (B)
  is aimed at the wrong object (section 7); attack (C) is now a finite
  question (section 5); attack (D) is discharged by sections 3, 4 and 7.
