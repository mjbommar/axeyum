# 05 -- Lemma B (the char-2 tame Belyi map) and the KM-ab global audit

Workstream 05 (NoH-p2). Date: 2026-08-20. Labels: **PROVED** / **REFUTED
(witness)** / **OPEN** / **CONDITIONAL-ON (named citation)**.

Read before this file: `00-charter.md`, `10-notes-coordinator.md` (Notes 5-9),
`01-kmu-extraction.md` sec. 1-2 and 5, `20-verify.md` sec. 1.3 and 2.2,
`04-weight-proof.md` (the theorem-candidate and its two named gaps).

**Sources fetched by me, never recalled** (`curl` + `pdftotext -layout`, session
scratchpad `pdf/`):

- KMU-I = arXiv:2110.08656v1 (Kramer-Miller--Upton, *Newton Polygons of Sums on
  Curves I*).
- KM-ab = arXiv:2006.04936v2, 10 Jul 2021 (Kramer-Miller, *p-adic estimates of
  abelian Artin L-functions on curves*).
- KM-exp = arXiv:1909.06905 (Kramer-Miller, *p-adic estimates of exponential
  sums on curves*) -- the source of both papers' geometric lemma.
- **KLW = arXiv:2010.01130v2, 2 Oct 2021** (Kedlaya--Litt--Witaszek, *Tamely
  ramified morphisms of curves and Belyi's theorem in positive
  characteristic*; accepted to IMRN). = KMU-I reference [13]. **Newly fetched
  by this workstream; nobody in this project had read it.**
- **SY = arXiv:1708.03036v2, 27 May 2018** (Sugiyama--Yasuda, *Belyi's theorem
  in characteristic two*; Compos. Math. 156 (2020) 325-339). = KMU-I reference
  [23]. **Newly fetched.**

---

## HEADLINE

1. **LEMMA B is PROVED**, at the same epistemic standard as the odd-`p` case
   (i.e. conditional only on a published, refereed theorem quoted verbatim
   below -- KLW Theorem 1.2, which at `p = 2` plays exactly the role Fulton's
   theorem plays at `p >= 3`). The 3-power composition works; I mirrored KM-exp
   Lemma 3.1's construction line by line and every step survives at `p = 2`.
   The other ramification point of `z -> z^3` lands over `infinity`, where the
   local Frobenius is `sigma(t) = t^p` regardless of index -- it creates **no**
   new Type-2 point and does not meet `S`.
2. **One arithmetic side condition, and it is free.** The 3-power stage needs a
   primitive cube root of unity in `F_q`, i.e. `3 | q-1` (`q = 2^a` with `a`
   even). This is **necessary** at degree 3 (proved by case analysis, machine
   checked for `q <= 64`) and **free**, because both papers explicitly license
   base extension ("After increasing q", KM-ab sec. 2.1 and Lemma 3.1;
   "After extending the base field", KMU-I Thm. 4.1) and both `NP_q` and
   `HP_q` are invariant under it (argument in sec. 1.6, which the sources
   assert but do not prove).
3. **The general statement is cleaner than `e_P = 3`:** for *every* odd `e > 1`
   with `e | q-1` there is a tame Belyi `eta` with `eta(S) = {0}` and every
   point over `1` of index exactly `e`. `e | q-1` is *simultaneously* the
   condition for the `e`-power stage to be definable over `F_q` and the
   condition for `mu_e subset Z_q`, i.e. for KMU's Galois-eigenspace
   decomposition of `A_{pi,P}`. At odd `p`, `e = p-1 | q-1` automatically --
   which is *why* KMU's choice is `p-1`. The extension-free choice at `p = 2`
   is `e = q-1` (sec. 1.8).
4. **REFUTED (witness), source infelicity:** KMU-I Prop. 4.3's "The second map
   is a linear transformation fixing 1 and `infinity` and sending 0 to any
   other `F_q`-rational point" is **false as stated at every p**: the point `c`
   must satisfy `c^{p-1} = 1`, else the composite has a fourth branch point and
   is not Belyi. KM-exp's original is correct -- it takes `c = 2`, and
   `2^{p-1} = 1` by Fermat. At `p = 2` the point "2" *is* the point `0`: a
   third, independent way the odd-`p` construction degenerates, beyond
   `e_P = 1` and Riemann-Hurwitz.
5. **KM-ab global audit: no `p = 2` obstruction outside the two already-named
   places.** 18-row table in sec. 2. `p >= 3` is consumed in KM-ab exactly
   twice, and they are the *same two* as in KMU-I: Lemma 3.1 (the index `p-1`
   over `1`) and sec. 4.2 (the Type-2 estimate whose weight denominator is that
   index). Everything else is `p`-uniform.
6. **Settled (04 left it OPEN): the theorem-candidate does not need KM-ab's
   globals -- and routing through them would be *cheaper*, not dearer.**
   KMU-I is self-contained for `NP^{<1} >= HP^{<1}` (Cor. 6.8 + Cor. 7.14), and
   full `NP >= HP` follows by the `p`-uniform reflection argument. Moreover
   **KM-ab's route does not have 04's Lemma E gap at all**: its local growth
   module `D = prod_n p^{b(n)} t^n O_L` is defined *coefficientwise*, not as a
   Galois-eigenspace sum, so a non-eigenspace weight is native there; the
   Riemann-Roch/exact-sequence step (Prop. 7.2) happens on the *unweighted*
   Banach space and the weight enters only through a similarity of matrices
   (Prop. 7.4). Risk R3 / Lemma E is an artifact of KMU-I's Def. 6.3, not of
   the mathematics.
7. **REFUTED (witness), p-uniform:** KM-ab sec. 4.1.1's "We know
   `-q(e,i) <= a(p-1)`" is false -- first counterexamples `p = 2, a = 3,
   eps = 3, j = 1` (`-q = 4 > 3`) and `p = 3, a = 2, eps = 5, j = 1`
   (`-q = 5 > 4`). Not a `p = 2` issue, and **vacuous for the NoH-p2 target**
   (2-power characters have `eps = 0`, so `q(e,j) = 0`).

---

## 0. Method

Everything below is either (a) a verbatim quotation from a fetched PDF, (b) an
argument written out here, or (c) an exact machine computation over `GF(2^n)`
(scripts `gf.py`, `deg3b.py`, `compose.py` in the session scratchpad
`noh05/`; integer/finite-field arithmetic only, no floating point). Where my
reading differs from 01's or 04's I say so.

---

# PART 1 -- LEMMA B

## 1.1 The citations, verbatim

**KMU-I Remark 4.2** (p. 20), verbatim:

> "In [23], Sugiyama and Yasuda extend Fulton's result to the case p = 2. We
> have omitted this case for other reasons (see Remark 6.5). By a recent
> theorem of Kedlaya-Litt-Witaszek, eta exists even without extending the base
> field [13]."

and immediately after, verbatim:

> "From now on we fix a choice of eta_0 as in Theorem 4.1. As in [13, Theorem
> 9.3], the existence of eta_0 implies the existence of a tamely ramified map
> X -> P^1_{F_q} with three ramified points. We shall need some control over
> the branching of this map, so we modify the construction slightly."

**KMU-I Theorem 4.1 (Fulton [9])**, verbatim: "After extending the base field,
there exists a finite, separable, tamely ramified morphism
`eta_0 : X -> P^1_{F_q}`."

Note what Theorem 4.1 asks for: **tame**, nothing more. Simple branching is
*not* part of the statement KMU use (it is how Fulton gets tameness at
`p >= 3`).

**SY Theorem 1.1** (arXiv:1708.03036v2, p. 1), verbatim:

> "Theorem 1.1. Let X be a proper smooth curve over an algebraically closed
> field k. Then X admits a morphism f : X -> P^1_k that is tamely ramified
> everywhere."

(`k` of characteristic two; the paper's whole content. This is the `p = 2`
replacement for Fulton, exactly as KMU's Remark 4.2 says.)

**KLW** (arXiv:2010.01130v2), verbatim:

> "Theorem 1.1 (Fulton). Let X be a smooth, projective, geometrically
> irreducible curve over a field k. If p = 0, or if p > 2 and k is infinite,
> then there exists a finite separable morphism f : X -> P^1_k which is
> everywhere simply ramified, and hence tame."

> "Theorem 1.2. If k is finite, then there exists a finite separable tame
> morphism f : X -> P^1_k."

> "Theorem 7.6. If k is finite, then every SY class of X is trivial.
> Consequently, by Lemma 5.4 and Lemma 6.6, X admits a tame morphism to P^1_k."

> "Theorem 9.3. Suppose that p > 0. (a) If X admits a tame morphism to P^1_k
> ramified only over {0, 1, infinity}, then X descends to F_p-bar. (b)
> Conversely, suppose that k is algebraic over F_p. Then X admits a tame
> morphism to P^1_k ramified only over {0, 1, infinity}."

> "Proof. [...] To prove (b), we may assume at once that k is finite. Apply
> Theorem 2.1 (if p > 2) or Theorem 7.6 (if p = 2) to obtain a tame morphism
> f_0 : X -> P^1_k. Choose a power q of p such that all of the branch points of
> f_0 in P^1_k are defined over F_q, then let f_1 : P^1_k -> P^1_k be the map
> x -> x^{q-1}. The composition f_1 o f_0 is tame and ramified only over
> {0, 1, infinity}, as desired."

Two things follow immediately.

- **(i) The `p = 2` input to KMU Theorem 4.1 exists and is unconditional.**
  KLW Theorem 1.2 (via Theorem 7.6, which uses SY) gives a tame
  `eta_0 : X -> P^1_{F_q}` over the *given* finite field, no extension.
  So the first ingredient of Lemma B is **not** a hypothesis; it is a published
  theorem, and it is *stronger* than what KMU assume at odd `p` (they extend).
- **(ii) KLW Theorem 9.3(b) gives a tame *Belyi* map but no control on `e_P`.**
  Its proof composes with `x^{q-1}` and stops. It says nothing about the
  ramification index over `1`, which is precisely what Prop. 4.3(2) supplies
  and what the weight denominator is. 20-verify sec. 1.3 is right that KLW does
  not hand you Prop. 4.3(2); sec. 1.3-1.5 below supply it.

## 1.2 What Prop. 4.3 actually requires -- the construction, decompiled

**KMU-I sec. 4.1**, verbatim (after "we modify the construction slightly"):

> "By extending the base field, we assume that all branch points of eta_0 and
> every point in S is F_q-rational. We assume moreover that q is large enough
> so that there are two F_q-rational points of P^1_{F_q} which are disjoint
> from the branch points of eta_0 and the image of S. Label these points as 0
> and infinity, and let 1 denote any other F_q-rational point of P^1_{F_q}.
> Consider the composition
>   eta_q : P^1 --(q-1)--> P^1 -> P^1 --(p-1)--> P^1 -> P^1.
> Here, the first and third maps denote the (q-1)- and (p-1)-power maps,
> respectively. The second map is a linear transformation fixing 1 and infinity
> and sending 0 to any other F_q-rational point of P^1_{F_q}. The final map is
> also a linear transformation which fixes infinity and swaps 0 with 1. Then
> eta_q is ramified over {0,1,infinity} and all branch points of eta_q are
> F_q-rational."

> "Proposition 4.3. The composite eta = eta_q o eta_0 : X -> P^1_{F_q} is a
> tame Belyi map such that 1. eta(P) = 0 for each P in S. 2. If eta(P) = 1 then
> the ramification index of eta at P is p-1."

The **original** of this is **KM-exp Lemma 3.1**, whose proof is verbatim:

> "Proof. This is similar to [20, Theoreme 5.6]. By [12, Proposition 7.1],
> there exists a simply branched cover f : X x Spec(F_q^alg) -> P^1. After
> increasing q, we may assume that f descends to a map f' : X -> P^1_{F_q}. We
> also take q large enough so that each tau_i and each branch point of f is
> defined over F_q. We may assume that f' is unramified over 0 and infinity,
> and that f(tau_i) != 0, infinity for each i. This means that
> f(tau_i) in G_m(F_q). After composing f with the (q-1)-th power map and a
> linear transformation, we obtain a map g : X -> P^1_{F_q} that is only
> ramified at 1, 2, and infinity. We then compose g with the (p-1)-th power map
> to obtain a map h : X -> P^1_{F_q}. Note that h is only ramified over
> {0,1,infinity} and the ramification index of every point over 0 is p-1. Swap
> 0 and 1 with a linear transformation to obtain eta."

Decompiled (my reconstruction, and it is forced):

| stage | map | what it does | why |
|---|---|---|---|
| `eta_0` | tame, `Branch(eta_0) u eta_0(S) subset F_q^*` | -- | coordinates chosen so `0, infinity` avoid it |
| `g_1` | `z^{q-1}` | collapses **all** of `F_q^*` to `1`; branched over `0, infinity` with index `q-1` | makes `Branch(g_1 eta_0) subset {0,1,infinity}` and puts `S` over `1` |
| `g_2` | linear, fixes `1, infinity`, `0 -> c` | moves the (unramified) point `0` off the `g_3`-ramification locus | so that the fibre over `0` is *clean* for the next stage |
| `g_3` | `z^{p-1}` | branched over `0, infinity` with index `p-1`; `c, 1 -> 1` | creates a fibre of **uniform** index `p-1` over `0` |
| `g_4` | linear, fixes `infinity`, swaps `0, 1` | `S`-fibre -> `0`; uniform-index fibre -> `1` | Prop. 4.3(1) and (2) |

**REFUTED (witness): the choice of `c` is not free.** After `g_2` the branch
locus is `{c, 1, infinity}`; after `g_3` it is
`{c^{p-1}, 1, infinity} u {0, infinity}`. For `eta` to be *Belyi* one needs
`c^{p-1} in {0,1,infinity}`, and `c not in {0,1,infinity}` forces
**`c^{p-1} = 1`, i.e. `c in mu_{p-1}(F_q) \ {1}`.** KMU's "any other
`F_q`-rational point" is therefore wrong as stated (at every `p`); KM-exp's
`c = 2` is right, because `2^{p-1} = 1` in `F_p` by Fermat and `2 != 1`
for `p >= 3`. If `c^{p-1} != 1` the map has a fourth branch point,
`U = eta^{-1}(V)` is not etale over `V`, and the entire lifting of sec. 4.2
collapses. So this is load-bearing, not cosmetic.

**Consequence at `p = 2`, stated sharply.** The odd-`p` construction
degenerates in *three* independent ways at `p = 2`: (a) `z^{p-1} = z` is the
identity, so no ramification is created; (b) the resulting `e_P = 1` is
incompatible with Riemann-Hurwitz for `g >= 1` (20-verify sec. 2.2's corrected
form); and (c) the auxiliary point `c = 2` *is* the point `0` in
characteristic 2, so even the placement step is empty. All three are the single
fact `mu_{p-1} = {1}` at `p = 2`.

## 1.3 LEMMA B

> **LEMMA B.** Let `q = 2^a`, let `X` be a smooth projective geometrically
> irreducible curve over `F_q`, let `S subset X` be a finite set of closed
> points, and let `e > 1` be an odd integer with `e | q-1`. Then, after
> replacing `F_q` by a finite extension if necessary (only to make the branch
> points and `S` rational and `q` large; see sec. 1.4), there is a tame Belyi
> map `eta : X -> P^1_{F_q}` -- finite, separable, ramified only over
> `{0, 1, infinity}`, all branch points `F_q`-rational -- such that
>
>   1. `eta(P) = 0` for every `P in S`;
>   2. every `P in eta^{-1}(1)` has ramification index exactly `e`;
>   3. consequently `r_1 e = deg(eta)`, `eta^*(1) = sum_{eta(P)=1} e P`, and
>      Riemann-Hurwitz gives `2(g-1) + r_0 + r_1 + r_infinity = deg(eta)`
>      (KMU-I (8) = KM-ab (4)).
>
> In particular `e = 3` is admissible whenever `3 | q-1`, i.e. `a` even.

**Proof.**

*Step 0 (the tame map).* By **KLW Theorem 1.2** (`k` finite, any `p > 0`; its
`p = 2` half is KLW Theorem 7.6, which rests on **SY Theorem 1.1**) there is a
finite separable tame `eta_0 : X -> P^1_{F_q}`. This is exactly the conclusion
of KMU-I Theorem 4.1 / KM-exp's use of [12, Prop. 7.1], and at `p = 2` it
replaces "simply branched" -- which is *false* at `p = 2` (KLW: "when p = 2 ...
simply ramified morphisms are not always tame") -- by the property actually
used, tameness. Enlarge `F_q` so that every branch point of `eta_0` and every
point of `S` is rational, so that `mu_e subset F_q` (automatic from
`e | q-1`), and so that `q+1 > |Branch(eta_0) u eta_0(S)| + 2`. Choose the
coordinate on the target so that `0` and `infinity` avoid
`Branch(eta_0) u eta_0(S)`; hence `Branch(eta_0) u eta_0(S) subset F_q^*`.

*Step 1 (`g_1 = z^{q-1}`).* `q-1` is odd, so `g_1` is tame; it is totally
ramified over `0` and over `infinity` (index `q-1`) and unramified elsewhere,
and `g_1(F_q^*) = {1}`. Put `phi = g_1 o eta_0`. Then
`Branch(phi) subset {0, 1, infinity}` and `phi(S) = {1}`. Because `0` is not a
branch point of `eta_0`, **every point of `phi^{-1}(0)` has index exactly
`q-1`** -- and `phi^{-1}(0) = eta_0^{-1}(0)`, of cardinality `deg(eta_0)`.

*Step 2 (`g_2`).* Choose `c in mu_e(F_q) \ {1}` (nonempty since `e | q-1`,
`e > 1`) and let `g_2` be the unique linear map fixing `1` and `infinity` with
`g_2(0) = c`. Now `Branch(g_2 phi) = {c, 1, infinity}` and `(g_2 phi)(S) = 1`;
the point `0` is *not* in the branch locus.

*Step 3 (`g_3 = z^e`).* `gcd(e, 2) = 1`, so `g_3` is tame; it is totally
ramified over `0` and `infinity` (index `e`), unramified elsewhere, and
`g_3^{-1}(1) = mu_e ni c, 1`. Hence
`Branch(g_3 g_2 phi) subset g_3({c,1,infinity}) u {0,infinity}
= {1} u {0, infinity}`, using `c^e = 1`. The fibre over `0` is
`g_3^{-1}(0) = {0}` with `e_{g_3}(0) = e`, and `0` is unramified for
`g_2 phi` (Step 2), so **every point of `(g_3 g_2 phi)^{-1}(0)` has index
exactly `e`**, and there are `deg(g_2 phi) = (q-1) deg(eta_0)` of them.

*Step 4 (`g_4`).* The linear map fixing `infinity` and swapping `0` and `1`
carries the `S`-fibre (over `1`) to `0` and the uniform-index-`e` fibre (over
`0`) to `1`. Set `eta = g_4 g_3 g_2 g_1 eta_0`. Claims (1) and (2) hold.

*Tameness of the composite.* Ramification indices multiply; each factor is odd
(`e_{eta_0}` odd because `eta_0` is tame at `p = 2`; `q-1` odd; `e` odd), so
every index of `eta` is odd, i.e. prime to `p = 2`. `eta` is separable
(composite of separable maps) and finite.

*Claim (3).* All points over `1` have index `e`, and indices over a point sum
to the degree, so `r_1 e = deg(eta)` and `eta^*(1) = sum_{eta(P)=1} e P` has
degree `deg(eta)`. Tame Riemann-Hurwitz for a map branched only over
`{0,1,infinity}` gives `2g-2 = -2 deg(eta) + sum_{Q}(deg(eta) - r_Q)`, i.e.
`2(g-1) + r_0 + r_1 + r_infinity = deg(eta)`. **QED**

### 1.3.1 The question the charge asks explicitly: where do the *other* ramification points of `z -> z^3` go?

`z -> z^e` has exactly two ramification points, `z = 0` and `z = infinity`.

- `z = 0` is the *wanted* one: it becomes the fibre over the final `1`,
  uniformly of index `e`. That is the whole point of `g_2` (it evacuates the
  point `0` so this fibre is clean).
- `z = infinity` maps to `infinity`, which `g_4` fixes. So the second
  ramification point lands **over `infinity`** and its points of `X` have index
  `3 (q-1) e_{eta_0}` -- large, but odd, hence tame.

**Does that create a new Type-2 point, or collide with `S`?** No, on both
counts, and the reason is structural, not accidental. KMU-I sec. 4.3, verbatim:

> "our assumptions on the branching of eta allow us to choose a uniformizer
> t_P in F_P such that t_P^{e_P} = u_Q [...] Evidently, if eta(P) = 0 or
> infinity then sigma(t_P) = t_P^p. The local Frobenius for eta(P) = 1 is more
> complicated: sigma(t_P) = ((t_P^{p-1} + 1)^p - 1)^{1/(p-1)}."

Because `sigma(u_0) = u_0^p` and `sigma(u_infinity) = u_infinity^p` are *pure*
`p`-th powers, extracting the `e_P`-th root is exact and
`sigma(t_P) = t_P^p` **whatever `e_P` is**. Ramification over `0` and
`infinity` is therefore *free*: it never produces a Type-2 estimate. Only over
`1`, where `sigma(u_1) = (u_1+1)^p - 1` is not a pure power, does the
`e_P`-th root produce the `(1 + p y)^{1/e_P}` factor -- and that is the single
local estimate the whole `p >= 3` hypothesis lives in. `S` sits over `0`, the
new ramification sits over `infinity`, and every point over `1` has the *same*
index `e`; there is no fibre over `1` with a mixed or different `e_P`.
(The exponent in the displayed local Frobenius is `e_P`, written `p-1` because
KMU's `e_P` *is* `p-1`; at `p = 2, e_P = 3` it reads
`sigma(t_P) = ((t_P^3+1)^2 - 1)^{1/3}`, which is exactly the operator 01
sec. 4, 03 and 04 computed. The `1/e_P`-power binomial series converges because
`gcd(e_P, p) = 1`.)

### 1.3.2 `mu(P) = e_P` and the global count -- checked against the source

KMU-I (11) defines `mu(P) = 0` for `Q in {0, infinity}` and `p-1` for `Q = 1`
(the printed text says "0 if Q = 0 or 1", an obvious typo -- the display and
every use say `0` for `0, infinity`). Its role, verbatim from the proof of
Prop. 4.10:

> "The kernel is precisely the global sections of the line bundle L(D), where
> D = sum_{eta(P)=1} (p-1)P."

So `D = eta^*(1)` **iff `mu(P) = e_P`**, and then `deg D = deg(eta)`, so
Riemann-Roch gives `N = deg(eta) + 1 - g = g - 1 + r_0 + r_1 + r_infinity`
(KMU-I (13)) -- the number that Lemma 7.12 (Deuring-Shafarevich) pins as the
count of slope-0 segments and that Cor. 7.14 cancels down to `g-1+|S|`. With
`e_P = 3`: `D = sum 3P = eta^*(1)`, `deg D = 3 r_1 = deg(eta)`, same `N`.
**Confirmed**: `mu(P) = e_P` is forced, it is `3` here, and 01 sec. 2b / 04
sec. 7.4 are right. KM-ab's Prop. 7.2 uses the same divisor with the same
`(p-1) = e_P` and the same conclusion (sec. 2 below, row 12).

## 1.4 The arithmetic side condition `3 | q-1`: necessary at degree 3, and free

Write the auxiliary stage as one map `h = g_4 g_3 g_2 : P^1 -> P^1`. What
Lemma B needs of it is: `h` tame; `Branch(h) subset {0,1,infinity}`;
`h({0,1,infinity}) subset {0,1,infinity}`; `h(1) = 0`; and every
`y in h^{-1}(1)` has `e_h(y) = 3` with `y not in {0,1,infinity}` (so that the
earlier stage, whose branch locus is `{0,1,infinity}`, is unramified there).

**Classification at degree 3 (PROVED).** A tame degree-3 self-map of `P^1` in
characteristic 2 has, by Riemann-Hurwitz, `sum (e-1) = 4` with every `e` odd
(`e = 2` is *wild* at `p = 2`) -- hence exactly two totally ramified points, so
`h` is `mu o z^3 o nu` for `mu, nu in PGL_2`. Running the four possible
placements of the second ramification point (over `0` or over `infinity`, with
`h(0), h(infinity) in {0, infinity}`) gives in every case the same equation:
the ramification point `alpha` over `1` must satisfy `alpha^3 = 1` with
`alpha != 1`. Two of the four cases, worked:

- `h^{-1}(infinity) = {infinity}`, `h(0) = 0`: `h = lambda(z+alpha)^3 + 1`,
  `h(1) = 0` and `h(0) = 0` give `lambda(1+alpha)^3 = lambda alpha^3 = 1`,
  hence `(1 + 1/alpha)^3 = 1`.
- `h^{-1}(0) = {1}`, poles simple at `0, beta, infinity`:
  `h = lambda(z+1)^3/(z(z+beta))`, and matching
  `lambda(z+1)^3 + z(z+beta) = lambda(z+alpha)^3` coefficientwise in
  characteristic 2 gives `lambda + 1 = lambda alpha`, `lambda + beta =
  lambda alpha^2`, `lambda = lambda alpha^3`, so `alpha^3 = 1`, `alpha != 1`.

**Machine confirmation** (`noh05/deg3b.py`, exact `GF(2^n)` arithmetic;
enumerates every degree-3 candidate of the forced shape, checks tameness,
Belyi-ness via RH saturation `sum(e-1) = 4`, and all five conditions):

```
q=2^1= 2   3|q-1: False   #maps:    0
q=2^2= 4   3|q-1: True    #maps:    8   alpha=2 A=[1,1,1,1] B=[0,2,3]
q=2^3= 8   3|q-1: False   #maps:    0
q=2^4=16   3|q-1: True    #maps:    8   alpha=6
q=2^5=32   3|q-1: False   #maps:    0
q=2^6=64   3|q-1: True    #maps:    8   alpha=58
```

i.e. **the degree-3 auxiliary map exists over `F_{2^a}` iff `3 | q-1` iff `a`
is even**, and `alpha` is always a primitive cube root of unity. (Whether some
*higher-degree* auxiliary map could achieve `e_P = 3` over a field with
`3 nmid q-1` is **OPEN**; it does not matter, by the next paragraph.)

**The condition is free (base-change licence, and why it is sound).**
KM-ab sec. 2.1, verbatim: *"It is enough to prove Theorem 1.1 after replacing q
with a larger power of p. In particular, we increase q throughout the article
if it simplifies arguments."* KM-ab Lemma 3.1 and KM-exp Lemma 3.1 both begin
"After increasing q"; KMU-I Thm. 4.1 says "After extending the base field" and
sec. 4.1 extends again. Both papers therefore *already* consume an unspecified
base extension, and a quadratic one makes `a` even.

The sources assert the reduction; here is the argument (**PROVED**, and
`p`-uniform), since it is the only thing that makes the side condition
harmless. Let `F_{q^m}/F_q` and `rho' = rho|_{pi_1(X_{F_{q^m}})}`.
`H^1_c(X_{F_q-bar}, F_rho)` is unchanged and `Frob_{q^m} = Frob_q^m`, so the
inverse roots become `alpha_i^m`; and
`v_{q^m}(alpha_i^m) = m v_p(alpha_i)/(m log_p q) = v_q(alpha_i)`, so
**`NP_q(rho)` is unchanged as a polygon**. On the Hodge side: `g` is unchanged;
Swan conductors are invariant under unramified base change; the slope multiset
is indexed by the *geometric* points of `S` (forced by the degree count
`dim H^1_c = 2g-2+|S|+sum d_P` from Grothendieck-Ogg-Shafarevich, which matches
`HP`'s length `2(g-1+|S|) + sum(d_P-1)`), so `HP_q(rho)` is unchanged;
ordinarity of `X` is geometric. For KM-ab's general `rho` one also needs
`Omega_rho` invariant: `eps' = eps(1 + q + ... + q^{m-1})` has base-`p` digits
equal to `m` copies of those of `eps`, so `omega' = m omega` and `a' = ma`,
whence `Omega' = Omega`. Hence Theorem 1.1 over `F_{q^m}` implies it over
`F_q`. **So Lemma B costs nothing.**

## 1.5 An explicit instance, machine-verified

Take `X = P^1`, `eta_0 = id` (tame, unbranched), `S subset F_q^*`, `omega` a
primitive cube root of unity in `F_q` (`3 | q-1`). Then
`g_2(z) = (1+omega) z + omega` and

```
    eta(z) = ( (1+omega) z^{q-1} + omega )^3 + 1,      deg eta = 3(q-1).
```

By hand: `eta - 1 = P(z)^3` with `P = (1+omega)z^{q-1} + omega` separable
(`gcd(P, P') = 1` since `P(0) = omega != 0`), so the fibre over `1` is
`q-1` points each of index exactly `3`, none of them `0, 1, infinity`;
`eta = 0` iff `P in mu_3`, giving `z = 0` (index `q-1`), `z in F_q^*` (simple,
and this is where `S` sits), and the `q-1` roots of `z^{q-1} = omega` (simple);
`eta^{-1}(infinity) = {infinity}` with index `3(q-1)`. So
`r_0 = 2q-1, r_1 = q-1, r_infinity = 1`, all indices odd, and
`sum(e-1) = 2 deg - 2` -- RH is saturated by the three fibres, so there is no
ramification anywhere else and `eta` is Belyi.

Independent machine check (`noh05/compose.py`; brute force over
`K = F_{2^{3a}}`, multiplicities by exact synthetic division):

```
  q=4  (K=F_2^6)   deg eta=9
   fibre over 1: r1=3,  indices={3}, contains 0/1? False
   fibre over 0: r0=7,  indices=[3,1,1,1,1,1,1]; S=F_q^* over 0 with e=1: True
   RH: sum(e-1)=16 = 2*deg-2  -> Belyi (saturated); all e odd: True
   eq(8): 2(g-1)+r0+r1+rinf = 9 = deg eta ; r1*3 = 9
  q=16 (K=F_2^12)  deg eta=45
   fibre over 1: r1=15, indices={3}, contains 0/1? False
   fibre over 0: r0=31, indices=[15,1,...,1]
   RH: sum(e-1)=88 = 2*deg-2 -> Belyi; all e odd: True
   eq(8): 2(g-1)+r0+r1+rinf = 45 = deg eta ; r1*3 = 45
```

Both instances reproduce the hand computation exactly, including KMU-I (8) and
`r_1 e_P = deg(eta)`.

## 1.6 Riemann-Hurwitz and the `mu(P) = e_P = 3` consistency used in 01 sec. 2b

Collected, with the source equations:

| item | KMU-I | KM-ab | with `e_P = 3` |
|---|---|---|---|
| index over `1` | `p-1` (Prop. 4.3(2)) | `p-1` (Lemma 3.1) | `3` (Lemma B) |
| `r_1 e_P = deg eta` | sec. 4.1 | sec. 3.2 | `3 r_1 = deg eta` |
| RH | (8) `2(g-1)+r_0+r_1+r_inf = deg eta` | (4), same | unchanged (tame RH, index-free) |
| truncation | `mu(P) = p-1` (11) | `mu(Q) = p` (33), i.e. drop poles `<= p-1` | `mu(P) = 3`; drop poles of order `<= 3` |
| divisor | `D = sum (p-1) P = eta^*(1)` | `D_j = sum (p-1)[P_{1,i}] - sum n_{Q,j}[Q]` | `sum 3 P`, `deg = deg eta` |
| rank | `N = g-1+r_0+r_1+r_inf` (13) | `g-1+r_0+r_1+r_inf - Omega_rho` | unchanged |
| cancellation | Cor. 7.14 removes `r_0+r_1+r_inf-|S|` | sec. 7.3 removes `r_0+r_1+r_inf-m` | unchanged, `e_P`-free |

Every `e_P`-dependence enters only through `r_1 = deg(eta)/e_P` and cancels
against `deg D = e_P r_1 = deg(eta)`. **The final polygon is the
Kramer-Miller ramification-defined one, independent of `e_P`** -- confirming 04
sec. 7.4 by an independent route (I re-derived it from KM-ab's Prop. 7.2 as
well as KMU's Prop. 4.10).

## 1.7 `mu(P) = e_P = 3` versus the `mu(P) = e_P` consistency in the weight

04's admissibility condition (A1) is `a(k) = 0` for `k <= mu(P) = 3`. On the
KM-ab side this is literally equation (21), `ker(pr) cap O_R subset O_R^con`,
which holds because `b(-k) = floor((k-1)/(p-1)) = 0` exactly for
`k <= p-1 = e_P`. So (A1) is not a convention -- it is the same statement in
both papers, and 04's weight (`a(k) = 0` for `k <= 3`) satisfies it for
`e_P = 3`. **Consistent.**

## 1.8 Variant with no side condition at all: `e_P = q-1`

Delete stages `g_2, g_3`: set `eta = g_4 o g_1 o eta_0`. By Step 1 above,
*every* point of `phi^{-1}(0)` already has index exactly `q-1` (odd, `> 1` for
`q >= 4`), so `g_4` alone gives a tame Belyi map with `eta(S) = {0}` and
**uniform index `e_P = q-1` over `1`**, with no root-of-unity condition and no
extra stage. More generally the `e`-power stage exists exactly when
`e | q-1` (`c in mu_e \ {1}`), so:

> **LEMMA B (general form, PROVED).** For every odd `e > 1` with `e | q-1`
> there is a tame Belyi `eta` with `eta(S) = {0}` and every point over `1` of
> index exactly `e`. (`e = q-1` needs no auxiliary stage at all.)

At odd `p`, `p-1 | p^a - 1 = q-1` automatically -- which is why KMU's `e = p-1`
is always available. And `e | q-1` is *also* exactly the condition for
`mu_e subset Z_q`, hence for the `Gal(E/E_0) = Z/e` eigenspace decomposition
`A_{pi,P} = (+)_i t^{-i} R_q((u))` that KMU Def. 6.3 uses. The two conditions
coincide; this is not a coincidence, both are "`e`-th roots of unity live in
the base".

**Trade-off.** `e = 3` matches 04's proved weight (Theorem 3's mod-6 analysis is
specific to `e = 3`) but needs `3 | q-1`, i.e. a quadratic base extension when
`a` is odd. `e = q-1` needs no extension but would need 04's Theorem 3
re-proved for `e = q-1` (04 states Theorems 1, 2 and Lemma A hold for **every**
odd `e`, and Theorem 4's sharpness threshold generalizes to `1/(2e)`; only
Theorem 3's case analysis is `e = 3`-specific). Since sec. 1.4 shows the
extension is free, **take `e = 3`.**

## 1.9 Status of Lemma B

**PROVED**, with exactly one external input, quoted verbatim in sec. 1.1:

> **CONDITIONAL-ON:** KLW = Kedlaya--Litt--Witaszek, arXiv:2010.01130v2,
> Theorem 1.2 ("If k is finite, then there exists a finite separable tame
> morphism f : X -> P^1_k"), whose `p = 2` case is their Theorem 7.6 and rests
> on SY = Sugiyama--Yasuda, arXiv:1708.03036v2 = Compos. Math. 156 (2020)
> 325-339, Theorem 1.1.

This is the *same* kind and degree of dependence that KMU-I has at odd `p` on
Fulton [9] (KMU Theorem 4.1). So Lemma B is no longer a gap: it is a citation.
04 sec. 8's "conditional on KMU Rem. 4.2's own citation, which I did not fetch"
is now discharged -- I fetched both citations and they say what is needed, and
KLW is *stronger* than needed (no base extension for the tame map itself).

Everything else in Lemma B -- the 3-power replacement, the `c in mu_3` fix, the
ramification bookkeeping, `mu(P) = e_P = 3`, RH, and the base-change
invariance -- is proved above and machine-verified.

---

# PART 2 -- THE KM-ab GLOBAL AUDIT

## 2.1 What KM-ab's global argument is, and where `p >= 3` could hide

KM-ab (arXiv:2006.04936v2) proves: **Theorem 1.1.** *"The q-adic Newton polygon
`NP_q(L(rho,s))` lies above the Hodge polygon `HP(rho)`"*, for an arbitrary
non-trivial finite character `rho = rho^wild (x) chi` on a smooth affine curve,
`p >= 3` standing hypothesis (sec. 1, verbatim: "Let p be a prime with
p >= 3").

**For the NoH-p2 target (`rho` of 2-power order) the tame part is trivial**:
`chi = 1`, `n = 0`, `eps_Q = 0`, `omega_Q = 0`, `Omega_rho = 0`,
`S_Q = {1/s_Q, ..., (s_Q-1)/s_Q}` and
`HP(rho) = 0^{g-1+m} (+) 1^{g-1+m} (+) (+)_i S_{tau_i}` -- **identical to KMU-I
sec. 1.2's `HP_q(rho)` with `m = |S|`, `s_Q = d_P`.** This collapses a large
part of the paper (the `Omega_rho` bookkeeping, the restriction-of-scalars
`(+)_j chi^{(x)p^j}` device, the `a`-th-root obstacle "only guaranteed to exist
if the order of Im(chi) divides p-1") to triviality: `|Im(chi)| = 1` divides
`p-1` at every `p`.

I inventoried **every** occurrence of `p-1` in KM-ab (44 of them) and
classified each as (i) a ramification index of `eta` -- degenerates at `p = 2`;
(ii) a normalization tied to `pi = (-p)^{1/(p-1)}` -- cancels; (iii) a digit
bound -- harmless. The table is the result.

## 2.2 The table

Verdicts: **UNCHANGED** = statement and proof survive verbatim at `p = 2`;
**RESTATED** = statement changes, restatement given; **BREAKS** = fails, with
witness.

| # | KM-ab item | invokes `p >= 3` / consumes `e_P` / strict? | verdict at `p = 2` |
|---|---|---|---|
| 1 | sec. 1.1 invariants `(s_Q, e_Q, eps_Q, omega_Q)`, `Omega_rho = (1/(a(p-1))) sum omega` | `p-1` as normalization; digits `0 <= e_{Q,i} <= p-1` | **UNCHANGED.** At `p = 2`, `a(p-1) = a != 0`, digits are bits. For 2-power `rho`, all are `0`. |
| 2 | sec. 1.1 `HP(rho)` | `omega_Q/(a s_Q (p-1))` shifts | **UNCHANGED**; `= 0` for 2-power `rho`, and then `HP(rho)` is exactly KMU-I's. |
| 3 | Remark 1.2 (endpoints agree; duality `omega' = a(p-1) - omega`) | `p-1` | **UNCHANGED.** Euler-Poincare + Poincare duality; no parity. |
| 4 | Cor. 1.6 (cyclic covers), multiplicity `p^{j-1}(p-1)` | `p-1` factor | **UNCHANGED**: `= 2^{j-1}` at `p = 2`; a corollary of Thm. 1.1, inherits its status. |
| 5 | sec. 2.1 `pi = (-p)^{1/(p-1)}`; `pi_s = pi^{1/s}` | root index `p-1` | **UNCHANGED**: at `p = 2`, `pi = -2`, `v_p(pi) = 1`. (Note 6's `pi = -2` is right *here*; 03/20 were right that it is not the `AH` splitting parameter.) |
| 6 | sec. 2.1 "It is enough to prove Theorem 1.1 after replacing q with a larger power of p" | -- | **UNCHANGED**, and *asserted without proof*; proof supplied in sec. 1.4 above. This is what makes Lemma B's `3 | q-1` free. |
| 7 | **Lemma 3.1** ("each `P in eta^{-1}(1)` has ramification index `p-1`"), proof = KM-exp Lemma 3.1 | **the geometric input** | **BREAKS at `p = 2`** (witness: `z^{p-1} = z`; `c = 2 = 0`; `e_P = 1` contradicts RH for `g >= 1`). **Repaired by LEMMA B** (Part 1), with `e_P = 3`. This and row 11 are the *only* two breaks. |
| 8 | sec. 3.2 `r_1(p-1) = deg(eta)`, RH (4), tame lifting `X -> P^1_{O_L}` by deformation theory of tame coverings | `e_P` | **RESTATED**: `3 r_1 = deg(eta)`; (4) unchanged (tame RH is index-free); tame deformation theory needs only tameness, which Lemma B supplies. |
| 9 | sec. 3.4 local Frobenius `t_0 -> t_0^p`, `t_inf -> t_inf^p`, `t_1 -> (t_1+1)^p - 1`; `u_Q^{nu_Q} = ((u_Q^{p-1}+1)^p-1)^{1/(p-1)}` | `e_P` in the radical index | **RESTATED**: index `3`; `(1+py)^{1/3}` converges since `gcd(3,2)=1`. |
| 10 | sec. 4.1 Type 1 (`t -> t^p`), Prop. 4.1, `U_p(O_{E_s}) subset O_{E_{s/p}}` | none | **UNCHANGED.** The `pi_s^{n(p-1)}` gain in (11) normalizes to slope `n/s` at **every** `p` because `v_p(pi) = 1/(p-1)`: the `(p-1)` is exactly cancelled, so there is **no** multiplicative slack here that vanishes at `p = 2`. (Answers coordinator risk R2 on the wild side, independently of 04.) |
| 11 | **sec. 4.2 Type 2**, `b(n) = floor((-n-1)/(p-1))`, **Prop. 4.2** (`U_p(p^{b(-k-np)}t^{-k-np}) in p^n D`, `U_p(D) subset D`), citing [15, Prop. 4.4] | **the local estimate** | **BREAKS at `p = 2`** exactly as KMU-I Remark 6.5 does: `b(-k) = k-1` is the `e_P = 1` weight. **Repaired by 04's Theorems 1-3** with `e = 3` and `a(k) = floor((k-1)/3) + (k mod 2)`; note `D = prod_n p^{b(n)} t^n O_L` is *already coefficientwise*, so 04's non-eigenspace weight drops straight in. |
| 12 | sec. 5.1 `a`-th root exists only if `|Im(chi)| | p-1`; workaround `(+)_j chi^{(x)p^j}` | `p-1` | **UNCHANGED**; **vacuous** for 2-power `rho` (`|Im(chi)| = 1`). At `p = 2` with `chi != 1` the workaround is *mandatory*, and it is `p`-uniform. |
| 13 | sec. 5.2.1-5.2.2 Props. 5.4, 5.5 (`E_r = prod prod E([r_{i,j}]t^{-j} gamma_{n-i})`, `v_p(gamma_i) = 1/(p^{i-1}(p-1))`) | `p-1` in `v_p(gamma_i)` | **UNCHANGED**: `v_2(gamma_i) = 1/2^{i-1}`, matching 02/03's measured rates (1 at `m=1`, 1/2 at `m=2`). No parity hypothesis; confirms 20-verify sec. 4.3. |
| 14 | sec. 5.2.3 Prop. 5.6 (tame characters, `u = t^{1/(q-1)}` Kummer) | `q-1` (odd at `p=2`) | **UNCHANGED.** |
| 15 | sec. 4.1.1 "We know `-q(e,i) <= a(p-1)`, which implies `pi_{as}^{q(e,j)} pi_s^p in O_L`" | integrality claim | **REFUTED (witness), `p`-uniform**: `p=2, a=3, eps=3, j=1` gives `-q = 4 > 3`; `p=3, a=2, eps=5, j=1` gives `-q = 5 > 4`. The weaker bound `-q <= ap` also fails (`p=2, a=4, eps=7, j=3`: `-q = 9 > 8`) and cannot be fixed by shrinking `s` (both terms scale as `1/s`). **NEEDS-RESTATEMENT in the source; vacuous for 2-power `rho`** (`eps = 0 => q(e,j) = 0`). Machine-swept `p in {2,3,5}`, `a <= 6`, all `eps`. |
| 16 | (18) `1/s_Q - omega_Q/(a s_Q (p-1)) >= 1` (a *choice* of `s_Q`) | `p-1` in the denominator | **UNCHANGED, but the feasibility argument is missing in the source and supplied here**: `eps_Q <= q-2` forces `omega_Q <= a(p-1) - 1`, so `1 - omega_Q/(a(p-1)) >= 1/(a(p-1)) > 0` and a small enough `s_Q` works. At `p = 2`: `omega_Q <= a-1`. Machine-verified for `p in {2,3,5}`, `a <= 6`. Trivial for 2-power `rho`. |
| 17 | (21) `ker(pr) cap O_R subset O_R^con` | `b(n) = 0` for `n >= -(p-1)` | **RESTATED**: this *is* 04's condition (A1), `a(k) = 0` for `k <= e_P = mu(P) = 3`, which 04's weight satisfies. |
| 18 | (22) `U_p o C(O_R^con) subset O_R^con` | -- | **RESTATED**: this is 04's (A3) in the weak form `d(k) >= 0`, implied by `d(k) >= 1`. |
| 19 | sec. 6 (normed spaces, formal bases, Fredholm determinants, Lemmas 6.12, 6.13) | none | **UNCHANGED.** Pure `p`-adic functional analysis; the only hypothesis is `lim col_i = infinity` (Lemma 6.12), i.e. `d(k) -> infinity`, which 04's Theorem 3 gives (`d(k) ~ k/6`). |
| 20 | sec. 7.1 Monsky trace formula; "each slope of `NP_q(1/det(1-sqU_q ...))` is at least one" | non-strict `>= 1`, consumed by a strict `<1` truncation | **UNCHANGED.** Self-supplying, as in KMU Lemma 7.1. |
| 21 | Prop. 7.2 (`pr(V^_0) = O_R^trun`; `ker` has dimension `a(g-1+r_0+r_1+r_inf-Omega_rho)`), via Lemma 7.3, `D_j = sum (p-1)[P_{1,i}] - sum n_{Q,j}[Q]`, `(p-1)r_1 = deg(eta)`, RR | `e_P`; needs `deg D_j > 2g-2` | **RESTATED with `3` in place of `p-1`**: `deg D_j = 3r_1 - sum n = deg(eta) - sum n`, and `sum n_{Q,j} <= m <= r_0+r_inf` by (14), so RR gives `g-1+r_0+r_1+r_inf - sum n`, and (15) sums to `a(...-Omega_rho)`. **Identical.** *This is the step that has no KMU-style Lemma-E problem*: it is carried out on the unweighted space `V` and on the reduction mod `m`, so it is weight-independent. |
| 22 | sec. 7.2 case (I) (`i in K`): `col >= 0`, multiplicity `a(g-1+r_0+r_1+r_inf-Omega_rho)` | -- | **UNCHANGED** given (22)/row 18. |
| 23 | sec. 7.2 **case (II)** (`eta(Q) = 1`): `n >= p`; `n = k+pm`, `0 <= k < p`; `b(n) >= m`; "each slope in `P_Q` is at least one" | **the unique consumer** | **RESTATED**: `n > mu(Q) = 3`; the gain is `d(n)`, the weight is `a(n)`, the two hypotheses are exactly 04's **(A4)** `a(n) >= d(n)` and **(A3)** `d(n) >= 1` (both proved in 04), plus `d(n) -> infinity` for row 19. `P_Q = {d(n)}_{n>3}` instead of `{1,2,3,...}^{ap}`; only "`>= 1`" is consumed, so the multiset shape is irrelevant. |
| 24 | sec. 7.2 cases (III),(IV) (`eta(Q) in {0,inf}`): slopes `n/s_Q - omega_Q/(a s_Q(p-1))` | `p-1` normalization | **UNCHANGED**; `= n/s_Q` for 2-power `rho`, i.e. exactly the local Hodge slopes `S_Q`. Matches 03's measured wild optimum `a_true(k) = k/s` at `p = 2`. |
| 25 | Prop. 7.4 (`det(1-sU_p C|V) = det(1-sU_p C|G^con_E)` by similarity) | weight enters only here | **UNCHANGED for any weight** for which `{x_i e_i}` is a formal basis of `V^con` -- true by construction for the coefficientwise `D*` built from 04's `a(k)`. |
| 26 | sec. 7.3 (cancel `r_0+r_1+r_inf-m` slope-0 factors from `L(rho,V,s) = L(rho,s) prod (1-rho(Frob_Q)s)`; Euler-Poincare for the slope-1 half) | `r_1` only | **UNCHANGED**; `e_P`-free, exactly as KMU Cor. 7.14. |

**Verdict.** Rows 7 and 11 are the only breaks, and they are the *same pair* as
in KMU-I (sec. 4.1 + sec. 6.1.2). Rows 15 and 16 are `p`-uniform source
defects, both vacuous for the NoH-p2 target. Nothing in KM-ab's global argument
consumes strictness or multiplicative slack that vanishes at `p = 2`: every
strict inequality is either definitional (`<1` truncation) or supplied by a
`p`-independent margin, and every `(p-1)` outside rows 7/11 is a normalization
that cancels against `v_p(pi) = 1/(p-1)` or a digit bound that stays
non-degenerate because `eps_Q <= q-2`.

## 2.3 Does the theorem-candidate need KM-ab's globals? -- SETTLED

04 sec. 9 left this open ("I audited KMU-I sec. 6-7 only"). Both halves now
have answers.

**(a) KMU-I is self-contained for `NP >= HP`. PROVED.** KMU-I cites [16] =
KM-ab only in sec. 1 (lines 121, 190, 279-280, 290, 312, 422 of the extracted
text); **there is no citation of [16] anywhere in sec. 4-7**, and the one
citation of [17] = KM-exp in the body is Lemma 6.2's "[17, Corollary 4.7]",
which 04's Theorem 1 supersedes. What KMU-I proves on its own:

> **Corollary 6.8 (Global Hodge Bound)**, verbatim: "The Newton polygon
> `NP^{<v_pi(p)}_{pi_q}(Theta_q | V_pi^dagger)` lies on or above the convex
> polygon with slope set `{0,...,0}_r (+) (+)_{P in S} {k(p-1)/delta_P :
> 1 <= k < v_pi(p) delta_P}`."

Normalize: `v_pi(p) = p^{n-1}(p-1)` and `delta_P = d_P/p^{n-1}`, so the local
slopes are `k(p-1)/delta_P / v_pi(p) = k/d_P`, and the truncation `< v_pi(p)`
is `< 1`; the range `k < v_pi(p) delta_P = (p-1)d_P` truncates to
`k <= d_P - 1`. So Cor. 6.8 says, in normalized terms,

```
    NP^{<1}(Theta_q|V^dagger)  >=  {0}_N  (+)  (+)_{P in S} {1/d_P, ..., (d_P-1)/d_P},
```

with `N = g-1+r_0+r_1+r_inf` (the proof's own count: "`v_pi(Theta~(e^{m_e}_{0,k}))
>= 0` for all `1 <= k <= N`"; the statement prints the multiplicity as `r`,
which clashes with the truncation parameter `r` of sec. 7 and is almost
certainly a typo for `N`). Cor. 7.14's cancellation of `r_0+r_1+r_inf-|S|`
slope-0 segments then gives `NP_q^{<1}(rho) >= HP_q^{<1}(rho)` -- KM-ab
Theorem 1.1 below slope 1. The rest is the `p`-uniform reflection argument: the
polygons have equal endpoints (Euler-Poincare + Poincare duality, KM-ab
Remark 1.2), `HP` is reflection-symmetric for `chi = 1`, and past the `<1`
region `NP` grows with slope `>= 1` while `HP` grows with slope exactly `1`.
**So the `p = 2` theorem-candidate does not need to import KM-ab.**

**(b) But routing through KM-ab is *cheaper*, because it dissolves Lemma E.
PROVED.** 04 sec. 7.3 had to introduce **Lemma E** (the sec.-6.2 exact sequence
for a non-eigenspace weight) because KMU Def. 6.3 builds `A^m_{pi,P}` as a
`Gal(E/E_0)`-eigenspace sum `(+)_i t^{-i} B^m_{pi,P}`, and 04 sec. 7.2 shows
(correctly) that the parity-corrected weight is *not* an eigenspace regrading.
KM-ab has no such construction: its local growth module is

> (12), verbatim: `D = prod_{n in Z} p^{b(n)} t^n O_L`, "which we regard as a
> sub-`O_L`-module of `O_{E^dagger}`",

a **coefficientwise** condition -- exactly the shape of 04's
`A^{m,*}_{pi,P} = {sum b_k t^{-k} : v_pi(b_k) >= a(k)/m_P}`. And the
Riemann-Roch step that KMU assert as an exact sequence is, in KM-ab,
Proposition 7.2 -- *proved*, via Lemma 7.3 (reduction mod `m`) on the
**unweighted** Banach space `V`, with the weight entering only afterwards
through the similarity of Prop. 7.4. The only place the weight touches that
argument is (21) `ker(pr) cap O_R subset O_R^con`, i.e. 04's (A1). Therefore:

> **On the KM-ab route, `NP >= HP` at `p = 2` needs exactly two new
> ingredients -- LEMMA B and 04's LEMMA A/Theorem 3 -- and nothing else.
> Risk R3 / Lemma E does not arise.**

This also re-labels R3: it is not a `p = 2` risk and not even a real gap in the
mathematics; it is an artifact of KMU-I's presentation choice, and KM-ab's own
earlier presentation avoids it.

---

## 3. Final dependency graph of the theorem-candidate

```
 TARGET A:  NP_q(rho) >= HP_q(rho),  p = 2, arbitrary smooth affine X/F_q,
            rho of 2-power order          [ = KM-ab Thm 1.1 at p = 2 ]
   |
   +-- KM-ab sec. 2, 3.2-3.4, 5, 6, 7.1, 7.2 (I)(III)(IV), 7.3 ....... CITE (p-uniform; audit sec. 2.2)
   +-- KM-ab Lemma 3.1 (geometry, e_P over 1) ....................... **LEMMA B**  [PROVED, this file]
   |      +-- KLW arXiv:2010.01130 Thm 1.2 / 7.6 .................... CONDITIONAL-ON (published; quoted)
   |      +-- SY arXiv:1708.03036 Thm 1.1 = Compos. Math. 156 ....... CONDITIONAL-ON (published; quoted)
   |      +-- base-change invariance of NP_q, HP_q .................. PROVED (this file, sec. 1.4)
   +-- KM-ab sec. 4.2 / Prop. 4.2 (Type-2 estimate) ................. **LEMMA A + Thms 1-3 of 04** [PROVED]
   +-- KM-ab (21) = (A1), (22) = (A3>=0), b(n)>=m = (A4) ............ PROVED in 04
   +-- Lemma E / eigenspace exact sequence ......................... **NOT NEEDED** (sec. 2.3(b))
   +-- KM-ab sec. 4.1.1 "-q(e,i) <= a(p-1)" ........................ REFUTED (witness) but VACUOUS here
                                                                      (eps = 0 for 2-power rho); p-uniform
 TARGET B:  KMU-I Thm 1.1 at p = 2 (the touching/vertex criterion)
   |
   +-- KMU-I sec. 2-3, 4.2-4.4, 5, 6.1(wild), 7.1-7.4 ............... CITE (p-uniform; 04 sec. 7 table)
   +-- KMU-I Prop. 4.3 (geometry) ................................... **LEMMA B**  [PROVED, this file]
   +-- KMU-I Def. 6.3 / Lemma 6.2 / Prop. 6.4 / Rem. 6.5 ............ **04 Thms 1-3** [PROVED]
   +-- KMU-I sec. 6.2 exact sequence for A^{m,*} .................... **LEMMA E**: OPEN IN KMU AT EVERY p;
                                                                      04 reduces it to KMU's own assertion
                                                                      with no loss for r in [0,1];
                                                                      dissolved entirely if one re-runs the
                                                                      argument in KM-ab's coefficientwise
                                                                      formulation (sec. 2.3(b))
   +-- KMU-I Lemma 7.11 (unique consumer of d(k) >= 1) .............. UNCHANGED given 04 Thm 3
   +-- Deuring-Shafarevich (Lemma 7.12), Katz-Gabber, Liu-Wei,
       Elkik, Monsky trace formula ................................. CITE (all p-uniform, not re-verified here)
```

**Net change to the project's risk register (Note 8):**

- **R4 (the 3-power Belyi modification at `p = 2`) -- CLOSED, PROVED.**
- **R5 (global count `N` with `e_P = 3`) -- CLOSED, PROVED** (sec. 1.6; verified
  against *both* KMU Prop. 4.10 and KM-ab Prop. 7.2).
- **R2 (strict-vs-non-strict slack at `p = 2`) -- CLOSED on the KM-ab side too**
  (sec. 2.2 rows 10, 16, 20, 23, 24): the `(p-1)` in the wild estimate is
  cancelled by `v_p(pi) = 1/(p-1)` at every `p`, so there is no odd-`p` factor
  to lose.
- **R3 (exact sequence / non-eigenspace weight) -- DOWNGRADED**: not needed for
  `NP >= HP`; still needed for KMU-I Thm. 1.1, where it is a pre-existing gap
  of the source at every `p`.
- **New, minor:** two `p`-uniform source defects in KM-ab (sec. 2.2 rows 15,
  16) and one in KMU-I (Prop. 4.3's "any other `F_q`-rational point", sec. 1.2).
  None is a `p = 2` obstruction; all are vacuous or repairable.

---

## 4. Epistemic status

- **PROVED** (argument written out here, plus exact machine verification):
  Lemma B in general form (any odd `e | q-1`), including the ramification
  bookkeeping, the fate of the second ramification point of `z -> z^e`,
  `mu(P) = e_P`, `r_1 e_P = deg(eta)`, RH (8)/(4), and the `e_P`-independence
  of the final polygon; the necessity of `3 | q-1` for a *degree-3* auxiliary
  map; base-change invariance of `NP_q` and `HP_q` (and of `Omega_rho`); the
  KM-ab audit table's verdicts; KMU-I's self-containedness for
  `NP^{<1} >= HP^{<1}`; the dissolution of Lemma E on the KM-ab route.
- **REFUTED (witness)**: KMU-I Prop. 4.3's "any other `F_q`-rational point"
  (needs `c^{p-1} = 1`); KM-ab sec. 4.1.1's `-q(e,i) <= a(p-1)` (and the
  weaker `<= ap`).
- **CONDITIONAL-ON**: KLW arXiv:2010.01130 Theorem 1.2 (and its input SY
  arXiv:1708.03036 Theorem 1.1) -- both quoted verbatim in sec. 1.1; this is
  the `p = 2` analogue of KMU's dependence on Fulton, no weaker.
- **OPEN**: whether an auxiliary map of degree `> 3` could give `e_P = 3` over
  a field with `3 nmid q-1` (irrelevant, since the base extension is free);
  the `e = q-1` variant's weight theory (04's Theorem 3 for general odd `e`);
  Lemma E for KMU-I's own presentation (pre-existing, `p`-uniform).
- **NOT DONE**: I did not verify at source Deuring-Shafarevich, Katz-Gabber,
  Liu-Wei, Elkik, Monsky's trace formula, KLW's or SY's internal proofs, or
  KM-ab sec. 6's functional analysis; those are cited as the sources cite them.

## 5. Reproduction

Session scratchpad `noh05/` (not committed): `gf.py` (exact `GF(2^n)` and
polynomial arithmetic), `deg3b.py` (degree-3 auxiliary-map classification,
`q = 2..64`), `compose.py` (explicit Lemma-B map over `F_4` and `F_16`,
brute-force fibre/RH verification in `F_{2^6}` and `F_{2^12}`), plus the
inline sweep for KM-ab rows 15-16 (`p in {2,3,5}`, `a <= 6`, all `eps`).
PDFs in `pdf/`: `kmu1.pdf`, `kmab.pdf`, `1909.06905.pdf`, `klw.pdf`, `sy.pdf`.
