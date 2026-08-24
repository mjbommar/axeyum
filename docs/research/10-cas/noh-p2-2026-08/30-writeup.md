# Newton over Hodge at p = 2 for 2-power-order characters on arbitrary smooth affine curves

Workstream 30 (NoH-p2), the write-up. Date: 2026-08-20. This file is the
standalone artifact; `31-writeup-log.md` records the decisions,
reconciliations and label changes behind it.

## What this document is, and the rule it obeys

Every assertion below is in exactly one of three categories, and each is
marked:

- **(a) PROVED HERE** -- a complete proof is written out in this document,
  re-derived by this workstream from the definitions, not copied from a diary.
  Where a diary states the same result, that is recorded as concurrence, not
  as evidence.
- **(b) CITED** -- quoted to a published paper with an exact statement number.
  Quotations are reproduced as extracted from the fetched PDFs by the
  workstream named; where two workstreams fetched a source independently, that
  is said, because it is the difference between one transcription and two.
- **(c) DIARY** -- taken from a project diary in this directory, always with
  its audit status attached: **AUDITED-CONFIRMED** (re-derived independently by
  workstream 20, the adversarial verifier), **PENDING-AUDIT** (proved in a
  diary, not yet through 20), **GAP** / **FALSE** (a hole or a refutation, with
  witness).

No label is ever upgraded on this document's authority. A result proved here
*and* audited is labelled both ways; a result proved here but never
adversarially audited says so.

## Headline status

- The local estimate that Kramer-Miller--Upton's Remark 6.5 calls "too low for
  applications to the global setting" is **repaired unconditionally**
  (Theorems 1-4 and Lemma A, sec. 3.2-3.7). **PROVED HERE and
  AUDITED-CONFIRMED.**
- The characteristic-2 geometric input their construction lacks is **supplied**
  (Lemma B, sec. 3.8). **PROVED HERE and AUDITED-CONFIRMED**, conditional only
  on two published theorems, each now fetched and quoted by two independent
  workstreams.
- **(T1) `NP_q(rho) >= HP_q(rho)` on an arbitrary smooth affine curve in
  characteristic 2, for every finite character of 2-power order, full polygon,
  no truncation, no restriction on the order.** This is the main theorem, and
  it is uncapped. **AUDITED-CONFIRMED**, modulo named citations.
- **(T2) The KMU-I local-to-global contact criterion at p = 2** goes through
  only on an initial segment, q-adic `r <= 2^{1-n}` for order `2^n` (the full
  `r in [0,1]` at order 2). This is the stretch tier, it is **PENDING-AUDIT**,
  and its restriction is **AUDITED-CONFIRMED as structural**.

---

# 1. Introduction

## 1.1 The gap

The Newton-over-Hodge problem in characteristic p splits, in the current
literature, along the geometry of the base.

**The projective line and its affinoids: closed at every prime, p = 2
included.** All of the following were verified at source during this project
or its parent (**CITED**):

| result | id | scope, verbatim |
|---|---|---|
| Zhu, *L-functions of exponential sums over one-dimensional affinoids: Newton over Hodge*, IMRN 2004 | -- | sharp Hodge lower bound on `P^1`-affinoids for any prime coprime to the pole orders, i.e. p = 2 with odd pole orders |
| Liu--Wan, *T-adic exponential sums over finite fields*, Alg. Number Theory 3 (2009) | arXiv:0802.2589 | Theorem 5.2, `NP_T(f) >= HP_q(Delta)`; verified from the PDF to carry **no hypothesis on p at all** |
| Schmidt, *T-adic exponential sums over affinoids*, JNT 2023 | arXiv:1901.05516 | standing hypothesis "Let p be a prime"; **no parity hypothesis anywhere** (independently confirmed by workstream 01, sec. 8) |
| Davis--Wan--Xiao | arXiv:1310.5311 | full-text grep finds no "p odd"; the tower needs `gcd(d,p) = 1` |

**Arbitrary smooth affine curves: proved only for p >= 3.** The
Kramer-Miller(--Upton) framework is the one that produces the
*ramification-defined* (Swan-local) Hodge polygon on an arbitrary curve:

| paper | id | standing hypothesis |
|---|---|---|
| Kramer-Miller, *p-adic estimates of exponential sums on curves* (KM-exp), ANT 15 (2021) 141-171 | arXiv:1909.06905 | p odd |
| Kramer-Miller, *p-adic estimates of abelian Artin L-functions on curves* (KM-ab) | arXiv:2006.04936 | sec. 1, verbatim: "Let p be a prime with p >= 3" |
| Kramer-Miller--Upton, *Newton Polygons of Sums on Curves I: Local-to-Global Theorems* (KMU-I) | arXiv:2110.08656 | sec. 1.1, verbatim: "Let p be an odd prime and let q be a power of p" |
| Kramer-Miller--Upton II, *Variation in p-adic Families* (KMU-II) | arXiv:2110.08657 | sec. 2-3 carry **no** parity hypothesis |

The exclusion is not an oversight and not an un-attempted case. It is a
specific analytic obstruction, stated by the authors.

**KMU-I Remark 6.5, verbatim** (p. 33; the display's OCR is normalised. This
remark was fetched and re-read independently by workstreams 01, 02, 04 and 20,
and by the parent project's novelty check -- five transcriptions in agreement):

> "Suppose that p = 2. For k >= 3, define a(k) = floor((k - 1)/3). A similar
> construction provides a submodule A^m_{pi,P} subset A^dagger_{pi,P} with the
> following property: Let k = 2 l - r with r = 0 or 1. Then
> U_p(pi^{a(k)/m_P} t_P^{-k}) in pi^{(a(k) - a(l+r))/m_P} A^m_{pi,P}.
> **This estimate is too low for applications to the global setting.** For
> example, if k = 5 = 2 * 3 - 1, then a(k) - a(l+r) = 0, and this contributes
> an extra segment of slope 0 in the global Hodge bound below."

The predecessor paper localises the difficulty the same way. **KM-exp
sec. 1.4, verbatim:**

> "Finally, we mention our requirement that p >= 3. When p = 2 it is likely
> that the methods in this paper still work. The main difficulty is that some
> estimates in section 4 must be modified. It is also not immediately clear
> that we can find a cover eta : X -> P^1_{F_q} satisfying the desired
> properties. To construct eta, we use the fact that X admits a simply branched
> map to P^1_{F_q}, which is false when p = 2. However, upcoming work of Kiran
> Kedlaya, Daniel Litt, and Jakub Witaszek provides a Belyi map in this case.
> This should [be] enough to handle the p = 2 case."

**KMU-I Remark 4.2, verbatim** (p. 20-21):

> "In [23], Sugiyama and Yasuda extend Fulton's result to the case p = 2. We
> have omitted this case for other reasons (see Remark 6.5). By a recent
> theorem of Kedlaya-Litt-Witaszek, eta exists even without extending the base
> field [13]."

So the p = 2 exclusion has exactly two components, and both are named by the
authors: an **analytic** one (the Type-2 local estimate; Remark 6.5) and a
**geometric** one (a Belyi map with controlled ramification index over the
point 1; KM-exp sec. 1.4). Sections 3.2-3.7 discharge the first, sec. 3.8 the
second.

**The gap is live, not historical.** Booher--Groen--Kramer-Miller (2025,
arXiv:2511.02733) treat Z/2-covers in characteristic 2 by moving to
Ekedahl--Oort / Dieudonne (mod-2) invariants rather than the full 2-adic
Newton polygon; the citation-graph sweep of the parent project found the
active school (Booher / Cais / Kramer-Miller / Upton) uniformly on p-adic and
mod-p invariants and nobody on the arbitrary-curve p = 2 Newton polygon
(`ac-bridge-2026-08/24-novelty-check.md`; **DIARY, PENDING-AUDIT**, and a
*weak* negative -- that file states its own search limitations explicitly).

## 1.2 The result, in two sentences

The obstruction of Remark 6.5 is not analytic: the number 3 in
`floor((k-1)/3)` is the *tame ramification index* of an auxiliary Belyi map,
and the estimate is repaired by a different weight on the same module --
`a(k) = floor((k-1)/3) + (k mod 2)` -- which we prove admissible for every `k`,
with defect `d(k) >= 1` and `d(k) ~ k/6`, that rate being exactly optimal.
Together with a characteristic-2 tame Belyi map of uniform index 3 over the
point 1, this gives the Newton-over-Hodge inequality, with the full
Kramer-Miller ramification-defined Hodge polygon and no truncation, for every
finite character of 2-power order on an arbitrary smooth affine curve over
`F_{2^a}`; the KMU local-to-global *contact* theory follows too, but only on
an initial segment whose length we prove cannot be extended by any choice of
auxiliary index.

## 1.3 What this document does *not* claim

- No novelty for Newton-over-Hodge at p = 2 on `P^1` or on affinoids. That is
  published (sec. 1.1), and the parent project withdrew an earlier
  over-general claim; see sec. 6.4.
- No re-verification of Deuring--Shafarevich, Katz--Gabber, Liu--Wei, Elkik,
  Monsky's trace formula, KM-ab sec. 6's functional analysis, or the internal
  proofs of Kedlaya--Litt--Witaszek and Sugiyama--Yasuda. Those are cited as
  the sources cite them.
- No claim that the KMU contact criterion holds at p = 2 for characters of
  order > 2 beyond the stated initial segment. Sec. 2.3 states exactly how far
  it goes and why it stops there.

---

# 2. Main theorems

## 2.0 Notation

`q = 2^a`; `X` a smooth affine curve over `F_q` with smooth compactification
`Xbar` of genus `g`, and `S = Xbar \ X`, **counted geometrically** (sec. 3.9
shows this is the reading the degree count forces);
`rho : pi_1(X) -> C^x` a nontrivial finite character of order `2^n`; `d_P` the
Swan conductor of `rho` at `P in S`, and `delta_P = d_P/2^{n-1}` its KMU
normalisation. `HP_q(rho)` is the **Kramer-Miller ramification-defined Hodge
polygon**, the polygon with slope multiset

```
   {0}^{g-1+|S|}  u  {1}^{g-1+|S|}  u  U_{P in S} {1/d_P, 2/d_P, ..., (d_P-1)/d_P}
```

(KMU-I sec. 1.2; KM-ab sec. 1.1 with `Omega_rho = 0`, which is automatic for
2-power `rho`). `NP_q` is the q-adic Newton polygon of `L(rho, s)`.
`eta : X -> P^1` is the auxiliary tame Belyi map, `e` its ramification index
over the point `1`, and `mu(P) = e` the pole-truncation parameter.

## 2.1 (T1) Newton over Hodge at p = 2 -- the main theorem, uncapped

> **THEOREM T1.** Let `q = 2^a`, let `X/F_q` be a smooth affine curve as in
> sec. 2.0, and let `rho` be a nontrivial finite character of `pi_1(X)` of
> **any** 2-power order `2^n`. Then
>
> ```
>     NP_q(L(rho, s))  >=  HP_q(rho)
> ```
>
> as full polygons: no truncation, no restriction on `n`.
>
> **Route.** KM-ab (arXiv:2006.04936) verbatim, with exactly two
> substitutions: its **Lemma 3.1** (the geometric input) replaced by
> **Lemma B** (sec. 3.8), and its **sec. 4.2 / Prop. 4.2** (the Type-2 local
> estimate) replaced by **Theorems 1-3 and Lemma A** (sec. 3.2-3.6) at tame
> index `e = 3` with the weight `a(k) = floor((k-1)/3) + (k mod 2)`,
> transported through the dictionary of sec. 3.11.
>
> **Status: AUDITED-CONFIRMED**, conditional only on the published citations
> named below.

| ingredient | status |
|---|---|
| Lemma A, Theorems 1-4 (the local estimate) | **PROVED HERE** (3.2-3.7); **AUDITED-CONFIRMED** (`20` Part Two, P0-1..P0-7, P2-1..P2-4) |
| Lemma B (the geometry) | **PROVED HERE** (3.8); **AUDITED-CONFIRMED** (`20` Part Three, P3-1..P3-5, P3-7) |
| the KM-ab weight/operator dictionary (`b(-K) = a_KMU(K)`, same `nu`, coefficientwise module) | **DIARY `05` row 11; AUDITED-CONFIRMED** (`20` P3-10), restated in sec. 3.11 |
| base-change invariance of `NP_q`, `HP_q` | **PROVED HERE** (3.9); **AUDITED-CONFIRMED** (`20` P3-6). Asserted without proof in both source papers |
| KM-ab load-bearing rows: Lemma 3.1 (7), Prop. 4.2 (11), Prop. 7.2 (21), Prop. 7.4 (25), sec. 7.2 case (II), sec. 7.3 | **DIARY `05` sec. 2.2; AUDITED-CONFIRMED** at source (`20` P3-9..P3-11) |
| the remaining p-uniformity rows of `05`'s 26-row table | **DIARY `05`, PENDING-AUDIT** -- Part Three verified the load-bearing rows and says the rest is "consistent with what I verified", which is not the same as row-by-row re-derivation |
| KLW arXiv:2010.01130 Thm 1.2 (p = 2 half: Thm 7.6), resting on Sugiyama--Yasuda arXiv:1708.03036 Thm 1.1 = Compos. Math. 156 (2020) 325-339 | **CITED**, quoted in sec. 3.8.2; **fetched independently by two workstreams** (`05`, and `20` for Part Three) |
| Deuring-Shafarevich, Katz-Gabber, Liu-Wei, Elkik, Monsky, KM-ab sec. 6 | **CITED, not re-verified here** (sec. 5, O6) |

**Why there is no cap on T1** (this is the substance of `20` P3-12, and it is
what makes T1 the main theorem rather than a corollary of a truncated one).
Workstream 20's Part Two found a genuine coverage cap on the KMU-I route: 04's
reduction of Lemma E needs the growth parameter `m_P >= 1`, hence `e <= 1`,
hence a truncation. **KM-ab has no such formalism at the Type-2 points.** Its
local growth module is

> KM-ab (12), verbatim: `D = prod_{n in Z} p^{b(n)} t^n O_L`, "which we regard
> as a sub-`O_L`-module of `O_{E^dagger}`",

a **coefficientwise** condition with **no radius parameter and no `pi`** --
the exponents are plain integers. The Riemann-Roch step (Prop. 7.2) is carried
out on the *unweighted* space by reduction mod `m` (Lemma 7.3) and the weight
never appears in it; the weight enters only through the **diagonal** change of
basis of Prop. 7.4, under which every principal minor, hence the whole
Fredholm series, is invariant. There is no free parameter for Lemma E to
constrain, and the requirement consumed in sec. 7.2 case (II) is the absolute
statement `d(k) >= 1` in `v_p`. **So Lemma E does not arise on this route, and
neither does the cap.** (`20` P3-10, P3-12, **AUDITED-CONFIRMED**.)

A corollary of the same observation, worth stating because it removes a
possible objection: since KM-ab's module carries no radius parameter, 04's
`m_P v_pi(p) >= 1` calibration -- conservative on the KMU-I route -- is
**exact** here. The requirement really is `d(k) >= 1`, in `v_p`, on the nose.

**The slope-1 half.** Cor. 6.8-type bounds give the polygon below slope 1;
KM-ab sec. 7.3 completes it by a degree count, verbatim: *"From the
Euler-Poincare formula we know `L(rho,s)` has degree `2(g-1+m) +
sum (s_{tau_i} - 1)`. This accounts for the remaining slope one segments."*
(Poincare duality appears only in KM-ab Remark 1.2, for endpoint equality;
`20` P3-11 notes the degree count is the cheaper and correct thing to quote,
correcting `05` sec. 2.3(a)'s description of the step.)

## 2.2 The base-change reduction, exactly

Lemma B produces the index-`e` fibre over `1` from an `e`-power map, whose
auxiliary branch point lands on `1` exactly when `mu_e(F_q)` is nontrivial,
i.e. **`e | q-1`**. Two ways to satisfy this:

1. **`e = 3`, needing `3 | q-1`, i.e. `a` even.** For `a` odd, pass to
   `F_{q^2}`. This costs nothing: `NP_q(rho)` and `HP_q(rho)` are invariant
   under finite base extension (**PROVED HERE**, sec. 3.9;
   **AUDITED-CONFIRMED**), and both source papers already license unspecified
   extensions -- KM-ab sec. 2.1, verbatim: *"It is enough to prove Theorem 1.1
   after replacing q with a larger power of p. In particular, we increase q
   throughout the article if it simplifies arguments."* Necessity of `3 | q-1`
   for a *degree-3* auxiliary map is **PROVED HERE** (sec. 3.8.3) and
   **AUDITED-CONFIRMED** by an independent enumeration.
2. **`e = q-1`, extension-free -- geometry only, and NOT a drop-in.** Deleting
   the two auxiliary stages gives a tame Belyi map with `eta(S) = {0}` and
   uniform index `q-1` over `1` (odd, `> 1` for `q >= 4`), with no
   root-of-unity condition. **PROVED HERE** (sec. 3.8.5),
   **AUDITED-CONFIRMED** (`20` P3-8). **But it is insurance, not a route:** it
   moves `mu(P)` to `q-1`, so (A1) becomes `a(k) = 0` for `k <= q-1` and the
   `N`/`D` bookkeeping changes shape (it still cancels, sec. 3.8.4); and while
   Theorems 1, 2, Lemma A and Theorem 4's threshold `1/(2e)` hold for **every**
   odd `e`, **Theorem 3's mod-6 case analysis is specific to `e = 3`** and
   would have to be redone mod `2e`, for a field-dependent `e`, i.e. once per
   `q`. That is a research task, not a substitution (sec. 5, O3).

We take route 1: the extension is free and the weight is proved.

## 2.3 (T2) The KMU-I contact-theory tier -- capped, and provably so

KMU-I Theorem 1.1 is not an inequality but a *contact* criterion (the two
polygons touch globally iff they touch locally at every wild point). At p = 2
it goes through on an initial segment only.

> **THEOREM-CANDIDATE T2.** Assume `X` ordinary and let `rho` have order
> `2^n`. For every **q-adic** `r` with `0 <= r <= 2^{1-n}`,
> `HP_q^{<r}(rho)` and `NP_q^{<r}(rho)` have the same terminal point **iff**
> `HP_q^{<r}(rho_P^ext)` and `NP_q^{<r}(rho_P^ext)` have the same terminal
> point for every `P in S`. In particular, for **order-2 characters (n = 1)
> the full range `r in [0,1]` of KMU-I Theorem 1.1 is covered**; at order 4,
> `r <= 1/2`; at order 8, `r <= 1/4`.
>
> **Status: PENDING-AUDIT** as a whole (its route through KMU-I sec. 6.2 rests
> on Lemma E). The **restriction** is **AUDITED-CONFIRMED as structural**.

*Why the restriction.* Workstream 04 stated this candidate for the full
`r in [0,1]` at every `n`; workstream 20's priority-0 audit found the
overreach, and it is **not** repaired here:

- 04's Lemma E reduction (sec. 2.4) needs the local parameter `m_P >= 1`,
  hence `e <= 1` in the normalisation `m_{e,P} = 1/e`.
- The `r` that this caps is the **`pi_q`-adic** truncation parameter; KMU
  Theorem 1.1's `r` is the **q-adic** one, and
  `v_{pi_q}(x) = v_pi(p) * v_q(x)` because `pi_q = pi^{v_p(q)}`. At p = 2 with
  `rho` of order `2^n`, `R = Z_2[zeta_{2^n}]` is totally ramified of degree
  `2^{n-1}`, so `v_pi(p) = 2^{n-1}` and `e <= 1` covers only q-adic
  `r <= 2^{1-n}`. Three independent confirmations of the conversion factor are
  in `20` P2-6: the glossary definition of `pi_q`; the ratio
  `d_P(p-1)/delta_P = v_pi(p)` between the two printings of the same local
  polygon; and the window count `deg L(rho_P^ext, s) = d_P - 1`.
- **The cap is structural, not a choice of normalisation.** For any
  `m_{e,P} = M`, KMU Def. 7.3(2) needs `d(k)/M >= r` for every `k > mu(P)`,
  and **Theorem 4 (sec. 3.7) gives `d(2e) <= 1` for every weight whatsoever
  and every odd `e`**; with Lemma E's `M >= 1` this forces `pi_q`-adic
  `r <= 1` whatever `M` is. Theorem 4 and the Lemma-E reduction are in direct
  tension, and no choice of auxiliary tame index relieves it.

(`20` P2-6 and P3-12, **AUDITED-CONFIRMED**. KMU's own Thm. 7.13 proof reads
*"Since r <= v_pi(p), we may enlarge e as necessary and assume that r <= e"* --
KMU **enlarge** `e` exactly where 04's reduction shrinks it.)

*What would remove the cap.* Two routes, and **nobody has taken either**:
prove Lemma E outright; or re-run KMU-I sec. 6.2 and the whole of sec. 7 in
KM-ab's coefficientwise formulation. The second is available in principle
(that is what makes T1 uncapped), but KMU-I's perturbation machinery
(Lemmas 7.1-7.4, 7.11, Cor. 7.14) is built on the `B^{m_e}` basis and the
tuple `m_e`; transporting it is a research task, not a citation (`20` P3-12).

## 2.4 Lemma E: a pre-existing p-uniform gap, named -- and it touches only T2

> **LEMMA E (required by the KMU-I route only).** With `A^{m,*}_pi` the
> product of the local growth modules for a weight `a`,
> `Atilde^{m,*}_pi = A^{m,*}_pi cap Atilde^dagger_pi` and
> `A^{m,*,tr}_pi = A^{m,*}_pi cap A^{dagger,tr}_pi`, the sequence
> `0 -> Ltilde_pi -> Atilde^{m,*}_pi -> A^{m,*,tr}_pi -> 0` is exact.

1. **It is asserted without proof in KMU-I, at every p, for KMU's own weight.**
   Only the `A^dagger` version (Lemma 5.15) is proved there.
   (DIARY `04` sec. 7.3 and `20` Part One sec. 3.1, **AUDITED-CONFIRMED**.)
2. **It is not created by dropping the eigenspace form.** `A^{m,*}_{pi,P}` is
   not a ring, and *no* weight satisfying (A1) can make it one: subadditivity
   plus `a(e) = 0` would force `a(k+e) <= a(k)`, contradicting divergence. KMU's
   own `B^m` is not a ring either (`u^{-1}` violates its growth condition).
   **PROVED HERE**, sec. 3.5; **AUDITED-CONFIRMED** at `20` P2-5.
3. **It does not arise on the KM-ab route** (sec. 2.1). So T1 is free of it;
   only T2 needs it. **AUDITED-CONFIRMED** (`20` P3-10, P3-12).

## 2.5 Dependency summary

```
 T1  NP_q(rho) >= HP_q(rho) -- FULL POLYGON, ALL 2-POWER ORDERS   [AUDITED-CONFIRMED]
  |
  +-- KM-ab sec. 2, 3.2-3.4, 5, 6, 7.1, 7.2(I)(III)(IV), 7.3 ... CITE (p-uniform)
  |     load-bearing rows 7/11/21/25 + case (II) ................ [AUDITED-CONFIRMED, 20 P3-9..P3-11]
  |     remaining p-uniformity rows ............................. [DIARY 05, PENDING-AUDIT]
  +-- KM-ab Lemma 3.1 (geometry) -> LEMMA B ..................... [PROVED HERE 3.8; AUDITED-CONFIRMED]
  |     +-- KLW arXiv:2010.01130 Thm 1.2 / 7.6 .................. [CITED, two independent fetches]
  |     +-- SY arXiv:1708.03036 Thm 1.1 ......................... [CITED, two independent fetches]
  |     +-- base-change invariance of NP_q, HP_q ................ [PROVED HERE 3.9; AUDITED-CONFIRMED]
  +-- KM-ab sec. 4.2 / Prop. 4.2 -> LEMMA A + THEOREMS 1-3 ...... [PROVED HERE 3.2-3.6; AUDITED-CONFIRMED]
  |     via the dictionary b(-K) = a_KMU(K), same nu ............ [AUDITED-CONFIRMED, sec. 3.11]
  +-- KM-ab (21) = (A1), (22) = (A3 weak), b(n) >= m = (A4) ..... [PROVED HERE 3.6]
  +-- LEMMA E ................................................... DOES NOT ARISE on this route

 T2  KMU-I Thm 1.1 at p = 2, q-adic r <= 2^{1-n}                  [PENDING-AUDIT]
  |
  +-- KMU-I sec. 2-3, 4.2-4.4, 5, 6.1(wild), 7.1-7.4 ............ CITE (p-uniform) [DIARY 04, AUDITED-CONFIRMED]
  +-- KMU-I Prop. 4.3 (geometry) -> LEMMA B ..................... as above
  +-- KMU-I Def. 6.3 / Lem. 6.2 / Prop. 6.4 / Rem. 6.5 .......... [PROVED HERE 3.2-3.6; AUDITED-CONFIRMED]
  +-- KMU-I sec. 6.2 exact sequence -> LEMMA E .................. OPEN IN KMU AT EVERY p; reduced to
  |                                                              KMU's own assertion, coverage capped
  |                                                              at q-adic r <= 2^{1-n}  [GAP, AUDITED-CONFIRMED]
  +-- KMU-I Lemma 7.11 (the unique consumer of d(k) >= 1) ....... UNCHANGED given Theorem 3
  +-- Deuring-Shafarevich, Katz-Gabber, Liu-Wei, Elkik, Monsky .. CITE, not re-verified
```

**A correction to `05`'s own dependency graph, carried here.** `05` sec. 3
repeats 04's pre-correction phrasing, *"04 reduces it to KMU's own assertion
with no loss for `r in [0,1]`"*; `05`'s reading list stopped at `20-verify`
Part One, so Part Two's correction was not absorbed. **That line must read
`r <= 2^{1-n}`** (`20` P3-14, **AUDITED-CONFIRMED as a GAP** in `05`). It is
an inherited misstatement, not an independent one, and it does not touch T1.

---

# 3. The new mathematics

Everything in this section is **PROVED HERE**: the arguments are written out
in full and were re-derived by this workstream from the definitions. Machine
confirmations are this workstream's own independent implementation
(sec. 6.1), not a diary's. Where a diary or the auditor reached the same
result, that is recorded as concurrence.

## 3.1 The Type-2 operator at p = 2

At an auxiliary tame point `P` of `eta` with `eta(P) = 1` and ramification
index `e` (odd, `e > 1` at p = 2), the local Frobenius downstairs is
`sigma(u) = (u+1)^p - 1` with `u = t^e` the pullback of the base parameter at
`1` (KMU-I sec. 4.3; KM-ab sec. 3.4). At `p = 2`:

```
   sigma(t)^e = sigma(u) = u^2 + 2u = t^{2e} + 2 t^e
   ==>  sigma(t) = t^2 G,    G := (1 + 2 x^e)^{1/e},   x := 1/t.
```

The binomial series `G` converges because `gcd(e, 2) = 1`. `[E : sigma(E)] = 2`,
and the nontrivial conjugate of `t` over `sigma(E)` is `t' = -tG`: the two
roots of `Y^2 + 2Y - sigma(u)` are `u` and `u' = -2-u`, and for `e` odd

```
   (-tG)^e = -t^e (1 + 2x^e) = -(u + 2) = u'.
```

Hence, with `U_p = (1/p) sigma^{-1} o Tr_{E/sigma(E)}` (KMU-I Def. 4.9) and
`E~_P` a constant in `1 + pi R_q` (KMU-I proof of Prop. 6.4: *"The claim
follows since E~_P in 1 + pi R_q"* -- `P not in S`, so `rho` is unramified
there and **no splitting function enters this estimate at all**), writing
`U_2(t^{-k}) = sum_j c_{k,j} t^{-j}` and applying `sigma`:

```
   Tr(t^{-k}) = x^k (1 + (-1)^k G^{-k}),        sigma(t^{-j}) = x^{2j} G^{-j},
   (1/2) x^k (1 + (-1)^k G^{-k}) = sum_j c_{k,j} x^{2j} G^{-j}.               (*)
```

**Support.** `G` is a series in `x^e`, so the left side of (*) lives in
degrees `= k mod e` and the `j`-th term on the right in degrees `= 2j mod e`;
`e` odd makes `2` invertible mod `e`, so the admissible `j` form one class
mod `e`. Minimal degree: for `k` even,
`1 + G^{-k} = 2 - (2k/e)x^e + ...`, so the left side starts at `x^k` and
`2j = k`; for `k` odd, `1 - G^{-k} = (2k/e)x^e + ...`, so it starts at
`x^{k+e}` and `2j = k+e` (an integer, both being odd). Therefore

> **`j'(k) = k/2` for `k` even, `j'(k) = (k+e)/2` for `k` odd,** and `j` runs
> over `j'(k) + e Z_{>=0}`.

For `e = 3` this is Remark 6.5's `l + r` with `k = 2l - r`, `r in {0,1}`:
`k = 2c` gives `l = c, r = 0, l+r = c = j'`; `k = 2c-1` gives `l = c, r = 1,
l+r = c+1 = j'`. It is also `01`'s "least `j >= ceil(k/2)` with `j = -k mod 3`".
(`20` Part One sec. 2.3 notes this discriminates: at `e = 5` the same
computation does *not* fit Remark 6.5's `k = 2l-r`, `r in {0,1}` shape, so
`e = 3` is **singled out** by KMU's own phrasing, not merely consistent with
it.)

## 3.2 THEOREM 1 (the hypergeometric closed form)

> **THEOREM 1.** Let `p = 2` and `e` odd. Then for every `k >= 1`, `m >= 0`,
>
> ```
>   k even:  c_{k, k/2 + em}     = prod_{i=0}^{m-1} (k^2 - 4 e^2 i^2)          / ( e^{2m} (2m)!   )
>   k odd :  c_{k, (k+e)/2 + em} = (k/e) prod_{i=0}^{m-1} (k^2 - e^2(2i+1)^2)  / ( e^{2m} (2m+1)! )
> ```

*Proof.* Put `v := 2x^e`, so `G = (1+v)^{1/e}` and `G^e = 1+v`. Put
`(1+v)^{1/2} = e^{phi}` (i.e. `phi = (1/2)log(1+v)`) and

```
   W := x^{2e}/(1 + 2x^e) = (v/2)^2/(1+v) = v^2/(4(1+v)).
```

Then `W = sinh^2(phi)`: indeed
`sinh(phi) = ((1+v)^{1/2} - (1+v)^{-1/2})/2 = v/(2(1+v)^{1/2})`, whose square
is `v^2/(4(1+v))`. **Note `W` does not depend on `e`.** Put `tau := phi/e`, so
`(1+v)^{k/(2e)} = e^{k tau}` and

```
   sinh(e tau) = sinh(phi) = v/(2(1+v)^{1/2}) = x^e (1+v)^{-1/2}.            (**)
```

Divide (*) by `x^{2j'} G^{-j'}`, `j' = j'(k)`. The right side becomes

```
   sum_{m>=0} c_{k,j'+em} x^{2em} G^{-em}
 = sum_{m>=0} c_{k,j'+em} ( x^{2e}/(1+v) )^m  =  sum_{m>=0} c_{k,j'+em} W^m,
```

using `G^e = 1+v`. The left side becomes:

- `k` even, `j' = k/2`:
  `(1/2)x^k(1 + G^{-k}) / (x^k G^{-k/2}) = (1/2)(e^{k tau} + e^{-k tau})
   = cosh(k tau)`.
- `k` odd, `j' = (k+e)/2`:
  `(1/2)x^k(1 - G^{-k}) / (x^{k+e} G^{-(k+e)/2}) = (1/2) x^{-e} G^{e/2}
   (G^{k/2} - G^{-k/2}) = x^{-e}(1+v)^{1/2} sinh(k tau) = sinh(k tau)/sinh(e tau)`,
  the last step by (**).

Set `z := sinh(phi) = W^{1/2}` and `lambda := k/e`, so
`k tau = lambda phi = lambda arcsinh(z)`. Both `y = cosh(lambda arcsinh z)`
and `y = sinh(lambda arcsinh z)` satisfy

```
   (1 + z^2) y'' + z y' - lambda^2 y = 0.
```

(For the first: `y' sqrt(1+z^2) = lambda sinh(lambda arcsinh z)`;
differentiating and multiplying by `sqrt(1+z^2)` gives
`(1+z^2)y'' + zy' = lambda^2 y`. The second is identical with `cosh` and
`sinh` exchanged.)

`cosh(lambda arcsinh z)` is even in `z`; write it `sum_m a_m z^{2m}`. The
coefficient of `z^{2m}` in the ODE gives

```
   (2m+2)(2m+1) a_{m+1} + [2m(2m-1) + 2m - lambda^2] a_m = 0,   2m(2m-1)+2m = 4m^2,
   ==>  a_{m+1} = a_m (lambda^2 - 4m^2)/((2m+2)(2m+1)),   a_0 = 1,
```

so, telescoping with `prod_{i=0}^{m-1}(2i+2)(2i+1) = (2m)!`,
`a_m = prod_{i=0}^{m-1}(lambda^2 - 4i^2)/(2m)!`. Since
`cosh(k tau) = sum_m c_{k,k/2+em} W^m = sum_m c_{k,k/2+em} z^{2m}`, we get
`c_{k,k/2+em} = a_m`; substituting `lambda = k/e` gives the even display.

`sinh(lambda arcsinh z)` is odd; write it `sum_m b_m z^{2m+1}`. The
coefficient of `z^{2m+1}` gives

```
   (2m+3)(2m+2) b_{m+1} + [(2m+1)2m + (2m+1) - lambda^2] b_m = 0,  (2m+1)2m+(2m+1) = (2m+1)^2,
   ==>  b_{m+1} = b_m (lambda^2 - (2m+1)^2)/((2m+3)(2m+2)),   b_0 = lambda,
```

and `prod_{i=0}^{m-1}(2i+3)(2i+2) = (2m+1)!`, so
`b_m = lambda prod_{i=0}^{m-1}(lambda^2 - (2i+1)^2)/(2m+1)!`. By (**),
`sinh(e tau) = z`, so the left side in the odd case is
`sinh(lambda arcsinh z)/z = sum_m b_m z^{2m}`, giving `c_{k,(k+e)/2+em} = b_m`.
**QED**

**Two consequences.**

- `c_{k, j'(k)} = 1` (`k` even) or `k/e` (`k` odd): a 2-adic unit in both
  cases, `e` being odd. So **Remark 6.5's estimate is sharp as stated** --
  there is no hidden gain behind the pole-order statement, and its `d(5) = 0`
  is real, not an artifact of a lossy bound. (`01` and `20` could only measure
  this; Theorem 1 proves it.)
- If `e | k` the product terminates (`cosh(n phi)` and
  `sinh(n phi)/sinh(phi)` are Chebyshev polynomials in `W`). That is why
  `U_2(t^{-3}) = t^{-3}` and `U_2(t^{-6}) = t^{-3} + 2t^{-6}` are finite.

**Independent confirmation (this workstream).** A from-scratch series solve of
(*) over exact `Fraction`s -- lowest-degree-first elimination, never using the
closed form -- agrees with Theorem 1 on every pair examined
(`e in {1,3,5,7}`, `k <= 16`, all `m` in the computed support; 355 pairs, 0
mismatches), verifies `G^e = 1 + 2x^e` exactly and the support containment,
and reproduces `01` sec. 6b's ground truth to the last digit:

```
 U_2(t^-3) = t^-3
 U_2(t^-4) = t^-2 + (8/9) t^-5 - (40/243) t^-8 + (512/6561) t^-11 - ...
 U_2(t^-5) = (5/3) t^-4 + (40/81) t^-7 - (112/729) t^-10 + (1600/19683) t^-13 - ...
 U_2(t^-6) = t^-3 + 2 t^-6
 U_2(t^-7) = (7/3) t^-5 + (140/81) t^-8 - (224/729) t^-11 + (2816/19683) t^-14 - ...
 U_2(t^-8) = t^-4 + (32/9) t^-7 + (224/243) t^-10 - (1792/6561) t^-13 + ...
```

*Concurrence:* DIARY `04` Theorem 1, **AUDITED-CONFIRMED** (`20` P0-1, P0-2,
P2-1: re-derived independently and checked against a third operator
implementation, `e in {1,3,5,7}`, `k <= 25`, every `m`, 0 mismatches).

## 3.3 THEOREM 2 (the valuation identity)

> **THEOREM 2.** With `xi_i = 2i` for `k` even and `xi_i = 2i+1` for `k` odd,
> and `s_2` the binary digit sum,
>
> ```
>    v_2( c_{k, j'(k)+em} )  =  Sigma_m(k) - 2m + s_2(m),
>    Sigma_m(k) := sum_{i=0}^{m-1} [ v_2(k - e xi_i) + v_2(k + e xi_i) ].
> ```

*Proof.* By Legendre's formula `v_2(N!) = N - s_2(N)`, with
`s_2(2m) = s_2(m)` and `s_2(2m+1) = s_2(m)+1`:

```
   v_2((2m)!) = 2m - s_2(m),        v_2((2m+1)!) = 2m+1 - (s_2(m)+1) = 2m - s_2(m),
```

so both factorials contribute `-(2m - s_2(m))`. `e` is odd, so
`v_2(e^{2m}) = 0` and, in the odd case, `v_2(k/e) = v_2(k) = 0`. The numerator
factors as `prod_i (k - e xi_i)(k + e xi_i)` in both cases, since
`k^2 - 4e^2i^2 = (k-2ei)(k+2ei)` and
`k^2 - e^2(2i+1)^2 = (k - e(2i+1))(k + e(2i+1))`. **QED**

**Independent confirmation.** `e in {1,3,5,7}`, `k <= 60`, `m <= 29`: 0
mismatches against the closed form (hence, via sec. 3.2, against the
from-scratch operator).

*Concurrence:* DIARY `04` Theorem 2, **AUDITED-CONFIRMED** (`20` P0-3, P2-2).

## 3.4 LEMMA A (the tail estimate)

> **LEMMA A.** For every `k >= 1` and every `m >= 1`,
> `v_2(c_{k, j'(k)+em}) >= m`. Moreover `v_2 >= m + s_2(m) >= m+1` when `k` is
> odd or `4 | k`; and `v_2 >= 3 floor(m/2) + s_2(m)` when `k = 2 mod 4`.
> Equality `v_2 = m` occurs **only** for `k = 2 mod 4, m = 1`.

*Proof.* `e` is odd throughout.

*Case `k` odd.* Every `e xi_i = e(2i+1)` is odd, so `k^2` and `e^2 xi_i^2` are
both `= 1 mod 8`, giving `v_2(k^2 - e^2 xi_i^2) >= 3`. Hence `Sigma_m >= 3m`
and, by Theorem 2, `v_2 >= 3m - 2m + s_2(m) = m + s_2(m) >= m+1`.

*Case `k` even*, `k = 2 kappa`. Here `xi_i = 2i`, so
`k +- e xi_i = 2(kappa +- ei)` and `Sigma_m = 2m + sum_{i<m} v_2(kappa^2 -
e^2 i^2)`; Theorem 2 then gives
`v_2 = sum_{i=0}^{m-1} v_2(kappa^2 - e^2 i^2) + s_2(m)`.

- *`kappa` even (`4 | k`).* For `i` odd, `ei` is odd and `kappa` even, so
  `kappa +- ei` is odd and the term is 0. For `i` even (including `i = 0`,
  whose term is `2 v_2(kappa) >= 2`) both `kappa` and `ei` are even, so the
  term is `>= 2`. There are `ceil(m/2)` even `i` in `[0,m-1]`, so the sum is
  `>= 2 ceil(m/2) >= m` and `v_2 >= m + s_2(m) >= m+1`.
- *`kappa` odd (`k = 2 mod 4`).* For `i` even the term is 0; for `i` odd both
  `kappa` and `ei` are odd, so the term is `>= 3` by the mod-8 argument. There
  are `floor(m/2)` odd `i`, so `v_2 >= 3 floor(m/2) + s_2(m)`. For `m` even
  this is `>= 3m/2 >= m`; for `m` odd it is `>= m` iff
  `(m-3)/2 + s_2(m) >= 0`, which holds for `m >= 3` (as `s_2 >= 1`) and at
  `m = 1` reads `-1 + 1 = 0`. **QED**

*Equality.* In the odd and `4|k` cases `v_2 >= m + s_2(m) > m`. In the
`k = 2 mod 4` case, `m = 1` gives `v_2 = 2v_2(kappa) + s_2(1) = 0 + 1 = 1 = m`
(`kappa` odd); for `m >= 2` the bound `3 floor(m/2) + s_2(m)` exceeds `m`.

**Independent confirmation.** `e = 3`, `k <= 600`, `m <= 80`: **0 violations**
of `v_2 >= m`; **0 violations** of the `m + s_2(m)` refinement on `k` odd or
`4|k`; exactly **150 tight pairs**, *all* of shape `k = 2 mod 4, m = 1` --
reproducing `04`'s and `20`'s counts to the pair.

*Concurrence:* DIARY `04` Lemma A, **AUDITED-CONFIRMED** (`20` P0-4, P2-2,
which checked the tight `m = 1` sub-case explicitly).

## 3.5 The admissibility conditions

The weight `a` enters through
`A^{m,*}_{pi,P} := { sum_k b_k t_P^{-k} : v_pi(b_k) >= a(k)/m_P for k > 0 }`
(on the KM-ab side, `D = prod_n p^{b(n)} t^n O_L` with `b(-k) = a(k)`; see
sec. 3.11), and

```
   d(k) := min_{m >= 0} [ a(k) - a(j'(k)+em) + v_2(c_{k, j'(k)+em}) ].
```

The conditions the sources consume, with their consumers (read off KMU-I
sec. 6.1.2, 6.2, Cor. 6.7, Cor. 6.8, Lemma 7.11 by `01` and independently by
`20`; **DIARY, AUDITED-CONFIRMED**, with (A4), (A5) added by `20` Part One
sec. 3.1 to `01`'s list, and each verified again on the KM-ab side by `05`
and `20` P3-11):

| | condition | consumed by |
|---|---|---|
| (A1) | `a(k) = 0` for `k <= mu(P) = e` | the KMU-I sec. 6.2 exact sequence (`L = H^0(D)` has poles of order `<= mu(P)`); on the KM-ab side this is literally eq. (21), `ker(pr) cap O_R subset O_R^con` |
| (A2) | `a(k) = O(k)` | KMU-I Cor. 6.7, `union_m Vtilde^m = Vtilde^dagger` |
| (A3) | `d(k) >= 1` for `k > mu(P)`, and `d(k) -> infinity` | KMU-I Lemma 7.11 (the unique consumer of `>= 1`) and Cor. 6.7 (divergence); KM-ab sec. 7.2 case (II) and Lemma 6.12 (`lim col_i = infinity`) |
| (A4) | `a(k) >= d(k)` | KMU-I proof of Prop. 6.6(2) verbatim; KM-ab sec. 7.2 case (II)'s "`b(n) >= m`" |
| (A5) | `d(k) >= 0` for `k <= mu(P)` | `Theta~`-stability in KMU-I Cor. 6.8; KM-ab (22), `U_p o C(O_R^con) subset O_R^con` |

**The `1/m_P` calibration, and why it is exact on the KM-ab side.**
`v_pi(c) = v_pi(p) v_2(c)` and `m_P >= m_{pi,P} = 1/v_pi(p)`, so
`m_P v_pi(p) >= 1` and the `v_2` term enters with coefficient `>= 1`. Using it
with coefficient exactly 1 is conservative on the KMU-I side, and legitimate
**because `v_2(c_{k,j}) >= 0`** -- now a consequence of Lemma A (`m >= 1`) plus
`v_2(c_{k,j'(k)}) = 0` (`m = 0`, Theorem 1), not an assumption. On the KM-ab
side there is no growth parameter and no `pi` at all (sec. 2.1, sec. 3.11), so
the requirement is **literally `d(k) >= 1` in `v_p`** and the calibration is
exact rather than conservative (`20` P3-10).

**Reduction of (A3).** Since the `m = 0` term of the minimum is
`a(k) - a(j'(k))`, (A3) is the pair

> **(A3a)** `a(k) - a(j'(k)) >= 1` for `k > mu(P)`, tending to infinity;
> **(A3b)** `a(j'(k)+em) - a(j'(k)) <= v_2(c_{k,m})` for `m >= 1`

(the second forces the general term to dominate, so `d(k) = a(k) - a(j'(k))`).

**Remark (no admissible weight makes the module a ring, at any p).** Closure
under multiplication needs `a(i+j) <= a(i) + a(j)`; with (A1)'s `a(e) = 0`
that forces `a(k+e) <= a(k)`, contradicting `a(k) -> infinity`. KMU's own
`B^m` is not a ring either (`u^{-1}` violates its growth condition). This is
why Lemma E (sec. 2.4) is a pre-existing feature of the source and not a cost
introduced here. **PROVED HERE**; **AUDITED-CONFIRMED** (`20` P2-5).

## 3.6 THEOREM 3 (the repaired weight is admissible, for all k)

> **THEOREM 3.** Let `p = 2`, `e = 3`, `mu(P) = 3`, and
>
> ```
>    a(k) = 0                              for k <= 3,
>    a(k) = floor((k-1)/3) + (k mod 2)     for k >= 4.
> ```
>
> Then (A1)-(A5) hold, `d(k) >= 1` for every `k > 3`, the minimum defining
> `d(k)` is attained at `m = 0` (so `d(k) = a(k) - a(j'(k))`), and
> `d(k) >= 2 floor(k/12) - 1 -> infinity`, with `d(k) ~ k/6`.

`a` is **integer-valued**. That is not cosmetic: on the KM-ab route the
weight appears as `p^{a(k)}`, which then lies in `O_L` with **no base
extension**. The pointwise-extremal weight `a*` of `04` sec. 6, which attains
the same sharp rate, takes values in `(1/6)Z` and would require one. This is
one of two reasons to make the parity-indicator weight the headline (the other
is sec. 3.11's bounded-difference property). (`20` P3-10.)

*(A1)* holds by definition. *(A2)*: `a(k) <= (k+2)/3`. *(A5)*: `a(k) = 0` for
`k <= 3` gives `d(k) = 0 >= 0` there. *(A4)* follows once (A3) is proved:
`d(k) <= a(k) - a(j'(k)) + v_2(c_{k,j'(k)}) = a(k) - a(j'(k)) <= a(k)`, since
`a >= 0` and the leading coefficient is a unit.

### 3.6.1 The increment formula

For `n >= 4` and `m >= 1`, `floor((n+3m-1)/3) = floor((n-1)/3) + m` and
`(n+3m) mod 2 = (n+m) mod 2`, so

```
   a(n+3m) - a(n) = m + [ ((n+m) mod 2) - (n mod 2) ]
                  = m       if m even,
                  = m + 1   if m odd and n even,
                  = m - 1   if m odd and n odd.
```

It also holds at `n = 2` (`a(2) = 0 = floor(1/3) + 0`), and **fails** at
`n = 1` and `n = 3`, where (A1) overrides the closed form. Both are handled
separately: for `k > 3`, `j'(k) = 1` never occurs (`k` even gives
`j' = k/2 >= 2`; `k` odd gives `j' = (k+3)/2 >= 4`), and `j'(k) = 3` occurs
only for `k = 6`.

### 3.6.2 (A3b): the tail

Let `k > 3`, `j' = j'(k)`, `m >= 1`. We must show
`a(j'+3m) - a(j') <= v_2(c_{k,m})`.

- *`j' = 3`.* Then `k = 2j' = 6` (the odd alternative `k = 2j'-3 = 3` is
  excluded by `k > mu(P) = 3`). By Theorem 1 with `lambda = 6/3 = 2`, the
  product has the factor `4 - 4 = 0` at `i = 1`, so `c_{6,m} = 0` for
  `m >= 2` and only `m = 1` constrains: `a(6) - a(3) = 1 - 0 = 1` and
  `c_{6,1} = lambda^2/2! = 2`, so `v_2(c_{6,1}) = 1`. Equality; OK.
- *`m` even.* Increment `m`, and Lemma A gives `v_2 >= m`. OK.
- *`m` odd, `j'` odd.* Increment `m - 1 < m <= v_2`. OK.
- *`m` odd, `j'` even.* Increment `m + 1`. The `k` with `j'(k) = j'` are
  `k = 2j'` and `k = 2j' - 3`; `j'` even makes `2j' = 0 mod 4`, and `2j'-3` is
  odd -- so in **both** cases Lemma A's refinement gives
  `v_2 >= m + s_2(m) >= m+1`. OK. **QED**

*Why the parity indicator is exactly the right correction.* Lemma A is tight
only at `k = 2 mod 4, m = 1`, i.e. at `j' = k/2` **odd** -- precisely the case
where the parity indicator makes the increment go *down* by one rather than
up. The two tightnesses are complementary. That is why `floor((k-1)/3)` alone
fails at `k = 5` and `floor((k-1)/3) + (k mod 2)` does not.

### 3.6.3 (A3a): the leading term

Write `c := j'(k)`, so `k = 2c` (`k` even) or `k = 2c-3` (`k` odd, and then
`c >= 4` because `k > 3`). Put `c = 6q + r`, `0 <= r <= 5`, and use
`floor((6q+s)/3) = 2q + floor(s/3)`.

*`k = 2c` even.* `2c` is even so `a(2c) = floor((12q+2r-1)/3) = 4q +
floor((2r-1)/3)`, while `a(c) = 2q + floor((r-1)/3) + (r mod 2)`, giving
`d = 2q + floor((2r-1)/3) - floor((r-1)/3) - (r mod 2)`:

| `r` | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|---|
| `d` | `2q` | `2q-1` | `2q+1` | `2q` | `2q+1` | `2q+1` |

*`k = 2c-3` odd.* `a(k) = floor((2c-4)/3) + 1 = 4q + floor((2r-4)/3) + 1`, so
`d = 2q + floor((2r-4)/3) - floor((r-1)/3) - (r mod 2) + 1`:

| `r` | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|---|
| `d` | `2q` | `2q-1` | `2q+1` | `2q` | `2q+1` | `2q+1` |

The two tables are identical. For `r in {2,4,5}`, `d >= 1` for every `q >= 0`.
For `r in {0,1,3}` we need `q >= 1`, and the `q = 0` cases are `c in {0,1,3}`:
on the even branch `c = 0,1` give `k = 0,2` (excluded by `k > 3`) and `c = 3`
gives `k = 6`, where the closed form for `a(c)` is invalid and (A1) applies:
`d(6) = a(6) - a(3) = 1`; on the odd branch `c >= 4`, so none occurs. Finally
`c = 2` (`r = 2, q = 0`, `k = 4`) uses the formula's validity at `n = 2`:
`d(4) = a(4) - a(2) = 1`. So `d >= 1` throughout.

*Divergence.* In both tables `d >= 2q - 1 = 2 floor(c/6) - 1`, and
`c = j'(k) >= k/2`, so `d(k) >= 2 floor(k/12) - 1 -> infinity`; asymptotically
`d(k) ~ c/3 ~ k/6`. **QED**

### 3.6.4 Independent confirmation

Exact-rational sweep with this workstream's own coefficients,
`4 <= k <= 400`, full support `m <= 259`:

```
   (A3) violations: 0.   Minimum attained at m = 0 for EVERY k.   min d = 1.
   d(4..24) = 1,1,1,1,1,2,1,1,2,3,1,2,3,3,2,3,3,4,3,3,4
   d(100) = 17    d(200) = 33    d(400) = 67
   control: with a(k) = floor((k-1)/3) (KMU Remark 6.5), d(5) = 0.
```

These match `04`'s and `20`'s independently computed rows exactly.

*Concurrence:* the witness weight is DIARY `20` Part One sec. 3.3 (found by
the auditor, refuting `01`'s "none of the obvious closed-form weights work");
the proof is DIARY `04` Theorem 3, **AUDITED-CONFIRMED** (`20` P0-5, P0-6,
P2-3, which recomputed both mod-6 tables entry by entry and confirmed the case
coverage is complete).

## 3.7 THEOREM 4 (sharpness: `gamma = 1/6` exactly), and e-universality

> **THEOREM 4.** For every odd `e`, the index `k = 2e` is a **self-loop** of
> the support map, and
>
> ```
>    c_{2e, 2e} = 2,     hence     d(2e) <= v_2(2) = 1
> ```
>
> **for every weight whatsoever.** Consequently, at `e = 3`, a target
> `d(k) >= max(1, gamma k)` is achievable **iff `gamma <= 1/6`**, and
> `d(k) >= max(1, k/6)` is achieved (sec. 3.6). At general odd `e` the
> threshold is `gamma <= 1/(2e)`.

*Proof.* `k = 2e` is even, so `j'(2e) = e` and `j'(2e) + e = 2e = k`: the
index `k` occurs in its own support, at `m = 1`. Theorem 1 with
`lambda = k/e = 2` gives `c_{2e, e+e} = (lambda^2 - 0)/2! = 4/2 = 2`,
**independently of `e`** -- `lambda = 2` erases `e` entirely. The (A3)
constraint at `(k,j) = (2e,2e)` reads
`d(2e) <= a(2e) - a(2e) + v_2(c_{2e,2e}) = 1`, and the weight cancels
identically. **QED**

**The `m = 2` self-loop.** `k = 4e` is even with `j' = 2e` and `j' + 2e = k`,
so it too is a self-loop, at `m = 2`; Theorem 1 with `lambda = 4` gives
`c_{4e,4e} = 16 * 12/4! = 8`, `v_2 = 3`, again independent of `e`.

**Consequence: the coverage cap of T2 is universal in the tame index.** Since
`d(2e) <= 1` for every odd `e` and every weight, **no choice of auxiliary tame
index repairs T2's restriction within the unmodified architecture**
(sec. 2.3). **PROVED HERE.** (This is the coordinator's Note 11 computation,
where it was exact-plus-numerically-verified for `e = 3,5,7,9,11`; here it is
one line from Theorem 1.)

**Independent confirmation.** `c_{2e,2e} = 2` for
`e = 1,3,5,7,9,11,13,15,21` and `c_{4e,4e} = 8` for `e = 3,5,7,9,11`, exact.

**Structural restatement -- the real content of Remark 6.5.** The descending
orbit of `succ = j'` has exactly two attractors below `mu(P) = e = 3`: the
fixed point `3` and the 2-cycle `{1,2}`. `U_2(t^{-3}) = t^{-3}` is a genuine
eigenvector of eigenvalue 1 -- which is why `mu(P) = e_P` is not optional --
and `k = 6` is the first index above the truncation that still sees it.

*Concurrence:* DIARY `04` Theorem 4, **AUDITED-CONFIRMED** (`20` P0-7, P2-4,
which retired its own earlier LP interval `[1/6, 2/11)` in favour of the exact
point `1/6`).

## 3.8 LEMMA B: the characteristic-2 tame Belyi map with uniform index `e`

### 3.8.1 What the odd-p construction is, and the three ways it degenerates

**KMU-I sec. 4.1, verbatim:**

> "Consider the composition
>   eta_q : P^1 --(q-1)--> P^1 -> P^1 --(p-1)--> P^1 -> P^1.
> Here, the first and third maps denote the (q-1)- and (p-1)-power maps,
> respectively. The second map is a linear transformation fixing 1 and infinity
> and sending 0 to any other F_q-rational point of P^1_{F_q}. The final map is
> also a linear transformation which fixes infinity and swaps 0 with 1."

**KMU-I Prop. 4.3, verbatim:** "The composite `eta = eta_q o eta_0 : X ->
P^1_{F_q}` is a tame Belyi map such that 1. `eta(P) = 0` for each `P in S`.
2. If `eta(P) = 1` then the ramification index of `eta` at `P` is `p-1`."

At `p = 2` this degenerates in **three independent ways**, all of them the
single fact `mu_{p-1} = {1}`:

(a) `z^{p-1} = z` is the identity, so no ramification is created;
(b) the resulting `e_P = 1` is incompatible with Riemann-Hurwitz whenever
    `g >= 1` (sec. 3.8.4 for the correct qualifier);
(c) the auxiliary point that KM-exp places at `c = 2` **is** the point `0` in
    characteristic 2, so even the placement step is empty.

(`20` P3-4 calls this framing "the clearest statement of the geometric half of
the p = 2 problem I have seen in this project"; it is `05` sec. 1.2's,
**AUDITED-CONFIRMED**.)

### 3.8.2 Lemma B and its proof

> **LEMMA B.** Let `q = 2^a`, let `X` be a smooth projective geometrically
> irreducible curve over `F_q`, let `S subset X` be a finite set of closed
> points, and let `e > 1` be odd with `e | q-1`. Then, after enlarging `F_q` if
> necessary (only to make branch points and `S` rational and `q` large), there
> is a tame Belyi map `eta : X -> P^1_{F_q}` -- finite, separable, ramified
> only over `{0, 1, infinity}`, all branch points `F_q`-rational -- with
>
> 1. `eta(P) = 0` for every `P in S`;
> 2. every `P in eta^{-1}(1)` of ramification index exactly `e`;
> 3. hence `r_1 e = deg(eta)`, `eta^*(1) = sum_{eta(P)=1} e P`, and
>    `2(g-1) + r_0 + r_1 + r_infinity = deg(eta)` (KMU-I (8) = KM-ab (4)).

*Proof.*

**Step 0 (the tame map).** By **KLW Theorem 1.2** there is a finite separable
tame `eta_0 : X -> P^1_{F_q}`. This is the `p = 2` replacement for the input
KMU-I Theorem 4.1 takes from Fulton, and it is *stronger*: no base extension
is needed for the tame map itself. Verbatim (arXiv:2010.01130v2; **CITED**,
fetched independently by `05` and by `20` for Part Three):

> "Theorem 1.1 (Fulton). Let X be a smooth, projective, geometrically
> irreducible curve over a field k. If p = 0, or if p > 2 and k is infinite,
> then there exists a finite separable morphism f : X -> P^1_k which is
> everywhere simply ramified, and hence tame."
>
> "Theorem 1.2. If k is finite, then there exists a finite separable tame
> morphism f : X -> P^1_k."
>
> "Theorem 7.6. If k is finite, then every SY class of X is trivial.
> Consequently, by Lemma 5.4 and Lemma 6.6, X admits a tame morphism to P^1_k."

whose `p = 2` half rests on **Sugiyama--Yasuda Theorem 1.1**
(arXiv:1708.03036v2 = Compos. Math. 156 (2020) 325-339; **CITED**):

> "Theorem 1.1. Let X be a proper smooth curve over an algebraically closed
> field k. Then X admits a morphism f : X -> P^1_k that is tamely ramified
> everywhere."

Note what KMU's Theorem 4.1 actually asks for: **tame**, nothing more. Simple
branching is how Fulton *gets* tameness at `p >= 3`; it is false at `p = 2`
(KLW: "when p = 2 ... simply ramified morphisms are not always tame") and is
not needed. (`20` P3-11 confirms the division of labour: SY is over an
algebraically closed field; KLW Thm 1.2 / 7.6 supplies the finite-field
statement KMU Theorem 4.1 needs.) Enlarge `F_q` so that every branch point of
`eta_0` and every point of `S` is rational, `mu_e subset F_q` (automatic from
`e | q-1`), and `q+1 > |Branch(eta_0) u eta_0(S)| + 2`; choose the coordinate
on the target so that `0` and `infinity` avoid `Branch(eta_0) u eta_0(S)`,
hence `Branch(eta_0) u eta_0(S) subset F_q^*`.

**Step 1 (`g_1 = z^{q-1}`).** `q-1` is odd, so `g_1` is tame; it is totally
ramified over `0` and `infinity` with index `q-1` and unramified elsewhere
(its derivative `(q-1)z^{q-2} = z^{q-2}` vanishes only at `0`), and
`g_1(F_q^*) = {1}`. Put `phi := g_1 o eta_0`. Then
`Branch(phi) subset {0,1,infinity}` and `phi(S) = {1}`. Because `0` is not a
branch point of `eta_0`, every point of `phi^{-1}(0) = eta_0^{-1}(0)` has
index exactly `q-1`.

**Step 2 (`g_2`).** Choose `c in mu_e(F_q) \ {1}` (nonempty since `e | q-1`,
`e > 1`) and let `g_2 in PGL_2` fix `1` and `infinity` with `g_2(0) = c`. Then
`Branch(g_2 phi) = {c, 1, infinity}` and `(g_2 phi)(S) = {1}`, and the point
`0` is **not** in this branch locus (`c` is a root of unity, so `c != 0`).

> **`g_2` is not decorative.** Its sole job is to evacuate the point `0` from
> the branch locus, so that the fibre over `0` is *clean* for Step 3. Without
> it, `0 in Branch(phi)` and the points of `(g_3 phi)^{-1}(0)` would have index
> `e * e_phi(.)` with `e_phi` varying over the fibre -- so the fibre over the
> final `1` would have **mixed** index and Prop. 4.3(2) would be false. This is
> the first thing a referee checks. (`20` P3-1.)

**Step 3 (`g_3 = z^e`).** `gcd(e,2) = 1`, so `g_3` is tame; it is totally
ramified over `0` and `infinity` with index `e`, unramified elsewhere, and
`g_3^{-1}(1) = mu_e ni c, 1`. Hence, **using `c^e = 1`**,

```
   Branch(g_3 g_2 phi) subset g_3({c,1,infinity}) u {0,infinity} = {0, 1, infinity}.
```

The fibre `g_3^{-1}(0) = {0}` has index `e`, and `0` is unramified for
`g_2 phi` by Step 2, so **every point of `(g_3 g_2 phi)^{-1}(0)` has index
exactly `e`**; there are `deg(g_2 phi) = (q-1) deg(eta_0)` of them.

**Step 4 (`g_4`).** Let `g_4 in PGL_2` fix `infinity` and swap `0` and `1`; it
carries the `S`-fibre (over `1`) to `0` and the uniform-index-`e` fibre (over
`0`) to `1`. Set `eta := g_4 g_3 g_2 g_1 eta_0`. Claims (1) and (2) hold.

**Tameness.** Ramification indices multiply and every factor is odd:
`e_{eta_0}` is odd because `eta_0` is tame at `p = 2`; `q-1` is odd; `e` is
odd; linear maps are unramified. So every index of `eta` is prime to `p = 2`.
`eta` is finite and separable as a composite of such. Explicitly:
`e_eta(P) = e_{eta_0}(P)` for `P in S`; `e_eta(P) = e` for `P` over `1`;
`e_eta(P) = e(q-1)e_{eta_0}(P)` for `P` over `infinity`.

**Claim (3).** All points over `1` have index `e` and indices over a point sum
to the degree, so `r_1 e = deg(eta)` and `eta^*(1) = sum_{eta(P)=1} e P` has
degree `deg(eta)`. Tame Riemann-Hurwitz for `eta : X -> P^1` unramified
outside `{0,1,infinity}`:

```
   2g-2 = -2 deg(eta) + sum_{Q in {0,1,inf}} sum_{P|Q}(e_P - 1)
        = -2 deg(eta) + sum_Q (deg(eta) - r_Q) = deg(eta) - (r_0+r_1+r_infinity).
```

**QED**

**The fibre over the final `0` is a genuine mixture, and that is fine.** It
contains the `S`-points with index `e_{eta_0}`, the `eta_0^{-1}(0)` points
arriving via `c` with index `q-1`, and `e-2` unramified sheets from the other
`e`-th roots of unity. KMU-I asks only `eta(S) = {0}` and KM-ab only
`tau_i in eta^{-1}({0, infinity})` -- **never** that the whole fibre be `S`.
(`20` P3-1 recommends stating this explicitly; `05` does not.)

**Where the second ramification point of `z -> z^e` goes.** `z -> z^e`
ramifies exactly at `0` and `infinity`. The point `0` is the wanted one: it
becomes the fibre over the final `1`. The point `infinity` maps to `infinity`,
which `g_4` fixes, so the second ramification point lands **over `infinity`**,
with index `e(q-1)e_{eta_0}` -- large, but odd, hence tame. **It creates no
new Type-2 point and does not meet `S`** (which sits over `0`). Two sources
say why:

> **KMU-I sec. 4.3, verbatim:** *"Evidently, if `eta(P) = 0` or `infinity` then
> `sigma(t_P) = t_P^p`. The local Frobenius for `eta(P) = 1` is more
> complicated: `sigma(t_P) = ((t_P^{p-1}+1)^p - 1)^{1/(p-1)}`."*
>
> **KM-ab sec. 3.4, verbatim:** *"For `Q in X` with `eta(Q) in {0, infinity}`,
> we may take the local parameter at `Q` to look like `u_Q = t^{+-1/e_Q}`,
> where `e_Q` is the ramification index at `Q`. In particular, the Frobenius
> endomorphism sends `u_Q -> u_Q^q`. If `eta(Q) = 1`, we take the local
> parameter to look like `u_Q = (t-1)^{1/(p-1)}`. Thus, the Frobenius
> endomorphism sends `u_Q -> ((u_Q^{p-1}+1)^p - 1)^{1/(p-1)}`."*

Because `sigma(u_0) = u_0^p` and `sigma(u_infinity) = u_infinity^p` are *pure*
p-th powers, the unique `e_P`-th root congruent to `t_P^p` mod `p` is `t_P^p`
itself, **whatever `e_P` is**. Only over `1`, where
`sigma(u_1) = (u_1+1)^p - 1` is not a pure power, does the root extraction
produce the `(1+py)^{1/e_P}` factor of sec. 3.1. KM-ab's phrasing is the
stronger witness, because it writes the `{0,infinity}` case with a **general**
`e_Q` in the parameter, where KMU-I's could be read as assuming `e_P = 1`
there (`20` P3-2).

**Status.** DIARY `05` Lemma B, **AUDITED-CONFIRMED** (`20` Part Three P3-1,
P3-2, P3-3, P3-7: every index re-derived independently, the local-Frobenius
point confirmed from two sources, the bookkeeping and the explicit instance
reproduced). The proof above is this workstream's own re-derivation and agrees
with both.

### 3.8.3 The correction to Prop. 4.3, and the necessity of `3 | q-1`

> **CORRECTION (PROVED HERE).** KMU-I Prop. 4.3's second map, "a linear
> transformation fixing 1 and infinity and sending 0 to **any other**
> F_q-rational point", over-states the freedom, at every p. The point `c` must
> satisfy `c^{p-1} = 1`.

*Proof.* After `g_2` the branch locus is `{c, 1, infinity}`; after
`g_3 = z^{p-1}` it is `{c^{p-1}, 1, infinity} u {0, infinity}`. For `eta` to be
Belyi one needs `c^{p-1} in {0,1,infinity}`, and `c not in {0, infinity}`
excludes the first and third, forcing `c^{p-1} = 1`, i.e.
`c in mu_{p-1}(F_q) \ {1}`. **QED** With a generic `c` the composite has a
**fourth** branch point, `U = eta^{-1}(V)` is not etale over `V`, and the
lifting of KMU-I sec. 4.2 has no basis -- so this is load-bearing, not
cosmetic.

> **But no published mathematics is wrong.** KM-exp Lemma 3.1, the original,
> is **correct**: it puts the branch points at `{1, 2, infinity}`, i.e.
> `c = 2`, and `2^{p-1} = 1` in `F_p` by Fermat with `2 != 1` for `p >= 3`.
> The defect is confined to KMU-I's *paraphrase* of that lemma, and the repair
> is one word: `c in mu_{p-1}(F_q) \ {1}`, a set that is nonempty **exactly
> because `p >= 3`**. At `p = 2` the point "2" is the point `0`, which is
> degeneration (c) of sec. 3.8.1.

(`05` sec. 1.2, **AUDITED-CONFIRMED** (`20` P3-4) as "a genuine requirement
and a genuine misstatement", with the KM-exp nuance.)

> **PROPOSITION (PROVED HERE).** A degree-3 auxiliary map with the properties
> Lemma B's Steps 2-4 require exists over `F_q`, `q = 2^a`, **iff `3 | q-1`**,
> i.e. iff `a` is even.

*Proof.* Write the auxiliary stage as one map `h = g_4 g_3 g_2 : P^1 -> P^1`.
Required of it: `h` tame; `Branch(h) subset {0,1,infinity}`;
`h({0,1,infinity}) subset {0,1,infinity}`; `h(1) = 0`; and every
`y in h^{-1}(1)` has `e_h(y) = 3` with `y not in {0,1,infinity}` (so the
earlier stage, whose branch locus is `{0,1,infinity}`, is unramified there).

*Sufficiency* is Lemma B with `e = 3`. For *necessity*: by Riemann-Hurwitz a
tame degree-3 self-map of `P^1` in characteristic 2 has
`sum_P(e_P - 1) = 2*3 - 2 = 4` with every `e_P` odd (`e = 2` is **wild** at
p = 2) and `e_P <= 3`; so `e_P in {1,3}` and there are exactly two totally
ramified points. Call them `alpha` (over `1`) and `beta`; then
`h^*(1) = 3[alpha]` and `h^*(w) = 3[beta]` with `w := h(beta) in {0,infinity}`
(it cannot be `1`, the fibre over `1` being `{alpha}`), and `h` is unramified
elsewhere. Four configurations, each forcing `alpha^3 = 1`, `alpha != 1`:

- *`w = infinity`, `beta = infinity`.* `h` is a cubic polynomial; `h(0) =
  infinity` is impossible and `h(0) = 1` would force `alpha = 0` (excluded), so
  `h(0) = 0`. Total ramification at `alpha` over `1` gives
  `h = lambda(z+alpha)^3 + 1` (char 2), so `h(1) = 0` gives
  `lambda(1+alpha)^3 = 1` and `h(0) = 0` gives `lambda alpha^3 = 1`, whence
  `(1 + 1/alpha)^3 = 1`. Setting `gamma := 1 + 1/alpha != 1`, `gamma` is a
  primitive cube root of unity; `gamma^2 + gamma + 1 = 0` gives
  `1 + gamma = gamma^2`, so `alpha = gamma^{-2} = gamma`.
- *`w = infinity`, `beta != infinity`.* Then `h(infinity) = 0`. If `beta = 0`,
  `h = lambda(z+alpha)^3/z^3` and `h(1) = 0` forces `alpha = 1`, excluded. So
  `beta not in {0,1,infinity}` and `h^*(0) = [0]+[1]+[infinity]`, i.e.
  `h = lambda z(z+1)/(z+beta)^3`. Matching
  `(z+beta)^3 + lambda z(z+1) = (z+alpha)^3` in characteristic 2 gives
  `beta + lambda = alpha`, `beta^2 + lambda = alpha^2`, `beta^3 = alpha^3`.
  The first two give `(alpha+beta)^2 = alpha+beta`, so `beta = alpha` (whence
  `lambda = 0`, degenerate) or `beta = alpha+1`; the third then gives
  `(alpha+1)^3 = alpha^3`, i.e. `alpha^2 + alpha + 1 = 0`.
- *`w = 0`.* Then `h^*(0) = 3[beta]` and `h(1) = 0` force `beta = 1`, and
  `h(0) = h(infinity) = infinity` (the alternatives force `0 = 1` or
  `alpha in {0,infinity}`). So `h = lambda(z+1)^3/(z(z+beta'))` for a third
  simple pole `beta'`, and matching
  `lambda(z+1)^3 + z(z+beta') = lambda(z+alpha)^3` in characteristic 2 gives,
  from the `z^0` coefficient, `lambda = lambda alpha^3`, i.e. `alpha^3 = 1`;
  and `alpha = 1` would make the `z^2` coefficient read `lambda + 1 = lambda`.
- *`w = 0`, `beta != 1`* is impossible, since `h(1) = 0` and the fibre over `0`
  is `{beta}`.

So `alpha` is a primitive cube root of unity in `F_q`, whence `3 | q-1`.
**QED**

*Concurrence and audit.* `05` sec. 1.4 reaches the same conclusion by the same
case analysis and enumerates every candidate over `GF(2^n)` for `q <= 64`.
`20` P3-5 did its **own** classification and enumeration and reports:

```
  a=1 q= 2  3|q-1: False  #maps=  0  alphas=[]        mu_3\{1}=[]
  a=2 q= 4  3|q-1: True   #maps=  6  alphas=[2, 3]    mu_3\{1}=[2, 3]
  a=3 q= 8  3|q-1: False  #maps=  0  alphas=[]        mu_3\{1}=[]
  a=4 q=16  3|q-1: True   #maps=  6  alphas=[6, 7]    mu_3\{1}=[6, 7]
  a=5 q=32  3|q-1: False  #maps=  0  alphas=[]        mu_3\{1}=[]
  a=6 q=64  3|q-1: True   #maps=  6  alphas=[58, 59]  mu_3\{1}=[58, 59]
```

**AUDITED-CONFIRMED.** (The map counts differ from `05`'s -- 6 against 8 -- a
normalisation difference in how the Mobius factor is parametrised; the two
load-bearing outputs, the existence pattern and the `alpha` set, agree on
every field. Recorded because a bare disagreement in a table should not be
buried.)

### 3.8.4 `mu(P) = e_P`, the global count, and the `e_P`-independence of the target

KMU-I (11) sets `mu(P) = 0` for `eta(P) in {0, infinity}` and `p-1` for
`eta(P) = 1`; the proof of Prop. 4.10 says, verbatim: *"The kernel is precisely
the global sections of the line bundle L(D), where D = sum_{eta(P)=1}
(p-1)P."* So `D = eta^*(1)` **iff `mu(P) = e_P`**, and then
`deg D = deg(eta) > 2g-2` by (8), so Riemann-Roch gives

```
   N = h^0(D) = deg(eta) + 1 - g = g - 1 + r_0 + r_1 + r_infinity   (KMU-I (13)),
```

**unchanged in form** with `e_P = 3`: the only `e_P`-dependence is
`r_1 = deg(eta)/e_P`, cancelling against `deg D = e_P r_1 = deg(eta)`.
Lemma 7.12 (Deuring-Shafarevich) pins the number of slope-0 segments at `N`,
and Cor. 7.14 cancels `r_0+r_1+r_infinity-|S|` of them, leaving `g-1+|S|` --
**exactly the Kramer-Miller ramification-defined count of KMU-I sec. 1.2,
independent of `e_P`.** So the target polygon is the KM one and not a weakened
variant. (`01`, `04` sec. 7.4, `05` sec. 1.6 from KM-ab Prop. 7.2 as well;
**AUDITED-CONFIRMED** at `20` Part One sec. 2.5, P2-5 and P3-3. `20` also
notes the `e_P`-independence needs no Riemann-Roch at all: `r_1` cancels
identically whatever its value.)

> **A counting-convention trap, flagged so readers do not stumble.** KM-ab's
> truncation function (33) reads `mu(Q) = 1` for `eta(Q) in {0, infinity}` and
> **`mu(Q) = p`** for `eta(Q) = 1` -- `p`, not `p-1`. KMU-I (11) has `p-1`.
> They denote the *same* truncation ("drop poles of order `<= p-1 = e_P`"),
> one counting the first **kept** index and the other the last **dropped**
> one. With `e_P = 3` both read "drop poles of order `<= 3`", which is (A1).
> (`05` renders this correctly; `20` P3-3 confirms it and calls it easy to get
> wrong.)

**A qualifier that must be carried.** "Riemann-Hurwitz forbids `e_P = 1` at
p = 2" is **over-stated without a genus hypothesis**. From (8), `e_P = 1`
gives `deg(eta) = r_1` and hence `2(g-1) + r_0 + r_infinity = 0`, impossible
for `g >= 1` but *not* for `g = 0`: the witness is `X = P^1`, `eta(x) = x^n`
with `n` odd, tame at p = 2, totally ramified over `0` and `infinity`
(`r_0 = r_infinity = 1`), unramified over `1` with `r_1 = n = deg(eta)`, and
satisfying (8): `2(0-1) + 1 + n + 1 = n`. (`20` Part One item 6,
**AUDITED-CONFIRMED as a GAP** in `01`; it changes nothing for the
arbitrary-curve target, but it is presented in `01` as a proof step and is not
one. The correct minimality statement: `e_P` must be prime to 2 and `> 1`,
hence odd and `>= 3`.)

### 3.8.5 An explicit instance, and the extension-free variant

**Explicit instance (PROVED HERE).** Take `X = P^1`, `eta_0 = id`,
`S subset F_q^*`, and `omega` a primitive cube root of unity in `F_q`
(`3 | q-1`). Then `g_2(z) = (1+omega)z + omega`, `g_4(z) = z+1`, and

```
     eta(z) = ( (1+omega) z^{q-1} + omega )^3 + 1,        deg eta = 3(q-1).
```

Write `P(z) = (1+omega)z^{q-1} + omega`, so `eta - 1 = P^3` in characteristic
2. `P' = (1+omega)z^{q-2}` (as `q-1` is odd) and `P(0) = omega != 0`, so
`gcd(P,P') = 1` and `P` has `q-1` distinct roots, none equal to `0`. Hence:

- **fibre over 1:** `q-1` points of index exactly 3, none in `{0,1,infinity}`
  (`P(0) = omega`, `P(1) = 1`); so `r_1 = q-1` and `r_1 * 3 = deg eta`;
- **fibre over 0:** `eta = 0` iff `P in mu_3`. `P = 1` iff `z^{q-1} = 1`, i.e.
  `z in F_q^*` (`q-1` simple points -- where `S` sits, unramified);
  `P = omega` iff `z = 0`, with multiplicity `q-1`; `P = omega^2` iff
  `z^{q-1} = (omega+omega^2)/(1+omega) = 1/omega^2 = omega` (using
  `1+omega+omega^2 = 0`), another `q-1` simple points. So `r_0 = 2q-1`, with
  indices `q-1, 1, ..., 1` summing to `3(q-1)`;
- **fibre over infinity:** `{infinity}` with index `3(q-1)`, `r_infinity = 1`.

Check (8): `2(0-1) + (2q-1) + (q-1) + 1 = 3q-3 = deg eta`. And
`sum_P(e_P - 1) = (q-2) + 2(q-1) + (3(q-1)-1) = 6q-8 = 2 deg(eta) - 2`, so
**Riemann-Hurwitz is saturated by these three fibres**: there is no
ramification anywhere else, and `eta` really is Belyi. All indices odd.
(**AUDITED-CONFIRMED**: `20` P3-7 verified this symbolically and numerically
over `GF(4)` and `GF(16)`; every number matches `05`'s.)

**Remark (extension-free variant: geometry only).** Delete Steps 2 and 3 and
set `eta := g_4 o g_1 o eta_0`. By Step 1 every point of `phi^{-1}(0)` already
has index exactly `q-1` (odd, `> 1` for `q >= 4`), so `g_4` alone gives a tame
Belyi map with `eta(S) = {0}` and **uniform index `e = q-1` over `1`**, with no
root-of-unity condition and no auxiliary stage. More generally the `e`-power
stage exists exactly when `e | q-1`; and `e | q-1` is *simultaneously* the
condition for `mu_e subset Z_q`, i.e. for the `Gal(E/E_0) = Z/e` eigenspace
decomposition KMU Def. 6.3 uses. At odd `p`, `p-1 | p^a - 1 = q-1`
automatically, which is *why* KMU's choice is `p-1`. **As stressed in
sec. 2.2, this variant is insurance, not a drop-in:** it moves `mu(P)` to
`q-1` and voids Theorem 3's `e = 3`-specific analysis. **AUDITED-CONFIRMED as
geometry** (`20` P3-8), with that caveat attached at source.

## 3.9 Base-change invariance of `NP_q` and `HP_q`

Both source papers consume an unspecified base extension and assert the
reduction without proof (KM-ab sec. 2.1, quoted in sec. 2.2; KM-exp Lemma 3.1
and KM-ab Lemma 3.1 both open "After increasing q"; KMU-I Thm. 4.1 says "After
extending the base field"). Since Lemma B's `3 | q-1` leans on it, here is the
argument.

> **PROPOSITION (PROVED HERE).** Let `F_{q^m}/F_q` be finite and
> `rho' = rho|_{pi_1(X_{F_{q^m}})}`. Assume `rho'` is nontrivial. Then
> `NP_{q^m}(rho') = NP_q(rho)` and `HP_{q^m}(rho') = HP_q(rho)` as polygons.
> Hence Theorem T1 over `F_{q^m}` implies it over `F_q`.

*Proof.* **Newton side.** `H^1_c(X_{Fbar_q}, F_rho)` is geometric, hence
unchanged, and `Frob_{q^m} = Frob_q^m`, so the inverse roots become
`alpha_i^m`. In the `q^m`-adic normalisation,

```
   v_{q^m}(alpha_i^m) = v_p(alpha_i^m)/v_p(q^m) = m v_p(alpha_i)/(m v_p(q)) = v_q(alpha_i).
```

The multiset of normalised valuations, hence the polygon, is unchanged.

**Hodge side, and the trap.** `HP_q(rho)` has length
`2(g-1+|S|) + sum_P (d_P - 1)`. **If `|S|` counted closed points of `X/F_q`,
base change would change it** (a closed point of degree `d` splits into
`gcd(d,m)` points) and `HP` would *not* be invariant. The degree count forces
the geometric reading:

```
   2(g-1+|S|) + sum_P (d_P - 1) = 2g - 2 + |S| + sum_P d_P = - chi_c(U, F_rho),
```

by Grothendieck-Ogg-Shafarevich for a rank-1 sheaf -- and **GOS sums over
geometric points**. So `|S|` is the geometric count and the `d_P` are the
geometric Swan conductors; `g` is geometric; Swan conductors are invariant
under unramified base change. Every ingredient of the slope multiset is
therefore unchanged, and so is ordinarity of `X`. **QED**

**The hypothesis is not vacuous but cannot fail here.** `rho'` could become
trivial for a character pulled back from `Gal(Fbar_q/F_q)`; it cannot here,
because `rho` is wildly ramified at some point of `S` and ramification is
geometric. (`20` P3-6 flags this as the one unstated hypothesis of `05`'s
proof.)

**Status: AUDITED-CONFIRMED** (`20` P3-6, which audited each half and
identified the geometric-count trap as "the one step where a careless reading
would make Lemma B's side condition *not* free"). For KM-ab's general `rho`
one also needs `Omega_rho` invariant: `eps' = eps(1 + q + ... + q^{m-1})` with
`eps <= q-2 < q`, so the `m` summands occupy **disjoint digit blocks with no
carries**, giving `omega' = m omega`, `a' = ma`, hence `Omega' = Omega`
(`05` sec. 1.4, **AUDITED-CONFIRMED** at `20` P3-6). Irrelevant here, since
`Omega_rho = 0` for 2-power `rho`.

## 3.10 What the global argument consumes, and why `d(k) = 0` is fatal

Two facts that explain why `d(k) >= 1` and nothing stronger is the right
target (`01` sec. 3 and `20` Part One sec. 2.5, **AUDITED-CONFIRMED**, with
`20` localising it more sharply than `01`; independently witnessed on the
KM-ab side at `20` P3-11):

- **On the KMU-I route the unique consumer is Lemma 7.11**, which opens:
  *"recall from the global Hodge bound that the pi-adic valuation of
  `Theta~(e^{m_e}_{alpha,k})` is >= e if either: alpha = P not in S, or
  alpha = P in S and k >= e delta_P."* With `m_{e,P} = 1/e` the `eta(P) = 1`
  columns have slope `d(k) e`, so this is `d(k) >= 1`, **non-strictly**, and
  nothing more. The non-strictness is right because
  `I^{<r}(Psi) = {i : v_pi psi(e_i) < r}` uses a strict `<`, so a column of
  slope *exactly* `r` is already outside `I^{<r}` and only `>= r` is asked of
  it (Def. 7.3(2)). **On the KM-ab route** the corresponding consumer is
  sec. 7.2 case (II), verbatim: *"Write `n = k+pm` [...] we know **`b(n) >= m`**
  [...] `col >= m`"* and *"When `Q` is from case (II) **each slope in `P_Q` is
  at least one**"* -- i.e. exactly (A4) and (A3), and nothing about the shape
  of the multiset.
- **`d(k) = 0` is fatal, not merely lossy.** Lemma 7.12
  (Deuring-Shafarevich) says that for `X` ordinary, `NP^{<r}_{pi_q}(phi)` has
  exactly `N` segments of slope 0, and the bound has `N` of them. A `d(k) = 0`
  column inserts an `(N+1)`-st, so the two polygons can no longer share a
  terminal point. It breaks a *count*, not a bound. That is why Remark 6.5
  says "too low for applications" rather than "weaker than we would like".

**The strictness audit at p = 2.** Workstream 03 measured that at p = 2 the
wild-point optimum has zero *multiplicative* slack (odd p carries a spare
factor `p-1`), so any step consuming strict slack was a candidate p = 2
obstruction. It comes out clean: the one strict inequality in the perturbation
machinery, KMU Def. 7.3(1), is supplied by the margin
`[kp - k(p-1)]/delta_P = k/delta_P`, **independent of p** -- the `(p-1)` that
vanishes at p = 2 is not the source of that strictness. (`04` sec. 7.1,
**AUDITED-CONFIRMED** at `20` P0-9, P2-5; independently on the KM-ab side by
`05` sec. 2.2 rows 10, 16, 20, 23, 24, with rows 16 and 23 re-verified at
`20` P3-10/P3-11: the `pi_s^{n(p-1)}` gain normalises to slope `n/s` at every
`p` because `v_p(pi) = 1/(p-1)`, so the `(p-1)` cancels exactly.) The only
additive tightness anywhere is `d(6) = 1`, exactly at the threshold and
exactly sufficient.

## 3.11 The dictionary: how the repair transports to KM-ab

This is the step that could have severed the chain between the local repair
(stated in KMU-I's language) and the global argument that carries T1 (KM-ab's).
It holds exactly. **KM-ab sec. 4.2, verbatim at source:**

> `nu : E^dagger -> E^dagger` sends `t` to `((t^{p-1}+1)^p - 1)^{1/(p-1)}`;
> `b(n) = floor((-n-1)/(p-1))` for `n <= -1`, `0` for `n >= 0`;
> `D = prod_{n in Z} p^{b(n)} t^n O_L`, "which we regard as a sub-`O_L`-module
> of `O_{E^dagger}`";
> **Proposition 4.2.** "For all `n in Z_{>=0}` and `0 <= k <= p-1`, we have
> `U_p(p^{b(-k-np)} t^{-k-np}) in p^n D`, `U_p(D) subset D`. Proof. See [15,
> Proposition 4.4]."

| KM-ab | KMU-I / this document | agree? |
|---|---|---|
| `nu(t) = ((t^{p-1}+1)^p-1)^{1/(p-1)}` | the Type-2 `sigma` of sec. 3.1 | **identical** |
| `b(-K) = floor((K-1)/(p-1))` | `a_KMU(K) = floor((K-1)/(p-1))` (KMU-I Def. 6.3) | **identical** under `n = -K` |
| `K = k + np`, `0 <= k <= p-1`, gain `p^n` | `K = p*ell + r`, `0 <= r < p`, gain `pi^{ell/m_P}` | **identical** (`n = ell`, `k = r`) |
| `D = prod_n p^{b(n)} t^n O_L` | `A^{m,*} = {sum b_k t^{-k} : v_pi(b_k) >= a(k)/m_P}` | **same shape**, and `D` is **coefficientwise** |
| `U_p(D) subset D` | (A5) / (A3) in the weak form | **identical** |

So **Lemma A and Theorem 3 transport to KM-ab sec. 4.2 verbatim**: same
operator, same weight function under `n <-> -K`, and because `D` is defined
coefficientwise, a non-eigenspace weight is native there. Two consequences,
already used above: the calibration is exact rather than conservative
(sec. 3.5), and the integer-valuedness of `a` means `p^{a(k)} in O_L` with no
base change (sec. 3.6).

**Status: DIARY `05` sec. 2.2 row 11 and sec. 2.3(b); AUDITED-CONFIRMED**
(`20` P3-10, which read every line of the correspondence at source and calls
it "the step that could have severed the chain, and it holds exactly").
Supporting rows, also read at source and **AUDITED-CONFIRMED** (`20` P3-11):
**Prop. 7.2**'s Riemann-Roch step is proved by reduction mod `m` (Lemma 7.3)
and *"the weight does not appear in Prop. 7.2 at all"*; **Prop. 7.4**'s change
of basis is **diagonal** (`x_i/y_i`), and every principal minor is invariant
under diagonal conjugation, so the Fredholm series agree coefficient by
coefficient **for any weight**, provided both operators are nuclear -- which is
Lemma 6.12's `lim col_i = infinity`, i.e. `d(k) -> infinity` (Theorem 3). The
source even settles KMU-I Def. 6.3's "formal basis" worry on its own side,
verbatim: *"From the definition of `O_R^con` we see that `G^con = {x_i e_i}`
is a formal basis of `V^con`. Indeed, we just selected the `x_i` appropriately
for each summand."*

---

# 4. Corrections to the literature found en route

Each with its witness and status. None is a p = 2 obstruction; all are
p-uniform source defects except sec. 4.5, which is the p = 2 estimate itself.

## 4.1 KMU-I Prop. 4.3's "any other F_q-rational point"

**Witness and repair:** sec. 3.8.3. The linear map's target `c` must satisfy
`c^{p-1} = 1`; with a generic `c` the composite has a fourth branch point and
is not Belyi, `U = eta^{-1}(V)` is not etale over `V`, and sec. 4.2's lifting
collapses. **Important framing: no published mathematics is wrong.** KM-exp
Lemma 3.1, the original, takes `c = 2` and is correct at every `p >= 3`; the
defect is confined to KMU-I's paraphrase, and the repair is one word
(`c in mu_{p-1}(F_q) \ {1}`, nonempty exactly because `p >= 3`). At `p = 2`
the point "2" is the point `0`, one of the three degenerations of sec. 3.8.1.
**PROVED HERE**; DIARY `05` sec. 1.2, **AUDITED-CONFIRMED** (`20` P3-4).

## 4.2 KMU-I Def. 6.3: the strict `>` is inconsistent with its own claim

Def. 6.3 defines `B^m_{pi,P} = { sum b_k u^{-k} : v_pi(b_k) > k/m_P }` with a
**strict** inequality, then asserts that `{ pi^{a(k)/m_P} t_P^{-k} }` is a
formal basis of `A^m_{pi,P}` -- which with `>` is **literally false**, the
basis elements sitting exactly on the boundary. KMU's own sec. 2.1 defines
`A^m(b) = { sum a_k t^{-k} : v_pi(a_k) >= (k-b)/m }`, **non-strict**. The
repair is `>=` throughout; nothing downstream sees the difference, every
estimate here being coefficientwise. The same slip bites Prop. 6.1's last
step, which needs the non-strict version. **Source infelicity, p-uniform**,
and it does not arise on the KM-ab side at all (sec. 3.11).
DIARY `04` sec. 7.1 and `20` Part One sec. 1.2 / P2-5 (which traced it to
sec. 2.1 at source), **AUDITED-CONFIRMED**.

## 4.3 KM-ab sec. 4.1.1: "We know `-q(e,i) <= a(p-1)`" is false, p-uniformly

**Witnesses:** `p = 2, a = 3, eps = 3, j = 1` gives `-q = 4 > 3`;
`p = 3, a = 2, eps = 5, j = 1` gives `-q = 5 > 4`. The weaker bound
`-q <= ap` also fails (`p = 2, a = 4, eps = 7, j = 3`: `-q = 9 > 8`) and
cannot be repaired by shrinking `s`, both terms scaling as `1/s`. **The true
bound is `-q(e,j) <= (p-1) a(a+1)/2`**, which equals `a(p-1)` only for `a = 1`.
Swept for `p in {2,3,5}`, `a <= 6`, all `eps`.
**NEEDS-RESTATEMENT in the source**, and **vacuous for the target of this
document** (2-power `rho` has `eps = 0`, hence `q(e,j) = 0`).
DIARY `05` sec. 2.2 row 15; **AUDITED-CONFIRMED** (`20` P3-12, which
reproduced the witnesses from its own independent sweep and supplied the true
bound).

## 4.4 KM-ab (18): the feasibility of the `s_Q` choice is asserted, not proved

KM-ab (18) requires an `s_Q` with
`1/s_Q - omega_Q/(a s_Q (p-1)) >= 1`, and the source does not argue such an
`s_Q` exists. **Repair:** `eps_Q` is "the unique integer between `0` and
`q-2`", and the only `eps <= p^a - 1` with digit sum `a(p-1)` is
`p^a - 1 = q-1`, which is excluded; so `omega_Q <= a(p-1) - 1` and
`1 - omega_Q/(a(p-1)) >= 1/(a(p-1)) > 0`, whence any small enough `s_Q` works.
At `p = 2`: `omega_Q <= a-1`. Exhaustively checked for `p in {2,3,5}`,
`a <= 6`: 0 violations. Trivial for 2-power `rho`.
DIARY `05` sec. 2.2 row 16; **AUDITED-CONFIRMED** (`20` P3-13, which
re-derived the digit-sum bound at source and confirms "the source really does
not prove it").

## 4.5 KMU-I Remark 6.5's `floor((k-1)/3)` is superseded

`floor((k-1)/3)` fails (A3) at exactly one index in the whole range, `k = 5`
(`d(5) = floor(4/3) - floor(3/3) = 0`), plus `k = 1,2,3` which `k > mu(P) = 3`
removes. The weight `floor((k-1)/3) + (k mod 2)` -- **KMU's own weight plus a
parity indicator** -- satisfies (A1)-(A5) for **every** `k`, with `d(k) >= 1`,
`d(k) ~ k/6`, and `k/6` exactly optimal (Theorem 4). So Remark 6.5's estimate
is not a theorem about p = 2; it is an artifact of one weight choice.
**PROVED HERE** (sec. 3.6, 3.7); **AUDITED-CONFIRMED**.

Two things this does *not* say. Remark 6.5's estimate **is sharp as stated**
(the leading coefficient is a unit, Theorem 1), so `d(5) = 0` was real, not a
lossy bound. And KMU nowhere claim `floor((k-1)/3)` is optimal -- Remark 6.5
says only "A similar construction provides ..." and "This estimate is too low
for applications".

## 4.6 Smaller textual defects, recorded

- **The `mu` counting convention differs between the two papers**: KM-ab (33)
  has `mu(Q) = p` for `eta(Q) = 1`, KMU-I (11) has `p-1`; they denote the same
  truncation, one counting the first kept index and the other the last dropped
  one (sec. 3.8.4). **AUDITED-CONFIRMED** (`20` P3-3).
- KMU-I (11) prints `mu(P) = 0` "if `Q = 0` or `1`"; the display and every use
  require `0` for `Q in {0, infinity}`. (`05` sec. 1.3.2, PENDING-AUDIT.)
- KMU-I Cor. 6.8 prints the slope-0 multiplicity as `r`, clashing with the
  truncation parameter `r` of sec. 7; the proof's own count
  (*"v_pi(Theta~(e^{m_e}_{0,k})) >= 0 for all 1 <= k <= N"*) makes it `N`.
  (`05` sec. 2.3(a), PENDING-AUDIT.)
- KM-ab Prop. 5.5 prints the characterisation of `gamma_i` as
  `E(gamma_n) = zeta_{p^n}^{p^{n-i}}`; since
  `zeta_{p^n}^{p^{n-i}} = zeta_{p^i}`, "`gamma_n`" is a typo for "`gamma_i`"
  and the condition is `E(gamma_i) = zeta_{p^i}`. Only the valuation
  `v_p(gamma_i) = 1/(p^{i-1}(p-1))` is used. (`01` sec. 6a, **CONFIRMED** at
  `20` sec. 4.3.)
- Remark 6.5 says "For `k >= 3`, define `a(k) = ...`" where the analogue of
  Def. 6.3's "`k > p-1`" at `e = 3` would be `k > 3`. Harmless, but it is not a
  perfect textual match to the reconstruction. (`20` Part One sec. 2.3,
  AUDITED-CONFIRMED.)
- **A project transcription slip, not a source defect:** `05` quotes KLW
  Theorem 9.3(a) as "then X descends to `F_p-bar`"; the source says
  "descends to `F_p`". Nothing depends on it (`05` uses 9.3(b) and Thms 1.2 /
  7.6). (`20` P3-11.)

---

# 5. Remaining open items, stated precisely

**(O1) Lemma E, for the full KMU-I contact theory (T2 only).** The sec. 6.2
exact sequence is asserted without proof in KMU-I at every p, for KMU's own
weight (only the `A^dagger` version, Lemma 5.15, is proved there). It is
**not** created by dropping the eigenspace form (sec. 3.5, Remark), and it does
**not** arise on the KM-ab route, so **T1 is untouched**. What is open: prove
it outright, or re-run KMU-I sec. 6.2 and the whole of sec. 7 in KM-ab's
coefficientwise formulation. The second is available in principle but is a
research task -- KMU-I's perturbation machinery (Lemmas 7.1-7.4, 7.11,
Cor. 7.14) is built on the `B^{m_e}` basis and the tuple `m_e` (`20` P3-12).
A third, partially-explored option (`20` P2-6, offered without development):
compare `A^{m,*}` (weight `a`, parameter `m_P`) against `A^{m'}(KMU)` (weight
`a_KMU`, parameter `m'_P = m_P/2`), which also gives a containment since
`a <= 2 a_KMU` for `k >= 4`, relaxing the cap to q-adic `r <= 1/2`
**uniformly in `n`**; whether the rest of the argument survives has not been
checked.

**(O2) The deflation program**, to push the contact tier past the universal
cap. Theorem 4 gives `d(2e) <= 1` for every weight and every odd `e`, so no
tame-index choice helps. The proposed route (coordinator Note 11; **DIARY,
PENDING-AUDIT**, and developed nowhere in this project): the `k = 2e` vector
contributes one explicit near-diagonal entry of valuation exactly 1; strip its
span (and if needed the finite forward orbit) as a **finite-rank correction**,
factor or bound `det(1 - Ms)` as (a small explicit block) x (a deflated
determinant), and run the weight argument on the complement, where `d(k) >= 2`
-type increments become available. The self-loop factor's contribution is
computable in closed form from Theorem 1, and it is where the polygon's own
slope-1/2-type segment should sit. **Status: a proposal, with no proof and no
computation behind it.**

**(O3) The weight theory for general odd `e`.** Theorems 1, 2 and Lemma A are
proved here for **every** odd `e`, and Theorem 4's threshold generalises to
`gamma <= 1/(2e)`. Only Theorem 3's mod-6 case analysis is specific to `e = 3`;
it would have to be redone mod `2e`. Closing this would make the
extension-free variant `e = q-1` usable (sec. 2.2), though the `3 | q-1`
condition is already free.

**(O4) Whether a higher-degree auxiliary map could give `e_P = 3` over a field
with `3 nmid q-1`.** Open; moot, because the base extension is free.

**(O5) The residual audit surface of `05`.** Part Three verified `05`'s
load-bearing content (Lemma B and all its sub-results, the KM-ab dictionary
row 11, Prop. 7.2 / 7.4, sec. 7.2 case (II), rows 15 and 16, the explicit
instance, base-change invariance). What it did **not** do is re-derive the
remaining p-uniformity rows of the 26-row table one by one; it reports them as
"consistent with what I verified". Those rows are **PENDING-AUDIT**, and they
are the only remaining un-audited surface under T1.

**(O6) Sources not verified at source by anyone here:** Deuring-Shafarevich,
Katz-Gabber, Liu-Wei, Elkik, Monsky's trace formula, KM-ab sec. 6's functional
analysis, KMU-I sec. 2-3's functional analysis, and the internal proofs of KLW
and Sugiyama-Yasuda. These are cited as the sources cite them.

**(O7) Matsuda's coefficient estimates** (Duke Math. J. 77(3):607-625, 1995)
could not be fetched (paywalled). Every Matsuda statement in this project is
quoted secondhand from Pulita or Kedlaya and flagged as such in `02`. Nothing
in this document depends on it.

---

# 6. Verification appendix

## 6.1 Machine-verification inventory

**Committed, self-checking artifacts in this repository.** Both assert their
findings and exit **nonzero** on any failure, so the exit status depends on
what the run found, not on the run completing.

| artifact | asserts | command |
|---|---|---|
| `crates/axeyum-cas/examples/noh_u2_matrix.rs` | Artin-Hasse 2-integrality to degree 150; `v_2(pi_1) = 1` and `pi_1 != -2`; `v_2(lambda_m) >= m`; the wild-point lattice certificate `s v_2(M[i][k]) + k - 2i >= 0` for `s = 1,3,5,7,9,11`, `i,k <= 96`; the Dwork trace formula against independently enumerated point counts for `s = 1,3,5,7`, `k <= 6`, each above the stated truncation bound; `v_2(pi_2) = 1/2`, `v_2(lambda^{(2)}_m) >= m/2` | `cargo run --release --example noh_u2_matrix -p axeyum-cas` (~15 s) |
| `crates/axeyum-cas/examples/noh_wt_certificate.rs` | Theorems 1-4 of sec. 3, with minimum examined-pair counts asserted (`pairs >= 400`, `vpairs >= 300`, `la >= 40000`, `cols == 397`) | `cargo run --release --example noh_wt_certificate -p axeyum-cas` (~1 s) |

**Mutation testing of the second artifact** (`20` P2-8, on a standalone
`rustc --edition 2024` build): six mutations, **all exit 1** --
`a(k) -> floor((k-1)/3)` (caught by `(A3) d(5) = 0 < 1`); valuation formula
`+1` (check [2]); `j'(k)` odd branch `-> (k+1)/2` (the ground-truth row
`U_2(t^-3)`); that error injected into both the product and the ODE route
(ground truth **and** check [2]); the same with the ground-truth block deleted
(check [2] alone); and the error injected consistently into product, ODE **and**
valuation (Lemma A's arithmetic, `v_2(c_{2,2}) = 1 < 2`). **The gate is real.**

**One known weakness of that artifact, recorded** (`20` P2-8, wording GAP):
its sec. 0 table calls the ODE recurrence "an independent route", and it is
not -- `c_ode` iterates `c *= (lambda^2 - sub)/((2i+2)(2i+1))`, the
closed-form product in a different association order. Its only binding to the
actual operator `U_2` is six hard-coded ground-truth rows (11 coefficients,
`k in {3..8}`, `m <= 2`). The claim should read "three independent routes",
and the series solve should be added. The pinning is supplied externally by
`20`'s operator and by this workstream's (next table).

**This workstream's own verification** (scratchpad `ws30/`, exact `Fraction`
arithmetic, no floating point; a from-scratch implementation sharing no code
with `01`, `03`, `04` or `20`):

| what | scope | result |
|---|---|---|
| from-scratch series solve of (*) vs Theorem 1 | `e in {1,3,5,7}`, `k <= 16`, all `m` in support (355 pairs) | 0 mismatches |
| `G^e = 1 + 2x^e` exactly (the only use of `e` odd) | `e in {1,3,5,7}` | holds |
| support `subset j'(k) + e Z_{>=0}` | same | holds |
| ground-truth rows of `01` sec. 6b | `k = 3..8` at `e = 3` | reproduced to the last digit |
| Theorem 2 valuation identity | `e in {1,3,5,7}`, `k <= 60`, `m <= 29` | 0 mismatches |
| Lemma A `v_2 >= m` | `e = 3`, `k <= 600`, `m <= 80` | 0 violations; 150 tight pairs, all `k = 2 mod 4, m = 1` |
| Lemma A refinement `>= m + s_2(m)` on `k` odd or `4 \| k` | same | 0 violations |
| Theorem 3 (A3) over the full support | `4 <= k <= 400`, `m <= 259` | 0 violations; minimum at `m = 0` for every `k`; `min d = 1` |
| `d(4..24)`, `d(100)`, `d(200)`, `d(400)` | -- | `1,1,1,1,1,2,1,1,2,3,1,2,3,3,2,3,3,4,3,3,4`; `17`, `33`, `67` |
| control: KMU weight `floor((k-1)/3)` | `k = 5` | `d(5) = 0` reproduced |
| Theorem 4 self-loop `c_{2e,2e}` | `e = 1,3,5,7,9,11,13,15,21` | `= 2` in every case |
| `c_{4e,4e}` | `e = 3,5,7,9,11` | `= 8` in every case |
| Lemma B explicit instance (sec. 3.8.5) | all `q` with `3 \| q-1` | verified by hand: fibre structure, `r_0, r_1, r_infinity`, (8), RH saturation |

All runs completed well inside the 5-minute / 2 GB budget.

**Independent machine work by the auditor**, recorded because it is what makes
the AUDITED-CONFIRMED labels mean something: `20` built its own Type-2
operator from KMU-I sec. 4.3 + 6.1.2 and validated it three ways (the identity
`G^3 = 1+2x^3`; the adjunction `U_2(sigma(t^{-j})) = t^{-j}`; and agreement at
`e = p-1 = 1` with KMU-I Lemma 6.2 = KM-exp Cor. 4.7, **a proved theorem**),
then re-derived Theorems 1-4 against it; and for Part Three it wrote its own
`GF(2^a)` arithmetic for the degree-3 classification and the KM-ab row-15/16
sweeps, and fetched the KLW and SY PDFs itself.

## 6.2 Audit trail: who proved and who audited what

| item | proved by | audited by | status |
|---|---|---|---|
| Charter's obstruction analysis (splitting-function mechanism) | -- | `01` sec. 7, `02` sec. 3.1, coordinator Note 1 | **REFUTED (witness)**: `c_2 = -2`, valuation `1 = 2v(pi)`; and KMU-I sec. 6.1.2 contains no `lambda_i` at all |
| Attack (B): a better splitting function | -- | `02` (ceiling (C1), Lubin-Tate census, negative control) | **DEAD**: no headroom; Artin-Hasse is at the ceiling. `20` sec. 4.1-4.2 **CONFIRMED** the ceiling and every Pulita / Kedlaya quotation |
| Attack (A): Schmidt transplant | -- | `01` sec. 8 | **RETIRED**: Schmidt's operator is the `eta(P)=0` analogue; no target to replace at `eta(P)=1` |
| Identification `3 = e_P` (tame index, not a decay rate) | `01` sec. 4 | `20` Part One sec. 2.1-2.3 | **CONFIRMED and sharpened**: `e = 5,7` do not fit Remark 6.5's shape, so `e = 3` is singled out by KMU's own phrasing |
| The exact global requirement `d(k) >= 1`, `d(k) -> inf` | `01` sec. 3 | `20` Part One sec. 2.5; `20` P3-11 on the KM-ab side | **CONFIRMED**, localized to Lemma 7.11 / KM-ab sec. 7.2 case (II) |
| Wild-point analysis needs nothing new at p = 2 | `02` sec. 3.3, `03` | `20` sec. 1.2, 4.3; `04` row 1; `05` rows 10, 13, 24 | **CONFIRMED** at source: no parity hypothesis anywhere |
| True `U_2` optimum at wild points `= k/s` exactly, with a Fredholm optimality cap | `03` | -- | **PROVED for the truncations**, with external anchors (point counts, L-functions, the supersingular `y^2+y=x^3` case). Not separately re-audited |
| The witness weight `floor((k-1)/3) + (k mod 2)` | `20` Part One sec. 3.3 | -- | found by the auditor; proved admissible by `04` |
| THEOREM 1 (closed form) | `04` | `20` P0-1, P0-2, P2-1; **this file 3.2** | **AUDITED-CONFIRMED** |
| THEOREM 2 (valuation identity) | `04` | `20` P0-3, P2-2; **this file 3.3** | **AUDITED-CONFIRMED** |
| LEMMA A (tail estimate) | `04` | `20` P0-4, P2-2; **this file 3.4** | **AUDITED-CONFIRMED** |
| THEOREM 3 (admissibility, all `k`) | `04` | `20` P0-5, P0-6, P2-3; **this file 3.6** | **AUDITED-CONFIRMED** |
| THEOREM 4 (`gamma = 1/6` exactly) | `04` | `20` P0-7, P2-4; **this file 3.7** | **AUDITED-CONFIRMED** |
| `e`-universality of the self-loop (`c_{2e,2e} = 2`) | coordinator Note 11 | **this file 3.7** | **PROVED HERE**, one line from Theorem 1 |
| Main Lemma / extremal weight `a*` (secondary) | `04` sec. 6 | `20` P0-13, P2-7 | **AUDITED-CONFIRMED** (not used for the headline: `a*` is not integer-valued, sec. 3.6) |
| 18-row KMU-I sec. 6-7 consumption table | `04` sec. 7 | `20` P0-8..P0-10, P2-5 | **AUDITED-CONFIRMED** on every row checkable at source |
| Lemma E coverage claim ("no loss for `r in [0,1]`") | `04` sec. 7.3 | `20` P0-12, P2-6 | **GAP**, AUDITED-CONFIRMED as such; downgraded to `r <= 2^{1-n}` here |
| LEMMA B, all stages and indices | `05` Part 1 | `20` P3-1, P3-2, P3-3; **this file 3.8** | **AUDITED-CONFIRMED** |
| `c^{p-1} = 1` correction (and the KM-exp nuance) | `05` sec. 1.2 | `20` P3-4; **this file 3.8.3** | **AUDITED-CONFIRMED** |
| `3 \| q-1` necessity at degree 3 | `05` sec. 1.4 | `20` P3-5 (own classification and enumeration); **this file 3.8.3** (all four cases) | **AUDITED-CONFIRMED** |
| Base-change invariance of `NP_q`, `HP_q`, `Omega_rho` | `05` sec. 1.4 | `20` P3-6; **this file 3.9** | **AUDITED-CONFIRMED**, plus one unstated hypothesis (nontriviality of `rho'`) now stated |
| Explicit Lemma-B instance | `05` sec. 1.5 | `20` P3-7 (symbolic and numeric); **this file 3.8.5** | **AUDITED-CONFIRMED** |
| `e = q-1` fallback | `05` sec. 1.8 | `20` P3-8 | **AUDITED-CONFIRMED as geometry**, with the "not a drop-in" caveat |
| KM-ab weight/operator dictionary (row 11) | `05` sec. 2.2 | `20` P3-10 | **AUDITED-CONFIRMED** -- the chain is not severed |
| KM-ab rows 7, 21, 25, sec. 7.2 case (II), sec. 7.3 | `05` sec. 2.2 | `20` P3-9, P3-11 | **AUDITED-CONFIRMED** at source |
| KM-ab rows 15, 16 (two source defects) | `05` | `20` P3-12, P3-13 (own sweeps) | **AUDITED-CONFIRMED**, with the true bound `(p-1)a(a+1)/2` supplied |
| "Lemma E does not arise on the KM-ab route" (hence T1 uncapped) | `05` sec. 2.3(b) | `20` P3-10, P3-12 | **AUDITED-CONFIRMED** -- Part Three calls it "05's best result ... states almost in passing" |
| remaining p-uniformity rows of the 26-row table | `05` sec. 2.2 | -- | **PENDING-AUDIT** (sec. 5, O5) |
| KLW Thm 1.2 / 7.6, SY Thm 1.1 quotations | `05` (fetched) | `20` Part Three (fetched independently) | **CITED, two independent fetches** |

## 6.3 What is new versus what is repackaged

**New, as far as this project can tell.**

- The closed form (Theorem 1) for the Type-2 transition coefficients at p = 2,
  for every odd tame index. The literature's statement is KM-exp Cor. 4.7 for
  `R = Z_p, pi = p` (i.e. `e = 1`), cited by KMU-I Lemma 6.2 and by KM-ab
  Prop. 4.2; the general-`e` hypergeometric form appears nowhere in the fetched
  sources.
- The valuation identity (Theorem 2) and Lemma A.
- The repaired weight `floor((k-1)/3) + (k mod 2)` and its admissibility for
  all `k` (Theorem 3) -- hence the repair of the estimate KMU-I Remark 6.5
  calls too low.
- The exact sharpness constant (Theorem 4): `gamma = 1/6`, certified by one
  coefficient, with the cap `d(2e) <= 1` universal in `e`.
- Lemma B: the `e`-power replacement for KMU's `(p-1)`-power stage, and with it
  the characteristic-2 instance of Prop. 4.3 / KM-ab Lemma 3.1.
- The four literature corrections of sec. 4.1-4.4, and the two proofs the
  sources assert without giving (base-change invariance, sec. 3.9; the
  feasibility of KM-ab (18), sec. 4.4).

**Repackaged, or classical, and cited as such.**

- `(L1)`, "`v(lambda_i) >= i v(pi)` for the Artin-Hasse splitting at every p":
  one line from Dwork-Dieudonne integrality, and *exactly* the argument KM
  already use -- KM-ab sec. 5.2.2 closes with "Since `E(x) in Z_p[[x]]`, it is
  clear that `E_r in O_L[[pi_s t^{-1}]]`". No leverage.
- The absence of a p = 2 loss in the splitting function at any Witt length:
  *stated in the literature* -- KMU-II Lemma 3.5 and Thm 3.6 carry no parity
  hypothesis, and KM-ab Prop. 5.5's `E_r` is a literal product of rank-one
  Artin-Hasse factors with no cross terms. The project's numerics confirm it;
  they do not establish it.
- The ceiling on splitting-function decay rates: exact and classical
  (Kedlaya Thm 19.4.1; Thm 12.6.4 = Christol-Mebkhout; Pulita Prop. 2.12;
  Robba's necessity). Uniform in p.
- Newton-over-Hodge at p = 2 on `P^1` and on affinoids: published (sec. 1.1).
- Everything in KM-ab, and in KMU-I sec. 2-5, 7, outside the two repaired
  places: cited verbatim.

**Honest framing of the whole.** This is a *repair of one local estimate plus
one geometric construction*, slotted into an existing global argument. The
global machinery is entirely Kramer-Miller's and Kramer-Miller--Upton's. What
this project adds is small in volume and load-bearing in position: it is
exactly the pair of pieces their own papers name as missing (KM-exp sec. 1.4:
"some estimates in section 4 must be modified" and "not immediately clear that
we can find a cover eta").

## 6.4 The error ledger

A record of what this project got wrong, including the coordinator's own
self-corrections. This is part of the evidence, not an appendix to it: the
headline rests on estimates that were wrong several times before they were
right.

**The coordinator's four self-corrections.**

1. **The charter's obstruction mechanism was wrong** (Note 1, self-corrected
   within hours). The charter claimed `AH(pi x)` has *unit* coefficients at
   degrees 2 and 4 at p = 2 (from `pi^2/2 = -1`, `pi^4/4 = 1`), "the exact
   source of `a(k) = floor((k-1)/3)`". Both halves are false: those units live
   in the **exponent** and cancel against `1/2!`, `1/4!` (witness:
   `lambda_2 = -2`, valuation `1 = 2v(pi)`); and the derivation of `a(k)`
   contains no splitting function at all, because at `eta(P) = 1` the point is
   not in `S` and `E~_P` is a constant. The whole of attack (B), and the
   charter's framing of the problem as Dwork-analytic, followed from this error.
2. **The `pi`-normalisation, wrong twice.** Note 4's degree-32 table used
   `pi^2 = -2`, the **order-4** Dwork `pi`, not the order-2 one (corrected in
   Note 6). Note 6 then asserted `pi = -2` for order 2; Note 8 corrected the
   identification again, and `20` sec. 5.3 **refuted `pi = -2` outright with a
   witness**: the splitting parameter must satisfy `AH(pi) = -1`, and
   `AH(-2) = 1 mod 4` while `-1 = 3 mod 4`. The load-bearing content (rate 1 at
   order 2, rate 1/2 at order 4) survived all three passes; the identification
   of the object did not.
3. **Note 7's explicit cost matrix was fabricated structure.** The coordinator
   derived `v_2(c_{k,j}) = m + v_2(binom(-k/3,m))` with `m = 2|j-k|/3` and built
   an LP-duality proof strategy on it. Both formulas are **REFUTED with
   witnesses**: the first is right for `k = 4` (`0,3,3`) and wrong for `k = 5`
   (predicts 1 at `m = 1`; the truth is 3) and for `k = 7`; the second is not
   even an integer (`k = 4, j = 5` gives `2/3`). The true structure is
   hypergeometric (Theorem 1). Note 7's *conclusion* -- that the LP-minimal
   weight is a shortest-path potential -- survived and was identified in closed
   form.
4. **Attacks (A) and (B) of the charter were both retired**, (A) because
   Schmidt's bigraded module has no target to replace at `eta(P) = 1`, (B)
   because Artin-Hasse is already at the theoretical ceiling. Two of the
   charter's four attack lines were aimed at objects that do not appear in the
   broken estimate.

**Workstream errors caught by the adversarial verifier.**

- `01`'s headline "the entire `p >= 3` hypothesis of KMU-I is the local
  estimate ... **Nothing else**" -- **GAP**. `p >= 3` is also consumed in
  sec. 4.1 (Fulton, and the `(p-1)`-power map that degenerates). `01`'s own
  body flagged this as caveat (iii); the headline contradicted it. This is why
  Lemma B exists as a named prerequisite.
- `01`'s "Riemann-Hurwitz forbids `e_P = 1`" -- **GAP**, needs a genus
  qualifier (witness in sec. 3.8.4).
- `01`'s "none of the obvious closed-form weights work" -- **FALSE**; the
  auditor found one on the second try, and it is KMU's own weight plus an
  indicator. That witness became Theorem 3.
- `01`'s (A1)-(A3) as "the complete constraint set" -- **GAP, benign**: (A4)
  and (A5) were missing, both verified satisfied. The feared failure mode
  (feasible only because a constraint was omitted) is **excluded**.
- `02`'s Table B is labelled as measuring KM-ab's `E_r` -- **GAP**: it measures
  `prod_i AH(pi^{p^i} x^{p^i})`, a different object. The verdict (no
  Witt-length loss) survives on the literature quote, which is what carries it.
- `04`'s Lemma E coverage claim -- **GAP**, the one substantive finding of the
  priority-0 audit; downgraded in this document (sec. 2.3).
- `04`'s "four independent routes" -- **wording GAP**: R4 is not independent of
  R2 (sec. 6.1).
- `05`'s dependency graph repeats 04's pre-correction "`r in [0,1]`" --
  **GAP (inherited)**: `05`'s reading list stopped at Part One, so Part Two's
  correction was not absorbed. Corrected in sec. 2.5. It does not touch T1,
  whose route has no cap at all.
- `05`'s KLW Theorem 9.3(a) quotation ("`F_p-bar`" for "`F_p`") --
  transcription slip; nothing depends on it (sec. 4.6).
- The feasibility threshold was reported three times before it was right:
  `01` measured `[1/6, 1/5)`, `20` sharpened it to `[1/6, 2/11)`, and `04`
  **proved** it is the single point `1/6` -- whereupon `20` retired its own
  interval. Only the last is a theorem.
- A cosmetic disagreement worth not burying: `05` counts 8 degree-3 auxiliary
  maps per admissible field, `20` counts 6 (parametrisation of the Mobius
  factor). The load-bearing outputs -- existence pattern and `alpha` set --
  agree on every field (sec. 3.8.3).

**Charter-level bibliographic corrections** (all by `02`, **CONFIRMED** by
`20` sec. 4.2): Pulita is arXiv:**math/0612725**, not math/0602627 (that id is
a combinatorics paper); Matsuda is **1995**, "coverings", not 1997,
"extensions"; at `p >= 3` KMU's rate is `floor((k-1)/(p-1))`, **not**
`floor((k-1)/2)` (that is the `p = 3` instance); and `Q_2(sqrt(-2))` does
**not** contain `zeta_4`.

**Parent-project correction, carried here for the record.** The claim that
"Newton-over-Hodge at p = 2 sits outside every published hypothesis" was
**withdrawn** by the parent project's own novelty check
(`ac-bridge-2026-08/24-novelty-check.md`): Liu--Wan Theorem 5.2 carries no
hypothesis on p, Schmidt's affinoid paper carries none, and Zhu covers p = 2
with odd pole orders. The accurate residual statement -- what this document
addresses -- is the **arbitrary-curve, Swan-local** case of the
Kramer-Miller(--Upton) framework. Nothing here should be read as a claim about
`P^1`.

## 6.5 Reproduction

```sh
cargo run --release --example noh_u2_matrix      -p axeyum-cas   # ~15 s, self-checking
cargo run --release --example noh_wt_certificate -p axeyum-cas   # ~1 s,  self-checking
```

Session-scratchpad scripts, not committed: `ws30/op.py` (from-scratch series
solve of (*) and the Theorem-1 binding), `ws30/fast.py` (Theorems 2-4,
Lemma A, the (A3) sweep, the self-loop census). Workstream scratchpads named
in the diaries: `01`'s `updwork.py`, `type2_e.py`, `lp2.py`; `02`'s `ah.py`,
`l1.py`, `lt.py`, `ltgen.py`, `more.py`, `dens.py`, `run2.py`; `04`'s `op.py`,
`closed.py`, `sym.py`, `lp.py`, `astar.py`, `mainlemma.py`, `a20.py`; `05`'s
`gf.py`, `deg3b.py`, `compose.py`; `20`'s `code/u2.py`, `checks.py`, `lp*.py`,
`closed.py`, `witness.py`, `ah.py`, `misc.py`, `tail.py`, `audit04.py`,
`audit04b.py`, `audit05.py`, `inst.py`, and `rs/` (the standalone certificate
build plus six mutants). PDFs fetched: KMU-I, KMU-II, KM-exp, KM-ab, Schmidt,
Pulita, Kedlaya's book (by `01`, `02`, `04`, `05`, `20`), KLW and SY (by `05`
and `20` independently).

---

## 6.6 Provenance and reconciliation

This artifact was assembled from `00-charter.md`, `01`-`05`, the coordinator's
notes (`10-notes-coordinator.md`, Notes 1-11), `20-verify.md` **Parts One,
Two and Three**, and the parent-project context file
`ac-bridge-2026-08/24-novelty-check.md`. Part Three (the audit of `05`) landed
during the write-up and was read in full before this file was finalised; it
**upgraded** Lemma B and all its sub-results, base-change invariance, the
explicit instance, the `e = q-1` fallback, the KM-ab dictionary and the KM-ab
load-bearing rows from PENDING-AUDIT to AUDITED-CONFIRMED, and it established
that **T1 carries no truncation cap** because Lemma E does not arise on the
KM-ab route. It also recorded one new GAP (`05`'s inherited "`r in [0,1]`",
corrected in sec. 2.5) and one transcription slip (sec. 4.6). Nothing it marks
GAP or FALSE is presented here at a stronger label than it gives.

Items still carrying **PENDING-AUDIT** after Part Three, and therefore the
only un-audited surface under T1: the non-load-bearing p-uniformity rows of
`05`'s 26-row KM-ab table (sec. 5, O5), the two minor KMU-I textual defects of
sec. 4.6, the deflation proposal of sec. 5 (O2), and the parent project's
citation-graph sweep quoted in sec. 1.1. `31-writeup-log.md` records the
decisions, the label changes and their timestamps.
