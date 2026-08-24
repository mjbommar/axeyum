# Novelty verification (triple-check), 2026-08-20

Method: (1) internal prior-art grep over the lane ledger and canonical note;
(2) arXiv API queries via WebFetch; (3) arXiv full-text search UI via
WebFetch, with a positive control query confirming the interface returns
known results. WebSearch was session-exhausted (200/200) before this pass;
MathSciNet/zbMATH not accessible. A demonstrated phrase-miss (Hast–Matei
1604.02067 is known to us by direct fetch but is NOT returned by the topical
arXiv searches) means every "no results" below is a WEAK negative only.

## Verdict per headline claim of 30-paper-draft.md

1. **kappa_3 supersingular period-24 theorem (diary 21): NOT NOVEL.**
   External priors found:
   - Gorodetsky, "Irreducible polynomials over F_2^r with three prescribed
     coefficients" (arXiv:1805.07105): proves the period-24-in-n phenomenon
     for these counts in characteristic 2, tied to supersingular curves and
     cyclotomic function fields.
   - Ahmadi–Gologlu–Granger–McGuire–Yilmaz, "Fibre products of
     supersingular curves and the enumeration of irreducible polynomials
     with prescribed coefficients" (arXiv:1605.07229): makes explicit why
     the formulae have period 24 in n.
   The lane's ledger also already imported "Gorodetsky's exact
   characteristic-two period-24 theorem" (canonical note line ~3131).
   Status: our sup_n kappa_3 = 2 is at best a corollary/repackaging; the
   artifact must cite both papers and drop any novelty claim here.
2. **Sibling-difference / ell-freeness identification (diary 21): INTERNAL
   REDISCOVERY, sharpened.** The ledger already reconstructs endpoint
   populations from "signed sibling differences in the binary Witt quotient
   tree" with a Haar triangle (landed 2026-08-19, `039d905a6`), and H_j^*
   is a pre-existing ledger object (ADR-0517 value reproduced). New here:
   the exact normalization D_[j](e) = Delta_j(pi_j e)/2^(ell-j+1) and the
   consequent (j,n)-only dependence. Incremental, claim accordingly.
3. **Conductor-grading orthogonality of the cell tensor (Wick = 3 M_2^2
   exactly) + parity selection rule + 1/4-per-level recursion (diary 11):
   NO EXTERNAL PRIOR FOUND** ("exact conductor" x "character sums": zero
   arXiv hits; conductor/wavelet/moment-ratio filtration queries: zero).
   Internally, exact-conductor Fourier inversion existed (`9c146dcc9`) but
   not the orthogonality-of-the-fourth-moment-grading, the parity rule, or
   the recursion. Status: plausibly novel as a package; mathematically
   elementary once stated; claim as a framework contribution, weak-negative
   caveat attached.
4. **q_j product identity R_0 = prod(1+q_j) with 0 <= q_j <= 1 (diary 13):
   the identity is elementary martingale/filtration algebra** (ratio of
   successive filtered second moments); we found no prior application to
   character-family fourth moments (weak negative), but the honest claim is
   the APPLICATION and the proved bounds, not the identity.
5. **(SUP-L) reduction theorem (diary 11, verified):** novel as far as
   found (weak negative), but its hypothesis is REFUTED (diary 21) — value
   is historical/structural. State as such.
6. **(TOP-POLY) and (CDL')/(VAR-EQ) pricing (diaries 21, 22): the genuinely
   new content of this project.** The fourth-moment-at-fixed-q territory is
   essentially unpublished: arXiv searches for fourth/higher moments of
   prime-polynomial counts in short intervals return zero (weak negative);
   the nearest published objects are Hast–Matei 1604.02067 (tame, p > n,
   ineffective constant), Gorodetsky 1810.00483 (vacuous at h ~ n/2),
   Yiasemides 2110.05959 (divisor second moments, Hankel), Keating–Rudnick
   (q -> infinity). Diary 22's targeted search for its (CDL) object found
   nothing at any q. The precise pricing — endpoint <=> one factor of ell
   over proved bounds, at either end of the conductor filtration — appears
   to be new.
7. **Lemmas A/B, D1–D4/D2, E_1 = 0, tau functional equation:**
   problem-specific; translation/reciprocal involutions are standard
   tricks; claim as new-in-context only.

## Required artifact edits (applied)

- Cite arXiv:1805.07105 and arXiv:1605.07229 at the kappa_3 material and
  withdraw novelty there.
- Point section 6.4 at this file; keep the global novelty status
  "externally unverified beyond weak negatives" until a full
  MathSciNet/zbMATH pass is possible.

## Correction (2026-08-20, late): Newton-over-Hodge at p=2 is NOT open

Deeper pass with SerpAPI (Google Scholar) + full-text PDF verification,
prompted by the owner's challenge. Result: the coordinator's claim that
"Newton-over-Hodge at p=2 sits outside every published hypothesis" is
FALSE as stated, and is hereby withdrawn.

- **Liu--Wan, "T-adic exponential sums over finite fields" (Alg. & Number
  Theory 3 (2009), arXiv:0802.2589), Theorem 5.2**: `NP_T(f) >= HP_q(Delta)`
  — verified from the PDF to carry **no hypothesis on p at all**. The
  T-adic Hodge bound specializes to every additive character of every
  p-power conductor, p = 2 included. Their Section 2 states it "extends,
  in one stroke, all known ordinariness results for psi of order p to all
  psi of any p-power order."
- **Haessig (arXiv:2606.10041, 2026)**: partial T-adic Newton-over-Hodge,
  setup "Let p be a prime" — no parity restriction found in the full text.
- **Davis--Wan--Xiao (arXiv:1310.5311)**: full-text grep finds **no "p odd"
  hypothesis**; their tower needs gcd(d,p) = 1, satisfied by the odd
  monomial directions of the Carlitz tower at p = 2. So even the SHARP
  large-conductor arithmetic-progression slope structure is plausibly
  published at p = 2 on each odd-monomial Z_2-line.
- **Blache (several papers, 2008-2015) and Scholten--Zhu** explicitly treat
  p = 2 first slopes and generic Newton polygons for order-p Artin--Schreier
  sums; char-2 hyperelliptic Newton polygons likewise.

The accurate residual statement: the `p >= 3` exclusions verified by the
p-adic sweep agent belong to the **Kramer-Miller(--Upton) curve-local
framework** (general curves, Swan-local Hodge polygons) — the sweep agent
reported this correctly, and the coordinator over-generalized it to the
whole field. For OUR family (P^1, one wild point, monomial directions),
the inequality is covered by Liu--Wan at p = 2, and the useful-to-others
divisibility consequences already flow from that theorem.

What plausibly remains ours, now correctly scoped (all THIN, remark-grade
until checked against Liu--Wan/DWX machinery): the exact ordinarity of
levels 2/4/8 for the full mixed-character Hayes family, the lattice-forced
min-slope law across mixed characters (multi-coordinate, so outside the
single-Z_2-line DWX setting; possibly reachable from Liu--Wan n-variable),
the NP-equals-rounded-Hodge counterexample, and the 32,766-character exact
verification data set. None of this supports a standalone-paper claim.

Consequently the project's strongest broadly-novel mathematics reverts to:
(1) the Betti no-go theorem (proved), (2) the (TOP-POLY)/(VAR-EQ) endpoint
pricing (proved), (3) the composition classification (proved). The NoH@p=2
item is downgraded from "most impactful discovery" to "evidence set +
possible remark, pending a derivability check against Liu--Wan".

## Second reconciliation (2026-08-20, latest): external review cross-check

An independent external review (owner-supplied, ChatGPT) of the NoH@p=2
landscape agrees with the withdrawal above and refines the map. We verified
its two key additions first-hand:

- **KMU arXiv:2110.08656, Remark 6.5 — verified verbatim from the PDF**:
  at p = 2 their lattice estimate degrades to `a(k) = floor((k-1)/3)` and
  is "too low for applications to the global setting" (spurious slope-zero
  segments, e.g. `a(5) - a(4) = 0`). The paper's standing hypothesis
  "Let p be an odd prime" also verified at source. So the p = 2 exclusion
  in the curve-local framework is a *specific analytic obstruction in the
  Dwork-lattice estimate*, not an un-attempted case — the char-2 Belyi/tame
  map ingredient exists (Kedlaya--Litt--Witaszek).
- **Zhu (IMRN 2004), "L-functions of exponential sums over one-dimensional
  affinoids: Newton over Hodge"** — existence and scope confirmed via
  Scholar: sharp Hodge lower bound on P^1-affinoids for any prime with
  p coprime to the pole orders, i.e. p = 2 with odd pole orders. This
  citation was missing from the first correction pass and strengthens it.
- Adjacent live char-2 work: Booher--Groen--Kramer-Miller (arXiv:2511.02733)
  moves to Ekedahl--Oort/Dieudonne invariants of Z/2-covers rather than the
  full 2-adic Newton polygon — the arbitrary-curve p = 2 gap is live, not
  merely historical.

**Placement of our data, final**: the Carlitz-tower computations live over
base P^1 — the column where the bound is published (Zhu on P^1; Liu--Wan
T-adic for 2-power conductors; DWX odd-monomial lines). They cannot support
the genuinely-open claim, which requires an ARBITRARY smooth affine base
curve with the Kramer-Miller ramification-defined sharp polygon, overcoming
the Remark 6.5 lattice loss. One modest, defensible use of our material:
the 32,766-character exceptionless data set, the exact ordinarity of levels
2/4/8, and the rounded-Hodge counterexample constitute *evidence, in the
P^1 higher-conductor corner, that no p = 2 pathology of the Remark-6.5 type
is visible in actual Newton polygons* — potentially useful to the
Kramer-Miller school as a data point, i.e. an email or short note, not a
paper. Verdict unchanged: no standalone novelty claim for NoH@p=2.

## Citation-graph sweep (2026-08-20, SerpAPI Scholar, cited-by since 2023)

Citers of Zhu 2004 (4), KMU-I (5), KM abelian-Artin (3). Complete recent
neighborhood:
- Schmidt, "T-adic exponential sums over affinoids" (JNT 2023,
  arXiv:1901.05516): "Let p be a prime" — no parity hypothesis; Hodge bound
  for p^k-order sums of one-variable rational functions over affinoids.
  Confirms the P^1/affinoid column is closed at ALL p, higher conductors
  included.
- Ito--Takeuchi--Tsushima, "Gauss--Heilbronn sums and coverings of
  Deligne--Lusztig type curves" (arXiv:2512.11288, Dec 2025): exponential
  sums on Witt vectors realized as Frobenius traces of DL-type curves —
  but **3-typical, length two** (p = 3), and determines SLOPES. The same
  trio's Heisenberg paper was already equation-audited by the lane. A
  future 2-typical version would be the item to watch.
- Booher--Cais (Iwasawa for p-torsion class schemes, char p);
  Booher--Hsieh--Rivera--Tran--Upton (higher a-numbers via lattice points);
  Booher--Groen--Kramer-Miller (EO types of Z/2-covers, char 2); Dang
  (deforming cyclic covers); KMU-II; D. Schmidt thesis (EO/NP algorithms).

Reading of the graph: the active school (Booher/Cais/Kramer-Miller/Upton +
ITT) is uniformly on p-adic and mod-p invariants; nobody in the citation
neighborhood works on archimedean family cancellation. Two conclusions:
(1) the arbitrary-curve p = 2 Newton-polygon gap is live and unclaimed —
consistent with the external review; (2) NOTHING in this line bears on the
Lemire missing piece, which is archimedean: every theorem here controls
2-adic valuations, the valuation route to the endpoint is closed with
witnesses (supersingularity unique and refuted; needed v_2 = ell+1 vs
lattice-forced small slopes), and Zhu's sharpness makes the smallness of
the available divisibility PROVABLE — the literature hardens the closure
of the 2-adic route rather than reopening it. Haessig's partial sums are
structurally adjacent to (CDL) but carry T-adic valuation content, not
second-moment archimedean content.
