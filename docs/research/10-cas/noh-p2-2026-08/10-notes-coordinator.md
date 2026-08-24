# Coordinator notes (own work)

## Note 1 (2026-08-20): the charter's obstruction analysis was WRONG, and
## the correction suggests the local estimate may be elementary

Charter claimed: AH(pi x) at p = 2 has unit coefficients at degrees 2, 4
(from pi^2/2 = -1, pi^4/4 = 1 in the exponent). SELF-CORRECTION: those unit
terms live in the EXPONENT, not in the coefficients of theta. Direct check:
lambda_2 = pi^2/2 + pi^2/2! = -1 - 1 = -2, valuation 1 = 2 * v(pi). The
units cancel inside the exponential.

**Lemma-candidate (L1), with proof sketch.** For every prime p, including
p = 2: the Dwork-Artin-Hasse splitting theta(x) = AH(pi x) satisfies
    v(lambda_i) >= i * v(pi)   for all i,
where AH(x) = prod_{(n,p)=1} (1 - x^n)^{-mu(n)/n}.
Proof sketch: each factor (1 - pi^n x^n)^{-mu(n)/n} is a binomial series
with exponent -mu(n)/n in Z_p (n coprime to p), so its x^{nk}-coefficient
is (Z_p-integral) * pi^{nk}, valuation >= nk * v(pi). The product of series
each satisfying v(coeff of x^d) >= d*v(pi) satisfies the same. QED (to be
adversarially checked: integrality of the binomial coefficients, the
rearrangement of the infinite product, and equality of AH(pi x) with the
product formula over Z_p[pi]).

Consequence if (L1) holds: the per-degree decay rate at p = 2 is v(pi) =
1/2 — NOT 1/3 — and is p-UNIFORM in the normalization v(pi_chi) = 1/(p-1)
p^{1-m} for order-p^m. The floor((k-1)/3) of KMU Remark 6.5 then likely
comes from using a short splitting exp(pi(x - x^p))-type (classical rate
(p-1)/p^2 = 1/4..1/3-ish at p=2) or from the Witt-length >= 2 cross terms
— workstream 01 must locate which. If their construction is rerun with the
product-formula bound, the certified a(k) should improve to ~floor(k/2).
THE REAL FRONTIER is then Witt length m >= 2: the splitting for
higher-order characters is a product over ghost/phantom components, and
the p = 2 loss, if genuine, lives in the cross terms. Priority question
for 01/02/03.

## Note 2: the even-part commutation trick (second tool)

psi (Dwork's U_2 on series) satisfies psi o M_{B(x^2)} = M_{B(x)} o psi
exactly, for any series B. Hence ANY integral factorization
theta(x) = A(x) * B(x^2) yields M := psi o M_theta = M_B o (psi o M_A),
and since M_B is integral with unit diagonal (B(0)=1), the Hodge-type
lower bound for det(1 - Ms) is governed by A's decay alone; the even part
B rides free. So one does not need the optimal splitting function — only
an integral odd/even factorization with a fast A. Candidate: take B(x^2)
:= the product of the (1 - pi^n x^n)^{-mu(n)/n}-derived even-degree
content... (to develop; at minimum this gives a second, independent route
to improving a(k), and it is exactly the kind of restructuring a
(pi,p)-bigrading formalizes.)

## Note 3: falsifiable predictions handed to the workstreams

P1 (to 02): computed v(lambda_i) of AH(pi x) at p = 2 will be >= i/2 with
equality infinitely often (rate exactly 1/2).
P2 (to 03): the true operator profile a_true(k) at m = 1 will support
floor(k/2)-type rates on the plain monomial basis after diagonal
rescaling; no exotic lattice needed at m = 1.
P3: any genuine p = 2 loss will first appear at Witt length m = 2, in the
cross terms of the two-level splitting.

## Note 4 (2026-08-20, later): (L1) numerically CONFIRMED by the coordinator

Exact computation over Q(pi)/(pi^2+2) (rational arithmetic, exp via the ODE
recurrence, degrees 0..32; script in session scratchpad noh2/): every
coefficient of AH(pi x) satisfies v(lambda_i) >= i/2, with EQUALITY at
i = 0,1,2,5,7,9,12,13,16,22,24,28 — the true decay rate at p = 2 is
exactly 1/2 = v(pi), matching the product-formula argument and beating the
1/3-type rate behind Remark 6.5's a(k) = floor((k-1)/3). Status of (L1):
numerically confirmed through degree 32; proof sketch pending adversarial
check (workstream 02 charged). Consequences: at Witt length m = 1 the
local estimate likely repairs to ~floor(k/2) immediately; the open heart
of the arbitrary-curve p = 2 theorem is (i) confirming their global glue
consumes only this rate (workstream 01), and (ii) the m >= 2 Witt
cross-terms (P3). This is the project's first concrete step past
Remark 6.5.

## Note 5 (2026-08-20): workstream 02 verdicts absorbed — program refocused

- Attack (B) DEAD: ceiling (C1) proved (no splitting beats v(pi_M); AH
  attains it; Lubin-Tate freedom empty). (L1) true but classical — KM/KMU
  already use AH integrality.
- P1 CONFIRMED (rate 1/2 exactly). P3 REFUTED with witness: no Witt-length
  loss; rate exactly v(pi_m) at m = 1,2,3; KMU II Lem 3.5/Thm 3.6 carry no
  parity hypothesis.
- Note 1's mechanism was aimed at the wrong object: floor((k-1)/3) is the
  WEIGHT EXPONENT on a U_p-stable basis; denominator = ramification index
  of the auxiliary tame Belyi map over 1 (p-1 at odd p, degenerate at
  p = 2, fallback 3). Required functional identity: a(pl+r) - a(l+r) = l;
  at p = 2 the natural weight a(k) = k-1 satisfies it and the fallback
  a(k) = floor((k-1)/3) does not (a(5) - a(4) = 0).
- Corrections recorded: Pulita is arXiv math/0612725v2; at p >= 3 KMU's
  rate is floor((k-1)/(p-1)) (not /2); Q_2(pi) with pi^2 = -2 does not
  contain zeta_4.

REFOCUSED PROBLEM (the whole gap in one line): construct a U_2-stable
filtered lattice on the local module with weights satisfying
a(2l+r) - a(l+r) = l at p = 2 — equivalently repair the degenerate
tame-geometry normalization at p - 1 = 1. Candidate tools: Note 2's
even-part commutation (build the stable basis from an odd/even
factorization); an auxiliary tame cover of index e chosen so the weight
increment survives (needs 01's extraction of exactly how e enters); or a
direct lattice search on 03's computed matrices (a(k) = k-1 is now the
target profile to search for, not floor(k/2)).

## Note 6: pi-normalization correction (coordinator's own error, caught in
## re-derivation)

Note 4's degree-32 table used pi with pi^2 = -2 (v = 1/2), which is the
ORDER-4 (M = 2) Dwork pi — matching v(zeta_4 - 1) = 1/2 and the (C1)
ceiling 1/2^(M-1) at M = 2. The order-2 character (M = 1) has
pi^(p-1) = pi = -2, v(pi) = 1, and the product-formula argument gives
coefficient rate 1 there. So the analytic budget at p = 2 is: rate 1 at
M = 1, rate 1/2 at M = 2 — exactly the ceiling, attained by AH, at every
level; consistent with 02's finding that the splitting side is optimal and
closed. All remaining tension is in the U_2-stable-lattice / tame-map
geometry, i.e. the weight-increment identity a(2l+r) - a(l+r) = l.

Held question for 01 (do not speculate past extraction): in KMU's linear
algebra, is the increment identity a ROW-valuation requirement at the
near-diagonal entries j in {0,1} (where lambda-decay contributes nothing,
so the increment must come from the weights alone), and does the p-1
denominator at odd p enter through the auxiliary tame cover's index or
through the Hodge-slope normalization i/s? The answer determines whether
the p = 2 repair is a new lattice (attack C) or a new auxiliary cover.

## Note 7 (2026-08-20): coordinator derivation — explicit cost matrix and
## the LP-duality proof strategy for the repaired weight

From 01 section 2b: at p = 2, e_P = 3 the tame-point Frobenius is
sigma(t) = ((t^3+1)^2 - 1)^(1/3) = t^2 (1 + 2 t^(-3))^(1/3). Binomial
expansion gives explicit transition costs
    v_2(c_{k,j}) = m + v_2(binom(-k/3, m)),   m = 2|j-k|/3,
on edges with 3 | (j - k) (direction convention to be fixed against the
source; -k/3 in Z_2 since 3 is a unit; valuations computable by Kummer's
theorem = carry-counting in base-2 addition of 2-adic integers).

Consequences:
1. 01's LP-minimal weight IS the shortest-path potential of this digraph
   from the base region k <= mu(P) = 3; its irregular values (19/6, 7/3,
   ...) are path minima, not a formula to guess.
2. By LP duality, proving (A3) for ALL k with d(k) >= max(1, k/6) reduces
   to exhibiting ONE dual certificate phi(k) = alpha k + beta_{k mod M}
   (M = 6 or 12) with phi(k) - phi(j) + v_2(c_{k,j}) >= the required
   increment on every edge: a finite check per residue class plus an
   induction, since the cost grows with slope 1 in m while |j - k| =
   3m/2. This converts workstream 04's task from weight-hunting to
   certificate-exhibiting.
3. Open risks tracked: 01's caveats (ii) (exact sequence for
   non-eigenspace weights — must become a lemma), (iii) (the 3-power
   Belyi modification at p = 2), (iv) (global count with e_P = 3). These
   are the remaining substance of the theorem-candidate beyond the
   certificate.

## Note 8 (2026-08-20): workstream 03 absorbed; Note 6 corrected again

- 03: wild-point optimum at p=2 is a_true(k) = k/s EXACTLY (no floors),
  attained by the integral diagonal lattice pi^{2k} t^k at s=1; optimum
  proved (Fredholm similarity-invariant cap); increment identity met
  exactly; m = 2 identical (P3 refuted a second time, now with genuine
  Witt arithmetic). Dwork trace anchored against point counts, m = 1 and 2.
- pi-normalization, third pass: at p=2, m=1 the Dwork pi is the root of
  E_2(x) = -1, in Z_2, v_2 = 1 (not -2; v(E_2(-2)+1) = 2). Note 6's rate
  claim stands; its identification of pi was imprecise.
- THE REMAINING RISK REGISTER for the theorem-candidate, complete:
  (R1) the tame-auxiliary dual certificate (04, in flight);
  (R2) strict-vs-nonstrict slack consumption in KMU sections 6-7 — the
       p=2 optimum has zero multiplicative slack (03's caution; sent to 04);
  (R3) the exact sequence for non-eigenspace weights (01 caveat ii);
  (R4) the 3-power Belyi modification at p=2 (01 caveat iii);
  (R5) global count N with e_P = 3 (01 caveat iv);
  (R6) the audit of the load-bearing extraction itself (20, in flight).

## Note 9 (2026-08-20): audit absorbed — the theorem-candidate's final shape

Audit verdicts (20-verify.md): two breaks, both absorbable; constraint set
complete (feared subset-artifact failure mode excluded); all numerics
reproduced.

The theorem-candidate now has exactly this shape:
- THEOREM (NoH at p=2, arbitrary smooth affine curve, 2-power characters,
  KM ramification-defined Hodge polygon), proof =
  - KMU verbatim: wild-point estimate (Prop 6.1), global glue (sections
    5-7, consumption localized at Lemma 7.11), KM-ab Prop 5.5 splitting;
  - NEW LEMMA A (weight): a(k) = floor((k-1)/3) + (k mod 2) is admissible
    ((A1)-(A5)) and d(k) >= 1 for all k >= 4 with d(k) -> infinity —
    reduces to one mod-6 identity + a tail bound on v_2(c_{k,j})
    (verified on [4,100] full support by the auditor); status: to prove
    (04 in flight);
  - NEW LEMMA B (geometry): a char-2 tame Belyi-type map with e_P = 3
    over 1 — Sugiyama-Yasuda (extending Fulton to p=2, per KMU Rem 4.2)
    composed with a 3-power map; status: to prove or state as a precise
    hypothesis (04 in flight);
  - RESIDUAL RISKS: R2 (strict-slack consumption at p=2 — zero
    multiplicative margin), R3 (exact sequence if Lemma A's weight breaks
    eigenspace form — possibly dissolvable if the parity indicator is an
    eigenspace regrading).
- Corrections ledger: Note 6's pi = -2 FALSE (audit witness AH(-2) != -1;
  03 had already corrected); 01's headline GAP (section 4.1 second
  consumption); 01's "no closed-form weight" FALSE (audit's witness
  weight). Feasibility threshold sharpened to [k/6, 2k/11).

## Note 10 (2026-08-20, late): Lemma A PROVED; endgame configuration

04 delivered: the hypergeometric closed form for the Type-2 transition
coefficients (both parities solve (1+z^2)y'' + zy' - lambda^2 y = 0;
four-route verification); the valuation identity v_2(c) = Sigma - 2m +
s_2(m) (Lemma A, proved, mod-8 arithmetic); THEOREM 3 (the audit's weight
floor((k-1)/3) + (k mod 2) is admissible with d(k) >= 1 for ALL k, machine
confirmed to k <= 400); THEOREM 4 (gamma = 1/6 sharpness via the k = 6
self-loop, one-coefficient certificate); and the 18-row global-consumption
audit of KMU-I sections 6-7: no further p=2 obstruction, strictness
resolved, no vertex loss, the final polygon is the KM one.

Coordinator's Note 7 cost formulas REFUTED by 04 with witnesses (wrong
expansion; the true structure is hypergeometric). Recorded.

Endgame dependency graph:
  THEOREM-CANDIDATE (NoH at p=2, arbitrary smooth affine curve)
   = KMU-I verbatim (wild + glue, audited)
   + Lemma A / Theorems 3-4 [PROVED by 04; priority-0 audit by 20 resumed]
   + Lemma B [char-2 tame map with e_P = 3; workstream 05 discharging via
     Sugiyama-Yasuda + KLW + 3-power composition]
   + Lemma E [KMU's own unproved section-6.2 assertion; 04 proved
     no-loss reduction for the theorem window]
   + KM-ab global audit [workstream 05, part 2].
After 20's audit and 05's discharge: write 30-writeup.md.

## Note 11 (2026-08-20, late): priority-0 audit absorbed; the coverage cap
## is universal in e; deflation proposed as the route to full coverage

- 20's PART TWO: Theorems 1-4 all CONFIRMED line by line (including the
  tail case Part One had flagged as the hard part); strictness and Cor
  7.14 confirmed; Note-7 refutations confirmed; threshold interval retired
  in favour of 04's exact gamma = 1/6. One structural GAP: Lemma E's
  coverage claim conflates pi_q-adic and q-adic normalizations of r
  (factor v_pi(p) = 2^(n-1)). Net coverage of the current candidate:
  FULL polygon for order-2 characters; initial segment r <= 2^(1-n)
  (q-adic) for order 2^n.
- Coordinator computation (exact, from 04's closed form, verified
  numerically for e = 3,5,7,9,11): the m = 1 self-loop sits at k = 2e
  with coefficient exactly 2 (v_2 = 1) for EVERY odd e; the m = 2
  self-loop at k = 4e has v_2 = 3. Hence the cap d(2e) <= 1 is
  UNIVERSAL — no tame index choice repairs higher-order coverage within
  the unmodified architecture.
- PROPOSED ROUTE TO FULL COVERAGE (new workstream when bandwidth allows):
  **finite-rank deflation of the self-loop line.** The k = 2e vector
  contributes one explicit near-diagonal entry of valuation exactly 1;
  strip its span (and, if needed, the finite forward orbit) as a
  finite-rank correction, factor/bound det(1 - Ms) as (small explicit
  block) x (deflated determinant), and run the weight argument on the
  complement, where d(k) >= 2-type increments become available. The
  self-loop factor's contribution to the Newton polygon is computable in
  closed form (it is where the polygon's own slope-1/2-type segment
  should sit). ALTERNATIVE route: prove KMU's unproved section-6.2
  assertion (Lemma E) directly with the M >= v_pi(p) range restored.
- Status: awaiting 05 (Lemma B + KM-ab). Write-up will state the
  two-tier result honestly: (T1) full NoH at p = 2, arbitrary smooth
  affine curve, order-2 characters [modulo Lemma B]; (T2) partial NoH
  (initial segment r <= 2^(1-n)) for order 2^n; plus the deflation
  program for the remainder.

## Note 12 (2026-08-20, night): PART THREE clean sweep — Target A complete

20's Part Three: every audited item CONFIRMED (Lemma B stage-by-stage; the
c^{p-1} = 1 correction — with the nuance that KM-exp itself was correct;
3 | q-1 necessity independently enumerated; base-change invariance audited
through the geometric-vs-closed-points trap; the KM-ab dictionary EXACT —
04's Lemma A/Theorem 3 transport verbatim into a coefficientwise module
with exact calibration).

FINAL RECONCILIATION (the project's result):
- TARGET A — SOLVED, all components proved and adversarially audited:
  NP_q >= HP_q (KM ramification-defined Hodge polygon), finite abelian
  characters of 2-power order, arbitrary smooth affine curves over
  F_{2^a}. Route: KM-ab globals + Lemma B (3-power tame composition,
  3 | q-1 free by proved base-change invariance) + Theorems 1-3 (the
  hypergeometric closed form, the valuation identity, the parity-indicator
  weight). Pending only: the 30-writeup assembly with label discipline.
- TARGET B — OPEN (stretch): KMU-I's contact/touching criterion at p = 2
  beyond q-adic r <= 2^{1-n}; obstruction = Lemma E (their own unproved
  Def-6.3-formalism assertion) + the universal d(2e) <= 1 self-loop cap;
  named routes: re-run sections 6.2/7 in KM-ab's coefficientwise
  formulation, or the finite-rank deflation of the k = 2e line (Note 11).
