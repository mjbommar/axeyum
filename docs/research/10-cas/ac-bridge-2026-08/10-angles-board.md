# Phase 2 board: angles of attack

Date: 2026-08-20. Inputs: diaries 01-05 (phase 1, complete).

## Phase-1 synthesis in six lines

1. The load-bearing target is now **(WK)**, the connected form:
   `K_4 <= 2^ell (mu - P_n)^4 - 3 (mu Sigma)^2`, with Lemmas A/B proving the
   proper-power mass and the Wick half discharged by the proved Weil
   envelope from `ell >= 14/13` (diary 04). Slack `2^ell/ell^2` (02, 04).
2. The bridge has a name: **remove the tameness hypothesis `p > n` from
   Hast--Matei Thm 1.4 at `m = 4`** (diary 02); their Remark 1.5 says the
   missing input is the `S_n^m`-action on cohomology.
3. Hypercontractivity with an absolute constant is FALSE (level-4 constant 9,
   global witness); the correct frame is **delocalization / participation
   ratio**, and the nearest machine is a **Green--Sawhney-style dichotomy**
   (level inequality OR density increment on a conductor progression) (01).
4. The Z/8 phase collapses to Z/4; **(E2') is a pure rank count** and
   **(S) is Arf-sign square-root cancellation weighted by `2^(n_F - r_F/2)`**;
   cancellation comes entirely from **incomplete twist orbits**, reopening
   fibre-level Burgess amplification (03). (E2') plateaus at 0.889 (04).
5. **Resurrected top candidate (05)**: cellwise absolute connected cumulant —
   `(CAB): sum_{a<=b<=c<=d} mult |K_(a,b,c,d)| < 2^(ell+4(n-ell)) - 3 M_2^2`
   for `ell >= ell_0` — closes measured rows from `(14,30)`, ratio decaying
   `2^(-0.28 ell)`; needs NO cross-order cancellation. Also resurrected:
   max-to-average, orderwise, annihilator-layerwise, (RF) coeff-2, (ORD).
6. Ledger meta-correction (05): refutation headlines were 64x inflated;
   only structural-support L2 Cauchy is exponentially dead.

## Phase-2 workstreams

- **A. (CAB) ladder** -> `11-angle-cab.md` + `acb_cab_*.rs`.
  Prove or maximally advance (CAB): per-cell proved bounds on `|K|` (Weil on
  fibre products minus Wick, exact low-order cells), the decay mechanism of
  the closure ratio, measurement to the largest affordable `ell`, and an
  induction/recursion on cell order. Deliverable: rung proofs L3 or a
  precise reduced lemma.
- **B. Wild Hast--Matei** -> `12-angle-wild-hm.md`.
  Equation-level read of Hast--Matei's proof of Thm 1.4; locate every use of
  `p > n`; determine what survives at `p = 2` for THIS family (long-cycle
  strata confinement is already proved in-ledger); connect to sweep-06's
  localized trace formula lemma. Deliverable: the minimal wild statement
  and an honest tractability verdict.
- **C. Dichotomy / delocalization** -> `13-angle-dichotomy.md` + `acb_dic_*.rs`.
  Formalize the Green--Sawhney-style dichotomy on `G_ell`'s conductor
  filtration; the increment side must collide with a PROVED fact (the
  low-conductor Weil equidistribution) — design the collision carefully
  around sweep-09's uncertainty-principle lemma (which forbids naive
  minorants, not structure extraction). Test both sides on `B_j(b)` data.
- **D. Rank/Arf split** -> `14-angle-rank-arf.md` + `acb_gr_*.rs`.
  Falsify or confirm (GR-2) first; then the rank-count form of (E2') as a
  provable statement (Artin--Schreier kernel dims are already proved
  in-ledger), and the incomplete-orbit Burgess amplification for (S).

Shared rules: charter section "Rules of the project". New code only as new
`crates/axeyum-cas/examples/acb_*.rs` files with the workstream prefix.

## Phase-2 results (2026-08-20 evening)

- **A (CAB)**: conductor-level regrading, all PROVED (orthogonality, parity
  selection rule, per-layer Weil, exact 1/4-per-level recursion). (CAB-L)
  implies even the STRONG target from ell=10 with decay 2^(-0.46 ell).
  Proved reduction chain to ONE statement:
  **(SUP-L)** `max_e |D_[j](e)| <= K (j-1) 2^((j-1)/2) 2^(n/2) / 2^ell`
  per conductor level j; K=2 closes the endpoint for ell >= 22/20.
  Measured: median ~1, global max exactly 2.0000 over 341 pairs, no drift.
- **B (wild HM)**: tameness = one lemma (2.6), REFUTED at p=2 on the
  Frobenius-square strata; proved char-free replacement **Lemma W**; but
  the HM architecture is vacuous at fixed q=2 (ineffective constant) —
  retired in favour of (HM4-2) = sweep-06 (PURITY). Unification: A's cells
  are the sub-threshold graded pieces of HM's filtration.
- **C (dichotomy)**: GS import refuted (density window empty); PROVED exact
  multiplicative dichotomy `R_0 = prod_j (1+q_j)`, `0 <= q_j <= 1`; naive
  Weil collision refuted (zero margin at the endpoint scale — proved
  mechanism); hypercontractivity closed on measured masses; proved
  `E_1 = 0` at odd endpoints. Residual:
  **(CDL)** `sum_(cond chi = j) |sum_e D_e^2 chi(e)|^2 <= M_2^2/ell` for
  `j <= 4.1 log2 ell` — a shifted second moment at poly(ell) low-conductor
  twists; measured margin 2^ell/ell^(c+1), growing.
- **D (rank/Arf)**: (GR-2..6) refuted/void (object mismatch found: c_F is a
  Mobius autocorrelation, not a Gauss sum); proved Lemmas D1/D1a/D3/D4 and
  Theorem D2 (fibres are COMPLETE orbits; Euler product predicts the 8/9
  plateau exactly); amplification is a lossless identity that moves the
  problem one level in; (E2')+(S) demoted to falsification instrument.

## Phase 3 assignments

- **20-verify-chains.md** — adversarial verification of the two load-bearing
  proved chains (A's (CAB-L)->(SUP-L) collapse; C's q_j product machinery
  and the (CDL) sufficiency derivation) plus Lemmas A/B/W/D1-D4/E1.
- **21-supl-assault.md** + `acb_sup_*.rs` — prove (SUP-L) where possible
  (low levels; the exact-2.0000 attainment structure; connection to the
  1/4-recursion and q_j <= 1), quantify the irreducible core.
- **22-cdl-assault.md** + `acb_cdl_*.rs` — prove (CDL) or its smallest
  sufficient sub-form; the object is a shifted convolution
  `2^-ell sum_psi S_psi conj(S_(psi chi))` at poly(ell) twists.
- **23-artifact.md** — assemble the standalone novel-math artifact:
  "conductor-graded Fourier analysis on principal-unit 2-groups"
  (the proved corpus: orthogonality, parity rule, 1/4-recursion, q_j
  dichotomy, E_1 = 0, Lemma W, D1-D4/D2, Lemmas A/B), with export targets
  for kernel admission and Lean verification of exports.

## Phase-3 results (partial, 2026-08-20 late)

- **20 (verify)**: A's and C's chains CONFIRMED; kappa_j <= 2^((j-1)/2)
  proved (so K=2 is a theorem for j <= 3); Lemma W (diary 12) GAP at m=4;
  Lemma D4 GAP, repaired; (SUP-L) true margin at j>=4 was 0.4%.
- **23 (artifact)**: 30-paper-draft.md assembled, 38 statements re-derived,
  reconciled with 20; novelty claim marked UNVERIFIED pending prior-art
  search (WebSearch budget exhausted).
- **21 (SUP-L assault)**: **(SUP-L) REFUTED for every absolute K** —
  witnesses (j,n) = (4,56), (5,48); kappa_j -> ceiling as n grows.
  Proved: layer ell-freeness (D_[j] = sibling short-interval difference,
  max = the ledger's H_j^*); kappa_2 exact; sup_n kappa_3 = 2 exactly
  (supersingular period 24); mechanism = KR form factor x Gaussian
  extreme value. Surviving residual, exactly priced:
  **(TOP-POLY)** H_j^* <= (j-1) 2^(n/2) / (2.4 ell) on the top
  ~4 log2 ell conductor levels (the L4 route over-asks by a factor ell
  vs the ledger's Haar-triangle route).
- **22 (CDL assault)**: pending.

Next: single revision pass on 30-paper-draft.md incorporating 21 + 22.
