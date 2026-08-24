# 31 -- Write-up log: decisions, reconciliations, label changes

Workstream 30 (NoH-p2). Date: 2026-08-20. Companion to `30-writeup.md`.
This file is the audit trail of the write-up itself: what was read, what was
re-derived, what was downgraded, what was upgraded and on whose authority.

---

## 1. Inputs read, in order

1. `00-charter.md`, `10-notes-coordinator.md` (Notes 1-11).
2. `01-kmu-extraction.md`, `02-pulita-splitting.md`, `03-u2-truth.md` (full).
3. `04-weight-proof.md`, `05-lemma-b-and-kmab.md` (full).
4. `20-verify.md` Parts One and Two (full), at the start of the run.
5. `ac-bridge-2026-08/24-novelty-check.md` (full), for the landscape section.
6. `20-verify.md` **Part Three**, which landed mid-run (file grew from 1042 to
   1480 lines). Read in full before finalising; see sec. 4.
7. Coordinator **Note 12**, which landed with Part Three and records the same
   reconciliation independently: "TARGET A -- SOLVED, all components proved
   and adversarially audited"; "TARGET B -- OPEN (stretch)". The artifact's
   two-tier structure agrees with it, and no label in the artifact is stronger
   than Part Three's own verdict table supports.

## 2. Independent re-derivation (what makes sec. 3 category (a))

Before writing sec. 3 I re-derived, from the definitions and without copying a
diary's argument:

- the Type-2 operator (conjugate `t' = -tG`, the trace, the support rule
  `j'(k)`);
- Theorem 1, including the `W = sinh^2(phi)` reduction, the ODE
  `(1+z^2)y'' + zy' - lambda^2 y = 0`, both series recurrences and both
  telescopings;
- Theorem 2 (Legendre + the factorisation), all four sub-cases of Lemma A
  including the tight `m = 1` point;
- Theorem 3: the increment formula, its failure at `n = 1, 3`, the four tail
  cases, and both mod-6 tables recomputed entry by entry, plus the `q = 0`
  exclusions;
- Theorem 4, and the `e`-universality `c_{2e,2e} = 2` (one line from
  Theorem 1 with `lambda = 2`; the coordinator's Note 11 had it as an exact
  computation verified numerically for `e = 3,5,7,9,11`);
- Lemma B, all four steps, the tameness argument, RH, and the fate of the
  second ramification point;
- the `c^{p-1} = 1` correction;
- the `3 | q-1` necessity: **all four configurations** of the degree-3
  classification worked out by hand (`05` writes out two);
- base-change invariance, both sides, including the Grothendieck-Ogg-
  Shafarevich degree count that forces the geometric reading of `|S|`;
- the explicit Lemma-B instance over any `F_q` with `3 | q-1` (fibre
  structure, `r_0 = 2q-1`, `r_1 = q-1`, `r_infinity = 1`, eq. (8), and RH
  saturation `sum(e-1) = 2 deg - 2`).

Machine confirmation was written from scratch in `ws30/` (exact `Fraction`
arithmetic; no code shared with any other workstream): a from-scratch series
solve of the defining identity, bound to Theorem 1 for `e in {1,3,5,7}`,
`k <= 16`, all `m` in support (355 pairs, 0 mismatches), reproducing `01`'s
ground-truth rows to the last digit; Theorem 2 for `e in {1,3,5,7}`,
`k <= 60`, `m <= 29` (0 mismatches); Lemma A for `k <= 600`, `m <= 80` (0
violations, 150 tight pairs all of shape `k = 2 mod 4, m = 1`); Theorem 3's
(A3) over the full support for `4 <= k <= 400`, `m <= 259` (0 violations,
minimum at `m = 0` for every `k`); the `d(4..24)` row, `d(100) = 17`,
`d(200) = 33`, `d(400) = 67`; the control `d(5) = 0` for KMU's own weight; and
`c_{2e,2e} = 2` for nine odd `e`, `c_{4e,4e} = 8` for five.

Every number reproduced `04`'s and `20`'s published values exactly. This is
the third or fourth independent implementation of the operator in the project
(`01`, `03`/`04`, `20`, and now `30`), and they agree.

Two runs were killed by the 2-minute foreground limit before being tuned; the
final scripts run in seconds. No result was taken from a partial run.

## 3. Decisions taken in assembling the artifact

**D1. Title.** "Newton over Hodge at p = 2 for 2-power-order characters on
arbitrary smooth affine curves." Chosen to name the exact scope: `p = 2`,
2-power order, arbitrary smooth affine curve. "Arbitrary curves" alone would
have been ambiguous against the published `P^1` results.

**D2. Which global route is the headline.** The KM-ab route, not KMU-I. Reason:
KMU-I's Def. 6.3 builds the local growth module as a Galois-eigenspace sum and
the parity-corrected weight is provably not an eigenspace regrading, which
forces Lemma E; KM-ab's module is coefficientwise, so the weight is native and
Lemma E does not arise. After Part Three this is not merely cleaner, it is the
difference between a capped and an uncapped theorem.

**D3. Two tiers, named T1 and T2.** T1 = the inequality (KM-ab route,
uncapped, all 2-power orders, full polygon). T2 = the KMU contact criterion
(KMU-I route, capped at q-adic `r <= 2^{1-n}`). Presenting only T1 would hide
the stretch goal; presenting only T2 would understate the result. The
coordinator's instruction after Part Three -- state A as the main theorem, B as
the partial tier -- matches what the audit supports.

**D4. Status labels are per-ingredient, not per-theorem.** Sec. 2.1 and
sec. 2.5 give a row for each input with its own label, because "T1 is
AUDITED-CONFIRMED" alone would obscure that (a) two external theorems are
cited, not proved, and (b) the non-load-bearing rows of `05`'s KM-ab table are
still un-audited (O5).

**D5. Every quotation carries its fetch provenance.** Where a source was
fetched by two workstreams independently (KMU-I Remark 6.5: five
transcriptions; KLW and SY: two), that is said, because a single transcription
is a single point of failure -- and this project has one such slip on record
(`05`'s "`F_p-bar`" for "`F_p`", sec. 4.6).

**D6. The error ledger is in the artifact, not only in this log.** Sec. 6.4.
The coordinator's four self-corrections, the workstream GAPs, and the parent
project's withdrawn novelty claim are all part of the evidence for how much
the surviving claims have been stressed.

**D7. Novelty framing.** Sec. 6.3 separates new from repackaged explicitly,
and sec. 1.3 disclaims `P^1`. The parent project already had to withdraw an
over-general claim here; the artifact states the withdrawal itself.

**D8. `a` versus `a*`.** The headline weight is the parity-indicator one, not
the LP-extremal `a*`, for three reasons now all stated in the artifact:
`a - a_KMU in {0,1}` is a bounded difference (`a*` drifts by `~(1/2)log_2 k`);
`a` is **integer-valued** so `p^{a(k)} in O_L` with no base change, while `a*`
takes values in `(1/6)Z`; and Theorem 3's proof is a finite case analysis
where `a*`'s is an induction.

## 4. Reconciliation with `20-verify.md` Part Three

Part Three landed after the first complete draft was written. It was read in
full, and the artifact was **rewritten**, not patched. Changes:

### 4.1 Labels upgraded (on Part Three's authority, never on mine)

| item | before Part Three | after |
|---|---|---|
| Lemma B (all stages, indices, tameness, RH) | PENDING-AUDIT | **AUDITED-CONFIRMED** (P3-1, P3-2, P3-3) |
| `c^{p-1} = 1` correction | PENDING-AUDIT | **AUDITED-CONFIRMED** (P3-4) |
| `3 \| q-1` necessity | PENDING-AUDIT | **AUDITED-CONFIRMED** (P3-5, independent classification) |
| base-change invariance of `NP_q`, `HP_q`, `Omega_rho` | PENDING-AUDIT | **AUDITED-CONFIRMED** (P3-6) |
| explicit Lemma-B instance | PENDING-AUDIT | **AUDITED-CONFIRMED** (P3-7) |
| `e = q-1` fallback | PENDING-AUDIT | **AUDITED-CONFIRMED as geometry**, with the "not a drop-in" caveat (P3-8) |
| KM-ab dictionary (row 11) and rows 7, 21, 25, case (II), sec. 7.3 | PENDING-AUDIT | **AUDITED-CONFIRMED** (P3-9, P3-10, P3-11) |
| KM-ab rows 15, 16 (the two source defects) | PENDING-AUDIT | **AUDITED-CONFIRMED** (P3-12, P3-13), with the true bound `(p-1)a(a+1)/2` |
| KLW Thm 1.2 / SY Thm 1.1 quotations | CITED, single fetch | **CITED, two independent fetches** |
| "Lemma E does not arise on the KM-ab route" | PENDING-AUDIT | **AUDITED-CONFIRMED** (P3-10, P3-12) |

### 4.2 The structural change: T1 is uncapped

The first draft stated T1 as PENDING-AUDIT and did not distinguish it sharply
enough from T2's coverage cap. Part Three P3-12 settles it: the Part Two cap
comes from Lemma E's need for `m_{e,P} >= 1` in **KMU-I's growth-tuple
formalism**, and KM-ab has no such formalism at the Type-2 points -- no radius
parameter, integer exponents, a weight-free Riemann-Roch step, and a diagonal
similarity. So there is no free parameter for Lemma E to constrain and no cap.
T1 is now the main theorem: full polygon, all 2-power orders, no truncation.
T2 keeps the cap, which Part Two proved structural (Theorem 4's
`d(2e) <= 1` for every weight, plus Lemma E's `m_P >= 1`).

### 4.3 Items still downgraded, and never upgraded by me

- **T2's range.** `04` sec. 9 claimed `r in [0,1]` for every order; `20` P2-6
  found the `pi_q`-adic / q-adic normalisation error and P3-14 reconfirmed it
  against `05`'s repetition of the same phrase. The artifact states
  `r <= 2^{1-n}` throughout and flags the cap as **structural**.
- **`05`'s dependency graph, TARGET B line** repeats 04's pre-correction
  "`r in [0,1]`" because `05`'s reading list stopped at Part One. Corrected in
  sec. 2.5 of the artifact, labelled as an inherited GAP (P3-14).
- **`04`'s "four independent routes"** for the Rust certificate: R4 is not
  independent of R2 (P2-8). Recorded in sec. 6.1 as a known weakness of the
  committed artifact, with the recommendation to add the series solve.
- **`01`'s three GAPs / one FALSE** ("nothing else"; the unqualified
  Riemann-Hurwitz claim; the incomplete constraint set; "no closed form
  works") all appear as such in sec. 4.6, sec. 3.8.4 and sec. 6.4.
- **`02`'s Table B labelling GAP** appears in sec. 6.4.
- **The non-load-bearing p-uniformity rows of `05`'s 26-row table** remain
  PENDING-AUDIT (O5). Part Three verified the load-bearing rows and says the
  rest is "consistent with what I verified"; that is not row-by-row
  re-derivation, and the artifact does not treat it as such.

### 4.4 Part Three notes folded in verbatim

1. **`g_2` is not decorative** (P3-1): without it, `0` would be a branch point
   of `g_2 phi` and the fibre over the final `1` would have **mixed** index,
   making Prop. 4.3(2) false. Stated as a display in sec. 3.8.2. The
   complementary point -- that the fibre over the final `0` **is** a genuine
   mixture and that this is fine, because the sources ask only
   `eta(S) = {0}` / `tau_i in eta^{-1}({0,infinity})` -- is stated immediately
   after, since P3-1 calls it "the first thing a referee will check".
2. **The `mu` counting-convention off-by-one** between KM-ab (33) (`mu(Q) = p`)
   and KMU-I (11) (`p-1`): same truncation, one counting the first kept index
   and the other the last dropped one. Flagged in sec. 3.8.4 as a display and
   listed in sec. 4.6.
3. **The parity-indicator weight is integer-valued**, so `p^{a(k)} in O_L`
   with no base change, unlike `a* in (1/6)Z`. Added to sec. 3.6's opening and
   to the `a*` row of the audit trail.
4. **KM-ab's module has no radius parameter**, so 04's calibration is exact
   there rather than conservative: the requirement is literally `d(k) >= 1` in
   `v_p`. Stated in sec. 2.1 and sec. 3.5.
5. **The `e = q-1` fallback is geometry only, not a drop-in** (it moves
   `mu(P)` to `q-1` and voids Theorem 3's `e = 3`-specific analysis). Stated
   in sec. 2.2 as a numbered option with the caveat inline, and again as a
   remark in sec. 3.8.5.
6. **`05`'s dependency-graph repetition of "`r in [0,1]`"** corrected in
   sec. 2.5, with the reason (reading list stopped at Part One).
7. **The `c^{p-1} = 1` correction is phrased so that no published mathematics
   is wrong**: KM-exp Lemma 3.1 takes `c = 2` and is correct; the defect is
   confined to KMU-I's paraphrase and the repair is one word. Sec. 3.8.3 and
   sec. 4.1 both carry that framing.

Also folded in, from Part Three but not in the coordinator's list: KM-ab
sec. 3.4 as a **second and stronger** witness for the local Frobenius at
`eta(Q) in {0, infinity}` (it writes a general `e_Q`, where KMU-I's phrasing
could be read as assuming `e_P = 1`); KM-ab sec. 7.3's degree count as the
cheaper way to get the slope-1 half (correcting `05`'s description of it as a
duality argument); the `05`/`20` map-count disagreement (8 vs 6) and its
harmless cause; and the unstated nontriviality hypothesis in the base-change
proposition, now stated with the reason it cannot fail here.

## 5. What a referee should attack first

In order of expected yield:

1. **The un-audited rows of `05`'s KM-ab table** (O5). Everything else under
   T1 has been re-derived twice or three times; these have been read once.
2. **Lemma E** (O1), which is a gap in the published source at every p, and
   which is the whole of T2's restriction.
3. **The two external citations** (KLW Thm 1.2 / 7.6, SY Thm 1.1). Quoted
   twice from PDF but their internal proofs are not verified here (O6).
4. **Theorem 3's `e = 3`-specificity** (O3): the mod-6 case analysis is the
   one part of the local repair that does not generalise as stated.

## 6. Budget

All computation for this workstream ran inside the 5-minute / 2 GB budget.
Nothing outside `docs/research/10-cas/noh-p2-2026-08/30-writeup.md` and
`31-writeup-log.md` was written; no git operation was performed.
