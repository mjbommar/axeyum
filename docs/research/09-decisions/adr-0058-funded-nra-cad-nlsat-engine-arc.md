# ADR-0058: The funded QF_NRA CAD/nlsat engine arc

Status: proposed
Date: 2026-07-07

## Context

What this closes: **how axeyum attacks the QF_NRA residue that no bounded slice
can reach** — and, by committing to it as a *scoped multi-week arc* rather than
ad-hoc slices, when to stop sharpening the existing linearization/CAD guards and
start building the decision engine the hard residue actually requires.

The 2026-07-06/07 arithmetic arc (decomposition
[P2.5 · 09](../../plan/track-2-theories/P2.5-nra/09-next-arithmetic-lever-decomposition.md))
drove QF_NRA to 27/38 and QF_NIA-cvc5 to 23/39 by *sharpening reachability* —
`/0` witnesses, threshold-1 monotonicity, the `a²=−k` even-power-equality shape,
the coordinate sat-witness grid. Its honest measured net was ~+5 decided rows
over ~57 commits and one P0 (the div/mod-by-const-0 convention fold, a
wrong-unsat, caught and repaired at `52f3b1d1`). The 8th and 9th periodic
reviews both concluded the same thing from the measured data: the **bounded**
NRA levers are nearly exhausted, and the remaining QF_NRA residue is **7/12
genuine-engine** —

- **I · Boolean-CAD** (`nl__factor_agg_s`): nested `or`/`not` over degree-3
  atoms whose theory *cubes* exceed what the linear abstraction can decide;
- **J · transcendental** (MetiTarski ×3, `sin-cos`): atoms over `sin`/`cos`/`pi`
  that no polynomial procedure decides at all;
- **K · high-degree CAD** (`nl__nt-lemmas-bad`): degree-8/10 univariate with
  algebraic coupling, past the current resultant/cell guards.

The decomposition doc's §3 audit establishes the precise shape of the wall.
axeyum's CAD (`decide_real_poly_constraint`, `nra_real_root.rs`) is
decision-complete *in principle* for **conjunctions** of polynomial comparisons
(2-var via resultants, N-var strict/mixed cells over the bignum algebraic core,
ADR-0044/45/46), and `check_with_nra_dpll` (commit `5ede57f4`) splits Boolean
structure. But three structural facts keep the residue out of reach:

1. **The DPLL↔CAD edge is missing.** `collect_conjuncts` has no `BoolOr` arm, so
   a top-level disjunction makes the exact CAD *decline entirely*; only
   `check_with_nra_dpll` case-splits it, and **each theory cube it produces is
   handed to the ≤2-cross-product linear abstraction, NOT back to the exact
   CAD.** A disjunction of nonlinear atoms never reaches the complete procedure.
2. **Four bounded engineering guards** (`MAX_CROSS_PRODUCTS=2`,
   `MAX_ABS_COEFF=2^40` i128, the ≤4-var product grid, `MAX_CAD_CELLS=256`) each
   *decline to `unknown`* (never a wrong verdict) but cap the reachable class.
3. **No transcendental substrate at all** — `sin`/`cos`/`pi` atoms have no
   procedure; today they can only ever be `unknown`.

This is not a decision-procedure gap for the *reachable* rows (those are the
remaining bounded slices #41/#43 in the queue) — it is a genuine **new engine**
for the *unreachable* rows. NRA is semidecidable (Tarski), so unlike the
strings theory-frontier (closed on the corpus) this residue has *real
headroom*: the rows are decidable, axeyum just lacks the machinery. That is
exactly what justifies a funded arc rather than continued slicing.

Register: research-questions RQ on "CAC over NLSAT" (the strings/nonlinear
program plan already recorded the CAC-over-NLSAT and `axeyum-poly`-crate
direction, and the no-C/C++ rule that rules out libpoly/MATA — this arc inherits
those constraints); the decomposition doc §2 ROI verdict; the CAD guards table
in §3.

## Decision

**Open a funded, ADR-scoped, multi-week QF_NRA decision-engine arc — built in
three phases (B → C → D), each phase decision-complete for a named fragment,
each verdict soundness-gated the same way the bounded slices are (sat = ground
replay, unsat = re-checkable certificate, dual-oracle DISAGREE=0), and each
unsat carrying a per-cell sign/Positivstellensatz certificate designed from the
start to reconstruct to a kernel-checked Lean `False` — and stop ad-hoc NRA
slicing once the two remaining cheap pickups (#43, slices 4+7) land.**

The arc is *not* sliced ad-hoc against individual corpus rows; it builds named
capability. But it is still landed incrementally — each phase is a sequence of
compiling, gated, additive commits (`unknown → decision`, never a flipped
verdict), per the working stance's "slice the keystone" rule.

### Phase B — Boolean-CAD: route DPLL cubes into the exact CAD (the missing edge)

The single highest-ROI engine step, and the one the decomposition doc already
identified. Make `check_with_nra_dpll`'s per-cube theory query call the **exact
CAD** (`decide_real_poly_constraint`) on the cube's conjunction *before*
falling through to the linear abstraction. Add a `BoolOr` handling path so a
disjunction of polynomial atoms is decided by case-split-then-CAD rather than
declining. First target: `nl__factor_agg_s` and `approx-sqrt-unsat` (the latter
also needs the Phase-B bignum coefficient path below).

- **Decision-complete fragment:** Boolean combinations (arbitrary `and`/`or`/`not`)
  of polynomial comparisons whose per-cube conjunctions are within the existing
  CAD's variable/degree reach.
- **Coefficient scaling:** lift the CAD *entry* guard off the i128
  `MAX_ABS_COEFF=2^40` onto the existing bignum algebraic path (ADR-0046) so
  tight/large rationals (`approx-sqrt`'s ~10²⁸ denominators) enter instead of
  declining. (This overlaps NRA slice 7 / #43 — Phase B subsumes it.)

### Phase C — ICP / transcendental with honest δ-sat

An interval-constraint-propagation layer over the bignum algebraic core for the
MetiTarski/`sin-cos` fragment: contract variable boxes against nonlinear +
transcendental atoms (Taylor/monotone enclosures for `sin`/`cos`/`exp`), refute
when a box empties (sound unsat with an interval certificate), and — crucially —
**return `unknown`, never `sat`, on a δ-satisfiable box that ICP cannot refine to
a replay-checkable witness** (the δ-sat⇒unknown discipline; `unknown` is a
first-class result, a δ-box is not a model). A genuine `sat` still requires a
ground-evaluator replay of an exact witness.

### Phase D — CAD projection / cell-count scaling for high degree

Raise the reachable degree/cell ceiling (`MAX_SYLVESTER_DIM=24`,
`MAX_CAD_CELLS=256`) with better projection (Brown/McCallum-style, or CAC-style
cylindrical *coverings* per the recorded CAC-over-NLSAT direction) for the
degree-8/10 algebraic-coupling rows (`nt-lemmas-bad`). Every raised guard stays a
*decline-to-`unknown`* past its new bound.

### Evidence-for-Lean, designed in from the start

Each phase's **unsat** emits a checkable certificate: Phase B a per-cell sign
assignment + the resultant/discriminant chain; Phase C an interval-contraction
trace; Phase D a Positivstellensatz/sign-certificate. These are specified so a
later P3.7 slice reconstructs NRA unsat to a kernel-checked Lean `False` (the
degree-2 SOS fragment already does — this generalizes it), keeping the arc on
*both* north-star axes (Z3 decide-rate parity **and** Lean proof parity) rather
than trading one for the other.

## Evidence

- **Decomposition doc §2/§3** (`fcbde209`): the ROI census classifying all 12
  QF_NRA declines; the CAD-machinery audit locating the missing DPLL↔CAD edge
  (`nra_real_root.rs`, `check_with_nra_dpll` from `5ede57f4`), the four guards
  with file:line, and the per-row escape analysis (each residue escapes on a
  *named* guard/shape, confirming the wall is engineering + missing-engine, not a
  soundness or completeness bug).
- **Bounded-slice diminishing-returns data** (9th review): ~+5 rows / ~57
  commits / one P0 — the measured signal that sharpening reachability has
  saturated and the residue requires new capability.
- **NRA is semidecidable** (Tarski): the residue is genuinely decidable, so the
  engine has real headroom — distinct from the strings theory-frontier which is
  corpus-closed.
- **Existing substrate** to build on: the bignum algebraic core (ADR-0044/45/46),
  the 2-var-complete/N-var-decision-complete CAD, the five z3-gated adversarial
  differential fuzzes at DISAGREE=0, and the SOS→Lean reconstruction precedent.

## Alternatives

- **Keep slicing NRA reachability ad-hoc.** Rejected: measured diminishing
  returns; the residue is provably out of reach of guard-sharpening (§3 escape
  analysis names an *engine* gap for 7/12, not a reachability gap).
- **Pivot entirely off arithmetic to Lean breadth** (the 8th review's framing).
  Rejected as the *primary* move: the 9th review established Lean is far more
  complete than assumed (8+ fragments incl. integer equality-systems; only the
  regex-emptiness cert #44 is a cheap pickup), and arithmetic remains the dominant
  *measured* Z3 decide-rate gap. Lean-NRA reconstruction is folded *into* this arc
  as the evidence plan rather than pursued as a separate thrust.
- **Depend on libpoly / an external CAD or nlsat implementation.** Rejected by
  the standing no-C/C++ default-build rule (CLAUDE.md hard rule; ADR-0002 identity)
  — the engine is pure Rust over the in-tree bignum algebraic core, consistent
  with the recorded `axeyum-poly`-crate direction.
- **NLSAT (model-constructing) instead of CAD/CAC.** Deferred, not rejected: the
  recorded program plan already leans CAC-over-NLSAT; Phase D revisits the
  projection strategy with measured cell-count data before committing.
- **Build the full engine as one keystone commit.** Rejected by the working
  stance — the arc lands as gated additive slices within each phase.

## Consequences

- **Easier:** the 7/12 genuine-engine QF_NRA residue becomes reachable
  phase-by-phase; Boolean-nonlinear queries (currently declining at the missing
  edge) decide from Phase B; NRA unsat gains Lean-reconstructable certificates.
- **Harder / cost:** this is the first *multi-week* arithmetic commitment
  (contrast the bounded slices) — it needs its own progress tracking under
  `docs/plan/track-2-theories/P2.5-nra/` and will not show the fast per-commit
  row gains slicing did; the honest expectation is capability-then-rows, not
  rows-per-commit.
- **Soundness surface grows** exactly where it is most fragile (nonlinear real
  arithmetic — the P0's home theory), so each phase carries: the dual-oracle
  `nra_differential_fuzz` **and** `nia_differential_fuzz` (shared multivariate
  path) at DISAGREE=0, `progress_frontier`, `corpus_regression`, `checked_*`
  arithmetic (graceful `unknown` on overflow, never a panic/wrong verdict — the
  standing i128/Rational lesson), δ-sat⇒unknown in Phase C, and unsat-certificate
  re-checking. No phase ships a `sat` without a ground-evaluator replay or an
  `unsat` without a re-checkable certificate.
- **Revisited when:** after Phase B lands and is measured, re-evaluate whether
  Phase C (transcendental) or Phase D (high-degree) is the higher-ROI next
  fragment against the then-current residue; the phase order past B is
  data-driven, not fixed here. If Phase B's measured yield is below the bounded
  slices it displaced, re-open the pivot question (this ADR is `proposed`, not a
  standing mandate — it is ratified to `accepted` only once Phase B's first
  sub-slice, the DPLL→CAD edge, is scoped and launchable with a measured target).

## Backlinks

- Decomposition & census: [P2.5 · 09](../../plan/track-2-theories/P2.5-nra/09-next-arithmetic-lever-decomposition.md)
- Bignum algebraic core: ADR-0044 / ADR-0045 / ADR-0046
- Identity / no-C/C++: ADR-0002; CLAUDE.md hard rules
- Lean reconstruction target: P3.7 (STATUS Track 3); SOS→Lean precedent
