# NRA durability plan: algebraic field arithmetic → CAD/nlsat, with evidence hooks

Status: research plan (sequences the durable NRA keystone; gates the implementation ADRs)
Date: 2026-06-21
Relates to: ADR-0024 (linear-abstraction NRA), ADR-0038 (real-algebraic numbers,
single-variable), ADR-0039/0040 (degree-2 SOS + its Lean reconstruction), and the
Sturm root-isolation primitive (`nra_real_root.rs`, commit 235e967).

## Why this exists

The NRA work so far is a set of *sound, exact, composable* pieces — but they stop
short of a general engine, and the reviewer's correct guidance is to build the
**durable, composable** ladder (field arithmetic → CAD/nlsat) rather than more
isolated decided shapes. This note sequences that ladder and fixes the
architecture decisions it needs, so each implementation slice lands against a plan
instead of ad hoc.

## Current state (the composable pieces in hand)

- **Single-variable real-algebraic values** (ADR-0038): `Value::RealAlgebraic{poly,
  lo,hi}` with an exact `sign_at` (zero only by exact polynomial divisibility;
  no float). Decides single-variable polynomial constraints with irrational
  witnesses.
- **Robust root isolation** (Sturm, 235e967): exact distinct-root counting
  (`V(a)−V(b)`), squarefree-part reduction, the completeness invariant
  (complete-or-`None`). This is the prerequisite for everything below: combining
  algebraic numbers produces a polynomial whose *correct* root must be identified,
  which needs no-missed-roots isolation.
- **Coupled 2-variable via Sylvester resultant** (`nra_real_root.rs`) and **degree-2
  SOS/PSD** (ADR-0039) with a kernel-checked Lean proof (ADR-0040). These are the
  two-variable / quadratic-form decided slices.

## The durable ladder

### Step 1 — Algebraic field arithmetic (the multivariate unlock)

`α + β`, `α · β`, `−α`, `α⁻¹` of two real-algebraic numbers. `α+β` is a root of
`Res_y(p_α(y), p_β(x−y))`; `α·β` of `Res_y(p_α(y), y^{deg} p_β(x/y))`. The resultant
may be reducible / carry extra roots, so the **correct** root is identified by
isolating within `[α.lo+β.lo, α.hi+β.hi]` (resp. the product interval) using the
Sturm isolation — exactly why Sturm landed first. Output: a new `RealAlgebraic`
with the resultant (or its squarefree part) as defining polynomial and the
isolating interval narrowed until it contains exactly one root.

**Architecture decision (to ADR):** field arithmetic belongs in
`crates/axeyum-ir/src/real_algebraic.rs` (it is an operation on the IR *value*
type, and the evaluator must compute it — today `eval` returns a graceful `Err`
for Real field ops on an algebraic operand). The Sturm isolation currently lives in
`axeyum-solver/nra_real_root.rs`; to avoid duplication, **move the exact-rational
polynomial + Sturm primitives down to `axeyum-ir`** (a `poly`/`sturm` module the IR
owns) and have the solver re-use them. This keeps one isolation implementation,
exact, overflow-graceful (decline on `i128` overflow — the bignum extension below
removes that ceiling later). Each operation stays exact or declines; `eval`
upgrades from `Err` to a computed `RealAlgebraic`, so models mixing algebraic values
replay-check.

### Step 2 — Bignum/Sturm robustness (remove the i128 ceiling)

The resultants and Sturm chains overflow `i128` for higher degree / large
coefficients (today: decline to `unknown`). Introduce an arbitrary-precision integer
(pure-Rust, no C/C++ — e.g. `dashu`/`num-bigint`, an ADR-gated leaf dependency that
must NOT enter the default *no-dep* surface for non-NRA fragments) behind a
`BigRational` used only on the algebraic path, so the decline becomes a decision.
Keep the `i128` fast path; fall to bignum on overflow.

### Step 3 — Cylindrical algebraic decomposition (CAD) / nlsat

With field arithmetic + robust isolation, build the real engine:
- **Projection** (McCallum/Hong) of the polynomial set onto fewer variables;
- **Lifting**: build sample points per cell (rational where possible, else
  algebraic via Step 1), evaluate the sign condition of every polynomial at each
  cell's sample;
- a query is `unsat` iff no cell satisfies all atoms. **nlsat** is the
  search-driven variant (model-guided, conflict-driven cell exclusion) — preferred
  for performance; CAD is the complete fallback. Bound the cell count → graceful
  `unknown`.

### Step 4 — Evidence hooks (Lean reconstruction for NRA)

This is where the proof track meets CAD. A CAD/nlsat `unsat` is "no cell satisfies
the atoms"; per cell the refutation is a **sign-condition contradiction** — a
product/sum of the atoms' polynomials that is sign-definite on the cell, i.e. a
*local* Positivstellensatz / SOS certificate. The degree-2 SOS→Lean pipeline
(ADR-0040, the ring normalizer + `sq_nonneg`) is the model; the general hook emits,
per cell, the polynomial-identity + nonnegativity certificate the kernel checks.
**Design the cell certificate format now** so the engine produces it as it decides,
rather than bolting proofs on later (the reviewer's "evidence hooks" point). Full
higher-degree Positivstellensatz reconstruction is a long arc; the near-term hook
is: CAD emits the per-cell sign-defining polynomial combination, and the existing
SOS reconstruction covers the degree-2 cells.

## Sequencing + deferral

1. **DONE** (commit `2a54d51`, ADR-0044) — Algebraic field arithmetic in
   `axeyum-ir` + Sturm/poly primitives moved down to `axeyum-ir/src/poly.rs`;
   `eval` upgraded from `Err` to computed `RealAlgebraic`.
2. **DONE** (commit `d3144bb`, ADR-0045) — Bignum on the algebraic path
   (`num-bigint`/`num-rational`, feature-gated `bignum`); intermediate resultant
   overflow becomes a decision. `RealAlgebraic` storage stays `i128` (final-result
   overflow still declines — the bignum-`Value` representation is a deferred slice).
3. **In progress** — the multivariate engine, sliced:
   - **slice 1 DONE** (commit `d3f8cfe`) — algebraic-grid lift: all-equality
     2-variable coupled systems with *irrational* coordinates now decide
     (enumerate roots(`Res_y`) × roots(`Res_x`), test each algebraic `(α,β)` pair
     by exact field arithmetic; Sat replay-checked, Unsat exhaustive only over the
     all-equality grid with every pair definitely signed).
   - **slice 2 DONE** (commit `3333c2a`) — exact evaluation-interpolation
     Sylvester determinant (`O(dim!)→O(dim³)`, caps 10/6→24), anchored by a
     differential test (3240 matrices ≡ Leibniz). Raises the resultant-degree
     reach for the bignum combinations and the future ≥3-var projection.
   - **slice 3 DONE** (commit `366eb45`, ADR-0046) — bignum
     `Value::RealAlgebraic` (`Vec<BigInt>`/`BigRational`, `num-bigint`
     unconditional): removes the i128-storage ceiling, collapses the i128/retry
     split, so the nested-radical coupled case `x²+y²=4 ∧ x·y=1` now decides
     **Sat** with replay. Soundness wall held (no verdict flip across 1558 tests).
   - **slice a DONE** (commit `60833cc`) — complete CAD for 2-variable
     **strict-inequality** systems via rational open-cell sampling (the open
     solution set ⇒ one rational interior sample per open cell is exhaustive, no
     algebraic substitution; Unsat complete-or-decline, every degeneracy declines).
   - **slice c DONE** (commit `e050b3e`) — recursive **N-variable** strict-inequality
     CAD (`visit_open_cells`): the same open-cell argument at every recursion level,
     so ≥3-var strict systems decide (Sat + Unsat); decline propagates via `?` so a
     gap is never mistaken for Unsat; nullification at a base point declines.
   - **SOUNDNESS AUDIT DONE** (commits `e39d161`, `af03e7b`, `2def73c`) — an
     adversarial **Z3 differential fuzz** (`tests/nra_differential_fuzz.rs`, 2000
     random coupled instances, gate DISAGREE=0) was added over the whole CAD/grid
     vertical. It found **two foundational wrong-`Unsat` bugs the 1370+ unit tests
     missed**, both in code every decider shares: (1) `sturm_isolate_rec`
     double-counted a root sitting at a bisection midpoint
     (`isolate_roots(−3x²−3x) → {0,0}`); (2) `cell_samples` used deep-dyadic
     `Root::locate` samples whose exact-rational term-eval overflowed `i128`, and
     the replay gate read the `Err` as "witness invalid" ⇒ wrong `Unsat`. Fixed
     (unconditional half-open split; simple eval-clean in-cell samples;
     replay declines on overflow). Now DISAGREE=0 over 2000 mixed instances. Run
     the fuzz before any NRA-decider change — it is the standing soundness gate.
   - **slice b DONE** (commit `84ce0af`) — mixed / non-strict cells with **rational**
     critical points: sample the rational 0-cells (boundaries the strict path skips)
     plus the open cells, decide each substituted univariate system completely;
     **decline** when a critical keep-value is algebraic. Fuzz-gated (DISAGREE=0 over
     2000 mixed instances).
   - **slice b2 IN PROGRESS** — **algebraic** critical-point lifting (the CAD
     completion). At an algebraic critical keep-value α (min-poly m), the elim-cell
     boundaries β satisfy `p(α,β)=0`, i.e. β is a root of `Res_x(m, p)` (a *rational*
     univariate in y) — isolate those, and sign-test `p(α,β)` exactly via the
     **algebraic field arithmetic** (`RealAlgebraic` add/mul, built in slice 1). So
     the deferred number-field case is reachable with existing infrastructure, not a
     new engine. Fuzz-gated.
   - **later slice:** (d) per-cell Positivstellensatz evidence (step 4) for Lean
     reconstruction.
4. Cell-certificate format + the degree-2 reconstruction hook; general
   Positivstellensatz reconstruction is the long arc.

Each step is sound-by-construction (exact arithmetic, decline-not-guess) and
composable (each reuses the prior). This replaces "more clever decided cases" with
the engine the cases were approximating.
