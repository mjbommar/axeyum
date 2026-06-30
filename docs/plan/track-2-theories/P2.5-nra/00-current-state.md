# P2.5 · 00 — Current state: what axeyum's nonlinear engine decides today

> **Corrected 2026-06-30.** An earlier draft of this doc (grounded only in the
> solver-side `nra*.rs` files) badly *understated* the baseline. The authoritative
> sources are **ADR-0038/0044/0045/0046**, **ADR-0039/0040** (SOS), and the
> sequencing roadmap
> [`docs/research/05-algorithms/nra-cad-nlsat-plan.md`](../../../research/05-algorithms/nra-cad-nlsat-plan.md).
> The reality: **a substantial CAD decision procedure already exists** — and it
> lives in `axeyum-ir` + `axeyum-solver`, **not** a future crate.

## The big correction: the CAD is largely built (decision side)

axeyum does **not** merely decide single-variable problems + a heuristic
≤2-cross-product fragment. Per the roadmap (each slice DONE, commit-cited,
Z3-differential-fuzz-gated DISAGREE=0):

- **Algebraic field arithmetic** (`α±β`, `α·β`, `−α`) on `Value::RealAlgebraic` —
  ADR-0044, in `crates/axeyum-ir/src/real_algebraic.rs`. `eval` computes mixed
  algebraic/rational arithmetic, so models with irrational witnesses replay.
- **Bignum everywhere on the algebraic path** — ADR-0045 (resultant/Sturm
  intermediates) + ADR-0046 (`Value::RealAlgebraic` stored as `Vec<BigInt>` /
  `BigRational`). The i128 ceiling is gone; nested-radical coupled cases like
  `x²+y²=4 ∧ x·y=1` decide **Sat** with replay.
- **Exact Sylvester resultant** with evaluation-interpolation (`O(dim³)`,
  differential-tested vs Leibniz over 3240 matrices).
- **2-variable CAD — COMPLETE** for any-coordinate (rational *or* algebraic)
  mixed / non-strict systems (slices a, b, b2).
- **N-variable CAD — complete on the *decision* side** for any dimension and any
  coordinate: strict (slice c) and algebraic critical-point lifting (slice c2),
  routed `or_else` after the rational path so it only upgrades `Unknown→decide`,
  never flips a verdict.
- **Degree-2 SOS / PSD** refutation (ADR-0039) **with a kernel-checked Lean
  proof** (ADR-0040/0041) — the only NRA route that currently carries a proof.

The polynomial + Sturm + resultant primitives live in **`axeyum-ir/src/poly.rs`**
(ADR-0044: one isolation implementation, shared by the IR value layer and the
solver — *deliberately not a new crate*). The single-variable
`nra_real_root.rs` reuses them and remains a fast pre-path + differential oracle.

## What that means for this program (plan correction)

1. **There is no `axeyum-poly` crate, and we should not create one** — ADR-0044
   already decided the primitives live in `axeyum-ir` (ADR-0001: split only when a
   boundary is exercised; reuse satisfies it). [02-architecture.md](02-architecture.md)
   and [03-phaseA-algebraic-core.md](03-phaseA-algebraic-core.md) are corrected to
   *extend `axeyum-ir`'s `poly`/`real_algebraic` modules*, not stand up a crate.
2. **Phase A (the algebraic core) is largely DONE** — multivariate-enough
   polynomials, bignum, Sturm isolation, resultants, real algebraic numbers, field
   arithmetic all exist. Remaining Phase-A-ish work is *performance* (McCallum/Hong
   projection to replace the current resultant-elimination lifting) and breadth,
   not greenfield construction.
3. **Phase D (the complete oracle) substantially exists as CAD**, not CAC. The
   roadmap built CAD directly (projection-by-resultant + lifting + cell sampling).
   The remaining Phase-D work is **(a) per-cell Positivstellensatz *evidence*** for
   Lean parity (roadmap step 4 / "remaining (d)") and **(b) performance** (bound
   cell blow-up; the cheaper front tier below).

## The genuine remaining gaps (where the work actually is)

| Gap | Status | Where it's addressed |
|---|---|---|
| **Cheap front tier** (incremental linearization CEGAR) so CAD is invoked sparingly | `nra.rs` has McCormick + ad-hoc point/SOS lemmas, **not** a principled lemma-on-demand loop | [Phase B](04-phaseB-incremental-linearization.md) |
| **ICP** for transcendentals + box pruning | spatial B&B exists (depth ≤6); not interval contractors | [Phase C](05-phaseC-icp.md) |
| **CAD performance** (projection quality, cell-count bound) | decision-complete but resultant-elimination lifting may be costly | [Phase D](06-phaseD-nlsat-cac.md) |
| **Per-cell proof / evidence** (Lean parity for NRA) | only degree-2 SOS cells carry a proof | [Phase D](06-phaseD-nlsat-cac.md) §certificate + Track 3 |
| **NIA UNSAT engine** (incremental linearization over UFLIA) | width-ladder = SAT finisher; `nia_square` = 1-var; NIA CAD-via-real-relax exists (slice c2 NIA fuzz clean) | [Phase E](07-phaseE-nia.md) |
| **Measured decide-rate / PAR-2 vs Z3** on public QF_NRA/QF_NIA | **not yet measured for the CAD engine** — the binding next step | [08-evaluation](08-evaluation-and-soundness.md) |

## NRA Layer-B / Layer-C (the heuristic relaxation, `nra.rs`) — still as described

The linear-abstraction + McCormick + spatial-B&B relaxation (ADR-0024) and the
even-power refutation remain, now as the *cheap tier below the CAD*: each product
`a·b` → fresh var, valid product/SOS/McCormick lemmas, spatial B&B (depth ≤6),
incremental point-lemma loop (≤12 rounds), ≤2-cross-product cap. Sound (relaxation
only grows the model space; `sat` replay-checked), incomplete. Phase B upgrades
this into a principled incremental-linearization tier.

## NIA — as before, plus the CAD reuse

- **`nia_square.rs`** — single-variable integer polynomial, exact (discriminant /
  rational-root), replay-checked.
- **Width-ladder bit-blast** (`auto.rs` tail) — SAT finisher; `int_real_relax`
  short-circuits real-unsat.
- **NIA via the N-variable CAD** (real relaxation + algebraic lifting, slice c2) —
  the NIA differential fuzz is DISAGREE=0, so the CAD path already serves NIA.

## The corrected one-sentence gap

The complete multivariate QF_NRA **decision procedure is largely built and
fuzz-sound**; the real remaining work is **(1) measuring it vs Z3**, **(2) a cheap
incremental-linearization tier + ICP so it scales**, **(3) per-cell proof evidence
for Lean parity**, and **(4) the NIA incremental-linearization UNSAT engine** —
*not* building CAD from scratch.

## What we reuse / must not rebuild

- `axeyum-ir`'s `poly` + `real_algebraic` modules (bignum, Sturm, resultant, field
  arithmetic) — **the foundation already exists; extend it**.
- The CAD slices in the solver (`decide_nonstrict_cad_nvar_algebraic`,
  `visit_all_cells_value`, `fiber_boundary_poly`, `multi_resultant`, …).
- The four differential-fuzz gates (NRA/NIA/UFLIA/ABV), DISAGREE=0 — run before any
  decider change.
- ADR-0040's SOS→Lean ring normalizer — the seed for per-cell certificate
  reconstruction.
