# P2.5 · 08 — Evaluation, soundness gates, and ADRs

How we know each phase worked, and how we never ship a wrong verdict.

## Measured baseline (2026-06-30) — the grounding number

First head-to-head of the **existing** engine (`check_auto`) vs the `z3` 4.13.3
binary on the curated non-incremental corpus (`measure_corpus`, 5 s cap, via
`scripts/mem-run.sh`):

| Division | axeyum decided | z3 decided | DISAGREE | axeyum PAR-2 | z3 PAR-2 |
|---|---|---|---|---|---|
| **QF_NRA** (curated, 36 considered) | 9 → **10 / 36** (28%) | 36 / 36 | **0** | ~7.3 s | 0.01 s |
| **QF_NIA** (curated, 28 considered) | **20 / 28 (71%)** | 28 / 28 | **0** | 2.985 s | 0.025 s |

> **LANDED 2026-06-30 — Boolean case-split (B.0b) shipped: QF_NRA 9 → 10** (commit
> `5ede57f4`). `check_with_nra_dpll` (a lazy-SMT loop deciding each Boolean-skeleton
> cube with `decide_real_poly_constraint`) unlocked the Boolean-structured
> `issue3656` (`(distinct (and (>= c …)(< c …)) (= (* b c) 0))`), which the
> flat-conjunction CAD declines.
>
> **The soundness gate earned its keep.** The first prototype *failed the
> `nra_differential_fuzz`* and was reverted in full before any commit. Full-capture
> diagnosis (task #68) showed the failure was **not** a DISAGREE / wrong verdict —
> it was `"solve returned an error"`: `finish_sat` propagated an **i128 eval-overflow
> during sat-replay** as a `SolverError::Backend` instead of a graceful `unknown`
> (the same class as the `lra.rs` fix, commit `1f615670`). So the case-split was
> **sound all along**; the blocker was a benign robustness gap. Fixing `finish_sat`
> (eval-error → graceful `unknown`; a *definitely-violated* model stays a loud
> alarm) let the case-split land. Verified: `nra_differential_fuzz` 2000 seeds
> **DISAGREE=0, no error**; `nia_differential_fuzz` **DISAGREE=0**; lib 613/613;
> clippy clean.
>
> **Next NRA levers** (the case-split only gains where each cube is within CAD
> reach): most remaining Boolean-structured curated instances (`ones`,
> `simple-mono-unsat`) have cubes with higher-degree / more-variable products
> (`a·b·c·d`) that the CAD *component* decider (`decide_component` at
> `nra_real_root.rs`) declines, or > 2 cross-products the relaxation caps. So the
> next gains are **(Phase D)** widening `decide_two_var_component` /
> `decide_*_cad_nvar` reach (degree/variable) and **(Phase B)** a proper
> incremental-linearization tier lifting the ≤ 2-cross-product cap.

**Reading:** soundness holds (DISAGREE=0). The CAD is decision-complete *in
principle* but decides only 25% of curated QF_NRA within 5 s — axeyum's high PAR-2
(7.5 s vs z3's 0.01 s) says the gap is dominated by **timeouts / not reaching a
verdict**, not wrong answers. The per-instance `explain_corpus` route trace
determines how much is (a) CAD too slow / cell blow-up (→ Phase B cheap tier +
Phase D projection) vs (b) shapes not routed to CAD (→ dispatch/coverage). NIA at
71% is closer; its residual is the UNSAT-side gap (→ Phase E incr-lin).

> This table is the P2.5 scoreboard anchor. **Re-run it after every phase** and
> record the delta here; no decide-rate claim without a re-run
> ([SCOREBOARD](../../../../bench-results/SCOREBOARD.md)).

### Why QF_NRA is 25% — per-instance decline breakdown (`explain_corpus`, 3 s)

The route trace on the 27 undecided QF_NRA instances localizes the gap precisely:

| Decline reason | ~count | Meaning |
|---|---|---|
| `nra: nonlinear abstraction: N cross-products exceed the bound of 2` | **~15** | the ADR-0024 ≤2-cross-product cap rejects N∈{3,6,7,9,12,14,15,20,31,322} |
| `lra: Fourier–Motzkin elimination exceeded the wall-clock/size budget` | **~7** | the LRA relaxation's FM elimination blows the budget |
| `milp: declined (unsupported)` (mixed real+int) | several | the {real,int} fragment isn't routed to a nonlinear path |
| i128 overflow in LRA replay (`approx-sqrt-unsat`) | 1 | `real_cmp` evaluation overflows i128 → backend **error** (should be graceful unknown) |
| parse-error | 1 | `real-numerals` front-end gap |

**The decisive observation:** on *every* multi-variable instance the trace shows
`nra-real-root: declined (not-applicable)` **before** falling to `nra.rs`. So the
**CAD that is "decision-complete" almost never fires on real benchmarks** — its
applicability gate only admits narrow conjunction/strict shapes, and Boolean-
structured / mixed real-int instances bypass it entirely. The 25% is therefore a
**routing + cap** problem, not a missing-algorithm problem.

### Re-prioritized next levers (measured, not assumed)

1. **Widen the CAD applicability gate** so the existing decision-complete CAD fires
   on more multi-variable polynomial conjunctions (the biggest lever — the engine
   exists, it just declines). → [Phase D](06-phaseD-nlsat-cac.md) / dispatch.
2. **Raise/remove the ≤2 cross-product cap** in `nra.rs` now that the algebraic
   path is bignum (the cap's stated reason — "multi-variable can OOM, needs CAD" —
   is exactly what the CAD now provides). → [Phase B](04-phaseB-incremental-linearization.md).
3. **Make the i128 LRA-replay overflow a graceful `unknown`**, not a backend error
   (the [Rational-overflow class](../../../research/)). Quick soundness-hygiene win.
4. **Route mixed real+int nonlinear** into the NRA path instead of `milp: unsupported`.

NIA at 71% is closer; its residual is the UNSAT side → [Phase E](07-phaseE-nia.md)
incremental linearization over UFLIA.

### ROOT CAUSE (2026-06-30): Boolean structure, not the polynomial algorithms

Inspecting the small undecided instances shows the real bottleneck. They are
**Boolean combinations of nonlinear atoms**, e.g.:
- `ones`: `(>= a 1)…(>= d 1) ∧ (or (= a 1)(= b 1)(= c 1)(= d 1)) ∧ (< (* a b c d) 1)`
- `simple-mono-unsat`: `(or (= a 4)(= a 3)) ∧ (> b 0) ∧ (> c 0) ∧ (< (* a b c d d) 0)`
- `issue3656`: `(distinct (and (>= c …)(< c …)) (= (* b c) 0))`

axeyum's CAD + sign-cell decider are mathematically strong but **only accept a flat
conjunction** (`decide_real_poly_constraint` declines on *any* non-conjunctive
structure; `decompose_multivariate` declines on coupled shapes). The moment an
`or` / `distinct` / `ite` appears — i.e. essentially every real benchmark — the
whole NRA stack declines and falls to the ≤2-cap `nra.rs`. **There is no
DPLL(T)/case-split over the Boolean skeleton feeding conjunctions (cubes) to the
CAD.** That missing lazy-SMT loop — not the polynomial math — is the dominant
QF_NRA gap.

**This reframes the priority order:**
1. **Boolean-case-split over NRA atoms (the keystone lever).** Enumerate the
   Boolean skeleton's satisfying assignments of theory atoms (DPLL(T)-lite, bounded
   cube count) and run the *existing* flat-conjunction CAD/decider on each cube;
   all-unsat ⇒ `unsat`, any cube `sat` (replay-checked) ⇒ `sat`, too many cubes /
   any cube `unknown` ⇒ `unknown`. Sound by construction (case analysis). This is
   the tractable precursor to the full [CDCL(T) loop (P1.5)](../../track-1-engine/P1.5-cdcl-t-loop.md)
   and is the **single highest-leverage NRA increment** — it unlocks the strong CAD
   on real (Boolean-structured) benchmarks. *(Next task; see #66.)*
2. Then the ≤2 cap matters less (cubes are conjunctions the CAD handles); raise it
   for the residual non-CAD multivariate cubes.
3. Graceful `unknown` on the LRA-replay i128 overflow (soundness hygiene).

The full CDCL(T) loop (P1.5) generalizes step 1 to incremental, conflict-driven
theory propagation; the bounded case-split is the measured-justified first slice.

## Measurement protocol (no claim without a re-run)

- **Corpus:** the public QF_NRA / QF_NIA / QF_UFNRA divisions (the gitignored NAS
  symlink + `corpus/public-curated/`), measured with `bench` `--backend solver`
  (`check_auto`) head-to-head against the `z3` binary.
- **Metric:** decide-rate (sat+unsat / total) and PAR-2, per division, vs Z3
  4.13.3, recorded in [bench-results/SCOREBOARD.md](../../../../bench-results/SCOREBOARD.md).
- **Rule:** *no decide-rate claim without re-running the scoreboard.* Each phase's
  exit criterion is a **measured** delta, not an asserted one.
- **Baseline to beat:** the residual hard instances on measured divisions are
  nonlinear (e.g. issue5836-2 = QF_UFNRA). Phase B should move the needle first;
  Phase D closes the completeness gap.
- **64 GB cap:** all runs via `scripts/mem-run.sh` — the multivariate blow-up is
  exactly what OOMs the box.

## DISAGREE=0 (the soundness floor)

Every phase is gated by the z3-differential fuzzes before commit:

- `crates/axeyum-solver/tests/nra_differential_fuzz.rs`
- `crates/axeyum-solver/tests/nia_differential_fuzz.rs`
- (shared multivariate path) run **both** when touching either decider.

These found 4 real defects the 1370+ unit tests missed (wrong-unsats from
`isolate_roots` midpoint, `cell_samples` overflow, `lift_candidate` positive-dim
collapse; + a nested-UF projection crash). The new code is far larger surface —
**expand the fuzzers** to generate multivariate polynomials, transcendental atoms,
and `iand` constraints as those land.

## Per-phase soundness obligations

| Phase | `sat` checkable by | `unsat` certified by | `unknown` triggers |
|---|---|---|---|
| A | (infra; differential vs `nra_real_root.rs`) | — | — |
| B incr. lin. | replay (drop fresh vars) | linear refutation retained | no refinement / budget |
| C ICP | **exact witness only** (δ-sat ⇒ unknown) | contraction trace | δ-small box / transcendental sat |
| D CAC | algebraic assignment `sign_at` replay | **covering + projection chain (re-checkable)** | budget / degree / time |
| E NIA | integer witness replay | Layer 1 relaxation / Layer 2 over-approx | branch depth / width ceiling |

**Non-negotiable invariants** (audited by dedicated tests):
1. No tier ever returns `sat` from a non-replayable witness (ICP δ-sat audit).
2. No tier converts another's `unknown` into a verdict without independent
   justification.
3. Width-ladder bit-blast (E Layer 4) never emits `unsat` for unbounded integers.
4. SOS/SDP certificates (if ever used) re-checked in exact rationals, never trusted
   from floating point.

## Proof / Lean-parity obligations (Track 3)

- Every new `unsat` route gets an independent checker or a
  [trust-ledger](../../track-3-proof-lean/P3.0-trust-ledger.md) entry, ideally an
  Alethe reduction proof ([P3.5](../../track-3-proof-lean/P3.5-reduction-proofs.md)).
- **CAC coverings are the natural certificate** — re-derivable by replaying
  projections. This is *why* we chose CAC over NLSAT.
- The degree-2 **SOS fragment already reconstructs to kernel-checked Lean** — extend
  it as the certified-nonlinear-`unsat` seed (p>0 cases, evidence wiring).

## ADRs to write (in order)

1. **ADR-A0** — `axeyum-poly`: a pure-Rust polynomial & real-algebraic core
   (bignum strategy, representation split, no-C/C++ + WASM constraints). *(Phase A)*
2. **ADR — incremental-linearization loop** semantics & lemma set, the lifted
   cross-product cap, transcendental UNSAT-only stance. *(Phase B)*
3. **ADR — ICP δ-sat ⇒ unknown** discipline and transcendental handling. *(Phase C)*
4. **ADR — CAC as the complete oracle** (vs NLSAT), the covering certificate
   format, and the SMT-LIB-division undecidability boundary. *(Phase D)*
5. **ADR — NIA portfolio**: undecidable-honest design, SAT/UNSAT layer split,
   width-ladder repositioning, `iand` semantics, div/mod axiomatization. *(Phase E)*

## Definition of done for P2.5

- `axeyum-poly` exists, pure-Rust, WASM-green, property-tested.
- Tiered NRA engine: incremental linearization → ICP → CAC, with measured
  decide-rate on public QF_NRA approaching Z3/cvc5 and **DISAGREE=0**.
- NIA portfolio decides UNSAT instances the bounded ladder cannot, measured.
- Every `unsat` route carries a checker / trust-ledger entry / Alethe proof; CAC
  coverings re-checkable.
- All five ADRs merged; foundational DAG + research-questions updated; STATUS.md
  reflects the measured pulse.
