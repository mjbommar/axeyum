# P2.5 · 08 — Evaluation, soundness gates, and ADRs

How we know each phase worked, and how we never ship a wrong verdict.

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
