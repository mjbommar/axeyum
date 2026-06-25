# Measurement & QA backbone — STATUS

Live tracker for the shared measurement/QA infra (App D). See [PLAN.md](PLAN.md).

## Current focus
- **2026-06-25 — doc-scaffolded (PLAN/STATUS written).** Implementation queued
  alongside App B: the first `measure_<app>.rs` targets B's construction-known
  property corpus (no external oracle needed), so D and B land together.
- Substrate already exists: `crates/axeyum-bench/examples/measure_corpus.rs`
  (axeyum-vs-shelled-binary, `run_z3` pattern, DISAGREE-gated) and the
  `audit_dominance` per-instance cert schema — D parameterizes these.

## Next actions (Phase 1, with B)
1. Generalize `measure_corpus.rs` into a parameterized harness (arbitrary SOTA
   binary + per-app corpus) emitting the DISAGREE/PAR-2/`evidence_certified`/
   `lean_checked` JSON schema.
2. Wire it to App B: a construction-known graduated property corpus →
   `docs/consumer-track/property/SCOREBOARD.md` via `gen-property-scoreboard.py`.
3. (later) EVM scoreboard vs hevm/halmos; Rust scoreboard vs Kani.

## Gates / discipline
DISAGREE = 0 is the asserted soundness floor in every scoreboard. Small curated
corpora only (never a 41GB sweep). Build caps; new-files-only.

## Changelog
- **2026-06-25** — PLAN/STATUS written; first harness queued with App B.
