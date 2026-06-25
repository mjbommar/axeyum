# Measurement & QA backbone — PLAN

> **App D** (shared infra, not a user-facing app). The honesty gate for the whole
> track: every app commits a measured "vs SOTA" scoreboard + a **DISAGREE = 0**
> differential gate before claiming any capability number. Plus an *outward*
> differential bug-hunter that turns axeyum's soundness into a bug-finder for other
> tools. Full scoping: [02-research-synthesis §D](../02-research-synthesis.md).

## Goal (worked backwards)
Each consumer app (B/A/C) must be able to say "here is exactly how we stack up vs
the SOTA tool, on a committed corpus, with zero wrong verdicts" — the consumer-track
analogue of the solver `SCOREBOARD.md`. Worked backwards from: *no app claims "SOTA"
without a reproducible number and a soundness floor.*

## Two deliverables
1. **Per-app measured scoreboard.** A parameterized harness (generalize
   `crates/axeyum-bench/examples/measure_corpus.rs`): for each corpus item, record
   axeyum's verdict + solve seconds, the SOTA tool's verdict (shelling its binary,
   as `run_z3` does), **agreement, `DISAGREE` (asserted 0)**, PAR-2, and —
   reusing the `audit_dominance` schema — `evidence_certified` / `lean_checked` /
   `trust_holes`. Emit deterministic JSON → a committed
   `docs/consumer-track/<app>/SCOREBOARD.md` via a `gen-<app>-scoreboard.py`.
   - **Per-app corpus/metric (NOT SV-COMP — it's C/reachability, off-mission):**
     - **B (SDK):** construction-known graduated property corpus (the
       `measure_graduated.rs` no-oracle trick); metric = proved-rate + **fraction of
       `Proved` with a verified Lean cert** + CE-found rate.
     - **A (EVM):** SWC registry + halmos examples + overflow micro-contracts; metric
       = bugs/safe vs **hevm/halmos**; differentiator = **proofs carried**.
     - **C (Rust):** Kani's `tests/` (integer/array fragment); metric = fns decided
       agreeing with **Kani** + cert-coverage.
2. **Outward differential bug-hunter.** Generalize the five existing z3-gated
   adversarial fuzzes: a generator emits random instances in a domain (random
   property closures / EVM snippets); run **axeyum (sound, cert-backed)** vs a
   **fast-but-unproven tool** (a fuzzer / halmos / a competing solver). **Any
   disagreement where axeyum carries a re-checked certificate = a bug in the other
   tool or its model** (the asymmetry is the point). Output: a triage record
   (instance, both verdicts, axeyum's cert/model).

## Why tractable
`measure_corpus.rs` + `audit_dominance` already do ~all of the per-instance
verdict/cert/PAR-2 mechanics and the `run_z3`-style external-binary shell; D
parameterizes them over an arbitrary SOTA binary and a per-app corpus. The outward
harness reuses the differential-fuzz infrastructure.

## Phases
- **Phase 1:** the parameterized `measure_<app>.rs` (axeyum verdict + shelled SOTA
  verdict + DISAGREE/PAR-2/cert JSON) + `gen-<app>-scoreboard.py`; wire it to **B**
  first (construction-known corpus, no external oracle needed).
- **Phase 2:** EVM scoreboard vs hevm/halmos; Rust scoreboard vs Kani (shell their
  binaries); commit the corpora (small, curated; never a 41GB sweep).
- **Phase 3:** the outward differential bug-hunter + a triage log.

## Success criteria
- Each app ships a committed `SCOREBOARD.md` with **DISAGREE = 0** and a stated
  metric vs a named SOTA tool, regenerable by a committed script.
- The outward harness produces at least a reproducible disagreement-triage format
  (a found-bug-in-tool is gravy, not required).

## Coordination
New `axeyum-bench` examples + new `gen-*` scripts + new `docs/consumer-track/*` —
all additive, consumer-track worktree. Reuses the existing harness patterns; no core
edits.
