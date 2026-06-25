# Measurement & QA backbone — STATUS

Live tracker for the shared measurement/QA infra (App D). See [PLAN.md](PLAN.md).

## Current focus
- **2026-06-25 — Phase 1 landed: the self-contained property scoreboard.** A new
  crate `crates/axeyum-consumer-bench` runs a **construction-known** bounded-property
  corpus through the App-B `axeyum-property` SDK and emits a committed, regenerable
  [`docs/consumer-track/property/SCOREBOARD.md`](../property/SCOREBOARD.md) with a
  hard **DISAGREE = 0** soundness floor. No external oracle is needed: each property
  is authored with its true status (`should-prove` / `should-find-ce`), the pure-Rust
  analogue of the `:status` trick in `measure_graduated.rs`.
  - **Aggregate (current run):** 17 cases — **12 proved (70.6%)**, **5 counterexample
    (29.4%)**, **0 unknown**, all 12 proved certs **re-verified (12/12)**,
    **Lean-cert coverage 1/12 (8.3%)**, **DISAGREE = 0**.
  - **Harness API** (lib + binary):
    - `corpus() -> Vec<Case>` — the construction-known corpus (each `Case` carries a
      `name`, `description`, `status`, and a `run: fn() -> RunOutcome` closure that
      decides the property through the SDK with the Lean-cert attempt on).
    - `run_corpus(&cases) -> (Vec<CaseResult>, Aggregate)` — runs all cases, records
      verdict + solve time + `Certificate::verify()` re-check + `to_lean_module()`
      presence, and counts any contradiction into `Aggregate::disagree`.
    - `render_scoreboard(&rows, &agg, include_timing) -> String` — deterministic
      markdown (timing-free for the committed file).
    - `ExternalOracle { binary, args }` with `::z3(timeout)`, `is_available()`,
      `run(path)` — the parameterized `run_z3`-style "shell a SOTA binary" seam, ready
      for the per-app vs-SOTA scoreboards; returns `None` (no row) when the tool is
      absent — never a faked verdict.
    - Binary `axeyum-consumer-bench [--check] [out.md]`: regenerates (or `--check`
      verifies) the scoreboard and **panics if DISAGREE != 0** (doubles as a gate).
  - **Regenerator:** `scripts/gen-property-scoreboard.py` (`--check` for CI).
  - **Gate status:** `cargo test -p axeyum-consumer-bench` green (7 integration
    tests); `cargo fmt` + `cargo clippy --all-targets -- -D warnings` (pedantic)
    clean; `#![forbid(unsafe_code)]`.

## Install-gated (NOT delivered, NOT faked)
The per-app "vs SOTA decide-rate" scoreboards require external binaries that are
**not installed** here, and the network is **offline** (no fetch possible). These
are deliberately left undone rather than fabricated:
- **A (EVM) vs hevm / halmos** — neither binary present.
- **C (Rust) vs Kani** — `kani` not present.
- **z3** *is* installed (`/usr/bin/z3`) and is wired as an optional cross-check via
  `ExternalOracle::z3(..)`, but App B's construction-known corpus already carries its
  own ground truth, so z3 is not on the critical path for the property scoreboard.

What ships now: the self-contained property scoreboard (above) + each app's own
soundness oracle (the SDK's re-checked `Certificate`). The `ExternalOracle` seam means
a future vs-hevm/halmos/Kani run drops in by constructing one oracle and adding the
per-instance compare/DISAGREE accounting — no harness rewrite.

## Next actions
1. **Phase 2 (when tools available):** per-app corpora + `ExternalOracle`-driven
   `measure_<app>` runs vs hevm/halmos (A) and Kani (C); commit small curated corpora
   only (never a 41GB sweep).
2. **Lean-cert coverage:** 8.3% reflects the SDK's shape-sensitive QF_BV Lean
   reconstructor (filed in `../property/STATUS.md`). As the reconstructor's fragment
   widens, coverage on this corpus rises automatically — the scoreboard re-measures it.
3. **Phase 3:** the outward differential bug-hunter (random property closures vs a
   fast-but-unproven tool; any disagreement where axeyum carries a re-checked cert is
   a bug in the other tool) + a triage log.

## Gates / discipline
DISAGREE = 0 is the asserted soundness floor in every scoreboard (the binary panics
otherwise). Small curated corpora only. Build caps (`-j4` + `scripts/mem-run.sh`);
new-files-only (a new crate, additive workspace member, the two docs, the regenerator).

## Changelog
- **2026-06-25** — Phase 1: `axeyum-consumer-bench` crate + construction-known
  property corpus + committed `property/SCOREBOARD.md` (DISAGREE = 0) +
  `gen-property-scoreboard.py`. vs-hevm/halmos/Kani recorded as install-gated.
- **2026-06-25** — PLAN/STATUS written; first harness queued with App B.
