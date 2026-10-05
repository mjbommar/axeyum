# Lane: capability-pareto-roadmap — source-backed SMT capability programme

<!-- plan-section: lane-status -->

**Capability Pareto roadmap (`DONE` research; implementation `TODO`, 2026-09-05).**
The [source-backed programme](docs/plan/capability-pareto-2026-09-05/README.md)
pins September 5 main and current Z3/cvc5/Bitwuzla releases, corrects format/domain
coverage claims, and separates capability inclusion from measured and maintained
Pareto dominance. R0–R9 define dependencies, evidence, negative controls and exit
criteria; no fresh performance or dominance result is claimed. First follow-up:
reproduce optimizer cap/overflow-to-Unbounded behavior, then capability registry
and a version-pinned pilot. This research does not reorder accepted programmes or
resume paused CAS/full-corpus campaigns.

Merge validation against `39efad56c`: roadmap merge is conflict-free; generated
plan, repository links, whitespace, cargo formatting and all 2,012-file formatting
checks passed. Full `just check` was stopped during facts validation after the
existing main docs CI failure was identified; it is not a full-gate pass. The
Lean acceptance suite independently reproduced the same pre-existing frozen-input
drift in `lean-toolchain` and `scripts/install-pinned-lean.sh` (24 tests, one
failure, one skipped). Neither input is changed by this documentation merge.
