# Axeyum — Master Plan And Status

This is the single entry point for starting or resuming work. Read this file
first; it tells you what the project is, where it stands, what to do next, and
where everything else lives. Update the **Status** and **Next Actions**
sections at the end of every working session.

## What Axeyum Is

A Rust-first automated reasoning stack: typed term IR → rewriting → query
planning → solver backends (native SMT oracles + a growing pure Rust
bit-blast-to-SAT path) → models, proofs, and checkable evidence.

Identity in one sentence: **untrusted fast search, trusted small checking.**
Every `sat` gets a model checked by evaluation; every `unsat` eventually gets
a proof artifact or an independent oracle cross-check.

Full framing: [docs/research/00-orientation/mission-and-scope.md](docs/research/00-orientation/mission-and-scope.md)

## Status

Last updated: 2026-06-10

- Phase: **pre-code**. Research documentation only; no Cargo workspace yet.
- Git: no commits yet; `docs/` and this file are untracked.
- Research tree complete at `docs/research/` — 35 notes across orientation,
  foundations, ecosystems, architecture, data structures, algorithms, Rust
  strategy, verification, planning, and decisions.
- Decision process exists: [docs/research/09-decisions/](docs/research/09-decisions/README.md).
- One proposed (not yet accepted) decision:
  [ADR-0001 vertical slice first](docs/research/09-decisions/adr-0001-vertical-slice-first.md).

## Next Actions

In order; check off and date as completed.

- [ ] Review and accept (or amend) ADR-0001 — it sets the build order.
- [ ] Initial commit of `docs/` + `PLAN.md`.
- [ ] Phase 0: Cargo workspace skeleton (`axeyum-ir`, `axeyum-solver`),
      license, CI (fmt, clippy, test).
- [ ] Milestone M0 (vertical slice): IR subset + arena + sort checking +
      ground evaluator + solver trait + Z3 feature backend + model
      check-by-evaluation. Done when the doctest in ADR-0001 passes:
      `x + 1 == 5` over `BV(8)` solves via Z3 and the evaluator confirms the
      lifted model.
- [ ] Then follow the [roadmap](docs/research/08-planning/roadmap.md)
      phase by phase; each phase has explicit exit criteria.

## How To Resume Work (for a human or an agent)

1. Read **Status** and **Next Actions** above.
2. Read the [roadmap](docs/research/08-planning/roadmap.md) for the current
   phase and its exit criteria.
3. Before changing architecture, check
   [open questions](docs/research/08-planning/research-questions.md) and
   [decision records](docs/research/09-decisions/README.md) — decisions close
   as ADRs, not as silent code choices.
4. New research notes start from
   [templates/research-note.md](docs/research/templates/research-note.md).
5. When a session ends: update **Status**, re-order **Next Actions**, and
   note any new ADRs here.

## Standing Rules

- The pure Rust core builds with no C/C++ dependency; native backends
  (Z3, Bitwuzla) are feature-gated leaf crates.
- Every transformation layer ships with its check (evaluator equivalence,
  round trips, lift maps) and a differential test once an oracle exists.
- Expensive bets are gated by the
  [benchmarking methodology](docs/research/08-planning/benchmarking-and-performance-methodology.md)
  — no custom CDCL core until its gate fires.
- `unknown` is a first-class result. Determinism (same input, same seed, same
  output) is a public API promise.

## Map

| Where | What |
|---|---|
| [docs/research/README.md](docs/research/README.md) | Research index and reading order. |
| [docs/research/08-planning/roadmap.md](docs/research/08-planning/roadmap.md) | Phased plan with exit criteria and gates. |
| [docs/research/08-planning/research-questions.md](docs/research/08-planning/research-questions.md) | Open question register. |
| [docs/research/09-decisions/](docs/research/09-decisions/README.md) | ADRs: how questions get closed. |
| `crates/` | (future) Cargo workspace. |
