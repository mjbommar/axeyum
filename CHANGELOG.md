# Changelog

All notable changes to this project will be documented in this file.
Format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/);
versioning follows [SemVer](https://semver.org/) (pre-1.0: minor versions
may break APIs; evidence artifact formats are versioned independently —
see `docs/research/06-rust-strategy/api-design-concurrency-and-stability.md`).

## [Unreleased]

### Added

- **Phase 1 (typed term core):** full scalar QF_BV operator set — signed and
  unsigned division/remainder/modulo, shifts (over-shift saturating),
  all comparisons, nand/nor/xnor/comp, zero/sign extension, rotates (build-
  time normalized), implication — with SMT-LIB-exact edge-case semantics;
  SMT-LIB-style pretty printer (`axeyum_ir::render`); exhaustive
  small-width evaluator tests; and a differential test suite in which Z3
  confirms the evaluator on every input for every operator.

- **Milestone M0 (vertical slice, ADR-0001):** `axeyum-ir` typed term core
  (Bool/BV sorts, hash-consed arena, sort-checked builders for the M0
  operator subset, ground evaluator with exhaustive small-width tests) and
  `axeyum-solver` (backend trait, `Unknown`-first results, symbol-keyed
  models, feature-gated Z3 oracle backend with conformance tests). Every
  `sat` result replays through the trusted evaluator. ADR-0003 records the
  representation choices (u128-backed BV constants, width cap 128).

- Research foundation: 36 notes under `docs/research/` plus the ADR process
  (`09-decisions/`); ADR-0001 (vertical slice first) and ADR-0002 (ground-up
  identity, oracle as bootstrap scaffolding) accepted.
- Workspace scaffold: `axeyum-ir`, `axeyum-solver` (edition 2024, MSRV 1.85),
  CI (fmt, clippy, test, MSRV, rustdoc, cargo-deny), dual MIT/Apache-2.0
  licensing, contributor and agent guidance (`CONTRIBUTING.md`, `CLAUDE.md`).
- Test corpus skeleton under `corpus/` and reference-clone tooling
  (`scripts/fetch-references.sh`).
- North-star orientation: the long-horizon goal (general reasoning, logic,
  proving) recorded in `docs/research/00-orientation/north-star.md`, with
  the horizon ladder, roadmap markers, and proving-layer reference clones
  (cvc5, Vampire, E, Lean 4).
