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

North star: a **complete framework for general reasoning, logic, and
proving**. The finite-domain core being built now is the foundation layer of
that framework, not the destination — the expansion ladder runs through
arithmetic, theory combination, quantifiers, and proof production
(see [north-star](docs/research/00-orientation/north-star.md)).

Full framing: [docs/research/00-orientation/mission-and-scope.md](docs/research/00-orientation/mission-and-scope.md)

## Status

Last updated: 2026-06-10

- Phase: **Phase 0 complete; M0 (vertical slice) is next.**
- Git: on `main`, pushed to `github.com/mjbommar/axeyum`; CI green on GitHub
  (fmt, clippy, test, MSRV 1.85, rustdoc, cargo-deny; checkout@v5 for the
  Node 24 runner migration).
- Supporting scaffold: corpus tier directories (`corpus/micro|client`
  committed, `corpus/public` gitignored), dependabot (cargo + actions
  weekly), CHANGELOG, .editorconfig, CITATION.cff, PR template, justfile
  (`just check`), docs link checker (`scripts/check-links.sh`, also a CI
  job); 23 reference repos cloned locally (incl. proving horizon: cvc5,
  vampire, eprover, lean4, ethos, lean-smt, nanoda_lib).
- Public corpus fetcher works: `scripts/fetch-corpus.sh` (verified Zenodo
  sources — SMT-LIB 2024 QF_BV/QF_ABV, HWMCC'24 BTOR2, SAT Comp 2024 main);
  QF_ABV fetched and extracted locally (3.4 GB under `corpus/public/`).
- North star recorded 2026-06-10: complete framework for general
  reasoning/logic/proving — see
  [north-star](docs/research/00-orientation/north-star.md), the horizon
  ladder in logics-and-decidability, the roadmap's "Beyond Phase 7"
  markers, and the horizon section of the research-questions register.
  Key landscape facts: Vampire (BSD-3) swept CASC-30 2025; cvc5
  CPC/Eunoia/Ethos is the proof-production leader; nanoda is the Rust
  Lean-kernel precedent; no Rust superposition prover or general proof
  kernel exists — that gap is the opportunity.
- Workspace: `axeyum-ir` + `axeyum-solver` (per ADR-0001), edition 2024,
  MSRV 1.85, workspace lints (`unsafe_code` denied, clippy pedantic).
  fmt/clippy/test/doc all green locally; CI workflow defined
  (fmt, clippy, test, MSRV check, rustdoc, cargo-deny).
- Project metadata: README, CONTRIBUTING, CLAUDE.md, dual MIT/Apache-2.0
  licenses, deny.toml, rustfmt.toml.
- References: 13 solver/checker repos shallow-cloned into `references/`
  (gitignored; reproducible via `scripts/fetch-references.sh`).
- Decisions: [ADR-0001 vertical slice first](docs/research/09-decisions/adr-0001-vertical-slice-first.md)
  and [ADR-0002 ground-up identity, oracle as bootstrap](docs/research/09-decisions/adr-0002-ground-up-identity-oracle-bootstrap.md)
  both **accepted** 2026-06-10. ADR-0002 settles the Z3 question: the pure
  Rust stack (including a custom SAT core) is the product; the linked oracle
  is scaffolding with a planned demotion path (backend → differential
  oracle → CI cross-check).
- Ecosystem facts checked 2026-06-10: stable Rust 1.96; z3 crate 0.20
  removed the `'ctx` lifetime API; varisat unmaintained since 2019 (splr and
  rustsat are the maintained Rust SAT options).

## Next Actions

In order; check off and date as completed.

- [x] Review and accept (or amend) ADR-0001 — accepted 2026-06-10.
- [x] Initial commit of `docs/` + `PLAN.md` — 2026-06-10.
- [x] Phase 0: Cargo workspace skeleton (`axeyum-ir`, `axeyum-solver`),
      licenses, CI — 2026-06-10.
- [x] Push `main` to GitHub and confirm CI is green there — 2026-06-10.
- [x] Scaffolding complete — 2026-06-10. All pre-code work is done:
      infrastructure, metadata, documentation (37 research notes, 2 ADRs,
      north-star, LLM integration points), Cargo workspace, CI green,
      CLAUDE.md, corpus skeleton, 20 reference clones. **Everything below
      this line is implementation, not scaffolding** — deliberately deferred
      to the next working session.
- [x] **Milestone M0 (vertical slice) — 2026-06-10.** The ADR-0001 doctest
      passes: `x + 1 == 5` over `BV(8)` solves via `Z3Backend` and the
      ground evaluator confirms the lifted model. `axeyum-ir` has the M0
      operator subset, hash-consed arena, sort-checked builders, and the
      evaluator with exhaustive small-width tests; `axeyum-solver` has the
      trait, symbol-keyed models, and the feature-gated Z3 backend
      (`z3` = system libz3 via pkg-config, `z3-static` = hermetic prebuilt).
      Representation decisions in ADR-0003. All sat results in the test
      harness replay through the evaluator.
- [ ] **NEXT: Phase 1 (broaden the typed term core)** per the
      [roadmap](docs/research/08-planning/roadmap.md): full scalar QF_BV
      operator set with SMT-LIB edge-case semantics (sub/mul/div/rem,
      shifts, comparisons, extensions), pretty printer, exhaustive
      small-width evaluator coverage for the edge-case operators.
- [ ] Then follow the roadmap phase by phase; each phase has explicit
      exit criteria.

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
| `crates/` | Cargo workspace: `axeyum-ir`, `axeyum-solver`. |
| [CLAUDE.md](CLAUDE.md) | Agent guidance: session protocol, commands, hard rules. |
| [references/](references/README.md) | Gitignored reference clones; `scripts/fetch-references.sh`. |
