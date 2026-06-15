# references/ — distilled top-down review of the reference solvers

These are the research findings the plan is built on: a top-down review of the
cloned reference projects in the repo-root `references/` directory (gitignored;
repopulate with `scripts/fetch-references.sh`). Produced 2026-06-15 by five
parallel Opus sub-agents.

| File | Covers | Source repos read |
|---|---|---|
| [`z3-core.md`](z3-core.md) | Z3 architecture, CDCL SAT core, DPLL(T)/new EUF core, preprocessing/tactics, strategy selection | `references/z3/src/{sat,smt,ast,tactic,solver}` |
| [`z3-theories.md`](z3-theories.md) | Z3 per-theory solvers (BV, arrays, EUF, arithmetic, FP, datatypes) + quantifiers; the eager→lazy gap | `references/z3/src/{smt/theory_*,sat/smt,ast/euf,math/lp,nlsat,qe}` |
| [`bitwuzla-and-sat.md`](bitwuzla-and-sat.md) | bitwuzla (closest BV-SMT analog) + its PBLS engine; CaDiCaL/Kissat techniques; Rust SAT landscape | `references/{bitwuzla,cadical,kissat,varisat,splr,batsat}` |
| [`proof-and-lean.md`](proof-and-lean.md) | proof-format landscape, Alethe+Carcara (Rust target), Lean kernel + nanoda, lean-smt bridge, per-reduction obligations | `references/{carcara,lean4,nanoda_lib,lean-smt,cvc5,drat-trim}` |
| [`axeyum-current-state.md`](axeyum-current-state.md) | honest audit of what axeyum has today: crates, capabilities/assurance, eager-vs-lazy, performance numbers, proof status, top-10 gaps | this repo |

## Reference repo sizes (counted 2026-06-15)

- Z3 `src/`: ~687,600 lines C/C++ across 2,051 files.
- cvc5 `src/`: ~511,900 lines C++.
- bitwuzla `src/`: ~88,900 lines C++.
- Carcara: ~27k lines Rust (the Rust-native Alethe checker — fits the no-C/C++ rule).
- nanoda_lib: ~9k lines Rust (~6k kernel — the in-tree Lean-kernel template).
- axeyum `crates/`: ~63k lines Rust (this repo).

## How to use these

When a plan task says "ref: `references/z3/src/sat/sat_simplifier.cpp`", that path
is exact and clickable after `scripts/fetch-references.sh`. The distillations
below name the specific files, algorithms, and data structures to read so you are
not searching a half-million-line codebase blind.
