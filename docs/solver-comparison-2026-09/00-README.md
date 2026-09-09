# Reference-solver comparison and gap analysis (2026-09-09)

A source-level inventory of the SAT/SMT solvers this project measures itself
against, filled against one fixed schema so the results compose into a gap
analysis. Companion to [`docs/solver-inventory-2026-09/`](../solver-inventory-2026-09/00-README.md),
which inventories our own stack; this folder is the other half of the comparison.

Nothing here was built. These are large C, C++, Java and Rust codebases;
building z3 or cvc5 takes hours and would take the development machine down.
Every claim is a source read with a `path:line` citation into `references/`.

## Reference clone provenance

`references/` is gitignored and repopulated by `scripts/fetch-references.sh`,
so the clones move. These are the exact commits every file in this folder was
read against. All are shallow (`--depth 1`).

| Repository | Commit | Last commit date | Size |
|---|---|---|---|
| abc | `fbaae0148` | 2026-09-05 | 56M |
| aiger | `039ec1a2c` | 2026-01-08 | 1.8M |
| bitwuzla | `a5e6e8a7a` | 2026-09-04 | 51M |
| boolector | `43dae91c1` | 2024-08-23 | 27M |
| cadical | `c60730422` | 2026-07-19 | 6.0M |
| carcara | `6624ea80c` | 2026-08-12 | 522M |
| cryptominisat | `7ae1b4a74` | 2026-09-02 | 7.0M |
| cvc5 | `1689f1333` | 2026-09-03 | 102M |
| drat-trim | `2e3b2dc0e` | 2024-11-25 | 15M |
| kissat | `8af8e56f1` | 2025-10-16 | 4.7M |
| lean4 | `d024af099` | 2026-05-02 | 2.7M |
| mata | `e8c9310e3` | 2026-08-19 | 15M |
| minisat | `37dc6c67e` | 2013-09-25 | 544K |
| opensmt | `15b42c6f3` | 2025-12-06 | 13M |
| smtinterpol | `1f55c1b9b` | 2026-06-12 | 35M |
| splr | `90fa3ad3e` | 2026-08-22 | 2.4M |
| stp | `e4af105c0` | 2026-09-08 | 26M |
| varisat | `33e876937` | 2022-11-02 | 1.4M |
| yices2 | `728b7eebd` | 2026-09-08 | 88M |
| z3 | `e18d63bda` | 2026-09-08 | 46M |
| z3-noodler | `1ffd452c3` | 2026-09-07 | 50M |

Eight of these (cryptominisat, minisat, z3-noodler, mata, varisat, opensmt,
smtinterpol, splr) were added on 2026-09-09 for this comparison; the rest were
already present.

Two dates are worth noting before anyone reads a staleness signal into them:
`minisat` last moved in 2013 and `boolector` in 2024 because both are finished
projects, not neglected ones — Boolector's line continues as Bitwuzla.
`varisat`'s 2022 date is relevant to CLAUDE.md's claim that it is "effectively
unmaintained (last release 2019)"; the clone's last *commit* is 2022-11-02,
which is a different measurement from a release.

## The schema

Every lane fills the same sixteen axes in the same order, so a reader can slice
the comparison by axis rather than by solver:

| # | Axis | # | Axis |
|---|---|---|---|
| A | Input front end | I | Model production |
| B | **Preprocessing** (before search) | J | Proof / certificate production |
| C | Core SAT engine | K | Proof checking |
| D | **Inprocessing** (during search) | L | Interpolation |
| E | Encoding / bit-blasting | M | Optimization |
| F | Theory solvers | N | Incrementality |
| G | Theory combination | O | Parallelism |
| H | Quantifiers | P | Resource limits and determinism |

Each file also carries two required tables — "they have, we do not" and "we
have, they do not" — plus a "not comparable" section, because a
feature-by-feature table between systems with different architectures is the
easiest way to produce a confident wrong answer.

## The files

| File | Subjects | Why this pairing |
|---|---|---|
| [01-cadical-kissat.md](01-cadical-kissat.md) | CaDiCaL, Kissat | The reference for CDCL and, more importantly for us, for inprocessing |
| [02-z3.md](02-z3.md) | Z3 | Our differential oracle; the tactic framework is the sharpest contrast with our hardcoded pipelines |
| [03-cvc5.md](03-cvc5.md) | cvc5 | Strings and quantifiers leader; emits Alethe, the format we emit; source of our vendored corpus |
| [04-bitwuzla-boolector-stp.md](04-bitwuzla-boolector-stp.md) | Bitwuzla, Boolector, STP | The most directly comparable lane — QF_BV/ABV by bit-blasting is our core and default profile |
| [05-yices-opensmt-smtinterpol.md](05-yices-opensmt-smtinterpol.md) | Yices2, OpenSMT, SMTInterpol | Exact simplex and interpolation, two things we built and cannot currently evaluate |
| [06-cryptominisat-and-rust-sat.md](06-cryptominisat-and-rust-sat.md) | CryptoMiniSat, MiniSat, varisat, splr | XOR/Gaussian reasoning, and where our native Rust core sits in its field |
| [07-z3-noodler-and-mata.md](07-z3-noodler-and-mata.md) | Z3-Noodler, Mata | The automata-based approach to strings, opposite to our derivative-based one |
| [08-proof-checking-ecosystem.md](08-proof-checking-ecosystem.md) | Carcara, drat-trim, Lean 4 | The trusted-checking half of "untrusted fast search, trusted small checking" |
| [09-abc-and-aiger.md](09-abc-and-aiger.md) | ABC, AIGER | What a mature AIG layer does beyond being an intermediate representation |
| [10-gap-analysis.md](10-gap-analysis.md) | — | The synthesis: ranked gaps, by axis, with effort and evidence |
| [11-roadmap-and-plan.md](11-roadmap-and-plan.md) | — | The plan: four phases ordered by value ÷ cost, each item with a falsifiable exit criterion |

## How to read the gap analysis

It is written backwards from the question "what would we have to build." A gap
is only listed if both sides are cited: what they do, and what we do or do not.
Gaps are ranked by what they cost us today, not by how interesting they are to
implement.
