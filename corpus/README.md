# Corpus

Benchmark and regression corpora, organized by the tiers defined in
[docs/research/08-planning/benchmarking-and-performance-methodology.md](../docs/research/08-planning/benchmarking-and-performance-methodology.md).

| Directory | Tier | Committed? |
|---|---|---|
| `micro/` | Hand-written op-level cases and minimized regression fixtures. | Yes — every differential-testing failure gets minimized and stored here. |
| `client/` | Minimized queries captured from real frontends. | Yes, with source noted. |
| `public/` | SMT-LIB QF_BV/QF_ABV sets, SAT Competition CNF, HWMCC BTOR2. | No — gitignored; fetched by script (to be added) with corpus name and file hash recorded in results artifacts. |

Conventions:

- Formats: SMT-LIB 2 (`.smt2`), DIMACS (`.cnf`), AIGER (`.aag`/`.aig`),
  BTOR2 (`.btor2`).
- Every committed file carries a header comment: origin, expected result
  (sat/unsat if known), and the bug or behavior it pins down.
- Keep committed files minimized; large unminimized failures do not land.
