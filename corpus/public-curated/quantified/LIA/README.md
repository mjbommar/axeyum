# LIA (quantified linear integer arithmetic) curated slice (cvc5 regress)

First **LIA** (quantified linear integer arithmetic — files carry
`forall`/`exists`) head-to-head of the high-level
`axeyum_solver::check_auto` dispatcher (`--backend solver`) against Z3 4.13.3.
Part of the **quantified** category (`quantified/UF`, `quantified/BV`,
`quantified/LIA`).

## Why this slice is all-`unsupported` (an honest skip)

The quantifiers `forall`/`exists` are parsed faithfully into the typed IR, but
the pure-Rust BV backend declines them: every file reports *"term #N uses
unsupported pure-Rust BV operator `Forall(...)`"* (or `Exists(...)`). No
quantifier-instantiation / e-matching / MBQI search is wired through the backend
yet, so the formula is never decided — and therefore no wrong verdict is
possible. The division is **opened and measured** (DISAGREE 0 vacuously); the
instantiation path is the tracked follow-up.

## Provenance

Files are reused from the cvc5 regression suite
(`references/cvc5/test/regress`, a shallow sparse clone — `references/` is
gitignored). bitwuzla's regress root yields **0** exact-`LIA` clean files. Each
vendored file's name flattens its original `test/regress/...` path (`/` → `__`).

## Selection criteria

Same clean, parser-faithful, status-annotated filter as the other slices
(`scripts/curate-public-slice.py LIA <out>`): exact `(set-logic LIA)`, a
`(set-info :status …)` ground truth, plain `(assert …)` + `(check-sat)` only,
not `.smtv1`-derived, no incremental/exotic commands, at least one `assert`. The
exact-`LIA` match yields **12** clean files (all 12 contain `forall`/`exists`).
`:status` distribution: 4 sat, 8 unsat.

## Measured head-to-head (12 files)

`bench-results/baselines/lia-cvc5-regress-clean-quantified-solver-vs-z3-10s.json`,
`--logic LIA --backend solver --compare-z3 --timeout-ms 10000 --jobs 4`:

- **files 12** — decided **0** (sat 0, unsat 0), unknown 0, unsupported **12**,
  errors 0.
- Oracle: **compared 0, agree 0, DISAGREE 0** — nothing to compare (all
  unsupported), but no wrong verdict was emitted.
- PAR-2 mean = 240 s by the harness's unsupported-as-2×timeout convention; the
  actual max axeyum solve is ~ 1 ms (the `Forall` operator is rejected at
  lowering, before any search).

## Dominant blocker (all 12 `unsupported`)

**The quantifier operator itself** — `Forall`/`Exists` is an unsupported
pure-Rust BV operator. Wiring a quantifier-instantiation path (finite
instantiation, e-matching, or MBQI) is a solver-source change, out of scope for
corpus curation. All 12 decline cleanly as `Unsupported`.
