# UF (quantified uninterpreted functions) curated slice (cvc5 regress)

First **UF** (quantified EUF — files carry `forall`/`exists`) head-to-head of
the high-level `axeyum_solver::check_auto` dispatcher (`--backend solver`)
against Z3 4.13.3. This opens the **quantified** category on the scoreboard
alongside its sibling slices `quantified/BV` and `quantified/LIA`.

## Why this slice is all-`unsupported` (an honest skip)

Quantified solving is not yet wired through axeyum's BV backend, so every
quantified file declines cleanly as `Unsupported` (never a wrong verdict). For
this UF slice the decline happens even earlier, at sort modeling: the files use
uninterpreted **sorts** that the front end does not model —

- special/synthetic sorts emitted by the SMT-LIB front end (`i_`, `sort__smt2`,
  `$$unsorted`), and
- a **parametric / arity-1** declared sort (`(declare-sort GrassArray 1)`):
  only arity-0 uninterpreted sorts are modeled (as a fixed-width `BitVec`).

So the front end declines at the sort layer before the quantifier path is even
reached. The division is **opened and measured** (DISAGREE 0 vacuously, no wrong
verdict); the quantifier-instantiation path is the tracked follow-up.

## Provenance

Files are reused from the cvc5 regression suite
(`references/cvc5/test/regress`, a shallow sparse clone — `references/` is
gitignored). bitwuzla's regress root yields **0** exact-`UF` clean files. Each
vendored file's name flattens its original `test/regress/...` path (`/` → `__`).

## Selection criteria

Same clean, parser-faithful, status-annotated filter as the other slices
(`scripts/curate-public-slice.py UF <out>`): exact `(set-logic UF)`, a
`(set-info :status …)` ground truth, plain `(assert …)` + `(check-sat)` only,
not `.smtv1`-derived, no incremental/exotic commands, at least one `assert`. The
exact-`UF` match yields **5** clean files (all 5 contain `forall`/`exists`).
`:status` distribution: 3 sat, 2 unsat.

## Measured head-to-head (5 files)

`bench-results/baselines/uf-cvc5-regress-clean-quantified-solver-vs-z3-10s.json`,
`--logic UF --backend solver --compare-z3 --timeout-ms 10000 --jobs 4`:

- **files 5** — decided **0** (sat 0, unsat 0), unknown 0, unsupported **5**,
  errors 0.
- Oracle: **compared 0, agree 0, DISAGREE 0** — nothing to compare (all
  unsupported), but no wrong verdict was emitted.
- PAR-2 mean ~ 0.0 s; max axeyum solve < 1 ms (declines at the front end before
  any solve runs).

## Dominant blocker (all 5 `unsupported`)

**Uninterpreted-sort modeling** — synthetic front-end sorts (`i_`, `sort__smt2`,
`$$unsorted`) and an arity-1 parametric sort (`GrassArray`). Closing the gap
(parametric/special sort handling, then the quantifier path) is a solver-source
change, out of scope for corpus curation. All 5 decline cleanly as
`Unsupported`.
