# QF_AUFLIA curated slice (cvc5 regress)

First **QF_AUFLIA (arrays + uninterpreted functions + linear integer
arithmetic)** head-to-head of the high-level `axeyum_solver::check_auto`
dispatcher (`--backend solver`) against Z3 4.13.3.

## What gets measured, and what does not

Like QF_ALIA, QF_AUFLIA arrays are **`Int`**-indexed/valued (`(Array Int Int)`
and friends), which axeyum cannot model -- it supports only
**bit-vector-indexed/valued arrays** (`eliminate_arrays` is QF_ABV, ADR-0010),
and the built-in unbounded `Int` sort has no finite bit-width abstraction. So
every array-bearing file declines with *"only bit-vector-indexed/valued arrays
are supported"*. The slice is **not** entirely unsupported, though: one file
declares `QF_AUFLIA` but uses no arrays/Int at all (Boolean UF only), and that
one routes to the supported core and decides.

## Provenance

Files are reused from the cvc5 regression suite
(`references/cvc5/test/regress`, a shallow sparse clone -- `references/` is
gitignored). bitwuzla's regress root yields **0** exact-`QF_AUFLIA` clean files
(its array tests are BV-indexed). Each vendored file's name flattens its
original `test/regress/...` path (`/` -> `__`).

## Selection criteria

Same clean, parser-faithful, status-annotated filter as the other slices
(`scripts/curate-public-slice.py QF_AUFLIA <out> --root references/cvc5/test/regress`):
exact `(set-logic QF_AUFLIA)`, a `(set-info :status ...)` ground truth, plain
`(assert ...)` + `(check-sat)` only, not `.smtv1`-derived, no incremental/exotic
commands, at least one `assert`. The exact-`QF_AUFLIA` match yields **7** clean
files. No file required a *measurement* (timeout) exclusion.

## Measured head-to-head (7 files)

`bench-results/baselines/qf-auflia-cvc5-regress-clean-solver-vs-z3-10s.json`,
`--logic QF_AUFLIA --backend solver --compare-z3 --timeout-ms 10000 --jobs 4`:

- **files 7** -- decided **1** (sat **1**, unsat 0), unknown 0,
  unsupported **6**, errors 0.
- Oracle: **compared 1, agree 1, DISAGREE 0** -- the one decided verdict
  (`cli__regress0__uf__issue4446.smt2`, a Boolean-UF `sat`) matches both Z3 and
  the `:status` annotation.
- PAR-2 mean ~ 0.0002 s (the decided file solves in well under a ms; the 6
  unsupported files decline immediately at the front end, so no timeout penalty
  accrues).

This holds QF_AUFLIA as a measured division with **DISAGREE 0**; no soundness
disagreement surfaced.

## Dominant blocker (the 6 `unsupported`)

**`Int`-indexed/valued arrays** -- `(Array Int Int)` etc. decline with *"only
bit-vector-indexed/valued arrays are supported"*. Closing the gap (an `Int`-array
model, or an Int-to-BV abstraction with range reasoning) is a solver-source
change, out of scope for corpus curation. All 6 decline cleanly as `Unsupported`
(never a wrong verdict).
