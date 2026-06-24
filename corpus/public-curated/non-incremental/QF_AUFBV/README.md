# QF_AUFBV curated slice (cvc5 + bitwuzla regress)

First **QF_AUFBV (arrays + uninterpreted functions + bit-vectors)** head-to-head
of the high-level `axeyum_solver::check_auto` dispatcher (`--backend solver`)
against Z3 4.13.3.

## Why this division decides well

Unlike the abstract-sort array logics (QF_AX/QF_ALIA/QF_AUFLIA), QF_AUFBV arrays
are already bit-vector-indexed/valued, which is exactly the shape the
read-over-write + Ackermann array elimination (`eliminate_arrays`, QF_ABV,
ADR-0010) handles, and the UF symbols are eagerly Ackermannized over the BV
theory (the QF_UFBV path). So most of this slice lands on the supported core and
decides; this is the richest of the three array-combination divisions measured
here.

## Provenance

Files are reused from the cvc5 (`references/cvc5/test/regress`) and bitwuzla
(`references/bitwuzla/test/regress`) regression suites — shallow sparse clones;
`references/` is gitignored. bitwuzla is the array-rich source (44 clean files);
cvc5 yields 9. Each vendored file's name flattens its original
`test/regress/...` path (`/` -> `__`).

## Selection criteria

Same clean, parser-faithful, status-annotated filter as the other slices
(`scripts/curate-public-slice.py QF_AUFBV <out> --root <regress root>`): exact
`(set-logic QF_AUFBV)`, a `(set-info :status ...)` ground truth, plain
`(assert ...)` + `(check-sat)` only, not `.smtv1`-derived, no incremental/exotic
commands, at least one `assert`. The exact-`QF_AUFBV` match yields **9** clean
cvc5 files and **44** clean bitwuzla files. No file required a *measurement*
(timeout) exclusion.

## Measured head-to-head

`--logic QF_AUFBV --backend solver --compare-z3 --timeout-ms 10000 --jobs 4`.
The in-repo `z3` *library* oracle declines array symbols, so the head-to-head
uses the **Z3 4.13.3 binary** at `/usr/bin/z3`.

### `cvc5-regress-clean` (9 files)

`bench-results/baselines/qf-aufbv-cvc5-regress-clean-solver-vs-z3-10s.json`:

- **files 9** -- decided **5** (sat **5**, unsat 0), unknown **1**,
  unsupported **3**, errors 0.
- Oracle: **compared 5, agree 5, DISAGREE 0** -- every decided verdict matches
  both Z3 and the `:status` annotation.
- PAR-2 mean ~ 3.3 s -- the unknown/unsupported PAR-2 penalty (each unsolved file
  scored at 2x the 10 s timeout); every solved file decides in a few ms.

### `bitwuzla-regress-clean` (44 files)

`bench-results/baselines/qf-aufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json`:

- **files 44** -- decided **41** (sat **21**, unsat **20**), unknown 0,
  unsupported **3**, errors 0.
- Oracle: **compared 41, agree 41, DISAGREE 0** -- every decided verdict matches
  both Z3 and the `:status` annotation.
- PAR-2 mean ~ 2.0 s.

Both slices hold QF_AUFBV as a measured division with **DISAGREE 0**; no
soundness disagreement surfaced.

## Dominant blockers

- **cvc5 (3 unsupported + 1 unknown):**
  - 2 `unsupported` -- non-BV array sorts (`only bit-vector-indexed/valued arrays
    are supported`).
  - 1 `unsupported` -- the `eqrange` operator (an array-segment-equality operator
    not yet in the front-end operator table).
  - 1 `unknown` -- `EncodingBudget`: the estimated CNF clause count before
    lowering exceeds the budget (an oversized-encoding guard, never a wrong
    verdict).
- **bitwuzla (3 unsupported):** all three are the **bounded-extensionality
  index-width cap** -- *"array equality over a 32-bit index (bounded
  extensionality supports indices up to 8 bits)"*; a wider/unbounded
  extensionality route is the tracked array follow-up (an
  `axeyum-solver`/`axeyum-rewrite` change, out of scope for corpus curation).

All decline cleanly as `Unsupported`/`Unknown` (never a wrong verdict).
