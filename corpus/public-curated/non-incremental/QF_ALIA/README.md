# QF_ALIA curated slice (cvc5 regress)

First **QF_ALIA (arrays + linear integer arithmetic)** head-to-head of the
high-level `axeyum_solver::check_auto` dispatcher (`--backend solver`) against
Z3 4.13.3.

## Why this slice is all-`unsupported` (an honest skip)

QF_ALIA arrays are indexed and valued by **`Int`** (`(Array Int Int)`,
`(Array Int Bool)`, etc.). axeyum only supports **bit-vector-indexed/valued
arrays** (`eliminate_arrays` is QF_ABV, ADR-0010), and -- unlike the abstract
arity-0 `(declare-sort U 0)` sorts of QF_AX, which the front end models as a
fixed-width `BitVec` -- the built-in unbounded `Int` index/element sort has no
finite bit-width abstraction, so every file declines with *"only
bit-vector-indexed/valued arrays are supported"*. The whole clean slice is
therefore `unsupported`. This is reported honestly: the division is **opened and
measured** (DISAGREE 0 vacuously, no wrong verdict), and the front-end gap
(Int-indexed arrays) is the tracked follow-up.

## Provenance

Files are reused from the cvc5 regression suite
(`references/cvc5/test/regress`, a shallow sparse clone -- `references/` is
gitignored). bitwuzla's regress root yields **0** exact-`QF_ALIA` clean files
(its array tests are BV-indexed: `QF_ABV`/`QF_AUFBV`). Each vendored file's name
flattens its original `test/regress/...` path (`/` -> `__`).

## Selection criteria

Same clean, parser-faithful, status-annotated filter as the other slices
(`scripts/curate-public-slice.py QF_ALIA <out> --root references/cvc5/test/regress`):
exact `(set-logic QF_ALIA)`, a `(set-info :status ...)` ground truth, plain
`(assert ...)` + `(check-sat)` only, not `.smtv1`-derived, no incremental/exotic
commands, at least one `assert`. The exact-`QF_ALIA` match yields **6** clean
files.

## Measured head-to-head (6 files)

`bench-results/baselines/qf-alia-cvc5-regress-clean-solver-vs-z3-10s.json`,
`--logic QF_ALIA --backend solver --compare-z3 --timeout-ms 10000 --jobs 4`:

- **files 6** -- decided **0**, unknown 0, unsupported **6**, errors 0.
- Oracle: **compared 0, agree 0, DISAGREE 0** -- nothing to compare (all
  unsupported), but no wrong verdict was emitted.
- PAR-2 mean ~ 0.0 s (every file declines immediately at the front end before
  any solve runs, so no timeout penalty accrues).

## Dominant blocker (all 6 `unsupported`)

**`Int`-indexed/valued arrays** -- `(Array Int Int)` / `(Array Int Bool)` etc.
decline with *"only bit-vector-indexed/valued arrays are supported"*. Closing the
gap (an `Int`-array model, or an Int-to-BV abstraction with range reasoning) is a
solver-source change, out of scope for corpus curation. All 6 decline cleanly as
`Unsupported` (never a wrong verdict).
