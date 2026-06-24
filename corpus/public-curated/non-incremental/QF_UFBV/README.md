# QF_UFBV curated slice (bitwuzla + cvc5 regress)

First **QF_UFBV (uninterpreted functions over bit-vectors)** head-to-head of the
high-level `axeyum_solver::check_auto` dispatcher (`--backend solver`) against
Z3 4.13.3. QF_UFBV is handled end-to-end: the SMT-LIB front end models
arity-0 `(declare-sort U 0)` uninterpreted sorts as a fixed-width `BitVec`
(`parse.rs::uninterpreted_sort_width`, sized to the distinct-symbol count), and
uninterpreted function symbols are eliminated by **eager Ackermann** congruence
before the BV bit-blast, so the whole formula reduces to QF_BV.

## Provenance

Files are reused from the bitwuzla and cvc5 regression suites
(`references/bitwuzla/test/regress`, `references/cvc5/test/regress`; both are
shallow sparse clones, `references/` is gitignored). Each vendored file's name
flattens its original `test/regress/...` path (`/` → `__`).

## Selection criteria

Same clean, parser-faithful, status-annotated filter as the other slices
(`scripts/curate-public-slice.py QF_UFBV <out> --root <regress-root>`): exact
`(set-logic QF_UFBV)`, a `(set-info :status …)` ground truth, plain
`(assert …)` + `(check-sat)` only, not `.smtv1`-derived, no incremental/exotic
commands, at least one `assert`. The exact-`QF_UFBV` match yields **2** clean
files from bitwuzla and **4** from cvc5 (6 total), split into per-source
directories.

No file required a *measurement* (timeout) exclusion: every file decides under
1 ms.

## Measured head-to-head

`--logic QF_UFBV --backend solver --compare-z3 --timeout-ms 10000 --jobs 4`.

### `bitwuzla-regress-clean` (2 files)

`bench-results/baselines/qf-ufbv-bitwuzla-regress-clean-solver-vs-z3-10s.json`:

- **files 2** — decided **2** (sat **1**, unsat **1**), unknown 0,
  unsupported 0, errors 0.
- Oracle (Z3 4.13.3 binary + `:status`): **compared 2, agree 2, DISAGREE 0**.
- PAR-2 mean ≈ 0.0004 s.

### `cvc5-regress-clean` (4 files)

`bench-results/baselines/qf-ufbv-cvc5-regress-clean-solver-vs-z3-10s.json`:

- **files 4** — decided **4** (sat **2**, unsat **2**), unknown 0,
  unsupported 0, errors 0. Includes the named `aufbv/issue3737` and
  `bv/ackermann2` regressions plus `bug520` / `bug593`.
- Oracle: **compared 4, agree 4, DISAGREE 0**.
- PAR-2 mean ≈ 0.001 s.

Both source slices fully decide with **DISAGREE 0** — every verdict matches both
Z3 and the `:status` annotation. This holds QF_UFBV as a measured division.

## Dominant blocker

None on this slice: all 6 files decide. (No `unsupported`, no `unknown`, no
timeout.) The eager-Ackermann + uninterpreted-sort-as-BV path covers the full
slice, and no soundness disagreement surfaced.
