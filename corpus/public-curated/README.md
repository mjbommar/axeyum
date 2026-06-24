# Curated public benchmark slices (committed, reproducible)

Curated, **committed** SMT-LIB benchmark slices for measured head-to-head runs of
the high-level `axeyum_solver::check_auto` dispatcher against Z3 on **non-`QF_BV`**
divisions. These exist because the QF_BV public corpus lives behind the gitignored
`/corpus/public/` NAS symlink, so it cannot be committed for reproducibility; the
slices here are small enough to vendor in-tree.

Run them with the `solver` backend of `axeyum-bench` (the `check_auto` adapter):

```sh
cargo build --release -p axeyum-bench --features z3
target/release/axeyum-bench \
  corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean \
  --logic QF_UF --backend solver --compare-z3 --timeout-ms 10000 --jobs 4 \
  --out bench-results/baselines/qf-uf-cvc5-regress-clean-solver-vs-z3-10s.json
```

The committed baseline artifacts live under
[`bench-results/baselines/`](../../bench-results/baselines/).

## Provenance

Files are reused from the cvc5 regression suite
(`references/cvc5/test/regress`, a shallow sparse clone — `references/` is
gitignored). Each vendored file's name flattens its original `test/regress/...`
path (`/` → `__`).

## Selection criteria (clean, parser-faithful, status-annotated)

A file is included only if it:

- declares the target logic (`(set-logic QF_UF)` / `(set-logic QF_LRA)`),
- carries a `(set-info :status …)` ground truth,
- uses plain `(assert …)` + `(check-sat)` only,
- is **not** an SMT-v1-derived (`.smtv1.smt2`) file, and
- contains **none** of the incremental/exotic commands that the flat
  benchmark-slice parser cannot faithfully represent:
  `check-sat-assuming`, `get-value`, `get-model`, `get-unsat-core`,
  `push`/`pop`, `reset-assertions`, `get-info`, `get-assignment`,
  `define-fun-rec`, `echo`.

This filter mirrors the bench harness's own **under-parse soundness guard**: the
harness independently re-checks each instance and marks it `unsupported` (never a
vacuous verdict) when the flat assertion view would silently solve a different
problem than the source — specifically when a `check-sat-assuming` carries inline
assumptions, or zero assertions parse from constraint-bearing source text.

## QF_UF: `cvc5-regress-clean-bounded` (88 files)

The QF_UF slice is committed as `cvc5-regress-clean-bounded`: the 88 of 103
otherwise-clean QF_UF files on which the `check_auto` dispatcher respects the
`--timeout-ms` budget. **15** files were excluded for a *measurement* (not
soundness) reason — on them `check_auto`'s EUF path does not currently honor the
solve timeout, so the harness cannot bound the run. They are listed here so the
exclusion is reproducible and so the gap can be re-checked once the timeout is
threaded through that path:

```
cli__regress1__nl__nl_uf_lalt.smt2
cli__regress1__uflia__FIREFLY_luke_1b_e2_3049_e7_1173.ec.minimized.smt2
cli__regress1__uflia__microwave21.ec.minimized.smt2
cli__regress1__uflia__simple_cyclic2.smt2
cli__regress2__hash_sat_06_19.smt2
cli__regress2__hash_sat_07_17.smt2
cli__regress2__hash_sat_09_09.smt2
cli__regress2__hash_sat_10_09.smt2
cli__regress2__javafe.ast.StandardPrettyPrint.319_no_forall.smt2
cli__regress2__javafe.ast.WhileStmt.447_no_forall.smt2
cli__regress2__nl__ufnia-factor-open-proof.smt2
cli__regress2__ooo.rf6.smt2
cli__regress2__ooo.tag10.smt2
cli__regress2__simplify.javafe.ast.ArrayInit.35_without_quantification2.smt2
cli__regress4__xs-11-20-5-2-5-3.smt2
```

## Note on the Z3 comparison oracle

The in-repo `Z3Backend` only supports `QF_BV`; it declines UF/arithmetic. For these
non-BV slices `axeyum-bench` therefore falls back to the **stand-alone Z3 binary**
(`z3` on `PATH`, overridable via `AXEYUM_Z3`) as the `--compare-z3` oracle, so the
`oracle` agree/disagree counters reflect a real head-to-head. Some files declared
`QF_LRA` actually exercise mixed features (e.g. `QF_UFNRAT`) that the Z3 binary
rejects as an unsupported logic; those are reported as oracle-`skipped`, not
disagreements.
