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

- declares the target logic — exact `(set-logic …)` for a specific division
  (`QF_LRA`, `QF_UFLIA`, `QF_LIA`), or the `QF_UF*` *family* prefix for the
  EUF-family `QF_UF` slice (so `QF_UFLIA`, `QF_UFNRAT`, `QF_UFBV`, … are kept),
- carries a `(set-info :status …)` ground truth,
- uses plain `(assert …)` + `(check-sat)` only,
- is **not** an SMT-v1-derived (`.smtv1.smt2`) file, and
- contains **none** of the incremental/exotic commands that the flat
  benchmark-slice parser cannot faithfully represent:
  `check-sat-assuming`, `get-value`, `get-model`, `get-unsat-core`,
  `get-unsat-assumptions`, `get-interpolant`, `get-abduct`, `get-proof`,
  `push`/`pop`, `reset`, `reset-assertions`, `get-info`, `get-assignment`,
  `declare-pool`, `block-model`, `define-fun-rec`, `echo`, and the
  `set-option :incremental true` / `:produce-models true` options, and
- contains at least one `(assert …)` (a zero-assert file would let the flat
  view solve a different, vacuous problem than the source).

The curation is reproduced by the committed helper
[`scripts/curate-public-slice.py`](../../scripts/curate-public-slice.py)
(`python3 scripts/curate-public-slice.py <LOGIC> <out_dir> [--prefix]`); it
reads the gitignored `references/cvc5/test/regress` clone and re-derives the
QF_UF / QF_UFLIA / QF_LIA slices byte-for-byte.

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

### QF_UF full re-measure: still blocked (measured 2026-06-24)

A planned "full" QF_UF re-measure — re-including the 15 files above on the
premise that commit `af35fe1` ("bound the QF_UF e-graph path by config.timeout")
makes them return `Unknown` within budget — was **measured and does not hold**.
Under `af35fe1` (HEAD at measurement) every one of the 15 still runs unbounded:
a per-file probe with a 10 s `--timeout-ms` and a 20 s / 60 s OS hard-timeout
backstop killed all 15 at the backstop (the budget was not honored). Root cause:
all 15 declare a UF-plus-integer-arithmetic logic
(`QF_UFLIA` / `QF_UFNIA` / `QF_UFIDL`), **not** pure `QF_UF`, so `check_auto`
routes them through the UFLIA-class arithmetic decision path, which `af35fe1`
did not touch — that fix bounds only the pure-EUF e-graph path (`check_qf_uf`).
The `cvc5-regress-clean-bounded` slice therefore remains the honest, runnable
QF_UF measurement; closing the gap needs the timeout threaded through the
UF+arithmetic path (a solver-source change, out of scope for corpus curation).

## QF_UFLIA: `cvc5-regress-clean-bounded` (8 files)

The `QF_UFLIA` slice (exact-logic match) yields 17 clean files from cvc5
`test/regress` (65 total declare `QF_UFLIA`; 18 are `.smtv1`-derived and 29
carry no `:status`). Of those 17, **9** run unbounded under `check_auto`'s
UF+integer-arithmetic path (the same unbounded path described above — they are
the `QF_UFLIA`-logic members of the QF_UF exclusion list plus their siblings),
so the committed slice is the **8** that respect the `--timeout-ms` budget. The
9 measurement-excluded files are:

```
cli__regress1__uflia__FIREFLY_luke_1b_e2_3049_e7_1173.ec.minimized.smt2
cli__regress2__hash_sat_06_19.smt2
cli__regress2__hash_sat_07_17.smt2
cli__regress2__hash_sat_09_09.smt2
cli__regress2__hash_sat_10_09.smt2
cli__regress2__javafe.ast.StandardPrettyPrint.319_no_forall.smt2
cli__regress2__javafe.ast.WhileStmt.447_no_forall.smt2
cli__regress2__simplify.javafe.ast.ArrayInit.35_without_quantification2.smt2
cli__regress4__xs-11-20-5-2-5-3.smt2
```

## QF_LIA: `cvc5-regress-clean-bounded` (11 files)

The `QF_LIA` slice (exact-logic match) yields 12 clean files from cvc5
`test/regress`. **1** of them runs unbounded under `check_auto`'s QF_LIA path
(`cli__regress3__arith_prp-13-24.smt2`), so the committed slice is the **11**
that respect the `--timeout-ms` budget.

## QF_NRA: `cvc5-regress-clean` (38 files)

The `QF_NRA` slice (exact-logic match) yields **38** clean files from cvc5
`test/regress`. **No** measurement exclusion was needed: with the eager
UF+arithmetic (Ackermann) bound (commit `6233a7c`) and the `nra.rs` solve
deadlines in place, every file respects the `--timeout-ms` budget — a per-file
probe with a 10 s `--timeout-ms` and a 30 s OS hard-timeout backstop killed
none of the 38. The committed slice is therefore the full clean set
(`cvc5-regress-clean`, not `-bounded`).

Measured head-to-head vs the Z3 4.13.3 binary
(`qf-nra-cvc5-regress-clean-solver-vs-z3-10s.json`,
`--timeout-ms 10000 --jobs 4`): axeyum decides **9** (sat 5, unsat 4),
**unknown 15** (all `ResourceLimit`), **unsupported 13**, and **1**
`solver-error`. Oracle: **compared 9, agree 9, DISAGREE 0**, skipped 16. PAR-2
mean ≈ 12.85 s. The `solver-error` (`cli__regress1__nl__approx-sqrt-unsat.smt2`)
is the i128 `Rational`-overflow *guard* — model replay caught a `real_cmp`
value outside i128 range and returned an error rather than a wrong verdict
(a graceful guard, never an unsound sat/unsat).

Dominant front-end gap (the real follow-up): **Int/Real coercion in the
SMT-LIB front-end** — 13 unsupported files split as `cannot coerce a
non-constant Int to Real` (6), `sort mismatch: expected Real, found Int` (6),
and `operands must share a sort: Real vs Int` (1). These are mixed Int/Real
arithmetic terms the front-end does not yet reconcile; closing the gap is a
solver-source change (out of scope for corpus curation). The 15 `unknown`s are
the genuine nonlinear-real arithmetic search frontier, which is the measured
opportunity this baseline exists to track.

## QF_NIA: `cvc5-regress-clean` (39 files)

The `QF_NIA` slice (exact-logic match) yields **39** clean files from cvc5
`test/regress`. As with QF_NRA, **no** measurement exclusion was needed — every
file respects the `--timeout-ms` budget under the `6233a7c` bound + `nra.rs`
deadlines (the same per-file 10 s / 30 s-backstop probe killed none of the 39).
The committed slice is the full clean set (`cvc5-regress-clean`).

Measured head-to-head vs the Z3 4.13.3 binary
(`qf-nia-cvc5-regress-clean-solver-vs-z3-10s.json`,
`--timeout-ms 10000 --jobs 4`): axeyum decides **19** (sat 15, unsat 4),
**unknown 8** (`Incomplete` 5, `ResourceLimit` 3), **unsupported 11**, and
**1** `parse-error`. Oracle: **compared 19, agree 19, DISAGREE 0**, skipped 8.
PAR-2 mean ≈ 5.85 s. The `parse-error`
(`cli__regress1__nl__issue3441.smt2`) is a front-end strictness gap: the file
wraps a single sub-term in `(and …)` (axeyum requires `and` to have ≥ 2
arguments), so it is a parser-arity limitation, not a verdict and not a
disagreement.

Dominant front-end gap (the real follow-up): **the `int.pow2` /
`(_ iand N)` / `@int_div_by_zero` operator family** — 11 unsupported files
split as `int.pow2` (7), `(_ iand 4)`/`(_ iand 5)` bitwise-and-over-Int (3),
and `@int_div_by_zero` (1). These nonlinear-integer operators are not yet in the
front-end's operator table; adding them is a solver-source change (out of scope
here). The 8 `unknown`s (5 `Incomplete`, 3 `ResourceLimit`) are the genuine
nonlinear-integer decision frontier this baseline exists to track.

## Note on the Z3 comparison oracle

The in-repo `Z3Backend` only supports `QF_BV`; it declines UF/arithmetic. For these
non-BV slices `axeyum-bench` therefore falls back to the **stand-alone Z3 binary**
(`z3` on `PATH`, overridable via `AXEYUM_Z3`) as the `--compare-z3` oracle, so the
`oracle` agree/disagree counters reflect a real head-to-head. Some files declared
`QF_LRA` actually exercise mixed features (e.g. `QF_UFNRAT`) that the Z3 binary
rejects as an unsupported logic; those are reported as oracle-`skipped`, not
disagreements.
