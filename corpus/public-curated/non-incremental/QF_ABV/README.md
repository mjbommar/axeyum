# QF_ABV curated slice (committed, reproducible)

Curated, **committed** SMT-LIB `QF_ABV` (quantifier-free arrays + bit-vectors)
benchmark slices for the measured head-to-head of `axeyum_solver::check_auto`
against the Z3 4.13.3 binary. QF_ABV is BV + arrays — axeyum's strongest theory
(the `eliminate_arrays` read-over-write + Ackermann path, ADR-0010, feeding the
bit-blast-to-SAT BV core), so it is an explicit **"drive to the top"** division.

Two source-labelled sub-slices, both walked by one bench run (the harness
recurses into sub-directories):

- `bitwuzla-regress-clean/` — 174 files from the bitwuzla regression suite
  (`references/bitwuzla/test/regress`, a BV+array solver; its regress tree is
  rich in QF_ABV).
- `cvc5-regress-clean/` — 19 files from the cvc5 regression suite
  (`references/cvc5/test/regress`).

`references/` is a gitignored shallow clone; each vendored file's name flattens
its original path relative to the source `test/regress/` root (`/` → `__`).

Run the combined slice:

```sh
cargo build --release -p axeyum-bench --features z3
target/release/axeyum-bench \
  corpus/public-curated/non-incremental/QF_ABV \
  --logic QF_ABV --backend solver --compare-z3 --timeout-ms 10000 --jobs 4 \
  --out bench-results/baselines/qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json
```

## Selection criteria

Identical clean / parser-faithful / status-annotated filter as the other
curated slices (see [`../../README.md`](../../README.md) and the committed
helper [`scripts/curate-public-slice.py`](../../../../scripts/curate-public-slice.py)).
A file is included only if it declares exactly `(set-logic QF_ABV)`, carries a
`(set-info :status …)` ground truth, uses only plain `(assert …)` +
`(check-sat)`, is not an `.smtv1`-derived file, and contains none of the
incremental/exotic commands the flat benchmark-slice parser cannot faithfully
represent (`check-sat-assuming`, `get-value`/`get-model`/`get-unsat-core`,
`push`/`pop`, `set-option :incremental`, `define-fun-rec`, …).

Reproduce both sub-slices:

```sh
python3 scripts/curate-public-slice.py QF_ABV <out> \
  --root references/bitwuzla/test/regress      # 175 clean (1 excluded, see below)
python3 scripts/curate-public-slice.py QF_ABV <out>   # 19 clean (cvc5, default root)
```

(`--root` is the committed extension that points the curation at the bitwuzla
regress tree; the default root remains cvc5.)

## Measurement exclusion (unbounded under 10 s)

The bitwuzla filter yields **175** clean files; **1** is excluded for a
*measurement* (not soundness) reason — it does not respect the `--timeout-ms`
budget under `check_auto` (a per-file probe with a 10 s `--timeout-ms` and a
30 s OS hard-timeout backstop killed it at the backstop):

```
solver__array__write21.btor.smt2
```

The committed `bitwuzla-regress-clean` slice is therefore the **174** that
respect the budget. cvc5 (19 files) needed no exclusion.

## Measured head-to-head (2026-06-24)

`qf-abv-cvc5-bitwuzla-regress-clean-solver-vs-z3-10s.json`,
`--timeout-ms 10000 --jobs 4`, oracle = the stand-alone Z3 4.13.3 binary
(`/usr/bin/z3`):

- **files 193** (bitwuzla 174 + cvc5 19).
- axeyum **decides 169** (sat **84**, unsat **85**) — an **87.6 %** decide rate,
  **unknown 0**, **unsupported 24**, errors 0. PAR-2 mean ≈ 1.666 s.
- Oracle: **compared 165, agree 165, DISAGREE 0**. 4 decided instances are
  oracle-skipped because the Z3 *binary* errors on their `(set-option
  :bv_solver …)` (an old Z3 parameter name) — axeyum decided all 4 (2 sat,
  2 unsat); the remaining skips are the 24 unsupported + 1 `:status unknown`
  source file. **No disagreement.**

This is a strong "drive to the top" result: axeyum's BV+array path **decides
87.6 % of this clean QF_ABV corpus with zero disagreements** against Z3 over the
165 head-to-head comparisons, and the residual is front-end coverage (below),
not search.

## Dominant front-end gaps (real follow-up, not fixed here)

The 24 `unsupported` files break down as:

- **array equality over wide indices** (14): bounded extensionality currently
  supports array-index widths up to 8 bits — files asserting array `=` over
  16-/32-/64-bit indices are declined (8 × 32-bit, 4 × 64-bit, 1 × 16-bit) plus
  1 nested-`Array`-of-`Array` and the `Array Bool Bool` / wide-Bool-valued
  variants (4 "only bit-vector-indexed/valued arrays are supported").
- **bit-vector reduction operators** (6): `bvredxor` (3), `bvredand` (2),
  `bvredor` (1) are not yet in the front-end operator table.
- 1 file references an unknown identifier `a24` (a front-end resolution gap).

These are solver-source / front-end-coverage changes (out of scope for corpus
curation). Widening bounded array extensionality past 8-bit indices and adding
the `bvred*` family would lift the bulk of the remaining 24.
