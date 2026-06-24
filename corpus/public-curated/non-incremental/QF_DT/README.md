# QF_DT curated slice (committed, reproducible)

Curated, **committed** SMT-LIB `QF_DT` (quantifier-free datatypes) slice for the
measured head-to-head of `axeyum_solver::check_auto` against the Z3 4.13.3
binary. Datatypes are Carcara+Lean-certified this session, so QF_DT is on the
measurement frontier.

- `cvc5-regress-clean/` — the **1** clean exact-`(set-logic QF_DT)` file from the
  cvc5 regression suite (`references/cvc5/test/regress`, a gitignored shallow
  clone).

```sh
target/release/axeyum-bench \
  corpus/public-curated/non-incremental/QF_DT/cvc5-regress-clean \
  --logic QF_DT --backend solver --compare-z3 --timeout-ms 10000 --jobs 4 \
  --out bench-results/baselines/qf-dt-cvc5-regress-clean-solver-vs-z3-10s.json
```

## Corpus reality: pure QF_DT is genuinely tiny in the references

The clean filter (same as the other slices — exact `(set-logic QF_DT)`, a
`(set-info :status …)` ground truth, plain `assert`+`check-sat` only, no
`.smtv1`, no incremental/exotic commands) selects **1** file across the entire
`references/` tree:

```
cli__regress1__datatypes__acyclicity-sr-ground096.smt2   (:status unsat)
```

This is not a curation artifact — it is the corpus. The references hold only
**2** files declared with the exact `QF_DT` logic (the other,
`regress0/datatypes/pf-v2l60078.smt2`, carries no `(set-info :status …)` and is
correctly dropped — no machine-readable ground truth to gate on). The cvc5
regress suite has **302** files that *use* `declare-datatype`, but they are
declared under combined/quantified logics — `ALL` (223), `UFDT` (18),
`QF_ALL` (12), `UFDTLIA` (8), `QF_UFDTLIA` (3), … — none of which is the exact
quantifier-free pure-`QF_DT` division this baseline measures, and most of which
are quantified (out of scope: the curated slices are quantifier-free and
non-incremental). No measurement exclusion was needed (the 1 file is bounded).

Reproduce:

```sh
python3 scripts/curate-public-slice.py QF_DT -    # lists the 1 selected file
```

## Measured head-to-head (2026-06-24)

`qf-dt-cvc5-regress-clean-solver-vs-z3-10s.json`,
`--timeout-ms 10000 --jobs 4`:

- **files 1**. axeyum **decides 0** (unknown 0, **unsupported 1**, errors 0).
  **DISAGREE 0** (nothing to compare — the single file is unsupported before a
  verdict, so the Z3 oracle is correctly skipped, not disagreed).

## Dominant front-end gap (real follow-up, not fixed here)

The single file is `unsupported` with detail:

```
`is`/`select` over a non-variable datatype term
(constructors should fold first) (ADR-0022)
```

i.e. the file applies a tester/selector to a *constructor application* (a
nested `(f1 …)`/`(f2 …)` term) rather than a variable, and the datatype front
end currently requires constructor folding first (ADR-0022). Closing this — and
acquiring a richer pure-`QF_DT` corpus — is a solver-source / curation-source
change out of scope for this measurement. The honest measured result is that the
**only** clean pure-QF_DT instance available hits this one front-end gap.
