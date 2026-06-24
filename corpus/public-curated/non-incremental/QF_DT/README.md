# QF_DT curated slice (committed, reproducible)

Curated, **committed** SMT-LIB `QF_DT` (quantifier-free algebraic datatypes)
slice for the measured head-to-head of `axeyum_solver::check_auto`
(`--backend solver`) against the Z3 4.13.3 binary — a scoreboard extension and a
differential soundness bug-hunt on the datatype path (constructors / selectors /
testers + datatype elimination, ADR-0022; Carcara+Lean datatype certs landed
earlier this session).

- `cvc5-regress-clean/` — the **3** clean exact-`(set-logic QF_DT)` files from the
  cvc5 regression suite (`references/cvc5/test/regress`, a gitignored shallow
  `--filter=blob:none --sparse` clone).

```sh
target/release/axeyum-bench \
  corpus/public-curated/non-incremental/QF_DT/cvc5-regress-clean \
  --logic QF_DT --backend solver --compare-z3 --timeout-ms 10000 --jobs 4 \
  --out bench-results/baselines/qf-dt-cvc5-regress-clean-solver-vs-z3-10s.json
```

## Corpus reality: pure QF_DT is genuinely tiny in the references

QF_DT is a **rare exact logic** in the public regression corpora: the cvc5 suite
has exactly **3** files declaring `(set-logic QF_DT)`, and the bitwuzla suite has
**0** (bitwuzla is BV/FP-focused, no datatype theory). All 3 cvc5 files are clean
under the standing filter (plain `assert`+`check-sat` only, no `.smtv1`, no
incremental/exotic commands), so the whole exact-QF_DT slice is vendored. The
cvc5 regress suite has hundreds of files that *use* `declare-datatype`, but they
are declared under combined/quantified logics (`ALL`, `UFDT`, `QF_UFDTLIA`, …) —
none of which is the exact quantifier-free pure-`QF_DT` division this baseline
measures, and most of which are quantified or carry extra theories (out of
scope). This is not a curation artifact — it is the corpus.

### Ground-truth annotation: `:status` vs `; EXPECT:`

Only 1 of the 3 files carries a `(set-info :status …)`. The other 2 use cvc5's
own regress convention, a `; EXPECT: <status>` comment, which the flat
benchmark-slice parser does not read as `set-info` (so the harness reports
`expected=unknown` for them). For these files the **binding soundness gate is the
`--compare-z3` head-to-head**, not `:status` — exactly as the QF_AX slice relies
on the Z3 oracle rather than `:status`. The committed baseline records
`DISAGREE=0` and `oracle_disagreements=0` on every decided file.

Reproduce the selection (a DT-specific flag accepts the `; EXPECT:` annotation as
ground truth; default behavior — `(set-info :status …)` only — is unchanged, so
every existing slice re-derives byte-for-byte):

```sh
python3 scripts/curate-public-slice.py QF_DT - --expect-comment
# QF_DT (..., expect_comment=True, ...): 3 files
#   cli__regress0__datatypes__pf-v2l60078.smt2
#   cli__regress0__proofs__dt-cons-eq-clash-qfdt.smt2
#   cli__regress1__datatypes__acyclicity-sr-ground096.smt2
```

## Measured head-to-head (2026-06-24)

`qf-dt-cvc5-regress-clean-solver-vs-z3-10s.json`, `--timeout-ms 10000 --jobs 4`:

files **3**, decided **2** (sat 0, **unsat 2**), unknown 0, **unsupported 1**,
errors 0; **compared 2, agree 2, DISAGREE 0** — both decided verdicts match the
Z3 4.13.3 binary oracle and the `; EXPECT:` annotation. PAR-2 mean ~10.0 s is the
standard penalty for the 1/3 unsupported file (scored at 2× the 10 s timeout);
every decided file decides in < 1 ms.

The in-repo Z3 *library* oracle declines datatypes
(`z3 oracle does not support … datatypes …`), so the head-to-head uses the Z3
4.13.3 **binary** (as the QF_AX slice does). No soundness disagreement surfaced
(`oracle_disagreements=0`, `status_disagreements=0`, `model_replay_failures=0`).

| file | axeyum | Z3 | EXPECT | outcome |
| --- | --- | --- | --- | --- |
| `cli__regress0__datatypes__pf-v2l60078.smt2` | unsat | unsat | unsat | agree |
| `cli__regress0__proofs__dt-cons-eq-clash-qfdt.smt2` | unsat | unsat | unsat | agree |
| `cli__regress1__datatypes__acyclicity-sr-ground096.smt2` | unsupported | (skipped) | unsat | declined |

The two decided files exercise the supported shape — finite algebraic datatypes
folded over constructors, with a constructor-clash distinctness conflict
(`dt-cons-eq-clash`) and a selector / `is`-tester combination (`pf-v2l60078`) —
and both decide unsat in agreement with Z3.

## Dominant front-end blocker (the 1 unsupported)

`acyclicity-sr-ground096.smt2` declines as **Unsupported** with detail:

```
`is`/`select` over a non-variable datatype term
(constructors should fold first) (ADR-0022)
```

It asserts a large ground acyclicity disjunction over deeply **nested
constructor applications** where a tester/selector is applied to a non-variable
(constructor-headed) datatype term that the elimination pass does not fold first.
It declines cleanly (never a wrong verdict) — a coverage gap in the
datatype-elimination front end, not a soundness defect. Closing it (and acquiring
a richer pure-`QF_DT` corpus) is a solver-source / curation-source follow-up out
of scope for this measurement.

## QF_UFDT: skipped (empty in references)

`QF_UFDT` (datatypes + UF) has **0** exact `(set-logic QF_UFDT)` files in either
the cvc5 or bitwuzla regression suites. The only nearby quantifier-free
datatype+UF logics in cvc5 are `QF_UFDTLIA` / `QF_UFDTFS`, which additionally
bring in linear integer arithmetic / finite sets (out of scope for the finite
algebraic-datatype path). No QF_UFDT baseline is committed because there is
nothing clean to measure; the division is recorded here as an honest empty skip.
