# QF_UFLRA: no clean corpus available (measured exclusion, reproducible)

This division was targeted for a measured `axeyum_solver::check_auto` vs Z3
baseline alongside QF_ABV and QF_DT, but **no committable baseline exists: the
reference corpora contain zero clean, status-annotated, non-incremental
exact-`(set-logic QF_UFLRA)` files.** This README records that fact so the
attempt is reproducible and the gap is honest, rather than fabricating ground
truth (which would void the DISAGREE=0 soundness guarantee the baselines exist
to certify).

## What's in the references

An exhaustive scan of the entire gitignored `references/` tree (cvc5, bitwuzla,
z3 clones) for `(set-logic QF_UFLRA)`, excluding `.smtv1`-derived files, finds
exactly **2** files — both correctly rejected by the standard clean filter:

```
references/cvc5/test/regress/cli/regress0/arith/non-normal.smt2
references/cvc5/test/regress/cli/regress1/bug800.smt2
```

- `non-normal.smt2` — has only a `; EXPECT: sat` **comment**, no SMT-LIB
  `(set-info :status …)` command, so there is no machine-readable ground truth
  for the harness to gate against. (Z3 4.13.3 does say `sat` on it, but a
  comment is not a curation-grade status annotation.)
- `bug800.smt2` — an **incremental** push/pop benchmark (`; COMMAND-LINE:
  --incremental`); its two `:status sat` annotations live inside separate
  `(push 1)` scopes. Flattening the assertion stack would conjoin two
  independent queries into one different problem, so it is dropped by the
  `push`/`pop` filter (the same non-incremental rule as every other curated
  slice).

The reference clones simply do not vendor a clean pure-QF_UFLRA regression set
(bitwuzla, a BV+array solver, carries none; the SMT-LIB QF_UFLRA category is not
part of these solvers' shallow test trees). The historical cvc5 `uflra/`
directory is entirely `.smtv1`-derived, which the filter excludes by policy.

Reproduce the empty selection:

```sh
python3 scripts/curate-public-slice.py QF_UFLRA -    # "QF_UFLRA … : 0 files"
```

## Front-end note for when a corpus is acquired

Independent of the corpus gap, QF_UFLRA exercises the **uninterpreted-sort**
front-end gap flagged for the UF divisions: pure QF_UFLRA uses only built-in
`Real`/`Bool` sorts (no `declare-sort`), so the blocker there would be UF +
linear-real-arithmetic theory combination (Nelson–Oppen over the `QF_UF`
e-graph and the `QF_LRA` simplex) rather than sort declaration. Acquiring a
clean QF_UFLRA slice (e.g. from a full SMT-LIB benchmark mirror, not the shallow
solver clones) is the prerequisite for this baseline and is out of scope for
in-tree corpus curation.
