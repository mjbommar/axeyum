# QF_ALIA curated slice (cvc5 regress)

First **QF_ALIA (arrays + linear integer arithmetic)** head-to-head of the
high-level `axeyum_solver::check_auto` dispatcher (`--backend solver`) against
Z3 4.13.3.

## What this slice now measures (constant arrays decided)

QF_ALIA arrays are indexed and valued by **`Int`** (`(Array Int Int)`,
`(Array Int Bool)`, etc.). axeyum has no `Int`-array IR sort -- it only supports
**bit-vector-indexed/valued arrays** (`eliminate_arrays` is QF_ABV, ADR-0010).
The general `Int`-array decision procedure remains the tracked IR keystone.

The **constant-array** subset, however, is now decided **without** that keystone:
a sort-agnostic SMT-LIB-front-end rewrite (`desugar_const_arrays`) eliminates
const arrays on the s-expression tree before any term is built, using the array
axioms only --

- `(select ((as const A) v) i)` -> `v` (a const array maps every index to `v`);
- `(select (store arr j w) i)` -> `(ite (= i j) w (select arr i))`
  (read-over-write), recursing until it bottoms out at a const array;
- `(= ca1 ca2)` between two const arrays -> `(= v1 v2)` (value equality).

The rewrite is **sort-agnostic** (index/element may be `Int`/`Bool`/`BV`), so an
`(Array Int Int)`/`(Array Int Bool)` const-array formula reduces to pure `Int`
constraints decided by the LIA path. Anything outside the const-array subset --
a `select`/`store` over a **free** (non-const-derived) array variable, or a
`store`-chain equality joining two *different* const arrays -- is left
**declined** (`Unsupported`), never given a wrong verdict.

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

- **files 6** -- decided **3** (sat **1**, unsat **2**), unknown 0, unsupported
  **3**, errors 0. (Before the const-array rewrite: decided **0**, unsupported
  **6**.)
- Oracle: **compared 3, agree 3, DISAGREE 0** -- every decided file agrees with
  both Z3 and its `:status`; no wrong verdict.
- PAR-2 mean ~ 0.0 s (the const-array files reduce to small `Int` formulas
  decided instantly; the rest decline immediately at the front end).

### Decided (3) -- the const-array subset

- `cli__regress0__arrays__constarr.smt2` -- **unsat**
  (`all1 = (as const) 1`, `a = select(all1, i)`, `a != 1`).
- `cli__regress0__arrays__constarr2.smt2` -- **unsat**
  (`all1 = (as const) 1`, `all2 = (as const) 2`, `all1 = all2` -> `1 = 2`).
- `cli__regress0__arrays__issue4414-2.smt2` -- **sat**
  (`c = (as const) 0`, `a = select(c, b)` -> `a = 0`).

### Still `unsupported` (3) -- general `Int`-array reasoning

- `cli__regress0__arith__integers__ackermann4.smt2` -- selects over **free**
  array vars (`select a (select b ...)`); the general `Int`-array procedure.
- `cli__regress0__proofs__ios_np_sf.smt2` -- `store`-chains over a **free** array
  var with variable indices; the general `Int`-array procedure.
- `cli__regress1__constarr3.smt2` -- a `store`-chain equality connecting two
  *different* const arrays (`aa = store(all1 i 0)`, `bb = store(all2 i 0)`,
  `aa = bb`); not a bare const-array equality (cvc5 itself **errors** on this
  shape). Declines cleanly.

All 3 declines are sound `Unsupported` (never a wrong verdict). Closing the
general `Int`-array case (an `Int`-array IR model, or an Int-to-BV abstraction
with range reasoning) remains the tracked IR keystone.
