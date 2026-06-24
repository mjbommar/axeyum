# QF_AX curated slice (cvc5 regress)

First **QF_AX (the array theory over abstract index/element sorts)** head-to-head
of the high-level `axeyum_solver::check_auto` dispatcher (`--backend solver`)
against Z3 4.13.3.

## How an abstract-sort theory still gets measured

QF_AX benchmarks use *uninterpreted* index/element sorts —
`(declare-sort Index 0)`, `(declare-sort Element 0)`, or `Bool` — not bit-vectors,
and axeyum only supports **bit-vector-indexed/valued arrays** (`eliminate_arrays`
is QF_ABV, ADR-0010). The slice is **not** all-`unsupported`, though, because the
SMT-LIB front end models every arity-0 `(declare-sort U 0)` uninterpreted sort as
a fixed-width `BitVec` (`parse.rs::uninterpreted_sort_width`, sized to the count of
distinct symbols of that sort). That turns an abstract-`Index`/`Element` `QF_AX`
formula into `QF_ABV`, which the read-over-write + bounded-extensionality array
path then handles — for the cases that fit.

## Provenance

Files are reused from the cvc5 regression suite
(`references/cvc5/test/regress`, a shallow sparse clone — `references/` is
gitignored). bitwuzla's regress root yields **0** exact-`QF_AX` clean files (its
array tests are `QF_ABV`/`QF_AUFBV`). Each vendored file's name flattens its
original `test/regress/...` path (`/` → `__`).

## Selection criteria

Same clean, parser-faithful, status-annotated filter as the other slices
(`scripts/curate-public-slice.py QF_AX <out> --root references/cvc5/test/regress`):
exact `(set-logic QF_AX)`, a `(set-info :status …)` ground truth, plain
`(assert …)` + `(check-sat)` only, not `.smtv1`-derived, no incremental/exotic
commands, at least one `assert`. The exact-`QF_AX` match yields **8** clean files.

No file required a *measurement* (timeout) exclusion: every file returns in a few
ms (no solve ran past 4 ms).

## Measured head-to-head (8 files)

`bench-results/baselines/qf-ax-cvc5-regress-clean-solver-vs-z3-10s.json`,
`--logic QF_AX --backend solver --compare-z3 --timeout-ms 10000 --jobs 4`:

- **files 8** — decided **3** (sat **1**, unsat **2**), unknown 0,
  unsupported **5**, errors 0.
- Oracle (Z3 4.13.3 binary + `:status`): **compared 3, agree 3, DISAGREE 0** —
  every decided verdict matches both Z3 and the status annotation.
  (The in-repo `z3` *library* oracle declines array symbols; the head-to-head
  uses the **Z3 4.13.3 binary** at `/usr/bin/z3`.)
- PAR-2 mean ≈ 20.0 s — this is the standard PAR-2 penalty: 5 of 8 files are
  `unsupported` (unsolved), each scored at 2× the 10 s timeout, so the mean is
  dominated by the penalty even though every *solved* file decides in < 4 ms.

This holds QF_AX as a measured division with **DISAGREE 0**; no soundness
disagreement surfaced.

## Dominant blocker (the 5 `unsupported`), two reasons

1. **Bounded-extensionality index-width cap (3 files)** —
   `arrays0`, `arrays3`, `arrays4` decline with
   *"array equality over a 9-bit index (bounded extensionality supports indices
   up to 8 bits)"*. The abstract `Index` sort is auto-sized to a 9-bit `BitVec`
   here (enough distinct index symbols), which exceeds the 8-bit cap of the
   bounded array-extensionality encoding. A wider/unbounded extensionality route
   is the tracked array follow-up (an `axeyum-solver`/`axeyum-rewrite` change,
   out of scope for corpus curation).
2. **`Bool`-indexed/valued arrays (2 files)** — `bool-array`,
   `proj-issue506-ms-var-elim` use `(Array Bool Bool)` and decline with
   *"only bit-vector-indexed/valued arrays are supported"*. `Bool` is not modeled
   as a `BitVec(1)` array index/element here.

All 5 decline cleanly as `Unsupported` (never a wrong verdict).
