# QF_FP curated slice (bitwuzla regress) — first measured division

First **QF_FP (floating-point)** head-to-head of the high-level
`axeyum_solver::check_auto` dispatcher (`--backend solver`) against Z3 4.13.3.
QF_FP is wired end-to-end in the SMT-LIB front end: `Float16/32/64/128` sorts,
the `fp.*` operator set (`fp.add/sub/mul/div/fma/sqrt/roundToIntegral`,
`fp.abs/neg/min/max/rem`, comparisons, the `fp.is*` classifiers, `fp.to_real`,
`(_ to_fp …)` / `fp.to_sbv` / `fp.to_ubv` conversions), the special constants
`(_ +oo/-oo/+zero/-zero/NaN eb sb)`, and all five literal rounding modes, all
lowered through `axeyum_fp`'s FP→BV bit-blast.

## Provenance

Files are reused from the bitwuzla regression suite
(`references/bitwuzla/test/regress`, a shallow sparse clone — `references/` is
gitignored). bitwuzla is the FP-richest reference suite. Each vendored file's
name flattens its original `test/regress/...` path (`/` → `__`).

## Selection criteria

Same clean, parser-faithful, status-annotated filter as the cvc5 slices
(`scripts/curate-public-slice.py QF_FP <out> --root references/bitwuzla/test/regress`):
exact `(set-logic QF_FP)`, a `(set-info :status …)` ground truth, plain
`(assert …)` + `(check-sat)` only, not `.smtv1`-derived, no
incremental/exotic commands, at least one `assert`. The exact-`QF_FP` match over
the bitwuzla regress root yields **16** clean files.

No file required a *measurement* (timeout) exclusion: a per-file probe with a
10 s `--timeout-ms` and a 30 s OS hard-timeout backstop killed none of the 16
(FP bit-blasting stays cheap on these crafted instances).

## Resolved soundness defect — `fp.min`/`fp.max` opposite-sign-zero (issue208)

Two files exercise an SMT-LIB-underspecified case of `fp.min`/`fp.max` that
formerly drove `check_auto` to a **wrong `unsat`**:

```
solver__fp__issue208_1.smt2   (status sat, Z3 sat)
solver__fp__issue208_2.smt2   (status sat, Z3 sat)
```

These reconstruct the original bitwuzla `issue208` instances (Florian Schanda's
SPARK-inspired probes; `references/` is gitignored, so they are rebuilt here as
the minimal `(distinct (fp.max x y) (fp.max y x))` / `(distinct (fp.min …))` over
`x = +0`, `y = −0` that isolates the defect — both verified **sat** by Z3 4.13.3
and carrying `:status sat`).

SMT-LIB **leaves the sign of an `fp.min`/`fp.max` result on opposite-sign zeros
unspecified**, and — crucially — the choice may differ between argument orders:
`fp.max(+0,−0)` and `fp.max(−0,+0)` may be `+0` or `−0` independently.
`axeyum_fp::min`/`max` formerly made a *single deterministic* choice (`−0` for
min, `+0` for max) regardless of order, forcing `fp.max(+0,−0) = fp.max(−0,+0)`,
so the `(distinct …)` constraint became unsatisfiable and the solver returned a
**wrong `unsat`** while a faithful model (as Z3 finds) is `sat`.

**Fix** (`crates/axeyum-fp/src/lib.rs`, `select_by_order`): on the
`is_zero(x) ∧ is_zero(y) ∧ sign(x) ≠ sign(y)` case the result is a zero whose
sign is a **fresh free Boolean, one per application** — structural hashing makes
the same syntactic `fp.min`/`fp.max` term reuse its bit (a real, consistent
function) while distinct applications (swapped argument order) get independent
bits and so *may* differ. Every other input keeps the exact ordered pick, so
only the genuinely-unspecified case becomes free: no model is excluded (no wrong
`unsat`) and the value is always a valid `±0` (no wrong `sat`). Both files now
decide **sat**, agreeing with Z3 and `:status`.

## Measured head-to-head (16 files)

`bench-results/baselines/qf-fp-bitwuzla-regress-clean-solver-vs-z3-10s.json`,
`--logic QF_FP --backend solver --compare-z3 --timeout-ms 10000 --jobs 4`:

- **files 16** — decided **14** (sat **9**, unsat **5**), unknown 0,
  unsupported **2**, errors 0.
- Oracle (Z3 4.13.3 binary + `:status`): **compared 14, agree 14, DISAGREE 0** —
  every decided verdict matches both Z3 and the status annotation.
- PAR-2 mean ≈ 0.001 s (the bit-blast is trivial on these crafted instances).

This holds QF_FP as a measured division with DISAGREE=0.

## Dominant front-end blocker (follow-up): the `RoundingMode` sort

Both `unsupported` files (`solver__fp__fp_misc.smt2`,
`solver__fp__fp_rm.smt2`) decline on **`sort RoundingMode`**:

- `fp_misc.smt2` declares a **symbolic** rounding mode
  (`(declare-const rm RoundingMode)`) — a free variable over the five modes; it
  needs a real `RoundingMode` enum / 5-way case split in the solver, not a
  front-end-only fix.
- `fp_rm.smt2` names the five *literal* modes via
  `(define-fun rne () RoundingMode roundNearestTiesToEven)` etc. — wireable in
  principle, but only the literal-mode case, and not without touching how the
  front end resolves a `RoundingMode`-sorted symbol.

Wiring the `RoundingMode` sort (symbolic + literal-binding) is the tracked
follow-up; it is an `axeyum-ir`/`axeyum-fp` change, out of scope for corpus
curation. Until then these two decline cleanly as `Unsupported` (never a wrong
verdict).
