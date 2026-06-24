# QF_BVFP curated slice (bitwuzla regress)

First **QF_BVFP (bit-vectors + floating-point)** head-to-head of the high-level
`axeyum_solver::check_auto` dispatcher (`--backend solver`) against Z3 4.13.3.
QF_BVFP exercises the FP↔BV boundary: `fp.to_sbv` / `fp.to_ubv` /
`((_ to_fp …) bv)` / `fp.to_real`, plus the `fp.*` core (all lowered through
`axeyum_fp`'s FP→BV bit-blast) over BV-valued terms.

## Provenance

Files are reused from the bitwuzla regression suite
(`references/bitwuzla/test/regress`, a shallow sparse clone — `references/` is
gitignored). bitwuzla is the FP-richest reference suite; cvc5's regress root
yields **0** exact-`QF_BVFP` clean files. Each vendored file's name flattens its
original `test/regress/...` path (`/` → `__`).

## Selection criteria

Same clean, parser-faithful, status-annotated filter as the other slices
(`scripts/curate-public-slice.py QF_BVFP <out> --root references/bitwuzla/test/regress`):
exact `(set-logic QF_BVFP)`, a `(set-info :status …)` ground truth, plain
`(assert …)` + `(check-sat)` only, not `.smtv1`-derived, no incremental/exotic
commands, at least one `assert`. The exact-`QF_BVFP` match yields **8** clean
files.

No file required a *measurement* (timeout) exclusion: the heaviest file decides
in a few ms.

## Measured head-to-head (8 files)

`bench-results/baselines/qf-bvfp-bitwuzla-regress-clean-solver-vs-z3-10s.json`,
`--logic QF_BVFP --backend solver --compare-z3 --timeout-ms 10000 --jobs 4`:

- **files 8** — decided **6** (sat **4**, unsat **2**), unknown 0,
  unsupported **2**, errors 0.
- Oracle (Z3 4.13.3 binary + `:status`): **compared 6, agree 6, DISAGREE 0** —
  every decided verdict matches both Z3 and the status annotation.
- PAR-2 mean ≈ 0.007 s.

This holds QF_BVFP as a measured division with **DISAGREE 0**. No soundness
disagreement surfaced (the bug-hunt came up clean on this slice — in particular
the `fp.min`/`fp.max` opposite-sign-zero defect fixed for the QF_FP slice does
not recur here).

## Dominant front-end blocker (the 2 `unsupported`)

- `solver__fp__fp_fromsbv.smt2` (`:status unsat`): declines on the
  **`RoundingMode` sort** (the same tracked `axeyum-ir`/`axeyum-fp` follow-up
  noted for the QF_FP slice — a symbolic/literal rounding mode binding).
- `solver__fp__issue130.smt2` (`:status sat`): declines as
  `unsupported construction: fp.div: unvalidated format` — the FP format
  `(eb, sb)` of this `fp.div` is outside the validated set the bit-blast accepts.

Both decline cleanly as `Unsupported` (never a wrong verdict).
