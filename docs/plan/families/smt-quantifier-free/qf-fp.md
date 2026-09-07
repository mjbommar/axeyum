# QF_FP and the floating-point family

<!-- Family: [SMT, quantifier-free](README.md) · Plan: [PLAN.md](../../../../PLAN.md) -->

**State:** not entered. **Rank among cheap targets: 6.**

There is no ledger row for this division. Nothing here is a measurement; it is
a statement of what entering would cost and what it would tell us.

| | |
|---|---|
| Corpus size (SMT-LIB 2024 non-incremental) | 40,407, plus QF_ABVFP 18,129 and QF_BVFP 17,249 |
| 2026 frontier | Bitwuzla and bitwuzla-dandelion; **an interval solver leads the 24-second score on QF_FP** |
| Harness changes needed | A list, and **two** reference solvers rather than one. |

## Why this one

`axeyum-fp` exists, and its generic exponent/significand design already covers the GPU and ML precisions (ADR-0023). This is the largest unmeasured capability in the repository.

## What entering requires

A committed list, and two oracles: the 2026 results show floating-point disagreements splitting bit-blasting solvers against the interval solver, so a single oracle cannot adjudicate this family. See the survey, section 1.9.

## Exit criterion for the entry slice

A committed benchmark list, a reference build pinned by version, one ledger
entry with zero disagreements, and a census of the losses **before** any
capability slice is authorised. Entering is a measurement task; it is finished
when the row exists, not when the ratio is good.

## Owning documents

- [The survey](../../../research/02-ecosystems/competition-landscape-2026-09/README.md), section 2
- Measurement protocol: `scripts/parity-run.sh`
