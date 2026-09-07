# QF_NRA — nonlinear real arithmetic

<!-- Family: [SMT, quantifier-free](README.md) · Plan: [PLAN.md](../../../../PLAN.md) -->

**State:** not entered. **Rank among cheap targets: 1.**

There is no ledger row for this division. Nothing here is a measurement; it is
a statement of what entering would cost and what it would tell us.

| | |
|---|---|
| Corpus size (SMT-LIB 2024 non-incremental) | 12,154 files |
| 2026 frontier | Z3-GEX, then Z3-alpha2; SMT-RAT leads the quantified NRA |
| Harness changes needed | **None.** Same input format, same 24 s / 8 GiB protocol, same runner. |

## Why this one

It is a division of SMT-COMP itself and the cheapest possible addition to the board: the runner needs nothing new. We ship nonlinear real routes and CAS-backed certificates and have never scored either against a reference, so we do not know whether this is a strength or a hole.

## What entering requires

A committed 200-file list, a reference build, one ledger entry, then a census.

## Exit criterion for the entry slice

A committed benchmark list, a reference build pinned by version, one ledger
entry with zero disagreements, and a census of the losses **before** any
capability slice is authorised. Entering is a measurement task; it is finished
when the row exists, not when the ratio is good.

## Owning documents

- [The survey](../../../research/02-ecosystems/competition-landscape-2026-09/README.md), section 2
- Measurement protocol: `scripts/parity-run.sh`
