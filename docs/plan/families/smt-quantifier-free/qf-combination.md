# The quantifier-free combination logics — QF_UFLRA, QF_UFBV, QF_AUFLIA, QF_UFIDL, QF_AX

<!-- Family: [SMT, quantifier-free](README.md) · Plan: [PLAN.md](../../../../PLAN.md) -->

**State:** not entered. **Rank among cheap targets: 2.**

There is no ledger row for this division. Nothing here is a measurement; it is
a statement of what entering would cost and what it would tell us.

| | |
|---|---|
| Corpus size (SMT-LIB 2024 non-incremental) | 5,276 across the five |
| 2026 frontier | Yices2, OpenSMT, SMTInterpol and bitwuzla-dandelion, depending on the logic |
| Harness changes needed | One committed list and one reference per logic. |

## Why this one

Each composes theory solvers we already ship, so the marginal implementation cost is close to zero. Several are near-saturated for every entrant — the leaders solve 300 of 300 on one and 505 of 505 on another — which makes them a test of **correctness under combination** rather than of power. That is the cheapest way we have to surface a dispatch or soundness bug, because on a saturated logic any miss is a finding rather than a ranking.

## What entering requires

Five lists and five references. Expect high ratios immediately; a low one is the interesting outcome.

## Exit criterion for the entry slice

A committed benchmark list, a reference build pinned by version, one ledger
entry with zero disagreements, and a census of the losses **before** any
capability slice is authorised. Entering is a measurement task; it is finished
when the row exists, not when the ratio is good.

## Owning documents

- [The survey](../../../research/02-ecosystems/competition-landscape-2026-09/README.md), section 2
- Measurement protocol: `scripts/parity-run.sh`
