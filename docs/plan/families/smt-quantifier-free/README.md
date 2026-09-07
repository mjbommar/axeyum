# Family: SMT, quantifier-free

Ten of the eleven divisions on the parity board, plus the three cheapest
unentered targets. This is where the measured work is.

## On the board

| Division | Gap | Cause established? | Owning lever |
|---|---:|---|---|
| [QF_SLIA](qf-slia.md) | 1 | yes, censused | width ladder + parser |
| [QF_UF](qf-uf.md) | 4 | **no** — census refuted, 4 unexplained | census, then S7 |
| [QF_BV](qf-bv.md) | 6 | yes, at the SAT level | S8 |
| [QF_RDL](qf-rdl.md) | 12 | **stale** — not re-censused since S1 | re-census, then S7 |
| [QF_ABV](qf-abv.md) | 18 | yes, censused | array shapes + S7/S8 |
| [QF_IDL](qf-idl.md) | 18 | yes, profiled and fixed twice | S7 |
| [QF_LIA](qf-lia.md) | 26 | yes, censused | S2 follow-up, cut budget |
| [QF_LRA](qf-lra.md) | 52 | yes, profiled; one diagnosis corrected | S7, S10 |
| [QF_UFLIA](qf-uflia.md) | 58 | partly — 21 files unexplained | instrument, then S7 |
| [QF_NIA](qf-nia.md) | 48 | yes, censused; three levers refuted | S12 |

Gaps are as of the divisions' latest ledger entries and move; the
[ledger](../../../../bench-results/PARITY.md) is authoritative.

**Roughly 194 of the board's remaining gap is in the arithmetic divisions**
(QF_IDL, QF_LIA, QF_UFLIA, QF_LRA, QF_NIA), which is why the plan is
arithmetic-first by weight.

## Not entered

| Division | Rank | Why |
|---|---:|---|
| [QF_NRA](qf-nra.md) | 1 | free: same format, same harness |
| [QF_UFLRA / QF_UFBV / QF_AUFLIA / QF_UFIDL / QF_AX](qf-combination.md) | 2 | compose solvers we ship; saturated logics test correctness |
| [QF_FP and family](qf-fp.md) | 6 | largest unmeasured capability we have |

Seventy-odd further SMT-LIB logics exist and are catalogued in
[the survey](../../../research/02-ecosystems/competition-landscape-2026-09/smt-lib-and-smt-comp.md).
They are not targets until the three above are done.
