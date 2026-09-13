# Lane: dt-exactness — the cheap check was the whole target

<!-- plan-section: lane-status -->

**Lane dt-exactness (`DONE`, dt-exactness, 2026-09-13).** [ADR-1975] handed over
**124 winnable rows across three divisions**, all blocked by
`datatype_expansion_is_exact`, and named the step it had not taken: run
[ADR-1966]'s check on the three refusal sites first, because a rung BELOW may
own the construct and then the fix is a DECLINE rather than a capability.

**It comes out positive, and the answer was already on disk.** The three
sentences are produced in `datatype_native.rs` but PROPAGATED at
`check_auto_dispatch`'s bare `?` — the one site ADR-1966 sized at **+22 / −2 on
`AUFDTLIRA`** and reverted, because it turned 7 assertions red in four other
ADRs' suites. This lane builds the one prerequisite ADR-1966 named, takes the
site, and moves each blocked assertion to where its guard actually lives.

ADR: [ADR-1980](../../research/09-decisions/adr-1980-the-cheap-check-was-the-whole-target-a-dispatch-decline-not-a-datatype-capability.md)
· artifact: [`bench-results/dt-exactness-20260913/`](../../../bench-results/dt-exactness-20260913/README.md)
· A/B: [`AB.md`](../../../bench-results/dt-exactness-20260913/AB.md)

## The measurement

| division | base | arm | net | gain | loss | flips |
|---|---:|---:|---:|---:|---:|---:|
| UFDTLIRA | 105 | **143** | **+38** | 38 | 0 | 0 |
| UFDT | 31 | **50** | **+19** | 19 | 0 | 0 |
| AUFDTLIRA | 96 | **118** | **+22** | 24 | 2 | 0 |
| **total** | **232** | **311** | **+79** | **81** | **2** | **0** |

Every one of the 83 moved rows re-run **3× per arm**: 81 STABLE-GAIN, 2
STABLE-LOSS, **0 UNSTABLE, 0 FLIP**. **240 independent comparisons** against
`:status`, z3 4.13.3 and cvc5 1.3.4, **0 disagreements**, with the comparable
denominator published per authority (80/81, 79/81, 81/81).

**Every base value reproduces `main` exactly** — UFDTLIRA 105, AUFDTLIRA 96,
UFDT 31 — which is the evidence that this is not a branch-only number.

`AUFDTLIRA` comes out **+24 / −2 from a base of 96**, reproducing ADR-1966's
**+22 / −2 from a base of 90** exactly. Two lanes, baselines six files apart,
identical delta.

## No encoding changed

`datatype_expansion_is_exact`, `field_sort_expands` and every
ADR-1920/1935/1942/1946 precondition fire on exactly the same queries under both
arms, so the inexact congruence clause [ADR-1930] shipped a wrong `unsat` from
is still never emitted. Only the dispatcher's handling of the refusal changed.

## What is left, and the correction it forces

**80 of the 124 converted (65 %).** The 44 that did not are the honest remainder
for the recursive expansion — but **ADR-1975's description of them no longer
holds.** It measured them declining with "a median 23.9 s of 24 s UNSPENT — a
shape refusal, not a clock problem"; they now spend a median of 1.4 s / 3.0 s /
**17.4 s** by division. They have moved from SHAPE-bound to searching and
failing. A lane taking that capability must re-census rather than inherit the
decline-time figure.

## Landed changes

| commit | what |
|---|---|
| `7b1e88363` | the ADR-1966 check, and the pre-registered sizing bracket |
| `7678a3e21` | the decline conversion, the message relabel, the lever, all 7 blocked assertions |
| `e5f6764ba` | mutation controls (4) and the A/B runner whose polarity is inverted |
| `78fcd2b26` | the reference verifier could not read `:status` at all |
| `d11e75f35` | movers / 3×-re-check / noise-floor instruments |
