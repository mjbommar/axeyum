# ADR-0233: QF_BV timeout-frontier sweep

Status: accepted
Date: 2026-07-18

## Context

The reviewer checklist rejects a speed comparison that rewards whichever
backend times out first. The historical tcpip split recorded 52 exact,
post-concat-fix, well-typed formulas where one backend decided and the other did
not at 250 ms, but artifact v31 skipped Z3 whenever Axeyum returned `unknown`.
It therefore could not reconstruct the required both-decided, Axeyum-only,
Z3-only, and neither populations.

ADR-0215/0217 already provide the fair retained-warm four-cell map, and
ADR-0232 provides a neutral retained-topology control. The remaining question
here is narrower: how cold decision coverage and solved-only latency change
when timeout is swept on a real hard-formula frontier, with a neutral solver
checking that Z3 is not the sole oracle.

## Decision

Advance `axeyum-bench` to artifact version 32. Always run the in-process Z3
oracle after a successfully parsed QF_BV query, including when the primary
backend returns `unknown`; partition every query into the four decision
populations. Permit Z3 binary fallback only after an in-process `unsupported`,
never after a real QF_BV timeout.

Accept the hash-bound 52-formula tcpip shadow-split manifest as a one-shot
timeout-frontier control at 50, 100, 250, and 1000 ms. Require five fresh,
CPU-pinned Axeyum/Z3 processes per tier, identical input/config/source identity
apart from timeout, and a fresh-process cvc5 1.3.4 neutral sweep over every
formula and tier. Treat `unknown` as a reported nondecision. Fail on any
operational error, replay failure, decided manifest disagreement, or SAT/UNSAT
contradiction across solver, repetition, or timeout.

Use only queries both Axeyum and Z3 decide in every repetition of a timeout
cell for paired latency. Report Axeyum/Z3 per-query geomean, deterministic
bootstrap 95% interval, latency quantiles/CDF samples, repetition variance, and
outcome drift. Keep cvc5 subprocess timing separate from the in-process ratio.

Classify the result as **cold deduplicated formula-regime evidence**, not a
retained-warm Glaurung speed headline or authoritative finding-parity result.

## Evidence

At clean Axeyum revision `befe1ba4`, all 20 artifact-v32 Axeyum/Z3 runs and all
1,040 cvc5 rows pass the fail-closed analysis. Every decided verdict matches
the manifest; there are zero operational errors, replay failures, decided
disagreements, or cross-solver SAT/UNSAT contradictions.

| timeout | Axeyum decided | Z3 decided | cvc5 decided | both / A-only / Z-only / neither | fixed paired | Axeyum/Z3 geomean [95% CI] |
|---:|---:|---:|---:|---:|---:|---:|
| 50 ms | 28 | 13 | 46 | 13 / 15 / 0 / 24 | 13 | 0.14165 [0.11136, 0.19907] |
| 100 ms | 30 | 25 | 51 | 25 / 5 / 0 / 22 | 25 | 0.14548 [0.10539, 0.21313] |
| 250 ms | 41 | 33--34 | 52 | 30 / 11 / 3--4 / 7--8 | 30 | 0.14112 [0.09622, 0.21343] |
| 1000 ms | 52 | 52 | 52 | 52 / 0 / 0 / 0 | 52 | 0.21095 [0.14904, 0.29644] |

Axeyum's outcome population is stable at every tier. Z3 has one 250 ms drift
query, decided in four of five runs; fixed paired timing excludes it. cvc5 is
stable in the accepted pinned run and decides the complete corpus by 250 ms.
The per-repetition paired-geomean CV is 0.12--0.35%.

The 1000 ms tier removes solved-subset selection because all 52 formulas are
jointly decided. Its 0.21095 Axeyum/Z3 geomean establishes a strong Axeyum cold
one-shot win on this exact hard-frontier corpus. It does not identify how much
comes from FFI/context setup, word representation, or search, and does not
reverse the workload-dependent retained-warm map.

Exact artifacts and the joined analysis are committed under
[`bench-results/glaurung-tcpip-timeout-sweep-20260718/`](../../../bench-results/glaurung-tcpip-timeout-sweep-20260718/README.md).

## Alternatives

- Compare ratio-of-sums over every query: rejected because nondecisions and a
  few hard rows dominate it.
- Run Z3 only when Axeyum decides: rejected because it hides Z3-only and
  neither-decided populations.
- Replace in-process Z3 timeout with a binary retry: rejected because it
  changes the execution boundary precisely on the hard rows.
- Require outcome stability as an acceptance condition: rejected because
  timeout-boundary drift is part of the result; decided contradictions remain
  fatal, while decision/Unknown drift is named and excluded from the fixed
  paired set.
- Divide cvc5 subprocess time into the Axeyum/Z3 ratio: rejected because
  startup, textual parsing, and model serialization are different boundaries.

## Consequences

The paper now has an executable timeout-sensitivity result with complete
decision-population accounting and a neutral third solver. It may state that
Axeyum wins this cold one-shot tcpip formula regime, including the all-decided
1000 ms tier, but may not generalize that to the retained warm integration.

The timeout-sensitive neutral formula blocker is closed. Wider/timeout-
sensitive sole-authority finding parity remains open because this deduplicated
corpus has no exploration or findings. The next correctness-led work remains
real-query term-to-CNF faithfulness, independent fuzz seeds and another neutral
implementation, and whole-certificate process isolation.
