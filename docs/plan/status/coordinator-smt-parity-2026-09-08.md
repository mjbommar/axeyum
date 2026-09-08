# coordinator-smt — the parity push of 2026-09-08

<!-- plan-section: lane-status -->

Status: **in progress**, four lanes running. ~11,000 lines of source-level
research against Kissat, CaDiCaL, Z3, cvc5, Bitwuzla, Boolector, Yices2 and ABC
landed, plus measured gains in three divisions.

## The finding that redirected the day

85% of the parity gap is **arithmetic**, not bit-vectors
([where-the-gap-actually-is.md](../where-the-gap-actually-is.md), `d3848c656`).
QF_BV is already at 96.9%. Closing bit-vectors completely would move 24 files;
QF_UFLIA alone is 58. Independently confirmed the same hour by a controlled
ablation showing vivification is worth +5 to +9 of 400 on generic sets.

**We are not missing the algorithms.** Read from source, we already have the
Dutertre-de Moura simplex, delta-rationals, Farkas certificates, Cotton-Maler
incremental difference logic, model-based combination, Gomory cuts,
branch-and-bound, and NIA linearization. The pattern in every division is that
a route we own **does not run, runs on a fraction of the budget, or re-solves
from scratch what it should update**.

| division | result | mechanism |
|---|---|---|
| QF_UFLIA | **116 -> 125 decided** (+10/-1, 0 disagreements) | 4 routes were unreachable above 64 congruence pairs; the CEGAR returned its own `Unknown` as final |
| QF_LIA | losses **26 -> 23** | admission rectangle justified by a retired SAT solver's allocator; measured 71 MiB at 7.7x the bound against an 8 GiB ceiling |
| QF_LRA | **+1**, 0 losses | swappable entering rule; Bland's was unconditional |

## Infrastructure landed

- **Deterministic work budget** (`axeyum-ir/src/budget.rs`) — ticks derived from
  counters we already keep, zero hot-path cost, proven identical across
  processes and under load, and used by a non-SAT route to show it generalizes.
  Budgets were wall-clock at 312 sites across 58 files against 5 deterministic.
- **Timeouts no longer discard instrumentation.** Counters moved out of
  thread-local into a shared board plus a mid-search mirror; a kill now reports
  partial data labelled by its leading token.
- **Three-tier clause database** with computed boundaries — 25% fewer conflicts,
  blocked on watch-visit cost (a lane is on it).
- **71% of BVE's cost and 53% of subsumption's recovered** by work meters and
  admission gates. Inprocessing is still **not** a net win at 24 s and stays off.
- **Unconstrained elimination 6 -> ~30 rules** across three theories, free at
  corpus scale, **no verdict changed** — the published win is on
  symbolic-execution output, which our corpus is not.
- **A gate that fails when a limit's justification expires**, after finding 52 of
  70 registry entries undated and 75 more limits outside the registry.
- Fixed three pre-existing breakages: the wasm32 build, 91 rustdoc errors, and
  the `axeyum-py` link.

## Corrections worth keeping

Seven of my own claims were refuted by lanes that measured them: the ~120 s
break-even (it is 12-24 s), a `sat` reconstruction blocker that does not exist,
a sparse-tableau headline that was the wrong ranking (the pivot's operation
count was already sparse; the cost was scans around it), "one shared simplex for
four divisions" (nobody does this), leading with Gomory cuts (cvc5 implements
none; Yices's path is `if (false && ...)`), and two premises aimed at code the
target division never executes.

The pattern: **reliable when computing, unreliable when relaying.** Briefs now
require each lane to verify a handed-down claim before building on it, and seven
directions were killed on evidence.

Also: an entering rule is a **search-trajectory** change whose effect is
uncorrelated with per-pivot cost and core width — both refuted by counters. Same
shape as the clause database's 25% fewer conflicts at 28% more work.
