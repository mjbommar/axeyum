# ADR-0237 third full attempt (rejected)

This directory preserves the fail-closed third attempt at ADR-0237. Despite
its historical `-final` suffix, it is **not** the accepted success artifact.

- Axeyum commit: `488c90f9` plus the committed 30-second protocol
- Formula ranges: unchanged from ADR-0237
- Per-engine cap: 30,000 ms
- `uniform-a`: 4,000/4,000 four-way agreements, zero nondecisions
- `uniform-b`: 4,000/4,000 four-way agreements, zero nondecisions
- `edge-c`: 3,999/4,000 four-way agreements; Axeyum worker timeout at seed
  3,000,881; no disagreement, crash, replay gap, or other nondecision

`hard-seed-3000881.smt2` is the exact retained formula. Follow-up unchanged-
formula diagnostics establish that all four engines decide `unsat` under a
600,000 ms cap:

- Axeyum: between 120 and 600 seconds in the focused harness
- direct Z3: 25.225 seconds in isolation
- cvc5 1.3.4: 41.67 seconds in isolation
- Bitwuzla 0.9.1: 12.62 seconds in isolation

The 600-second combined diagnostic let Axeyum decide, then direct Z3 narrowly
exceeded the old 30-second cap under the loaded sequential process. This is a
real solver-bound formula, not a verdict disagreement. The next protocol keeps
every seed/formula fixed and applies the same explicit 600,000 ms bound to all
four engines. These timers are correctness-campaign resource bounds and must
not be reused as performance evidence.

