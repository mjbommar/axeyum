# ADR-0538: Theory-core minimisation is rationed by oracle calls, not by core width

Status: accepted
Date: 2026-08-21
Index-summary: Lazy-LIA core minimisation is gated by a deterministic oracle-call budget; core width now only decides retention accounting

## Context

`crates/axeyum-solver/src/dpll_lia.rs` had one constant doing two jobs.
`MAX_MINIMIZED_THEORY_CORE_ATOMS = 128` decided **whether deletion minimisation
was attempted** on a theory conflict core, and — because a core that skipped
minimisation was tagged `Large` — it also decided **which cores were charged
against `MAX_DYNAMIC_LARGE_CORE_LITERALS = 8_192`**, the retention budget that
exists because 24 retained clauses of roughly 430 literals once grew `BatSat`
from 1.8 GiB to an 8 GiB abort.

Those two jobs pull in opposite directions, and the 2026-08-21
[linear-arithmetic deficit diagnosis](../05-algorithms/linear-arithmetic-deficit-diagnosis-2026-08-21.md)
§5.2 measured the consequence: **the cores too wide to minimise are exactly the
cores whose width then exhausts the retention budget**, so a solve declines for
want of the narrow clauses it refused to narrow. On the pinned QF_UFLIA
competition list, 48 files returned `unknown` after a median 1.3 s of a 24 s
budget reporting `core_src_minimized=0` beside `core_src_large=24`. That note
also measured the naive repair (raise the constant to 4 096) and stated
explicitly that it is **not** what should ship, because it buys its files by
making wide cores stop counting against the memory protection.

## Decision

**Minimisation is rationed by a deterministic work budget counted in conjunctive
theory-oracle calls; core width is retained only as the accounting threshold for
what consumes the wide-clause retention budget.**

- `MINIMIZATION_ORACLE_CALL_BUDGET = 4 * MAX_DYNAMIC_LARGE_CORE_LITERALS`
  (32 768), cumulative over one `IncrementalArithDpll` — the same lifetime as the
  retention budget it is paired with. One deletion candidate is exactly one
  oracle call, charged before the call is issued.
- Exhaustion returns the partially minimised core, which is always a valid
  conflict core, and counts the decline (`min_declined_cores`). The budget
  degrades core quality, never soundness.
- The pre-existing wall-clock deadline poll inside `minimize_core` stays as the
  outer safety bound, because a single oracle call can run for tens of seconds
  and no work budget can interrupt work already in flight.
- `MAX_MINIMIZED_THEORY_CORE_ATOMS` is renamed `WIDE_THEORY_CORE_ATOMS`, keeps
  the value 128, and now governs only this: a **retained** core wider than it
  charges its full width to `MAX_DYNAMIC_LARGE_CORE_LITERALS`, whatever its
  provenance.

## Evidence

Whole-division A/B on the committed 200-file competition lists, three binaries
plus z3 4.13.3 run **adjacent in time per file** so contention is shared across
the arms. Full method and per-file data:
[budget-driven theory-core minimisation](../05-algorithms/budget-driven-theory-core-minimisation-2026-08-21.md)
and `bench-results/lia-core-minimisation-20260821/`.

- QF_UFLIA: baseline **92** (reproducing the diagnosis's 92 exactly), the naive
  constant bump **112**, this decision **114** — **+22, −0**, with **0
  disagreements against z3 and 0 against the declared `:status`** over all 114
  decided files, and no cross-arm verdict conflict on any of the 200.
- This decision **strictly dominates** the constant bump on that population: it
  decides everything the bump decides plus two more, while keeping the memory
  protection the bump gives up.
- The decline it targets — `retained N literals in unminimized theory cores` —
  occurs 31 times in the baseline arm and **0 times in 400 patched runs**.
- QF_IDL as the control (the same route is on its ladder): see the note.
- Seven of eight guard mutations kill exactly one test each; the survivor is a
  pre-existing arm whose unreachability is documented rather than papered over.

## Alternatives

- **Raise the width gate (128 → 4 096).** The measured A/B, and refused as the
  shipped form: it exempts wide cores from the retention budget rather than
  giving them a chance to become narrow, and it measured *worse* here anyway.
- **A wall-clock minimisation budget.** Rejected on the determinism promise: the
  learned clause set, and therefore the verdict on a marginal instance, would
  become a function of machine load. Wall clock stays only as the outer bound it
  already was.
- **Charge the retention budget by provenance, as before.** Rejected because a
  minimised core that is still 300 literals wide costs the warm propositional
  solver exactly what an unminimised one of that width costs. While minimisation
  was width-gated the two notions agreed; they no longer do, and width is the one
  that matches the hazard.

## Consequences

- QF_UFLIA's largest non-parse loss class stops being a policy artefact. The
  files that remain undecided in that division now fail on the **pre-SAT skeleton
  envelope** (`MAX_PRE_SAT_ARITH_ATOMS` / `MAX_PRE_SAT_CNF_VARS`) — a different
  constant, and the diagnosis's separate `S2` class, which is where the next
  increment on this route belongs.
- Where the new budget sits relative to demand is **unmeasured**: its counters
  print only in the two in-loop resource declines, and neither fired on the swept
  population — the retention decline is gone, and the timeout decline is erased
  by `dispatch_reduced` before a consumer sees it. That erasure (diagnosis §2)
  now has a second, concrete cost, and fixing it would make this constant
  observable.
- `MAX_MINIMIZED_THEORY_CORE_ATOMS` no longer exists; documents citing it should
  read `WIDE_THEORY_CORE_ATOMS` for the accounting threshold and
  `MINIMIZATION_ORACLE_CALL_BUDGET` for the admission decision.
