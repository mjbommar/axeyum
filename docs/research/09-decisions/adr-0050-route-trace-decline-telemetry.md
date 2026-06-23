# ADR-0050: Route-trace / decline telemetry as a verdict-invariant addition

Status: accepted
Date: 2026-06-22

## Context

The gap audit ([gap-analysis-z3-cvc5-2026-06-22](../../plan/gap-analysis-z3-cvc5-2026-06-22.md),
Gap 4 / recommended increment #6) and the reviewing agent both asked for a
**strategy/probe layer with provenance**: a way to see which dispatch routes
`check_auto` tried and *why* each declined (size cap, theory unsupported, proof
required, timeout, verifier failure). This was named as a prerequisite for the
larger lazy-CDCL(T) dispatch push — you cannot safely reorder or extend routing
you cannot observe.

The risk is that instrumenting the central dispatcher (`auto.rs`,
`check_auto` → `check_auto_inner` → `check_auto_dispatch` plus the special
routes) silently changes a verdict. `check_auto` is the trusted entry point for
every quantifier-free query; a behavioural drift here is a soundness event.

## Decision

**Add `check_auto_explained(arena, assertions, config) -> (CheckResult,
RouteTrace)` as a PURELY ADDITIVE layer over a single dispatch path.** Both
`check_auto` and `check_auto_explained` call one internal
`check_auto_with_recorder(.., rec: &mut Recorder)`, where `Recorder` is an
`Option<&mut RouteTrace>`:

- `check_auto` passes the absent recorder and returns only the `CheckResult`;
- `check_auto_explained` passes a live recorder and returns the trace too.

Recording happens at the **existing** decide/decline sites and **never
participates in a branch condition** — so the control flow, and therefore the
verdict, is identical with or without a recorder. That is the structural
guarantee of *verdict invariance*. No decider module is touched; the only
`auto.rs` changes are recording side-effects plus two verbatim helper
extractions (to keep functions ≤100 lines) whose `Some`/`None`/`return`
semantics reproduce the original fall-through exactly.

The `DeclineReason` taxonomy **reuses `UnknownKind`/`UnknownReason`** rather than
inventing a parallel one: `Unsupported`, `NotApplicable`, `Budget(detail)`,
`Incomplete(UnknownReason)`, `VerifierRejected(detail)`. A cheap deterministic
**probe** (reusing the existing `Features::scan` + `contains_quantifier`, no new
fragment engine) records the classified fragment as the trace's first entry.

## Evidence

- **Verdict-invariance differential (load-bearing):** a 400-query deterministic
  LCG corpus spanning QF_BV (sat+unsat), conjunctive/Boolean QF_LIA, QF_LRA,
  QF_UF, mixed BV+int, and an undecided nonlinear case asserts
  `check_auto_explained(..).0 == check_auto(..)` exactly (Sat by model replay,
  Unknown by kind) — 0 mismatches.
- **Determinism:** the trace (`Eq` and `Display`) is byte-identical across runs.
- **Well-formedness + per-route unit traces:** probe-first; terminal `Decided`
  iff Sat/Unsat and terminal `Declined` iff Unknown; a QF_BV decided sat/unsat,
  an unsupported fragment (all routes `Declined(Unsupported)`), a resource-capped
  LIA (`Budget`).
- The 380 existing `axeyum-solver` lib tests pass unchanged.

## Alternatives

- **Duplicate the dispatch order in a separate explained driver.** Rejected: two
  routing copies drift, and drift here is a verdict-correctness risk; the single
  recorder-threaded path cannot diverge from itself.
- **A new decline-reason enum.** Rejected: `UnknownKind` already encodes the
  reasons; a parallel taxonomy would desync from the engine's own `Unknown`
  detail.
- **Skip telemetry, reorder routing directly.** Rejected: the reviewer gated the
  CDCL(T) dispatch push on observability; routing you cannot trace you cannot
  safely change.

## Consequences

- New diagnostics surface (`check_auto_explained`, `RouteTrace`, `RouteAttempt`,
  `RouteOutcome`, `Verdict`, `DeclineReason`) on `axeyum-solver`; a capability
  ledger row (diagnostics, `Validated` — verdict-invariant, differentially
  guarded) accompanies it.
- The recorder is the seam the future strategy/probe scheduler and the SMT-LIB
  `(get-info :reason-unknown)` surface plug into.
- Deferred: sub-route granularity inside the SAT/bit-blast core, per-width
  int-blast-ladder detail, and the quantified `solve()` special routes (FM/MBQI/
  e-matching) — additive future increments on the same recorder.
