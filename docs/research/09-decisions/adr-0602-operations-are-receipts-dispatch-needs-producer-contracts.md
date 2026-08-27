# ADR-0602: Operations are receipts; dispatch requires a separate, prospective producer contract

Status: accepted
Date: 2026-08-27
Index-summary: The autogenesis operation registry is retrospective by construction (admission requires "proved"), so ADR-0601 §4's route-aware dispatch cannot be built on it; a distinct prospective producer-contract artifact is decided, with fabricating "proved" explicitly forbidden.
Index-status: accepted

## Context

ADR-0601 §4 assumed the jammed frontier selector (141 ready, 0 admissible)
could be fixed by registering route-aware operations over open facts. A
diagnostic lane (doc 288) measured why that is structurally impossible:
`validate-autogenesis-operations.py`'s `ADMISSION_CONTRACTS` is a closed set
whose every arm requires `epistemic_status: "proved"`. All 27 registered
operations name already-proved facts; zero candidate manifests exist for any
open fact. **An operation is a retrospective receipt of an independently
checked proof.** Registering one for open work would assert "proved" falsely —
the checker-that-cannot-fail defect, deliberately.

The same measurement split the 132 ready-but-unregistered facts by route:
**1 decidable** (a QF_FP fact), **125 proof-route-only** (need a kernel lane),
**6 no-route** (Collatz, CH, FLT — open in the ledger and genuinely
unreachable). So dispatch pressure is overwhelmingly on the kernel-lane route,
and any dispatch design that cannot express "send this to a proving lane" is
decoration.

## Decision

1. **Receipts stay receipts.** The operation registry's admission contract is
   correct and unchanged. Nothing prospective enters it.
2. **A producer contract is a new, separate artifact** (schema under
   `artifacts/autogenesis/`, validated by its own script): a *claim of
   capability*, not of completion — "facts matching this shape are dischargeable
   via route R with recipe X", where R is ADR-0601 §4's `kernel-lane |
   cas-bridge | import`. It carries no `proved` field at all, so the false-
   assertion failure mode is unrepresentable rather than merely forbidden.
3. **Admissibility is redefined** as: dependency-ready × matched by a producer
   contract × that route's capability existing. `fact-frontier.py` selects
   against contracts; a selection is an instruction to dispatch (for
   `kernel-lane`, a brief for a proving lane; for `import`, a row of the
   ADR-0601 §3 backlog artifact; for `cas-bridge`, a bridge invocation), and
   only the resulting *receipt* — checked, admitted — ever touches the
   operation registry.
4. **The 6 no-route facts are marked as such** in frontier output, not
   silently retried forever.

## Consequences

- The flywheel's "what next" arrow becomes buildable without corrupting the
  receipt system that keeps the ledger honest.
- Contract matching is the new falsifiable surface: a contract that matches
  everything is the vacuous-checker defect reborn, so the validator for
  contracts must reject shape predicates that match every open fact, and each
  contract needs at least one named NON-example it provably does not match.
- The held-out nursery partition (ADR-0542) binds contract-driven dispatch
  exactly as it binds manual dispatch.
