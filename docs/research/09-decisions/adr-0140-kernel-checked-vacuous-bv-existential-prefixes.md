# ADR-0140: Kernel-checked vacuous BV existential prefixes

- **Status:** accepted
- **Date:** 2026-07-13
- **Owners:** solver / evidence / Lean reconstruction
- **Extends:** ADR-0128, ADR-0138, ADR-0139

## Context

ADR-0128 independently checks `issue2031-bv-var-elim` by proving the leading
Bool/BV existential binders absent from the closed universal body and evaluating
one complete universal assignment to false. The evidence had no Lean route.
ADR-0138 and ADR-0139 established typed Bool/BV domains plus logical and
computational AIG reduction, so the remaining proof obligation is the genuine
elimination of the untouched existential prefix.

An explicit gate-by-gate prototype failed safely under the 4 GiB guard after a
1.42 GiB contiguous allocation request. The computational gate-let encoding
removed that heap blow-up, but its thousands-deep proof term overflowed a
default test-thread stack. This is a proof-worker resource boundary, not a
reason to weaken the source statement or trust the prefix rewrite.

## Decision

Add `BvVacuousExistsUniversalCounterexample` as a distinct proof fragment.

1. Re-run the ADR-0128 original-IR certificate checker.
2. Encode the untouched `exists+ forall+` Bool/BV source. The existential
   predicates are definitionally constant only because the checker has already
   proved every existential binder absent.
3. Eliminate each leading existential with the kernel prelude's `Exists.rec` at
   a constant `False` motive. No witness is invented or assumed.
4. Apply the surviving universal to the certificate's exact typed constructor
   values.
5. For small bodies, reuse the explicit evaluated-AIG negative proof. For large
   bodies, use shared reducible computational Bool operations and local gate
   lets; the kernel reduces the exact instantiated source body to `False`.
6. Run this potentially deep reconstruction on a scoped 64 MiB worker stack.
   Thread creation or a worker panic is an ordinary reconstruction error. The
   4 GiB release gate remains authoritative for total memory.

The route retains ADR-0128's exact nonempty direct prefix, closure, sort,
binder, and source-node limits, with Lean BV widths restricted to 1 through 64.

## Consequences

- The public `issue2031-bv-var-elim` proof reconstructs twice (direct and routed)
  in 16.54 seconds in optimized mode. The cold build-and-test gate takes 38.04
  seconds and peaks at 1,975,764 KiB RSS under 4 GiB.
- Its generated module is 28,791,505 bytes and contains no `sorryAx`.
- The exact 54-row audit remains fully decided, evidence-certified, and
  evidence-checked with zero mismatch, audit error, or timeout. Dominant
  candidates rise 49→50/54 and Lean UNSAT coverage rises 13→14/18.
- The independent evaluator remains a gate, not a proof authority: the final
  `False` exists only if `Exists.rec`, typed universal application, and
  computational reduction all pass the kernel.

## Validation

- a small non-enumerated direct/router `Exists.rec` regression;
- public direct/router determinism under `just
  test-quant-vacuous-exists-lean-stress`;
- tampered universal-value rejection;
- representative external-Lean registration (skips honestly without `lean`);
  and
- the refreshed exact quantified-BV dominance audit and dashboard.
