# ADR-0139: Kernel-checked BV universal counterexamples

- **Status:** accepted
- **Date:** 2026-07-13
- **Owners:** solver / evidence / Lean reconstruction
- **Extends:** ADR-0100, ADR-0138

## Context

ADR-0100 checks concrete counterexamples to closed scalar universals by
evaluating the untouched source body. ADR-0102 reconstructed the Int/Bool
instances, but the public quantified-BV row `qbv-simp` still lacked a genuine
Lean proof. ADR-0138 established typed Bool/BV values and an explicit evaluated
AIG proof for a concrete assignment, so the same proof spine can apply here
without a SAT-resolution tail.

The adjacent ADR-0127 row was evaluated first because it appeared to reuse the
ADR-0135 source-instance machinery. Its public 32-bit multiplier residual
contains 15,705 Alethe commands and repeated 4,700--5,000-premise RUP chains;
the reconstructed proof requested a 2.18 GiB allocation and failed safely under
the 4 GiB guard. That family therefore needs compact reflected-RUP checking and
is not the smallest next reconstruction slice.

## Decision

Add a distinct `BvClosedUniversalCounterexample` proof fragment.

1. Re-run the ADR-0100 original-IR certificate checker.
2. Encode the untouched closed Bool/BV universal with typed Bool and width-exact
   bit-vector domains.
3. Apply the source theorem to the exact carried constructor values.
4. Lower the untouched body through the existing AIG semantics and build a
   proof for every evaluated gate. Because the carried assignment makes the
   root false, the result is a proof of the negated body.
5. Apply that negative proof to the genuine source instance and require the
   kernel to infer exactly `False`. No SAT proof, theorem-specific refuter, or
   `sorryAx` enters the module.

The route admits only a direct nonempty Bool/BV universal chain with a closed
quantifier-free body and Lean bit-vector widths 1 through 64. Other source
shapes continue to their existing routes or decline.

## Consequences

- `qbv-simp` reconstructs in 0.08 seconds in the focused debug test.
- The exact public audit remains 54/54 evidence-certified/rechecked with zero
  mismatch, audit error, or timeout; dominant candidates rise 48→49 and Lean
  UNSAT coverage rises 12/18→13/18.
- The evaluator still grants no proof authority: certificate replay gates entry,
  while the kernel checks the typed source application and every AIG gate.
- ADR-0127 remains evidence-checked but not Lean-reconstructed until a compact
  RUP reflection route replaces its multi-thousand-premise proof expansion.

## Validation

- public `qbv-simp` direct/router determinism and tampered-witness rejection;
- representative external-Lean registration (skips when no `lean` binary is
  installed);
- full focused closed-counterexample suite; and
- refreshed exact quantified-BV dominance audit and dashboard.
