# ADR-0562: Boolean ANF interchange keeps external algebra untrusted

Status: accepted
Date: 2026-08-26
Index-summary: Export bounded canonical Boolean ANF systems while replaying SAT witnesses and withholding credit from uncertified rewrites

## Context

ADR-0561's complete truth-row CNF is an auditable multiplicative-complexity encoding, but it
does not exploit the sparse algebraic structure used by specialist Boolean solvers. The
published `PRIMATEs^-1 >= 7` control must be reproduced before attempting its open seven-AND
boundary. A reusable algebraic interchange is useful beyond this instance, but an external
simplifier's output is not automatically equivalent to the Axeyum source system.

## Decision

Add canonical multivariate Boolean polynomials to `axeyum-cas`. Monomials are square-free
sorted variable sets, addition is symmetric difference, multiplication uses `x^2=x`, and
systems enforce explicit variable, equation, per-polynomial, and total-monomial ceilings.
Serialization targets Bosphorus's line-oriented ANF syntax deterministically.

Add a sparse coefficient-DAG encoding for the complete affine-between-AND normal form. It
allocates selector variables plus coefficient variables for each intermediate affine form,
AND output, and coordinate output. Equations define every auxiliary coefficient and bind the
complete target ANF. A returned assignment is accepted only if it satisfies the original
Axeyum system and its selectors lift to an ADR-0558 circuit that replays the full truth table.

External ANF simplification and ANF-to-CNF conversion remain untrusted transformations. SAT
can become evidence only after the original ANF assignment is reconstructed and replayed;
UNSAT receives no credit without a checked equivalence chain from the original system to the
refuted formula. A timeout, interrupted solver, or incomplete proof file is not retained as
a certificate.

## Evidence

- Canonical arithmetic tests cover idempotent products, cancellation, stable serialization,
  equation evaluation, and resource-bounded system construction.
- The sparse encoding's zero-AND boundary is exhaustive over all sixteen two-input Boolean
  functions; a satisfying one-AND assignment lifts and replays for the AND function.
- The PRIMATEs inverse six-AND control exports 738 variables, 759 equations, and 8,835
  monomials in 133,154 bytes (SHA-256 `5fc1286e...b2b2`).
- Bosphorus 1.2.12 reduces that system to 586 free variables, 603 equations, and 6,157
  monomials, then emits 5,782 variables and 62,674 CNF clauses. This is performance data,
  not trusted equivalence evidence.
- CaDiCaL on the independently generated 6,322-variable / 21,559-clause truth CNF remained
  unknown after 300 seconds and 11,515,089 conflicts. CryptoMiniSat on the Bosphorus CNF
  remained indeterminate after 300 seconds and 6,066,101 conflicts. Bosphorus solve mode
  exceeded its requested 300-second limit and was interrupted. No lower bound is credited.

## Consequences

- Axeyum gains a reusable, deterministic, resource-bounded Boolean-polynomial interchange and
  a much smaller exact multiplicative-synthesis representation.
- The trusted boundary remains narrower than the available external tooling: original-system
  SAT replay is specified, but certified algebraic preprocessing and external model-map import
  are future work.
- The known MC=6 lower control remains unreproduced. MC=7 search is premature until that
  control completes with a certificate checked against the exact source problem.
