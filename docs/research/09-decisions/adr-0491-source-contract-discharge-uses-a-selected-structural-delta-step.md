# ADR-0491: Source contract discharge uses a selected structural delta step

Status: accepted
Date: 2026-08-19
Index-summary: Bind a residualized contract to its exact source with one structural delta step that consults only the selected definition and leaves residual constants opaque

## Context

ADR-0490 rejected the first `Int.gcd` reflexivity witness because its complete
declaration closure reaches 52 theorems. That is the correct rule for theorem
evidence, but it is wider than the actual source-side reduction: exposing the
stored body of `Int.gcd` needs one delta step and does not need to unfold
`Nat.gcd` at all.

Ordinary definitional equality cannot support the narrower assurance claim. It
returns a Boolean result but no record of which definitions were unfolded.
Inferring a trace from the final answer would recreate the direct-dependency
mistake in another form.

## Decision

Add an importer-side structural checker for exactly one selected transparent
definition unfold. A valid step must:

1. name one exact `Definition` and bind its canonical content identity;
2. have a `before` expression headed by that exact constant;
3. carry exactly the declaration's universe arity;
4. substitute only those universe parameters into the stored body;
5. preserve the existing term application spine; and
6. equal the proposed `after` expression structurally, without beta, zeta,
   iota, recursive delta, theorem lookup, or dependency-closure traversal.

Constants occurring in the resulting body remain opaque syntax. For the exact
`Int.gcd` control the checker consults only `Int.gcd`; `Nat.gcd` remains in the
body but is not opened. The separately checked residualized contract replaces
both functions with local binders, and exact source specialization remains
mandatory.

The step is mechanism evidence, not yet a semantic function-contract receipt.
A follow-on receipt version must bind the trace, proof-free template, exact
source identity, and specialization replay before any contract, target, proof,
or ledger credit is available.

## Evidence

- Four synthetic controls accept the exact step and preserved application
  spine while rejecting wrong heads, wrong bodies, theorem sources, and wrong
  universe arities.
- The positive helper control inspects the one-step output and confirms the
  helper application remains syntactically opaque.
- The exact pinned Mathlib `Int.gcd` control binds one selected step, one
  consulted declaration, zero recursive delta steps, and zero theorem walks.
- Its generalized contract contains neither `Int.gcd` nor `Nat.gcd` as a
  constant and specializes exactly back to the source equation.

## Consequences

The 52-theorem closure remains a hard rejection for theorem-valued witnesses;
none is whitelisted. The new trace is smaller evidence for a different claim:
the exact stored source body follows from one declared delta rule. Receipt
integration, clean replay, and real target selection remain open.
