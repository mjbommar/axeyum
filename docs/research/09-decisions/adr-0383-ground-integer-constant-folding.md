# ADR-0383: Ground integer constant folding, declining underspecified division

- Status: proposed
- Date: 2026-08-12
- Deciders: (pending review)

## Context

The canonicalizer's generic constant fold matched only `Bool`/`BitVec`
literals, so a ground integer term such as `(div 48 4)` survived
canonicalization verbatim and reached the backend as *structure*, not as
`12`. Every distinct spelling of the same integer became a distinct
argument term: an uninterpreted application `(c (+ (div 48 4) 1))` is not
syntactically `(c 13)`, so the congruence/Ackermann machinery had to prove
the arguments equal, and the integer encoder blasted a divider for a term
with no variables in it. Measured on a ground `QF_UFLIA` probe holding
everything else fixed and varying only the spelling of an integer: up to
**49× slower**, and two otherwise-decided instances turned into timeouts
(roadmap item R4 / finding A6 in
[the 2026-08-12 findings register](../../plan/findings-register-2026-08-12.md)).

The same gap had a second, worse face in `propagate_values`: its
`ground_constant` reified *any* ground term through the total evaluator,
including `div`/`mod` by zero — which SMT-LIB leaves **total but
underspecified**. Pinning a variable to the evaluator's in-tree convention
(`div a 0 = 0`, `mod a 0 = a`) refutes formulas that are satisfiable under
a different underspecified value: `(= x (div 5 0)) ∧ x > 100` returned
`unsat` through the shipped front door while it is `sat`. That is the P0
wrong-`unsat` class regressed by `a946f925` and fixed by `52f3b1d1`, and a
Hard Rule in CLAUDE.md exists specifically because of it.

## Decision

1. **`int.const_fold.v1`** (`crates/axeyum-rewrite/src/canonical.rs`,
   `fold_ground_int`): fold an application whose operands are all `Int`
   literals into the literal it denotes, for exactly the operators whose
   SMT-LIB value is *uniquely determined* by the operands — `+`, `-`, `*`,
   unary `-`, `abs`, `int.pow2`, `<`, `<=`, `>`, `>=`, `=`, and `div`/`mod`
   **with a non-zero constant divisor**.
2. **The folded value is an evaluator call, not a reimplementation.** The
   rule rebuilds the application and returns whatever `axeyum_ir::eval`
   yields under the empty assignment, so agreement with the ground
   evaluator — the same code that replays every `sat` model — is
   definitional. An evaluator error (`abs(i128::MIN)`, `i128::MIN / -1`,
   `2^127`: outside the `i128` reference range) declines the fold and
   leaves the term unfolded; the reference range is never silently
   exceeded.
3. **A zero constant divisor is declined outright**, leaving the term for
   `eliminate_int_divmod`, which models it as a fresh congruent variable.
   Declining computes no value, so it cannot disagree with any model.
4. **`propagate_values` gains a conservative guard**
   (`depends_on_underspecified_division`): `ground_constant` declines any
   term containing an `IntDiv`/`IntMod`/`RealDiv` whose divisor does not
   evaluate to a definite non-zero constant.

## Soundness gates

- An exhaustive agreement test drives every folded binary operator over
  `[-6, 6]²` — including the zero-divisor column, which must stay
  structural — and asserts the folded constant equals the evaluator's
  value (`int_const_fold_agrees_with_ground_evaluator_including_zero_divisors`).
- Decline paths (out-of-`i128`-range, nested zero divisors) are unit
  tested, as are the `propagate_values` guard and its positive control.
- The differential fuzz that deliberately emits constant-zero divisors
  (`qf_nia_divmod_const_differential_fuzz`, per the Hard Rule) runs the
  full front door, so the fold and the guard sit inside its verdict
  differential against Z3.

## Consequences

Ground integer spellings normalize before encoding, retiring the measured
49× spelling sensitivity. The underspecified-division carve-out means a
ground `div`-by-zero term is *never* folded by rewriting; it always
reaches `eliminate_int_divmod`'s free/congruent modeling. `RealDiv` is not
folded by this rule at all (the guard in `propagate_values` covers its
zero-divisor case); extending the fold to fully specified real division is
future work and needs its own agreement tests.
