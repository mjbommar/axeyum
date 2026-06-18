# Proof Methods

> Layer 0 · foundations · decidability: `bounded` · axeyum theory: Refutation (negate-and-decide) · status: `planned`

## What it is

The standard techniques for establishing a mathematical statement: **direct**
proof (assume the hypotheses, derive the conclusion), **contrapositive** (prove
¬Q → ¬P instead of P → Q), **contradiction** (assume ¬P, derive a falsehood),
and **case analysis**.

## Role in the tour

The methods a student must internalize to do any later mathematics — and the
place where a solver's mechanism is most directly educational, because **proof
by contradiction is exactly what a solver does**: to prove φ, it refutes ¬φ.

## Prerequisites

- [Propositional Logic](propositional-logic.md)
- [Predicate Logic](predicate-logic.md)

## Unlocks

- [Mathematical Induction](induction.md)

## Testable in axeyum

axeyum's `prove` front door *is* a proof-by-contradiction engine: it proves a
goal from hypotheses by checking that `hypotheses ∧ ¬goal` is unsatisfiable, and
hands back a re-checkable certificate. So "proof by contradiction" is not just
described but *executed and verified* on any decidable instance.

Example exercise: prove `x > 0 ⊨ x ≥ 0` over the reals — axeyum refutes
`x > 0 ∧ x < 0` (LRA, Farkas-certified) and the certificate re-checks. A
non-theorem (`x > 0 ⊨ x > 1`) yields a counter-model (e.g. `x = 1/2`),
illustrating the difference between a proof and a refutation.

## Lean-horizon

Proofs that require genuine creativity (lemma introduction, clever case splits
beyond a decidable theory) are Lean-horizon; the *checking* of such a proof is
the P3.6/P3.7 target.

## References

- Velleman, *How to Prove It*.
- axeyum: `prove` (`crates/axeyum-solver/tests/prove.rs`), evidence `recheck`.
