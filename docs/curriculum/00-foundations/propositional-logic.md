# Propositional Logic

> Layer 0 · foundations · decidability: `decidable` · axeyum theory: Bool / SAT · status: `covered`

## What it is

The logic of statements that are true or false, combined with connectives —
*not* (¬), *and* (∧), *or* (∨), *implies* (→), *iff* (↔). A formula is **valid**
(a tautology) if it is true under every assignment of truth values, **satisfiable**
if true under some assignment, and **unsatisfiable** if true under none.

## Role in the tour

The root of the whole tour: every proof is, at bottom, a manipulation of
propositions. It is also the one node that is *completely* automatable — the
decision problem (SAT) is decidable — which makes it the natural place to teach
what "valid", "satisfiable", and "proof" even mean before quantifiers arrive.

## Prerequisites

None — a root of the tour.

## Unlocks

- [Predicate Logic](predicate-logic.md)
- [Proof Methods](proof-methods.md)

## Testable in axeyum

Fully decidable, and already covered by the `Family::Logic` self-checking
scenarios. A tautology is checked by asserting its **negation** and confirming
unsatisfiability over the (finite) truth table; a satisfiable formula carries a
witness assignment. Examples that self-check today:

- Modus ponens `((p → q) ∧ p) → q` — negation unsatisfiable (all 4 rows).
- Law of excluded middle `p ∨ ¬p`; the contradiction `p ∧ ¬p`.
- Boolean De Morgan `¬(p ∧ q) ↔ (¬p ∨ ¬q)`.

Under the hood this is exactly axeyum's Bool/SAT path; a proof can additionally
be emitted and re-checked (DRAT/Alethe), making the *why* exhibitable.

## Lean-horizon

None — propositional logic is fully within reach.

## References

- Enderton, *A Mathematical Introduction to Logic* (ch. 1).
- axeyum: `axeyum-scenarios::logic`, `axeyum-cnf` (Tseitin, DRAT, `check_alethe`).
