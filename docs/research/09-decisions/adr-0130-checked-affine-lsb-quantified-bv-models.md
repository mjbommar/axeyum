# ADR-0130: Checked affine-LSB quantified-BV models

Status: accepted
Date: 2026-07-12

## Context

After ADR-0129, `smtcomp-qbv-053118` is the smallest unsupported row in the
public cvc5 quantified-BV slice. It has one free `BV32` symbol `x` and two
assertions. At `x = 0`, the first assertion is universally valid because it
equates an even expression with an odd expression under a negation. The second
assertion is a negated universal; `m = 1, n = 0` makes its inner disequality
false. Thus a complete source model needs both a universal parity proof and a
complete existential counterexample, not merely a value for `x`.

cvc5's CEGQI-BV implementation uses current model values, rewrites literals,
and sends candidate paths through its BV inverter. Its source explicitly calls
candidate selection heuristic and limits multiple instantiations to control
exponential growth. Z3's model checker asserts the negated model-interpreted
quantifier in a fresh context and extracts counterexample bindings. Those are
useful search designs, but neither candidate trace is Axeyum evidence.

## Decision

**Carry a complete free-BV interpretation for each quantified assertion and
accept it only when a separate checker proves the untouched source through an
exact affine-LSB invariant or evaluator-replays a complete counterexample to a
directly negated universal.**

`QuantifiedBvModelSatCertificate` records the exact assertion, strictly ordered
values for every free symbol in that assertion, and one of two proof forms:

1. `AffineLsbUniversal` peels a nonempty direct `forall+` prefix and evaluates
   its quantifier-free Boolean body in a small three-valued checker. BV
   equalities can be proved false only when both least-significant bits reduce
   to affine GF(2) forms with identical variable coefficients and opposite
   constants. The exact interpreter supports constants, symbols, negation,
   add/sub/xor, bitwise-not, low-preserving extension/extraction/concatenation,
   and multiplication only when one LSB operand is constant. A nonlinear
   symbolic product declines.
2. `NegatedUniversalWitness` requires exact source shape `not (forall+ body)`,
   exact binder order, and one typed value for every binder. The checker combines
   those values with the complete free model and requires the untouched
   quantifier-free body to evaluate to `false`.

Both forms require only Bool/BV source terms, no function applications, unique
binders, exact free-symbol coverage, and hard limits of 128 binders, 4,096
complete source DAG nodes, and depth 256. Canonical `check_model` independently
checks certificate/model agreement, rejects stale or extra certificates, and
replays every original assertion.

Untrusted search enumerates every low-bit assignment for at most eight free BV
symbols, under a 4,096-total-free-bit limit and one shared deadline. This is
complete for the affine-LSB proof class. For a directly negated universal it
asks the ordinary QF_BV solver for a counterexample under the fixed free model,
then discards the solver verdict unless the source checker accepts the complete
returned tuple. Unsupported witness subqueries decline rather than changing the
front-door error surface.

The fourth quantified certificate family exposed unnecessary `Model` growth.
All quantified certificate vectors now live in one lazily allocated boxed
aggregate, so future proof families do not enlarge every ordinary model or
`CheckResult`.

## Evidence

`smtcomp-qbv-053118` moves from unsupported to checked SAT. Five release corpus
samples report target solve times 0.285816, 0.195489, 0.213322, 0.192103, and
0.190069 ms (median 0.195489 ms). Separate evidence-production samples are
3.339, 3.287, 3.293, 2.437, and 3.036 ms (median 3.287 ms).

The 54-row public cvc5 quantified-BV slice is now 33 SAT / 17 UNSAT / 0 unknown
/ 4 unsupported, with 50 expected-status agreements and no disagreement,
error, or replay failure. Five PAR-2 samples are 1.624330, 1.623963, 1.623953,
1.624041, and 1.623998 seconds (median 1.623998 seconds). Exactly the target
changes outcome.

The dominance audit certifies and checks all 50 decisions, marks 41/50 dominant
candidates, and retains Lean coverage at 8/17 UNSAT. The target evidence kind is
`quantified-bv-model-sat`, its evidence rechecks, and its trust ledger is empty.

Five focused tests cover the public model and evidence, free-value/witness/
source/certificate tampering, nonlinear and polarity near misses, binder/node/
depth limits, and 64 generated direct-Z3 comparisons: 32 certified affine-LSB
SAT models plus 32 UNSAT controls. Cumulative quantified-BV direct-Z3 coverage
is 1,784 cases and controls with no disagreement. Existing Skolem, free-Boolean,
guard, paired-existential, and eight prior quantified-BV differential suites
remain green after the model-layout refactor.

## Alternatives

- **Trust the free assignment returned by quantifier erasure or MBQI.** Rejected:
  a value for `x` does not prove either quantified source assertion.
- **Bit-blast the complete universal domain.** Rejected: a 32-bit five-binder
  domain is not an evidence format. The LSB invariant is a complete small proof
  for this theorem.
- **Normalize the formula to integer parity.** Rejected: no arithmetic bridge is
  needed. The checker interprets the exact modular LSB semantics of source BV
  operators.
- **Accept arbitrary multiplication in the affine interpreter.** Rejected:
  multiplying two symbolic parity forms is nonlinear over GF(2). Such terms
  decline unless one operand's LSB is constant.
- **Use a solver UNSAT result to validate the universal.** Deferred: a
  source-bound QF_BV proof of a fresh universal counterexample query could be a
  broader future proof form, but is unnecessary for this exact invariant.
- **Store another independent certificate slice directly in `Model`.** Rejected:
  it increases every model and triggered strict large-error lint regressions.

## Consequences

Axeyum can now return a replay-checked free-BV model when direct universal
validity follows from affine low-bit semantics and directly negated universals
have complete evaluator-replayed witnesses. This is not general BV MBQI,
nonlinear polynomial reasoning, nested alternation, function/array models,
proof serialization, or Lean SAT reconstruction. The next measured unsupported
row is `intersection-example-onelane` at 70 DAG nodes; it requires a separate
checked contract for a negated existential implication with many free BV facts
and signed division, not an expansion of ADR-0130 by assumption.
