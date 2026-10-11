# ADR-6500: Wide CAS traces opt in to bounded promoted arithmetic

Status: accepted; bounded contract adopted, final integration gates remain open
Date: 2026-10-11

Polynomial trace v1 explicitly declines coefficients beyond i128. Rust Rational
already has opt-in promoting operations, while checked_add/checked_mul deliberately
demote or decline. Globally widening MultiPoly would change unrelated solver and
CAS contracts, so trace v2 uses a private, bounded polynomial evaluator with the
existing promoting Rational operations. It reuses canonical monomial ordering
and expression reconstruction, without changing bounded normalization.

Version 2 retains ordered source-bound steps, surrounding-expression binding,
local witnesses and explicit empty assumptions. Its coefficient strings must be
canonical reduced exact fractions with positive denominators. Local hard caps
bound coefficient magnitude to 16384 bits and work charges account for operand
width as well as monomial operations. Every intermediate arithmetic result is
checked against the bit cap. Input decimal text is bounded before BigInt parsing.
No coefficient passes through a float or a narrowing accessor.

The trace envelope version selects arithmetic/codec behavior. Version-1 replay
continues to reject wide coefficients and division. Version-2 parsing alone does
not certify a statement; replay binds the caller's original input and endpoint.
Both producer and checker may share this arithmetic implementation, as in v1;
private guard mutations, independent Fraction evaluation and corrupted witnesses
must establish that checking can fail. Neither version grants kernel admission.

Closed constant powers may use exponents through 512 while expanded polynomial
degree remains at most 32. This enables the exact 360-month calculation without
allowing symbolic powers to bypass expansion bounds. Constant denominators must
be proved nonzero by exact evaluation before division steps are admitted. Their
nonzero side conditions are recorded and independently checked. A zero or
symbolic denominator cannot be licensed by this unconditional v2 route; guarded
symbolic quotient certificates remain subject to ADR-6400's external context.

Milestones: bounded promoted polynomial evaluator; canonical wide expression
transport and step replay; closed rational-power/division steps; Python and
separate-process replay; independent 30-year amortization fractions; private
bit-cap/canonical/witness/domain mutation controls; broad gates. Guarded wide
quotients and automatic kernel reconstruction remain required follow-up work.

## Adoption evidence and remaining scope

The bounded contract is adopted on the feedback implementation branch. See the
[trace route inventory](../../plan/notes/cas-trace-kernel.md) and
[current validation receipts](../../plan/notes/28-wide-real-smtlib-writer.md).
Full CAS validation passes 2,154 tests with zero failures and 11 ignored;
fresh native trace suites, source-bound replay and independent exact-value
controls pass. Private checker guard controls establish targeted rejection.
This status records the architecture decision, not a main landing or completion
of broader arithmetic/kernel coverage. Final workspace/all-target integration
verification remains open; unsupported bridges remain explicit declines.
