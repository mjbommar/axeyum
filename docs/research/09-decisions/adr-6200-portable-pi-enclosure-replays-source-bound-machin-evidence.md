# ADR-6200: portable pi enclosure replays source-bound Machin evidence

Status: accepted; bounded surface adopted, final integration gates remain open
Date: 2026-10-11

## Decision

Expose a bounded PiEnclosureCertificate and Python enclose_pi / PiEnclosure.
Version1 JSON carries canonical expression-wire source bytes for distinguished
Pi, precision, Machin order, exact remainder and exact lower/upper endpoints.
All rational components are reduced canonical decimal strings. This is a
single-node Pi certificate: head Pi, no operand intervals, no root signs. These
fixed distinctions are part of the version1 format, not omitted arbitrary fields.

Replay requires the caller's original subject and verifies both its distinguished
Pi identity and the carried source binding. Reconstruct the existing Enclosure
and Step(Pi), then call Enclosure::verify with empty bindings. Replay never calls
the enclosure producer or uses approximate pi. Report examined/discharged steps,
acceptance and failure reason. Parsing alone does not confer acceptance, and
exposed bounds remain claims until replay. Producer self-checks before returning.

Hard caps: 64 KiB wire bytes, precision256 bits, order128, 16384 bits per rational
component. Bound decimal lengths before bignum parsing. Unknown/duplicate fields,
noncanonical components, reversed endpoints and unsupported versions reject.
Resource refusals remain distinct from rejected evidence. Wrong source,
insufficient order, overstated precision, understated remainder and invalid
endpoints reject. Conservative relaxations can remain valid: the existing
verifier permits a larger remainder or a wider containing interval within the
precision budget. Replay checks mathematical evidence, not a hash of a producer
receipt; do not reject a still-valid certificate merely because bytes changed.

This first transport implements the pi-specific byte-replay requirement. General
expression/binding/root enclosure transport, checked fixed-value inequalities,
transcendence and kernel reconstruction remain separate required work. No
kernel admission or universal enclosure-coverage claim follows from this format.

## Validation

Rust and fresh Python round-trip exact bytes and bounds. Replay in a separate
process, change each certificate distinction, and substitute Var(pi) as the
original subject. Compare exact rational endpoints with 3 and 22/7 and assert
width at most 2^-precision. Remove only the source-binding guard in a private
snapshot and require exactly one targeted test to fail. Run broad CAS/workspace
gates against immutable source and retain terminal results separately.

## Adoption and validation boundary

This bounded surface is adopted on the feedback implementation branch. Current
CAS library tests and the fresh native consumer suites cover exact values,
transport, parser/domain controls and explicit unsupported/resource outcomes;
see the [validation receipts](../../plan/notes/28-wide-real-smtlib-writer.md).
Signed-power fuzzing includes guaranteed zero-base negative-exponent and
undefined-base seed classes. Private Pi/source-binding controls remain recorded
with exact intended failures. Production Python parsing uses ADR-6900; ADR-3100
is historical and superseded. Promoted transport does not widen every arithmetic
operation, and Pi bounds or parsed expressions do not grant kernel admission.
The final workspace/all-target gates and main integration remain open.
