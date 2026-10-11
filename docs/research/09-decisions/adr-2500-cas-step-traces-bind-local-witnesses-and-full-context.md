# ADR-2500: CAS step traces bind local witnesses and full context

Status: accepted; bounded contract adopted, final integration gates remain open
Date: 2026-10-10

## Decision

LIB-5 begins with exact polynomial expressions over rationals, including empty
sums/products, named parameters, negation and nonnegative integer powers. Each
step preserves denotation at every rational assignment. Division and
transcendental rewrites explicitly decline until their domain obligations can be
carried and checked. This is the planned first slice, not completion of LIB-5.

A versioned JSON envelope carries complete input/result trees, rational sort,
empty-assumption context, caller limits and ordered steps. Each step carries
its index, full before/after trees, child-index path, versioned rule name,
explicit power argument where relevant, premise IDs, side conditions and the
local polynomial normal form as witness. No digest replaces an expression.
Rational coefficients serialize as canonical decimal numerator/denominator
strings. Named variables remain parameters; a parameter named pi is not π.

The producer visits original operator locations in deterministic postorder and
normalizes the subexpression at each location. It logs only actual changes.
Replay checks the original binding, continuity, IDs/premises/context, admitted
head and arguments, local arithmetic witness, unchanged surrounding expression,
and final endpoint. Replay never invokes the trace producer or heuristic CAS
equality search. It shares the existing exact polynomial arithmetic with the
producer; this is not an independent arithmetic implementation. Negative,
mutation and independent-evaluation controls compensate for that shared code.

Trace validity certifies an equality, not that a result is canonical. An empty
trace is valid only with identical source/result. A truncated trace cannot
certify a different claimed endpoint. Resource limits apply to syntax, depth,
steps, conservative polynomial expansion, work and bytes; exhaustion is
separate from invalid evidence and unsupported syntax. Reader limits are local
policy and cannot be enlarged by an untrusted envelope.

No checked trace is labeled kernel-admitted. T2 adds Python export/replay and
guarded fraction cancellation. T3 reconstructs supported steps and composes
kernel terms through Kernel::add_declaration, measuring its axiom footprint.
LIB-6 extends the coefficient carrier separately; version 1 declines promoted
coefficients in this first polynomial trace producer.

## Validation

Multi-step rational/polynomial examples; exact deterministic serialization and
standalone replay; deleted/reordered/forged steps, witness/context/endpoint and
path changes; zero versus unsupported conditional division; explicit resource
exhaustion; independent rational evaluation. A private-snapshot guard deletion
must kill exactly one targeted test before accepting the checker increment.

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
