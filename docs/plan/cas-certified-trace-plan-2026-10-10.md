# Certified CAS traces and exact expression surface — 2026-10-10

Specification for LIB-5 and LIB-6. The [audit](user-feedback-audit-2026-10-10.md)
records current source and diagnostic evidence; [PLAN.md](../../PLAN.md) owns
scheduling. All milestones below are proposed, unimplemented work.

## Constraints and reuse

Read the [foundational DAG](../research/08-planning/foundational-dag.md) and
[ADR-0601](../research/09-decisions/adr-0601-three-producers-one-trust-anchor.md),
[ADR-0602](../research/09-decisions/adr-0602-operations-are-receipts-dispatch-needs-producer-contracts.md),
[ADR-0603](../research/09-decisions/adr-0603-classical-theorems-land-as-graded-statement-families.md)
before selecting a public format. Search existing certified operations and CAS
bridges first (`just brief <specific-target>` before an implementation brief).
CAS trace checking is evidence validation; library admission still goes through
`Kernel::add_declaration`. A valid trace is not automatically an admitted theorem.

Reuse `CasExpr`, assumptions, polynomial/rational normalization, big zero-test
witnesses and existing kernel bridges. Keep prospective producer capabilities
separate from retrospective receipts; no `proved` field in a producer contract.
Decide the trace envelope, arithmetic carrier and constant/domain semantics in
ADRs before introducing public types. Allocate ADR numbers explicitly at that time.

## LIB-5: CAS becomes a trace producer

### T0 — identify the first useful certified path

Inventory the normalization and algebra/calculus paths used by consumers.
Choose exact rational arithmetic and polynomial equality first. Pin at least
one multi-step input/output example and a currently unsupported conditional
rewrite. Distinguish identity, implication under assumptions, and domain
restriction; these cannot share an unchecked equality tag.

**Exit:** route table names producer, verifier, current certificate, assumptions,
and eventual kernel reconstruction. Every proposed first-slice rule has a
mechanical checking recipe; unsupported steps are explicit declines.

### T1 — stable trace contract and independent replay

Proposed per-step content: ordered step ID; typed before/after expressions;
subexpression location; versioned rule ID; exact rule arguments; premise IDs;
side-condition statements and evidence; witness; assumption-context identity.
The whole trace binds original input, claimed result, rule-set version, expression
encoding, resource limits, and ordered steps. If digests are used, carry or
resolve the full expressions; a digest alone cannot be checked.

The checker rebuilds the step relation from the rule contract and witness,
checks the rewritten location and surrounding expression, and requires each
output to feed the next input. It verifies the original-to-final claim, domain
and assumptions. Producer-only simplification and heuristic search never count
as checking. Rational arithmetic can be recomputed locally; polynomial expansion
can use a carried normal form; whole-result normalization remains a separate
check. Define precisely whether replay reuses arithmetic code and how independent
controls compensate; do not advertise implementation independence without it.

Return checked, rejected, unsupported, or resource-limited outcomes explicitly.
A partial trace carries no full-result certification. Stable order, bounded
parsing, and deterministic serialization are mandatory.

**Exit:** serialized trace checks without invoking the search producer; deleting,
reordering or corrupting a step, witness, context or endpoint fails; no missing
certificate is treated as success. Mutation work runs in a snapshot, and removing
one checker guard must kill exactly one targeted test.

### T2 — expose a narrow producer and Python replay

Add an opt-in trace-producing normalization path; retain the ordinary fast path.
Expose trace serialization and replay, plus the failing step/reason, in Python.
Demonstrate rational simplification, polynomial expansion, and guarded fraction
cancellation. `(x*x)/x -> x` requires `x != 0`; test zero as a negative case.
Require distinct results for a false claim and a budget-exhausted check.

**Exit:** fresh Rust and Python runs produce the same deterministic trace; an
external process replays exported bytes; user examples explain the certificate
and its domain. Compare bounded small workloads for size/runtime with tracing
off/on, without promoting performance anecdotes into a parity claim.

### T3 — compose with the trust anchor

Reconstruct each supported step into existing kernel lemmas and compose them.
Record a receipt only after admission. Measure the resulting declaration's
`Kernel::axiom_footprint`, not a source label or rule name. Integrate the producer
with LIB-1 discovery only after that boundary is demonstrated.

**Exit:** at least one automatically generated multi-step identity becomes an
admitted declaration with empty footprint; a changed assumption or side condition
is rejected by the kernel route. Report checked-trace and kernel-admitted counts
separately. Do not raise a certified-function inventory merely for adding logging.

## LIB-6: exact inputs and useful expression syntax

### X0 — public arbitrary-precision rationals

The Rust `Rational` carrier already has small/promoted arbitrary-precision
representations; reuse it rather than introducing a replacement carrier.
Inventory input, result, serialization, Python `Fraction` conversion and
coefficient containers for route-specific width limits. In particular, narrow
`numerator()`/`denominator()` access panics on promoted values; conversion and
checking paths need checked access or the existing big accessors.
Avoid a repository-wide arithmetic rewrite as the first delivery: choose the
exact rational expression path and operations needed by amortization.

Use a pinned independent Python `Fraction` calculation for
`P*r / (1 - (1+r)^(-360))`, for example `P=300000`, monthly `r=1/240`.
Handle `r=0` separately as `P/360`. Retain the user's original example if supplied;
this chosen case is a replacement regression, not a claimed reproduction of it.
No float intermediates, narrowing, or silent rounding. Limits must bound
coefficient bits, term count and work; exhaustion is an explicit decline.

**Exit:** inputs/results beyond `i128` round-trip exactly through Rust, Python
and certificate serialization; bounded cases preserve behavior; 360-period
payments agree with independently constructed fractions. Rechecking and kernel
bridges either handle the wider carrier or explicitly decline. Existing
`CertifiedBig` certificates continue to check.

### X1 — negative integer powers with explicit domains

First slice can lower `x^(-n)` to `1/(x^n)` using current quotient semantics.
Specify `0^(-n)`, `0^0`, symbolic nonzero assumptions, and signed-exponent limits
before changing Python `pow`. Do not silently equate a partial rational function
with a total SMT operation. Test zero denominators and avoid minimum-signed-value
negation overflow. Record cancellation side conditions in T1 traces.

**Exit:** negative powers compute and certify for nonzero inputs; zero and missing
assumptions produce the documented outcome; existing nonnegative powers survive.
Symbolic and fractional exponents remain separately scoped future work.

### X2 — symbolic π and bounded text parsing

Add a distinguished symbolic π constant with a stable encoding; a variable named
`pi` is not the constant. Reuse `enclose_constant` and its checkable bounds.
Define normalization behavior without claiming complete transcendental equality.

Specify an exact expression grammar: identifiers, integer/rational literals,
parentheses, arithmetic operators, integer powers, π and the existing unary
heads. Decide precedence for `-x^2`, division associativity, exponent syntax,
reserved names and Unicode aliases. Parse decimals exactly if admitted; never
coerce them through `f64`. Implement source-span diagnostics and depth/node/bit
limits. Human `__str__` and canonical serialization may differ; choose and test
which representation round-trips. No host-language `eval`.

**Exit:** constructor-built and parsed expressions agree; malformed, oversized
and ambiguous forms are rejected predictably; π enclosure bytes recheck and
corrupted endpoints fail. Parser and traces preserve assumptions and domains.

## Required validation when implemented

Run workspace library tests and the affected CAS/arith/kernel tests using
`scripts/cargo-serialized.sh`; verify nonzero counts. Run relevant Python CAS
and certificate suites against a fresh extension. Keep the CAS trust-registry
floor and fact/evidence validation intact. If a solver bridge changes, run the
full-feature solver library suite and the applicable front-door/differential
gates from AGENTS.md. These tests are planned obligations, not results of this
research-only change.
