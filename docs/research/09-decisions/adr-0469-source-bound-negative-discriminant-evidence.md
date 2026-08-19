# ADR-0469: Source-bound negative-discriminant evidence for integer quadratics

Status: accepted
Date: 2026-08-18
Index-summary: Exact source-bound negative-discriminant certificates for one-variable integer quadratic equalities

## Context

`F:no-integer-square-is-minus-one` was intentionally open even though Axeyum
returned `unsat`: the result carried `Evidence::Unsat(None)`, so a verdict-only
checker passed while the certification-aware gate correctly reported
`certified=0`. On 2026-08-18 the existing exact one-variable integer-polynomial
decider already had enough normalized structure to explain this refutation, but
discarded it when returning its verdict.

Autogenesis requires more than reaching the right answer. A registered
authoritative operation must produce evidence that a fresh checker can bind to
the exact source problem, and unsupported nearby problems must decline. The
operation registry also needs a route/evidence/footprint contract that does not
pretend an SMT certificate is an axiom-free kernel term.

This decision specializes the open evidence-envelope question in
[`research-questions.md`](../08-planning/research-questions.md) for one exercised
QF_NIA route and follows the evidence requirements in
[`foundational-dag.md`](../08-planning/foundational-dag.md).

## Decision

**Axeyum may certify an unsatisfiable integer quadratic equality when the whole
original query is exactly one assertion over one integer variable, normalization
produces `a*x^2 + b*x + c = 0` with positive `a`, bounded exact coefficients, and
the recomputed discriminant `b^2 - 4*a*c` is negative.**

The certificate carries only the normalized coefficient triple and the
discriminant. It carries no `TermId`, `SymbolId`, producer arena, model, or
solver verdict. `Evidence::check` re-collects the polynomial from the original
assertion in the checker's arena, repeats sign normalization and checked
arithmetic, requires the discriminant to be negative, and accepts only exact
equality with the carried certificate.

The public evidence label is
`unsat-int-quadratic-negative-discriminant`. The ledger route is
`smt-term-level`, with a non-empty footprint naming integer polynomial
normalization, exact integer arithmetic, and the negative-discriminant theorem.
It is not `kernel-lean`: no kernel term is produced. It is not `smt-clausal`:
the certificate does not pass through CNF or a SAT proof.

The typed Autogenesis registry may grant authoritative scope only to the exact
fact ID, formal language, fragment, and this admitted route/evidence/footprint
tuple. Registry v1 continues to reject every other tuple.

## Evidence

- The focused `nia_square` integration suite passes 28 tests, including a
  fresh-arena source mutation from `x*x = -1` to satisfiable `x*x = 1` and an
  extra-assertion mutation.
- Unit controls mutate the source assertion, assertion count, certificate
  discriminant, and certificate coefficients; each mutation rejects.
- The public SMT-LIB evidence harness reports
  `kind=unsat-int-quadratic-negative-discriminant certified=1 arena=ok` for the
  exact negated fact instance.
- The certification gate failed on purpose when its old negative control became
  certified. Its replacement `x*x = 2` remains genuinely unsatisfiable but
  reports `certified=0`, because positive-discriminant integer-root exclusion is
  outside this certificate's scope.
- The machine frontier mutation tests require exact authoritative operation
  matching before selection and reject fixture-only scope.

## Alternatives

### Treat the existing `unsat` verdict as evidence

Rejected. This is the precise defect the settled-SMT certification gate was
introduced to prevent: solver completion is not an independently checkable
refutation.

### Certify every verdict from the quadratic decider

Rejected for this increment. Positive-discriminant equalities such as
`x*x = 2` require independently checking square-root exactness and divisibility;
inequality and higher-degree branches require still different arguments. A
narrow complete checker is preferable to a broad certificate whose semantics
are inherited implicitly from the decision procedure.

### Reuse the producer's term and symbol identifiers

Rejected. Arena-local IDs can coincide accidentally after a reparse. The
checker must rediscover the source polynomial in its own arena and compare only
portable mathematical data.

### Keep the newly proved fact open as the gate's negative control

Rejected. Test calibration cannot override mathematical knowledge. A dedicated
uncertified mutation fixture separates the gate lifecycle from ledger status.

## Consequences

- One real authoritative operation can enter the machine frontier without
  broadening dispatch authority to all QF_NIA facts.
- The trusted base grows by the small polynomial collector and discriminant
  checker; the fact ledger must name that non-empty footprint.
- `x*x = 2` remains a visible next certificate gap. When it becomes certified,
  the mutation gate will fail and force an explicit control transition.
- This operation proves selection and evidence availability, but Autogenesis-1
  still requires typed transaction preparation, authoritative application,
  readiness recomputation, and a dependent A proof.
