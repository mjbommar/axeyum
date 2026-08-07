# Supported Logics

Axeyum support is layered and route-specific. A logic name alone cannot answer
whether its syntax parses, terms evaluate, the pure-Rust dispatcher decides a
shape, SAT models replay, or UNSAT has independent evidence.

## Use the right authority

| Question | Authority |
|---|---|
| What proof/model capability exists, with assurance? | [Generated capability matrix](../research/08-planning/capability-matrix.md) |
| Which parser/IR/evaluator/oracle/pure-Rust/evidence layers exist? | [Generated support matrix](../research/08-planning/support-matrix.md) |
| What remains trusted in a result? | [Generated trust ledger](../research/08-planning/trust-ledger.md) |
| How well is a fragment measured on retained corpora? | [Benchmark results](../../bench-results/README.md) and [`PLAN.md`](../../PLAN.md) |
| Which SMT-LIB commands execute? | [SMT-LIB support](smtlib-support.md) |

## Current broad shape

The default build is the scalar QF_BV foundation: typed Bool/BV terms lower to
AIG/CNF and pure-Rust SAT, with source-model replay and selected independently
checked UNSAT routes.

The `full` pure-Rust profile adds broad, uneven support across:

- arrays and uninterpreted functions;
- linear and nonlinear integer/real arithmetic;
- finite/bounded strings, sequences, regular expressions, and word equations;
- floating-point front doors and bit-vector reductions;
- datatypes, quantifiers, and theory combinations;
- optimization, interpolation, transition systems, and verification helpers.

This list is a map, not a completeness claim. Many routes accept only bounded or
recognized shapes and safely return `unknown` outside them. Proof coverage is
also narrower than decision coverage.

## Declared logic versus dispatch

The SMT-LIB parser records `(set-logic ...)`, but current solver dispatch is
derived from the parsed terms rather than selected or rejected solely by the
declared logic. A successful parse under a logic name therefore does not prove
the whole standard logic is supported.

Use retained corpus and differential evidence for scope claims. Do not infer
support from one example or an enum variant.

## Answer taxonomy

- `sat` means a returned model/witness passed the route's source-level replay.
- `unsat` means the route produced a definitive refutation; assurance varies by
  evidence chain.
- `unknown` is expected for unsupported-by-procedure shapes, incomplete search,
  or resource bounds.
- `SolverError::Unsupported` means the selected backend cannot represent the
  input at its boundary.

For user-facing limitations and examples, see the
[Limitations guide](../user-guide/limitations.md).

