# ADR-0493: Calibration closes the contract-to-theorem seam before evaluation

Status: accepted
Date: 2026-08-19
Index-summary: Preregister Int.gcd_def as a zero-evaluation calibration control for consuming the first real source-contract receipt before attempting the Int.gcd_fib dependency chain

## Context

ADR-0492 produced a real trace-backed source-contract receipt for `Int.gcd`.
The next missing arrow is not another source analysis; it is consuming that
receipt to issue a theorem receipt without restoring the rejected
theorem-closure shortcut.

Seven evaluation-eligible train statements mention `Int.gcd`. The reviewed
dependency catalog makes one of them structurally different:
`Int.gcd_fib` explicitly depends on `Int.fib_neg` and `Nat.fib_gcd`. Both facts
remain open in the Axeyum ledger. Attempting `Int.gcd_fib` now would mix the new
contract seam with two unresolved mathematical premises and would not identify
which arrow failed.

The reviewed nursery separately retains `Int.gcd_def` as calibration-only. Its
statement is exactly the source contract already received. It can isolate the
receipt-consumption seam, but it must not be relabelled as evaluation yield.

## Decision

Preregister one deterministic `Int.gcd_def` bridge control before execution:

- input: the exact trace-backed `Int.gcd` source-contract receipt;
- grammar: introduce exactly two pointwise arguments, then construct
  `Eq.refl`;
- budget: at most two binders, five constructed nodes, one invocation, and zero
  retries;
- acceptance: replay the source receipt, independently check the constructed
  theorem, require an empty axiom footprint, and issue one semantic theorem
  receipt;
- credit: mechanism control only, with zero evaluation and ledger credit.

The policy checker binds the exact reviewed-candidate identity and disposition,
the exact source-contract receipt, and the two open direct premises of the real
`Int.gcd_fib` horizon target. Historical diagnostic producer outcomes are not
policy inputs. Held-out outcomes and upstream proof bodies remain forbidden.

## Evidence before execution

- `Int.gcd_def` is reviewed `calibration-only` with candidate identity
  `744a8bc1...`.
- The source-contract receipt replays with identity `ae758575...`.
- `Int.gcd_fib` is reviewed `evaluation-eligible` and is the only reviewed
  `Int.gcd` consumer whose catalog records an explicit two-premise chain.
- `Int.fib_neg` and `Nat.fib_gcd` both remain epistemically `open`.
- Six mutation controls reject evaluation credit, budget widening, self-reported
  execution, hidden horizon premises, and held-out authority.

## Consequences

No producer has run under this decision. The next increment may execute exactly
the frozen bridge once. Success will validate the contract-to-theorem seam but
will not establish evaluation throughput. The real compounding target remains
`Int.gcd_fib`, gated by independent receipts for both named premises.
