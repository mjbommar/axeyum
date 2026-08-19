# ADR-0494: Contract-receipt authority and theorem-dependency diagnostics remain distinct

Status: accepted
Date: 2026-08-19
Index-summary: Admit the exact Int.gcd defining equation from a replayed structural contract receipt while recording, but never whitelisting, its transitive theorem closure

## Context

ADR-0493 froze `Int.gcd_def` as a one-invocation calibration control for the
source-contract-to-theorem seam. The producer had to consume the first real
trace-backed source receipt, construct exactly two binders and five nodes, and
receive zero evaluation and ledger credit.

The earlier residualization control exposed a subtlety: the defining-equation
proof has no direct theorem dependencies, but the transparent `Int.gcd`
implementation's complete declaration closure contains 52 theorem
declarations. Treating that closure as an admitted premise set would recreate
the shortcut that the structural delta receipt was designed to replace.

## Decision

Issue a distinct trace-backed semantic theorem receipt only after:

- exactly replaying the source-contract receipt;
- reconstructing the exact source equation;
- constructing the frozen `trace-contract-reflexivity-v1` proof within its
  two-binder, five-node budget;
- independently admitting the theorem with an empty axiom footprint; and
- binding the theorem identity, proof identity, operation, budget, and source
  receipt identity.

Record direct and transitive theorem dependencies as diagnostic fields. They
grant no premise authority and are never accepted as a whitelist. The source
contract's selected structural delta step is the authority for the transparent
definition.

## Evidence

The sole frozen invocation succeeded:

- producer invocations: 1; retries: 0;
- constructed binders/nodes: 2/5;
- kernel acceptance: yes;
- theorem axiom footprint: 0;
- direct theorem dependencies: 0;
- diagnostic transitive theorem dependencies: 52;
- semantic theorem receipts: 1;
- evaluation credit and ledger writes: 0/0.

Six external mutation controls and three Rust adversarial tests reject stale
source authority, receipt mutation, target reuse, absent policy, credit
promotion, and dependency-authority relabelling.

## Consequences

The contract-to-theorem mechanism seam is closed for one real Mathlib source
definition. This does not establish autonomous mathematical throughput. The
next credited work must move to a real dependency fact, beginning with a frozen
choice between the open `Int.fib_neg` and `Nat.fib_gcd` premises of
`Int.gcd_fib`.
