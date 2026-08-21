# ADR-0533: Official gcd unfolding uses pointwise fuel congruence, not function extensionality

Status: accepted
Date: 2026-08-20
Index-summary: A target-specific pointwise proof replaces quotient-bearing generic well-founded recursion congruence for official Nat.gcd unfolding

Related: [ADR-0495](adr-0495-fibonacci-gcd-progress-starts-at-the-iterator-recurrence-foothold.md),
[ADR-0530](adr-0530-checked-theorem-specialization-is-named-replayable-and-axiom-free.md),
[ADR-0531](adr-0531-target-owned-theorem-leaves-cut-only-compatible-axiom-free-proofs.md).

## Context

The constructive imported-to-official Fibonacci route advanced to
`Nat.gcd_succ`. Lean 4.30's official theorem and generated well-founded
equation both reach `Quot.sound`. The generic
`WellFounded.Nat.fix.go_congr` theorem proves equality between complete
recursive functions with `funext`, so importing it would enlarge the trusted
footprint even though Euclid's algorithm needs equality only at one concrete
pair of arguments.

The native Fibonacci theorem cannot simply replace the official theorem.
Official `Nat.Coprime` closes over the imported `Nat.gcd` definition, while the
native theorem closes over Axeyum's separately constructed gcd. Compatible
names and types authorize a target check, not unchecked semantic transport.

## Decision

**Official `Nat.gcd` unfolding is reconstructed with a target-specific,
pointwise induction over the two recursion fuels. It may compare only the
recursive call reached by the concrete Euclidean step and may not use generic
function extensionality, `Quot.sound`, or same-name definition substitution.**

The proof is authored outside the trusted base and exported normally. Its
successor-modulo decrease is an explicit theorem parameter. Checked
specialization first supplies the already established axiom-free target
`Nat.mod_lt`, then specializes the gcd computation theorem to the public target
name `Nat.gcd_succ`. Both specializations and the final native compatibility
check are replayable receipts.

The resulting theorem is eligible as a target-owned leaf only after its
kernel-derived footprint is empty and the ordinary target kernel accepts its
proof. It grants no authority to transport arbitrary well-founded definitions.

## Evidence

Pinned Lean 4.30 reports no axioms for the authored successor-mod bound,
pointwise fuel congruence, gcd model equation, or final gcd successor theorem.
The independent Rust importer reports empty footprints for both exported
roots. Two complete runs produce identical result bytes.

The final specialization establishes:

```text
Nat.gcd (Nat.succ m) n = Nat.gcd (n % Nat.succ m) (Nat.succ m)
```

Its declaration identity is
`e41996f98e01e15b88e11773bb42db825bf271888ece2d002c193627a8392727`,
its footprint is empty, and its type is definitionally compatible with the
native theorem. With `Nat.dvd_mod_iff`, `Nat.mod_lt`, and the new
`Nat.gcd_succ` as explicit target leaves, the 57-declaration native
`Nat.dvd_gcd` slice now composes and replays with receipt
`5be80180f535cce7a42d9ac9b87f2e7fe716479a3aaf3f2108fdc00fe40a3261`.

The immutable evidence manifest is
`/nas3/data/axeyum/autogenesis/reference-packs/f94489c74-lean430-nat-gcd-succ-bridge-v1/manifest.json`,
with SHA-256
`7190676a198599fd7d4f14bb5cb0a83f2a8d9806be7d5803e3de920cf8e77637`.

## Alternatives

### Import official `Nat.gcd_succ`

Rejected. Its kernel footprint reaches `Quot.sound`; convenience does not
justify expanding the trusted base.

### Use generic `WellFounded.Nat.fix.go_congr`

Rejected. It proves equality of recursive functions with `funext`, which is
strictly stronger than the pointwise fact required by Euclid's algorithm.

### Credit the native Fibonacci theorem directly

Rejected. It proves a theorem over a separately constructed gcd definition.
Type compatibility alone is not a semantic bridge.

## Consequences

The assumption-bearing gcd frontier is closed without changing kernel
semantics or the target-leaf policy. `Nat.dvd_gcd` becomes available in the
official r082 environment through ordinary checked composition.

Six other planned gcd/divisibility support theorems and the exact official
Fibonacci-coprimality theorem remain to be reconstructed. No fact status,
semantic theorem receipt, evaluation credit, or ledger row changes in this
increment.
