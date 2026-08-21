# ADR-0532: Mixed definition and inductive composition follows source dependency order

Status: accepted
Date: 2026-08-20
Index-summary: Checked composition admits definitions and atomic singleton packages in one source-derived dependency order before admitting their consumers

Related: [ADR-0523](adr-0523-cross-kernel-theorem-composition-publishes-only-a-completed-clone.md),
[ADR-0525](adr-0525-missing-singleton-inductives-are-reconstructed-as-atomic-packages.md),
[ADR-0526](adr-0526-missing-definitions-are-rebuilt-and-checked-in-dependency-order.md),
[ADR-0531](adr-0531-target-owned-theorem-leaves-cut-only-compatible-axiom-free-proofs.md).

## Context

The imported-to-official gcd route reached an assumption-bearing
`Nat.gcd_succ`. The complementary route starts with Axeyum's axiom-free native
Nat and gcd library, then composes the exact imported `Nat.fib` definition into
that kernel.

The first unchanged r082 attempt declined at `HAdd` with an unknown constant.
The source closure was already dependency ordered: the missing definition
`outParam` preceded the atomic `HAdd` package whose family type referenced it.
Composition nevertheless reconstructed every singleton package before every
definition. That phase ordering contradicted the graph order promised by
ADR-0526 and manufactured a missing dependency that did not exist in the
source closure.

## Decision

**Checked theorem composition admits every missing declaration in the single
dependency order returned by the checked source closure. An atomic singleton
package occupies its family position in that order and is reconstructed there
as one target-kernel operation.**

The boundary is:

1. Validation still runs before staging and classifies every complete
   singleton package. Unsupported axioms, opaques, partial packages, recursive
   lookalikes, and mutual families decline before publication.
2. Admission walks the selected missing declarations exactly once. A
   definition or theorem is submitted when encountered. A singleton family
   reconstructs its complete family, constructor, and recursor package at the
   family's position; later package-member rows are skipped because the atomic
   operation already created them.
3. One expression translator and one private target clone span the mixed walk,
   so every earlier independently admitted name is available to later
   definitions and packages without source-arena handles crossing the boundary.
4. Package atomicity, exact reconstruction requirements, ordinary target
   kernel checking, completed-clone publication, receipt contents, and replay
   remain unchanged.
5. Dependency order grants no new declaration kinds or semantic compatibility.
   It fixes scheduling only.

## Evidence

A synthetic regression defines `Composition.BaseProp`, uses it as the sort of
a singleton `Composition.Wrapped`, and proves a theorem with the constructor.
The old package-first schedule rejects the family before the definition exists;
the mixed dependency walk admits the definition, reconstructs the package,
admits the theorem, replays the receipt, and leaves the caller empty.

The real Lean 4.30 probes then close both required directions:

- r082 composes the exact imported `Nat.fib` definition into a 198-declaration
  native Nat kernel. The 46-declaration closure reuses eight declarations and
  adds 19 definitions plus six atomic singleton packages. Receipt
  `208b7e8703b3de9e89319d2ba9716a917940ccaeb3f4a7af4527d1e2d6f790ee`
  replays with no caller mutation.
- r080 reconstructs the already admitted `Nat.fib_add_two` candidate, then
  composes its 46-declaration proof closure into the same native kernel. It
  adds exactly one theorem with empty axiom footprint and no direct theorem
  dependencies. Receipt
  `f7244fbc69e6ceec6ed2511e46786bccd2d5a4e4485f3e6de70743104f888168`
  replays.
- r080 and r082 give `Nat.fib` the identical declaration digest
  `15f76f9318e04cf653cd094524473919b14a333c308cee32d6d428136bdc522c`.

The immutable reference-pack manifest is
`/nas3/data/axeyum/autogenesis/reference-packs/91d7df736-lean430-native-fib-composition-v1/manifest.json`,
with SHA-256
`b797f5876ca3d033a5e58424573a774e3cad1af6dc9723059555a779d3028877`.
The complete importer all-target suite passes, including the 395-second
official-Lean differential; warning-denied importer Clippy and focused
composition controls pass.

## Alternatives

### Add `outParam` or `HAdd` directly to the native prelude

Rejected. The source closure already supplies the checked dependency. Expanding
the permanent native prelude would conceal the scheduler defect and repeat it
at the next package whose type depends on a missing definition.

### Keep packages first and make multiple retry passes

Rejected. Retry-until-progress is a second dependency algorithm with ambiguous
failure reporting. The kernel-derived closure already provides the required
deterministic order.

### Reimplement a different native Fibonacci definition

Rejected for this seam. The target fact names Lean's `Nat.fib`; composing its
exact checked definition preserves the imported statement's semantics and
avoids an additional equivalence theorem.

## Consequences

The selected Fibonacci-coprimality route no longer needs to move Axeyum's gcd
proofs into the official imported environment. It moves the exact Fibonacci
definition and its already established recurrence into the axiom-free native
environment, where `Nat.dvd_gcd`, `Nat.gcd_dvd_left`,
`Nat.gcd_dvd_right`, and the remaining planned lemmas already coexist.

The next task is mathematical rather than representational: construct the
bounded induction for `gcd (fib n) (fib (n + 1)) = 1` in that completed native
kernel, independently check its footprint, and only then prepare a fact-ledger
transition. This ADR establishes no theorem and grants no ledger credit.
