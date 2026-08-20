# ADR-0530: Checked theorem specialization is named, replayable, and axiom-free

Status: accepted
Date: 2026-08-20
Index-summary: Generic checked theorems may be specialized only by named checked declarations in a private clone with an empty footprint and replayable receipt

Related: [ADR-0348](adr-0348-owned-lean-import-publication.md),
[ADR-0484](adr-0484-proof-free-type-slices-are-generalized-and-exactly-specialized.md),
[ADR-0523](adr-0523-cross-kernel-theorem-composition-publishes-only-a-completed-clone.md).

## Context

The first constructive replacement for Lean's assumption-bearing
`Nat.dvd_mod_iff` is deliberately generic. Its proof accepts a divisibility
predicate plus checked addition, subtraction, and commutativity theorems, then
proves the successor-divisor remainder invariant over the official `Nat.mod`
implementation. Cross-kernel composition can independently admit that generic
proof, but applying it to the target's arithmetic declarations is a separate
trusted-boundary event.

Leaving this application inside one example would make the decisive step
unreplayable. Treating ordinary type inference as the whole contract would
also omit the source identity, ordered arguments, caller-state boundary,
resulting footprint, and environment transition needed by Autogenesis.

## Decision

**A checked theorem may be specialized only by applying an ordered list of
named declarations already present in the same checked kernel, admitting the
result as a fresh theorem in a private clone, requiring an empty kernel-derived
axiom footprint, and issuing a receipt that reproduces exactly.**

The V1 contract is:

1. The source handle must name an admitted `Declaration::Theorem`. Every
   argument handle must name an existing declaration in that same input
   kernel. The target name may be interned, but it must not already name a
   declaration.
2. V1 applies universe-monomorphic constant references in caller order. It
   does not accept arbitrary expressions, hidden local hypotheses, synthesized
   instances, or producer-provided types.
3. The input kernel is borrowed immutably. Application, inference, and theorem
   admission run only in a private clone. Any missing declaration, argument
   mismatch, non-proposition result, existing target, or kernel rejection
   returns no completed environment and cannot mutate the caller.
4. `Kernel::infer` derives the specialized proposition from the application;
   the caller cannot supply a more convenient target type. The ordinary
   `Kernel::add_declaration` theorem gate independently checks the proof.
5. Success additionally requires `Kernel::axiom_footprint` of the new theorem
   to be empty. An application that type-checks only because an argument or its
   dependencies reach an axiom declines rather than publishing a lower-assurance
   theorem under the same operation name.
6. The receipt binds the source theorem name and declaration identity, every
   ordered argument name and identity, target name and admitted identity,
   footprint, environment identities before and after, schema, and its own
   canonical digest.
7. Verification re-executes specialization from the unchanged input and
   requires both the receipt and completed environment identity to match. A
   serialized receipt is evidence only after this replay succeeds.
8. Specialization is proof plumbing, not proof search or ledger admission. It
   earns neither theorem-discovery credit nor fact credit by itself.

## Evidence

The authored Lean 4.30 module
`scripts/lean/autogenesis_nat_mod_invariant.lean` exports 211 declarations and
no axioms. Axeyum independently derives empty footprints for
`modCoreGo_invariant`, `modSucc_invariant`, and `modSucc_dvd_iff`.

After composing the generic root and the target's checked `Nat.dvd`,
`Nat.dvd_add_iff_right`, `Nat.sub_add_cancel`, and `Nat.add_comm`, the V1
operation admits `Nat.dvd_mod_iff` with an empty footprint. Its kernel type-shape
identity is
`82789b0e69792f3d2308a32b4c6f108fef63bbded868e066fed2422a1b49019e`,
exactly the native theorem's type shape. The specialization receipt digest is
`f03cd55d79467478528e24cdc347e6f9945a3eb1c49064e075176068451e358d`.

Unit controls reject a wrong-typed named argument and an existing target while
leaving the caller unchanged; receipt mutation fails replay. The complete
importer suite, warning-denied all-target Clippy, real-Lean differential tests,
and the exact r082 execution pass.

The immutable proof/export/result pack is
`/nas3/data/axeyum/autogenesis/reference-packs/667201932-lean430-nat-mod-invariant-v1/manifest.json`,
whose SHA-256 is
`ba31490c95fbd9b08005fcc0517fe6c09645d63c216005be0a795be85a15ef0e`.

## Alternatives

### Specialize only inside the r082 example

Rejected. The most consequential admission would have no reusable contract,
no negative matrix, and no independent replay API.

### Accept arbitrary expression arguments

Rejected for V1. Expression provenance and identity would require a broader
receipt, free-variable policy, and cross-arena transport contract. The measured
case needs only named checked declarations.

### Permit assumption-bearing specializations and report the footprint

Rejected for this operation. A lower-assurance route may be designed under a
different explicit policy, but silently widening V1 would erase the property
that licenses bottom-up axiom-free library growth.

### Trust the inferred type without a new theorem admission

Rejected. Inference establishes the application's type; it does not create the
durable named declaration or rerun the theorem admission boundary that later
composition and dependency accounting consume.

## Consequences

Autogenesis now has a reusable checked operation for turning a generic proof
program into a concrete target theorem without trusting the proof producer or
growing the axiom base. The operation is intentionally limited to named,
universe-monomorphic declaration arguments.

The next blocker is no longer construction of `Nat.dvd_mod_iff`. The current
root-closure algorithm still traverses the native proof hidden behind an
already compatible target theorem, which unnecessarily reintroduces native
`Nat.div_mod_exec`. The next decision must define an explicit target-theorem
leaf/cut contract before `Nat.dvd_gcd` is retried.
