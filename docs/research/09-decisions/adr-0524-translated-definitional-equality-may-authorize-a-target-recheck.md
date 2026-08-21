# ADR-0524: Translated definitional equality may authorize a target recheck

Status: accepted
Date: 2026-08-20
Index-summary: Cross-kernel theorem composition may reuse a declaration after its rebuilt source type is definitionally equal in the target, but only the target admission gate accepts new proofs

Related: [ADR-0523](adr-0523-cross-kernel-theorem-composition-publishes-only-a-completed-clone.md),
[ADR-0508](adr-0508-native-prelude-composition-precedes-fibonacci-coprimality-search.md),
[kernel-type-shape census](../../autogenesis/55-kernel-type-shape-prelude-compatibility.md).

## Context

ADR-0523 conservatively allowed a same-name target declaration to be reused
only when the source and target types had identical canonical kernel-type-shape
digests. The first remaining Fibonacci-support root then declined at
`Nat.zero_le`; its native type names `Nat.le` and `Nat.zero` directly, while the
imported type retains reducible `LE.le`, `instLENat`, `OfNat.ofNat`, and
`instOfNatNat` wrappers.

That digest inequality establishes a structural spelling difference, not a
semantic type difference. The target kernel already owns the only relevant
judgment: translate the source type into the target arena, require it to infer
to a sort using target declarations, and compare it to the actual target type
by the kernel's definitional equality. Refusing to ask that question would make
presentation artifacts a permanent library-composition boundary.

## Decision

**Theorem composition V2 may authorize reuse when the translated source type is
well-typed and definitionally equal to the existing target type; this remains
permission to attempt fresh target admission, never proof or declaration
identity.**

The ordered policy is:

1. Exact canonical kernel-type-shape equality remains the cheap first class.
2. On a shape mismatch, rebuild the complete source type structurally in a
   private clone of the target arena. No source handle crosses kernels.
3. Require the rebuilt type to infer in the target and its inferred type to
   weak-head normalize to a `Sort`. An unknown constant, free variable,
   malformed application, or non-type declines.
4. Require the target kernel's ordinary definitional equality between that
   rebuilt type and the existing target declaration's type. False declines as
   the existing typed `TypeShapeMismatch`.
5. Record either `kernel-type-shape` or
   `translated-definitional-equality` on every reused-declaration receipt.
   Because this changes both policy and receipt content, the schema advances
   from `axeyum.checked-theorem-composition.v1` to V2.
6. Every missing theorem is still rebuilt and submitted to
   `Kernel::add_declaration` in the private completed-clone transaction. A
   compatibility result alone never publishes a theorem or environment.
7. Missing definitions, inductives, constructors, recursors, axioms, opaques,
   and quotient primitives retain ADR-0523's fail-closed V1 authority boundary.

## Evidence

An in-tree synthetic control gives source and target axioms of the same name
types spelled `Composition.DefeqSurface` and `True`. The former is a checked
reducible definition of the latter. Their type-shape digests differ, translated
definitional equality succeeds, and the fresh root theorem passes the target
gate. Receipt mutation from one compatibility class to the other invalidates
reverification.

On the exact Mathlib 4.30.0 `r082` stream, enabling this policy moves the
`Nat.eq_one_of_dvd_one` control past both `Nat.zero_le` and `Nat.le_trans`.
The first honest blocker becomes `UnsupportedMissingDeclaration { name:
"Exists", kind: "inductive" }`; the target environment identity remains
unchanged. The positive `Nat.add_comm` slice still admits exactly
`Nat.zero_add`, `Nat.succ_add`, and `Nat.add_comm`, each axiom-free.

Focused evidence is 11 warning-clean `axeyum-lean-import` library tests, the
real-stream probe, formatting, and all-target Clippy with warnings denied.

## Alternatives

### Keep digest equality as the permanent boundary

Rejected. It mistakes non-normalized imported wrappers for a mathematical
incompatibility even when the target kernel reduces both types to the same
term. That blocks checked proof reuse for presentation reasons.

### Normalize rendered source text before hashing

Rejected. Pretty-printing is not the trusted reduction relation, and choosing a
normal form outside the kernel duplicates semantics while still requiring a
target-arena translation.

### Treat definitional equality as declaration identity

Rejected. Definitions with different bodies can expose definitionally equal
types. Exact declaration digests remain distinct and are retained in the
receipt; only fresh target proof checking can authorize additions.

## Consequences

The first measured order-theorem mismatch is no longer the next representation
project. The demand signal moves downward to atomic transport of the missing
singleton `Exists` inductive package. That extension changes reduction and
recursor surface and therefore requires its own decision and controls; this ADR
does not authorize it.

Each composition now pays for one private compatibility clone and target
inference only when a shape mismatch is reached. Receipts make that cost class
observable. Representative full-library scaling remains unmeasured.
