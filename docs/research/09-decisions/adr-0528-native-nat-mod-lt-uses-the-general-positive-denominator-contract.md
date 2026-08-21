# ADR-0528: Native Nat.mod_lt uses the general positive-denominator contract

Status: accepted
Date: 2026-08-20
Index-summary: Native Nat.mod_lt states the general positive-denominator theorem, while named cross-kernel compatibility remains read-only attempt authority

Related: [ADR-0524](adr-0524-translated-definitional-equality-may-authorize-a-target-recheck.md),
[ADR-0527](adr-0527-native-bool-follows-official-lean-constructor-order.md),
[ADR-0508](adr-0508-native-prelude-composition-precedes-fibonacci-coprimality-search.md).

## Context

After native Bool adopted official Lean constructor order, the unchanged
Mathlib r082 `Nat.dvd_gcd` composition control stopped at `Nat.mod_lt`.
Mathlib's theorem is general:

```text
forall x y, 0 < y -> x % y < y
```

The native theorem instead quantified a predecessor and dividend and exposed
only the successor-denominator instance. A one-off adapter could have derived
that instance from the imported theorem, but it would preserve an avoidable
same-name API mismatch and add a theorem-transport policy to the composition
boundary.

## Decision

**Native `Nat.mod_lt` uses the general positive-denominator contract. Its proof
is independently admitted by the native kernel, and cross-kernel compatibility
may be inspected by a read-only named-declaration diagnostic that grants no
publication authority.**

The contract is:

1. `Nat.mod_lt : forall x y, 0 < y -> Nat.mod x y < y`. The proof inducts on
   `y`: the zero branch eliminates the impossible positivity witness, and the
   successor branch projects the checked remainder bound from `Nat.div_mod_exec`.
2. Native GCD and Bezout consumers supply `0 < succ k` explicitly from
   `Nat.zero_le` and `Nat.le_succ_succ`. The old predecessor-first application
   shape is rejected by a focused mutation.
3. `checked_reused_declaration_compatibility` applies the exact same
   kernel-shape/translated-definitional-equality policy used by theorem
   composition to one same-name declaration. It mutates neither kernel and
   returns only a `ReusedDeclarationReceipt`.
4. A successful compatibility receipt is permission to attempt ordinary
   target reconstruction, not proof, admission, or composition credit. Missing
   target names and real type mismatches fail closed.
5. End-to-end authority remains with `compose_checked_theorem_slice`: the
   unchanged root must advance, and its failed transaction must leave the
   target environment byte-identical.

## Evidence

The kernel implementation is commit `a5a111498`; the compatibility diagnostic
and probe are commit `ac33a0a2d`. The generalized theorem is a checked theorem
with an empty axiom footprint. Its exact rendered native type is pinned, a
concrete `6 % 4 < 4` application infers, and the old argument order is rejected.
All 393 pre-existing kernel library tests passed in 3,556.11 seconds; the new
contract/mutation test passed separately. The first merged checkpoint also
passed the authoritative pre-push workspace, corpus, full solver, kernel, and
golden-module battery in 499 seconds.

The immutable Mathlib 4.30.0 r082 observation is:

`/nas3/data/axeyum/autogenesis/probes/ac33a0a2d-nat-mod-lt-compatibility-v13/observation.json`

Its SHA-256 is
`29fc6b096e28e7f99b8005e86673259b3b1e3686778af6b0e452d4f31be079c1`.
Two independent executions were byte-identical; the directory and observation
are mode `0555` and `0444`.

The coarse census deliberately still classifies `Nat.mod_lt` as a type-shape
mismatch because Mathlib's statement contains its `LT`, `OfNat`, `HMod`, and
instance wrappers. The named compatibility check translates those wrappers in
the target and records `translated-definitional-equality`, binding distinct
source/target declaration digests and distinct type-shape digests. No kernel
submission occurs during that diagnostic.

Most importantly, the unchanged `Nat.dvd_gcd` control passes `Nat.mod_lt` and
now declines at:

```text
UnsupportedMissingDeclaration { name: "Acc", kind: "recursive-inductive" }
```

The target environment digest remains
`798b19a16b1e6937d4fc9eb6f0c2f5f58c5544d5ea58641c7aa04119dc6b0982`
before and after. Existing definition, singleton-inductive, and theorem
composition receipts are unchanged, and authority remains 15 kernel
submissions, zero proof-search invocations, and zero ledger writes.

## Alternatives

### Add a theorem-specific successor-denominator adapter

Rejected. It would solve the immediate call site while retaining a weaker
native public theorem under the same official name. The general theorem is
provable from the existing checked division relation and benefits every native
consumer.

### Treat wrapper-level type-shape mismatch as incompatibility

Rejected. ADR-0524 already permits translated definitional equality to
authorize a fresh target check. The named diagnostic exposes that existing
policy; it does not weaken it or publish a declaration.

### Count successful compatibility as theorem composition

Rejected. Compatibility checks only types. They do not reconstruct a proof,
admit a theorem, or produce a completed environment and therefore receive no
kernel or ledger credit.

## Consequences

Native arithmetic now exposes the same useful general `Nat.mod_lt` contract as
Lean, and successor-specific GCD/Bezout uses remain explicit derived instances.
The composition path crosses the wrapper representation seam without a
transport exception.

The next measured blocker is the complete recursive `Acc` package. Supporting
it requires an atomic target-kernel reconstruction contract for a recursive
inductive, its constructor, and generated recursor, with exact source/target
identities and rollback controls. This decision grants no such authority; it
only makes that real boundary visible.
