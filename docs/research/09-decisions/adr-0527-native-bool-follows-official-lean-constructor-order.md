# ADR-0527: Native Bool follows official Lean constructor order

Status: accepted
Date: 2026-08-20
Index-summary: Native Bool uses Lean's false-then-true constructor order, and every branch-sensitive native proof or reconstruction site must migrate atomically

Related: [ADR-0523](adr-0523-cross-kernel-theorem-composition-publishes-only-a-completed-clone.md),
[ADR-0526](adr-0526-missing-definitions-are-rebuilt-and-checked-in-dependency-order.md),
[ADR-0508](adr-0508-native-prelude-composition-precedes-fibonacci-coprimality-search.md).

## Context

The checked-definition increment moved the unchanged Mathlib `r082`
`Nat.dvd_gcd` control to `Bool.rec`. The imported Lean 4.30.0 package declares
constructors as `Bool.false`, then `Bool.true`, so its generated recursor takes
the false minor before the true minor. Axeyum's native package used the reverse
order. Both kernels were internally coherent, but the declarations could not
share one checked environment.

Bool is foundational. Its recursor is used not only in the prelude but in Nat,
Int, and String proofs and in solver-side Lean reconstruction. Changing the
inductive declaration without changing every semantic minor application would
silently invert branches while still producing well-typed terms.

## Decision

**The native Bool inductive uses official Lean's constructor order
`[Bool.false, Bool.true]`, and the migration includes every branch-sensitive
recursor application in one gate-proven change.**

The contract is:

1. `build_logic_prelude` declares `Bool.false` before `Bool.true`; the generated
   `Bool.rec` therefore receives the false minor before the true minor.
2. Native kernel proofs and solver reconstruction must express their semantic
   false and true branches in that order. Call-site source order is not trusted
   as evidence; behavior and independent replay are tested.
3. Official-order module fixtures and golden bodies are regenerated from the
   corrected reconstruction path. Existing mutation controls must still be
   rejected by official Lean.
4. The change grants no generic recursor-permutation, declaration-grafting, or
   theorem-transport authority. Composition still reuses only declarations
   admitted by its existing identity and target-kernel rules.
5. The exact native prelude source digest, implementation tree, immutable r082
   observation, and four-member Bool overlap package are bound by the
   Autogenesis manifest checker.

## Evidence

The implementation is the tree at
`772646c0d1a0c6ebca302c37a42cf2bb2f5030ee`, composed from focused commits
`502184d3f`, `012c6b4f6`, and `866add778`. The first full pre-push run exposed
18 reconstruction failures in lexicographic, regex, word, datatype, and
quantified-proof paths; correcting those sites made the full 1,248-test solver
sweep pass. A later run exposed one stale 111,821-byte equality-partition
golden digest; repinning its unchanged-size official-order body completed the
gate. The authoritative pre-push battery then passed in 734 seconds.

Independent validation also passed the complete ignored official-Lean
differential in 286.33 seconds, replayed 15 committed Lean modules with a
mutation rejection, and read 139 Nat theorems plus 57 derived and zero asserted
Int theorems from the kernel. The logic, Nat, Int, and String trusted surfaces
remain empty.

The exact axiom-free Mathlib 4.30.0 r082 observation is read-only at
`/nas3/data/axeyum/autogenesis/probes/772646c0d-official-bool-order-v11/observation.json`
with SHA-256
`2f65c2c86e883269f60f96ba3e396f82ba044d1d99959a89bc47e2ada839c264`.
Imported declaration and theorem counts remain 261 and 52; native declarations
remain 198. Exact overlaps increase from 7 to 11, alpha-compatible mismatches
fall from 18 to 15, shape-compatible mismatches remain 10, and unresolved type
overlaps fall from 8 to 7. `Bool`, `Bool.false`, `Bool.rec`, and `Bool.true` are
all exact.

The unchanged `Nat.eq_one_of_dvd_one` control still composes exact `Nat.mul`,
exact `Nat.dvd`, the `Exists` package, and eight axiom-free theorems with receipt
`9ac9ace96e64d1bd9cd8131ebe1f2f7404cc93b4ed9d962ae55ffe51ef200cd0`.
The larger `Nat.dvd_gcd` control now declines at `Nat.mod_lt`; its environment
digest is identical before and after, so the new result remains fail-closed.

## Alternatives

### Permute Bool recursor branches during imported theorem composition

Rejected. A generic expression rewrite would need motive-aware proof that it
preserves every dependent recursor use and would create a new transport policy
outside ordinary kernel admission. Aligning the native foundational package
removes the representation difference instead.

### Keep the native order and rename the constructors

Rejected. Constructor names are already public declaration identities, and
renaming would not make the generated recursor identical to official Lean.

### Change only the native inductive declaration

Rejected. The failed full solver sweep demonstrated that well-typed recursor
applications can retain the wrong branch semantics. The blast radius has to be
migrated and tested atomically.

## Consequences

The Bool package is now an exact reusable part of the imported/native boundary,
and every current native consumer retains its intended branch behavior. The
next measured blocker is not another constructor-order workaround: imported
`Nat.mod_lt` proves the general positive-denominator theorem, while the native
library exposes the successor-denominator specialization. The next increment
must derive the native statement through an explicit checked specialization or
adapter and must not authorize arbitrary mismatched-theorem transport.
