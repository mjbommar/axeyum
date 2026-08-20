# ADR-0531: Target-owned theorem leaves cut only compatible axiom-free proofs

Status: accepted
Date: 2026-08-20
Index-summary: Theorem composition may stop at an explicit target-owned theorem only after checked type compatibility, empty footprint, source reachability, and receipt replay

Related: [ADR-0523](adr-0523-cross-kernel-theorem-composition-publishes-only-a-completed-clone.md),
[ADR-0524](adr-0524-translated-definitional-equality-may-authorize-a-target-recheck.md),
[ADR-0530](adr-0530-checked-theorem-specialization-is-named-replayable-and-axiom-free.md).

## Context

The constructive remainder invariant produced an independently checked target
`Nat.dvd_mod_iff`, but ordinary root selection for native `Nat.dvd_gcd` still
walked through the unrelated native proof behind that same-name theorem. That
proof reached native `Nat.div_mod_exec`, whose term is not admissible over the
imported Lean 4.30 division definitions.

Automatically stopping at every same-name target declaration would make target
presence an unchecked graph-cut authority. A stale theorem, a theorem of the
wrong type, an assumption-bearing theorem, or an unreachable caller-supplied
name could then hide precisely the proof dependencies composition is meant to
check.

## Decision

**Theorem-rooted composition may stop source proof traversal at an explicitly
named target-owned theorem only when the source and target declarations are
checked theorems, the target theorem has an empty kernel-derived axiom
footprint, the source theorem is reachable from the requested roots, its type
passes the existing target compatibility gate, and the exact cut replays from
a receipt.**

The V1 boundary is:

1. The caller supplies a non-empty, duplicate-free list of complete theorem
   names. Each name must resolve to a `Declaration::Theorem` in both source and
   target kernels.
2. Every target leaf must have an empty `Kernel::axiom_footprint`. A valid
   theorem that reaches an assumption declines before source closure selection.
3. A leaf changes only the dependency view of its source theorem value. The
   theorem itself and every constant in its type remain selected; proof-only
   dependencies behind the theorem are omitted.
4. Every proposed leaf must be reachable from the requested roots under that
   exact cut. Unused names decline instead of appearing in a receipt as
   fictitious work.
5. Same-name reuse still passes the existing kernel-type-shape or translated
   definitional-equality check in the target. The cut does not weaken type
   compatibility and grants no declaration transport authority.
6. All missing declarations are still admitted through ordinary target gates
   in a private clone. An admission failure publishes no partial environment
   and cannot mutate the caller.
7. The receipt uses a distinct schema and binds roots, ordered leaf names,
   selected source closure, reuse evidence, additions, both environment
   identities, and its digest. Verification reruns the target-leaf operation
   and requires the receipt and completed environment to match exactly.
8. A target leaf is proof plumbing, not a claim that the source and target
   proofs are identical. It earns no search, theorem-discovery, or fact-ledger
   credit by itself.

## Evidence

The kernel graph primitive and importer operation have controls for a precise
proof-only cut, dependency order, duplicate, missing, non-theorem, unreachable,
wrong-type, assumption-bearing, receipt-mutation, and unchanged-caller cases.
The original V5 composition and specialization output remains byte-identical.

Against the unchanged Lean 4.30 r082 target:

| Explicit leaves | Source closure | `Nat.div_mod_exec` retained | First rejection |
|---|---:|---|---|
| `Nat.dvd_mod_iff` | 66 | yes | `Nat.div_mod_exec` |
| `Nat.dvd_mod_iff`, `Nat.mod_lt` | 57 | no | `Nat.gcd_succ` |

Both attempts leave the 315-declaration caller unchanged. The second result
proves that the cut removes the division mismatch rather than suppressing its
error text: the dependency is absent from the selected source closure, and the
next independently checked admission reaches a different theorem.

The immutable evidence pack is
`/nas3/data/axeyum/autogenesis/reference-packs/5fb817301-lean430-nat-gcd-target-leaf-frontier-v1/manifest.json`,
whose SHA-256 is
`5619dcefce4aea6be55a3f66fa8d81d2a2869a654b5e5d036db3ccb848d21154`.
It also records that official `Nat.gcd_succ` and its generated recursion
equation both reach `Quot.sound`; they are reference material, not admissible
support for the axiom-free route.

The complete importer all-target suite passes, including the 336-second
official-Lean differential. Kernel export tests, warning-denied all-target
Clippy, the tracked evidence checker, and its mutation controls pass.

## Alternatives

### Stop automatically at every target theorem

Rejected. Target presence alone says nothing about type compatibility,
assumptions, reachability, or whether the caller intended to replace that proof
dependency.

### Stop at any same-type target declaration

Rejected. Definitions and axioms are not theorem evidence, and a theorem with
a non-empty footprint would silently lower assurance for the entire downstream
composition.

### Remove the leaf theorem from the closure entirely

Rejected. Its type dependencies remain necessary to validate same-name reuse
and to type-check downstream declarations. Only the proof value's dependency
edges are cut.

### Record proposed but unreachable leaves

Rejected. A receipt must describe an operation that changed selection. Accepting
an unused cut would make replayable metadata misleading.

## Consequences

Autogenesis can now reuse target-owned, axiom-free mathematical knowledge as a
checked dependency boundary without importing an unrelated source proof. This
is the graph operation required for library growth to become cumulative rather
than repeatedly reopening every old proof.

The operation deliberately exposes the next genuine foundation. For
`Nat.dvd_gcd`, that foundation is target-compatible gcd computation:
`Nat.gcd_succ` is absent from r082, the native proof does not type-check over
the imported definition, the official proof reaches `Quot.sound`, and the
successor equation is not definitional by `rfl`. The next increment must build
an axiom-free target-side gcd contract or replace the downstream proof route;
this ADR does not authorize importing the quotient footprint.
