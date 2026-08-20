# ADR-0526: Missing definitions are rebuilt and checked in dependency order

Status: accepted
Date: 2026-08-20
Index-summary: Theorem-rooted composition may rebuild demanded definitions with exact type, value, universe parameters, and reducibility only through ordinary target-kernel admission

Related: [ADR-0523](adr-0523-cross-kernel-theorem-composition-publishes-only-a-completed-clone.md),
[ADR-0524](adr-0524-translated-definitional-equality-may-authorize-a-target-recheck.md),
[ADR-0525](adr-0525-missing-singleton-inductives-are-reconstructed-as-atomic-packages.md),
[ADR-0508](adr-0508-native-prelude-composition-precedes-fibonacci-coprimality-search.md).

## Context

ADR-0525 moved the first Fibonacci-support control through the missing `Exists`
package. Its next exact decline was `Nat.mul`, a definition. Definitions are not
proofs: their values participate in reduction, and their reducibility hints
change when the kernel may unfold them. Treating a same-name definition as a
theorem, an axiom, or an unchecked copied environment entry would silently
change the target's computation relation.

The source kernel already checked each definition when it built the native Nat
library. That does not authorize publication in another kernel. The target must
receive a structurally rebuilt declaration and independently type-check it with
the dependencies that were actually admitted or reused there.

## Decision

**Theorem-rooted composition V4 may rebuild demanded `Definition`
declarations in source-closure dependency order, but only ordinary target
`Kernel::add_declaration` admission can publish them.**

The contract is:

1. Definitions enter only when reached by the kernel-derived closure of an
   explicit theorem root. A caller cannot use this API to nominate a definition
   as a root or bulk-copy an environment.
2. The complete definition name, ordered universe parameters, type, value, and
   `ReducibilityHint` are rebuilt structurally in the private target clone. No
   source `NameId`, `LevelId`, or `ExprId` crosses the kernel boundary.
3. Definitions and theorems are submitted in the dependency order returned by
   the checked root-closure operation, after any complete singleton inductive
   packages required by the slice have been reconstructed.
4. `Kernel::add_declaration` performs the ordinary target inference and
   definitional-equality checks. A rejection at any definition or later theorem
   discards the private clone and publishes no prefix.
5. A same-name target declaration is never overwritten. It remains a reuse
   candidate under ADR-0523/0524 and must pass the existing type compatibility
   policy before any new declaration is attempted.
6. Each added-definition receipt binds its rendered name, exact source
   declaration digest, exact independently admitted target digest, and stable
   reducibility spelling. The enclosing receipt schema advances to
   `axeyum.checked-theorem-composition.v4`.
7. Axioms, opaque declarations, quotient primitives, recursive or mutual
   inductive packages, partial packages, and incompatible reused declarations
   remain outside this authority boundary.

## Evidence

The synthetic control adds a regular-height definition whose value is `True`,
then a theorem whose type unfolds that definition. Composition admits the
definition and theorem into a fresh target, records equal source/target
definition identities and `regular:1`, derives an empty theorem axiom
footprint, and reproduces the complete environment and receipt. Existing
late-failure, free-variable, axiom, opaque, recursive-inductive, structural
mismatch, and receipt-tamper controls remain fail-closed.

On the exact axiom-free Mathlib 4.30.0 `r082` stream, commit `acade2a45`
composes the unchanged `Nat.eq_one_of_dvd_one` root. The target independently
admits exact `Nat.mul` (`regular:2`) and `Nat.dvd` (`regular:4`) definitions,
the exact `Exists` singleton package, and eight theorems. All eight theorem
axiom footprints are empty; both definition source identities equal their
target identities. The deterministic V4 receipt is
`9ac9ace96e64d1bd9cd8131ebe1f2f7404cc93b4ed9d962ae55ffe51ef200cd0`.

The next unchanged larger control, `Nat.dvd_gcd`, now declines before staging
at the imported/native `Bool.rec` type mismatch. The imported recursor orders
the `false` branch before `true`; the native package orders those branch
premises oppositely. The negative control's environment digest is identical
before and after, so this result grants no recursor-permutation authority.

Focused evidence is 13 warning-clean importer library tests, the complete
`axeyum-lean-import` suite including the 275-second official-Lean differential,
all-target Clippy with warnings denied, formatting, the exact r082 replay, and
the manifest checker's definition-identity, reducibility, compatibility-count,
authority, and receipt mutation controls.

## Alternatives

### Copy a checked source definition directly into the target environment

Rejected. Source checking proves a fact about source handles and dependencies;
it does not establish a target-arena declaration or preserve transactional
publication.

### Replace definitions with axioms or opaque declarations

Rejected. Downstream proofs depend on reduction of `Nat.mul` and the
existential body of `Nat.dvd`. Hiding those values would expand the trusted base
and change theorem computation.

### Normalize every definition before admission

Rejected. The original value and reducibility are part of the declaration's
identity and behavior. Pre-normalization creates a second, unnecessary
translation policy outside the target kernel.

### Generalize immediately to every declaration kind

Rejected. Recursive/mutual inductives, generated recursors, quotient packages,
axioms, and opaques have distinct atomicity and trust obligations. This
decision follows the exact measured definition demand only.

## Consequences

The library/import arrow can now carry computational helpers as well as simple
logical data and checked theorems. One demanded root closes a 35-declaration
source slice with two new definitions and eight axiom-free theorems rather than
stopping at its first reducible operation.

The next bottom-up task is not broader definition transport. It is the measured
`Bool.rec` representation seam: determine whether the native Bool package
should adopt official Lean constructor order or whether a narrowly checked
recursor-aware theorem reconstruction can rebuild the proof against the target
order. No branch permutation, declaration graft, or bulk prelude replacement
is authorized by V4. Representative full-library scaling remains unmeasured.
