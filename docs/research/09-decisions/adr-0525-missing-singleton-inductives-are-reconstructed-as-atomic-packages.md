# ADR-0525: Missing singleton inductives are reconstructed as atomic packages

Status: accepted
Date: 2026-08-20
Index-summary: Theorem-rooted composition may rebuild a complete non-recursive singleton inductive only through the target kernel's atomic family-constructor-recursor gate

Related: [ADR-0523](adr-0523-cross-kernel-theorem-composition-publishes-only-a-completed-clone.md),
[ADR-0524](adr-0524-translated-definitional-equality-may-authorize-a-target-recheck.md),
[ADR-0508](adr-0508-native-prelude-composition-precedes-fibonacci-coprimality-search.md).

## Context

ADR-0524 moved the first Fibonacci-support control past the structurally
different Nat.zero_le and Nat.le_trans types. The next exact decline is the
missing Exists inductive. Its source closure contains a family, constructor,
and generated recursor; copying any member independently would bypass the
kernel's positivity, parameter, recursor, and reduction contracts.

Axeyum already has the appropriate trusted target gate. Kernel::add_inductive
checks a complete singleton family transactionally and generates its recursor
from the checked family and constructor surface. The theorem-composition layer
can rebuild inputs for that gate without learning how to insert inductive
declarations itself.

## Decision

**A theorem-rooted composition may reconstruct a missing non-recursive
singleton inductive only as one complete package through
Kernel::add_inductive; every broader or partial package continues to
decline.**

The V3 contract is:

1. Roots remain checked theorems. Inductive composition is pulled only by the
   kernel-derived closure of those roots.
2. A candidate family must be missing from the target, non-recursive, and have
   exactly one motive in its source recursor.
3. Every source constructor must be missing, belong to that family, preserve
   source order and index, and carry the family's universe parameters.
4. The canonical family.rec declaration must be present in the source closure,
   missing from the target, agree on parameter/index counts, and name exactly
   the family's constructors in its checked reduction rules.
5. Any partial target collision, absent package member, mutual group, recursive
   or nested family, standalone constructor/recursor, definition, axiom,
   opaque declaration, or quotient primitive declines before the target clone
   is mutated.
6. Family and constructor names, universe parameters, and types are rebuilt
   structurally in the private target clone. Kernel::add_inductive is the sole
   admission mechanism and generates the target recursor.
7. The completed receipt binds the family, ordered constructors, recursor, and
   exact source and reconstructed-target declaration identities. The receipt
   schema advances to axeyum.checked-theorem-composition.v3.
8. Only after every demanded singleton package admits are missing theorem
   proofs rebuilt and checked. Any later failure discards the private clone and
   publishes nothing.

## Evidence

The in-tree positive control starts with a checked True family in the source
and an empty target. A theorem-rooted composition reconstructs True,
True.intro, and target-generated True.rec atomically, then independently admits
the axiom-free root theorem. Reverification reproduces both the package receipt
and completed environment.

A second real-target control adds a checked Composition.existsTrue theorem over
Exists to the native source. Against the exact Mathlib 4.30.0 r082 target, V3
reconstructs Exists, Exists.intro, and Exists.rec with source and target
identities equal, then admits the control theorem with an empty axiom footprint.
The environment transition and canonical V3 receipt are deterministic.

The unchanged Nat.eq_one_of_dvd_one control now advances through the
definitionally compatible order surface and recognizes the missing singleton
packages. Its first remaining unsupported member is Nat.mul, a definition; the
caller environment remains unchanged. This is a measured next demand, not
authority to transport definitions.

Negative controls retain axiom/opaque rejection, reject recursive Nat, reject a
non-recursive two-family mutual group, and preserve all earlier structural,
free-variable, partial-staging, and receipt-tamper checks.

## Alternatives

### Insert source inductive declarations directly

Rejected. Constructor and recursor records are consequences of one checked
package, not independent trusted inputs. Direct insertion would enlarge the TCB
and make source metadata authoritative over target reduction.

### Rebuild all inductive and mutual groups immediately

Rejected. The measured demand is the singleton Exists package. Mutual,
recursive, nested, and quotient machinery has different closure and reduction
obligations and must not inherit authority from this case.

### Model Exists as an axiom or opaque constant

Rejected. It would destroy constructor/recursor computation and enlarge every
downstream theorem's assumption footprint to avoid using an existing trusted
inductive gate.

## Consequences

The proof-library/import arrow can now bring simple logical data needed by a
native theorem into a proof-isolated target without bulk-building the native
prelude. The operation remains all-or-nothing and demand-selected.

The next bottom-up blocker is Nat.mul definition composition. Definitions carry
reduction behavior, so that extension requires an exact value contract,
height/reducibility accounting, target-gate admission, and a new decision. It
must be selected and tested independently rather than folded into V3.
