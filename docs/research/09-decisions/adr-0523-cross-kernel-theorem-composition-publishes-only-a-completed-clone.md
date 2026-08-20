# ADR-0523: Cross-kernel theorem composition publishes only a completed clone

Status: accepted
Date: 2026-08-20
Index-summary: Cross-kernel theorem composition is theorem-only, identity-gated, independently rechecked, and publishes only a completed cloned environment

Related: [ADR-0348](adr-0348-owned-lean-import-publication.md),
[ADR-0387](adr-0387-fallible-composable-lean-preludes.md),
[ADR-0484](adr-0484-proof-free-type-slices-are-generalized-and-exactly-specialized.md),
[ADR-0508](adr-0508-native-prelude-composition-precedes-fibonacci-coprimality-search.md).

## Context

ADR-0508 requires identity-aware transactional composition before Fibonacci
coprimality search. The first real control now admits `Nat.zero_add`,
`Nat.succ_add`, and `Nat.add_comm` from Axeyum's native axiom-free library into
the checked Mathlib `r082` environment. It does so in a measurement example,
where its cross-kernel expression translator and compatibility policy are not a
reusable contract.

Promoting that code without a decision would silently answer several trust
questions. A name collision could mean exact identity, compatible type but a
different implementation, or a genuinely different proposition. Missing
closure members could be definitions, inductives, axioms, opaques, or checked
theorems. A failed admission after two successful additions could expose a
partial environment. Arena-relative names, levels, and expressions cannot be
copied as raw handles.

ADR-0348 already establishes the publication rule for imports: incomplete
environments do not cross the API. ADR-0387 establishes exact validation and
whole-package transactions for native preludes. ADR-0484 identifies canonical
cross-kernel cloning as a required implementation boundary. This decision
applies those rules to the narrower theorem-slice case measured here.

## Decision

**V1 cross-kernel composition lives in `axeyum-lean-import`, accepts a checked
source kernel, a checked target kernel, and explicit theorem roots, and returns
an owned completed environment only after the entire selected slice passes
compatibility checks, translation, and independent kernel admission.**

The contract is:

1. The source root closure is derived by the kernel in deterministic dependency
   order. Roots must exist and be theorems. An empty root set or a request that
   would add no declaration declines.
2. A closure declaration whose name already exists in the target is reused
   only when its binder-name-, binder-info-, and universe-spelling-insensitive
   kernel type-shape identity agrees. Exact receipt identity is recorded
   separately and is never redefined by this compatibility relation.
3. Compatibility authorizes only an admission attempt. It does not assert that
   two declarations have the same value or behavior. Every translated proof is
   checked against the actual reused target declarations by
   `Kernel::add_declaration`; only that trusted-gate result authorizes the new
   theorem.
4. A missing closure member is admitted only when it is a checked
   `Declaration::Theorem`. V1 declines missing definitions, inductives,
   constructors, recursors, axioms, opaques, and quotient primitives. It never
   manufactures an assumption to make a proof typecheck.
5. Names, universe levels, and expressions are rebuilt structurally in the
   target arena. Constant names are mapped by their complete structural names,
   not by source handles. Bound variables retain de Bruijn indices. Closed
   declaration translation rejects free variables. Every supported expression
   form has a deterministic translation; unknown future forms decline until the
   contract is extended.
6. The target is borrowed immutably and cloned only after root selection and
   compatibility validation. All translations and admissions occur in that
   private clone. Success returns a completed owned result; failure returns no
   kernel or arena-relative handle, leaving the caller's target unchanged.
7. The completed result binds the source roots and closure, target environment
   identity before composition, reused declaration identities, added theorem
   identities and axiom footprints, target environment identity afterward, and
   the compatibility/translation schema versions. Reverification recomputes
   these fields rather than trusting serialized counts.
8. V1 is deterministic and resource-bounded. The clone cost is accepted for
   the currently measured small imported environments and slices, but must be
   measured before representative full-library use. A later kernel-owned
   transaction may replace cloning only with equivalent no-partial-publication
   controls and a new decision.
9. Composition grants neither proof-search credit nor ledger credit. It records
   how a proof was obtained (`native-library` in the first route), and ordinary
   theorem receipt and fact admission remain separate operations.

## Evidence

The immutable observation
`/nas3/data/axeyum/autogenesis/probes/9caac0bf5-nat-add-comm-composition-v5/observation.json`
uses the exact Mathlib 4.30.0 `r082` stream. Eight imported dependencies pass
the compatibility gate. Three translated native theorem proofs then pass the
ordinary independent kernel gate, and all three have empty kernel-derived axiom
footprints.

The negative control selects `Nat.eq_one_of_dvd_one`. Its derived closure
reaches the structurally different imported `Nat.zero_le`; composition declines
before admission, and the caller environment digest is identical before and
after. The positive transition changes the environment digest and binds exact
receipts for all three additions.

Acceptance of this ADR does not claim the public API is implemented. The
implementation gate requires committed in-tree controls for:

- successful deterministic theorem-only composition and repeat behavior;
- exact-identity and type-shape-compatible reuse;
- structural type mismatch;
- missing non-theorem, axiom, opaque, inductive, and quotient dependencies;
- free-variable rejection and all supported expression forms;
- trusted-gate failure after at least one successful staged admission;
- unchanged caller state on every failure;
- tampered root, closure, receipt, provenance, and environment identities; and
- nonzero warning-denied tests, Clippy, rustdoc, plan, ADR-index, and link gates.

## Alternatives

### Treat matching names as the same declaration

Rejected. The `r082` census contains exact matches, metadata-only type matches,
and eight structural mismatches under the same names. Presence alone erases the
distinction the kernel depends on.

### Require exact declaration-content identity for every reused dependency

Rejected for this route. It would reject all three measured proofs even though
the independent target kernel accepts them against the imported definitions.
Exact identity remains receipt authority; conservative type compatibility plus
fresh trusted-gate checking is the stronger test of whether a new proof is
valid in the actual target environment.

### Mutate the caller and roll back on failure

Rejected for V1. It expands the kernel's public mutation/rollback surface and
makes every future arena, interner, cache, or environment field part of the
rollback proof. Private-clone publication inherits ADR-0348's simpler ownership
boundary.

### Copy raw arena handles or serialize through rendered Lean

Rejected. Handles belong to one kernel, while pretty-printed source would add a
parser/elaborator and presentation choices to an otherwise structural bridge.

### Compose definitions and inductives immediately

Rejected. Their reduction behavior, constructor order, recursor rules,
projections, and atomic-group admission require contracts beyond theorem proof
translation. Actual closure declines should order those extensions.

## Consequences

The first reusable API is intentionally narrower than the probe's general
appearance. It can grow the bottom-up theorem layer over imported environments
without replacing Mathlib declarations or adding assumptions, but cannot yet
bridge the six Fibonacci-support lemmas whose closures reach structurally
different order, literal, modulus, or recursor representations.

Clone memory is paid once per attempted V1 composition. That is acceptable for
the current 261-declaration environment and must remain visible in receipts and
benchmarks; it is not evidence of full-Mathlib scalability.

The immediate implementation sequence is: extract structural translation and
completed-result types into `axeyum-lean-import`; register the negative matrix;
reproduce the three-theorem `r082` result through the API; then choose the first
representation bridge from measured closure demand rather than broadening the
translator speculatively.
