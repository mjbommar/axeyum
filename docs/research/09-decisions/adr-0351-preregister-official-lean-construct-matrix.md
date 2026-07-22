# ADR-0351: Preregister the official Lean construct matrix before widening admission

Status: proposed

Date: 2026-07-22

## Context

Axeyum independently admits exact flat, direct-recursive, projection, and Nat-
literal Lean 4.30 export fixtures. The next compatibility tasks cover recursive-
indexed, reflexive/higher-order, mutual, nested, and well-founded families, but
their exact official core forms are not yet frozen. In particular, nested and
well-founded source syntax can elaborate into core declarations whose feature
classification differs from the source label.

Implementing TL2.11--TL2.14 against guessed forms risks both wasted work and
false claims. Running the Axeyum importer first and then choosing fixtures risks
post-observation selection. Treating official source acceptance or NDJSON parse
success as independent checking would collapse distinct assurance layers.

## Decision

Preregister and execute a two-stage official construct matrix before widening
the independent kernel's recursive admission profile.

### Stage A: source freeze

Freeze minimal pinned-Lean source cases for:

- the existing direct-recursive non-indexed positive control;
- a Vector-shaped recursive-indexed family;
- an Acc-shaped reflexive/higher-order family;
- a two-family mutual tree;
- a rose-tree-shaped nested family;
- one explicit well-founded definition with a computation witness;
- one official non-positive source rejection.

Commit case IDs, selected roots, source hashes, and exact official commands
before running the product on any new stream.

### Stage B: official wire freeze

Export each positive root twice and require byte identity. Use only the
independent Python reader to freeze exact bytes, hashes, records, name/level/
expression/declaration counts, dependency roots, and inductive group metadata.
Record source family separately from observed wire features. Commit this
registration before running the Rust importer.

### Product measurement

After both freezes, run the current Rust importer without broadening it. Pair
every unsupported row with the immutable direct-recursive control. Record exact
typed parse, translation, kernel, or successful-completion outcomes. A decline
with no published environment is a valid result. Unexpected admission pauses
credit until an official/Axeyum computation and malformed-control gate passes.

### Generated assurance matrix

Generate the public Markdown matrix from one machine-readable registration.
Keep official-source acceptance, official export, independent Python inventory,
Rust parse, Rust translation, independent admission, computation, and assurance
class in distinct fields. The generator rejects impossible assurance
promotions.

### Scope and retention

This milestone advances TL1.8 and seeds TL2.16. It does not implement or
complete TL2.11--TL2.14. Commit each new stream only when it is at most 1 MiB
and the total new fixture set is at most 2 MiB; otherwise retain source,
command, counts, and hash without exact-fixture credit until TL1.9 supplies the
artifact store.

The full execution contract is
[`docs/plan/lean-official-construct-matrix-plan-2026-07-22.md`](../../plan/lean-official-construct-matrix-plan-2026-07-22.md).

## Exit gates

The ADR may be accepted only when the plan and repository state enforce:

1. a source-first and wire-second freeze before product observation;
2. byte-identical official reproduction under exact Lean/exporter pins;
3. separate source-family and wire-feature classification;
4. independent Python inventory before Rust measurement;
5. a direct-recursive positive control beside every unsupported Rust row;
6. exact typed Rust outcomes and completion-only publication;
7. fail-closed generated assurance classes;
8. hard 4 GiB, one-worker Lean, and at-most-two-job Rust limits;
9. explicit stop conditions for drift, nondeterminism, unexpected admission,
   resource failure, or retention overflow;
10. PLAN, STATUS, roadmaps, and docs index synchronization before push.

## Consequences

- The next kernel work targets measured official forms rather than source-level
  guesses.
- Negative rows become durable compatibility evidence instead of pressure to
  weaken the checker.
- Nested and well-founded source support cannot be confused with native core or
  frontend support.
- TL2.11 strict positivity remains mandatory before TL2.12 widens recursive
  admission.
- The matrix can grow toward TL2.16 without hand-maintained assurance claims.

## Alternatives

### Implement recursive-indexed support first

Rejected. The exact official group, motive, minor, and dependency shapes have
not been frozen, and positivity must precede admission widening.

### Put every source family in one broad export

Rejected. A large shared dependency closure can hide the first blocker and
prevents target-specific provenance and retention decisions.

### Freeze expected Rust errors before official export

Rejected. That would guess how source syntax lowers into core declarations.
Only source intent is frozen before export; exact wire expectations are frozen
after independent official inventory and before product measurement.

### Count official compilation as checker credit

Rejected. Official Lean is the source/export authority in this experiment, not
the independent Axeyum admission result.

### Accept the ADR immediately with the plan

Rejected. The ADR remains proposed until the source/wire freeze mechanics and
generated assurance gate are implemented and validated.
