# ADR-0387: Fallible, transactional, namespaced Lean preludes

Status: proposed

Date: 2026-08-13

Requirements:
[`lean-kernel-requirements-2026-08-13.md`](../../plan/lean-kernel-requirements-2026-08-13.md),
R1 / TL3.3 / T6.0.8.

## Context

The logic, natural-number, integer, and real prelude builders cannot currently
share one kernel. Each arithmetic builder first rebuilds the anonymous-root
logic package, so the second builder panics on `True`. If that collision were
skipped, the real and integer packages would still collide on anonymous-root
names such as `add`, `mul`, `le`, and `zero`. The trusted kernel correctly
rejects these duplicates; the library turns the typed rejection into a panic.

This is already a product defect for mixed-theory reconstruction. It is also a
mathematical-research blocker exposed by the Rado/Ramsey work: the natural
shell indices and the signed defect sequence in `thm:rigid` must coexist in one
checked environment if the direct integer encoding is selected. A local
special-case environment would hide the same composition problem from the next
mixed mathematical development.

The builders also admit several declarations sequentially. Merely replacing
`expect` with `?` would leave a partial package after a late rejection, and
merely returning an existing name would make idempotence accept a declaration
whose type or role is wrong.

## Decision

**Make every reconstruction prelude a fallible, whole-package transaction;
share one validated logic package; namespace theory declarations under
`Nat`, `Int`, `Real`, and a deterministic parameterized string namespace; and
permit idempotent reuse only after exact package validation.**

The implementation must satisfy these rules:

1. `build_logic_prelude`, `build_nat_prelude`, `build_int_prelude`,
   `build_arith_prelude`, and `build_string_prelude` return
   `Result<Prelude, KernelError>` (or a narrower typed prelude error which
   preserves the underlying `KernelError`). Production callers propagate or
   deliberately translate the error; prelude modules never panic on a trusted
   gate rejection.
2. A package build uses one environment checkpoint. Any failure rolls back
   every declaration added by that invocation and clears environment-sensitive
   inference and WHNF caches.
3. The logic package remains the one anonymous-root bootstrap because every
   theory shares its `Eq`, connectives, `Bool`, and `Nat`. A theory builder
   ensures that exact package rather than blindly rebuilding it.
4. Natural-number library declarations remain below `Nat`. The axiomatized
   integer and real packages use distinct `Int.*` and `Real.*` names,
   respectively, including their carriers and every theorem/operation. Rust
   handle field names may remain source-compatible where their mathematical
   meaning is already clear, but rendered and ledgered declaration names may
   not alias.
5. Idempotence is exact-package idempotence. All required declarations, kinds,
   universe arities, types, values, constructor order, and recursor metadata
   must match. A missing member, extra reserved-name conflict, or mismatched
   declaration returns a typed error; presence alone is never evidence.
6. Parameterized string alphabets receive deterministic namespaces keyed by
   their declared alphabet size. Rebuilding the same size is idempotent;
   building a different size creates a distinct package without weakening the
   existing finite-alphabet proof encoding.
7. Mixed-environment tests check more than successful construction: they infer
   representative `Nat`, `Int`, and `Real` applications, prove a proposition
   containing both a natural and integer component, repeat every builder, and
   mutate or pre-populate one reserved declaration to prove fail-closed
   conflict handling and transaction rollback.
8. Declaration identities, rendered Lean, the generated axiom ledger, and
   every reconstruction consumer are regenerated or updated from the new
   names. Old counts and hashes are not patched around the change.

This ADR does not choose constructed versus axiomatized integers. The existing
integer package remains explicitly axiomatized while R2 is decided, and any
result using it retains its 34-assumption disclosure. It also does not choose
the signed-integer versus natural-deficit encoding of `thm:rigid`; composition
is required infrastructure for measuring that choice honestly.

## Evidence required for acceptance

1. An executable reproducer confirms the current collision and the completed
   regression builds logic + Nat + Int + Real in one kernel without panic.
2. Repeating each builder yields the same handles and changes neither the
   environment length nor declaration identities.
3. A mixed Nat/Int theorem is inferred and checked in that environment; both
   theory operations retain their distinct carrier types.
4. Every registered partial/conflicting package mutation returns an error and
   leaves the pre-call environment unchanged.
5. Exact-name searches find no anonymous-root integer/real operation or theorem
   declarations and no trusted-gate `expect`/panic path in prelude library code.
6. Focused kernel and reconstruction tests, warning-denied Clippy and rustdoc,
   the generated axiom ledger, parity documentation, foundational resources,
   plan authority, and links pass with nonzero test counts.
7. The Rado-facing route note records that this closes only the mixed-environment
   blocker. It does not claim `thm:sharp`, either half of `thm:rigid`, or
   `thm:main` is formalized.

## Alternatives

### Ignore duplicate declarations

Rejected. Equal names do not establish equal declaration kinds or types, and
silently aliasing `Int.add` with a real operation would recreate a
type-confusion boundary the kernel is correctly preventing.

### Keep one anonymous arithmetic namespace per kernel

Rejected. It preserves one-theory-at-a-time reconstruction and cannot support
the Rado signed-defect development or general mixed LRA/LIA evidence.

### Return `Result` without whole-package rollback

Rejected. A late error would publish a prefix which no builder can safely
identify as canonical on retry.

### Add a Rado-only combined prelude

Rejected. The defect is in shared proof infrastructure, and a theorem-specific
package would duplicate axioms while concealing the general composition gap.

## Consequences

The public builder signatures and rendered declaration names change, so every
caller and generated identity authority must move in one bounded migration.
The resulting environment supports mixed mathematical theories without
weakening declaration uniqueness, makes prelude construction a recoverable API,
and creates the correct substrate for comparing the two `thm:rigid` encodings.
