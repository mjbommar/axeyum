# Lean kernel transaction and cache hardening result

Date: 2026-08-13

Status: **implemented locally; publication and hosted CI recorded separately**

Authority: [requirements](lean-kernel-requirements-2026-08-13.md), R1 / R6.3;
[ADR-0392](../research/09-decisions/adr-0392-revision-scoped-whnf-cache-and-kernel-owned-rollback.md).

## Result

The declaration environment's unchecked rollback is private. Prelude,
inductive, nested-inductive, and quotient transactions now converge on one
kernel rollback boundary that removes the environment suffix and invalidates
the closed-inference and WHNF caches together.

WHNF storage retains only the current declaration revision. On the first
lookup after admission it clears the unreachable previous generation, keeping
the same hit set with memory bounded by the live revision instead of all
admission revisions.

Duplicate package registration now asserts in release builds before insertion,
and a regression catches the panic and confirms the original exact snapshot
survives. An unrepresentable string alphabet size reports the typed
`StringAlphabetSizeOverflow` cause rather than a false conflict naming `True`.

The kernel library run passes 210 tests, including new cache-generation,
rollback-invalidation, and duplicate-registration controls. All kernel
integration suites and doctests, strict all-target/all-feature Clippy, strict
rustdoc, the 65-row axiom ledger and eight ledger controls, foundational
resources, plan authority, links, owned-file formatting, and diff integrity
also pass.

The workspace-wide parity-doc and formatting gates are temporarily non-green
because a concurrent search lane added a 36th example without yet updating its
inventory markers and is editing unformatted search sources. Those paths are
outside this increment and are neither staged nor counted as kernel failures.

## Deferred measurement

`declarations_since` still clones the exact package snapshot on first build.
Current reconstruction routes commonly create one kernel per query, so repeat
package-cache hits may be rare and the clone may be avoidable allocation. It
is not changed in this repair: a lazy or compact representation must preserve
exact conflict detection across rollback and same-name reinsertion, and should
be selected only after measuring representative Rado/reconstruction kernels.

## Boundary

This repairs integrity and unreachable-cache retention. It does not claim
better bulk-admission hit rate, measured end-to-end memory reduction, or any
new Rado theorem. ADR-0391's geometric finite-sum reindexing dependency remains
the next mathematical action.
