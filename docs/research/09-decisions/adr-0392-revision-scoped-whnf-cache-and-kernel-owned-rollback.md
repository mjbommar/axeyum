# ADR-0392: Revision-scoped WHNF cache and kernel-owned rollback

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R1 / R6.3.

## Context

Prelude transactions introduced a fourth rollback site. Each site had to call
the environment's unchecked suffix removal and then remember to clear both
environment-sensitive kernel caches. Omitting either invalidation can reuse a
judgment from a declaration environment that no longer exists.

The WHNF cache also keyed entries by `(expression, environment length)`. A
successful admission permanently increases the environment length, while a
rollback clears the cache. Consequently, an entry from an older revision can
never hit again, but remained allocated for the kernel's lifetime. Large
single-kernel exports could therefore retain cumulative dead WHNF entries.

Finally, duplicate prelude registration was protected only by a debug
assertion after map insertion, and a host integer-conversion failure in the
string prelude was misclassified as a conflict naming `True`.

## Decision

Only `Environment` may perform unchecked suffix removal. Every transactional
kernel path calls one `Kernel::rollback`, which removes the suffix and clears
both environment-sensitive caches.

Store WHNF results as `(revision, entries)`. Before lookup, a revision mismatch
sets the current revision and clears the entry map. This preserves every
possible cache hit while bounding retained entries to one live revision.

Duplicate prelude registration is a release-build assertion checked before
map insertion, so even a caught panic cannot replace the integrity snapshot.
String alphabet-key conversion has its own typed overflow error.

## Evidence

The kernel regression suite proves that:

- the first WHNF lookup after admission discards a distinct prior-revision
  entry and retains the current-revision entry;
- the sole kernel rollback removes the declaration suffix and clears both
  caches;
- duplicate registration panics and leaves the original exact snapshot
  queryable.

The cache bound follows analytically from monotonic admission plus mandatory
clearing on the only path by which an environment length can recur.

## Alternatives

Keeping revision in every hash key was rejected because it has identical hit
behavior and cumulative dead storage. A size-based eviction policy was
rejected because it would spend policy and bookkeeping on entries already
proved unreachable.

Lazy prelude snapshots and structural hashes are deferred. Exact declaration
snapshots are the current conflict detector; changing their representation
needs a measured reconstruction workload and an equivalence argument that
covers rollback followed by same-name reinsertion. Hash-only equality would
also add collision assumptions to an integrity mechanism. This performance
question does not block the cache and rollback repair.

## Consequences

Adding a future rollback path cannot compile outside the environment module by
calling unchecked removal, and cache invalidation is attached to the only
kernel rollback operation. WHNF memory is proportional to the current
revision's live cache rather than cumulative admissions. Bulk prelude
admission still has little cross-declaration WHNF reuse; that is required by
the possibility that a new recursor enables additional reduction.
