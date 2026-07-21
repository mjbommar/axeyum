# ADR-0331: Preregister Tock cache hard-link inventory

Status: proposed
Date: 2026-07-21

## Context

ADR-0330 preparation v3 proves the resolver correction and completes the exact
locked fetch, then stops because ADR-0329 rejects all hard links. Cargo/libgit
legitimately hard-links one firmware pack index between the dedicated Git
database and checkout. No cache survives, and the remainder of the inventory is
unobserved.

Rejecting every inode alias is stricter than input authentication requires. The
inventory must preserve the alias relationship rather than copy, dereference,
or ignore it.

## Decision

Create preparation v4 with output
`target/tock-log2-20260721/cache-v4`. Reuse ADR-0330's source, resolver, DNS,
fetch, offline probe, resource, no-compilation, and atomicity gates exactly.
Replace only regular-file inventory with deterministic in-root inode groups:
one lexicographic owner row plus explicit hard-link alias rows.

## Frozen v4 gates

1. Commit and push this zero-result ADR before adding v4. Commit and push the
   separate v4 producer/tests/registration before its DNS probe or fetch. V3 is
   never rerun.
2. Reuse the complete compact ADR-0330 registration by exact file hash. The v4
   overlay may change only schema, output version, producer identities, and
   inventory schema/version. No resolver, DNS, command, source, tool,
   environment, namespace, package-count, resource, or phase-order field may
   change.
3. Enumerate the complete `cargo-home/` without following symlinks. Group every
   regular file by `(st_dev, st_ino)` only during local enumeration; device and
   inode numbers never enter canonical output.
4. Sort each group's relative POSIX paths bytewise. The first path is the
   canonical owner and receives a `file` row binding path, mode, size, SHA-256,
   and `links` equal to the group's path count. Each later path receives a
   `hardlink` row binding its own path, canonical owner path, the same mode,
   size, SHA-256, and `links` value.
5. Require every member's mode, size, content hash, and `st_nlink` to match the
   group. Require `st_nlink == group path count`; this rejects any hard link
   whose other path lies outside the dedicated cache. Require owner paths to
   precede aliases in the final canonical path order.
6. Directory and symlink rows, escaping/dangling/special/temp rejection, compact
   sorted JSON identity, package/checkout counts, before/after offline-probe
   equality, and result identity remain unchanged. Add `hardlinks` and
   `hardlink_groups` counts; `files` counts owner rows, while total bytes count
   each distinct inode once and `path_bytes` counts every regular-file path.
7. Do not copy, break, recreate, normalize, or dereference hard links. The cache
   retained after success is exactly Cargo/libgit's prepared filesystem. The
   inventory authenticates both contents and alias topology.
8. Tests accept single-link files and multi-path groups independent of creation
   order; mutate owner choice, alias target, mode/size/content/link count,
   outside-root links, three-member groups, and before/after topology drift.
   All 14 inherited preparation tests remain required, including DNS failure,
   read-only offline probe, inventory special cases, OOM, and atomic cleanup.
9. Failure closes v4 with no partial credit. Success authorizes only a separate
   zero-row capture-v2 ADR pinning the exact v4 inventory read-only. It does not
   authorize compilation during preparation, target capture, admission, proof,
   query, performance, or a scoreboard row.

No DNS probe, fetch, cache byte, or expected hard-link count may be observed
before the v4 producer and registration are committed and pushed. No gate may
be weakened after the DNS probe begins.

## Result

Proposed. No v4 producer, registration, DNS probe, fetch, cache, hard-link row,
inventory, offline probe, build, capture, or query exists.

## Rejected alternatives

- **Copy aliases into separate files.** Rejected: it changes the prepared cache
  and erases representation identity.
- **Hash each path independently and ignore alias topology.** Rejected: content
  equality is not evidence that the retained filesystem is unchanged.
- **Use inode numbers in the digest.** Rejected: inode allocation is a local
  filesystem accident, not a reproducible semantic identity.
- **Allow unobserved links outside the cache.** Rejected: the supposedly
  self-contained read-only input would depend on an unauthenticated path.
- **Patch v3 and rerun.** Rejected: the hard-link observation occurred under a
  frozen rejection gate.

## Consequences

- Legitimate Cargo/libgit storage sharing can be authenticated without
  weakening path or content identity.
- The resulting inventory is portable across inode renumbering but still binds
  the complete alias graph.

## References

- [ADR-0330](adr-0330-preregister-tock-cache-resolver-correction.md).
- [ADR-0329](adr-0329-preregister-tock-dedicated-cargo-cache.md).
- [P5.5 external target](../../plan/track-5-verified-systems/P5.5-external-target.md).
