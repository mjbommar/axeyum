# ADR-0332: Preregister Tock cache structural metadata authentication

Status: accepted
Date: 2026-07-21

## Context

ADR-0331 preparation v4 validates DNS, the locked fetch, and hard-link-aware
cache inventory. Its offline probe then fails because an inherited assertion
equates 162 active metadata packages with all 169 `Cargo.lock` entries. A lock
file legitimately retains inactive target/feature alternatives, so equal counts
are not a sound cache-completeness invariant.

Using the observed 162 as the next expected count would merely replace one
accidental constant with another. The correct boundary is whether Cargo's exact
active resolution is closed, source-authenticated, and backed by the exact
lockfile and materialized source tree.

## Decision

Create preparation v5 with output
`target/tock-log2-20260721/cache-v5`. Reuse ADR-0331's complete DNS/fetch/
hard-link-inventory/resource/no-compilation/atomic pipeline. Replace only the
offline metadata validator with a structural package-graph and lockfile
authentication rule. Record active counts and a canonical active-resolution
digest as results; do not preregister either value.

## Frozen v5 gates

1. Commit and push this zero-result ADR before adding v5. Commit and push the
   thin v5 producer/tests/registration before DNS or fetch. V4 is never rerun.
2. Reuse the compact ADR-0331 registration by exact hash. The v5 overlay may
   change only schema, output version, producer identities, and metadata
   validator schema/version. All source/tool/resolver/DNS/fetch/namespace/
   environment/inventory/resource fields remain byte-identical.
3. Keep the independent source check that exact `Cargo.lock` contains 169
   `[[package]]` tables. Parse it with Python's standard TOML parser. Reject
   duplicate lock identities `(name, version, source-or-null)` and malformed
   names, versions, sources, or checksums.
4. Run the unchanged full-workspace `cargo metadata --locked --offline` command
   with the cache read-only and network unshared. Require exact virtual
   `workspace_root`, a package array, resolve object, node array, and workspace
   member/default-member arrays.
5. Require every metadata package ID unique and every resolve-node ID unique.
   The package-ID set and node-ID set must be equal. Every dependency edge and
   dependency-package reference must target a known ID; every workspace/default
   member must be known, and defaults must be workspace members.
6. Require exactly one metadata package named `kernel`, exactly one matching
   resolve node, and that package in workspace members. Do not select by array
   position or observed count.
7. For every external metadata package, require exact `(name, version, source)`
   membership in the lockfile. Registry rows require the exact lock checksum;
   Git sources require the exact locked URL/query/revision. For every null-source
   path package, require its manifest path to be beneath
   `/axeyum-vroot/source`, map to an existing regular file in the independently
   materialized source tree, and match a null-source lock identity.
8. Reject any metadata package absent from the lockfile, unknown graph ID,
   duplicate identity, escaping/missing manifest, or malformed source/checksum.
   Inactive lock entries are permitted and counted but need not appear in the
   active metadata graph.
9. Canonicalize sorted active rows binding package ID, name, version, source,
   checksum-or-null, and virtual manifest path. Compact sorted JSON plus a final
   newline defines `active_resolution_sha256`. Record active/external/path/
   registry/Git/node/edge/workspace/default counts and the digest only after all
   checks pass; none is an expected gate.
10. Recompute the hard-link-aware cache inventory after the structural probe
    and require exact equality. The read-only probe may not mutate cache bytes or
    topology.
11. Focused tests cover inactive lock entries, duplicate lock/package/node IDs,
    unknown edges, workspace/default closure, missing/multiple kernel, registry
    checksum and Git-source drift, path escape/missing manifest, active-row
    order independence, and count changes without expected constants. All 18
    inherited preparation tests remain required.
12. Failure closes v5 with no partial credit. Success authorizes only a separate
    zero-row capture-v2 ADR pinning the exact cache-v5 inventory read-only. It
    authorizes no preparation-time build, target capture, admission, proof,
    query, performance claim, or scoreboard row.

No DNS probe, fetch, cache byte, active count, or active digest may be observed
before the v5 producer and registration are committed and pushed. No gate may
be weakened after the DNS probe begins.

## Result

Accepted. Pushed producer `020f079c` completes one DNS probe and locked fetch,
then passes hard-link-aware inventory, the structural read-only/offline metadata
gate, unchanged post-probe inventory, and zero OOM deltas. The retained local
Cargo home has identity:

- 3,077 rows: 565 directories, 2,508 distinct files, four hard-link aliases in
  four groups, zero symlinks;
- 41,179,781 distinct file bytes / 57,245,401 path bytes;
- 36 registry package directories and two Git checkouts; and
- inventory SHA-256
  `fd6ee33dd536c75d654bb750a8919911dd6065f382ea59d8ac0e26464097d379`.

The structural probe authenticates 162 active packages/nodes and 814 dependency
edges against all 169 lock entries: 129 path packages, 32 registry packages,
one Git package, exactly one workspace `kernel`, 129 workspace/default members,
and active-resolution SHA-256
`da6971e417c906a9c0fa81768cfd511136d0946f651a1ec891ce1f7891dbf305`.
Those populations are results, not expected thresholds.

An independent post-run recomputation matches the inventory byte-for-byte.
Fetch observation is 7,799 ms / 84,308 KiB peak RSS; every cgroup OOM delta is
zero. No build, target capture, admission, property query, proof, or scoreboard
row exists. Cache bytes remain ignored local data; committed summary identity is
`3c926909d28380f95da23ef3170f069b46cd2642d23e712b660074c61068fb06`.
This positive input-preparation result authorizes only a separately
preregistered capture-v2 protocol pinning the exact retained inventory read-only.

## Rejected alternatives

- **Expect 162.** Rejected: it is the prior run's observation, not an invariant.
- **Require every lock entry active.** Rejected: target/feature alternatives are
  valid authenticated inactive state.
- **Check names only.** Rejected: version and source identity are part of Cargo
  package identity.
- **Trust metadata without the lockfile.** Rejected: the read-only cache must be
  tied to the exact committed dependency authentication boundary.
- **Patch v4 and rerun.** Rejected: its numeric gate has an official result.

## Consequences

- The dedicated cache is now an authenticated local input rather than ambient
  mutable state.
- Official target builds remain unauthorized until a fresh capture-v2 ADR and
  registration pin this exact inventory and build protocol.

## References

- [ADR-0331](adr-0331-preregister-tock-cache-hardlink-inventory.md).
- [ADR-0330](adr-0330-preregister-tock-cache-resolver-correction.md).
- [P5.5 external target](../../plan/track-5-verified-systems/P5.5-external-target.md).
