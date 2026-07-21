# ADR-0333: Preregister Tock LLVM capture v2

Status: proposed
Date: 2026-07-21

## Context

ADR-0328 capture v1 closes before builds because its ambient Cargo cache is
incomplete. ADR-0332 now accepts a separately prepared, ignored local Cargo home
with hard-link-aware inventory
`fd6ee33dd536c75d654bb750a8919911dd6065f382ea59d8ac0e26464097d379`
and structurally authenticated active resolution
`da6971e417c906a9c0fa81768cfd511136d0946f651a1ec891ce1f7891dbf305`.
No target build has consumed it.

The target-build protocol itself remains valid: two complete archived source
trees at identical virtual paths, independent writable target roots, raw full
LLVM-module equality, compiler-matched extraction, and strict admission. Capture
v2 should change only the cache input and its validation.

## Decision

Create a thin capture-v2 policy wrapper over the frozen ADR-0328 producer. Pin
and recompute ADR-0332's exact `cache-v5/cargo-home` inventory, mount it read-only
at `/axeyum-vroot/cache`, set `CARGO_HOME` to that virtual path, rerun the
structural locked-offline metadata validator before builds, then execute every
remaining ADR-0328 source/build/module/extraction/admission/atomicity gate.

## Frozen v2 gates

1. Commit and push this zero-result ADR before adding v2. Commit and push the
   thin wrapper, focused tests, and compact registration before either official
   build. Capture v1 remains closed and is never rerun.
2. Reuse ADR-0328's exact Tock commit/tree/critical files, complete traversal-
   safe two-root materialization, Git/Cargo/rustc/Bubblewrap/GNU-time/LLVM-22/
   admission identities, build argv, two-build ordering, cgroup limits, raw
   module equality, symbol discovery, extraction/assembly, admission, local-only
   output, and no-query rule by exact base-registration and producer hashes.
3. Pin ADR-0332 committed summary at its exact file hash. Require local envelope
   `target/tock-log2-20260721/cache-v5`, regular `preparation-result.json`, and
   `cargo-home/`; require the local result SHA-256 and identity, inventory,
   structural-probe summary, upstream, and zero-build summary to equal the
   committed result.
4. Before namespace entry, recompute the hard-link-aware cache inventory and
   require exact equality to all committed fields: 3,077 rows, 565 directories,
   2,508 distinct files, four aliases/four groups, zero symlinks, 41,179,781
   distinct bytes, 57,245,401 path bytes, 36 registry packages, two Git
   checkouts, and SHA-256 `fd6ee33d...d379`. Any drift ends v2 before builds.
5. Replace ADR-0328's ambient `/home/mjbommar/.cargo` bind with one read-only
   bind of the exact physical `cargo-home/` at `/axeyum-vroot/cache`. Set only
   `CARGO_HOME=/axeyum-vroot/cache`; keep every other ordered environment value
   unchanged. Do not bind the ambient Cargo home, resolver file, `/run`, network,
   credentials, or a writable cache.
6. In a network-unshared namespace with the first complete source root, exact
   read-only cache, and fresh writable scratch target, rerun ADR-0332's
   structural `cargo metadata --locked --offline` validator. Require exact
   equality to the committed active-resolution summary and recompute inventory
   afterward to prove the probe changed no cache byte/topology.
7. Then build both source roots sequentially with the unchanged exact command:

   ```text
   cargo rustc -p kernel --lib --release --locked --offline --
     -Ccodegen-units=1 -Clink-dead-code --emit=llvm-ir
   ```

   The only run-specific namespace argv bytes are physical source and target
   binds. Cache bind source, virtual destinations, cwd, environment, and child
   argv are identical.
8. Reapply ADR-0328 gates 8--13 unchanged: one module/root; time/RSS/OOM; no
   host-path tokens; matching virtual-path counts; raw complete-module byte
   equality before symbol observation; LLVM-22 full assembly; exact two-comment
   symbol discovery and widths; registered `llvm-extract`; ModuleID-only
   extracted comparison; hash-pinned checked admission; atomic ignored output;
   target bytes never committed.
9. The v2 result schema adds cache inventory/active-resolution identities and
   cache virtual-path occurrences. These stable inputs enter result identity;
   build time/RSS, cgroup path/events, and DNS-free observations do not.
10. Focused tests mutate base/summary/local-result hashes, missing or drifting
    cache topology, ambient-versus-dedicated cache path, writable/wrong cache
    mount/order, structural-probe mismatch/mutation, and v2 atomic cleanup. All
    ADR-0328 producer/admission tests and all ADR-0332 cache inventory/metadata
    tests remain required.
11. Success closes only authenticated local T5.5.2 capture/parser admission and
    authorizes a separate zero-row proof/scoreboard ADR for the already frozen
    Tock obligations. Failure closes v2. Neither outcome authorizes source edits,
    cache preparation, target proof/query, replay, performance claim, or a
    scoreboard row inside this protocol.

No official build, module hash, symbol, extraction, or admission may be observed
before the v2 producer and registration are committed and pushed. No gate may be
weakened after the first official build begins.

## Result

Proposed. The authenticated cache exists locally and is committed only by
summary/digests. No capture-v2 producer, registration, official build, module,
symbol, extraction, admission, query, proof, or scoreboard row exists.

## Rejected alternatives

- **Rerun capture v1 after filling ambient cache.** Rejected: v1's authenticated
  input failed and is frozen.
- **Copy the dedicated cache into ambient Cargo home.** Rejected: it loses exact
  inventory and read-only mount identity.
- **Skip metadata replay because preparation passed.** Rejected: the capture
  must independently prove it consumed the authenticated input.
- **Mount only crate sources and omit index/Git state.** Rejected: that rewrites
  the prepared Cargo-home representation after observation.
- **Start the Tock proof in the capture run.** Rejected: admission success must
  precede a separately frozen query/negative-control protocol.

## Consequences

- Network access remains confined to the completed non-crediting preparation;
  both official target builds are offline.
- Cache completeness and target-build reproducibility become separately
  reviewable identities.

## References

- [ADR-0332](adr-0332-preregister-tock-cache-structural-metadata.md).
- [ADR-0328](adr-0328-preregister-tock-log2-llvm-capture.md).
- [Tock target selection](../../plan/track-5-verified-systems/P5.5-target-selection-tock-log2.md).
- [P5.5 external target](../../plan/track-5-verified-systems/P5.5-external-target.md).
