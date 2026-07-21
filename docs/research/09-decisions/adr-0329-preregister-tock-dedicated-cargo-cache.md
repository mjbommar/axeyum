# ADR-0329: Preregister dedicated Tock Cargo-cache preparation

Status: proposed
Date: 2026-07-21

## Context

ADR-0328 v1 closes before compilation because its frozen full-workspace
`cargo metadata --locked --offline` probe finds that the ambient Cargo cache
lacks `ghash 0.4.4`. Refilling that ambient cache after observing the miss and
rerunning v1 would change an authenticated input after observation.

The selected `kernel` build itself has a much smaller active dependency graph,
but Cargo still resolves an exact disabled optional Git dependency. Guessing a
minimal cache from the observed missing crate would create another adaptive
input. Fetching into the user's ambient Cargo home would also mix unrelated and
mutable state into the capture boundary.

## Decision

Create a separate v2 cache-preparation phase before any successor official
build. One committed, hash-pinned producer will materialize the exact Tock Git
tree, populate a new dedicated Cargo home once with the exact locked workspace,
validate it under a network-isolated read-only mount, and atomically retain the
local cache plus a canonical whole-tree inventory digest. This phase prepares
inputs only: it may fetch, but it may not compile, emit LLVM, invoke the Axeyum
frontend, or run a property query.

## Frozen preparation gates

1. Commit and push this zero-result ADR before adding or running the preparation
   producer. Commit and push the producer, tests, and source/tool/network/command
   registration before the first networked preparation invocation.
2. Reuse ADR-0328's exact Tock commit/tree, critical-file hashes, Git, Cargo,
   rustc, Bubblewrap, source materialization, and 2.5 GiB-high / 4 GiB-max /
   512 MiB-swap scope. The source comes only from traversal-safe `git archive`,
   not the sparse checkout.
3. The output is exactly ignored
   `target/tock-log2-20260721/cache-v2`. It and its sibling partial path must not
   exist before the one official preparation. The envelope contains only the
   dedicated `cargo-home/` payload and `preparation-result.json`; populate the
   partial envelope and rename atomically only after every gate passes.
4. Use a fresh constructed Bubblewrap root. Bind `/usr`, `/etc`, Rustup, and the
   exact source read-only; bind only the partial dedicated Cargo home writable.
   Clear the environment and reject ambient Cargo/Rust flags, proxy overrides,
   registry overrides, credentials, alternate Git/config homes, and compiler
   wrappers. Keep the network shared only for the registered fetch command;
   no source or target directory is writable.
5. From `/axeyum-vroot/source`, with
   `CARGO_HOME=/axeyum-vroot/cache`, run exactly:

   ```text
   cargo fetch --locked
     --manifest-path /axeyum-vroot/source/Cargo.toml
   ```

   Do not use `cargo build`, `cargo check`, `cargo rustc`, `cargo vendor`, a
   package selector, feature override, patch/source replacement, alternate
   registry, retry-time source edit, or preseed copied from the ambient cache.
6. Cargo's exact `Cargo.lock` checksums and Git object IDs authenticate package
   contents. The preparation does not claim transport-byte reproducibility or
   trust the registry as a correctness oracle; its output becomes a separately
   hash-pinned local input for v2.
7. After fetch, remount the dedicated cache read-only in a new Bubblewrap
   namespace with networking unshared and a fresh writable scratch target. Run
   the exact full-workspace locked-offline metadata command rejected by v1.
   Require the Tock workspace root, `kernel` package, 169 lock packages, and no
   network or cache write. Failure is the preparation result.
8. Inventory every retained directory, regular file, and symlink beneath the
   `cargo-home/` payload. Reject sockets/devices/FIFOs, absolute or escaping symlinks, hard-link
   aliasing, and path traversal. The exact Cargo zero-byte package-lock
   sentinels and global-cache database are ordinary inventoried files; reject
   any leftover temporary/download-part path. Canonical rows bind
   relative path, kind, mode, byte size, file SHA-256 or symlink target; sorted
   compact JSON plus a final newline defines the inventory SHA-256. Record row,
   file, directory, symlink, byte, registry-package, and Git-checkout counts.
9. Recompute the inventory after the offline read-only probe and require exact
   equality. Record preparation wall time, peak RSS, and cgroup OOM deltas only
   as observations excluded from the inventory identity.
10. The producer writes a local preparation result beside the cache. Commit
    only Axeyum-owned producer/tests/registration and later the result summary,
    counts, inventory digest, and prose. Cache/package/source bytes remain
    ignored local data.
11. Mutation tests cover registration and producer drift, environment/network
    argv, wrong source/tool/lock, existing/aliased output, traversal/symlink/
    hard-link/special-file inventory cases, fetch/offline-probe failure,
    inventory drift, cgroup/OOM accounting, and atomic cleanup. Stable
    stage/kind and zero partial credit are mandatory.
12. A positive preparation result authorizes only a new zero-row v2 capture ADR
    and registration that pin the exact cache inventory and mount it read-only.
    It does not authorize rerunning v1, compiling during preparation, target
    capture, admission, proof, replay, performance, or a scoreboard row.

No cache content or expected inventory may be observed before the preparation
producer and registration are committed and pushed. No gate may be weakened
after the networked fetch begins.

## Result

Proposed. The separate preparation producer, nine focused mutation/cleanup
tests, exact support/source/tool/environment/namespace/command/resource
registration, and live no-op network/offline namespace probes are frozen with
zero networked fetches. Commit and push this checkpoint before the one official
preparation invocation. No dedicated cache byte, inventory, successor build,
target artifact, or property result exists.

## Rejected alternatives

- **Refill the ambient cache and rerun v1.** Rejected: it changes a frozen input
  after observing the exact miss.
- **Fetch only `ghash`.** Rejected: the observed first miss cannot define an
  independently complete input boundary.
- **Copy the currently sufficient ambient subset.** Rejected: selection would
  depend on mutable host state and the failed run's demand order.
- **Vendor dependencies into the repository.** Rejected: it expands committed
  third-party bytes and changes the intended external-source boundary.
- **Build online once to discover the dependency closure.** Rejected: that is
  already a target build and would consume the first output observation before
  the capture protocol is frozen.

## Consequences

- Network access is confined to a named non-crediting input-preparation phase.
- The eventual official builds can use one exact read-only cache rather than an
  ambient cache whose completeness and unrelated contents are unknown.
- Full-workspace fetch may be larger than the active kernel closure; that cost
  is preferable to an adaptive post-miss subset and will be measured honestly.

## References

- [ADR-0328](adr-0328-preregister-tock-log2-llvm-capture.md).
- [Tock target selection](../../plan/track-5-verified-systems/P5.5-target-selection-tock-log2.md).
- [P5.5 external target](../../plan/track-5-verified-systems/P5.5-external-target.md).
