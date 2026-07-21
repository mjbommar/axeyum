# ADR-0330: Preregister Tock cache resolver correction

Status: accepted
Date: 2026-07-21

## Context

ADR-0329 preparation v2 shares the host network but fails before download
because its constructed root binds `/etc` while omitting the runtime target of
the relative `/etc/resolv.conf` symlink. The host target is exactly
`/run/systemd/resolve/stub-resolv.conf`; a no-op namespace probe did not expose
that missing input.

The cache, locked fetch, offline validation, inventory, resource, and atomicity
designs were not reached. The successor should correct only resolver
availability and make the probe exercise name resolution.

## Decision

Create preparation v3 as a separate producer and output
`target/tock-log2-20260721/cache-v3`. Reuse every ADR-0329 non-network gate
unchanged. In the network-enabled namespace only, construct
`/run/systemd/resolve`, bind the exact host stub resolver file read-only at the
same absolute path, and require a registered `getent ahostsv4 github.com` probe
to return at least one syntactically valid IPv4 address before the one locked
Cargo fetch.

## Frozen v3 gates

1. Commit and push this zero-result ADR before adding v3. Commit and push the
   v3 producer/tests/registration before its DNS probe or networked fetch.
   Preparation v2 remains closed and is never rerun.
2. Reuse ADR-0329's exact Tock source, complete Git-archive materialization,
   support code, Cargo/rustc/Git/Bubblewrap/GNU-time identities, cleared
   environment, locked full-workspace fetch, offline read-only metadata replay,
   169-package gate, canonical whole-cache inventory, resource/OOM accounting,
   no-compilation rule, and atomic envelope. Only the items below change.
3. Pin `/run/systemd/resolve/stub-resolv.conf` at SHA-256
   `acfee52a6a0860bf1ff42bfa79d349f2373a9defc0fb05990489743ae0965ec1`,
   regular-file mode `0644`, and size 939 bytes. Reject drift before entering a
   namespace. Do not bind all of `/run`, the systemd-resolved socket, D-Bus,
   Tailscale state, host credentials, or another resolver file.
4. In the network root argv, create `/run`, `/run/systemd`, and
   `/run/systemd/resolve`, then read-only bind that exact file at its existing
   path. The offline root remains ADR-0329's network-unshared root with no
   `/run` input.
5. Pin `/usr/bin/getent` at SHA-256
   `fb07378c47e0560ca954eb2c48b2138f0560ee86132ce8ad0bd296e472df5c04`
   and version `getent (Ubuntu GLIBC 2.43-2ubuntu2) 2.43`. In a fresh
   network-enabled namespace with the exact fetch mounts/environment, run only:

   ```text
   /usr/bin/getent ahostsv4 github.com
   ```

   Require exit zero, nonempty output, and at least one whitespace-delimited
   first field accepted by Python's strict IPv4 parser. Record returned
   addresses only as observations excluded from cache/preparation identity; do
   not pin, rank, or inject them into Cargo.
6. After the DNS probe, run the unchanged exact `cargo fetch --locked
   --manifest-path /axeyum-vroot/source/Cargo.toml` in a second fresh namespace.
   Cargo performs its own DNS/TLS/Git/registry requests; the probe does not
   substitute an address or relax certificate verification.
7. The output envelope is ignored `cache-v3/{cargo-home,
   preparation-result.json}`. It and its partial sibling must not exist before
   the one official v3 invocation. V2 output paths remain absent.
8. Mutation tests add resolver hash/mode/size, missing/wrong bind destination or
   order, accidental resolver bind in the offline namespace, DNS command/host,
   empty/malformed/mixed/valid output, and DNS failure cleanup. All ADR-0329
   registration/environment/source/fetch/probe/inventory/resource/cleanup tests
   remain required.
9. A DNS or fetch failure closes preparation v3 with no partial credit. Success
   still authorizes only a separate zero-row capture-v2 ADR that pins the exact
   `cache-v3/cargo-home` inventory read-only. Neither outcome authorizes a build,
   target capture, admission, proof, query, performance claim, or scoreboard row.

No DNS probe, fetch, cache byte, or expected inventory may be observed before
the v3 producer and registration are committed and pushed. No gate may be
weakened after the DNS probe begins.

## Result

Accepted as a negative preparation-v3 result. Producer commit `384e2045` was
pushed before invocation. The real DNS probe and exact locked fetch both
complete, proving the one-file resolver correction. The first inventory then
stops on ADR-0329's frozen hard-link rejection:

```text
stage=inventory
kind=hardlink
detail=git/checkouts/firmware-.../.git/objects/pack/...idx=
       git/db/firmware-.../objects/pack/...idx
```

Cargo/libgit represents the same firmware pack index inode in its Git database
and checkout. V3 does not inspect further cache contents or complete an
inventory. It runs no offline probe, build, capture, or query; atomic cleanup
leaves no cache or partial directory, and no OOM-delta failure is reported.
Exact negative metadata is committed in `cache-v3-preparation-negative.json`.

Changing the inventory after observing this inode alias and rerunning v3 would
weaken a frozen gate. V3 ends here. A successor must preregister canonical
hard-link rows that bind the alias path to a lexicographically selected in-cache
file plus the shared mode/size/content hash, while keeping every DNS/fetch/
offline/resource/no-compilation gate unchanged.

## Rejected alternatives

- **Add all of `/run`.** Rejected: it exposes unrelated mutable runtime state.
- **Replace `/etc/resolv.conf` with a generated file.** Rejected: that invents a
  new network input rather than restoring the host file selected by the exact
  symlink.
- **Hard-code the currently observed GitHub address.** Rejected: Cargo must
  retain normal DNS, TLS hostname, and certificate validation.
- **Use a no-op probe again.** Rejected: v2 proves mount-namespace liveness is
  not resolver liveness.
- **Rerun v2 with an ad hoc bind.** Rejected: its root argv is frozen and the
  official failure has already been observed.

## Consequences

- The only new host input is one exact public resolver configuration file.
- The resolver correction is validated: DNS and locked fetching succeed.
- The remaining failure is cache-representation fidelity, not network access or
  package availability.

## References

- [ADR-0329](adr-0329-preregister-tock-dedicated-cargo-cache.md).
- [ADR-0328](adr-0328-preregister-tock-log2-llvm-capture.md).
- [P5.5 external target](../../plan/track-5-verified-systems/P5.5-external-target.md).
