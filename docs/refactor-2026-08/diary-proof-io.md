# Diary: dropping written proof pages from the page cache (item 05.1)

Lane: `proof-io`. Date: 2026-08-15.

Scope: `docs/refactor-2026-08/05-proof-consumption.md` item 05.1 only. 05.2
(mmap) is explicitly out of scope — it needs an ADR for an `unsafe_code`
exception and its prize (1.49x -> sub-1x) is smaller than 05.1's.

## Dependency check, done first as instructed

`rustix` on its `linux_raw` backend was checked before adopting, not assumed:

- `rustix = { default-features = false, features = ["fs", "std"] }` resolves
  to the `linux_raw` backend on this target. `cargo tree` after `cargo build`
  shows only `rustix`, `bitflags`, `linux-raw-sys` compiled — **no `libc`
  crate is built** for this dependency edge (verified both in a scratch crate
  and in the real `axeyum-cnf` build).
- The safe half matters as much as the C-free half: `rustix::fs::fadvise`
  takes `impl AsFd`, and `std::fs::File: AsFd` is a *safe* method (Rust
  1.63's I/O-safety traits) — no `unsafe { BorrowedFd::borrow_raw(..) }`
  needed anywhere in our code. `grep -c unsafe` on the new code is zero, and
  the workspace's `unsafe_code = "deny"` lint (already active on
  `axeyum-cnf`) confirms it — clippy passed with the lint on.
- Aside: `rustix` (and transitively `libc`, via `cpu-time`/`getrandom` used by
  `rustsat`/`tempfile`) was already in the dependency graph before this
  change. This change only makes `axeyum-cnf` a *direct* consumer of an
  already-vetted, already-present crate.
- Target-gated to `cfg(unix)` in both `Cargo.toml`s, the same pattern already
  used for `web-time` on `wasm32`. `wasm32-unknown-unknown` never sees the
  dependency at all — confirmed with `cargo tree --target
  wasm32-unknown-unknown -p axeyum-solver -i rustix` (no output: not in the
  graph for that target), and `cargo build --target wasm32-unknown-unknown -p
  axeyum-solver` succeeds.
- `cargo deny check` exits 0 (`advisories ok, bans ok, licenses ok, sources
  ok`); the licenses of `rustix`/`bitflags`/`linux-raw-sys` are already on the
  allow list (MIT/Apache-2.0 family) and produced no new warning.

Conclusion: a safe, C-free route exists and was used.

## What shipped

`CacheDroppingWriter<F>` in `crates/axeyum-cnf/src/drat.rs` (`cfg(unix)`,
re-exported from the crate root): a `Write` wrapper for a real file handle
that calls `posix_fadvise(POSIX_FADV_DONTNEED)` over the bytes just written,
batched to a 64 MiB interval (`CACHE_DROP_INTERVAL_BYTES`), plus one final
call on `flush()` for the tail. Wrap the target `File` in it before handing it
to `TextProofSink::new`.

Wired into the three real producers of large proofs found by grep:

- `crates/axeyum-cnf/examples/sorting_network.rs` — already passed a bare
  `File`; now wraps it.
- `crates/axeyum-search/examples/recertify_rado.rs` — **the actual producer
  of the 19.9 GB Rado certificate that motivated this item.** Also dropped a
  redundant outer `BufWriter::new(file)` (`TextProofSink` already buffers
  64 KiB internally; the double-buffering was pure overhead and, more to the
  point, it hid the file's file descriptor behind a type that doesn't
  implement `AsFd`, which would have blocked wiring this in at all — see
  "one specialization dead end" below).
- `crates/axeyum-search/examples/akb2_frontier.rs` — same redundant
  `BufWriter` removed, same wrapper wired in.

All three are `#[cfg(unix)] ... #[cfg(not(unix))] ...` branches so they still
build on any target; only the `unix` arm changes behavior.

## One specialization dead end, recorded so it isn't retried

The first instinct was to make `TextProofSink<W>` itself drop pages
automatically, for any `W`, with no wrapper type. That runs into two walls:

1. `TextProofSink<W>`'s `finish`/`flush` are generic over `W: Write`, used
   with `Vec<u8>` and `String` sinks throughout the test suite. Adding an
   `AsFd` bound to the existing generic impl would break every non-file
   caller; Rust has no stable specialization to give `File` a different body
   than `Vec<u8>` under one method name.
2. Even restricted to file-backed callers, `BufWriter<File>` — the exact
   shape both `axeyum-search` call sites used — **does not implement `AsFd`**
   (confirmed by compiling `fn f<W: AsFd>(w: &W) {} f(&BufWriter::new(file))`
   and getting `E0277`). Only the file itself does. So the fix has to sit at
   the layer that holds the real file descriptor, which is also the reason
   the redundant outer `BufWriter` had to go.

The wrapper (`CacheDroppingWriter<F: Write + AsFd>`, composed *underneath*
`TextProofSink`'s own buffering) sidesteps both: it only exists for callers
that opt in, and it only needs to compile against whatever `F` the caller
actually hands it (here, always `File`).

## Measurement 1: per-write fadvise was 2.9x slower — this is why the design
batches

First implementation called `fadvise` after every `write`/`write_all`, i.e.
once per 64 KiB chunk `TextProofSink`'s internal `BufWriter` spills. Measured
on the `/nas3/data/axeyum` NFS mount (256 MiB synthetic DRAT-shaped write):
**9.53 s wrapped vs 3.27 s unwrapped — 2.9x slower.** That's ~4,096 `fadvise`
calls costing roughly 1.5 ms each on this mount; not free, and not something a
production run should pay per-64 KiB.

Fix: batch to `CACHE_DROP_INTERVAL_BYTES = 64 MiB`, so a call fires roughly
every 64 MiB of new data instead of every 64 KiB, plus one more for the tail
on `flush()`. Re-measured at the same 256 MiB size: **3.80 s wrapped vs
3.31 s unwrapped — ~15% overhead**, and on real (non-tmpfs) local disk at
1 GiB: **3.86 s vs 3.72 s — ~4% overhead.** This is the version that shipped.
This tradeoff is explicit in the type's doc comment so nobody "simplifies" it
back to per-write.

## Measurement 2: page-cache footprint, before vs after (the exit criterion)

Host is `server0` (`hostname`), not one of `s1`/`s5`/`s6`/`s7` named in the
brief — those hostnames do not exist on this box; `server0` was the only
machine available to run this on. Local disk is `/dev/nvme0n1p1` (**ext4**,
457 GB free at time of test) — real, not `tmpfs`. `/nas3/data/axeyum` is a
genuine NFS4 mount (confirmed via `mount`), used for a second measurement
below. A synthetic ~4.15 GB DRAT-shaped stream (195M add-clause steps, real
`TextProofSink` + real `DratSink` calls, not a raw `dd`) was written twice:
once through a plain `File`, once through `CacheDroppingWriter`-wrapped
`File`. Isolated per-file residency via `fincore` (util-linux 2.41.3), plus
`/proc/meminfo`'s system-wide `Cached` as a secondary, noisier signal (this
box has other lanes' builds running concurrently).

**On ext4 (the disk that actually matters for the motivating scenario — local
build-lane cache contention):**

| | file size | `fincore` RES (resident bytes) | resident fraction | system `Cached` delta |
|---|---:|---:|---:|---:|
| before (plain `File`) | 4,457,646,498 | 4,457,648,128 | **100%** | +4,250,188 kB (~4.05 GiB) |
| after (`CacheDroppingWriter`) | 4,457,646,498 | 652,115,968 | **14.6%** | +1,437,724 kB (~1.37 GiB) |

Resident footprint for this write dropped from 100% to 14.6% of the file — an
~85% reduction in what stays cached from a single proof write. The residual
~622 MiB is consistent with the tail: pages within the most recent advise
interval, or pages the kernel's async writeback (kicked by `fadvise` but not
waited on — `fadvise(DONTNEED)` never blocks or forces a sync) had not yet
flushed to clean at the moment of the call, since `POSIX_FADV_DONTNEED` only
evicts *clean* pages and does not force writeback of dirty ones.

**On NFS: no measurable effect.** Same synthetic write (256 MiB, since the
2.9x per-write regression above was found on this mount first) showed
`fincore` reporting the wrapped file **100% resident**, identical to the
unwrapped file, both immediately after the write and after an additional 8 s
delay. Best explanation, consistent with the ext4 result: `fadvise(DONTNEED)`
only reclaims clean pages, and on this NFS4 mount the written-back state
either never converges to "clean" from the client cache's perspective in the
observed window, or the client's `fadvise` handling doesn't route through the
same clean/dirty invalidation path local ext4 does. This was not chased
further (out of scope for 05.1: the motivating incident — "three build lanes
competing for cache" — describes local box cache pressure, not NFS), but it
is a real, measured gap: **this fix has no shown effect for proofs written
directly to the NFS mount**, only for local disk. Flagging for whoever picks
up proof output placement.

## Byte-identity (the "does not change a single byte" requirement)

Two routes, both real, not just the small in-memory unit test:

1. Unit test `drat::tests::cache_dropping_writer_output_is_byte_identical_to_the_plain_file`
   in `crates/axeyum-cnf/src/drat.rs`: writes a small mixed add/delete/empty-
   clause proof through both a plain `File` and a `CacheDroppingWriter`-
   wrapped `File`, reads both back, asserts equal bytes and equal to
   `write_drat`'s in-memory serialization. Runs in `cargo test -p axeyum-cnf`.
2. The 4.15 GB measurement pair above: `sha256sum` on both output files —
   **identical digest**
   (`d149b75e2255fc59a7c540861f6c95c83c202e1fc697c9a83874ceed9a84cc88`) on
   both the plain and the `CacheDroppingWriter`-wrapped output. `fadvise`
   never touched a byte of either file; only the OS cache's residency
   differs.

## Gates run

- `cargo test -p axeyum-cnf` — 372 lib tests + 4 integration suites + 3
  doc-tests, all green (nonzero, confirmed each run).
- `cargo clippy -p axeyum-cnf --all-targets --all-features -- -D warnings` —
  clean.
- `cargo clippy -p axeyum-search --examples --all-features -- -D warnings`
  and `cargo test -p axeyum-search --all-features` (89 tests) — clean; run
  because this lane also touched the two `axeyum-search` examples that are
  the real large-proof producers.
- `cargo build --target wasm32-unknown-unknown -p axeyum-solver` — succeeds;
  `rustix` confirmed absent from that target's dependency graph.
- `cargo deny check` — exits 0.
- All builds used `CARGO_BUILD_JOBS=4`; the 4+ GB measurement writes went to
  `/home/mjbommar/proof_io_local_test` (ext4) and `/nas3/data/axeyum/proof-io-test`
  (NFS), both cleaned up (`rm`/`rmdir`) after the measurement.

## Bottom line

A safe, C-free `posix_fadvise(DONTNEED)` route exists (`rustix`,
`linux_raw` backend, zero `unsafe` in our code) and is now wired into
`TextProofSink`'s three real large-proof producers via a new
`CacheDroppingWriter` wrapper. Measured on real ext4: resident footprint for
a 4.15 GB write drops from 100% to ~15%, at ~4% wall-clock cost, with
byte-identical output (unit test + SHA-256 on the multi-GB pair). No effect
was measured on the NFS mount tested — noted as an open gap, not silently
absorbed into the win.
