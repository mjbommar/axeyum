# Gate throughput: where the pre-push battery's time actually goes

Lane: `gate-throughput`. Measured 2026-08-27 on s4 (16 cores, 123 GB RAM).

Companion to [`2026-08-27-architecture-review.md`](2026-08-27-architecture-review.md)
§4 (last bullet: "suite wall-clock is trending toward a publication gate") and
[`../../formalized-math-2026-08/05-throughput.md`](../../formalized-math-2026-08/05-throughput.md)
C1/C4. C1 recorded that sharding the library did **not** move `f`, and left the
open question: *if not the file lock, what is `f` actually spent on?* Part of the
answer is here — a merge costs a battery, and a battery under lane contention
costs ~35 minutes.

## The observation being diagnosed

Two consecutive `hooks/pre-push` batteries under 4-5 concurrent lanes, against
the same steps run earlier the same day on a quiet box:

| Step | uncontended | contended | inflation |
|---|---|---|---|
| kernel suites (non-Lean integration) | 105 s | 422 s | 4.0x |
| corpus `:status` sweep | 39 s | 266 s | 6.8x |
| solver unit sweep | 55 s | 269 s | 4.9x |
| golden Lean module pins | 41 s | 226 s | 5.5x |
| **battery total** | ~250 s | **2,152 s / 2,654 s** | ~9x |

Inflation is roughly uniform across steps. That is the signature of
**starvation**, not of a regression in any one gate: a gate that got slower gets
slower by itself.

## Finding 1 — the wrapper is a 5-slot semaphore, not a serializer

`CLAUDE.md` says "one cargo at a time on this host". The brief for this lane
says the wrapper "already serialises heavy cargo behind an `flock`". **Both are
out of date, and the script says so in its own header.**

`scripts/cargo-serialized.sh` was changed (comment dated 2026-08-18) from a
mutex to a **counting semaphore**:

    AXEYUM_CARGO_SLOTS   concurrent jobs on this host (default: RAM / MEM, 1..6)

with `slots_default()` = `clamp(floor(RAM_GB / MEM_GB), 1, 6)`. On this host:

    MemTotal_GB=123, AXEYUM_CARGO_MEM default 24G  ->  floor(123/24) = 5 slots

Confirmed against the filesystem rather than by reading the arithmetic — the
slot files exist and are numbered 1..5:

    /var/tmp/axeyum-cargo.lock.1 .. .lock.5

The change was correct on its own terms and its reasoning is sound: the hazard
the lock was built for is **memory**, and `MemoryMax`+`MemorySwapMax` bound that
per job, so blocking on CPU was too strict. But the consequence is the thing
being diagnosed here:

**The semaphore bounds memory. Nothing in it bounds CPU.** `AXEYUM_CARGO_CPUS`
(the `taskset` list) defaults to *unset* — no pinning, and no `-j` cap. So five
concurrent cargo jobs each spawn `nproc`-wide rustc codegen and `nproc`-wide
test threads on a 16-core box. Five slots x 16 threads is a 5x CPU
oversubscription that the wrapper permits by design, and load 17.7 on 16 cores
is fully consistent with it.

## Finding 2 — the battery does not take a slot at all

The battery is not one of the five. It takes a **different lock**:

`hooks/pre-push` opens `$GATE_ROOT/.lock` (`/data0/axeyum/prepush/.lock`) and
`flock`s it, then runs bare `cargo test` / `cargo check` invocations. It never
calls `scripts/cargo-serialized.sh`.

Measured, with a positive control for the grep (an empty grep and a wrong query
are the same observation):

    grep -c cargo-serialized hooks/pre-push        -> 0    (negative)
    grep -c cargo-serialized scripts/local-ci.sh   -> 1    (positive control)
    grep -c cargo-serialized scripts/check.sh      -> 0
    grep -c cargo-serialized justfile              -> 0

So the two locks are disjoint populations:

- `$GATE_ROOT/.lock` serializes **battery against battery** (correct, and
  deliberate — the header explains why the gate worktree is shared not per-lane).
- `/var/tmp/axeyum-cargo.lock.{1..5}` admits **up to five lane cargo jobs**.

Nothing serializes a battery against a lane. The battery is the *lowest*-priority
consumer on the box in practice: it starts last and competes with five slots'
worth of work that was already resident.

**And `scripts/check.sh` and the `justfile` do not use the wrapper either**, so
a lane running `just check` — which is what lanes are told to run — is a heavy
cargo job outside the semaphore too. The admitted concurrency on this host is
therefore *not* 5. It is 5 (semaphore) + 1 (battery) + N (every lane invoking
`just check`, `cargo test`, or bare `cargo` directly).

That is the measured answer to "how are 4-5 lanes plus a battery contending at
all": **almost nothing that runs is inside the lock.**
