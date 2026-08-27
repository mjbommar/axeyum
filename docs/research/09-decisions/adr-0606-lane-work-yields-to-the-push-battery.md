# ADR-0606: lane work yields to the push battery, by cgroup weight in a sibling slice

Status: accepted
Date: 2026-08-27
Index-summary: The pre-push battery was starved because `scripts/cargo-serialized.sh` bounds memory and nothing bounded CPU, and because pre-push, `check.sh` and the justfile called the wrapper zero times between them; lane work now runs at `CPUWeight=10` in `axeyumlane.slice` (a true sibling of a session scope) while the battery runs unweighted, measured 1.89x -> 1.11x inflation under identical offered load, with no gate step dropped.
Index-status: accepted

## Context

The programme's operating mode is 3-5 permanent parallel lanes, and every merge
costs a `hooks/pre-push` battery. Measured 2026-08-27 on s4 (16 cores), that
battery went from ~250 s uncontended to **2,152 s and 2,654 s** under 4-5 lanes,
with inflation of 4.0x / 6.8x / 4.9x / 5.5x spread roughly uniformly across
kernel suites, corpus sweep, solver unit sweep and golden pins. Uniform
inflation across unrelated steps is starvation, not a regression in any gate.

The parallelism that produces the work is what destroys the ability to merge it.
That makes verification throughput the binding constraint on the flywheel, and
it is the same question
[`05-throughput.md`](../../formalized-math-2026-08/05-throughput.md) C1 left
open when sharding the library did not move `f`.

Full measurement:
[`../11-design-review/2026-08-27-gate-throughput.md`](../11-design-review/2026-08-27-gate-throughput.md).

Three facts decided this, and each contradicted the obvious reading:

1. **`scripts/cargo-serialized.sh` has not been a serializer since 2026-08-18.**
   It is a counting semaphore of `clamp(RAM/MEM, 1, 6)` slots — 5 here — and it
   bounds **memory** only. `AXEYUM_CARGO_CPUS` defaults unset, so five jobs each
   take `nproc` threads. CLAUDE.md, this lane's brief, and three documents all
   still said "one cargo at a time".
2. **Nothing that consumes this box was inside the semaphore.** `hooks/pre-push`
   takes an unrelated flock of its own; `scripts/check.sh`, the `justfile` and
   `scripts/local-ci.sh` take none. The only callers in `scripts/` were
   `check-kernel-stack-envelope.sh` and the mutation harness. Admitted
   concurrency was not 5; it was unbounded, and the authoritative pre-merge gate
   was one more equal consumer.
3. **`nice` does not fix it.** With `sched_autogroup_enabled=1`, scheduling is
   per **session**, so `nice` reorders within a session and barely crosses the
   boundary. A controlled A/B with 27 competitors in both arms measured
   **1.85x vs 1.82x — 1.01x, no effect**, despite the nice values being verified
   as applied down to forked grandchildren.

## Decision

**Lane work yields to the push battery, and it does so by cgroup CPU weight in a
slice that is a sibling of a session scope.**

- `scripts/cargo-serialized.sh` runs jobs in `axeyumlane.slice` at
  `CPUWeight=10` (systemd default is 100), plus `nice 10` and `ionice -c 3`.
- `hooks/pre-push` sets `AXEYUM_CARGO_NICE=0` and runs unweighted.
- `scripts/check.sh` takes **one** cargo slot for its whole run
  (`cargo-serialized.sh --batch`), with a re-entrancy marker so nested calls do
  not take a second.
- The battery additionally takes an **advisory, fail-open** slot.

The slice name has no dash **on purpose**: systemd reads `-` as hierarchy, so
`axeyum-lane.slice` would be a child of `axeyum.slice` and the weight would
apply one level too deep.

### What this decision is not

It is not an admission-control policy. Nothing blocks, no lane is denied, and no
gate can be prevented from running by a scheduling mechanism. It is not a
statement about *how many* lanes may run. And it changes no step's inputs,
outputs, ordering, or exit status.

## Consequences

Measured after, same harness, identical offered load (27 competitors in both
arms, asserted), subject width 16 to match a `cargo test` binary:

```
QUIET   6.1s
BEFORE 11.5s   unweighted                  1.89x inflation
AFTER   6.8s   nice 10 + CPUWeight 10      1.11x inflation
speedup 1.69x
```

Residual inflation falls from 89% to 11%. The figures are from a **reduced**
run (3 x 8 rather than 5 x 16) because another lane's battery was resident;
`scripts/measure-gate-admission.sh` now refuses to run at all while one is,
since oversubscribing the box against somebody else's gate is the harm this ADR
removes.

Costs and risks, stated:

- **A lane's own work is slower when a battery is running.** That is the trade
  being made deliberately: batch throughput yields to the gate everyone is
  blocked behind. When the box is quiet the weight is inert — a lone job still
  gets every core.
- **The weight is per-host and depends on cgroup `cpu` delegation.** Where the
  user manager does not delegate it, only `nice`/`ionice` apply, and on a host
  with autogrouping that is close to nothing. `scripts/tests/test-gate-admission-controls.sh`
  skips rather than failing there, and says so.
- **A lane that does not call the wrapper is unaffected.** `check.sh` is wired;
  the `justfile`'s ~90 recipes are not, and remain future work.

## Alternatives rejected

- **Shared `CARGO_TARGET_DIR` across lane worktrees.** The largest apparent win
  (246 worktrees, ~363 GB, each paying a cold build) and unsound here with an
  incident to cite: cargo bakes absolute paths into `CARGO_MANIFEST_DIR`, and on
  2026-08-01 a shared target dir made the main checkout reuse a binary whose
  manifest dir no longer existed (`read_dir(/tmp/axeyum-prepush.ll4jFr/...)`),
  with `-p <pkg> --lib` passing while `--workspace --lib` failed. Cargo also
  locks the build directory, so sharing serializes builds host-wide as an
  unchosen side effect. **`sccache` is the right shape of this idea** and needs
  its own evaluation; it does not belong in a scheduling change.
- **Capping `-j` / `--test-threads` per slot.** Taxes the common case (a lone
  job on an idle box becomes N times slower) to fix the contended one.
- **Hard admission control — the battery reserves every slot.** Converts a slow
  gate into one a stream of lane jobs can starve indefinitely, and couples push
  latency to lane scheduling. The advisory form gets the memory accounting
  without the failure mode.
- **Dropping or narrowing a battery step.** Examined and rejected on evidence.
  `axeyum-solver` depends on `axeyum-lean-kernel` under `--features full`, so a
  kernel-only push — the shape every library lane makes — is inside the build
  closure of both always-on solver steps, and `--skip reconstruct::` is a
  runtime filter rather than a proof of non-reachability. The gating was already
  as tight as it soundly can be. The one filter that was **too loose** was
  widened instead: `Cargo.lock` is not `*.toml`, so a dependency bump skipped
  the entire battery (verified against `f8173a069` — 4 files changed, 0 seen).

## The general rule this instance teaches

**A property that is applied is not a property that has effect, and reading it
back does not tell them apart.** This wrapper has now produced the same failure
three times:

- `MemoryMax` without `MemorySwapMax` — `memory.max` read correctly, and a
  400 MB allocation survived, because the cgroup swapped.
- `nice 10` — verified on forked grandchildren, and worth 1.01x, because
  autogrouping schedules per session.
- `CPUWeight=10` — `cpu.weight` read back as `10` twice, at two different wrong
  cgroup levels, ordering lane jobs against each other and nothing else.

In each case the check that would have caught it is not "is it set" but "is the
thing it is set *relative to* the thing you meant". So a control for a resource
policy must assert the **relation** — the sibling level, the swap ceiling, the
scheduling domain — and never only the value. This is the resource-policy form
of the checker-that-cannot-fail defect, and the value check is exactly the
comfortable check that cannot fail.
