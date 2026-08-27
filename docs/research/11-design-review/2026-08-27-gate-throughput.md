# Gate throughput: where the pre-push battery's time actually goes

Lane: `gate-throughput`. Measured 2026-08-27 on s4 (16 cores, 123 GB RAM).

Companion to [`2026-08-27-architecture-review.md`](2026-08-27-architecture-review.md)
§4 (last bullet: "suite wall-clock is trending toward a publication gate") and
[`../../formalized-math-2026-08/05-throughput.md`](../../formalized-math-2026-08/05-throughput.md)
C1/C4. C1 recorded that sharding the library did **not** move `f`, and left the
open question: *if not the file lock, what is `f` actually spent on?* Part of the
answer is here — a merge costs a battery, and a battery under lane contention
costs ~35 minutes.

Decision recorded as [ADR-0606](../09-decisions/adr-0606-lane-work-yields-to-the-push-battery.md).

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

---

## Part 1 — Diagnosis

### Finding 1: the wrapper is a 5-slot semaphore, not a serializer

`CLAUDE.md` says "one cargo at a time on this host". This lane's brief said the
wrapper "already serialises heavy cargo behind an `flock`". **Both are out of
date, and the script says so in its own header.**

`scripts/cargo-serialized.sh` was changed (comment dated 2026-08-18) from a
mutex to a **counting semaphore** of `clamp(floor(RAM_GB / MEM_GB), 1, 6)` slots.
On this host that is `floor(123/24) = 5`, confirmed two independent ways — the
slot files `/var/tmp/axeyum-cargo.lock.1 .. .5` exist, and the script now prints
the number itself (`--slots` → `5`, a mode added by this lane precisely so the
figure stops being inferred).

The 2026-08-18 change was correct on its own terms: the hazard the lock was
built for is **memory**, which `MemoryMax`+`MemorySwapMax` bound per job, so
blocking on CPU was too strict. But the consequence is the thing being diagnosed:

**The semaphore bounds memory. Nothing bounded CPU.** `AXEYUM_CARGO_CPUS`
defaults unset — no `taskset`, no `-j` cap. Five jobs each spawn `nproc`-wide
rustc and `nproc`-wide test threads on a 16-core box.

### Finding 2: almost nothing that consumes this box was inside the lock

The battery is not one of the five slots. It takes a **different lock**:
`hooks/pre-push` `flock`s `$GATE_ROOT/.lock` (`/data0/axeyum/prepush/.lock`) and
then runs bare `cargo` invocations. The two lock populations are disjoint:

- `$GATE_ROOT/.lock` serializes **battery against battery** (correct, and
  deliberate — the hook's header explains why the gate worktree is shared).
- `/var/tmp/axeyum-cargo.lock.{1..5}` admits **five lane cargo jobs**.

Nothing serialized a battery against a lane.

**The first version of this finding was wrong, and the way it was wrong is the
point.** The census was `grep -c cargo-serialized <file>`, with
`scripts/local-ci.sh` → `1` as the "positive control". That 1 is a **comment**,
not a call. The control was satisfied by a file that does not invoke the wrapper
either, so it certified a query that was measuring the wrong thing — a pairing
that looked like the discipline CLAUDE.md prescribes while providing none of it.

The corrected census, over every tracked reference and separating callers from
prose:

| Caller | invokes the wrapper? |
|---|---|
| `hooks/pre-push` | **no** |
| `scripts/check.sh` | **no** |
| `justfile` (`check` recipe) | **no** |
| `scripts/local-ci.sh` | **no** — one comment only |
| `scripts/check-kernel-stack-envelope.sh` | yes |
| `scripts/tests/mutation_controls.py` | yes |
| ~70 fact `checker_command`s | yes |

So the admitted concurrency on this host was **not 5**. Two small scripts and a
set of ad-hoc fact checkers were inside the semaphore; every gate a lane is
actually told to run was outside it. The semaphore was well built, carefully
reasoned, documented in four places — and **unwired**. That is the measured
answer to "how are 4-5 lanes plus a battery contending at all".

### Finding 3: `nice` does not cross a session boundary — the fix that measured as nothing

The obvious remedy is priority rather than admission. Capping `-j` per slot
makes a lone job N times slower on an idle box; blocking lanes destroys the
parallelism that produces the work. `nice` costs nothing when the box is quiet
and only bites under oversubscription, which is exactly the condition.

So lane work was set to `nice 10` + `ionice -c 3`, and the battery to `nice 0`.
The mechanism verified directly — the wrapper's nice reaches even a job's
**forked grandchildren** (histogram: 7 processes at nice 10 with the default, 0
with `AXEYUM_CARGO_NICE=0`).

**And a controlled A/B measured it doing nothing: 1.85x vs 1.82x inflation,
speedup 1.01x**, with 27 competitors in *both* arms and the competitors' nice
values read back rather than assumed.

The cause is `/proc/sys/kernel/sched_autogroup_enabled = 1`. Autogrouping puts
each **session** in its own scheduling entity and divides CPU between entities;
`nice` then reorders tasks *within* a session and barely crosses the boundary.
Every lane is a different session, so a cross-lane `nice` is close to
decoration.

This is the third instance in this one wrapper of the same failure shape — a
property that is genuinely applied and has no effect. `MemoryMax` without
`MemorySwapMax` was the first; two more follow immediately below.

### Finding 4: `CPUWeight` works, and it was applied at the wrong cgroup level twice

What does cross a session boundary is the cgroup `cpu` controller, which **is**
delegated here (`cpu memory pids` in `user.slice`'s `subtree_control`), and the
wrapper already runs every job in a systemd scope.

Two attempts were **correctly applied and completely ineffective**, both
"verified" by reading `cpu.weight` back and seeing `10`:

```
scope only            user@1000.service/app.slice/run-*.scope                 weight 10
--slice=axeyum-lane   user@1000.service/axeyum.slice/axeyum-lane.slice/...    weight 10
an agent session      user@1000.service/tmux-spawn-*.scope                    weight 100
```

In each case the *sibling* of the session scope holding the battery is some
other cgroup at the default weight — `app.slice`, then `axeyum.slice` — so the
10 ordered lane jobs **against each other** and against nothing else. The second
failure is a systemd naming rule: a `-` in a slice name means hierarchy, so
`axeyum-lane.slice` is implicitly a child of `axeyum.slice`.

The working form puts lane work in **`axeyumlane.slice`** — no dash, a direct
child of `user@1000.service`, a genuine sibling of a session scope — with
`CPUWeight=10` set on the slice against systemd's default of 100.

`nice`/`ionice` are kept alongside it, not replaced: they still order work
within a session, `ionice -c 3` addresses I/O contention that a CPU weight does
not, and a host without cgroup `cpu` delegation has nothing else. Neither
mechanism is sufficient alone.

### Finding 5: a `Cargo.lock`-only push skipped the entire battery

The hook's early exit keys on `git diff --name-only <base> <tip> -- '*.rs' '*.toml'`.
**`Cargo.lock` is not `*.toml`.** Measured against a real commit:

```
git diff --name-only f8173a069~1 f8173a069                    -> 4 files
git diff --name-only f8173a069~1 f8173a069 -- '*.rs' '*.toml' -> 0
```

That commit changed `Cargo.lock` and three docs/ledger files, so the hook exited
at "docs/bench-results/scripts-only push — no cargo gate needed" while the
resolved dependency graph of the whole workspace moved. This is the
skip-too-much direction, which the file exists to prevent. Fixed by adding
`Cargo.lock` to the pathspec — a **widening**, which can only cause the battery
to run where it previously did not.

### Orphaned processes

**None found.** `ps -eo pid,ppid,etimes,pcpu,args --sort=-pcpu | awk '$2==1 && $4>50'`
was empty at the start of this work and again before each measurement. The
2026-08-21 incident (a task reported as exited running 85 h at 99.5% CPU) has
not recurred.

Two live observations worth recording instead:

- At one point the box read **load 38.59 on 16 cores** while another lane's
  `hooks/pre-push` was resident — worse than the 17.7 that prompted this work.
- **Load average is a poor instrument for "is the box busy now."** At a reading
  of 31.76 the box had **1 runnable process and 3 in D state**; the number is a
  lagging EWMA and includes uninterruptible sleep. An A/B run against that
  reading found no nice effect *because there was no contention to arbitrate*.
  Read `/proc/loadavg`'s runnable field or count `R`-state processes.

---

## Part 2 — Is the change-detection gating right?

### What it currently keys on

| Step | gated on |
|---|---|
| whole battery (early exit) | any `*.rs`, `*.toml` — **now also `Cargo.lock`** |
| `cargo check --workspace --all-targets`, `fmt` | always |
| corpus `:status` sweep | always |
| solver unit sweep (`--skip reconstruct::`) | always |
| 4 cheap integration suites | always |
| kernel suites (non-Lean) | `crates/axeyum-lean-kernel/**`, the two gate scripts, `Cargo.toml`, `Cargo.lock` |
| golden Lean module pins | `crates/axeyum-lean-kernel/src/**`, `tests/support/**` |
| evidence + route agreement | `crates/axeyum-solver/src/**`, `crates/axeyum-rewrite/src/**` |
| string front door (5 suites) | smtlib / string / regex / str paths |

### Can the always-on solver steps be skipped for a kernel-only push?

This is the tempting narrowing, because a kernel-only push is what every library
lane makes, and the corpus sweep plus solver unit sweep are 266 s + 269 s of the
contended battery. **The answer is no, and the reason is mechanical:**

```
crates/axeyum-solver/Cargo.toml:
  axeyum-lean-kernel = { path = "../axeyum-lean-kernel", optional = true }
```

`axeyum-solver` **depends on** `axeyum-lean-kernel`, and both steps run
`--features full`, which enables it. A change to `creal.rs` is therefore inside
the build closure of `cargo test -p axeyum-solver --features full` and can reach
solver behaviour through the reconstruction path. `--skip reconstruct::` is a
*runtime* filter on which tests execute, not a proof that the executed ones
never enter the kernel, and this repository's standard is not "probably
doesn't".

So the honest finding is that **the gating is already about as tight as it
soundly can be, and tightening it further is not where the win is.** The
diff-scoped steps that could be skipped for a kernel-only push (evidence, string
front door) already are. The correct move was to fix the contention and to
*widen* the one filter that was skipping too much.

The one narrowing that would be sound is mechanical rather than judged — gate
the solver steps on the **reverse-dependency closure** of the changed crates, so
a change confined to `axeyum-bench` or `axeyum-scenarios` (which nothing depends
on) skips them. That is a real but narrow win; it is not implemented here
because no measured push in the observed window had that shape.

---

## Part 3 — Fixes: implemented, and rejected with the argument

### Implemented

1. **`CPUWeight=10` on `axeyumlane.slice`** for all wrapper-admitted work, plus
   `nice 10` / `ionice -c 3`. `hooks/pre-push` sets `AXEYUM_CARGO_NICE=0` and
   runs unweighted. *Correctness: scheduling only. No step's inputs, outputs,
   ordering, or exit status change. A slow gate and a fast gate compute the same
   verdict.*
2. **`scripts/check.sh` takes one cargo slot for its whole run**
   (`cargo-serialized.sh --batch`), making the largest consumer on the box
   visible to the semaphore. *Correctness: the step list is byte-identical
   before and after (verified by diffing `AXEYUM_CHECK_LIST=1` output), so
   `check-aggregate-scope.sh` is unaffected and nothing is dropped.*
3. **Re-entrancy marker** (`AXEYUM_CARGO_SLOT_HELD`). Required by (2): without
   it a wrapped script calling a wrapped script blocks for `AXEYUM_CARGO_WAIT`
   (5,400 s default) once slots run out — silently, looking exactly like a slow
   gate.
4. **`--batch` applies no memory scope.** A batch is a supervisor, not a cargo
   job; `MemoryMax=24G` on `check.sh` would have the cgroup SIGKILL the
   aggregate gate at a threshold no individual step exceeded, reporting a
   failure that is not one. Nested cargo jobs each keep their own ceiling.
5. **Advisory, fail-open slot acquisition in `hooks/pre-push`.** *Correctness: a
   scheduling mechanism must never be able to block a correctness gate. If every
   slot is busy the battery proceeds and says so — a battery that waits for the
   box turns a slow gate into a stalled one.*
6. **`Cargo.lock` added to the change filter** (Finding 5). Strictly widening.
7. **`--slots`** prints the host's admitted concurrency, so the number is read
   rather than inferred from prose that has been wrong since 2026-08-18.

### Rejected

- **A shared `CARGO_TARGET_DIR` across lane worktrees.** This is the largest
  apparent win (246 worktrees, ~363 GB, each paying a cold workspace build) and
  it is **unsound here**, with an incident to cite. Cargo bakes absolute paths
  into `CARGO_MANIFEST_DIR`, so two worktrees at different paths sharing one
  target dir let cargo consider an artifact fresh for both; the main checkout
  then reuses a binary whose manifest dir no longer exists. Observed 2026-08-01
  as `read_dir(/tmp/axeyum-prepush.ll4jFr/...): No such file or directory` on a
  perfectly good tree, and as `cargo test -p <pkg> --lib` passing while
  `cargo test --workspace --lib` failed. `hooks/pre-push` already keeps a
  dedicated target dir for exactly this reason. Cargo also locks the build
  directory, so sharing would serialize builds host-wide as a side effect nobody
  chose. **`sccache` is the right shape of this idea** — it caches compilation
  units rather than a directory tree, so the absolute-path hazard does not apply
  the same way — but it needs its own evaluation against `env!`/`include_str!`
  and is not something to switch on in the same change as a scheduling fix.
- **Capping `-j` or `--test-threads` per slot.** Bounds CPU, but a lone job on
  an idle box becomes N times slower — it taxes the common case to fix the
  contended one. Reducing test parallelism is the safe *direction* for
  correctness, but the cost is paid every run.
- **Hard admission control (the battery reserves all slots).** Turns a slow gate
  into one that can be starved indefinitely by a stream of lane jobs, and
  couples push latency to lane scheduling. The advisory form gets the memory
  accounting without the failure mode.
- **Dropping or narrowing any step.** No step was removed. Two candidate
  narrowings were examined and rejected on the dependency evidence in Part 2.

---

## Part 4 — Before/after under comparable load

### How the load was generated

`scripts/measure-gate-admission.sh`. Three arms with identical fixed work:
`quiet` (subject alone), `before` (subject vs unweighted lane load), `after`
(subject vs `nice 10` + `CPUWeight=10` lane load). Load is `JOBS` wrapper-
admitted jobs each forking `PROCS` busy processes; the subject is a fixed-work
task forked `SUBJ` ways to model a `cargo test` binary's width.

An end-to-end battery A/B was **not** run, deliberately: a contended battery
costs ~35 minutes, both arms would need the same offered load (which a shared
box with live lanes cannot provide), and `hooks/pre-push` only runs on a push —
starting one would perturb the measurement and block every other lane behind the
gate flock. The numbers below are the **scheduling mechanism** under a
controlled load, not an end-to-end battery figure.

The run is **reduced** (3 jobs x 8 processes rather than 5 x 16) because another
lane's push battery was resident throughout this lane's window, and
oversubscribing 16 cores against somebody else's gate is precisely the harm this
change exists to remove. The script now refuses to run at all while a battery is
live (`exit 75`); the numbers below were taken with an explicit override at
reduced scale.

### Result

Subject width 16, matching a `cargo test` binary; 27 competitors in **both**
arms, asserted rather than assumed:

```
QUIET   competitors=0     6.1s
BEFORE  competitors=27   11.5s   (unweighted)      1.89x inflation
AFTER   competitors=27    6.8s   (nice 10 + CPUWeight 10)   1.11x inflation

arms: before=27 competitors, after=27  -> COMPARABLE
gate speedup under the SAME offered load: 1.69x
```

Residual inflation falls from **89% to 11%**. Subject width matters and is the
mechanism in one number: at width 8 the same change measured 1.12x, at width 16
it measures 1.69x — a *wide* consumer is what gets starved, which is exactly
what a battery step is.

### Three wrong answers this measurement produced first

Recorded because each looked plausible and each is now guarded in the script:

1. **1.11x inflation where the gate sees 4-7x.** The burners used Python
   *threads*; the GIL is held through a 32-byte `sha256`, so each "4-thread"
   burner pinned one core. Everything forks processes now.
2. **Arms compared at 14.3 vs 31.6 load.** `kill` on the wrapper PID does not
   reach the job — the wrapper `exec`s into `flock` → `nice` → `ionice` →
   `systemd-run --scope`, and the process inside the scope survives. Arm one's
   burners were still at 97% CPU during arm two. The script now reaps by
   token-resolved PID, waits for the count to return to baseline, and **prints
   `NOT COMPARABLE` and exits nonzero** rather than reporting a ratio.
3. **"The wrapper is not applying nice."** `ps -C python3` **did not filter** on
   this host — it printed every process — so the reported competitor nice was
   `khugepaged`'s 19. An instrument that answers a question you did not ask is
   indistinguishable from a strong negative result.

## Controls

`scripts/tests/test-gate-admission-controls.sh` — 15 assertions, each paired
with the input that makes it fail. The two that carry the suite:

- **A real deadlock probe.** Every slot is held; the re-entrant job must
  complete *and* the non-re-entrant one must report 75. Without the second half
  the first passes on any host where slots were never contended.
- **The cgroup LEVEL, not the value.** A `cpu.weight == 10` assertion passes on
  *both* broken versions from Finding 4. The suite asserts that the lane slice
  is a sibling of an ordinary session scope.

`scripts/tests/mutate-gate-admission.sh` — baseline-first, then one mutant per
guard; each kills exactly its own case. It mutates a four-file **scratch copy**,
never the checkout: these are shell scripts read fresh on every invocation, so
an in-place mutant is worse than the Rust-constant case CLAUDE.md records — any
lane running a gate during the window would execute it.

Both are registered in `scripts/check.sh` and the `justfile`
(`check-control-registration.sh`: `orphans=1` → `orphans=0`).
