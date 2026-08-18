# Notes: local-ci-run

Detail behind [`../status/102-local-ci-run.md`](../status/102-local-ci-run.md).

## The record

[`artifacts/local-ci-runs/a6ee37c6a-s4.json`](../../../artifacts/local-ci-runs/a6ee37c6a-s4.json)
— the first completed run of `scripts/local-ci.sh` in this repository's history.

| verdict | tests | seconds | step |
|---|---|---|---|
| pass | — | 3 | `cargo fmt --all --check` |
| pass | — | 1 | `rustup run stable cargo clippy --workspace --all-targets --all-features -- -D warnings` |
| pass | — | 0 | `rustup run 1.88.0 cargo check --workspace` |
| **FAIL** | −1 | **6386** | `cargo nextest run --profile local --workspace --all-features --no-fail-fast` |
| pass | 179 | 11 | `cargo test --workspace --all-features --doc` |

`7511 tests run: 7507 passed (85 slow), 4 failed, 32 skipped`, rc=100, total
6401 s.

**The clippy and MSRV seconds are warm-cache figures and are not those steps'
cost.** An earlier attempt at the same SHA had already built them, and was
killed at 59 m 59.9 s by the agent harness's background-task cap — not by the
box (39.4 G peak against a 64 G ceiling), with 6498 of 7511 tests done and **no
record written**, because the recorder only writes at the end. Cold, that
attempt spent ~11 m in clippy + MSRV before testing began. So a cold run of this
gate is roughly **two hours**, against `hooks/pre-push`'s 722–1176 s.

Both runs were driven from a detached worktree at exactly `a6ee37c6a`, never the
shared checkout, which carried other lanes' uncommitted work throughout —
including three untracked `crates/axeyum-solver/examples/zz_*_probe.rs` that
`--all-targets --all-features` compiles.

## What it found in committed code

Four failures, all `axeyum-solver` integration suites, all deterministic (each
failed all three nextest retries in under a second), all one cause:

    quant_affine_growth_lean::repair_const_nterm_reconstructs_and_routes
    quant_counterexample_cover::small_cover_generated_module_is_byte_stable
    quant_eq_partition_lean::sdlx_reconstructs_genuine_nested_quantifiers_and_routes
    quant_residue_lean::committed_clock_rows_reconstruct_and_route

Each pins `(source.len(), fnv1a)` of a reconstructed Lean module, and each was
off by the **same +1 640 bytes on four unrelated modules** — the signature of a
fixed header addition, not of a proof change:

| bytes | commit | what |
|---|---|---|
| +863 | `b760fd6ae` | `unsafe axiom lcErased/lcAny/lcVoid` — without them 21 of 77 crosscheck families died under Lean 4.34.0-rc1 |
| +777 | `46724faec` | `set_option maxRecDepth 65536` — a scope-shared `let` chain is nested syntax; 2 897 bindings in one lemma blow Lean 4.30.0's default of 512 |

Both producers are correct and both re-pinned only the golden module that sits
in a gate (`diophantine_lean_reconstruct` / `farkas_over_the_integers`). This is
the **third** recurrence: `6389e0194` (2026-08-15) diagnosed exactly this for
three of these same four suites, re-pinned them, and registered them with
`scripts/check-lean-gate.sh` — which runs real Lean over the modules but is not
what anyone runs before merging.

The pins are the symptom. The cause is that **no pre-merge gate runs these
suites**: `cargo test --lib` skips integration targets by construction, and the
pre-push battery names its suites explicitly. The full workspace sweep is the
only thing that covers them, and that is local-ci.

Re-pinned at cause in `31442bd5d`; measured and verified green at `51432808f`
in a detached worktree (4 + 7 + 6 + 3 = 20 tests, 0 failed).

## Two defects in the gate itself

**It gated the working tree** (`a2841965e`). `hooks/pre-push` already checks the
pushed SHA out into a stable per-lane detached worktree for precisely this
reason; local-ci now does the same, `--no-worktree` opting out. One shared root
under `flock`, exit 75 on lock timeout so a queued gate is never read as a
failure. Controls: the gate tree must equal the commit **after a reuse** (a
first call tests a fresh tree, where `--force` and `clean -xdf` are both no-ops
and every assertion holds vacuously), and the sibling lane's WIP must survive —
a gate that "isolated" by stashing passes the first three and fails that one.
Dropping `--force` kills exactly one test; dropping `clean -xdf` kills one other.

**The zero-test guard could not fire on the step it exists for** (`e069afa03`).
`count_tests` matched nextest's summary with a pattern anchored at `^`, and
nextest indents that line by five spaces:

    $ sed -n 7907p run.log | cat -A
         Summary [6384.534s] 7511 tests run: 7507 passed (85 slow), 4 failed, 32 skipped$

So it never matched, and the recorder wrote `"tests": -1` — the *no count*
value — for a step that ran 7511 tests. A `cargo nextest` that compiled an empty
suite and exited 0 would have been recorded `pass`. That is this repository's
signature defect reproduced inside the thing built to detect it, and it took
running the gate once to see it. The control missed it because its fixture was
typed from nextest's documentation rather than captured from nextest, and so was
flush-left; every nextest fixture is now a captured line, including the failing
summary from this run (a different shape: `(85 slow)`, `4 failed`). A step that
claims to run tests and prints a count this script cannot parse is now
`unreadable` (89), not `pass`.

## Cost, and why more hardware will not help

From the run's own per-test timings (7507 timed tests):

- sum of test time **15 754 s**, wall **6385 s** → **2.47x achieved parallelism
  on 16 cores**
- longest single test **630.7 s** (`real_lean_wire_differential
  our_kernel_admits_nothing_the_real_lean_kernel_refuses`) — an absolute floor
  for any scheduler
- five differential-fuzz binaries holding **one test each** account for 2 537 s,
  **40 % of the wall**

### `cargo test` vs `cargo nextest`: measured, and the model was wrong

I first modelled `cargo test` from the sweep's per-test timings as *binaries
sequential, tests within a binary parallel over 16 threads*, got 6569 s against
nextest's 6385 s, and concluded it was a wash. **That model is invalid and the
conclusion was wrong**, because its inputs were per-test times measured *under
nextest*, which is exactly the quantity in dispute.

Measured instead, same tree, same warm target dir, same host, on the heaviest
binary in the workspace (`axeyum-lean-kernel --lib --all-features`, 372 tests):

| runner | test time |
|---|---|
| `cargo test` | **114.42 s** |
| `cargo nextest run --profile local` | **398.995 s** |

**nextest is 3.5x slower here** — far worse than the 25 % penalty measured on the
`--lib` subset. The likely mechanism is nextest's process-per-test isolation
destroying in-process reuse that `cargo test` gets for free within one binary:
this crate's suite is built around a prelude cache, and
`prelude_cache::creal_reuse_matches_fresh_build` alone took 215 s under nextest.
This binary contributed 3751 s of the sweep's 15 754 test-seconds.

That does **not** generalise to the whole sweep — the five single-test
differential-fuzz binaries (2 537 s, 40 % of the wall) cannot be affected by the
runner, and the floor of 630.7 s stands either way. But it does mean local-ci's
choice of nextest is plausibly costing a large fraction of an hour per run, and
**nobody should put this gate on a timer before someone measures
`cargo test --workspace --all-features` end to end.** I did not; it is another
~2 h and it belongs to whoever owns the schedule.

Adding cores remains the wrong lever regardless: 2.47x achieved parallelism on
16, with the floor set by one 630 s test.

Incidentally, `scripts/cargo-serialized.sh`'s flock is heavily contended — the
nextest half of this comparison waited **~19 minutes** for the lock before it
started, which is why two 10-minute foreground attempts at it timed out looking
like slowness. `local-ci.sh` does not take that lock, so the gate and the lanes
compete rather than queue.

## Should it run on a schedule

**Yes, and the timer is the easy half.** It cannot be a per-push gate at ~2 h
cold, and it must not be per-lane-on-demand, because that is what it already was
and the answer was zero runs in its lifetime.

s5 and s7 **measured today cannot run it**, which is the first thing any
schedule has to fix:

| host | stable | 1.88.0 | nextest | z3 | checkout |
|---|---|---|---|---|---|
| s4 | yes | yes | yes | 4.13.3 | current |
| s5 | **no** | **no** | **no** | 4.13.3 | 342 commits behind, dirty |
| s7 | 1.97.1 | **no** | **no** | 4.13.3 | 422 commits behind |

`provision-fleet-host.sh` installs all three — but installing them is not the
same as having run it there, and it has not been. Neither host has `cvc5` at
all, and the preflight does not check for it even though the script's own header
names "~32 z3/cvc5 differential-fuzz binaries".

**How the result gets seen.** A timer writing a file nobody opens is the defect
wearing a hat. Make the record's *absence* fail a gate people already run:

1. The timer (user systemd timer on s5, s7 as second slot) fetches `origin/main`
   and runs `scripts/local-ci.sh --record`. Safe to do on a shared checkout now
   that the gate materialises the commit itself. It commits and pushes only
   `artifacts/local-ci-runs/`.
2. `scripts/check-local-ci-freshness.sh`, wired as a `step` in **both**
   `scripts/check.sh` and the `justfile` (one without the other is exactly the
   gate divergence `check-aggregate-scope.sh` exists to pin), fails when:
   - no record's `sha` is an ancestor of `HEAD` within the freshness window, or
   - the newest such record's `verdict` is not `PASS`, or
   - any step in it is `vacuous` or `unreadable`, or its `tests` is 0/−1 on a
     step that claims to run tests.

That last clause is the point. A checker that cannot fail is worse than none, so
the freshness gate must reject a *green* record that proves nothing, not merely
a missing one. Bootstrapping order matters: land a **passing** record first,
then the gate, or the gate is red on arrival and everyone learns to skip it.

Not landed here — it is a separate change with its own controls, and it should
not go in before a green record exists to satisfy it.

## Claims in the brief that were wrong

- *"run it in the FOREGROUND and wait rather than polling a background job."*
  Not possible as stated: the harness caps a foreground Bash call at 10 minutes
  and killed a background one at exactly 60 minutes, mid-run, losing 6498 tests
  of work. The gate needs `setsid` to survive its own runner.
- *"s5 and s7 are idle 16-core hosts with z3; `provision-fleet-host.sh` now
  installs `cargo-nextest`, stable and 1.88.0."* True of the script, false of
  the hosts — measured above. Their checkouts are also 342 and 422 commits
  behind on a stale session branch.
- *"`--record` marks a step that exited 0 having run ZERO tests as `vacuous`."*
  True in principle and unreachable in practice on the nextest step, for the
  reason above.
- The contention worry was real but not decisive: the gate does not go through
  `scripts/cargo-serialized.sh`, and the first attempt ran at 3.4x parallelism
  against other lanes' builds. It shows up in the 106 min wall, but the run's
  own parallelism ceiling of 2.47x is a property of the suite, not of the
  neighbours.
