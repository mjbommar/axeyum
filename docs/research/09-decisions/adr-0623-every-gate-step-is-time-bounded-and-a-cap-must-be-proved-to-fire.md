# ADR-0623: every gate step is time-bounded, and a cap must be proved to fire

Status: accepted
Date: 2026-08-30
Lane: `gate-termination`
Index-summary: `scripts/check.sh` had zero timeout-guarded steps and one hung run cost nine hours; every step now carries a generous per-step cap with a third outcome (UNCHECKED), and `scripts/check-gate-step-timeout.sh` proves the cap fires — because `check-fast.sh` shipped a cap for weeks that could not.

## Context

`scripts/check.sh` is the aggregate gate. Measured 2026-08-30 it declared 401
steps and **zero** of them were timeout-guarded, so one hung step hung the
entire gate forever.

That is not a hypothetical. A live run started at 16:43 was still alive at
02:51 the following morning — **over nine hours**, 0% CPU at every level of the
process tree, reparented to init, its log last written at 17:33 and stopped mid
`=== facts-replay ===`. Nothing timed it out and nothing noticed; it was found
by hand and killed by PID.

One lost run is the cheap part. The expensive part is already measured
elsewhere in this repository: **gates rot because nobody ever completes the
aggregate gate.** A census the same day found 64 failing steps, 32 of them
pre-existing, and `scripts/check-local-ci-freshness.sh` — the gate whose entire
job is to notice the battery has gone stale — sat RED for 265 hours across
3,974 commits, because its only caller was the battery that had gone stale. A
gate people cannot finish is a gate people stop running.

The step that hung is `facts-replay`, which executes `checker_command` strings
taken from the fact ledger. Those are arbitrary strings in 2,220 JSON files. As
far as termination is concerned they are **untrusted input**, and any one of
them could take the aggregate gate down.

## Decision

**1. Every step of `scripts/check.sh` runs under a per-step time cap**, and a
step that exceeds it is a THIRD OUTCOME — `TIMED OUT`, meaning UNCHECKED. It is
counted separately from a failure, named on stderr, and it sets the gate's
failure flag. `scripts/check-fast.sh` already established the
`ok` / `FAILED` / `DEFERRED` contract and this follows it rather than inventing
a second vocabulary. **A timed-out step can never read as a pass**, and the
"all N gates passed" banner cannot print when one exists.

**2. The caps are generous, per-shape, and anchored to measurements**, because
a cap that fires on healthy steps is worse than no cap: a gate that reports
spurious timeouts is one people learn to ignore, which is the failure being
fixed. Each number is cited in `scripts/check.sh` beside the constant.

| cap | value | what it is anchored to |
| --- | --- | --- |
| default (non-cargo) | 30 min | the entire non-cargo half — all 355 such steps — extrapolates to ~45 min, so no single cheap step may take two thirds of what all of them together take |
| anything that builds | 2 h | worst measured cargo step in this file is `axiom-freedom-*` at 509 s release; contention on this box is documented at 4–7x, projecting ~3,560 s |
| `test` (workspace tests) | 4 h | never timed; nearest recorded artifact is the 6,588 s workspace nextest sweep, the highest-confidence single-step number in the repository |
| `facts-replay` | 3 h | 747.7 s under contention against a ledger a fifth of today's size |

**3. A cap needs `--kill-after` AND an explicit process-group kill.** Both
halves are load-bearing and neither is obvious.

`timeout N` sends SIGTERM at the deadline and then **waits forever**, while
still exiting 124 — so a caller testing for 124 gets a correct-looking "timed
out" verdict after an arbitrarily long wait. The status is right and the bound
is fiction:

    trap '' TERM; sleep 25
    timeout 2      ./that.sh   ->  exit 124 after 25s
    timeout -k 1 2 ./that.sh   ->  exit 137 after  3s

`--kill-after` is still not enough, because `timeout` signals the child it
monitors rather than the tree beneath it, and `trap '' TERM` sets SIG_IGN which
is **inherited across exec**. Measured at a 2s cap with an uncapped positive
control proving the grandchild was there to be counted, in two fixture shapes:

|  | sleeper last | sleeper backgrounded |
| --- | --- | --- |
| uncapped (control) | 1 | 1 |
| `timeout -k` | 1 | 1 |
| `timeout -k`, group kill omitted | 1 | 1 |
| `timeout -k` + `kill -KILL -$pgid` | **0** | **0** |

The surviving grandchild is not untidiness; it is the nine-hour bug. An
orphaned `cargo` holds the build-directory lock, whose wait is unbounded, so
every later cargo step blocks on a process nothing will reap.

**4. The ledger sweep carries its own bounds, at three scales.** Per-row
(the process tree is killed, not just the direct child), a capped build probe,
and a whole-sweep deadline of 9,900 s — deliberately just under `check.sh`'s
10,800 s cap for that step, so the informative stop wins the race and the
script names the facts it never reached instead of being killed mid-fact.
Unreached facts are a fourth outcome, `NOT RUN`, counted and named and non-zero.

**5. A cap must be PROVED to fire.** `scripts/check-gate-step-timeout.sh` is
registered in both aggregate gates. It is the time analogue of
`scripts/cargo-serialized.sh --self-check`, which exists because `MemoryMax`
without `MemorySwapMax` is a ceiling that never bites.

## Consequences

The gate terminates. The bound is per-step rather than global, deliberately: a
global wall-clock deadline would truncate a legitimately long full gate and
report dozens of spurious timeouts, which is the failure mode above. The
theoretical worst case is therefore large (401 steps × their caps) and the
realistic one is not, because the mechanism that produced nine hours —
one orphan blocking every later cargo step — is what the group kill removes.

### What this decision is worth is exactly what the probe measures

`scripts/check-fast.sh` had a per-step cap **from the day it was written** and
it did not bind: line 127 was `timeout "$budget" bash -c "$cmd"` with no `-k`.
A run of it was found stuck **23 minutes on a step with a 3-second budget**,
its child shell alive and its grandchildren `<defunct>` — wedged inside its own
`trap ... EXIT` cleanup. The tool whose entire purpose was per-step capping had
a cap that could not fire, and nothing said so.

So the probe is not a formality attached to the fix; it is the part that
distinguishes this from what was already there. It is written to fail:

- **Case 2 is the self-check** — a step that ignores SIGTERM, under the real
  gate's real cap. It measured 120 s before the fix and 3 s after. It also
  tests the orphan reaper for free, because the gate is read through a command
  substitution and a command substitution returns only when every descendant
  has closed the pipe.
- **Cases 4 and 5 are the other half of the contract.** A step exiting 124 in
  no time is FAILED, not TIMED OUT (124 is `timeout`'s status but also an
  ordinary exit code, and a broken step must not be able to soften its own
  classification by choosing one); and a slow-but-finishing step is not
  misclassified.
- **Case 8 runs the real ledger sweep** against a synthetic one-fact ledger
  whose `checker_command` hangs.

**The probe caught two defects in the fix it was written to verify**, which is
the argument for it. Case 2 failed on its first run against a version that had
`--kill-after` — that is how the group-kill requirement was discovered at all.
Case 8 failed against the first Python reaper, which sent SIGTERM to the group,
waited on the direct child, and broke out of the loop when that child was
reaped — so SIGKILL was never sent:

    /bin/sh -c ./bad.sh   did NOT exec; it forked `bash ./bad.sh`
    killpg(SIGTERM)       killed the sh, not the TERM-ignoring bash
    p.wait() succeeded    -> break -> no SIGKILL
    FINAL survivors = 1

The direct child dying says nothing about the rest of the group, which is the
entire population the reaper exists for.

### Mutation results, as measured

Seven mutants, six killed:

| mutant | killed |
| --- | --- |
| drop `--kill-after` (check.sh) | case 2 |
| drop the `elapsed >= cap` conjunct | case 4, both assertions |
| drop `fail=1` on the timeout path | case 3, exit status and banner |
| drop the tool-presence refusal | case 7, both assertions |
| drop the `pgid == pid` safety guard | **SURVIVED** |
| drop the group kill | case 2 |
| drop `--kill-after` (check-fast.sh) | case 6 |

The survivor is reported rather than excused. It guards against aiming a
SIGKILL at an unrelated process group, and its precondition — `timeout` failing
to make its child a group leader — is not reproducible on this host, so no case
can reach it. It stays.

Two process notes worth more than the table. A `setsid` wrapper was in the
first version of the fix and the sweep **measured it at zero effect**: dropping
it killed nothing, because `timeout` already calls `setpgid(0,0)` on itself
(pid=2198873 pgid=2198873 with no `setsid` anywhere). It was removed, and one
host dependency with it. And the first `fail=1` mutant also survived — because
the `sed` appended a no-op instead of deleting the line below. **A mutation
that does not apply is indistinguishable from a guard nobody tests**, so the
harness now compares checksums and refuses to report a result for a mutation
that changed nothing.

### Other unbounded waits, surveyed

- `scripts/cargo-serialized.sh` — bounded, `flock --timeout 5400
  --conflict-exit-code 75`. But `check.sh` execs itself through it, so the gate
  can wait up to 90 minutes for the slot *before any step timing begins*.
- `scripts/local-ci.sh` — `flock -w 10800` (3 h). Bounded, not in `check.sh`.
- `read -r … < <(…)` process substitutions in
  `scripts/check-autogenesis-apply-search.sh` (3 sites) and
  `scripts/check-autogenesis-induction-search.sh` (1) — the `read` blocks for as
  long as the substituted subshell runs, and those subshells invoke cargo. Now
  bounded from outside by the step cap; individually still unbounded.
- **No network fetch anywhere in the gate.** `check-links.sh` explicitly skips
  `http://`/`https://`/`mailto:` and `check-adr-remote-collisions.py` performs
  no fetch, both verified by reading rather than inferred from a green run.
- Steps no longer inherit stdin: every capped step gets `</dev/null`, so a step
  that read a terminal cannot block, and cannot be stopped by SIGTTIN in the new
  process group and then reported as a timeout the cap caused itself.

### The partial-artifact question

SIGKILL can leave a partial file. Surveyed for the case that matters — a capped
step writing a file a later step reads — the generated artifacts in this gate
(`PLAN.md`, the ADR index, the axiom ledger, the trackers) are written by
generator steps that are themselves `--check`ed by the same gate, so a truncated
write is caught as a freshness mismatch rather than consumed silently. The
ledger sweep writes only its per-lane build log. This is a survey, not a proof;
a step that begins writing an input for a later step should carry a
write-to-temp-then-rename, and the risk is stated here rather than left implicit.

## Alternatives considered

**A global wall-clock deadline instead of per-step caps.** Rejected as the
default: a legitimately long gate would be truncated and dozens of healthy steps
reported as timeouts, which teaches readers to ignore the gate — the failure
this ADR exists to fix. The ledger sweep gets one because its worst case
(993,952 s of summed per-row budgets) is pathological rather than long.

**Copying `check-fast.sh`'s 3-second budget.** Rejected explicitly. Its cap is
tuned for a tier-0 sweep; applied to the full gate it would fire on almost every
cargo step.

**Leaving `check-fast.sh` alone.** Rejected once its cap was measured not to
bind. Fixing the full gate while the tier-0 gate kept a decorative cap would
have left the more frequently run of the two unbounded.
