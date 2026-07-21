# SMT-COMP runner E1b integration audit

Status: schema v2 prototype landed; active runner unchanged
Date: 2026-07-21

## Outcome

The E0/v1 resume contract was sufficient to test durable file installation,
but insufficient to represent a real solver process without losing or guessing
evidence. It is therefore preserved as the historical first prototype and
superseded—before production use—by
[`smtcomp-resumable-run-contract-v2.json`](smtcomp-resumable-run-contract-v2.json).

V2 has **18 invariants and 28 executable scenarios**: five accepted controls
and 23 rejected mutations. Interrupted/resumed lifecycle evidence differs from
an uninterrupted run, as it should, while the canonical scoring projection is
byte-identical. No corpus or solver was run, and `compete.py`/`runner.py` remain
unchanged.

## Source audit: what the active runner loses

### 1. A timeout response is discarded

`runner.py` deliberately sets `reported = None` when its watchdog fires, even
if captured stdout already contains `sat` or `unsat`. `compete.py` suppresses it
again with `run.reported if not run.timed_out else None`.

That conflicts with the official
[SMT-COMP 2026 rules](https://smt-comp.github.io/2026/rules.pdf), section 7.1.2,
which says a response is considered even if the process terminates abnormally
or exceeds the limit. The same section warns solvers not to emit accidental
`sat`/`unsat` text for precisely that reason.

V2 therefore separates:

- `observed_status`: what the pinned output parser found;
- `reported_status`: what the registered scoring policy admits; and
- `verdict_admission`: `admitted` or `no-verdict`.

The v2 policy is named
`smtcomp-2026-response-even-after-timeout`. Scenario F26 proves a `sat`
observed before a forced wall timeout remains admitted while the typed timeout
state is preserved. This is a contract test, not a retroactive correction to
the committed 228-file result. The old raw artifact lacks the output/termination
evidence needed to determine whether either no-answer row was affected.

### 2. Any non-timeout signal is guessed to be memory exhaustion

`runner.py` currently computes:

```text
mem_exceeded = exit_code is not None and exit_code < 0 and not timed_out
```

On Python/POSIX, a negative return code identifies a signal. It does not
identify why that signal occurred. `SIGKILL` can come from an operator, parent,
cgroup, OOM killer, scheduler, or another source. The field is not currently
serialized by `compete.py`, but it cannot become publication evidence in that
form.

V2 replaces loose booleans with a checked tagged state:

- `completed`;
- `wall-timeout`;
- evidenced `resource-limit` (`cpu` or `memory`);
- unclassified `signal`;
- `nonzero-exit`; or
- `runner-error`.

Exit code, signal, and resource-limit kind have legal combinations. Memory is
named only when the enforcement layer supplies that evidence. F24 rejects an
illegal `completed + exit 7` combination.

### 3. Raw scoring JSON drops process evidence

`RawResult` and `raw_to_json` retain solver/path/logic/status and wall/CPU time,
but omit:

- exact benchmark bytes and normalized ID;
- solver binary/configuration identity;
- attempt and shard lifecycle identity;
- exit code, signal, termination class, and resource-limit source;
- peak RSS;
- the competition-bounded wall-time value separately from local watchdog/
  kill/reap elapsed time;
- stdout/stderr bytes or hashes; and
- the distinction between observed and scoring-admitted verdicts.

Those omissions make the current raw JSON suitable as a small scoring input,
not as the authoritative durable execution record. V2 keeps a richer immutable
record and defines a separate canonical scoring projection. The compatibility
raw JSON must be exported only from a fully validated completed bundle.

The active runner's monotonic wall duration includes timeout handling and may
exceed `T`, while the rules define `aw` in `[0,T]`. V2 therefore retains both a
limit-bounded `wall_time_ns` for scoring and `runner_elapsed_ns` for harness
diagnosis; a wall-timeout record must clamp the former exactly to the registered
limit and may exceed it only in the latter.

### 4. V1 could not explain which retry produced a record

V1 attached attempts to a shard but not to individual results. A terminal had
one result-set hash but no checkable partition between results newly installed
by that attempt and valid prior records skipped on resume.

V2 adds `attempt_id` to each immutable result. Every terminal lists disjoint
`new_result_keys` and `skipped_result_keys`; their union is the durable set, and
the durable set plus missing keys is the exact assignment. Closed-attempt
attribution is checked against the records. Terminal-less attempts remain
possible and must be named in final completion. F23 and F27 mutation-test both
sides of this relation.

### 5. Multi-solver execution is not one resumable run identity

`compete.py` accepts multiple `--solver` arguments, while v1 used singular
solver binary/command fields and keyed records only by a display name. Two
configurations can share a display name or change a command behind it.

V2 explicitly scopes one run identity to one solver configuration. Its result
key binds normalized benchmark ID, exact input SHA-256, and
`solver_config_sha256`. Multi-solver comparison is central composition of
separate complete runs. E1b must reject more than one solver in resumable mode;
legacy small-run mode can remain unchanged.

### 6. Output parsing is evidence, not just a derived token

The active parser selects the last `sat|unsat|unknown` token anywhere in
stdout. The competition rules warn about accidental tokens. V2 does not choose
a new parser yet; it binds the output-capture and verdict policies and retains
stdout/stderr SHA-256 plus byte counts. E1b must store content-addressed output
sidecars and verify them before export. A parser change then becomes a new
policy/run identity instead of silently changing old evidence.

## V2 contract changes

The generated
[v2 failure/recovery matrix](generated/smtcomp-resumable-run-contract.md)
adds four invariants and five scenarios beyond v1:

| Addition | Reason |
|---|---|
| Observed vs admitted response | Preserve late/abnormal responses under the registered competition policy |
| Typed termination | Prevent signal-to-OOM guessing and illegal state combinations |
| Bounded scoring time vs runner elapsed | Keep watchdog kill/reap overhead out of the competition time field without deleting it |
| Per-result attempt ID + terminal partitions | Make resume attribution and hit/new counts checkable |
| Content-addressed stdout/stderr | Make verdict derivation independently replayable |
| Source/toolchain/resource/output/verdict policy hashes | Make a retry's measurement identity complete |
| One solver configuration per run | Avoid ambiguous multi-solver identity and result-key collisions |

The canonical scoring projection deliberately omits attempt ID, record hash,
and output-sidecar identity. Those facts remain in the evidence bundle but do
not make a recovered deterministic result score differently from the same
uninterrupted measurement.

## E1b integration seams

Production integration should be narrow and opt-in:

1. Add `--run-manifest` plus one `--run-dir` mode to `compete.py`; require
   exactly one solver and an explicit file list.
2. Validate the precomputed manifest, selected-list hash, each normalized
   benchmark ID/hash, solver executable/configuration, runner source, and
   environment before any solver starts.
3. Acquire one shard lease; install a launch manifest before the first result.
4. Execute only missing valid keys. Capture raw stdout/stderr even on timeout,
   classify termination without guessing, store sidecars, then atomically
   install the v2 result.
5. Write a best-effort terminal. Write completion last only after strict
   validation of the full assigned set.
6. Export legacy raw scoring JSON from the completed canonical projection; do
   not teach `inventory.py` to ingest partial v2 directories.
7. Change `raw_from_json` duplicate assignment into a hard conflict in a
   separately tested compatibility patch.

## Gates before touching the large candidate

- A deterministic fake solver emits a verdict then hangs; the v2 record retains
  and admits the verdict while recording wall timeout.
- Separate fake solvers exit nonzero, die by operator signal, and receive an
  evidenced resource-limit termination; none is mislabeled.
- Output-sidecar byte mutation fails before scoring export.
- Kill before solver start, during solver execution, and at the four E1a
  persistence phases; resume yields exact scoring projection and honest
  attempt partitions.
- A second process targeting the same shard fails its lease preflight.
- Legacy non-resumable mode produces byte-identical output on the existing
  synthetic pipeline tests.

Only after these E1b gates should E2 add actual aggregate enforcement and E3
exercise remote loss/recovery. The full candidate still waits for E1b-E3 and
the independent selection-provenance gates.
