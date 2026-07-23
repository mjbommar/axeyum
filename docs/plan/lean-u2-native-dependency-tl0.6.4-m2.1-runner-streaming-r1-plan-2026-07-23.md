# Lean U2 TL0.6.4 M2.1 R1 plan — live stream ceilings and launch records

Status: **preregistered correction; attempt 001 remains unconsumed**

Date: 2026-07-23

Parent:
[M2.1 pre-execution result](lean-u2-native-dependency-tl0.6.4-m2.1-pre-execution-2026-07-23.md).

## 1. Trigger

The post-publication runner audit found two implementation gaps before any
M2.1 process ran:

1. `subprocess.communicate` buffered complete stdout/stderr and checked their
   registered byte ceilings only after child termination. This would reject an
   oversized result but would not enforce the promised live output bound.
2. `subprocess.Popen` or pre-exec setup failure could escape before a sealed
   typed process record was written, leaving an incomplete root without the
   exact launch failure required by the execution contract.

The evidence root is absent. Observed processes, header edges, resolutions,
native outcomes, pairs, and parity credit remain zero. The prior authorization
digest is revoked because it binds runner bytes that will change.

## 2. Authorized implementation correction

Change only the M2.1 runner and its focused tests:

- connect child stdin/stdout/stderr to retained evidence files rather than
  buffering streams in the parent;
- poll the child sequentially and kill its process group immediately on the
  registered wall, stdout, or stderr ceiling;
- retain the complete bounded files, exact termination class, and whether the
  wall/stdout/stderr limit fired;
- catch launch/pre-exec failures, materialize empty raw streams where needed,
  write a sealed `failed-launch` record, and stop without retry;
- preserve the exact 39-process sequence, inputs, commands, environment,
  resource values, concurrency one, evidence root, and completion-last rule;
  and
- add temporary-root synthetic tests for a successful child, stdout overflow,
  and launch failure. Synthetic test children are implementation controls, not
  M2.1 corpus/control observations or attempt processes.

Do not materialize the registered evidence root, pass a corpus/control path to
Lean, run attempt 001, alter the input/control authority, change a process
command/limit, or add a retry.

## 3. Required behavior

For a launched child:

1. open the already-retained stdin file read-only and stdout/stderr files with
   exclusive creation;
2. start one new process group under the existing CPU/address/file limits;
3. poll wall time and on-disk stream sizes at a bounded interval;
4. send `SIGKILL` to the process group on the first exceeded limit;
5. reap the child, close and hash exact streams, and write the sealed record;
6. classify `complete` only for exit zero with no fired limit; and
7. stop the attempt on every other class without retry or completion.

A launch/pre-exec exception records its exception type/message as diagnostic
metadata, `returncode = null`, `status = failed-launch`, zero-byte stdout and
stderr, and the same expected command/cwd/environment/stdin/limit identity.
It cannot become a successful process or consume a later process ordinal.

## 4. Tests and acceptance

Focused tests must prove:

- a bounded successful synthetic child retains exact stdout and a valid sealed
  complete record;
- a child exceeding a tiny synthetic stdout ceiling is killed/reaped, retains
  no more than a bounded polling overshoot, writes an output-limit record, and
  raises without retry;
- a nonexistent executable writes a sealed launch-failure record and raises;
- the registered 39-process program and authorization payload remain otherwise
  unchanged; and
- contract, complete-parity, parity-prose, link, Python, shell, whitespace, and
  CI gates remain green with all credit zero.

After the corrected implementation is committed and pushed, update the
pre-execution result with new runner/test hashes and render a new authorization
digest. Attempt 001 still requires explicit user authorization for that exact
new digest.
