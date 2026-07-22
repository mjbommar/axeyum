# Resumable distributed benchmark execution

Status: E0/v2 contract and E1a local filesystem prototype landed; production integration not implemented
Date: 2026-07-21

## Plain-English outcome

The first 64,345-case candidate run did not merely fail to finish. It showed
that the current runner cannot preserve structured evidence from a failed
shard. The replacement should treat each solver/benchmark result as an
immutable checkpoint, treat a shard completion as a separately validated fact,
and refuse scoring until every expected checkpoint is present under one exact
measurement identity.

The checked prototype now freezes that data contract. It does **not** rerun the
corpus, modify the remote launcher, or turn the candidate selection into an
official SMT-COMP population.

The follow-on [E1a result](smtcomp-resumable-filesystem-e1a-2026-07-21.md)
implements and kill-tests the local immutable-record boundary on tmpfs and the
repository's ext-family filesystem. E1b launcher/solver integration remains
open.

## Current implementation audit

The failure follows directly from the current code:

- `compete.py::run_all` retains every `RawResult` in memory and returns only
  after the last selected case;
- `--dump-raw` writes one shard-level JSON file after `run_all` returns, with no
  atomic temporary/install boundary;
- `raw_from_json` assigns into `per[bench][name]`, so later duplicate keys
  silently overwrite earlier results instead of exposing a conflict;
- the raw format does not bind input bytes, solver binary, command, runner
  source, selected-list hash, repository commit, resource limits, shard
  mapping, or measurement environment;
- `distribute_run.sh` launches 52 `nohup` processes but persists no launch PID,
  exit/signal state, assigned IDs, attempt identity, aggregate memory budget,
  or completion manifest; and
- the local executor's `RLIMIT_AS` is explicitly best-effort per child. The
  distributor multiplies requested per-child memory by concurrent workers but
  does not prove a host-level limit.

Consequently, 2,041 human progress lines survived the first interruption while
zero machine-mergeable result shards did. Rerunning unchanged would reproduce
the measurement-architecture risk even if the unexplained termination did not
recur.

## External reference boundary

The [SMT-COMP 2026 rules](https://smt-comp.github.io/2026/rules.pdf) specify
BenchExec as the competition execution framework. BenchExec's
[benchmark documentation](https://github.com/sosy-lab/benchexec/blob/main/doc/benchexec.md)
binds tools, tasks, and resource limits in a benchmark definition and emits
individual execution results and resource measurements for later table
generation. The local Axeyum harness deliberately separates execution from
central scoring in the same broad shape, but it is not BenchExec and should not
describe its self-contained executor as competition-faithful.

The near-term protocol is therefore pre-rehearsal infrastructure: make local
distributed evidence durable and auditable, then use BenchExec for an
official-style execution rehearsal after selection provenance is complete.

## Contract prototype

The active source contract is
[`smtcomp-resumable-run-contract-v2.json`](smtcomp-resumable-run-contract-v2.json).
It supersedes the preserved v1 prototype before production integration because
the [E1b audit](smtcomp-runner-e1b-audit-2026-07-21.md) found v1 could not
represent real process outcomes or retry attribution without loss.
Its generated
[failure/recovery matrix](generated/smtcomp-resumable-run-contract.md) checks
**18 invariants against 28 executable scenarios**: five accepted controls and
23 fail-closed mutations. The interrupted/resumed deterministic scoring
projection merges byte-for-byte identically to its uninterrupted control.

The prototype establishes five boundaries.

### 1. Immutable run identity

Before launch, one digest binds:

- contract and result schemas;
- selection manifest, selected list, and corpus identity;
- solver binary and command;
- runner source and repository commit;
- track, wall/CPU/memory/core limits;
- shard count and mapping; and
- measurement environment class.

A changed limit, executable, selected list, runner, or environment is a new run,
not a resume. Hardware identity may be represented as a preregistered
equivalence class, but that class must itself be measured and hashed; hostname
substitution alone is not evidence of equivalence.

### 2. Immutable per-result checkpoints

A result key binds normalized benchmark ID, exact input SHA-256, and solver ID.
The production writer should create a same-directory temporary record, flush
and fsync it, atomically install the final immutable name, and fsync the
directory. An existing valid record is skipped on resume. An existing invalid
or different record is preserved as a conflict and stops the run; it is never
overwritten.

Individual immutable files are selected over one append-only JSONL ledger for
v1. A killed writer can leave a partial JSONL tail, while a same-directory
install exposes either the old namespace or the complete new record. At roughly
1,238 records per shard, the file count is bounded enough for this candidate.
Production validation still has to test the actual shared filesystem's rename
and fsync semantics; the in-memory prototype does not claim NFS durability.

### 3. Attempts are not shard completion

Every launch gets an immutable attempt manifest. A graceful terminal records
PID, host, exit/signal/status, wall duration, peak RSS, completed count, record
set hash, and missing IDs. SIGKILL, host loss, or OOM may prevent terminal
emission; absence is retained as evidence, not synthesized into a guessed
cause.

A later resume may complete the shard. Its completion manifest must enumerate
all attempt IDs and explicitly list any older terminal-less attempts. This
allows honest recovery without either deleting the failed attempt or requiring
the impossible—that a killed process write its own terminal footer.

### 4. Completeness is a merge precondition

Central merge validates all and only assigned result keys, exact run identity,
self-hashes, unique shard ownership, environment identity, attempt accounting,
completion counts, and result-set hashes. It rejects identical as well as
conflicting duplicate records: resume should skip a valid immutable checkpoint,
so a duplicate at merge is evidence of overlapping ownership or orchestration
drift.

No incomplete merge is scoreable. A separate diagnostic may summarize partial
progress, but it must carry `incomplete` status and cannot flow into inventory,
PAR-2, decide-rate, or publication tables.

### 5. Aggregate resources are part of the experiment

Per-child limits do not prevent 16 concurrent 6 GiB workers from asking one
host for 96 GiB. The production launcher must record a cgroup-v2 or equivalent
enforcement identity, worker slots, and aggregate memory/CPU bounds. Preflight
must prove `worker_slots * per_worker_memory <= aggregate_memory`; the terminal
manifest records the observed peak. Merely printing requested limits is not a
resource-control result.

## What byte-identical recovery means

The byte-identity gate uses a deterministic fake solver with fixed outcomes and
times. It proves checkpoint selection and canonical merge do not depend on
interruption, retry, shard order, or filesystem enumeration. It does **not**
claim that two real timed solver executions should have identical durations.

For real execution, a resumed run skips already committed measurements and
executes only missing keys. If a completed key must be remeasured, the old run
is preserved and a new run identity is created rather than mixing trials.

## Staged production plan

### E0 — Data contract (landed v2 prototype)

- Preserved v1 sketch plus active machine-readable v2 process-evidence contract.
- Self-hashed immutable records and strict merge model.
- Attempt versus shard-completion semantics.
- 28-scenario mutation matrix.
- Deterministic interruption/recovery byte-equivalence control.
- Typed termination, observed/admitted verdict separation, per-result attempt
  attribution, terminal new/skipped partitions, and output identities.

Exit: generated artifacts are byte-stable and all mutations behave as
declared. This authorizes design review only.

### E1 — Local filesystem writer and validator

- Implement atomic record installation and conflict quarantine.
- Add immutable run, assignment, launch, terminal, and completion manifests.
- Replace silent raw merge overwrites with strict validation.
- Preserve a compatibility exporter to the current raw JSON shape only after a
  complete validated merge.

Exit: kill a real fake-solver worker before write, after temporary fsync, after
install, and after completion; resume each case and match an uninterrupted
canonical output. Mutation-test truncation, conflicts, and identity drift.

**E1a result:** the filesystem/record half passes 8/8 forced-kill recoveries
across tmpfs and the local ext-family worktree plus conflict, orphan, and
filename-drift controls. The actual solver/launcher, lease, current-raw export,
and duplicate-merge replacement remain E1b; E1 as a whole is not complete.

The E1b source audit also finds two active-runner semantic defects that v2 must
correct inside opt-in mode: a parsed timeout response is discarded despite the
SMT-COMP 2026 response rule, and any other negative POSIX return code is guessed
to mean memory exhaustion. See the
[runner audit](smtcomp-runner-e1b-audit-2026-07-21.md).

### E2 — One-host enforced execution

- Add a single-owner shard lease with explicit stale-owner recovery.
- Enforce and record one aggregate cgroup/resource envelope.
- Record exact host/environment profile and peak resources.
- Exercise bounded concurrency under a tiny committed corpus.

Exit: forced process kill and host-runner kill both preserve accepted records;
resource overcommit and environment drift fail before solver launch.

### E3 — Multi-host rehearsal

- Allocate disjoint assignments and immutable attempt IDs centrally.
- Validate shared-filesystem durability or switch to host-local spools plus
  content-addressed transfer.
- Simulate one host loss and one retry on an equivalent registered host class.
- Require a complete run manifest before producing current-format raw JSON.

Exit: N>=3 interrupted and uninterrupted tiny-corpus runs are canonical-shape
equivalent, every attempt is accounted, and central merge has zero missing,
unexpected, or duplicate keys.

### E4 — Candidate completeness run

Only after E1-E3 and the separate official-style selection ledger are complete:

- launch into a new timestamped directory;
- use conservative measured concurrency, not the old 52-worker plan by default;
- make artifact completeness/resume behavior the primary endpoint; and
- grant performance or coverage credit only after strict merge and independent
  provenance validation.

## Explicit non-goals

- Do not diagnose the first termination as OOM without kernel/cgroup evidence.
- Do not parse progress logs into raw records.
- Do not repair or overwrite the frozen first attempt.
- Do not rerun the 64,345-case candidate during E0-E3.
- Do not call the current selection official, random, representative, or
  source-balanced.
- Do not turn a complete local run into an official SMT-COMP result; BenchExec
  rehearsal and the full selection policy remain separate gates.

## Strategic effect on G1

G1's next step is no longer “run more files.” It is “make every file result
survive and prove what run it belongs to.” This is a small measurement-
infrastructure project, not a solver feature. Once complete, the official-style
selection ledger and matched cvc5/Bitwuzla executions can proceed without
risking another opaque partial run.
