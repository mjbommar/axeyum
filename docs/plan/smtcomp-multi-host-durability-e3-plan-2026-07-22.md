# SMT-COMP resumable execution E3 multi-host durability plan

Status: preregistered; implementation and destructive gates open
Date: 2026-07-22
Owner: SMT-COMP measurement/full-library lane

## Decision

Close ADR-0344 E3 with a content-bound coordinator over the actual shared
NFSv4.1 mount used by the candidate harness. Do not add an untested generic SSH
wrapper or claim that NFS is durable by construction.

The E3 coordinator will:

1. bind one immutable run and one self-hashed multi-host plan;
2. preregister at least three distinct hosts, disjoint initial shard ownership,
   and any permitted retry allocation;
3. require the same registered environment class and per-host E2 aggregate
   envelope on every allocation;
4. launch each host allocation inside its own E2 user-systemd/cgroup-v2 service;
5. write attempts, results, terminals, resource sessions, and recoveries through
   the existing same-directory fsync plus atomic hard-link/no-overwrite boundary
   on the shared mount;
6. preserve a lost host runner as a terminal-less allocation, resource session,
   and shard attempt;
7. recover a lease only after an exact allocation/session/unit liveness check,
   and only onto a preregistered equivalent host; and
8. publish multi-host completion and raw output only after the full E1/E2/E3
   evidence bundle validates.

This is the shared-storage branch of E3. A host-local spool and
content-addressed transfer protocol remains an alternative for environments
without the exact tested shared mount; it is not silently treated as equivalent.

## Why this storage boundary

The 2026-07-22 preflight observed the following common host class on `s5`,
`s6`, and `s7`:

- Linux `7.0.0-28-generic`, x86-64;
- Python `3.14.4`, executable SHA-256
  `b8d8288faefdd300201f43fcf00f6f539a27218eeed3a3dff5ab10b9c4c99700`;
- unified cgroup v2 with `cpu`, `memory`, and `pids` controllers;
- a working user-systemd transient service; and
- `/nas3/data/axeyum/harness` mounted from `nas3:/volume1/data` as hard
  NFSv4.1 with the same rsize/wsize, timeout, retransmit, security, and
  `local_lock=none` policy. Only client address differs.

The protocol does not use advisory locks. POSIX `link()` atomically creates the
new directory entry, and Linux specifically recommends the unique-file plus
hard-link pattern for portable NFS lock acquisition. Linux NFS clients flush
application data when `fsync()` is requested, while NFSv4 specifies synchronous
modifying operations except for explicitly unstable writes. These are design
inputs, not proof that this NAS survives every server or power failure; E3 earns
only the exact observed NFSv4.1 client/server and interruption cells.

References:

- [POSIX `link()` atomicity](https://man7.org/linux/man-pages/man3/link.3p.html)
- [Linux `open(2)` NFS hard-link locking guidance](https://man7.org/linux/man-pages/man2/open.2.html)
- [Linux NFS client caching and `fsync`](https://man7.org/linux/man-pages/man5/nfs.5.html)
- [NFSv4 stable-storage and COMMIT semantics](https://www.rfc-editor.org/rfc/rfc7530)
- [systemd kill semantics](https://www.freedesktop.org/software/systemd/man/latest/systemd.kill.html)

## Frozen evidence schemas

All JSON uses the existing canonical encoding: UTF-8, sorted object keys,
compact separators, and one trailing LF. Immutable records are self-hashed.

### Multi-host plan

Schema: `axeyum.smtcomp-multi-host-plan.v1`

Required fields:

- `schema`
- `run_identity_sha256`
- `transport`
- `shared_root`
- `shared_filesystem_class_sha256`
- `environment_class_sha256`
- `host_registrations`
- `allocations`
- `fault_injection`
- `plan_sha256`

`transport` is exactly `shared-nfs-v4.1-atomic-link-v1` for this slice.
`shared_root` must be an absolute, non-symlinked path below the explicitly
provided E3 test root. The filesystem class binds source, type, protocol
version, hard/soft behavior, rsize/wsize, timeout, retransmits, security mode,
and lock policy while excluding only the per-client address.

Every host registration binds:

- a safe logical `host_id` and exact SSH target;
- the hostname observed by the remote process;
- kernel, architecture, Python version, and Python executable hash;
- cgroup-v2 controller set and user-systemd capability;
- the environment-class and shared-filesystem-class digests; and
- a self-hash.

Every allocation binds:

- a unique allocation ID and generation;
- one registered host;
- a sorted, unique, nonempty shard list;
- the exact E2 enforcement ID;
- an optional earlier allocation ID that it may recover; and
- a self-hash.

Generation zero allocations must cover every shard exactly once with no
overlap. A later allocation may repeat only shards owned by the exact failed
allocation it names. Retry capacity is preregistered; the coordinator cannot
invent a new host after failure.

### Allocation attempt

Schema: `axeyum.smtcomp-host-allocation-attempt.v1`

The immutable launch binds plan/run/allocation IDs, host registration,
resource session ID, exact argv digest, coordinator PID/host, and start time.
An optional terminal records SSH exit status, stdout/stderr content addresses,
end time, and `completed`, `failed`, or `lost` status. A coordinator kill may
leave this terminal absent; later completion must list it as unclosed.

### Recovery record

Schema: `axeyum.smtcomp-host-recovery.v1`

A recovery binds the failed and retry allocation IDs, failed resource session,
exact stale lease owner, remote unit name, remote unit state, launcher PID
probe, probe time, recovered shard ID, quarantine path, and record hash. The
coordinator refuses recovery if the unit is active, the launcher PID is live,
the lease owner differs, the retry is not preregistered, or the environment
class differs.

### Multi-host completion

Schema: `axeyum.smtcomp-multi-host-completion.v1`

Completion binds plan/run IDs, all allocation attempt IDs, unclosed allocation
attempt IDs, recovery IDs, all resource session IDs, the full E1 canonical
bundle hash, the E2 resource-completion hash, completion time, and its own
record hash. Raw export requires this record for an E3 run.

## Source and command transport

The remote hosts do not see the topic worktree. E3 therefore stages a
content-addressed execution bundle on the shared root containing only the
registered runner source files and committed tiny fixtures. A canonical source
identity artifact carries the repository commit, dirty-tree content identity,
and runner-source digest already bound by the run manifest. Remote preflight
recomputes every staged runner file and solver executable hash and compares the
source identity fields; it does not invent a clean Git checkout or weaken the
run identity.

The coordinator invokes only one fixed staged helper through SSH; solver argv
is stored in a canonical manifest and executed by that helper, not interpolated
into the SSH command. Because OpenSSH may still pass its fixed remote command
through the account's login shell, every transport token is restricted to safe
identifiers or absolute safe paths. SSH stdout and stderr are content-addressed
rather than parsed as result evidence.

## Preregistered gates

### Portable contract gates

1. Fewer than three host registrations reject.
2. Duplicate hosts, allocation IDs, or generation-zero shard ownership reject.
3. Missing/unexpected shards and unregistered retry hosts reject.
4. Environment, filesystem, run, resource, source-bundle, and command drift
   reject before launch.
5. A recovery without an exact failed allocation/session/lease match rejects.
6. An active unit or live launcher PID blocks lease recovery.
7. Missing, malformed, unclosed-unaccounted, or tampered allocation/resource/
   recovery evidence blocks completion and raw export.
8. Reordered directory enumeration preserves the canonical result projection.

### Required live N>=3 gate

Use `s5`, `s6`, and `s7`, a committed six-case fake-solver corpus, three
striped shards, one worker/one core/64 MiB/32 PIDs per host, zero swap, and a
new run-specific NFS directory.

Run two independent controls:

- **uninterrupted:** all three generation-zero allocations finish; the result,
  resource, allocation, and multi-host completions validate;
- **loss/retry:** after the failed host publishes resource preflight and starts
  its solver, kill that exact transient service's host-runner process. Prove
  the unit inactive and launcher absent, retain the terminal-less session and
  shard attempt, recover only the exact stale lease, execute the preregistered
  retry on an equivalent second host, and validate final completion.

The two canonical timing-free outcome projections must be byte-identical.
Lifecycle and
resource evidence must differ in the expected way: the interrupted run has one
failed allocation terminal, one unclosed resource session and shard attempt,
plus one exact recovery record. An absent allocation terminal remains a valid
representation of coordinator loss, but the registered host-runner-loss gate
keeps the coordinator alive and therefore closes that outer SSH attempt.

The live gate must use `AXEYUM_REQUIRE_SMTCOMP_MULTIHOST=1`; absence of any
registered host, user-systemd/cgroup capability, or exact shared filesystem
class fails closed. The default repository gate runs portable tests and skips
the live cell explicitly.

## Stop and cleanup safety

Each allocation has one exact transient unit name derived from the run and
resource session IDs. Fault injection and cleanup target that unit, never a
host-wide `pkill`. A failed test retains its evidence directory and prints the
exact unit/run paths for operator cleanup. Successful development-only runs may
remove their own explicitly resolved temporary directory; the final accepted
live evidence is append-only under a dated E3 gate directory.

The stale s4 diagnostic run is outside this plan. It remains untouched and
receives zero measurement credit.

## Exit and nonclaims

E3 is complete only when portable mutations and both required live N>=3 runs
pass from the committed branch, the exact external evidence paths/digests are
recorded, and ADR-0344/roadmap/STATUS are reconciled.

E3 does not establish official SMT-COMP selection, performance neutrality,
cross-datacenter fault tolerance, NFS server power-loss survival, arbitrary
host equivalence, or BenchExec compatibility. Those claims require their own
artifacts and gates.
