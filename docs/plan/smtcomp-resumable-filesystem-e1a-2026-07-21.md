# Resumable benchmark filesystem prototype: E1a result

Status: accepted prototype result; production integration open
Date: 2026-07-21

## Outcome

ADR-0344's first production prerequisite now has a real filesystem and process-
kill prototype. A child was forcibly killed at four exact record-persistence
boundaries on two local filesystem profiles. All **8/8** interrupted cases
resumed to the same canonical merged bytes as the uninterrupted control.

This closes E1a—the local immutable-record mechanism and kill matrix. It does
not close E1 launcher integration, E2 aggregate resource enforcement, E3
multi-host recovery, or the separate official-style selection ledger. The
64,345-file candidate remains unauthorized.

Subsequent status: the
[fixture-only E1b result](smtcomp-resumable-runner-e1b-2026-07-22.md) now closes
the active-runner/lease/sidecar/export portion of E1. E2-E3 and the selection
ledger remain open, so the candidate is still unauthorized.

The matrix was rerun clean after the
[v2 process-evidence correction](smtcomp-runner-e1b-audit-2026-07-21.md):
attempt-attributed v2 records retain the same 8/8 local recovery result and
canonical scoring projection.

## Implementation under test

[`scripts/smtcomp_repro/resume_fs.py`](../../scripts/smtcomp_repro/resume_fs.py)
implements the bounded Linux filesystem prototype:

1. serialize canonical UTF-8 JSON with sorted keys and one trailing newline;
2. create a unique same-directory temporary with `O_EXCL`;
3. write fully, set mode `0444`, and `fsync` the file;
4. install the immutable final name with a same-filesystem hard link, which
   fails rather than replacing an existing name;
5. unlink the temporary and `fsync` the directory; and
6. publish shard completion only after records.

Resume has three outcomes:

- identical existing canonical bytes: `existing-valid`, skip safely;
- different existing bytes: retain the final, quarantine the incoming
  candidate, and fail; or
- orphan temporary after interruption: quarantine it without promotion, then
  rerun the missing result.

The strict loader accepts only the registered run/assignment/attempt/record/
completion namespace, requires canonical JSON, checks record filenames against
their content-bound keys, and then delegates to the E0 identity/completeness
validator. Quarantine is visible but excluded from accepted results.

## Forced-kill matrix

The child process writes a durable phase marker and pauses. The parent sends
`SIGKILL`, waits for reaping, quarantines any orphan temporary, installs only
missing immutable records, writes completion last, and performs strict merge.

| Filesystem profile | Before temporary open | After temporary fsync | After final hard link | After directory fsync | Canonical recovery |
|---|---:|---:|---:|---:|---:|
| `/tmp` (`tmpfs`) | pass | pass | pass | pass | 4/4 byte-identical |
| repository worktree (`ext2/ext3` family reported by `statfs`) | pass | pass | pass | pass | 4/4 byte-identical |

Commands:

```sh
PYTHONWARNINGS=error python3 -m unittest scripts.tests.test_smtcomp_resume_fs
AXEYUM_FS_FIXTURE_PARENT=. PYTHONWARNINGS=error \
  python3 -m unittest scripts.tests.test_smtcomp_resume_fs
```

The four-test suite also passes these non-kill controls:

- second installation of identical content is idempotent;
- a self-consistent conflicting record is preserved in
  `quarantine/conflicts/` while the original final remains unchanged;
- a deliberately truncated temporary is preserved in
  `quarantine/orphans/` and never promoted; and
- a valid record under the wrong content-addressed filename is rejected.

## What this establishes

- Process interruption does not require parsing progress logs.
- The final filename is a no-overwrite commit point.
- Resume does not remeasure an already committed record.
- A final hard link left beside an orphan temporary remains usable; the
  temporary is quarantined.
- A completed namespace is independent of directory enumeration and retry
  order because strict merge is canonical.
- Completion-last ordering is enforceable and incomplete namespaces fail
  closed.

## What this does not establish

- Power-loss durability. `SIGKILL` preserves the kernel and mounted
  filesystem; it is not a crash-consistency test.
- NFS/shared-filesystem hard-link, cache-coherence, rename, or `fsync`
  guarantees. No `/nas3` mutation was performed.
- Signal-safe terminal emission. `SIGKILL` correctly leaves no terminal; the
  later completion accounts for that attempt using the E0 contract.
- Single-owner leases or stale-owner recovery.
- Actual solver execution, remote launch, cgroup-v2 enforcement, peak RSS
  capture, or host environment-class qualification.
- Compatibility export into `compete.py --score-raw` or strict replacement of
  `raw_from_json`.
- Official BenchExec execution or SMT-COMP selection fidelity.

## Remaining sequence

### E1b — Integrate without changing benchmark semantics

- Move the immutable writer behind `compete.py` as an opt-in versioned output
  mode; keep legacy `--dump-raw` explicitly non-resumable.
- Create run and assignment manifests before execution, launch attempts before
  solver invocation, best-effort terminals after it, and completion last.
- Add a deterministic fake solver that is killed during execution as well as
  during persistence.
- Export the current raw JSON only from a fully validating canonical bundle.
- Replace duplicate overwrite in `raw_from_json` with a conflict error.
- Define a single-owner lease and explicit stale-owner recovery before allowing
  two processes to target one shard.

### E2/E3 — Resource and distributed gates

- Enforce and record one-host aggregate cgroup/resource limits.
- Measure environment equivalence rather than assuming hostnames are
  interchangeable.
- Validate host-local spool plus content-addressed transfer or the actual
  shared-filesystem durability boundary.
- Kill one remote worker/host on a tiny corpus for N>=3 runs and require full
  attempt accounting and canonical completion.

Only after these gates and the selection-provenance work may E4 create a fresh
large-candidate attempt directory.
