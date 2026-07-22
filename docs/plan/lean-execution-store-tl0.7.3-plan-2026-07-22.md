# TL0.7.3 plan — immutable Lean execution checkpoint store

Status: **preregistered; no store implementation or kill/resume observation yet**

Date: 2026-07-22

Owner: complete Lean-parity documentation/evidence lane

Parent:

- [TL0.7 execution-evidence plan](lean-execution-evidence-tl0.7-plan-2026-07-22.md)
- [TL0.7.1 machine-contract result](lean-execution-evidence-tl0.7.1-2026-07-22.md)
- [TL0.7.2 process-adapter result](lean-execution-process-tl0.7.2-2026-07-22.md)
- [`TL0.7.3`](lean-system-implementation-plan-2026-07-21.md#tl07-lean-execution-evidence-slices)
- [ADR-0344](../research/09-decisions/adr-0344-preregister-resumable-distributed-benchmark-execution.md)

## 1. Decision boundary

TL0.7.3 proves that the immutable TL0.7.1 run/attempt/case/artifact/completion
records can survive process interruption on two explicitly registered local
Linux filesystem classes. It owns no process-result classification and does
not execute Lean, CTest, `lean4export`, or Axeyum. It cannot create an official
outcome, Axeyum outcome, U2 case result, performance row, paired cell, or parity
credit.

This slice must distinguish:

1. **atomic visibility**: a final path is either absent or names complete
   bytes and never replaces an existing path;
2. **process-interruption recovery**: `SIGKILL` at an exposed persistence
   boundary leaves a state that can be quarantined/resumed;
3. **semantic closure**: completion is installed only after all and only the
   expected immutable dependencies validate; and
4. **power-loss durability**: explicitly **not proved** by a live mounted
   filesystem plus process kill.

TL0.7.3 may reuse the accepted ADR-0344 local primitive but must add an
independent Lean namespace and completion validator. It must not modify the
SMT-COMP lane or convert its E1a/E1b/E2/E3 evidence into Lean credit.

## 2. Frozen predecessor and implementation inputs

| Input | SHA-256 | Role |
|---|---|---|
| `lean-execution-evidence-v1.json` | `83fbfeaf6baa4c1bd747ce80bba87a15aaf159bb164a7647cc8e3155282fa05a` | exact TL0.7.1 record/checkpoint/credit contract |
| `lean-execution-process-v1.json` | `0fc2d552f8594e2285eef2f0307a9b4d5313024166f0256486b731366947c0bf` | completed TL0.7.2 boundary and zero-credit handoff |
| `scripts/lean_execution_process.py` | `96f6866f619563e9fc639ca360f40260d2c35b521b3fc67941675d22984b2007` | process evidence producer; read-only predecessor |
| `scripts/tests/test_lean_execution_process.py` | `5aea0fe02b3fa3278153807f7c1a1c8068ed1bfa7ea910f9b3aca08ae4a6521d` | process mutation/behavior gate |
| TL0.7.2 result | `666ab3c6b8bc6e889c14ef418d67ff30a83940e45f4bf82560cb8b300bd872d7` | exact residual and source-first history |
| `scripts/smtcomp_repro/resume_fs.py` | `1968e7b6424c2dd9273bff5041e96fc21b83ec01b2205dcc840d5dc942be1aec` | accepted local no-replace hard-link/fsync primitive; dependency only |
| `scripts/tests/test_smtcomp_resume_fs.py` | `43a4c588903e331e1cd8582b9ba80496f9e3686a25e3b4a6dedf99afaa171cdf` | existing four-boundary process-kill precedent |
| SMT-COMP E1a result | `3c0477b3a459399d45608e3c988d5b103242acd185780b72b5b7a2cf676643f1` | bounded precedent and non-claims |
| ADR-0344 | `3faef4ae21a1b61739812c524d76f1efc2d7e473b1a59d7d3921594ec0a475ed` | immutable record, resume, attempt, and completion-last decision |

Implementation begins from published topic revision
`2fee0f83c91317b6d3f8824cf76a0713c966d810`. This plan must be committed and
pushed before the store source exists or a kill/resume cell runs.

The mechanism is informed by primary references reviewed on 2026-07-22:

- [`fsync(2)`](https://man7.org/linux/man-pages/man2/fsync.2.html) states that
  syncing a file does not necessarily persist its directory entry, so the
  directory needs a separate `fsync`;
- [`open(2)`](https://man7.org/linux/man-pages/man2/open.2.html) specifies
  `O_CREAT|O_EXCL` create-or-`EEXIST` behavior;
- [`link(2)`/hard-link semantics](https://man7.org/linux/man-pages/man2/link.2.html)
  provide the same-filesystem no-replace commit point used by the accepted
  primitive; and
- [ext4 journal documentation](https://www.kernel.org/doc/html/latest/filesystems/ext4/journal.html)
  distinguishes metadata journaling from application-level data guarantees.

These references constrain the protocol; this process-kill slice still cannot
claim power-loss recovery.

## 3. Registered storage classes

The first result must exercise both ordered classes. Actual mount/source/
options, statfs type, device ID, filesystem ID, block size, kernel, and root
path are retained for every cell; a class name never substitutes for observed
identity.

| Class | Required mechanism | Current preregistration observation | Credit boundary |
|---|---|---|---|
| `linux-local-worktree-hardlink-fsync-v1` | local writable Linux filesystem; same-directory `O_EXCL` temporary; hard links; file and directory `fsync` | worktree resolves to `/dev/nvme0n1p1`, `ext4`, `rw,relatime`; statfs reports the ext family, 4,096-byte blocks | local process-interruption contract only |
| `linux-tmpfs-hardlink-fsync-v1` | writable `/dev/shm` `tmpfs` with the same primitive | `/dev/shm`, `tmpfs`, `rw,nosuid,nodev,inode64,usrquota`; 4,096-byte blocks | volatile-memory filesystem contrast only |

The implementation must preflight an actual hard-link round trip, file fsync,
directory fsync, canonical readback, and no-replace `EEXIST` behavior before a
cell. Symlinks, network filesystems, unknown mount identity, cross-filesystem
links, missing directory fsync, and read-only/unsupported paths fail before the
worker. Overlay/XFS/Btrfs may exercise portable tests but do not retrospectively
become the exact retained ext4 class.

Neither class represents GitHub artifact retention, NFS, object storage,
distributed coordination, host-loss recovery, or a released production data
store.

## 4. Reused atomic primitive

The store wraps, but does not edit, the frozen `resume_fs.py` sequence:

1. create a unique same-directory private temporary with
   `O_WRONLY|O_CREAT|O_EXCL`;
2. write canonical exact bytes completely;
3. `fsync` the temporary;
4. create the final path by same-filesystem hard link, which fails if the final
   name already exists;
5. make the inode read-only, `fsync` it again, close, and unlink the temporary;
6. `fsync` the directory.

Existing identical canonical bytes return `existing-valid`. Existing different
bytes remain untouched; the incoming temporary is quarantined and the install
fails. Orphan temporaries are quarantined, never silently promoted or parsed as
completed records. The accepted namespace ignores quarantine but exposes its
inventory in diagnostics.

The four exact exposed interruption boundaries are:

```text
before_temp_open
after_temp_fsync
after_final_link
after_commit
```

They cover absence before creation, a durable orphan before commit, a visible
final plus orphan before directory commit completes, and a committed final.
The source hash above fixes the internal operations between these hooks.

## 5. Lean store namespace and closure

Planned owned implementation:

- `scripts/lean_execution_store.py` — storage-class capture, fixture
  materialization, strict loader, completion validator, recovery, result
  authority, and generated summary;
- `scripts/tests/test_lean_execution_store.py` — structural/mutation and live
  16-cell tests;
- `docs/plan/evidence/lean-execution-store-tl0.7.3/` — small retained cell
  records plus raw child stdout/stderr;
- `docs/plan/lean-execution-store-v1.json` — exact result authority;
- `docs/plan/generated/lean-execution-store.{json,md}` — derived views; and
- `docs/plan/lean-execution-store-tl0.7.3-2026-07-22.md` — bounded result.

The store root accepts only:

```text
store.json
run/run.json
attempts/<attempt-id>.json
cases/<case-id>.json
artifacts/<artifact-id>.json
completion/completion.json
quarantine/...
```

No symlink, directory alias, extra top-level entry, wrong suffix, unsafe ID,
noncanonical JSON, writable final, or filename/content-ID mismatch is accepted.
Every accepted record revalidates its TL0.7.1 self-hash and exact field set.

The fixed fixture is TL0.7.1's `interrupted-resumed` synthetic control: two
attempts (including the terminal-less first attempt), two passed synthetic
cases owned by the retry, four artifacts, and one completion. It carries
`synthetic-no-credit` and all-zero credits. No TL0.7.2 observation is copied
into this fixture, and no real identity is introduced.

`store.json` freezes the schema/producer, storage class and observed identity,
fixture/control ID, exact expected relative paths and hashes, completion path,
and credit class before dependency installation. Completion may be installed
only when:

- every expected run/attempt/case/artifact record exists exactly once;
- every record validates and its filename/ID/hash matches the manifest;
- no unexpected accepted-namespace record exists;
- the terminal-less first attempt remains accounted;
- case and artifact aggregate digests equal the completion;
- the reconstructed TL0.7.1 bundle validates; and
- completion is still absent.

After completion install, strict validation reconstructs the bundle again and
requires the final accepted-namespace projection to equal the uninterrupted
reference byte-for-byte. Quarantine and observational crash-cell evidence are
outside that canonical projection.

## 6. Frozen process-kill matrix

Each storage class has one uninterrupted reference. The required destructive
matrix has **16 cells**:

```text
2 storage classes
× 2 target roles (one dependency case record; completion record)
× 4 exposed persistence boundaries
= 16 SIGKILL cells
```

For every cell:

1. create a fresh store root and install all records preceding the target;
2. launch the exact committed worker in a new session with the target canonical
   payload and one stop phase;
3. wait for a separately fsynced phase marker;
4. send `SIGKILL` to the worker process group and reap it;
5. retain exact command, environment, source/executable hashes, PID/group,
   signal, marker bytes/hash, stdout/stderr bytes/hashes, storage identity, and
   pre/post namespace inventories;
6. quarantine orphan temporaries without promotion;
7. reinstall only a missing target or accept only identical existing bytes;
8. install any remaining dependencies and completion last;
9. validate exact closure; and
10. compare the timing/PID/quarantine-independent canonical projection with the
    uninterrupted reference for that storage class.

The dependency target is `cases/case-a.json`. The completion target is
`completion/completion.json`. `after_final_link` and `after_commit` resume must
return `existing-valid`; pre-link states must install the missing target.
Every worker must have return status `-SIGKILL`; a clean/other exit invalidates
the cell.

Retained result order is storage class, then target role, then the four phase
names above. No skipped retained cell is allowed. Portable CI tests may report
an unavailable optional filesystem separately, but cannot fill the committed
16-cell authority.

## 7. Required controls and mutations

The implementation must test at least:

1. exact storage descriptor and observed mount/statfs identity;
2. hard-link/no-replace/fsync preflight failure before worker launch;
3. canonical/self-hash/exact-field drift in every record family;
4. unsafe ID, path traversal, symlink, wrong filename/ID, wrong mode, and extra
   namespace entry;
5. identical reinstall is idempotent and produces no duplicate;
6. different valid bytes under one final path preserve the original,
   quarantine the incoming candidate, and fail;
7. truncated/malformed orphan is quarantined and never promoted;
8. each of the four kill phases has exact marker, signal, reap, and raw output
   evidence;
9. dependency-target and completion-target recovery on both classes;
10. missing, duplicate, unexpected, reordered, wrong-attempt, or hash-drifted
    dependency blocks completion;
11. terminal-less attempt omission blocks completion;
12. case/artifact record-set digest drift blocks completion;
13. completion before dependencies or a second/different completion fails;
14. interrupted/resumed and uninterrupted canonical projections match;
15. observational PIDs/times/quarantine names cannot enter the canonical
    projection;
16. store/process sources or preregistration identity drift;
17. any Lean/CTest/exporter/Axeyum command or U2 case in the fixture; and
18. any nonzero real/outcome/case-denominator/performance/paired/parity credit.

At least twelve focused tests must cover all eighteen mutation families. The
existing SMT-COMP filesystem suite remains an independent regression and must
stay green.

## 8. Acceptance and stop conditions

TL0.7.3 is complete only when:

- this plan was committed and pushed before implementation and kill controls;
- both uninterrupted references validate;
- all 16 exact kill cells validate with `SIGKILL`, recovery, closure, and
  projection equality;
- identical resume, conflict quarantine, malformed orphan, namespace, record,
  completion-order, lost-attempt, digest, and credit mutations fail closed;
- the result authority rehashes every retained evidence/source input and
  records zero real/parity counters;
- TL0.7.1, TL0.7.2, complete-parity, foundational-resource, cargo-check, and
  owned documentation gates remain green; and
- any unrelated baseline failure is reported exactly rather than hidden.

Stop with TL0.7.3 partial if a filesystem cannot be identified, hard-link or
directory fsync behavior is assumed rather than preflighted, a killed worker
survives, a temporary is promoted without re-execution, an existing final can
be overwritten, completion can precede dependencies, projection equality needs
observational fields removed after the fact rather than by schema, or any real
Lean/U2/parity result would be required.

The result must say explicitly that process `SIGKILL` is not host loss or
power loss, `tmpfs` is volatile, the ext4 observation is one mounted host, and
neither class qualifies NFS/provider/object/distributed durability.

After TL0.7.3, TL0.7 remains `PARTIAL`. Only TL0.7.4 may send one pinned-Lean
preflight and one official-export control through the complete path, both with
zero U2/parity credit. TL0.6.3 remains blocked until that acceptance slice
closes.
