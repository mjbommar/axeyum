# TL0.7.3 result — immutable Lean execution checkpoint store

Status: **complete for registered local process-interruption controls; no
power-loss, Lean, U2, or parity outcome**

Date: 2026-07-22

Parent:

- [source-first TL0.7.3 plan](lean-execution-store-tl0.7.3-plan-2026-07-22.md)
- [TL0.7 execution-evidence plan](lean-execution-evidence-tl0.7-plan-2026-07-22.md)
- [TL0.7.2 process-adapter result](lean-execution-process-tl0.7.2-2026-07-22.md)
- [complete Lean 4.30 parity contract](lean4-complete-parity-contract-2026-07-22.md)

Machine-readable evidence:

- [result authority](lean-execution-store-v1.json)
- generated [Markdown](generated/lean-execution-store.md) and
  [JSON](generated/lean-execution-store.json)
- [65 retained files](evidence/lean-execution-store-tl0.7.3/) across two
  storage descriptors and sixteen exact kill-cell directories
- [`scripts/lean_execution_store.py`](../../scripts/lean_execution_store.py)
- [`scripts/tests/test_lean_execution_store.py`](../../scripts/tests/test_lean_execution_store.py)

## 1. Verdict

TL0.7.3 proves the planned immutable-store behavior for **process
interruption** on the two registered local Linux storage observations. The
accepted result contains:

- two uninterrupted references, one on the worktree's observed ext4 mount and
  one on `/dev/shm` tmpfs;
- sixteen of sixteen exact `SIGKILL` cells: two storage classes by dependency
  versus completion target by four persistence boundaries;
- sixteen reaped workers with return status `-SIGKILL` and sixteen exact
  separately fsynced phase markers;
- eight pre-link resumes returning `installed`, eight post-link resumes
  returning `existing-valid`, and no overwrite or duplicate;
- eight cells that quarantine one orphan temporary and eight with no orphan,
  exactly matching the registered phase partition;
- sixteen of sixteen interrupted/resumed canonical projections equal to their
  uninterrupted storage-class reference;
- 65 retained evidence files totaling 43,978 bytes; and
- zero real outcomes, completed U2 cases, official/Axeyum outcomes, paired
  cells, performance rows, or parity credit.

TL0.7 remains `PARTIAL`. TL0.7.4 must send one pinned-Lean preflight and one
official-export control through the complete path, both with zero U2/parity
credit, before TL0.6.3 can begin.

## 2. Source-first order and superseded diagnostic pass

The exact classes, namespace, closure rules, persistence phases, sixteen-cell
matrix, eighteen mutation families, claims, and stop conditions were committed
and pushed at `8bad614645137164eafec6ab6cf068e5035695b5` before the store source
existed or a kill cell ran.

The first implementation was pushed at `7c1fb0e9`; contract hardening was
pushed at `c4b59d86` before the first kill cell. A first complete retained pass
was committed at `7516a2f1`. The subsequent integration audit found that its
validator compared the retained absolute worktree root with the validating
checkout's current root. That made otherwise content-stable evidence
checkout-path-dependent. The first pass was therefore treated as superseded
diagnostic evidence rather than relabeled.

The path-portable validator and its regression were committed and pushed at
`afe7db6e04c78fcbce04c6f502268ce2d9934121`. All sixteen authoritative cells
were then recreated from that exact revision. The authority records that full
revision and rehashes the plan, store, tests, reused primitive/worker,
predecessor authorities, and every retained file on each check. The superseded
bytes remain recoverable from Git commit `7516a2f1`; they are not referenced by
the accepted authority.

No Lean binary, CTest command, `lean4export`, Axeyum executable, or U2 case ran
in any TL0.7.3 pass.

## 3. Exact observed storage classes

| Class | Root/source | Observed identity | Qualified claim |
|---|---|---|---|
| `linux-local-worktree-hardlink-fsync-v1` | worktree on `/dev/nvme0n1p1` | ext4, statfs magic `ef53`, 4,096-byte blocks, kernel `7.0.0-27-generic` | local process-interruption recovery on this mounted host |
| `linux-tmpfs-hardlink-fsync-v1` | `/dev/shm` on `tmpfs` | tmpfs, statfs magic `1021994`, 4,096-byte blocks, kernel `7.0.0-27-generic` | volatile-memory filesystem contrast only |

Each class passed an actual same-directory temporary write, file fsync,
hard-link no-replace/`EEXIST`, directory fsync, inode/readback preflight before
its cells. The retained descriptor includes the mount IDs, root, source,
options, device/filesystem IDs, statfs magic, block sizes, kernel, and mechanism
identity. Validation preserves the recorded absolute root as evidence without
requiring a later checkout to occupy the same path.

These observations do **not** qualify power loss, host loss, NFS, provider
artifact retention, object storage, cross-filesystem publication, or
distributed coordination. In particular, tmpfs is volatile; it is not a
durability upgrade over ext4.

## 4. Recovery and completion closure

The store wraps the frozen ADR-0344 primitive without editing it. The exact
commit point is a same-filesystem no-replace hard link after a fully written
and fsynced private temporary. The final inode becomes read-only and is fsynced;
the temporary is removed and the directory is fsynced. Resume accepts identical
bytes only. Different bytes preserve the existing final, quarantine the
incoming temporary, and fail.

The accepted Lean namespace is limited to the manifest, exact run/attempt/
case/artifact records, one completion, and ignored-but-auditable quarantine.
No symlink, directory alias, extra record, wrong suffix/mode, unsafe path,
filename/content mismatch, noncanonical JSON, field drift, self-hash drift, or
record-set drift is accepted.

Completion is installed only after every exact dependency validates and is
reconstructed into the TL0.7.1 interrupted/resumed bundle. The terminal-less
first attempt remains explicit; case and artifact record-set digests must
match; completion is installed last; and final validation reconstructs the
bundle again. PIDs, temporary paths, quarantine names, and other observational
crash facts cannot enter the canonical projection.

## 5. Validation

Reproduction and offline validation:

```sh
python3 -m unittest scripts.tests.test_lean_execution_store
python3 scripts/lean_execution_store.py result --check
python3 -m unittest scripts.tests.test_smtcomp_resume_fs
python3 -m unittest scripts.tests.test_lean_execution_evidence
python3 scripts/gen-lean-execution-evidence.py --check
python3 -m unittest scripts.tests.test_lean_execution_process
python3 scripts/lean_execution_process.py result --check
python3 -m unittest scripts.tests.test_lean_complete_parity
python3 scripts/gen-lean-complete-parity.py --check
```

The focused suite has 22 contract/mutation tests plus one live sixteen-cell
test. It covers all eighteen preregistered mutation families: storage/source/
claim identities, preflight failure, every record family, unsafe paths and
symlinks, idempotence and conflict quarantine, malformed orphans, missing/
reordered/duplicated/wrong dependencies, terminal-less attempts, completion
ordering and record-set digests, raw process evidence, projection independence,
and zero-credit enforcement. The independent SMT-COMP filesystem suite remains
green and its authority is not converted into Lean credit.

The complete-parity report remains at 0/10 complete populations, 0/12 complete
axes, zero paired cells, 0/10 satisfied terminal gates, and a disabled terminal
claim.

## 6. Handoff

TL0.7.4 owns the first real but explicitly no-credit controls. It must
preregister and then retain:

1. one pinned-Lean toolchain/preflight attempt through the exact TL0.7.2
   process adapter and this store; and
2. one official-export control through the 8 GiB lane and this store.

Both controls must retain exact source/toolchain/command/platform/resource/
artifact identities and completion closure. Neither may enter a U2 official or
Axeyum denominator, paired cell, performance comparison, or parity gate. If the
complete policy cannot represent either control without weakening an identity
or credit boundary, TL0.7.4 must revise the policy and keep TL0.6.3 blocked.
