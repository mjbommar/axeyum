# SMT-COMP E3 multi-host durability result — 2026-07-22

## Bounded verdict

E3 is complete for the preregistered tiny-corpus, shared-NFSv4.1,
user-systemd/cgroup-v2 host-loss cell. Three equivalent hosts (`s5`, `s6`, and
`s7`) ran the same six-case/three-shard identity both uninterrupted and with
the exact `s5` host-runner killed after its solver marker. The preregistered
shard-0 retry completed on `s6`, both final bundles validate, and their
timing-free outcome projections are byte-identical.

This closes the execution-durability prerequisite. It does not make the stale
64,345-file run creditable and does not close the independent official
selection-identity ledger.

## What is implemented

- `multi_host.py` freezes host observations, one environment/filesystem class,
  initial and retry allocations, canonical host commands, allocation attempts
  and terminals, exact fault and recovery records, and multi-host completion.
- Runner and fixture bytes are staged under a content-addressed directory.
  Remote preflight recomputes the staged runner digest and binds it to the run's
  repository/source identity. Every staged Python process uses `-B`; repeat
  execution cannot create bytecode inside the immutable bundle.
- The coordinator creates the full shared run namespace before concurrent host
  launch. Immutable files use same-directory write/fsync, no-replace hard-link
  publication, post-link mode freeze, and directory fsync.
- Each host allocation runs only its preregistered shard set inside one exact
  transient user-systemd service with one worker, one CPU, 64 MiB memory, zero
  swap, and 32 PIDs.
- Recovery requires the exact failed allocation/session/shard, inactive unit,
  absent launcher PID, unchanged lease owner, and a preregistered different
  host. The stale lease is moved to a deterministic quarantine path.
- E3 raw export requires valid E1 results and sidecars, E2 resource completion,
  exact E3 allocation/fault/recovery evidence, and E3 completion.

## Required live evidence

Final repeated accepted root:

```text
/nas3/data/axeyum/harness/e3-gate/live-1784740048714236679-84b40626d845
```

Common identity:

- repository commit: `84b40626d845d1c4ec5a6735986329bdb2d00d53`
- run identity: `93bf3f85fdd1e336bfe9dcaf50b279194ad6e824ffaead3309cb3ef04c4dd864`
- outcome projection: `411fb218896ba36ef45852235c05a3ef1dd95cfef5d2b6ea26c8c8ea09671055`
- source bundle:
  `/nas3/data/axeyum/harness/e3-gate/source-bundles/83e9f5e5ec37c0ecb0a62b0da730c6ed99c465bcfd6fab76a7086b07423b8b05`
- source identity record:
  `2b884c4fed50170c1626f15523fe5a3dd02dcdf409e36379df862652cab59b29`
- runner-source digest:
  `9bf3293071005eaa147f37d87764e631dde08bbb8380d62b09f4fe7444507660`
- environment record:
  `7bf1ceeb52c53c39c753129ab2e0e40b5f867e5454fc0bb046b9d10a848d1c42`

The registered environment is Linux `7.0.0-28-generic`, x86-64, Python
3.14.4, with the same Python executable digest on all three hosts. Shared
storage is `nas3:/volume1/data`, mounted at `/nas3/data` as hard NFSv4.1 with
the exact normalized options preserved in `inputs/environment.json`; its class
digest is `3ed04d2f443e42ff9681dc6184b672c2593b6d38d25127db4afef4efd730d9bf`.

### Uninterrupted control

- six result records, three completed allocation attempts, three completed
  resource sessions, no recovery, and no unclosed attempt/session;
- multi-host completion record:
  `c1410f7041864fb82b77c3579d336e9557f7d7cb1cfb7e5e09dd2bbd98bf7738`;
- resource completion record:
  `b1fb964ca9b31e0ef18f867f4171a00a6007213be0ba9bc6af66cd65c80f1ee1`;
- canonical merged bundle:
  `2e7fbf668a5dfda3b9ea920e31a593fcf0bcd3b7af3bf5a0d4d18b79b6c0d1b6`.

### Loss/retry control

- the exact unit
  `axeyum-smtcomp-e3-loss-initial-0-84b40626.service` and launcher PID 64244
  were bound to cgroup
  `/user.slice/user-1000.slice/user@1000.service/app.slice/axeyum-smtcomp-e3-loss-initial-0-84b40626.service`
  and killed with signal 9 after the shard-0 solver marker;
- fault record:
  `8428b13747ccef6b6bf5022019c4c4a44375d20531176a1525cd792208751bc9`;
- recovery record:
  `6a3bddcd6a3530a82c8f3ff0623b7a21295b82606c50333f2a177d6ddb71a736`;
- the failed outer SSH allocation has an honest failed terminal; resource
  session `loss-initial-0-84b40626` and its first shard attempt remain
  terminal-less, and shard completion names that unclosed attempt;
- retry allocation `retry-0` ran shard 0 on `s6` and completed;
- multi-host completion record:
  `4a07245c1bf57ebee2d86091a446a0a15b84f7b26db9b45b6abcc4aece15d533`;
- resource completion record:
  `df2e052c7cc19393668d87d41931b84f3e96d33d88e807bfeda00ac9c0d12f09`;
- canonical merged bundle:
  `216f88045c37f91bb944a2989304b4fee08ea6bf7c121cb97b5be76c2dbcbd55`.

The merged hashes differ because attempts and timings are evidence. The
registered timing-free result population/verdict projection is identical.
After validation, all `axeyum-smtcomp-e3-*` services were inactive on all
three hosts, and the reused source bundle contained no `__pycache__` or `.pyc`
objects.

## Executed gates

```sh
./scripts/check-smtcomp-resume.sh
AXEYUM_REQUIRE_SMTCOMP_MULTIHOST=1 ./scripts/check-smtcomp-resume.sh
AXEYUM_REQUIRE_SMTCOMP_MULTIHOST=1 \
  python3 -m unittest -v scripts.tests.test_smtcomp_multi_host_live
```

The aggregate mandatory run passed 24 resumability/resource/multi-host tests,
the 5 runner tests, 30 scoring tests, 6 pipeline tests, 5 selection tests, 2
provenance tests, and the generated 18-invariant/28-scenario contract check.
The direct live test was repeated at the same commit, proving that the
content-addressed source bundle remains reusable and unchanged.

Portable E3 tests additionally reject fewer than three or duplicate hosts,
partition overlap/gaps, same-host and unregistered retry, environment drift,
escaped fault markers, staged-source/namespace mutation, host-command drift,
live-owner recovery, unaccounted failed allocations, and raw export without
E3 completion.

## Failures found while earning the gate

1. The NAS maps created files to server UID 1024. Linux protected-hardlink
   policy rejected a link after the temporary was frozen to mode 0444. The
   writer now publishes the fully written/fsynced private temporary first and
   freezes both hard links through the still-open descriptor before returning.
2. Concurrent cross-client directory creation produced `EEXIST` races despite
   local `exist_ok` handling. The coordinator now creates the exact namespace
   before any host starts.
3. The coordinator's NFS client retained a negative lookup after deleting the
   old marker. Fault readiness is now observed and content-hashed through the
   owning host's client.
4. A successful run created Python bytecode under the staged source, and the
   next reuse correctly rejected the extra namespace. `-B` is now mandatory for
   the remote helper, host runner, systemd child, and shard workers.

The rejected/partial roots remain preserved under the E3 gate directory. They
receive no completion credit.

## Residual boundary

This proves process/service loss and retry on the registered three-host/NFS
class. It does not prove NAS power-loss survival, server failover, network
partition tolerance, arbitrary hosts/filesystems, hostile same-account
workers, BenchExec equivalence, selection representativeness, or solver
performance. The next G1 item is the independent official eligibility/status/
difficulty/release/seed/corpus/per-file selection ledger.
