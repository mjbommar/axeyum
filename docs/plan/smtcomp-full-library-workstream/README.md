# SMT-COMP Full-Library Work Stream — RESUME HERE

**This folder is the single entry point for the SMT-COMP measurement,
full-library inventory, and gap-closing lane.** Updated 2026-07-22 after E2
one-host aggregate enforcement and the second full-library soundness finding.

The goal is an honest, reproducible per-logic decide/decline/**wrong** map over
a source-balanced SMT-COMP-style population, followed by a measured and ranked
gap-closing program. A run receives no score credit unless its selection,
environment, resource envelope, attempt history, outputs, and shard completion
are all checkable.

The ranked program is
[`../full-library-gap-closing-plan-2026-07-22.md`](../full-library-gap-closing-plan-2026-07-22.md).
The active durability design is
[`../smtcomp-resumable-run-design-2026-07-21.md`](../smtcomp-resumable-run-design-2026-07-21.md)
under proposed
[ADR-0344](../../research/09-decisions/adr-0344-preregister-resumable-distributed-benchmark-execution.md).

---

## 1. Current bounded verdict

The measurement lane is **not ready for another credited 64,345-file run**.

- E0 contract and E1a local persistence are complete.
- E1b is now fixture-complete in the active runner: exact preflight identity,
  immutable attempts/results/output sidecars, typed process outcomes,
  observed/admitted verdict separation, completion-last publication, strict
  duplicate rejection, a no-steal lease, and explicit stale recovery are all
  executable.
- E2 is complete on one delegated user-systemd/cgroup-v2 host: exact aggregate
  memory/swap/CPU/PID limits, bounded shard concurrency, immutable controller
  evidence, host-runner kill, explicit unclosed-session recovery, overcommit,
  environment drift, and evidence tamper are executable gates.
- E3 multi-host allocation, host-loss recovery, and shared-storage or spool
  transfer durability are open.
- The independent official eligibility/status/difficulty selection ledger is
  open. E1b's exact ordered per-file digest ledger does not substitute for it.

The old s4 run remains useful only as a bug-discovery stream. It predates both
soundness repairs, uses end-of-shard raw output, and does not satisfy E1-E3; it
receives zero measurement credit even if every shard eventually exits.

---

## 2. What landed in this increment

### E1b runner/solver integration

`compete.py --run-manifest ... --run-dir ...` now activates the v2 evidence
path for one fixture-only solver. Before creating a run directory or starting a
solver, it validates:

- ordered selected-list bytes and every benchmark's normalized ID, SHA-256,
  and byte count;
- selection, corpus, and environment artifacts;
- solver executable bytes, command template, and configuration;
- runner source identities, repository commit, dirty-tree content identity,
  and Python toolchain identity;
- track, shard mapping, output policy, and the complete declared resource
  envelope.

Execution acquires one exact-owner shard lease, publishes an immutable launch,
captures byte-exact stdout/stderr and typed termination, installs the result and
sidecars, records a separate best-effort terminal, and publishes completion
last. Resume skips only complete validating checkpoints. A terminal-less old
attempt remains visible in `unclosed_attempt_ids`; recovery must explicitly name
the prior lease owner, and age alone never steals ownership.

The runner preserves a response printed before watchdog termination under the
registered SMT-COMP 2026 response policy. Wall timeout, ordinary signal,
nonzero exit, evidenced CPU/memory resource termination, and runner error are
separate states. Arbitrary signals are never guessed to be OOM. Legacy raw JSON
is exported only after the entire bundle validates, and any duplicate
benchmark/solver cell is rejected.

Detailed result:
[`../smtcomp-resumable-runner-e1b-2026-07-22.md`](../smtcomp-resumable-runner-e1b-2026-07-22.md).

### E2 one-host aggregate enforcement

`compete.py --host-run` now launches all registered shards under one transient
user-systemd service. The service cgroup contains the host runner, at most the
registered number of shard workers, every solver process, and descendants.
Before workers start, the adapter validates the registered unit identity,
limits, controllers, path/inode, and launcher membership; only then does it
configure and read back `memory.oom.group=1` and validate the complete snapshot.
The exact limits include `memory.max`, zero `memory.swap.max`, `cpu.max`, and
`pids.max`.

Each immutable resource session records those facts plus baseline counter maps.
Its terminal records worker exits, memory/PID peaks, and deltas for
`memory.events`, `cpu.stat`, and `pids.events`. Every E2 attempt names its
session. Killing the in-cgroup host runner leaves an honest terminal-less
attempt and resource session; systemd kills the rest of the control group, and
the next session completes only after exact-owner lease recovery. Raw export
requires self-hashed resource completion as well as the E1 result bundle.

Detailed result:
[`../smtcomp-one-host-resource-enforcement-e2-2026-07-22.md`](../smtcomp-one-host-resource-enforcement-e2-2026-07-22.md).

### QF_AUFLIA soundness gate

The old run's second WRONG marker was not FP-family noise:

```text
QF_AUFLIA/array_benchmarks/misc/pipeline-invalid.smt2
expected sat; staged Axeyum unsat in 12.10 s
```

The exact file SHA-256 is
`dc7f8f51be688669321c8a9a15f2543fc070bc3a4c55b81c763604c34fa73bde`.
Current Axeyum reproduced `unsat`; cvc5 1.3.4 returned `sat`, including after
Axeyum parsed and sharing-preservingly rewrote the script. The parser and stale
binary are therefore not the cause.

The lazy-ROW adapter's scalar QF_UFLIA search exported an unproved refutation of
a satisfiable abstraction. The adapter now enforces the foundational evidence
boundary: an unchecked scalar `unsat` becomes `unknown` until an independently
checked proof can be lifted through the array abstraction. Certificate-rechecked
array refuters still run first. The exact 2024 benchmark is committed in the
curated QF_AUFLIA corpus with a no-wrong-verdict regression.

---

## 3. Live stale run snapshot

At the latest audit, the eight s4 shards had written 20,657 progress lines
(about 32% of 64,345) and were processing QF_BV. No `raw_*.json` shard had been
published. The exact two WRONG markers were:

1. QF_ABVFP KLEE `query.26.smt2`: expected `unsat`, stale binary returned
   `sat`; the exact-cancellation FP repair is on main.
2. QF_AUFLIA `pipeline-invalid.smt2`: expected `sat`, stale and then-current
   Axeyum returned `unsat`; this branch adds the sound decline above.

Run identity:

- selected list: 64,345 paths, seed `20260721`, SHA-256
  `1f988de6efd8b0dd47ccbc14d7c61739f6e47f55a675fc705e7f58c7baf47609`;
- staged Axeyum binary SHA-256
  `ff36fc2d309966ad8e1f8b87096e09e1582567078d3f13ce21df5ec04c9a5d4f`;
- host: s4, eight shards, `RAYON_NUM_THREADS=1`, 300-second ceiling;
- logs: `/nas3/data/axeyum/harness/full-inventory/raw_selection/log_0..7.log`.

Do not stop this diagnostic job by killing only `compete.py`; that orphans
solver children. Use `scripts/smtcomp_repro/stop_run.sh` if an authorized stop
is needed.

---

## 4. Executable gates

The bounded E0-E2 gate is:

```sh
./scripts/check-smtcomp-resume.sh
AXEYUM_REQUIRE_SMTCOMP_CGROUP=1 ./scripts/check-smtcomp-resume.sh
AXEYUM_FS_FIXTURE_PARENT=. PYTHONWARNINGS=error \
  python3 -m unittest scripts.tests.test_smtcomp_resume_fs
```

The first command runs the portable gate and auto-skips live cgroup cells if
the host lacks the required delegation. The second makes the live E2 cells
mandatory. The filesystem override repeats E1a on the worktree filesystem.

Together they cover:

- 18 contract invariants and 28 mutation/control scenarios;
- local tmpfs and worktree-filesystem kill recovery;
- real runner kills before and during fake-solver execution;
- lease collision and explicit recovery;
- interrupted/resumed versus uninterrupted canonical equivalence;
- timeout-observed response admission;
- typed exit/signal/resource outcomes and non-UTF-8 byte preservation;
- output-sidecar mutation and duplicate raw-cell rejection;
- exact cgroup descriptor/controller validation, two-worker bounded execution,
  resource-evidence mutation, and killed-host-runner recovery; and
- scoring, selection, provenance, and generated-contract checks.

The QF_AUFLIA regression is:

```sh
CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --all-features \
  --test int_array_sort public_pipeline_invalid_sat_never_exports_unchecked_auflia_unsat
```

`just check` includes the resumability gate and remains the branch-wide merge
gate.

---

## 5. Remaining work, in dependency order

1. **E3 — multi-host recovery.** Preallocate host/shard/resource ownership for
   N>=3 hosts; prove host loss, retry, spool/shared-storage transfer, lease
   recovery, complete-set validation, and canonical equivalence to an
   uninterrupted control.
2. **Selection identity.** Implement the official eligibility, status,
   difficulty, release, seed, cap/family, corpus-tree, and exact-file ledger.
   Keep this policy artifact separate from the E1b execution ledger.
3. **Fresh P0 slices.** Stage the repaired binary and rerun
   QF_FP/QF_BVFP/QF_ABVFP plus QF_AUFLIA under the completed protocol. Require
   DISAGREE=0.
4. **Credited full population.** Only then execute Axeyum, cvc5, and Bitwuzla on
   the same versioned selection; publish the per-logic inventory and regenerate
   the coverage-weighted parity matrix without combining incompatible regimes.

The implementation rule for E3 is the same as E1-E2: build the mechanism and
its destructive/interruption tests on a tiny corpus before spending the full
population.

---

## 6. Artifact map

Repository:

- active harness: `scripts/smtcomp_repro/`;
- aggregate gate: `scripts/check-smtcomp-resume.sh`;
- v2 contract source and generated view:
  `docs/plan/smtcomp-resumable-run-contract-v2.json` and
  `docs/plan/generated/smtcomp-resumable-run-contract.{json,md}`;
- E1a result: `docs/plan/smtcomp-resumable-filesystem-e1a-2026-07-21.md`;
- E1b audit/result: `docs/plan/smtcomp-runner-e1b-audit-2026-07-21.md` and
  `docs/plan/smtcomp-resumable-runner-e1b-2026-07-22.md`;
- E2 result: `docs/plan/smtcomp-one-host-resource-enforcement-e2-2026-07-22.md`;
- candidate failure handoff:
  `docs/plan/smtcomp-full-library-candidate-run-handoff-2026-07-21.md`;
- ranked gap plan: `docs/plan/full-library-gap-closing-plan-2026-07-22.md`;
- preserved FP repro:
  `bench-results/smtcomp-full-library-20260722/soundness-fp-wrong-sat/`;
- preserved AUFLIA regression:
  `corpus/public-curated/non-incremental/QF_AUFLIA/cvc5-regress-clean/smtlib2024__array_benchmarks__misc__pipeline-invalid.smt2`.

NAS (shared, corpus read-only in practice):

- SMT-LIB 2024 corpus: `/nas3/data/axeyum/corpus/smtlib-2024/`;
- old candidate identity: `/nas3/data/axeyum/harness/full-inventory/`;
- stale run logs: `/nas3/data/axeyum/harness/full-inventory/raw_selection/`;
- staged binaries: `/nas3/data/axeyum/harness/bin/`.

---

## 7. Resume protocol

1. Read `PLAN.md`, this file, the roadmap, foundational DAG, and proposed
   ADR-0344.
2. Work in a dedicated `agent/smtcomp/*` worktree; never mutate the integration
   checkout or another lane's NAS output.
3. Confirm the old s4 process/log state and count literal `WRONG` lines without
   treating the stale run as evidence.
4. Take E3 next. Keep the v2 result schema and E1-E2 gates fixed unless a failing
   mutation demonstrates a necessary correction.
5. Update `STATUS.md` and this file before handoff; push only a green topic
   branch for the integration owner.

*Owner: SMT-COMP measurement/full-library lane. Next milestone: E3 N>=3
multi-host loss/retry and transfer durability, not another large run.*
