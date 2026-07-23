# SMT-COMP Full-Library Work Stream — RESUME HERE

**This folder is the single entry point for the SMT-COMP measurement,
full-library inventory, and gap-closing lane.** Updated 2026-07-23 after F1
integration and the fixture-only F2 preparation implementation.

The goal is an honest, reproducible per-logic decide/decline/**wrong** map over
a source-balanced SMT-COMP-style population, followed by a measured and ranked
gap-closing program. A run receives no score credit unless its selection,
environment, resource envelope, attempt history, outputs, and shard completion
are all checkable.

The ranked program is
[`../full-library-gap-closing-plan-2026-07-22.md`](../full-library-gap-closing-plan-2026-07-22.md).
The active durability design is
[`../smtcomp-resumable-run-design-2026-07-21.md`](../smtcomp-resumable-run-design-2026-07-21.md)
under accepted
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
- E3 is complete on the registered `s5`/`s6`/`s7` NFSv4.1 class: exact
  allocation, source staging, per-host cgroups, host-runner loss, stale-lease
  recovery, different-host retry, central completion, raw-export gating, and
  repeated outcome equivalence are executable.
- The independent official eligibility/status/difficulty selection ledger is
  preregistered under proposed ADR-0356. S0 now freezes the 29-source,
  51-direct-child-submission, seven-result, 90-archive authority plus an
  18-invariant/
  18-mutation contract and exact synthetic fixture. Full official-input audit
  and production are still open. The authority is the pinned 2026 organizer
  code plus matching SMT-LIB 2025.08.04 release; E1b's exact ordered per-file
  digest ledger does not substitute for it. S1a now parses the organizer's
  actual `defs.py`, benchmark/results JSON, and submission shapes without
  importing organizer code. The first S1b live input attempt is retained as a
  negative: it stopped before metadata reduction on the official regexp-valued
  logic shape and exposed that the organizer's submission glob is
  non-recursive. A second retained attempt proved that regexp expansion ranges
  over the complete `Logic` enum before `Participation.get` filters it through
  the selected track's divisions. A third retained attempt completed metadata
  streaming and proved the two configured removal IDs already match zero
  metadata rows, so the producer's anti-join is idempotent. A fourth retained
  attempt reduced all seven historical files and exposed that official metadata
  order is not canonical path order. S1b is now complete: the fifth fresh run
  verified 89 inputs, 450,472 metadata rows, and 5,345,294 historical rows,
  then published a 256,182,191-byte path-sorted eligibility ledger with
  `selection_observed=false`. S2 is also complete: the committed resumable
  downloader and safe extractor verified all 90 release files and
  4,890,207,406 compressed bytes, then proved an exact 450,472-file,
  82,270,961,563-byte metadata/tree bijection across 89 logic trees. A fresh
  process rehashed every retained archive and extracted file. The official
  S3 is complete: after its implementation was committed and pushed, two fresh
  88-file no-Git bundles and hash-required 14-package environments generated
  byte-identical official 45,905-path selections (2,709 new / 43,196 old).
  A fresh standard-library process rehashed both complete runs. S4 is now also
  complete: the accepted content-addressed root reconstructs all 450,472
  decisions, binds 45,905 selected files / 15,148,369,947 selected bytes,
  passes 18 invariants and 18 rejecting mutations, and was independently
  reverified with a second physical selected-file hash pass. ADR-0356 is
  accepted. S5 harness admission remains required before any credited solver
  run, but is deferred while the active lane closes checked solver capability.

The old s4 run remains useful only as a bug-discovery stream. It predates both
soundness repairs, uses end-of-shard raw output, and does not satisfy E1-E3. It
stopped without a raw shard artifact and receives zero measurement credit.

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

### E3 multi-host durability

The coordinator now preregisters at least three equivalent hosts, exact
initial/retry shard ownership, one normalized NFSv4.1 filesystem class, and
canonical host commands. It stages content-addressed source/fixture bytes,
precreates the shared namespace, launches only the allocated shards, records
outer allocation attempts and per-host E2 sessions, and refuses central
completion or raw export without complete E1/E2/E3 evidence.

The required live gate ran the same six-case/three-shard identity on `s5`,
`s6`, and `s7`. Its uninterrupted control completed directly. Its loss control
sealed the solver marker and exact cgroup/launcher/SIGKILL observation, retained
one terminal-less resource session and shard attempt, quarantined only the
matching stale shard-0 lease after the unit and PID were dead, and completed the
preregistered retry on `s6`. Both timing-free outcome projections have SHA-256
`411fb218896ba36ef45852235c05a3ef1dd95cfef5d2b6ea26c8c8ea09671055`.

Detailed result:
[`../smtcomp-multi-host-durability-e3-2026-07-22.md`](../smtcomp-multi-host-durability-e3-2026-07-22.md).

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

## 3. Final stale run snapshot

At the bounded 2026-07-22 19:28 EDT audit, no `compete.py` or staged solver
process remained. The eight s4 logs stopped after 33,305 of 64,345 cases
(51.8%), with per-shard last indices 4,123, 4,139, 4,168, 4,141, 4,150,
4,149, 4,302, and 4,125. No `raw_*.json` shard was published. The logs contain
56 literal `<<< WRONG` markers: 25 `sat -> unsat` and 31 `unsat -> sat`.

The first two markers triggered the preserved soundness work:

1. QF_ABVFP KLEE `query.26.smt2`: expected `unsat`, stale binary returned
   `sat`; the exact-cancellation FP repair is on main.
2. QF_AUFLIA `pipeline-invalid.smt2`: expected `sat`, stale and then-current
   Axeyum returned `unsat`; this branch adds the sound decline above.

The remaining 54 markers are later FP-family alarms from the same stale binary,
including division, multiplication, FMA, conversion, and a repeated
`query.26.smt2` row. They have not been adjudicated against the current branch
and receive no correctness, coverage, or measurement credit. The stopped logs
remain immutable bug-discovery input only.

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

The bounded E0-E3 gate is:

```sh
./scripts/check-smtcomp-resume.sh
AXEYUM_REQUIRE_SMTCOMP_CGROUP=1 ./scripts/check-smtcomp-resume.sh
AXEYUM_REQUIRE_SMTCOMP_MULTIHOST=1 ./scripts/check-smtcomp-resume.sh
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
- three-host plan/source/command mutation gates, complete E3 export gating,
  exact fault/recovery evidence, and repeated live uninterrupted/loss controls;
  and
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

1. **Harness admission (S5) — complete.** Selection identity S0--S4 is complete under
   [accepted ADR-0356](../../research/09-decisions/adr-0356-preregister-official-smtcomp-selection-identity.md).
   E1b now binds the accepted completion, selected list, selected-file ledger,
   and physical bytes. The [S5 result](../smtcomp-harness-admission-s5-result-2026-07-23.md)
   records the tiny mutation gate and a read-only 45,905-file physical rehash.
   It does not authorize a large run by itself.
2. **Fresh P0 slices — Axeyum/cvc5 closed; Bitwuzla recovery repair pending.** Stage the repaired binary and rerun
   QF_FP/QF_BVFP/QF_ABVFP plus QF_AUFLIA under the completed protocol. Require
   DISAGREE=0. The bounded
   [S5.1 admitted-slice plan](../smtcomp-admitted-slices-s5.1-plan-2026-07-23.md)
   and [result](../smtcomp-admitted-slices-s5.1-result-2026-07-23.md) close the
   ordered-subset handoff without launching a solver. Preregister the actual P0
   execution identities and limits before launching it. The
   [repaired-P0 execution plan](../smtcomp-repaired-p0-execution-plan-2026-07-23.md)
   freezes the preparation boundary. The
   [P0-S1 result](../smtcomp-repaired-p0-preparation-s1-result-2026-07-23.md)
   now records the integrated source, exact binaries, sentinels, three run/plan
   identities, and empty initial/retry namespaces. Its v2 layout keeps immutable
   run manifests under `inputs/`, outside the mutable runtime evidence roots;
   all 50 artifacts rehash and all 18 commands name those exact external
   manifests. The retained v1 run remains diagnostic-only and contributes no
   records or timings. The v2 Axeyum cell then completed all 1,810 records and
   all resource/multi-host terminals with a safe adjudication, but raw export
   rejected the coordinator-owned adjudication file in the strict generic run
   root. The [closure plan](../smtcomp-repaired-p0-v2-export-layout-closure-plan-2026-07-23.md)
   freezes that evidence and separates coordinator outputs without weakening
   the validator. Commit `5c06ec76` implements that process-free closure and
   passes the portable, cgroup, and live multi-host gates. The
   [closure result](../smtcomp-repaired-p0-v2-axeyum-closure-result-2026-07-23.md)
   records the exact process-free migration, 1,810-row raw export, external
   completion, independent validation, and byte-identical replay. Axeyum
   receives no credit and cvc5 remains blocked until that result and its
   admission-source check are integrated on `origin/main`. Merge `39691255`
   integrated that boundary, after which the
   [cvc5 result](../smtcomp-repaired-p0-v2-cvc5-result-2026-07-23.md)
   closed all 1,810 records with zero known-status contradiction and zero
   Axeyum/cvc5 disagreement. Bitwuzla remains blocked until the exact cvc5
   result and its admission-source check are integrated.
   Merge `0f7cdac1` integrated that boundary and admitted the three frozen
   Bitwuzla initial allocations. Shards 0 and 2 completed 435 records each;
   shard 1 failed before producing a record because concurrent startup exposed
   a shared-directory orphan-temporary quarantine race. The coordinator
   retained all evidence and stopped before recovery. The
   [Bitwuzla recovery plan](../smtcomp-repaired-p0-v2-bitwuzla-recovery-plan-2026-07-23.md)
   freezes the 870-record stop state and preregisters the runner repair plus
   exact different-host `retry-1` path. The implementation now scopes orphan
   recovery to shard-owned targets, represents cleanly released failed-runner
   recovery without fake lease evidence, and exposes a hash-pinned recovery-only
   coordinator mode. Twenty-three focused tests now cover the three coordinator
   restart paths, including fresh liveness/evidence validation when replaying an
   existing authority record. Released runner evidence must also exactly account
   every shard-assigned key as missing under the complete terminal contract. The
   real frozen session retains a valid failed resource terminal; `6a34bf2e`
   corrects the earlier absent-terminal model by validating and binding its file
   and record hashes plus matching worker exit code. Twenty-eight focused tests
   and the 72-test portable/cgroup/live gates pass; live E3 has no skips. No
   Bitwuzla credit is claimed at that checkpoint. The recovery batch and the
   command-manifest launch correction were subsequently integrated. The sole
   `retry-1` then executed all 435 shard-1 cases, yielding a complete 1,305-row
   inner bundle with zero known-status contradiction and zero Axeyum/cvc5
   disagreement. Outer finalization nevertheless failed because the strict
   loader encountered the original zero-record diagnostic terminal, which was
   written before its launch manifest. The
   [post-run closure plan](../smtcomp-repaired-p0-v2-bitwuzla-post-run-closure-plan-2026-07-23.md)
   freezes that state and forbids another solver retry. Bitwuzla remains
   uncredited. Commit `0eff5d64` now implements the explicit process-free
   closure without changing `resume_fs.py`: it binds the failed outer and
   successful inner evidence, quarantines only the exact diagnostic terminal,
   emits a closure-bound v2 multi-host completion, and never calls the
   allocation launcher. Thirty-one focused tests and the 75-test
   portable/cgroup/live gates pass; live E3 has no skips. The real NAS run
   remained unchanged until the plan and implementation were integrated on
   `origin/main`.
   The integrator landed those boundaries through `2855ddf7`. The explicit
   no-launch closure then completed successfully, published a 1,305-row safe
   Bitwuzla result, and replayed with an identical 1,359-file inventory digest.
   The [Bitwuzla closure result](../smtcomp-repaired-p0-v2-bitwuzla-closure-result-2026-07-23.md)
   records zero known-status contradiction, zero Axeyum/cvc5 disagreement, and
   every final artifact identity. All three repaired-P0 cells are now closed.
   The [combined-comparison plan](../smtcomp-repaired-p0-combined-comparison-plan-2026-07-23.md)
   freezes the exact 1,810-row Axeyum/cvc5 population, the 1,305-row
   three-solver FP population, the separate 505-row QF_AUFLIA projection, and
   forbids a cross-scope scalar ranking. The
   [combined-comparison result](../smtcomp-repaired-p0-combined-comparison-result-2026-07-23.md)
   now closes that boundary: all populations account, zero known-status
   contradictions and zero cross-solver disagreements remain, and the
   self-sealed JSON/Markdown reproduce from the three validated roots.
3. **Credited full population — F1 and the process-free F2 implementation are
   integrated.** The
   [full-population plan](../smtcomp-credited-full-population-plan-2026-07-23.md)
   freezes the same 45,905-file selection for all three solvers, a 96-shard/
   48-allocation wave schedule, six-worker aggregate/16-GiB-per-host resource envelope,
   exact different-host retries, thermal backoff, and complete per-logic
   adjudication. The [F1 result](../smtcomp-credited-full-population-f1-result-2026-07-23.md)
   now closes fixture-only selection rehashing, 432-command composition,
   checkpoint/restart scheduling, exact thermal-unit stop, and supervised wave
   interruption tests. The final supervisor is integrated. The
   [F2 implementation result](../smtcomp-credited-full-preparation-f2-implementation-2026-07-23.md)
   adds clean-`origin/main` readiness evidence, a content-addressed staged source
   bundle, frozen oracle checks, a complete artifact ledger, completion-last
   publication, durable Git-object replay, and zero-execution-evidence gates.
   The implementation landed by merge `502e8875`; this result/status document
   still requires normal integration. Live preparation is blocked by out-of-lane
   bench/CAS format drift and the not-yet-implemented Lean R7 current-source
   identity repair. No host probe, sentinel, NAS preparation root, resource
   session, allocation, or solver process was started.

The same implementation rule continues to apply: prove each new mechanism and
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
- E3 plan: `docs/plan/smtcomp-multi-host-durability-e3-plan-2026-07-22.md`;
- E3 result: `docs/plan/smtcomp-multi-host-durability-e3-2026-07-22.md`;
- official selection plan:
  `docs/plan/smtcomp-official-selection-identity-plan-2026-07-22.md`;
- official selection S0 authority/contract:
  `docs/plan/smtcomp-official-selection-{authority,contract}-v1.json`;
- official selection S1 input-audit result:
  `docs/plan/smtcomp-official-selection-input-audit-s1b-2026-07-22.md`;
- official selection S2 corpus result:
  `docs/plan/smtcomp-official-selection-corpus-s2-2026-07-22.md`;
- official selection S3 producer result:
  `docs/plan/smtcomp-official-selection-producer-s3-2026-07-22.md`;
- official selection S4 final result:
  `docs/plan/smtcomp-official-selection-final-s4-2026-07-22.md`;
- repaired P0-S1 preparation result:
  `docs/plan/smtcomp-repaired-p0-preparation-s1-result-2026-07-23.md`;
- retained repaired-P0 v1 layout incident:
  `docs/plan/smtcomp-repaired-p0-v1-layout-incident-2026-07-23.md`;
- repaired-P0 v2 export-layout closure plan:
  `docs/plan/smtcomp-repaired-p0-v2-export-layout-closure-plan-2026-07-23.md`;
- repaired-P0 v2 Axeyum closure result:
  `docs/plan/smtcomp-repaired-p0-v2-axeyum-closure-result-2026-07-23.md`;
- repaired-P0 v2 cvc5 result:
  `docs/plan/smtcomp-repaired-p0-v2-cvc5-result-2026-07-23.md`;
- repaired-P0 v2 Bitwuzla recovery plan:
  `docs/plan/smtcomp-repaired-p0-v2-bitwuzla-recovery-plan-2026-07-23.md`;
- repaired-P0 v2 Bitwuzla post-run closure plan:
  `docs/plan/smtcomp-repaired-p0-v2-bitwuzla-post-run-closure-plan-2026-07-23.md`;
- repaired-P0 v2 Bitwuzla closure result:
  `docs/plan/smtcomp-repaired-p0-v2-bitwuzla-closure-result-2026-07-23.md`;
- repaired-P0 combined-comparison plan:
  `docs/plan/smtcomp-repaired-p0-combined-comparison-plan-2026-07-23.md`;
- repaired-P0 combined-comparison result and generated views:
  `docs/plan/smtcomp-repaired-p0-combined-comparison-result-2026-07-23.md` and
  `docs/plan/generated/smtcomp-repaired-p0-comparison.{json,md}`;
- credited full-population execution plan:
  `docs/plan/smtcomp-credited-full-population-plan-2026-07-23.md`;
- credited full-population F1 fixture result:
  `docs/plan/smtcomp-credited-full-population-f1-result-2026-07-23.md`;
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
- staged binaries: `/nas3/data/axeyum/harness/bin/`;
- accepted E3 repeated live evidence:
  `/nas3/data/axeyum/harness/e3-gate/live-1784740048714236679-84b40626d845/`;
- accepted E3 source bundle:
  `/nas3/data/axeyum/harness/e3-gate/source-bundles/83e9f5e5ec37c0ecb0a62b0da730c6ed99c465bcfd6fab76a7086b07423b8b05/`.
- verified SMT-LIB 2025.08.04 S2 corpus acquisition:
  `/nas3/data/axeyum/harness/official-selection-2026-sq/corpus-acquisition-1784745749642951377-d48fb0dc/`.
- twice-repeated S3 official producer:
  `/nas3/data/axeyum/harness/official-selection-2026-sq/official-producer-1784755629430228923-38c5f2af/`.

---

## 7. Resume protocol

1. Read `PLAN.md`, this file, the roadmap, foundational DAG, and accepted
   ADR-0344.
2. Work in a dedicated `agent/smtcomp/*` worktree; never mutate the integration
   checkout or another lane's NAS output.
3. Confirm the old s4 process/log state and count literal `WRONG` lines without
   treating the stale run as evidence.
4. Treat the accepted S4 root as immutable. S5/S5.1 admission and the repaired
   P0-S1 v2 preparation, Axeyum closure, and cvc5 execution are complete.
   Bitwuzla's sole retry and process-free evidence closure are complete. Its
   1,305 records, v2 E3 completion, external result, safe adjudication, and
   byte-identical replay are frozen in the closure result. Do not launch another
   retry. The combined three-cell repaired-P0 comparison is also complete and
   keeps the 1,305-row FP scope separate from the 1,810-row Axeyum/cvc5 scope.
   The credited full-population F1 fixture result and supervised-wave bytes are
   integrated. Its F2 process-free preparation mechanism is also integrated,
   but its result/status document and registered source set remain on the SMT
   topic branch and no live root has been published. Integrate those bytes,
   revalidate the exact current `origin/main`, run both registered green gates,
   then perform the
   separately reviewed host/sentinel preparation and publish only a process-free
   `launch_authorized=false` root. Do not probe hosts, mutate the NAS, or launch
   a solver allocation while `origin/main` is branch-wide red. The active solver
   capability checkpoint is
   [`../checked-multi-binder-quantified-uf-models-2026-07-22.md`](../checked-multi-binder-quantified-uf-models-2026-07-22.md).
5. Update `STATUS.md` and this file before handoff; push only a green topic
   branch for the integration owner.

*Owner: SMT-COMP measurement/full-library lane. Next measurement milestone:
preregistered fresh admitted QF_FP/QF_BVFP/QF_ABVFP and QF_AUFLIA P0 slices;
the bounded multi-binder checked quantified-UF
milestone is accepted under ADR-0358. The bounded
[unknown adjudication](../quantified-uflia-unknown-adjudication-2026-07-22.md)
now measures the accepted ADR-0359
[default-only checked repair](../checked-quantified-uf-default-repair-2026-07-22.md):
178 checked SAT results versus 111 at baseline, with zero disagreements and
every SAT model replayed. The complete 39-case Z3-SAT remainder is now
[measured](../quantified-uflia-free-int-completion-measurement-2026-07-22.md):
the strict exact-source, non-truncating 16-value/256-tuple scalar policy checks
28 additional SAT models. The exploratory 33-case result used two broader
heuristics and is not the production gate. The preregistered ADR-0360 boundary
is now implemented in `5b4c5b40`: the solver package, complementary workspace
tests, static/resource/profile/recovery gates, and 225/225 direct-Z3 joint
differential are green, with 207/207 SAT replay. Acceptance is blocked only by
the cross-lane Lean parity-evidence worktree-path drift recorded in the
measurement note; do not rewrite that lane's retained evidence here. The
eleven residual seeds remain separate. Their first exact follow-up is now
[measured](../quantified-uflia-evaluated-scalar-measurement-2026-07-23.md):
proposed ADR-0361 adds only initial UF-result and evaluable exact-source integer
values to a deferred ADR-0360 retry and checks two more models under the
unchanged 16-value/256-tuple caps. The initial fixed-query probe's third model,
seed 111, required recursive MBQI re-entry and is excluded. Implement only that
preregistered post-decline search-hint change. Commit `471738aa` now implements
it after the established ADR-0360, MBQI, and E-matching routes, preserving all
prior decisions. The 256-case production gate reaches 227/227 agreement and
209/209 SAT replay; the remaining nine seeds stay separate. The complementary
workspace, lint, documentation, resource, profile, recovery, reflection,
benchmark, public QF_BV, rules, and link gates pass. ADR-0361 remains proposed:
the non-CI solver aggregate reproducibly misses its hardware-relative LIA
frontier ratchet. A fresh uninterrupted CI-mode aggregate clears the earlier
load-sensitive word/Int transient. The rebased
Lean parity gate still rejects retained `exit-zero-4g` evidence for run/spec
attribution drift. Keep those branch-gate observations separate from the green
227-case semantic result and do not rewrite Lean-owned retained evidence here.
The exact nine-seed follow-up is now
[measured](../quantified-uflia-one-level-fixed-mbqi-measurement-2026-07-23.md):
proposed ADR-0362 permits one recursion-guarded inner MBQI pass under the first
ordered temporary source-`Int` fixing, with the unchanged 16-value pool, shared
deadline, and exact unfixed replay. Preimplementation tests corrected every
inert late placement: the single pass runs immediately after initial candidate
certification fails, then continues ADR-0360, ordinary MBQI, E-matching, and
ADR-0361 on decline. The prototype reaches 228/228 agreement and 210/210 SAT
replay, adds seed 111 at `-5`, preserves seed 145, and does not authorize
multi-value or two-symbol recursive search, cap growth, or general function
synthesis. Commit `f380d1b3` implements that exact boundary. Focused controls,
the strengthened differential, solver Clippy, strict rustdoc, and one
uninterrupted CI-mode full solver-package run pass. ADR-0362 remains proposed
only on the unchanged Lean-owned retained `exit-zero-4g` run/spec attribution
drift; do not rewrite that evidence in this lane.*

*The next exact eight-seed classification is now frozen in the
[source-guided default measurement](../quantified-uflia-source-guided-default-measurement-2026-07-23.md)
under proposed ADR-0363. One additive outer initial-candidate retry augments
ADR-0359's default pool with exact source integer literals and
binder-independent evaluated source terms, after ADR-0362 and ADR-0360 decline.
The unchanged 32-value/256-combination envelope independently certifies seeds
30, 32, 70, 150, and 242; seed 122 declines at 289 combinations and seeds
175/182 exhaust. Commit `568efb15` implements this exact default-only,
replay-checked boundary. The frozen differential now returns exactly 215 SAT,
24 UNSAT, and 17 Unknown with 215/215 SAT replay, zero errors/disagreements,
and exactly `122, 175, 182` as ordinary Z3-SAT residuals. Focused tests, solver
Clippy, strict rustdoc, and links pass. One uninterrupted full-package run
passed all 907 library tests and this differential before an unrelated late
word/Int SAT test declined under sustained load; the exact test and its full
14-test binary pass under the same CI configuration. Keep that aggregate
observation separate, do not raise caps or rewrite cross-lane evidence, and
classify one distinct bounded mechanism for the three residual seeds next.*

*That next mechanism is now frozen in the
[profile-guided completion measurement](../quantified-uflia-profile-guided-model-completion-measurement-2026-07-23.md)
under proposed ADR-0364. After all established routes decline, one SAT-only
single-Int-binder CEGIS loop uses exact total-function source definitions and
checker-derived finite-profile counterexamples under the original remaining
deadline. Two complete 256-case measurements identically recover ordinary
Z3-SAT seeds 122/175/182 plus independently certified Z3-timeout seed 226 in
1/0/1/2 rounds. The projected exact totals are 219 SAT, 24 UNSAT, 13 Unknown,
and 219/219 replay with no ordinary Z3-SAT residual. Implement only this
32-round/32-instance, fail-closed boundary next; do not use the measured-bad
blind batch, grant fresh time, transfer inner UNSAT, or rewrite arbitrary
function entries. Commit `1c8e5125` now implements that exact boundary. Two
production runs reach 236/236 agreement, exactly 219 SAT, 24 UNSAT, 13 Unknown,
219/219 replay, zero errors/disagreements, and no ordinary Z3-SAT residual.
Focused controls, solver Clippy, strict rustdoc, and one uninterrupted CI-mode
all-feature solver-package run pass, including all 913 library tests, every
non-ignored integration test, and both doctests. ADR-0364 remains proposed only
on the unchanged Lean-owned parity-evidence run/spec attribution drift; do not
rewrite that evidence here. Publish these checkpoints, then resume the ranked
full-library gap plan without widening this quantified-UF boundary.*
