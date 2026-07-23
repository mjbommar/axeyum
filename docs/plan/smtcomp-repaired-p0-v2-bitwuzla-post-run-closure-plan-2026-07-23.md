# SMT-COMP repaired P0 v2 Bitwuzla post-run closure plan

Status: preregistered; implementation complete and green; no live closure
mutation performed
Date: 2026-07-23
Predecessor: [Bitwuzla recovery plan](smtcomp-repaired-p0-v2-bitwuzla-recovery-plan-2026-07-23.md)
Preparation: [P0-S1 v2 result](smtcomp-repaired-p0-preparation-s1-result-2026-07-23.md)

## Bounded verdict

The sole preregistered `retry-1` executed all 435 assigned shard-1 cases and
published a complete inner attempt terminal and shard completion. Together
with the two completed initial shards, the cell now has all 1,305 immutable
result records. The result population has zero known-status contradiction and
zero disagreement with the completed Axeyum and cvc5 cells.

The retry nevertheless has failed outer E2/E3 terminals. After the inner
runner installed shard completion, its final whole-bundle validation read the
zero-record diagnostic terminal left by the original pre-launch failure. That
terminal has no launch manifest, so the strict loader rejected it:

```text
resumable run rejected: terminal has no launch manifest: /nas3/data/axeyum/harness/official-selection-2026-sq/repaired-p0-prep-20260723-75e544a8-v2/cells/bitwuzla/terminals/1/1-1784829799870139753-9f61945e0d6f42b5b11aefb32ad7f393.json
```

This is a post-run evidence-layout/finalization failure, not a solver,
resource, timeout, or result-persistence failure. No second solver retry is
authorized. The only admissible continuation is the process-free,
hash-pinned closure below.

## Execution chronology

The recovery implementation and its exact admission bytes were integrated on
`main`. The first coordinator invocation published the already-authorized
clean-release recovery record, then stopped before a retry attempt because it
passed the parsed command object where the allocation API requires the command
manifest path. Commit `d9607b84` corrected that type/path boundary and passed
28 focused tests plus all 72 portable, mandatory-cgroup, and live-E3 tests.
Merge `2b88b317` integrated the correction. Revalidation against those exact
integrated bytes passed, after which the coordinator launched exactly one
`retry-1` allocation on `s7`.

The retry ran for about 15 minutes 30 seconds. It remained inside the frozen
resource envelope, peaked at 2,266,148,864 bytes and four PIDs, and published
all 435 shard-1 records before the final validation error. The coordinator
retained the failed outer terminals and stopped. There is one recovery record,
one retry allocation attempt, and no second retry attempt.

## Frozen post-retry identity

| Item | Value |
|---|---|
| Preparation completion SHA-256 | `8d9145b2673ee10bf7c38990c20301f13323cfe4ab02c9946b403d0d2e4f4261` |
| Bitwuzla run identity SHA-256 | `f495615511402433ae6eaa7a5b90f4b62ad417fb5b71e7459ce4f66da145fc94` |
| Multi-host plan file SHA-256 | `1a724265a12ecb70bf61f147012e824f63675456096accc38677f6338894e219` |
| Recovery file SHA-256 | `3501ebe1810602771f5731a6e5bc2d0aaff684c7e311739fcd5123745ad7ec8c` |
| Recovery record SHA-256 | `ef46f8d6b0d8f372b0926b34f2d9ab248f81bc933b9227c2f2a714b64dbe623a` |
| Durable records | 1,305 |
| Record-set SHA-256 | `ae55b2d0061ffeb615c2e852d5d16f9e886df780de2e53c79808d5578db3a78f` |
| Canonical bundle SHA-256 after excluding only the diagnostic terminal | `93e62151c9ef8798a9a84bbea80f772b9092b751eff686ae1dfbe249b87cee95` |
| Reported statuses | 432 `sat`, 789 `unsat`, 84 no verdict |
| Terminations | 1,221 completed, 84 wall timeout |
| Known-status contradictions | 0 |
| Cross-solver disagreements | 0 |
| Live shard leases | 0 |
| Resource completion | absent |
| Multi-host completion | absent |
| External Bitwuzla result | absent |

Each shard has exactly 435 records. Shard-completion file identities are:

| Shard | Completion file SHA-256 | Result-set SHA-256 |
|---:|---|---|
| 0 | `2f54b229a9e9b0274beadaac2c474ec7a0569947a3cbf3ce4faab4d6c688ad67` | `4064fe6cc9fcbad169f07cf735bc82280a67a7c50cf6dc6cad6c1a3bf194aac7` |
| 1 | `e838333ac7b6e16526fc20e37d8679deca14b70618f356254c1a7879ffcd53bf` | `78b7772ca17b9fc7b0961669591f4c5802271e7f0135782656676c768f853e9d` |
| 2 | `5d60638f60583c1e19096c0aff732db352af71b023eb61bfa4b86b1096fa0adb` | `9700defd280b82a1417db7c6862acfb671c806127a123f07db83dc62f63eaaef` |

### Successful inner retry evidence

| Artifact | File SHA-256 |
|---|---|
| Shard-1 attempt `1-1784838807213721563-a1914cecdfc641a1a1c3f5c96d79ad1c` | `b362c886340e1b312ed9660a01fd99266aeb8f5d08eee2937685cfed4ec46970` |
| Shard-1 completed terminal | `e22c976eb52b8ca3a57e7c489fc16cdd3ea24f4d9d017a6357c35125158a9400` |
| Shard-1 completion | `e838333ac7b6e16526fc20e37d8679deca14b70618f356254c1a7879ffcd53bf` |

The completed terminal reports 435 durable/new keys, zero skipped keys, zero
missing keys, exit code zero, and result-set SHA-256
`78b7772ca17b9fc7b0961669591f4c5802271e7f0135782656676c768f853e9d`.
Every shard-1 result names that exact attempt.

### Failed outer retry evidence

| Artifact | File SHA-256 | Record SHA-256 |
|---|---|---|
| Retry command | `d0d03b3c5fde3704629c2c27fc22336d31ab5ef3043325814451247ed671505f` | `907a794604b2c9b798346c0d0090e9c6e4299f577756f7ffe373cbe6f6c8aaeb` |
| Allocation attempt | `f95fd96966933b476d240064cc273289fa115af65d0a7a8dd7d5c0706680dccc` | `36d1bc36a50e978dd13625fda208213a61635b4cbb47b3b287ba6420e75240c5` |
| Allocation terminal | `fe06334111bd3b79603cca48d2eda2bc16b4fe1ef38d45cf4a9a9c2bcb1d8bdd` | `e39ac72199dab6f126cf1f39a68bc05cd225cd80e8882fbde8c061e5ef14ad63` |
| Resource preflight | `02983c9970e5d4f2fd778a2cd038215cefc68348d2a46f174501448eef76f04c` | `1ff08a1761cd170a5651bce9694f85cbe501fa715bf9e4aafcfc3b0383cef9b8` |
| Resource terminal | `c7418c31531707a2465186b425262c766e7b2b009e39c5aea7453de835c24dde` | `fac2532e80a99ab7a72cd3a663332466eff4bbd99eab2a89220066fa0e4b8a48` |

The allocation and resource terminals are both honestly retained as failed
with worker/outer exit code 2. The allocation stderr SHA-256 is
`afaf730d63b71829b5c268cd09284bb1088512b4b75b9cc0db1ddba2645eb941`
and binds the exact loader rejection above. The closure must not rewrite either
terminal to `completed`.

### Exact diagnostic artifact

The sole artifact excluded from the otherwise valid generic bundle is:

```text
terminals/1/1-1784829799870139753-9f61945e0d6f42b5b11aefb32ad7f393.json
```

Its file SHA-256 is
`092579dd324cbbf17cebd4c5a49b0e25dcf850b0b8c85e2912bf7fdfece1ac26`.
It is a complete failed-terminal record for zero durable/new/skipped keys and
all 435 shard-1 keys missing, but no corresponding launch manifest was ever
installed. It was written by exception cleanup during the original failure
before the normal attempt-launch boundary. Synthesizing a launch manifest or
deleting this evidence is forbidden.

Read-only liveness checks after retry termination found the registered service
inactive/dead with `MainPID=0` on the retry host and no matching solver,
runner, coordinator, or live lease on `s5`, `s6`, or `s7`.

## Preregistered process-free closure

### 1. Preserve history with explicit closure evidence

Add `axeyum.smtcomp-post-run-validation-closure.v1`. One sealed record under a
dedicated multi-host closure namespace must bind:

- plan, run, recovery, retry allocation, retry attempt, and resource-session
  identities;
- the failed outer allocation and resource terminal file/record identities;
- the allocation stderr identity and exact post-run loader-error class;
- the successful inner runner attempt, completed terminal, shard completion,
  and complete shard result-set identity;
- the diagnostic terminal's original path, exact bytes, absent launch
  manifest, and deterministic quarantine destination;
- the complete 1,305-record set and canonical bundle identity calculated while
  excluding only that named diagnostic terminal;
- absent shard leases plus dead registered service/launcher observation; and
- an observation timestamp and self-seal.

The closure is not a replacement terminal. It explains why an honestly failed
outer finalizer is acceptable only when the underlying runner already completed
the exact frozen shard and the only failing check is the bound diagnostic
artifact.

### 2. Quarantine, never fabricate or erase

After publishing the sealed closure authority, move exactly the diagnostic
terminal to a deterministic path under `quarantine/post-run-validation/` with
`os.replace`, then fsync the source and destination directories. Replay must
accept either the pre-move state or the completed-move state while requiring
exactly one copy with the frozen hash. Both copies, neither copy, a symlink,
another terminal, or a hash mismatch reject.

No result, output sidecar, attempt launch, valid runner terminal, shard
completion, allocation terminal, resource terminal, recovery, or prior-cell
artifact may move or change.

### 3. Close E2/E3 without falsifying outcomes

The generic finalizer must retain and validate all four resource sessions. A
resource completion may include failed closed sessions; only genuinely
terminal-less recovered sessions belong in `unclosed_session_ids`. This
corrects the current validator's assumption that every recovered session is
unclosed, which is false for the already-defined clean-release recovery
variant.

Introduce a versioned multi-host completion that binds the sorted post-run
closure record hashes. For recovery satisfaction only, a retry allocation is
effectively complete when either:

1. its ordinary outer allocation terminal is `completed`; or
2. one exact validated post-run closure binds its failed terminal to a complete
   inner shard attempt/completion and complete canonical bundle.

The original failed terminal remains failed and remains part of the allocation
attempt history. Existing v1 completions and normal completed/lost/failed paths
must validate unchanged.

### 4. One explicit, no-launch coordinator path

Add a Bitwuzla-only closure mode separate from retry execution. It must:

1. require this plan and every closure source byte exact on `origin/main`;
2. acknowledge the frozen preparation completion;
3. hard-pin and revalidate every identity above plus both prior cell results;
4. prove there is exactly one retry attempt, no second retry, no lease, and no
   live registered unit/launcher;
5. publish/replay the closure record and quarantine only the exact diagnostic
   terminal;
6. finalize resource and multi-host evidence without launching a subprocess;
7. recompute the 1,305-row adjudication and require zero contradiction and zero
   cross-solver disagreement;
8. publish raw results and external cell completion last; and
9. validate a second replay byte-for-byte without mutation or process launch.

Any result/evidence drift, live process, new retry attempt, unexpected terminal,
non-complete shard, contradiction, disagreement, or partial closure rejects.

## Required gates

Before any live closure mutation:

- focused tests cover exact closure, pre-move crash replay, post-move replay,
  hash/identity/liveness mutations, duplicate/absent diagnostic artifacts,
  failed inner completion, and a proof that no allocation launcher is called;
- the existing released-recovery test proves closed failed resource sessions
  are not misclassified as unclosed;
- existing v1 normal/loss/retry multi-host evidence remains byte-valid;
- portable, mandatory cgroup, and live multi-host E3 gates pass;
- links, foundational resources, and `git diff --check` pass; and
- this plan, implementation, and frozen checkpoint bytes are integrated on
  `origin/main` by the integration owner.

Only then may the explicit process-free closure mode run. The topic agent must
remain in `agent/smtcomp/full-library-resume`, commit regularly, and neither
merge nor push to `main`.

## Credit boundary

Until the integrated implementation performs and independently validates the
closure, the Bitwuzla cell receives no correctness, performance, coverage, or
parity credit despite its complete inner records. The completed Axeyum and
cvc5 cells remain unchanged and retain their existing bounded credit.

After closure, credit is limited to this repaired P0 population and its frozen
resource policy. A process-free evidence repair does not erase the two harness
incidents, prove official SMT-COMP equivalence, or authorize a larger run.

## Implementation checkpoint

Commit `0eff5d64` implements the preregistered process-free path:

- `axeyum.smtcomp-post-run-validation-closure.v1` binds the failed outer
  allocation/resource evidence, successful inner attempt/completion, exact
  diagnostic terminal, recovery authority, complete record/canonical bundle,
  and dead-unit/launcher observation;
- the closure authority is installed under the quarantine namespace before an
  exact, deterministic, fsynced diagnostic-terminal move;
- crash replay accepts exactly the pre-move or post-move state, while duplicate,
  missing, symlinked, or hash-drifted evidence rejects;
- `axeyum.smtcomp-multi-host-completion.v2` binds the closure record hash while
  retaining the original failed outer terminals unchanged;
- resource completion distinguishes closed failed recovery sessions from
  genuinely terminal-less recovered sessions;
- ordinary v1 completion/loss/retry evidence remains unchanged; and
- the explicit Bitwuzla coordinator mode validates both prior cells, every
  frozen hash above, and the final external result without calling the
  allocation launcher.

The first draft would have broadened `resume_fs.py`, but review removed that
dependency. The generic strict loader is unchanged, and this increment creates
no new Lean live-source pin drift. A disposable byte-for-byte copy of the live
1,305-record run completed the new closure, produced a validating v2 multi-host
completion, and replayed canonical bundle SHA-256
`93e62151c9ef8798a9a84bbea80f772b9092b751eff686ae1dfbe249b87cee95`.
The real NAS run was not changed.

Current gates on committed `0eff5d64`:

```text
python3 -m unittest \
  scripts.tests.test_smtcomp_resume_fs \
  scripts.tests.test_smtcomp_multi_host \
  scripts.tests.test_smtcomp_resource_enforcement \
  scripts.tests.test_smtcomp_p0_prepare
  31 tests, OK

./scripts/check-smtcomp-resume.sh
  75 tests, OK, one live-host skip

AXEYUM_REQUIRE_SMTCOMP_CGROUP=1 ./scripts/check-smtcomp-resume.sh
  75 tests, OK, one live-host skip

AXEYUM_REQUIRE_SMTCOMP_MULTIHOST=1 ./scripts/check-smtcomp-resume.sh
  75 tests, OK, no skips
  evidence=/nas3/data/axeyum/harness/e3-gate/live-1784841036231463027-0eff5d64cc60
  control=514f316102fa4f64cfc90af7e62336a1b0bb774521b6a7a1fa7e7d3172f5a756
  loss=1b665db7f48adf973c4fe28097a5b0242bd42a64d2f1d3728d2d4165516c7994
```

Next: the integration owner green-gates and lands `e9178ed2` plus `0eff5d64`.
After exact `origin/main` revalidation, execute only
`--close-post-run-validation-failure retry-1`; do not launch a solver retry.
