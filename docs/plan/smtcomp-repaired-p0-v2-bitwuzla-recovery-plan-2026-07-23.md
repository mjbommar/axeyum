# SMT-COMP repaired P0 v2 Bitwuzla recovery plan

Status: preregistered; implementation complete and portable-gated; no recovery
mutation or retry launch performed
Date: 2026-07-23
Predecessor: [cvc5 result](smtcomp-repaired-p0-v2-cvc5-result-2026-07-23.md)
Preparation: [P0-S1 v2 result](smtcomp-repaired-p0-preparation-s1-result-2026-07-23.md)

## Observed stop state

After merge `0f7cdac1` integrated the cvc5 result and Bitwuzla admission gate,
the coordinator launched exactly the three frozen Bitwuzla initial allocations.
`initial-0` and `initial-2` completed their 435-record shards. `initial-1`
failed before publishing a shard-1 result because concurrent shard startup
exposed a shared-directory orphan-temporary recovery race. The exact stderr is:

```text
resumable run rejected: [Errno 2] No such file or directory: '<records temp>' -> '<quarantine orphan>'
```

The runner acquires a per-shard lease, but startup currently scans every
temporary file in the shared `records/` directory. One shard may therefore try
to quarantine another live shard's atomically published temporary. In this
observation the target disappeared between scan and move. The runner wrote a
typed failed shard terminal and released its lease in `finally`; the outer host
allocation retained a typed failed terminal. The coordinator then waited for
the other initial allocations, retained all evidence, and rejected with:

```text
P0 cell rejected: P0 cell has a failed/lost allocation; exact recovery required
```

No Bitwuzla or coordinator process remains on `s5`, `s6`, or `s7`. No retry was
launched. No recovery authority, shard-1 completion, resource completion,
multi-host completion, adjudication, raw export, or external cell completion
exists.

## Frozen identity

| Item | Value |
|---|---|
| Preparation completion SHA-256 | `8d9145b2673ee10bf7c38990c20301f13323cfe4ab02c9946b403d0d2e4f4261` |
| Bitwuzla run identity SHA-256 | `f495615511402433ae6eaa7a5b90f4b62ad417fb5b71e7459ce4f66da145fc94` |
| Multi-host plan file SHA-256 | `1a724265a12ecb70bf61f147012e824f63675456096accc38677f6338894e219` |
| Multi-host plan record SHA-256 | `3531135a711b6de1e899e4cfdcda432c68e5ec77387f3e004131579725eec927` |
| Durable records | 870 |
| Record-set SHA-256 | `feb2021200f8b12042cf58416e2f12459f2d740aaebf67fd9dfa19527cefe70c` |
| Shard 0 records | 435 |
| Shard 1 records | 0 |
| Shard 2 records | 435 |
| Reported statuses | 285 `sat`, 532 `unsat`, 53 no verdict |
| Terminations | 817 completed, 53 wall timeout |
| Known-status contradictions | 0 |
| Live shard lease files | 0 |
| Recovery records | 0 |

Initial allocation terminal identities are:

| Allocation | Status | Terminal file SHA-256 | Terminal record SHA-256 |
|---|---|---|---|
| `initial-0` | completed | `6047e12bad9c1db8662176e387d35bf3e1591b2124d14a0bbf23497b0216f5c7` | `38870bedfde3381387f20bd694f303a81a7853151807541a2e8751e661a36f80` |
| `initial-1` | failed | `879d3fdcf87aca603fc14c5984bd42be2528fe7b14f6ac7506486bc4f14d54ec` | `e1e03fa91750ac8a0f0d2dca6f841e74e3ec3ef133192972d54802b1e703bd35` |
| `initial-2` | completed | `30c7451d170899d64bf1fb7098a06e8edc84dce7d5248ab5cca168b3c0d6110d` | `fc90a921265c0431183c229305285e7cf507609b65b8282631e11a62ad378aab` |

The failed allocation binds stderr SHA-256
`d536bb18a81354f9e0077c0f81f8172f4a4773725d8099922abb7df026fa620a`.
Its zero-record runner terminal file SHA-256 is
`092579dd324cbbf17cebd4c5a49b0e25dcf850b0b8c85e2912bf7fdfece1ac26`.
Its resource session is `p0-bitwuzla-initial-1-f49561551140`, whose preflight
record SHA-256 is
`5b641f004abb26a6e2a538b7c021df81c95657ede00bc4a2e45b2e2c6083f713`.
That session also has a valid failed resource terminal with worker exit codes
`[2]`: file SHA-256
`e39e1e5cc665315b6b3bb6f96a80ea57303510255c8a858c544a233431a4ae43`
and record SHA-256
`6e7cf1b693c26fa6651de86f2c66e9c0c86086b4635291092d202c5e9d213df5`.

Completed shard files are:

| Shard | Completion file SHA-256 |
|---:|---|
| 0 | `2f54b229a9e9b0274beadaac2c474ec7a0569947a3cbf3ce4faab4d6c688ad67` |
| 2 | `5d60638f60583c1e19096c0aff732db352af71b023eb61bfa4b86b1096fa0adb` |

The only eligible retry is frozen `retry-1`: command file SHA-256
`d0d03b3c5fde3704629c2c27fc22336d31ab5ef3043325814451247ed671505f`,
command record SHA-256
`907a794604b2c9b798346c0d0090e9c6e4299f577756f7ffe373cbe6f6c8aaeb`,
session `p0-bitwuzla-retry-1-f49561551140`, shard 1 on `s7`. This is the
preparation's preregistered different-host mapping from failed `initial-1` on
`s6`.

## Preregistered repair

### 1. Scope orphan recovery to the owned shard

The runner must derive the exact assigned result filenames before acquiring the
shard lease and pass that closed set to orphan-temporary recovery. Once the
lease is held, startup may inspect and quarantine temporary files only when the
target result filename belongs to that shard. It must ignore temporary files
owned by every other shard. The generic atomic-install and quarantine formats
remain unchanged.

Tests must prove that two shard startups cannot quarantine each other's live
temporaries, that an owned orphan is still recovered, and that arbitrary or
malformed temporary names are not admitted.

### 2. Represent cleanly released failed-allocation recovery

The existing recovery record covers a dead owner with a stale lease. This
failure is different: remote liveness is false, the runner emitted an exact
failed terminal, and its `finally` block cleanly released the lease. Add a
separate fail-closed recovery evidence variant that binds:

- plan, run, failed allocation, retry allocation, resource session, and shard;
- failed outer terminal file/record identity;
- failed resource terminal file/record identity and matching worker exit code;
- failed inner runner terminal file/identity and zero durable shard records;
- exact remote liveness observation;
- the assertion that the shard lease is absent; and
- the preregistered different-host retry command.

It must not synthesize stale-lease quarantine evidence. Existing stale-lease
recovery remains valid and unchanged. Any live process, present lease, missing
or non-failed terminal, durable shard-1 record, wrong retry mapping, or identity
drift rejects.

### 3. Expose one exact coordinator recovery mode

Add a recovery-only coordinator mode that:

1. requires this plan and its coordinator/runner/recovery sources to be exact on
   `origin/main`;
2. hard-pins and revalidates every frozen identity above plus both prior cell
   completions;
3. publishes only the clean-release recovery authority;
4. launches only `retry-1` and waits for its terminal;
5. on success, finalizes the generic bundle and multi-host/resource evidence,
   adjudicates all 1,305 Bitwuzla records, and publishes the external cell result
   completion last; and
6. on any failure, preserves evidence and stops without another retry.

Replay after completion must validate without launching a process. No Axeyum or
cvc5 evidence may be changed.

## Gates and credit boundary

Before live recovery:

- focused concurrent-orphan and clean-release recovery tests pass;
- portable, mandatory cgroup, and live multi-host E3 gates pass;
- links, foundational resources, and `git diff --check` pass; and
- this plan, the implementation, and checkpoint bytes are separately integrated
  on `origin/main`.

The current 870 records receive no Bitwuzla correctness, performance, coverage,
or parity credit. The completed Axeyum and cvc5 cells remain unchanged and
credit-eligible under their own integrated result boundaries.

## Implementation checkpoint

The bounded implementation:

- scopes startup orphan recovery to the current shard's exact assigned result
  filenames, leaving every foreign or malformed temporary untouched;
- adds `axeyum.smtcomp-host-released-recovery.v1`, which binds the failed outer
  allocation terminal, failed resource terminal, zero-record inner runner
  terminal, absent lease, dead process observation, and exact different-host
  retry without fabricating stale lease quarantine;
- preserves and continues to validate the existing stale-lease recovery schema;
- adds a Bitwuzla-only `--recover-failed-allocation initial-1` coordinator mode
  with every frozen live hash above hard-pinned;
- requires this plan and all recovery-source bytes to be exact on `origin/main`;
  and
- validates replay after authority publication, process-free finalization after
  a completed retry, and a fully published result without launching twice; and
- directly exercises all three coordinator restart paths: fresh exact retry,
  completed-retry finalization, and completed-result replay. Authority replay
  repeats current remote-liveness, lease, allocation-evidence, runner-terminal,
  and zero-record checks before returning the existing record. The runner
  terminal must have the complete contract field set, exact empty-result digest,
  and all shard-assigned keys in its missing set.

Read-only live validation reports:

```text
FROZEN_BITWUZLA_RECOVERY_VALID
plan=3531135a711b6de1e899e4cfdcda432c68e5ec77387f3e004131579725eec927
retry=retry-1
```

Current gates:

```text
python3 -m unittest \
  scripts.tests.test_smtcomp_resume_fs \
  scripts.tests.test_smtcomp_multi_host \
  scripts.tests.test_smtcomp_resource_enforcement \
  scripts.tests.test_smtcomp_p0_prepare
  28 tests, OK

./scripts/check-smtcomp-resume.sh
  72 tests, OK, one live-host skip

AXEYUM_REQUIRE_SMTCOMP_CGROUP=1 ./scripts/check-smtcomp-resume.sh
  72 tests, OK, one live-host skip

AXEYUM_REQUIRE_SMTCOMP_MULTIHOST=1 ./scripts/check-smtcomp-resume.sh
  72 tests, OK, no skips
  evidence=/nas3/data/axeyum/harness/e3-gate/live-1784833951553616481-378813e09840
  control=4574cfc31d1dbe905510d4fe629b1e62d8e779ebcc3745a7078fc87973f034a0
  loss=fc5f11d24804ce1d1f8a9d9d948dc6c10eeae3676570742d8f86a79898f26fe0

./scripts/check-links.sh
  passed

just foundational-resources
  passed

git diff --check
  passed
```

Next: integrate the implementation/checkpoint bytes, revalidate the frozen stop
state against the integrated source, then execute only `retry-1`.
