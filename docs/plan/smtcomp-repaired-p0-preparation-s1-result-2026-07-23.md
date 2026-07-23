# SMT-COMP repaired P0-S1 preparation result

Status: complete at v2; no distributed solver launched
Date: 2026-07-23
Plan: [repaired P0 execution plan](smtcomp-repaired-p0-execution-plan-2026-07-23.md)
Layout repair: [preregistered repair plan](smtcomp-repaired-p0-runtime-layout-repair-plan-2026-07-23.md)
Operator implementation: `de91aff0`
Integrated source: `be4cb33c41b0bc0e709e783d4f2f3984bd1d46e3`

## Bounded result

P0-S1 v2 is complete. The preparation-only operator reproduced both admitted
selection identities, copied and rehashed all three solver binaries, reran the
eight incident sentinel cells, registered the live `s5`/`s6`/`s7` environment,
and published three empty E3 run namespaces with exact initial and
different-host retry commands.

This v2 root supersedes the unusable v1 preparation. The
[retained v1 incident](smtcomp-repaired-p0-v1-layout-incident-2026-07-23.md)
records why its completed Axeyum records receive no result credit. V2 does not
reuse any v1 record, attempt, timing, terminal, or namespace.

No allocation attempt, resource session, shard attempt, solver record,
multi-host terminal, adjudication, or raw export exists in any v2 cell. The
preparation completion sets `launch_authorized=false`; this document records
reviewable inputs and is not evidence that P0 has run or passed.

## Immutable preparation identity

| Item | Value |
|---|---|
| Attempt root | `/nas3/data/axeyum/harness/official-selection-2026-sq/repaired-p0-prep-20260723-75e544a8-v2` |
| `complete.json` bytes | 29,449 |
| `complete.json` SHA-256 | `8d9145b2673ee10bf7c38990c20301f13323cfe4ab02c9946b403d0d2e4f4261` |
| Completion record SHA-256 | `d3ae8e7cd870c48c19417495aeb99b53ed1a797db58092b79d0828b9255b5f7b` |
| Accepted-selection completion | `322adaa78396bf42d4660d12582e6db1cf2166a765bb912fdfb179975a9c9698` |
| Source identity SHA-256 | `423e45ec8bfb7b28e6cd0db722f2a8a39935b3eec9efe2f7e8a23173e3b13483` |
| Source bundle | `/nas3/data/axeyum/harness/official-selection-2026-sq/source-bundles/4c970d3ec9e94add432cd5322b5619f1c87bb1a7f3dc2de2bde07ee043035091` |
| Environment manifest SHA-256 | `72188709c7ba654593f13ce508073e789afb68a38d386dafd744ee05d2ca5031` |
| Frozen child environment | `AYU_THREADS=1`, `OMP_NUM_THREADS=1`, `RAYON_NUM_THREADS=1` |
| Content-bound attempt artifacts | 50 |

Independent post-publication validation rehashed all 50 artifacts, confirmed
that every cell run manifest is under the immutable `inputs/` namespace,
checked that all 18 host-command manifests name the exact external manifest,
and found zero runtime evidence artifacts. No cell runtime root contains
`run-manifest.json`.

## Selection and binary identities

| Slice | Files | Absolute-list SHA-256 | v2 manifest SHA-256 |
|---|---:|---|---|
| Four-logic union | 1,810 | `e6da1f475ef2674a8461697babaa4e86bce9f3da9d3e7f9b03f0fbf146572e3d` | `a8cb9ba090b22e658e06dc53b4c97e1cdce595117acc1cbdc7f8476e9e85f4f4` |
| FP-family only | 1,305 | `6025cf1dedfe7e425601f41f10e29ad594ddc083db3f997cb1303e93e70ca801` | `498184e470072824eaefe46092ff1b2c7228ee23c35b165800a9169a52026041` |

| Solver | Bytes | Copied binary SHA-256 |
|---|---:|---|
| Axeyum integrated release | 10,121,752 | `d705d700f67cf75c0510dd40b0a1a523ebea5f19acbb037ba24f2875475fb756` |
| cvc5 1.3.4 | 31,866,552 | `7562a8b0b835e3eaad5f1a7b4616cd762350cf567b6be03d7e8ee24fa5ced5ee` |
| Bitwuzla 0.9.1 | 4,490,928 | `d98164badcd34c12ccbbd9e5aab9373854bb187e79f99ccda4ec2aa9951c0eab` |

The union and FP-only values exactly reproduce the S5.1 preregistration. The
Axeyum release bytes also reproduce the pre-operator build because the
integrated layout repair affects only the Python harness and documents, not the
Rust target.

## Sentinel result

| Sentinel | Axeyum | cvc5 | Bitwuzla |
|---|---|---|---|
| QF_ABVFP `query.26.smt2` | `unsat`, completed | `unsat`, completed | `unsat`, completed |
| QF_BVFP `query.26.smt2` | `unsat`, completed | `unsat`, completed | `unsat`, completed |
| QF_AUFLIA `pipeline-invalid.smt2` | no verdict, wall timeout at 20 s | `sat`, completed | outside cell |

Every stdout/stderr byte stream has a content-addressed sidecar. The two FP
sentinels require completed exit-zero `unsat` from all three solvers. The
AUFLIA guard requires completed `sat` from cvc5 and rejects any Axeyum `unsat`;
Axeyum's no-output wall timeout is explicit no-credit behavior, not an
`unknown` decision.

## Host and cell identities

Fresh probes registered `server5`, `server6`, and `server7` in one environment
class:

- toolchain identity SHA-256:
  `66ef2132353367644282baa8d14c9991255716ef5066110e83e38057728dfbda`;
- shared-filesystem class SHA-256:
  `3ed04d2f443e42ff9681dc6184b672c2593b6d38d25127db4afef4efd730d9bf`;
- initial ownership: shard 0 on `s5`, 1 on `s6`, 2 on `s7`;
- registered retries: shard 0 on `s6`, 1 on `s7`, 2 on `s5`.

Each cell has six immutable host-command manifests and the same 20-second,
one-worker, one-core, 8-GiB, three-striped-shard E3 policy.

| Solver | Run identity SHA-256 | Plan identity SHA-256 | Run file SHA-256 | Plan file SHA-256 |
|---|---|---|---|---|
| Axeyum | `5d75bf98f1fe7e8458ac1f5efbd75ea728bd57cff9b0c674002986c6e8dcd2d3` | `1f3adf46565cc627fc534bfb0abeff61fe7480404f138006e77e376c41aea734` | `96930791f801169580e39d67e7ed7e25a9081ad953e6c4237cbbdaa6dbbf0f24` | `2b2429419d3d6c1e9f860da438174c0a6cb70d888227bdc861550327b772b97d` |
| cvc5 | `1d32c45c1371528cf3d4e6bad5801600490f09151ede779bd348de2f124e7745` | `2b48eb57b514e57b2cc46d3df9fb932a3b5c4bcd066540599cf62bd061d75d6f` | `81d82f17c3642e03673e64166cc16bc5f834c395d5e6becc0a7744681bd9c64b` | `3dade51c26d724ec5157b8cf6a09c860c57775a197bc4f961ed45b8a03e630f8` |
| Bitwuzla | `f495615511402433ae6eaa7a5b90f4b62ad417fb5b71e7459ce4f66da145fc94` | `3531135a711b6de1e899e4cfdcda432c68e5ec77387f3e004131579725eec927` | `2c5f26323af8f6b05ff0dcf291323083d7d06848ae42d727e52143d95ee75ccb` | `1a724265a12ecb70bf61f147012e824f63675456096accc38677f6338894e219` |

## Gates

```text
CARGO_BUILD_JOBS=2 CARGO_TARGET_DIR=target-codex cargo build --release --locked \
  -p axeyum-bench --example smtcomp_cli
  passed; exact binary hash above

./scripts/check-smtcomp-resume.sh
  62 tests, OK, one live-host skip

AXEYUM_REQUIRE_SMTCOMP_CGROUP=1 ./scripts/check-smtcomp-resume.sh
  62 tests, OK, one multi-host skip

AXEYUM_REQUIRE_SMTCOMP_MULTIHOST=1 ./scripts/check-smtcomp-resume.sh
  62 tests, OK, no skips
  evidence: /nas3/data/axeyum/harness/e3-gate/live-1784819040016021568-be4cb33c41b0
  control completion: 602cd3549e35ec62228d79d072c340548f44aca3ac05699605617768df94b971
  loss/retry completion: 267959c87e71935c9639d7f9b2363861883df4d006d7f9f8a120b1a7f7b0806c

just foundational-resources
  passed

./scripts/check-links.sh
  passed

git diff --check
  passed
```

## Next boundary

After these exact v2 result bytes are committed and integrated on
`origin/main`, P0 execution may begin in the preregistered order: Axeyum, then
cvc5, then Bitwuzla. The coordinator's exact-byte admission gate must reject
execution before that integration. One coordinator must launch only the three
initial commands for the active cell, retain all failure evidence, use a retry
command only after the existing exact liveness/recovery gate proves the
corresponding initial owner dead, and finalize/export only after all three
shards complete. Solver cells must not overlap.

Any known-status contradiction, cross-solver `sat`/`unsat` disagreement,
identity drift, malformed evidence, or unregistered recovery stops remaining
cells. No P0 correctness, performance, or coverage result is credited by this
preparation.
