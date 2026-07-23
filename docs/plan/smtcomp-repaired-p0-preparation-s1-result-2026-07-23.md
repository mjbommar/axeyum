# SMT-COMP repaired P0-S1 preparation result

Status: complete; no distributed solver launched
Date: 2026-07-23
Plan: [repaired P0 execution plan](smtcomp-repaired-p0-execution-plan-2026-07-23.md)
Operator implementation: `b226652f`
Integrated source: `da679e1429de9d55effad35e6608d54ddb1d8fcd`

## Bounded result

P0-S1 is complete. The preparation-only operator reproduced both admitted
selection identities, copied and rehashed all three solver binaries, reran the
eight incident sentinel cells, registered the live `s5`/`s6`/`s7` environment,
and published three empty E3 run namespaces with exact initial and
different-host retry commands.

No allocation attempt, resource session, shard attempt, solver record, or
multi-host terminal exists in any prepared cell. The preparation completion
sets `launch_authorized=false`; this document records reviewable inputs and is
not evidence that P0 has run or passed.

## Immutable preparation identity

| Item | Value |
|---|---|
| Attempt root | `/nas3/data/axeyum/harness/official-selection-2026-sq/repaired-p0-prep-20260723-da679e1429de-v1` |
| `complete.json` bytes | 29,191 |
| `complete.json` SHA-256 | `63c153f2c84c82d5363bdcec648b39a19d7c43308874b7549ba2e16687b5d76b` |
| Completion record SHA-256 | `c3c4c45d7916aad818e9196ee3975282465e0413b8f8359391cddc70d29a8c3a` |
| Accepted-selection completion | `322adaa78396bf42d4660d12582e6db1cf2166a765bb912fdfb179975a9c9698` |
| Source identity SHA-256 | `a4aa9b774cb07079160a371f5c0b570aaba08a7f570eeb01d70ad8e005119b10` |
| Source bundle | `/nas3/data/axeyum/harness/official-selection-2026-sq/source-bundles/5b4c24fdc0f6fa69f5f9f92d991ebd48660b2172861c7298d282142f7db2467d` |
| Environment manifest SHA-256 | `72188709c7ba654593f13ce508073e789afb68a38d386dafd744ee05d2ca5031` |
| Frozen child environment | `AYU_THREADS=1`, `OMP_NUM_THREADS=1`, `RAYON_NUM_THREADS=1` |
| Content-bound attempt artifacts | 50 |

Independent post-publication validation rehashed all 50 artifacts, revalidated
the source bundle, and confirmed zero files in each cell's `records`,
`attempts`, and `multi-host-attempts` namespaces.

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
integrated preparation changes affect only the Python harness and documents,
not the Rust target.

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
| Axeyum | `03966268266c31fceee7e9eb8d8c5610b137462a5d62bb24a432c00bd828efd8` | `7f119f954accd5c1652dc4bcd16a2e80bf0092f7001f173645123caaf00f7690` | `eebd046c6373e06935a3dae0b435a8c079f0b0ca857b992ca59b16a95fefe9fe` | `a06fad16d6c491dd89645981c88804756d7d219d2c8f3296b8f03781cd13ab40` |
| cvc5 | `ba0b5d22a31b6271456a0be6a6b716b9b09575b8571b115abe9978453294fce7` | `89668c324b4f7f6bde669ecaf027038d6563bcb001ec35d9627f4217695ccec9` | `f54bdf25b685a58d630e1943c68e800058c293b9f4e9710b0cb6251c0100b7a5` | `aebbfa540f7e8c1f62f8053fecf744d51c1e260e1188c0449b73418bcbba4f18` |
| Bitwuzla | `15c63870992b2fd372129e98ba188e5c5e4a20733c88f4797904900adf0f45b6` | `87b8086ebb93ca15b78c69824a3475be1738819ba505f8bc96e82f92155d3d92` | `c610e51f72d3a8ad62dda884fe8d2c77e6a859089412f7fec03782102b3fcd22` | `9875fbca92644a00895f948c7560c5ec71a56dfd5190d025977fa8f31fabbdc3` |

## Gates

```text
CARGO_BUILD_JOBS=2 CARGO_TARGET_DIR=target-codex cargo build --release --locked \
  -p axeyum-bench --example smtcomp_cli
  passed; exact binary hash above

./scripts/check-smtcomp-resume.sh
  60 tests, OK, one live-host skip

AXEYUM_REQUIRE_SMTCOMP_CGROUP=1 ./scripts/check-smtcomp-resume.sh
  60 tests, OK, one multi-host skip

AXEYUM_REQUIRE_SMTCOMP_MULTIHOST=1 ./scripts/check-smtcomp-resume.sh
  60 tests, OK, no skips
  evidence: /nas3/data/axeyum/harness/e3-gate/live-1784811785919018559-da679e1429de
  control completion: 8d84004a667ca78cf3a869c16e5816aca87881aca69adcd1e73edd251ce16a83
  loss/retry completion: 2a2f98a5d9285930944fb72b44771af3e2ab38498c4cd2d611fe5882468dc50c

just foundational-resources
  passed

./scripts/check-links.sh
  passed
```

## Next boundary

After this result is committed and integrated, P0 execution may begin in the
preregistered order: Axeyum, then cvc5, then Bitwuzla. One coordinator must
launch only the three initial commands for the active cell, retain all failure
evidence, use a retry command only after the existing exact liveness/recovery
gate proves the corresponding initial owner dead, and finalize/export only
after all three shards complete. Solver cells must not overlap.

Any known-status contradiction, cross-solver `sat`/`unsat` disagreement,
identity drift, malformed evidence, or unregistered recovery stops remaining
cells. No P0 correctness or coverage result is credited by this preparation.
