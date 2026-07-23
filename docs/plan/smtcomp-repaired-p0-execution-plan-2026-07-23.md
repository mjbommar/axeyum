# SMT-COMP repaired P0 execution plan

Status: preregistered; preparation only, no solver launched
Date: 2026-07-23
Depends on: [S5.1 admitted-slice result](smtcomp-admitted-slices-s5.1-result-2026-07-23.md)
Execution contract: [accepted ADR-0344](../research/09-decisions/adr-0344-preregister-resumable-distributed-benchmark-execution.md)
Selection contract: [accepted ADR-0356](../research/09-decisions/adr-0356-preregister-official-smtcomp-selection-identity.md)

## Bounded objective

Rerun the complete accepted `QF_FP`, `QF_BVFP`, `QF_ABVFP`, and `QF_AUFLIA`
slices after the two full-library P0 soundness repairs. The only promotion gate
is zero known-status contradictions and zero cross-solver `sat`/`unsat`
disagreements. Unknown, timeout, and unsupported outcomes remain explicit and
receive no decision credit.

This is not the credited full-population run. It does not authorize any other
logic, a different selection, altered limits, or an in-place rerun after a
failure.

## Frozen population

Every run consumes S5.1 manifests derived from accepted completion SHA-256
`322adaa78396bf42d4660d12582e6db1cf2166a765bb912fdfb179975a9c9698`.

| Logic | Files | Physical bytes | Known `sat` | Known `unsat` | No file status |
|---|---:|---:|---:|---:|---:|
| `QF_FP` | 275 | 4,748,038 | 118 | 84 | 73 |
| `QF_BVFP` | 505 | 3,333,275 | 224 | 276 | 5 |
| `QF_ABVFP` | 525 | 24,428,743 | 94 | 419 | 12 |
| `QF_AUFLIA` | 505 | 4,485,241 | 262 | 243 | 0 |
| **Total** | **1,810** | **36,995,297** | **698** | **1,022** | **90** |

The combined absolute list has SHA-256
`e6da1f475ef2674a8461697babaa4e86bce9f3da9d3e7f9b03f0fbf146572e3d`;
its v2 selection-input manifest has SHA-256
`a8cb9ba090b22e658e06dc53b4c97e1cdce595117acc1cbdc7f8476e9e85f4f4`.
The FP-only 1,305-file list and manifest have SHA-256 values
`6025cf1dedfe7e425601f41f10e29ad594ddc083db3f997cb1303e93e70ca801`
and `498184e470072824eaefe46092ff1b2c7228ee23c35b165800a9169a52026041`.

Fresh preparation must reproduce these digests under the same physical S2
corpus root before publishing run manifests.

## Solver cells

Three immutable run identities execute one at a time:

1. Axeyum over all 1,810 files, with a 19-second internal timeout inside the
   20-second runner ceiling.
2. cvc5 1.3.4 over all 1,810 files.
3. Bitwuzla 0.9.1 over the 1,305 FP-family files. `QF_AUFLIA` is outside this
   FP/BV oracle cell and is adjudicated by its official status plus cvc5.

The existing shared reference candidates are:

| Solver | Candidate path | SHA-256 |
|---|---|---|
| cvc5 1.3.4 | `/nas3/data/axeyum/harness/bin/cvc5` | `7562a8b0b835e3eaad5f1a7b4616cd762350cf567b6be03d7e8ee24fa5ced5ee` |
| Bitwuzla 0.9.1 | `/nas3/data/axeyum/harness/bin/bitwuzla` | `d98164badcd34c12ccbbd9e5aab9373854bb187e79f99ccda4ec2aa9951c0eab` |

All three accepted hosts currently observe those exact bytes through the
shared NFS mount. The Axeyum candidate is deliberately not frozen yet: P0-S1
must build it from the clean, integrated post-S5.1 commit, run the sentinel and
repository gates, copy it to a new attempt root, and record its size/SHA-256.
The old shared Axeyum binary (`52661129...`) is not admitted.

## Incident sentinels before distributed launch

The newly built Axeyum binary must first run the three preserved incident
files without modifying them:

| Sentinel | SHA-256 | Required Axeyum outcome |
|---|---|---|
| preserved QF_ABVFP `query.26.smt2` | `6f0b87776052d1770e8503bcc593ad842cc649d533c41fa4a898808397524b8b` | `unsat` |
| preserved QF_BVFP `query.26.smt2` | `31ce580816bfb0647001f64ef480cdd779fe2f31da320354ea1ea63cd9da34ae` | `unsat` |
| official QF_AUFLIA `pipeline-invalid.smt2` | `dc7f8f51be688669321c8a9a15f2543fc070bc3a4c55b81c763604c34fa73bde` | not `unsat`; expected `sat` or honest `unknown` |

The first two historical incident files are not members of the accepted 2026
selection, so they remain prelaunch regression sentinels rather than being
smuggled into the credited slice identity. cvc5 and Bitwuzla confirm the two FP
sentinels; cvc5 confirms the AUFLIA sentinel. Any contradiction stops before a
distributed run.

## Execution identity and resources

- Hosts: `s5`, `s6`, and `s7`; shared hard NFSv4.1 storage and environment
  class must revalidate against the accepted E3 contract.
- Initial shards: shard 0 on `s5`, shard 1 on `s6`, shard 2 on `s7`.
- Preregistered different-host retries: 0 on `s6`, 1 on `s7`, 2 on `s5`.
- Sharding: three striped shards from the exact ordered execution list.
- Per-host concurrency: one worker, one CPU, one active solver run.
- Per-worker memory: 8 GiB; aggregate host-run memory: 8 GiB; zero swap;
  `pids.max=32`.
- Wall limit: 20,000 ms; CPU limit: 20,000 ms; Axeyum internal limit: 19,000 ms.
- Environment: `RAYON_NUM_THREADS=1`, `OMP_NUM_THREADS=1`, and
  `AYU_THREADS=1`; Python and platform identities remain content-bound.
- Run order: Axeyum, cvc5, then Bitwuzla. Do not overlap solver cells.

Read-only inventory on 2026-07-23 found 16 CPUs, approximately 28--29 GB RAM,
Python 3.14.4, cgroup v2, and delegated user systemd on each host. Preparation
must record the fresh observations rather than rely on this prose.

## Publication and failure policy

Each solver receives a new immutable attempt root under
`/nas3/data/axeyum/harness/official-selection-2026-sq/`; no existing S0--S5.1,
E1--E3, stale-run, or binary artifact is overwritten. Inputs, source bundle,
binary copies, run/environment/corpus manifests, host plan, commands, and empty
evidence namespaces are published before launch; completion is published last.

No synthetic host-loss control is repeated. If a real host/allocation fails,
retain its incomplete evidence and use only the preregistered retry mapping.
Any other recovery or identity correction requires a new plan and new root.

Stop all remaining cells immediately on:

- an official known-status contradiction;
- a `sat`/`unsat` disagreement between solvers;
- selected bytes, source, binary, environment, limit, command, or host drift;
- malformed/noncanonical evidence, result conflicts, missing completion, or an
  unaccounted allocation/resource failure; or
- a sentinel failure.

## Exit gates

Successful completion requires:

- 1,810 Axeyum records, 1,810 cvc5 records, and 1,305 Bitwuzla records;
- valid E1/E2/E3 evidence and complete-only raw export for every cell;
- zero known-status contradictions for every admitted solver decision;
- zero cross-solver `sat`/`unsat` disagreements on shared files;
- the three incident sentinels retaining their required outcomes; and
- a compact result document reporting per-logic/per-solver
  sat/unsat/unknown/timeout/error counts without merging nonidentical regimes.

Before P0-S1 preparation:

```sh
./scripts/check-smtcomp-resume.sh
AXEYUM_REQUIRE_SMTCOMP_CGROUP=1 ./scripts/check-smtcomp-resume.sh
AXEYUM_REQUIRE_SMTCOMP_MULTIHOST=1 ./scripts/check-smtcomp-resume.sh
CARGO_BUILD_JOBS=2 CARGO_TARGET_DIR=target-codex \
  cargo build --release --locked -p axeyum-bench --example smtcomp_cli
./scripts/check-links.sh
just foundational-resources
```

Passing this plan review authorizes only P0-S1 preparation and sentinel checks.
Distributed solver launch begins only after a committed preparation result
freezes the integrated source commit, staged Axeyum binary, three run identities,
host plans, and exact external attempt roots.
