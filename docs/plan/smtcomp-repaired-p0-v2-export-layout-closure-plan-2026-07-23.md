# SMT-COMP repaired P0 v2 export-layout closure plan

Status: implemented and gated in `5c06ec76`; no closure mutation performed
Date: 2026-07-23
Preparation: [P0-S1 v2 result](smtcomp-repaired-p0-preparation-s1-result-2026-07-23.md)
Prior incident: [v1 runtime-layout incident](smtcomp-repaired-p0-v1-layout-incident-2026-07-23.md)

## Observed stop state

The v2 Axeyum solver execution itself completed. All three preregistered
initial allocations terminated `completed`, all 1,810 selected benchmarks have
one immutable result record, all three shard completions are closed, aggregate
resource and multi-host completions exist, and the coordinator-produced
adjudication reports:

- 450 `sat`, 464 `unsat`, 280 `unknown`, and 616 no-verdict records;
- 1,192 completed processes and 618 wall timeouts;
- zero known-status contradictions;
- zero cross-solver disagreements; and
- `safe_to_continue=true`.

The coordinator then installed `p0-cell-adjudication.json` in the generic run
root and called `export_legacy_raw`. That exporter correctly starts by invoking
the strict generic bundle validator. The validator rejected the coordinator-
owned file with:

```text
P0 cell rejected: unexpected run artifact: p0-cell-adjudication.json
```

This is a second namespace-composition defect, not a solver or runtime-evidence
failure. The base validator's closed allowlist is correct and must not be
widened. The defect is that the P0 coordinator published a derived artifact
inside the generic run-evidence namespace before asking the generic exporter to
validate that namespace.

No cvc5 or Bitwuzla process was launched. No retry was used. No solver process
or matching coordinator remains on `s5`, `s6`, or `s7`.

## Frozen evidence identity

| Item | Value |
|---|---|
| Preparation root | `/nas3/data/axeyum/harness/official-selection-2026-sq/repaired-p0-prep-20260723-75e544a8-v2` |
| Axeyum run identity | `5d75bf98f1fe7e8458ac1f5efbd75ea728bd57cff9b0c674002986c6e8dcd2d3` |
| Records | 1,810 |
| Canonical bundle SHA-256 | `104f27cd184b3aff00e33b2322409fcc707bf7f37f9c6a548e0bb6376f733c6a` |
| `resource-completion.json` file SHA-256 | `99483e252237bf40afd99a556fc4b94a5b079dac36a032acd87a28bd55bcd900` |
| Resource completion record SHA-256 | `2ef457926974aa3684e9bb32a31556a50f2f5266d8c018fba5f396b35815af93` |
| `multi-host-completion.json` file SHA-256 | `8e2463fc157a6324149b2902739f7a282fec11c978b5ba467f6e529014c459cc` |
| Multi-host completion record SHA-256 | `ab0648347ab4b1a34f7f1bef58f3683930805039034ef7bf817f3334f73b5eaa` |
| Observed adjudication file SHA-256 | `fe880b9ae4dc04aeed938ad9e3fd7a350fe326cdba1a97fd6361721f85a6a824` |
| Observed adjudication record SHA-256 | `bf26f54c89d2f09b49155ff13239c1fb87fc165deffa61e6537c6471e5073598` |
| Raw export | absent |
| cvc5 runtime evidence | absent |
| Bitwuzla runtime evidence | absent |

The three shard completions are frozen as follows:

| Shard | Records | Completion file SHA-256 | Result-set SHA-256 |
|---:|---:|---|---|
| 0 | 604 | `8fc09607434e042b280c6fc1b45259c6290345837ea6b72bf4ac1453c044f515` | `7bdb3067084f40cb45d1561920d67dfc78cd17fb1bec8c5f546e57d88c01cde4` |
| 1 | 603 | `660396452b1e115d3311228e85ffa1be5cd8153db075801c708b4d7db000d6b5` | `0dd81a3474fd5855a495aa2125758b40f8c6fdcbb859d814c2fe09cbc1a7bfc0` |
| 2 | 603 | `d3fa627dfaf5d882709d46a0ecd30df310426b851aeef4b0d4b8839f91c4d718` | `1a5a354c6cd3689e6ceafeaeab30541084c62f4f75fc866fcc2398297615ea9d` |

The three allocation-terminal file SHA-256 values are:

- `initial-0`: `3901cc06a407575c01c234aced5084a17329d328189e985baed0f09beee77a95`;
- `initial-1`: `77d7774047ca83d735984d0d6707094536eff37b4cca728d6caa9e38fde8563d`;
- `initial-2`: `813fc263830e224f48d5d63c2e1635f60e6a626b5793141f572d9ad2a8a60909`.

These runtime records, timings, sidecars, attempts, terminals, and completions
are frozen. The repair must neither rerun a solver nor rewrite any of them.

## Credit boundary

The frozen runtime completion and safe adjudication are necessary but not yet
sufficient for P0 cell credit. The required raw export and coordinator-level
completion are absent, and the generic run root currently contains one
unexpected coordinator artifact. Therefore:

- no Axeyum P0 correctness, performance, or coverage credit is claimed yet;
- cvc5 remains blocked;
- the v2 Axeyum records are not discarded or called diagnostic-only; and
- a process-free, hash-pinned closure may make this same completed v2 cell
  creditable if every gate below passes.

This is not reuse across attempts. It is completion of the already closed v2
cell's derived-artifact publication, with its exact runtime evidence unchanged.

## Preregistered repair

### 1. Separate coordinator outputs

For every P0 cell, publish coordinator-owned artifacts under:

```text
<preparation-root>/cell-results/<solver-id>/
```

The namespace contains only:

- `p0-cell-adjudication.json`;
- `raw-results.json`; and
- completion-last `complete.json` using
  `axeyum.smtcomp-repaired-p0-cell-result.v1`.

Fresh cells must never install these files in the generic run root. The generic
run validator and `load_bundle` allowlists remain unchanged.

### 2. Completion-last cell result

The external `complete.json` must bind at least:

- preparation completion file SHA-256;
- solver ID and run identity;
- canonical bundle SHA-256;
- resource- and multi-host-completion file and record SHA-256 values;
- adjudication file and record SHA-256 values;
- raw-export file SHA-256 and exact row count; and
- a `safe_to_continue` value copied from a freshly recomputed adjudication.

It is installed only after the generic run bundle, adjudication, raw export,
and all referenced hashes validate. A conflicting pre-existing output is an
error; byte-identical replay is idempotent.

### 3. Exact process-free v2 closure

The one-time closure path for this observed Axeyum cell must:

1. require the exact preparation, run, completion, shard, allocation-terminal,
   and observed adjudication hashes frozen above;
2. recompute and byte-compare the adjudication before changing any path;
3. atomically install those exact adjudication bytes in
   `cell-results/axeyum/`;
4. move only the exact legacy top-level adjudication into the existing ignored
   quarantine namespace under a content-bound migration name;
5. run the unchanged strict generic validator and reproduce canonical bundle
   SHA-256 `104f27cd…3c6a`;
6. create and validate the complete 1,810-row raw export outside the run root;
7. install external completion last; and
8. rerun all validation idempotently without launching a process.

Any hash mismatch, extra top-level artifact, missing record/sidecar, changed
adjudication, malformed raw row, conflicting external file, or incomplete
resource/multi-host state rejects without granting credit. The closure may not
delete evidence or silently accept an arbitrary unexpected artifact.

### 4. Subsequent-cell admission

The coordinator may admit cvc5 only after validating Axeyum's external
completion and recomputing its adjudication and raw population. Bitwuzla
similarly requires validated Axeyum and cvc5 external completions. Solver cells
must remain sequential and non-overlapping.

## Required tests and gates

Before operating on the live v2 cell:

1. a fresh fixture cell closes with no coordinator artifact in the generic run
   root;
2. the exact legacy-layout fixture migrates process-free and is byte-identical
   on replay;
3. injected interruption after external adjudication, after quarantine move,
   and after raw export resumes to the same completion;
4. wrong frozen hashes, wrong adjudication, malformed/missing raw rows,
   conflicting outputs, premature completion, and arbitrary top-level files
   reject;
5. the unchanged base validator still rejects unregistered artifacts;
6. portable, mandatory cgroup E2, and live multi-host E3 suites pass;
7. links, foundational resources, and `git diff --check` pass; and
8. implementation and live-closure result bytes are separately integrated on
   `origin/main` before cvc5 launch.

## Implementation checkpoint

Commit `5c06ec76` implements only the preregistered boundary:

- deterministic legacy raw bytes are now separable from their destination;
- fresh coordinator outputs publish under `cell-results/<solver-id>/`;
- `complete.json` binds the preparation, generic bundle, resource completion,
  multi-host completion, recomputed adjudication, and exact raw export;
- the one-time Axeyum v2 closure hard-codes every frozen hash above, moves only
  the exact legacy adjudication to a content-bound quarantine path, and launches
  no process;
- later-cell admission requires validated external prior-cell completion; and
- every future launch requires the closure plan and repaired coordinator/export
  sources to be byte-identical to `origin/main`.

The exact live freeze validates read-only before migration:

```text
FROZEN_AXEYUM_V2_VALID|adjudication_bytes=493
```

Committed gates:

```text
python3 -m unittest scripts.tests.test_smtcomp_p0_prepare
  7 tests, OK

./scripts/check-smtcomp-resume.sh
  65 tests, OK, one live-host skip

AXEYUM_REQUIRE_SMTCOMP_CGROUP=1 ./scripts/check-smtcomp-resume.sh
  65 tests, OK, one multi-host skip

AXEYUM_REQUIRE_SMTCOMP_MULTIHOST=1 ./scripts/check-smtcomp-resume.sh
  65 tests, OK, no skips
  evidence: /nas3/data/axeyum/harness/e3-gate/live-1784826604526363736-5c06ec7606e2
  control completion: 818420d35b2986d4286c70d09d8feb78e8e47180dd45f6db3fd77811efa4c8c5
  loss/retry completion: 2c701bf7cde0f4d8b6a8fabd6e303d39b8aa2d2bcf4dd9f6840ccb115caa1f8e

just foundational-resources
  passed

./scripts/check-links.sh
  passed

git diff --check
  passed
```

The failed pre-commit E3 invocation is not a gate result: it correctly refused
to run from a dirty worktree. The committed rerun above is the qualifying E3
evidence.

## Next boundary

The preregistration is integrated and the bounded implementation is committed,
gated, and pushed. After the implementation and these exact checkpoint bytes
are integrated, run the closure once against the
frozen Axeyum v2 cell, independently validate and document its result, and
integrate that result. Only then may the frozen cvc5 cell start.
