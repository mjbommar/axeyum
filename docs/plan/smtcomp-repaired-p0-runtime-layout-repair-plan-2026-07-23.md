# SMT-COMP repaired P0 runtime-layout repair plan

Status: preregistered; failed root retained, no retry authorized
Date: 2026-07-23
Depends on: [P0-S1 preparation result](smtcomp-repaired-p0-preparation-s1-result-2026-07-23.md)
Execution plan: [repaired P0 plan](smtcomp-repaired-p0-execution-plan-2026-07-23.md)

## Incident boundary

The first frozen Axeyum cell computed and durably published all 1,810 records
under the registered three-host resource envelope. Initial allocations 1 and 2
completed. Initial allocation 0 completed its shard, then exited 2 during the
runner's aggregate bundle validation:

```text
resumable run rejected: unexpected run artifact: run-manifest.json
```

The preparation operator had installed its immutable input
`run-manifest.json` inside the mutable evidence root. The E1/E2/E3 bundle
validator correctly rejects that filename because a completed runtime root may
contain only contract-owned evidence artifacts. The live E3 gate did not share
this defect: its run manifest already resides in a separate input directory.

The retained failed root is:

```text
/nas3/data/axeyum/harness/official-selection-2026-sq/repaired-p0-prep-20260723-da679e1429de-v1
```

It has 1,810 records, three shard completions, three resource terminals, and
three allocation terminals. Allocation statuses are `failed`, `completed`,
and `completed`; aggregate resource and multi-host completion were not
published. Its records contain zero known-status contradictions, but the root
receives no E3, P0, performance, coverage, or correctness credit.

The preregistered retry for shard 0 is not used. It would consume the same
frozen command and encounter the same invalid root layout after observing the
existing shard completion. Rewriting, moving, deleting, or exempting the
content-bound input in place is forbidden.

## Exact repair

The next preparation operator revision makes one layout-only change:

1. publish each solver's immutable run manifest under the preparation
   `inputs/` namespace;
2. point the cell's six immutable command manifests at that external input;
3. retain only `multi-host-plan.json` plus contract-created directories in the
   cell runtime root before launch; and
4. record the external run-manifest path and SHA-256 in the preparation
   completion and coordinator validation.

No solver binary, benchmark list, selection manifest, sentinel rule, solver
environment, timeout, memory/CPU/PID limit, host registration, shard mapping,
retry mapping, result schema, or adjudication policy changes.

The correction must not weaken the runtime artifact allowlist. In particular,
do not teach `validate_bundle_directory` to ignore arbitrary coordinator input
files merely to salvage the failed root.

## Gates before a new root

- The tiny preparation test must assert that all three run manifests are under
  `inputs/`, every command names the matching external path, and no prepared
  runtime root contains `run-manifest.json`.
- Mutation of the external manifest or command path must reject before an
  allocation attempt.
- The 62-test portable resumability suite, mandatory E2 gate, mandatory live
  E3 gate, links, foundational resources, Python compilation, and whitespace
  checks must pass from integrated `main`.
- A new preparation root must reproduce both selection hashes, all three
  binary hashes, all eight sentinels, and fresh host/environment identities.
- Independent prelaunch inspection must confirm the exact runtime-root
  allowlist and zero attempts/records for all cells.

## New-root and execution policy

After the repair implementation and result are committed and integrated,
create a new immutable preparation root. Do not copy or resume any record,
attempt, terminal, lease, session, sidecar, completion, or timing from the
failed root. Rerun Axeyum from sequence zero, then cvc5 and Bitwuzla in the
original order only after each preceding cell has valid aggregate completion
and safe adjudication.

Stop again on any unexpected root artifact, non-completed initial allocation,
known-status contradiction, cross-solver disagreement, identity drift, or
unregistered recovery. Any further correction requires another plan and root.
