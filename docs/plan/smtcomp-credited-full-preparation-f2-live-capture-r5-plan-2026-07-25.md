# SMT-COMP credited full-population F2 live-capture R5 plan

Status: preregistered; implementation, integration, and live F2 remain
prohibited

Date: 2026-07-25

Parent:
[F2 live-capture plan](smtcomp-credited-full-preparation-f2-live-capture-plan-2026-07-24.md)

Prior corrections:
[R1](smtcomp-credited-full-preparation-f2-live-capture-r1-plan-2026-07-24.md),
[R2](smtcomp-credited-full-preparation-f2-live-capture-r2-plan-2026-07-24.md),
[R3](smtcomp-credited-full-preparation-f2-live-capture-r3-plan-2026-07-25.md),
and
[R4](smtcomp-credited-full-preparation-f2-live-capture-r4-plan-2026-07-25.md)

Durability authority:
[accepted ADR-0344](../research/09-decisions/adr-0344-preregister-resumable-distributed-benchmark-execution.md)

## Why this correction exists

The parent plan requires a fresh release build from the exact integrated
commit after C0. The current operator instead accepts a caller-selected
`--axeyum-binary`, copies and hashes those bytes, and assigns version label
`integrated-release-<readiness-commit>`. The composition and completion bind
the source identity and binary hash independently, but no retained record
proves that the executable was produced from that source.

The live-only frozen executable table closes this question for cvc5 and
Bitwuzla, but deliberately contains no Axeyum hash because Axeyum must be built
from the then-current integrated commit. The fixture end-to-end operator also
demonstrates the missing relation by completing with arbitrary executable
Axeyum bytes. That fixture behavior is valid for test isolation; the defect is
that live mode adds no source-build authority beyond the caller-supplied path.

Therefore a stale, substituted, or locally modified executable can receive the
integrated-release label while every current binary, run-identity, sentinel,
artifact-ledger, and completion hash remains internally consistent. The
separate documented shell command is a human procedure, not replayable
evidence. No live binary, host, sentinel, NAS root, acceptance, allocation, or
solver wave was used to find this gap.

R5 closes only the exact-source Axeyum build-provenance gap. All C0--C5 and
R1--R4 source, gate, selection, host, thermal, sentinel, deadline, exact-main,
completion-last, and no-launch requirements remain unchanged.

## R5.1: operator-owned clean exact-source build

Live mode must not accept an Axeyum executable path from the caller. After C0
and repaired-P0 replay, but before creating the shared attempt directory or
starting the 30-minute capture interval, the registered operator must:

1. create a unique local temporary Cargo target directory outside the source
   repository and shared preparation root;
2. resolve and seal the canonical Cargo and Rust compiler executables;
3. run exactly one registered offline locked release build for package
   `axeyum-bench`, example `smtcomp_cli`, with two build jobs;
4. use a constructed non-secret environment rather than ambient compiler,
   loader, wrapper, target, network, or credential settings;
5. require an exit-zero build and a regular, executable, non-symlink output at
   the exact target path; and
6. recheck the clean local/tracking/live-remote exact-main identity before any
   shared attempt path is created.

The logical build is:

```sh
cargo build --release --locked --offline \
  -p axeyum-bench --example smtcomp_cli
```

The registered environment fixes `CARGO_BUILD_JOBS=2`, points
`CARGO_TARGET_DIR` at the unique temporary directory, and explicitly selects
the sealed compiler executable. Account, toolchain, path, locale, Python, and
terminal controls follow R4's positive non-secret construction. Arbitrary
`RUSTFLAGS`, encoded flags, wrappers, incremental settings, loader paths,
target overrides, remap options, network/proxy settings, and credentials are
absent. A dependency missing from the already exercised locked offline cache
is a rejection, not permission to use the network.

The built bytes are read from the private temporary directory and installed as
the Axeyum binary beneath the new attempt. The temporary build tree receives no
measurement credit and is removed after staging. Live mode cannot fall back to
a caller path or an earlier build. Fixture mode may inject a bounded builder,
but live mode must require the registered implementation and runtime hooks.

## R5.2: sealed build observation and replay

The preparation schema advances to v3 and gains one
`axeyum.smtcomp-credited-full-axeyum-build.v1` observation. It records and
seals:

- the exact source commit and repository root;
- the unchanged logical build command;
- the complete constructed environment and canonical digest;
- canonical Cargo and Rust compiler paths, byte counts, and SHA-256 values;
- start/end timestamps, exit code, and exact stdout/stderr byte counts and
  SHA-256 values; and
- the produced `smtcomp_cli` byte count and SHA-256.

The build stdout and stderr are installed as exact-byte sidecars beneath the
attempt before publication. The observation, sidecars, staged Axeyum binary,
Axeyum run identity, readiness commit, and completion must all agree. The
version label is derived only after that relation validates. Current-state
capture checks external tool bytes; durable replay validates the retained
observation and products without pretending mutable Cargo/Rust compiler bytes
were copied into the preparation.

Build failure, source/ref/worktree drift, missing output, path escape,
executable mutation, observation mutation, output-sidecar mutation, or any
source/binary/run/completion mismatch rejects before `complete.json`. A failure
before shared attempt creation leaves no shared path; a later failure preserves
the incomplete append-only attempt under the existing rules.

## R5.3: mutation and integration gates

Focused coverage must prove:

1. live mode cannot accept, infer, or fall back to a caller-selected Axeyum
   executable;
2. the build command, unique target, two-job limit, offline/locked flags,
   constructed environment, and Cargo/Rust compiler identities are exact;
3. representative ambient compiler, loader, wrapper, target, network, Python,
   skip, and credential variables are absent;
4. nonzero exit, missing/non-regular/non-executable/symlink output, source
   mutation, dirty tree, or ref drift rejects before shared mutation;
5. every build-observation field, output sidecar, staged Axeyum byte, run
   identity, readiness commit, and completion link has a rejecting mutation;
6. both oracle hashes, all eight sentinels, capture ordering, deadline,
   completion-last, and empty execution namespaces remain unchanged; and
7. the live module retains no admission, allocation, host-unit, or solver-wave
   path.

Required gates are:

```sh
PYTHONWARNINGS=error python3 -m unittest \
  scripts.tests.test_smtcomp_full_population
./scripts/check-smtcomp-resume.sh
python3 scripts/gen-smtcomp-resume-contract.py --check
just check-scope origin/main
./scripts/check-links.sh
```

The final corrected topic must pass `just check` from a clean pushed
implementation and leave the source worktree and tracked frontier artifacts
clean. The integration owner must land the complete corrected stack on
repaired green exact main and pass the combined full gate before C0 or the new
build may run. C5, live hosts, sentinels, NAS mutation, F3 acceptance,
allocation, and solver execution remain separately prohibited.

## Stop conditions

Stop source-first if the exact offline build cannot be isolated, toolchain
identity is ambiguous, the source tree changes, executable bytes cannot be
linked through every retained layer, or any mutation control fails. Do not
restore the caller-selected binary, widen the environment, use a networked
build, infer freshness from mtime or filename, or perform any live F2 action
from this topic.
