# TL0.7.4 plan — no-credit pinned Lean/export acceptance controls

Status: **preregistered; no Lean compilation or exporter control has run**

Date: 2026-07-22

Owner: complete Lean-parity documentation/evidence lane

Parent:

- [TL0.7 execution-evidence plan](lean-execution-evidence-tl0.7-plan-2026-07-22.md)
- [TL0.7.2 process-adapter result](lean-execution-process-tl0.7.2-2026-07-22.md)
- [TL0.7.3 checkpoint-store result](lean-execution-store-tl0.7.3-2026-07-22.md)
- [`TL0.7.4`](lean-system-implementation-plan-2026-07-21.md#tl07-lean-execution-evidence-slices)
- [ADR-0345](../research/09-decisions/adr-0345-preregister-lean-system-interoperability.md)

## 1. Decision boundary

TL0.7.4 accepts or revises the complete local execution path with two actual
but structurally **no-credit** external controls:

1. compile the committed flat probe with the exact pinned Lean 4.30 executable
   under the 4 GiB lane; and
2. export that compiled module with a source-built, pinned `lean4export`
   v4.30.0 executable under the 8 GiB lane and require exact equality with the
   committed 65-line NDJSON reference.

This slice proves that a real Lean compiler process and a real official
exporter process can pass through the preregistered resource, attempt,
artifact, immutable-store, and completion-last boundaries. It does **not** run
an official U2 test, CTest, an Axeyum importer/checker, a paired comparison, or
a performance experiment. Neither control may create an official or Axeyum
outcome, U2 denominator, paired cell, performance row, axis/gate credit, or
parity credit.

An identity-only `lean --version` observation and read-only exporter source
census were performed while writing this plan. No Lean source compilation,
`.olean` creation, exporter build, or export process has run for TL0.7.4. The
plan must be committed and pushed before any of those actions.

## 2. Frozen repository and installed-tool inputs

Implementation begins from published topic revision
`2ba05ec17699344ced3cd56546d4d77de9c608f3`. The first result must bind these
current bytes:

| Input | SHA-256 | Role |
|---|---|---|
| `lean-execution-evidence-v1.json` | `83fbfeaf6baa4c1bd747ce80bba87a15aaf159bb164a7647cc8e3155282fa05a` | lane, record, completion, and credit contract |
| `lean-execution-process-v1.json` | `0fc2d552f8594e2285eef2f0307a9b4d5313024166f0256486b731366947c0bf` | accepted synthetic process-result boundary |
| `scripts/lean_execution_process.py` | `96f6866f619563e9fc639ca360f40260d2c35b521b3fc67941675d22984b2007` | process/resource/platform mechanism dependency; read-only predecessor |
| `lean-execution-store-v1.json` | `e167c2054537d628bf1e0621bd6fb864bc8f38847aaf690b8767687ef1d1a647` | accepted ext4/tmpfs process-interruption result |
| `scripts/lean_execution_store.py` | `06d388a49d927a2f1b65a4632cd6297b140a579cf80edd5177fc6849b62ec679` | storage-class/preflight dependency; read-only predecessor |
| `scripts/smtcomp_repro/resume_fs.py` | `1968e7b6424c2dd9273bff5041e96fc21b83ec01b2205dcc840d5dc942be1aec` | frozen no-replace JSON/byte installation primitive |
| `lean-toolchain` | `54727eec5cba149c18842e6deb5c41b369d66455c93ce135d7d5347c782b2325` | exact `leanprover/lean4:v4.30.0` selection |
| `scripts/install-pinned-lean.sh` | `75acb49a48e18b43523257ac22bc82889d614a6678c1cc3a457b3a150e1c7f71` | checksum-pinned Linux x86-64 installer boundary |
| installed pinned `bin/lean` | `3e0d0d3d801675359f2d4cf9815bfdb417b20b92fdd9d48b3b14c95bbae28bbf` | exact 9,024-byte executable used by the compile control |
| flat probe source | `342337c885dd88d3ddc7c49aec52b57867206ebc3ae50f81f55e85e236dfb5` | exact 146-byte Lean source copied as `AxeyumProbe.lean` |
| flat reference NDJSON | `c582b5d5ab19cba61183d592d70c17eb7d101b8a1ad61e8c4c6022dfe95a8280` | exact 3,849-byte, 65-line exporter output acceptance oracle |
| `lean-u2-official-ci-profiles-v1.json` | `4817d177828797f9dab9e62cf7647732d2b9c3788db7b7b4e3461bc868948548` | proves the controls select none of the 3,678/3,723 registered U2 cases |

The installed executable's required identity line is exactly:

```text
Lean (version 4.30.0, x86_64-unknown-linux-gnu, commit d024af099ca4bf2c86f649261ebf59565dc8c622, Release)
```

The implementation must not rediscover a different executable through ambient
`PATH`. It uses the exact absolute installed executable after rechecking its
bytes and identity. A different architecture, build type, Lean commit, or
binary hash is a different control and stops this result.

## 3. Frozen official exporter source and build

Git and `gh` inspection of official tag `v4.30.0` fixes:

| Field | Exact identity |
|---|---|
| repository | `https://github.com/leanprover/lean4export` |
| tag commit | `a3e35a584f59b390667db7269cd37fca8575e4bf` |
| Git tree | `e8b4adcea8445abbe0ae656eb6067d079e3efca8` |
| recursive tree population | 13 files |
| `git archive --format=tar` SHA-256 | `a66fd0b6f04701565221cb82c9702ab4036ab624471f91af27cf306ee4e35098` |
| `README.md` SHA-256 | `98833b66efc1289df582d85faa79b253c83bcca27c9fdb073ba42bdf0ffe77c9` |
| `lakefile.toml` SHA-256 | `54dde3aba280f32035c882dcd2f2039e738e20ed45ca538337b65cc69c02f7df` |
| `lean-toolchain` SHA-256 | `54727eec5cba149c18842e6deb5c41b369d66455c93ce135d7d5347c782b2325` |
| `format_ndjson.md` SHA-256 | `f82a21e17e4258a1043895d0653ea4333bef8cb07aad2e3d6c1fc4be52b138e3` |

After this plan is pushed, preparation may clone exactly that commit into a
new task-local cache and run the pinned toolchain's absolute `lake build
lean4export` with one worker, `LAKE_NO_CACHE=1`, and no package dependencies.
The source status must be clean before and after the build. The build command,
working directory, environment, stdout/stderr, exit status, source commit/tree,
recursive tree listing, built executable path/size/mode/SHA-256, and pinned
Lean/Lake executable hashes are retained. A preexisting binary is not accepted
without recreating and validating this build record.

The official sources establish the intended mechanics:

- the pinned [README](https://github.com/leanprover/lean4export/blob/a3e35a584f59b390667db7269cd37fca8575e4bf/README.md)
  requires `lake build` and execution in the correct Lake environment;
- the pinned [Lake package](https://github.com/leanprover/lean4export/blob/a3e35a584f59b390667db7269cd37fca8575e4bf/lakefile.toml)
  declares `lean4export` as the default executable target with
  `supportInterpreter = true`;
- pinned [`Main.lean`](https://github.com/leanprover/lean4export/blob/a3e35a584f59b390667db7269cd37fca8575e4bf/Main.lean)
  imports compiled modules, emits metadata, and optionally restricts roots
  after `--`; and
- the [Lean Lake reference](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)
  defines `.lake/build/bin` as the package executable directory and `lake env`
  as the command environment boundary.

These build facts are provenance for a later external control, not Lean or
parity outcomes themselves.

## 4. Frozen controls

Both controls use the observed worktree-local storage class accepted by
TL0.7.3. Each has an empty selection, no case records, one prelaunch attempt
installed before process creation, exact raw streams, an evidence-backed
terminal record, immutable artifacts, and a completion installed last.

### 4.1 `pinned-lean-compile-preflight-4g`

Preparation copies the committed 146-byte source without modification to a
fresh private `AxeyumProbe.lean`. The one launched command is structurally:

```text
<exact-pinned-lean> -j1 -o <private-run>/AxeyumProbe.olean <private-run>/AxeyumProbe.lean
```

The exact absolute paths are frozen in the run record. The environment is the
complete mapping `LANG=C.UTF-8`, `LEAN_NUM_THREADS=1`, and
`PATH=<pinned-lean-bin>:/usr/bin:/bin`. The process has a 60-second wall
watchdog, one process group, and exact 4 GiB `RLIMIT_AS` enforcement. Acceptance
requires exit zero, no watchdog, a reaped group with no live non-zombie member,
exact source-copy equality, and one nonempty regular `AxeyumProbe.olean` whose
bytes/hash are installed immutably. Stdout and stderr are retained even when
empty.

The `.olean` is a version-specific untrusted adapter artifact. Its hash becomes
an exact input to the exporter control; it earns no checking or cache-format
credit.

### 4.2 `official-lean4export-flat-export-8g`

The exporter consumes only the preceding completed `.olean`. Its one launched
command is structurally:

```text
<exact-pinned-lake> env <built-lean4export> AxeyumProbe
```

The working directory is the clean exporter source checkout. The complete
environment is `LANG=C.UTF-8`, `LAKE_NO_CACHE=1`, `LEAN_NUM_THREADS=1`,
`LEAN_PATH=<completed-compile-artifact-directory>`, and
`PATH=<pinned-lean-bin>:/usr/bin:/bin`. The process has a 120-second wall
watchdog, one process group, and exact 8 GiB `RLIMIT_AS` enforcement.

Acceptance requires exit zero, empty stderr, no watchdog, a reaped group with
no live non-zombie member, and stdout byte-for-byte equal to the committed
3,849-byte, 65-line NDJSON reference. Its metadata must independently state
exporter/format `3.1.0`, Lean `4.30.0`, and commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`. No `--export-unsafe` or
`--export-mdata` option and no declaration filter is allowed.

The equality oracle is fixed before execution. The accepted result cannot
replace it with a newly generated expected stream.

## 5. Evidence store and completion

Planned owned implementation:

- `scripts/lean_execution_acceptance.py` — source/build validation, generic
  no-credit external runner, immutable control stores, result authority, and
  generated views;
- `scripts/tests/test_lean_execution_acceptance.py` — offline structural/
  mutation suite plus an explicit opt-in live pair;
- `docs/plan/evidence/lean-execution-acceptance-tl0.7.4/` — retained build and
  two control stores;
- `docs/plan/lean-execution-acceptance-v1.json` — result authority;
- `docs/plan/generated/lean-execution-acceptance.{json,md}` — derived views;
  and
- `docs/plan/lean-execution-acceptance-tl0.7.4-2026-07-22.md` — bounded result.

The acceptance implementation imports but does not modify the TL0.7.2 process
and TL0.7.3 storage modules. It reuses their lane constants, platform/resource
capture, group cleanup checks, storage-class capture/preflight, and the frozen
ADR-0344 installation primitive. The predecessors' fixture-specific schemas
remain unchanged; TL0.7.4 adds a separate exact schema for external controls.

Each control store accepts only its manifest, run, attempt, artifact, terminal,
and completion paths. Every JSON record is canonical, exact-field, self-hashed,
read-only, and content-bound. Binary/raw artifacts are installed through the
same same-directory `O_EXCL` temporary, fsync, no-replace hard-link, inode
fsync, unlink, and directory-fsync primitive. Existing identical bytes are
idempotent; different bytes preserve the final, quarantine the incoming
candidate, and fail.

Completion is installed last only after all exact dependencies exist, raw
hashes/sizes agree, the process terminal matches the preregistered result, the
compile output or exporter equality predicate holds, and all credit counters
are zero. A final canonical projection excludes PIDs, durations, temporary
paths, build-cache paths, and quarantine names while retaining tool/source/
command/environment/resource/output identities.

## 6. Required controls and mutations

At least sixteen focused tests must cover:

1. preregistration, predecessor, fixture, toolchain, Lean binary, and exporter
   source identity drift;
2. exporter build commit/tree/file population, dirty source, command,
   environment, log, exit, or binary drift;
3. implicit/ambient executable discovery instead of exact absolute paths;
4. wrong lane, 4/8 GiB limit, worker count, timeout, environment, directory, or
   process-group semantics;
5. any nonempty U2 selection or case record;
6. prelaunch record missing, late, duplicated, reordered, or attributed to the
   wrong run;
7. missing, extra, symlinked, writable, noncanonical, wrong-field, wrong-ID, or
   self-hash-drifted record;
8. raw stdout/stderr hash or size drift;
9. nonzero exit, signal, timeout, surviving process, or guessed terminal class;
10. changed source copy, absent/empty/symlinked/writable `.olean`, or changed
    compile-artifact attribution;
11. missing/mutated exporter metadata or any byte/line-count difference from
    the committed NDJSON reference;
12. exporter use of unsafe/mdata options, declaration filtering, a different
    module, or an `.olean` not owned by the completed compile control;
13. missing, duplicate, unexpected, conflicting, or reordered dependency;
14. completion before dependencies, wrong record-set digest, or second
    different completion;
15. observational PID/time/cache/quarantine fields entering the canonical
    projection; and
16. any official/Axeyum outcome, credited run/case, denominator, paired cell,
    performance row, axis/gate, or parity credit becoming nonzero.

Live tests are opt-in and never silently rebuild or download tools. Offline CI
rehashes the committed authority/evidence without requiring the external cache
paths to remain present.

## 7. Acceptance and stop conditions

TL0.7.4 is complete only when:

- this plan was committed and pushed before exporter build, implementation,
  Lean compilation, or export;
- implementation/tests were committed and pushed before the authoritative
  pair;
- the exporter build record validates from the exact official source;
- both exact processes exit zero under their registered lane limits with full
  attempt/raw/group evidence;
- the compile artifact is immutable and the exporter stream equals the
  preregistered reference byte-for-byte;
- both completions install last and the offline authority rehashes every
  retained/source input;
- all mutation, TL0.7.1, TL0.7.2, TL0.7.3, complete-parity,
  foundational-resource, cargo-check, and owned documentation gates pass; and
- the result records two observed external controls but zero credited runs,
  U2 cases/outcomes, Axeyum outcomes, paired cells, performance rows, and
  parity credit.

Stop with TL0.7 partial if a pin or build input drifts, the exporter cannot be
built from the exact source, a child survives, the resource/store mechanism is
bypassed, the `.olean` ownership is ambiguous, exporter output differs by one
byte, completion can precede dependencies, offline validation requires a live
external cache, or any result would need U2/parity credit to pass.

Successful TL0.7.4 acceptance closes TL0.7's local policy prerequisite only.
It allows TL0.6.3 to start retaining actual official U2 profile executions; it
does not itself execute or satisfy one registered U2 case.
