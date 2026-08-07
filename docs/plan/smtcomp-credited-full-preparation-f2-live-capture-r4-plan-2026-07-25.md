# SMT-COMP credited full-population F2 live-capture R4 plan

Status: implemented, fully gated, and pushed; integration and live F2 remain
prohibited

Date: 2026-07-25

Parent:
[F2 live-capture plan](smtcomp-credited-full-preparation-f2-live-capture-plan-2026-07-24.md)

Prior corrections:
[R1](smtcomp-credited-full-preparation-f2-live-capture-r1-plan-2026-07-24.md),
[R2](smtcomp-credited-full-preparation-f2-live-capture-r2-plan-2026-07-24.md),
and
[R3](smtcomp-credited-full-preparation-f2-live-capture-r3-plan-2026-07-25.md)

Durability authority:
[accepted ADR-0344](../research/09-decisions/adr-0344-preregister-resumable-distributed-benchmark-execution.md)

## Why this correction exists

The R3 readiness runner correctly replaces the volatile frontier destination,
but it constructs the rest of each gate subprocess environment by copying the
complete ambient `os.environ`. A bounded source audit demonstrated that both
`RUSTFLAGS=--cfg axeyum_unregistered_gate_flag` and
`AXEYUM_GLAURUNG_QFBV_AUTO_DISCOVER=0` survive unchanged in the child mapping.
The first can change compiled code; the second can turn a normally discovered
real-data gate into an explicit skip. Loader/compiler overrides, Python user
site configuration, and unrelated credentials would also cross this boundary
without appearing in the sealed gate observation.

Consequently, the current C0 record proves the command spelling, exit code,
output identities, commit, and clean tree, but not the execution environment
that gave the command those semantics. This is an authority gap, not evidence
that any retained gate was malicious or incorrect. No live F2 root exists and
no host, sentinel, NAS, admission, allocation, or solver-wave action was used
to find it.

R4 closes only the registered-gate environment and executable-identity gap.
All C0--C5, R1--R3, exact-main, clean-tree, frontier-ratchet, and no-launch
requirements remain unchanged.

## R4.1: constructed non-secret gate environment

The readiness runner must build each gate subprocess environment from scratch.
It must not begin with `os.environ`, and it must not pass arbitrary
`AXEYUM_*`, `GLAURUNG_*`, Cargo/Rust compiler flags, dynamic-loader settings,
Python path/user-site settings, shell hooks, or credential variables.

The constructed mapping contains only:

- canonical account/runtime discovery required to execute the local toolchain:
  `HOME`, `USER`, `LOGNAME`, `PATH`, `CARGO_HOME`, `RUSTUP_HOME`, and, when the
  registered user-systemd session exists, `XDG_RUNTIME_DIR` and
  `DBUS_SESSION_BUS_ADDRESS`;
- fixed locale/runtime values: `LANG=C.UTF-8`, `LC_ALL=C.UTF-8`, `TZ=UTC`,
  `PYTHONHASHSEED=0`, `PYTHONNOUSERSITE=1`, `PYTHONWARNINGS=error`,
  `NO_COLOR=1`, and `CARGO_TERM_COLOR=never`;
- the explicit default regular-gate policy:
  `AXEYUM_GLAURUNG_QFBV_AUTO_DISCOVER=1` and
  `AXEYUM_GLAURUNG_QFBV_MEMORY_GB=4`; and
- the unique external `AXEYUM_PROGRESS_FRONTIER_ARTIFACT_DIR` already required
  by R3.

Account fields are derived from the effective uid rather than copied from
ambient text. `PATH` is constructed from the canonical Cargo bin directory and
fixed system tool directories; empty, relative, or caller-prepended components
are forbidden. The user-systemd values are derived from the effective uid and
accepted only when their canonical runtime directory and bus socket exist.
An unavailable required tool or runtime mismatch rejects the gate rather than
falling back to the caller environment.

The child mapping intentionally contains no API keys, tokens, proxy settings,
`LD_PRELOAD`, `LD_LIBRARY_PATH`, `RUSTFLAGS`, `CARGO_ENCODED_RUSTFLAGS`,
`RUSTC_WRAPPER`, `CARGO_TARGET_DIR`, `RUST_TEST_THREADS`, `PYTHONPATH`, or
caller-selected gate controls. This list is explanatory, not a deny-list: the
positive allow-list is authoritative.

## R4.2: sealed executable and environment identity

The gate-observation schema advances to v2 and its containing readiness schema
advances to v3. In addition to the existing exact registered command and
output identities, each gate row records:

- the complete constructed non-secret environment mapping and its canonical
  SHA-256;
- the canonical resolved executable path, byte count, and SHA-256; and
- the unchanged logical command (`just check` or
  `./scripts/check-smtcomp-resume.sh`).

The runner resolves the executable through the constructed environment before
launch and executes that exact canonical file. For the repository script, the
resolved path must be the registered tracked path below the exact source root.
For `just`, the executable must resolve through the constructed canonical
`PATH`. Symlink, non-regular, non-executable, path, byte, or environment drift
rejects. Validation accepts no unregistered environment key. Live construction
and current-state validation rehash the executable before authority is granted;
later durable replay validates the sealed external-tool identity without
pretending that the external executable bytes were retained in Git.

This schema is safe to advance because no live F2 readiness or preparation
root exists. Existing fixture-only gate records are regenerated by tests and
receive no measurement credit.

## R4.3: mutation and integration gates

Focused coverage must prove:

1. caller-supplied semantic flags, loader settings, skip controls, Python path,
   target overrides, and representative credential names are absent;
2. the fixed locale, Python, regular-gate, Cargo-account, and R3 frontier values
   are exact, and an inherited frontier destination is replaced;
3. `PATH` has only canonical absolute components and the launched executable
   equals the path and bytes sealed in the observation;
4. environment, executable-path, executable-byte-count, and executable-hash
   mutations reject;
5. both registered logical commands, gate order, byte-exact output hashes,
   clean-tree checks, and frontier isolation remain unchanged; and
6. the F2 module still has no admission, allocation, host-unit, or solver-wave
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

The final corrected topic must pass `just check` with a clean post-gate
worktree before integration. Neither preregistration nor implementation
authorizes live F2. The integration owner must land the complete corrected
stack on repaired green exact main before C0 may run, and C5 remains separately
authorized after that gate.

## Implementation and closure result

The preregistration is pushed as `8b6a11f4`. The implementation is pushed as
`30287148852bdfe4485eda490d14569e926bbe72` and makes only the registered
correction.

The implementation constructs the positive allow-list from the effective uid,
canonical Cargo/Rustup homes, fixed system paths, and an observed canonical
user-systemd bus; every other ambient key is absent. It advances the gate row
to v2 and readiness to v3, seals the complete environment and resolved command
executable, executes that canonical file, and detects executable mutation
across the child lifetime. Current-state validation rehashes the executable;
durable Git-object replay retains the recorded external-tool identity without
requiring that mutable external byte source later remain installed.

The focused 47-test full-population suite passes, including 52 subtests. The
160-test SMT-COMP aggregate passes with one expected live-host skip, the
generated resume contract remains exact, and `just check-scope origin/main`
passes the Python, aggregate, solver-library, and solver-Clippy routes. A real
invocation of the registered `check-smtcomp-resume.sh` through `run_gate`
exited zero under the constructed 19-key environment and emitted a sealed v2
observation; links also pass. The complete `just check` and post-gate clean-tree
proof then passed through the same constructed environment from the clean,
pushed implementation commit.

The final full gate ran the exact logical command `just check` through
`run_gate`. It exited zero and emitted a v2 gate observation bound to commit
`30287148852bdfe4485eda490d14569e926bbe72`:

| Field | Sealed value |
|---|---|
| executable path | `/home/mjbommar/.cargo/bin/just` |
| executable SHA-256 | `8a4c6f2def1922823287aa93042be584306280a8f5c4c37a84d68a21338d10c3` |
| environment SHA-256 | `4b8f6ae1923199dbf6265d70ec50912da50abf6ae1bbf534ab505b22eb6f453f` |
| stdout | 478,004 bytes; SHA-256 `1d7ebd52aaacfd81b4479f53ec161ed52de0e1ea94b280d4d22f93b716728049` |
| stderr | 59,752 bytes; SHA-256 `7b667e5aa794f9b4eba4b1c1f1a3b34af6247b6cdb2a32e8d2d3dcf5762c3186` |

After terminal exit, `git status --porcelain=v1` was empty and
`git diff --exit-code -- bench-results/frontier` passed. Local, tracking, and
live remote topic refs all equaled the tested implementation commit. R4 is
therefore ready for integration only as part of the complete corrected stack.
Exact repaired green main and an integrated combined full gate remain required
before C0 can run; C5 and every live host, sentinel, NAS, admission, allocation,
and solver-wave action remain prohibited.

## Stop conditions

Stop without widening the allow-list if a required tool is unavailable, the
clean environment changes a gate result, user-systemd runtime identity is
ambiguous, a gate mutates tracked bytes, or any mutation control fails.
Preserve the rejection and amend source-first. Do not restore ambient flags,
pass credentials for convenience, weaken a regular gate to recover green, or
perform any live F2 action from this topic.
