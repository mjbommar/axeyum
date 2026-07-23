# TL0.6.3 M0 R2 result — retained adapter-invocation failure

Status: **failed before runner import; zero new official outcomes and zero parity credit**

Date: 2026-07-22

Authority:
[`lean-u2-official-execution-tl0.6.3-m0-r2-invocation-v1.json`](lean-u2-official-execution-tl0.6.3-m0-r2-invocation-v1.json)

## 1. Bounded verdict

The separately committed and pushed R2 implementation was invoked once from
the repository root at revision
`660915572968435f68b7a08fd95e737db6ef7762`. Python exited `1` while loading
the script, before the R2 runner imported, prepared a harness, created either
fresh root, or launched CTest:

```text
ModuleNotFoundError: No module named 'scripts'
```

Attempt 003 is therefore an incomplete adapter-invocation failure. It adds no
official case outcome and does not alter attempt 002's retained official
failure. The cumulative history is three process attempts, one decided local
official outcome, zero official passes, zero Axeyum outcomes or pairs, and zero
parity credit.

## 2. Exact retained observation

| Field | Value |
|---|---|
| implementation | `660915572968435f68b7a08fd95e737db6ef7762` |
| attempt / sequence | `attempt-003` / 3 |
| invoked entry point | `python3 scripts/lean_u2_official_execution_r2.py run-m0 ...` |
| terminal | exited 1; no signal |
| raw stdout | 0 bytes / `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| raw stderr | 265 bytes / `743f4e81513ab9f004ccab1115da538340a490b805d783e285f26ddcbafb8ca2` |
| runner import / harness / CTest | no / no / no |
| work root after exit | absent |
| evidence root after exit | absent |
| new official outcomes | 0 |

The authority embeds the exact stderr bytes. It explicitly marks the ambient
environment as not recorded and therefore makes no broader environment claim.

## 3. Root cause and correction boundary

When Python executes a file path, it prepends the file's containing directory,
not the repository root, to `sys.path`. The R2 file lives under `scripts/` but
imports the top-level `scripts` package, so direct invocation could not resolve
that package. Unit tests imported R2 as a package from the repository root and
therefore did not exercise the direct-file entry point.

The correction is not to reinterpret or silently rerun R2. R3 must be
preregistered and must add a direct-entry smoke gate that runs the exact
published command shape through `--help` with an isolated harmless argument
path. It must retain attempt 003 as incomplete and use a new attempt ID,
sequence, work root, evidence root, result authority, and implementation
revision. Python's command-line contract documents the relevant difference
between direct-file and `-m` execution:
[Python command-line documentation](https://docs.python.org/3/using/cmdline.html#interface-options).

Even a later passing singleton remains only one observed case from the
3,678-case parent. No parent/provider completion, Axeyum observation, semantic
pair, performance row, parity axis, gate, or complete-parity claim follows.
