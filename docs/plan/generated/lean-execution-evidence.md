# Lean execution evidence contract

> **Generated; do not edit by hand.** Regenerate with `python3 scripts/gen-lean-execution-evidence.py`; validate with `--check`.

> **Verdict: execution evidence contract represented; no process or parity outcome observed.** All real counters remain zero.

Preregistered at `ff8f8dd4b71c3c488ce53229f4301527d5e9d360` before implementation.

## Registered lane templates

| Lane | Purpose | Memory ceiling | Scope | Workers | Credit class |
|---|---|---:|---|---:|---|
| `standard-local-4g` | bounded local development and contract evidence | 4,294,967,296 bytes | `per-process-address-space` | 2 | `development-only` |
| `official-export-8g` | bounded official Lean exporter adapter | 8,589,934,592 bytes | `per-process-address-space` | 1 | `adapter-export-only` |

The generic wrapper's 64 GiB default is not either registered lane; the 4/8 GiB value must be explicit in each run identity.

## Typed termination classes

`exited`, `signaled`, `wall-timeout`, `cpu-timeout`, `memory-limit`, `pids-limit`, `disk-limit`, `cancelled`, `runner-lost`, `launch-failed`, `preflight-invalid`, `unknown-termination`.

A memory, timeout, PID, or disk classification requires matching enforcement evidence. A signal or nonzero exit alone is not OOM proof.

## Record contracts

| Record | Required fields |
|---|---:|
| `run` | 22 |
| `attempt` | 8 |
| `attempt_terminal` | 8 |
| `case` | 8 |
| `artifact` | 9 |
| `completion` | 10 |
| `credits` | 7 |

## Synthetic representation controls

| Control | Contract result | Meaning |
|---|---|---|
| `clean-complete` | `valid` | two passed cases and completion-last closure |
| `failed-case-complete` | `valid` | one passed and one failed case retained in a complete run |
| `interrupted-resumed` | `valid` | terminal-less first attempt retained beside a completing retry |
| `incomplete` | `valid` | partial diagnostic bundle with no completion or credit |
| `preflight-invalid` | `valid` | preflight-invalid attempt with no launched cases or credit |

The fail-closed register contains 19 mutation classes. Synthetic controls test representation only and cannot enter a Lean denominator.

## Checkpoint and credit boundary

- Run identity is fixed before launch; every launch is an immutable attempt.
- Case and raw-artifact records are content-addressed and never overwritten.
- Resume retains terminal-less attempts and may add only missing valid records.
- Completion is installed last and proves all-and-only case/attempt closure.
- JUnit, logs, runner labels, provider conclusions, and expiring provider artifacts are not completion by themselves.
- Adapter/export evidence cannot fill a native-system parity cell.

## Observed real outcomes

- `real_runs`: 0
- `executed_attempts`: 0
- `completed_cases`: 0
- `official_outcomes`: 0
- `axeyum_outcomes`: 0
- `paired_cells`: 0
- `performance_rows`: 0

## Remaining work

- Implement forced process exit, signal, timeout, and evidence-backed limit capture in TL0.7.2.
- Prove immutable filesystem checkpoints, conflict handling, kill/resume, and completion-last publication in TL0.7.3.
- Run no-credit pinned-Lean and official-export controls in TL0.7.4 before any U2 execution.
