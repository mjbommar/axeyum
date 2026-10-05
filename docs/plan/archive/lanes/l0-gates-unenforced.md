# Lane: l0-gates-unenforced

<!-- plan-section: lane-status -->

**Status:** complete — all seven L0 gates wired, each proved able to fail, and
an enforcement gate added so the wiring cannot silently regress (ADR-1050).

## The deficiency, confirmed and worse than briefed

All seven L0 trusted-library safety gates ran in NO automated context. Measured
with positive controls in the same run, so a zero could not be a broken query:

| file | L0 gates named | control (`scripts/` refs) |
| --- | --- | --- |
| `.github/workflows/ci.yml` | **0** | 44 |
| `hooks/pre-push` | **0** | 28 |
| `scripts/local-ci.sh` | **0** | 10 |

The third row was not in the brief. `ci.yml`'s own comment calls
`scripts/local-ci.sh` "the authoritative gate for main"; it runs none of the
seven either. Three automated contexts, gates in none of them.

## Measured cost (foreground, this host, uncontended)

| gate | first run | warm | needs |
| --- | --- | --- | --- |
| holdout-closed-evaluation | 0.06s | — | pure Python |
| settled-fact-statements | 0.09s | — | pure Python |
| semantic-control-fixtures | 1.09s | — | pure Python |
| credit-transaction-ledger | 10.6s | — | pure Python |
| kernel-differential | 27s | 7s | `cargo test` + pinned Lean |
| proposition-duplication | 54.7s | 72s | pure Python |
| trust-closure | 103s | 58s | `cargo run --release` |

**The obvious split is wrong.** "Pure Python is cheap, cargo is expensive" fails
in both directions: `proposition-duplication` is pure Python and costs more than
`kernel-differential`, which builds and runs real Lean.

## Wiring decision, per gate

| gate | where | why |
| --- | --- | --- |
| settled-fact-statements | pre-push + CI | 0.09s |
| holdout-closed-evaluation | pre-push + CI | 0.06s |
| semantic-control-fixtures | pre-push + CI | 1.09s |
| credit-transaction-ledger | CI only | 10.6s — 10x the whole pre-push block |
| proposition-duplication | CI only | 55–72s |
| trust-closure | CI only, NEW `l0-trust-closure` job | needs `cargo run --release`; no CI job did a release build |
| kernel-differential | CI only, `lean-inductive-crosscheck` | `AXEYUM_REQUIRE_LEAN=1` makes a missing toolchain a hard failure; that job already installs the pin |

Added to a push: **~1.2s** against a documented ~545s battery. The pre-push
block sits ABOVE the Rust/TOML early exit, because every L0 gate guards non-Rust
content and a docs/artifacts-only push takes that exit.

## Proof each wired gate can fail

Broken and restored in an isolated `/data0` snapshot, never in `artifacts/`:

| gate | clean | broken | restored |
| --- | --- | --- | --- |
| settled-fact-statements | 0 | **1** | 0 |
| semantic-control-fixtures | 0 | **1** | 0 |
| holdout-closed-evaluation | 0 | **1** | 0 |
| trust-closure | 0 | **1** | 0 |
| proposition-duplication | 0 | **1** | 0 |
| credit-transaction-ledger | 0 | **1** (both vacuity controls) | 0 |
| kernel-differential | 0 | G1–G6 each fire | 0 |

Pre-push block proved to fail the push: `CONTROL HOOK EXIT = 0`,
`MUTANT HOOK EXIT = 1`.

## Honest negatives

- Deleting `_verify_staged_integrity` from `credit-transaction-ledger.py`'s
  `apply()` does NOT fail its gate — a surviving mutant. Out of scope to fix
  (this lane must not edit the seven gate scripts); recorded in ADR-1050.
- `scripts/local-ci.sh` still runs none of the seven. Out of briefed scope.
- The gate most worth wiring that could not be: `kernel-differential` in
  pre-push. It is the only L0 gate comparing this kernel against real Lean and
  costs 7s warm, but `AXEYUM_REQUIRE_LEAN=1` hard-fails without a toolchain, and
  Lean is on one fleet host of five — every other lane would be unable to push.

## Landed

| commit | what |
| --- | --- |
| `2a74c42b0` | measurements: gates in no automated context, two are slow |
| `d29f29a28` | pre-push: three sub-2s gates, above the early exit |
| `0b46deff8` | CI: all seven wired + `check-l0-gate-enforcement.py` |
| `ccac03e56` | 11 controls, mutation-verified, registered in the suite table |

Holdout isolation, before and after, byte-identical:
`held_out=146|files_scanned=1110|settled=0|references=0|verdict=PASS`.
