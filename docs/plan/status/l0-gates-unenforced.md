# Lane: l0-gates-unenforced

**Status:** in progress (first commit, incomplete — measurements landed, wiring not yet written)

## Problem

The seven L0 trusted-library safety gates run only from `scripts/check.sh` and
the `justfile` — that is, only when a human types a command. Neither
`.github/workflows/ci.yml` nor `hooks/pre-push` invokes any of them.

Measured in this worktree, with positive controls in the same run
(`ci.yml` references `scripts/` 44 times, `hooks/pre-push` 28 times, so the
zeros below are real absences and not a broken query):

| gate | check.sh | just | CI | pre-push |
| --- | --- | --- | --- | --- |
| check-trust-closure | 1 | 1 | **0** | **0** |
| check-settled-fact-statements | 2 | 2 | **0** | **0** |
| check-semantic-control-fixtures | 1 | 1 | **0** | **0** |
| check-kernel-differential | 2 | 4 | **0** | **0** |
| check-credit-transaction-ledger | 1 | 1 | **0** | **0** |
| check-proposition-duplication | 1 | 1 | **0** | **0** |
| check-holdout-closed-evaluation | 1 | 1 | **0** | **0** |

## Measured cost (this host, uncontended, single run)

| gate | exit | wall |
| --- | --- | --- |
| settled-fact-statements | 0 | 0.09 s |
| holdout-closed-evaluation | 0 | 0.06 s |
| semantic-control-fixtures | 0 | 1.09 s |
| credit-transaction-ledger | 0 | 10.64 s |
| proposition-duplication | 0 | 54.70 s |
| trust-closure | 0 | 103.15 s |
| kernel-differential | (pending) | (pending) |

The headline finding for the design: **"pure Python" does not mean "cheap"**.
`trust-closure` at 103 s and `proposition-duplication` at 55 s are Python and
are still too expensive to put in front of every push unconditionally. The
brief's framing (cheap Python vs. expensive kernel) does not survive
measurement; the split has to be made on measured seconds.

## Next

- Time `check-kernel-differential` and its mutants companion.
- Decide per-gate placement and wire it.
- Add an enforcement gate so the wiring cannot silently regress.
