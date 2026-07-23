# Lean complete-parity worktree-portability R1 result

Status: **accepted bounded validator repair; cross-worktree complete-parity
check passes; no historical authority, observation, or parity credit changed**

Date: 2026-07-23

Scope: TL0.7 retained process/store evidence and the TL0.6 U2/M2 validation
chain used by the complete Lean 4.30 parity registry.

## 1. Result

The complete-parity gate is no longer structurally blind to its checkout path.
At repair revision `2267f41b3a64eaf35ac684aa01c864cab8039cd5`,

```sh
python3 scripts/gen-lean-complete-parity.py --check
```

completed from a detached worktree rooted at
`/tmp/axeyum-path-check.zZKm06`, while the topic lane remained rooted at
`/home/mjbommar/projects/personal/axeyum-lean-parity`.

The resulting terminal line remained the honest non-parity result:

```text
LEAN_COMPLETE_PARITY|populations=10|complete_populations=0|axes=12|complete_axes=0|paired_cells=0|gates_satisfied=0|terminal_ready=false
```

This is validator-portability evidence. It does not add a U2 outcome, native
outcome, pair, performance row, completed population/axis/gate, or Lean parity
credit.

## 2. Defects and repairs

### R1.1 — retained process attribution

The accepted `exit-zero-4g` run records the absolute repository path that
actually executed. The live spec is generated under the current checkout.
Comparing those strings byte-for-byte made a check pass only in the original
worktree and fail in another checkout with `run/spec attribution drift`.

Commit `c3f068ea` now compares repository-owned command arguments and the
working directory by one recovered `ROOT`-relative identity. The external
Python executable remains byte-exact. All eight controls exercise arbitrary
root relocation; wrong targets, mixed roots, wrong working directories, and a
different external interpreter reject.

### R1.2 — retained checkpoint-store worker

After R1.1 exposed the next layer, the retained store cells still compared
their worker path and `PYTHONPATH` with the live checkout. Commit `09e1dcd2`
now recovers one root from the exact repository-owned worker suffix and
requires the retained `PYTHONPATH` to use that same root. External executable,
worker/primitive content, command/environment self-digests, process-group
identity, raw streams, markers, and every store seal remain exact.

The accepted TL0.7.2/TL0.7.3 source rows continue to name their historical
bytes. Current U2/M2 validators admit only the exact enumerated compatible
successors; they do not regenerate or rewrite an accepted authority.

### R1.3 — Git checkout permission representation

After R1.1-R1.2, the detached worktree reached M2 R3 and rejected retained
`CTestTestfile.cmake` as mutable. The evidence-producing store had installed
files with mode `0444`, but Git records only executable versus non-executable
for ordinary blobs and reproduced the same files as tracked `100644` entries.

Commit `2267f41b` accepts that checkout representation only when the file is a
clean tracked non-executable entry under the exact evidence root. Untracked,
dirty, executable, symlinked, non-regular, missing, or content/seal-drifted
evidence still fails closed. Creation-time stores continue to require their
immutable installation behavior; the exception is only for Git's portable
representation of already committed retained bytes.

### R1.4 — historical replay versus new result generation

The first R1.2 implementation always selected the historical source rows. That
was correct for replaying the accepted authority but too narrow for the live
16-cell regression, which intentionally builds a fresh authority at current
`HEAD`. The full parity-document gate exposed the difference after the repair
commits became current history.

Commit `98d85098` now selects historical rows only for the exact recorded
implementation revision `afe7db6e04c78fcbce04c6f502268ce2d9934121`.
Any other revision must be an ancestor of current `HEAD`, contain every current
source byte, and emits current source identities. The accepted authority still
replays byte-for-byte, while the live 16-cell matrix again proves that a new
committed implementation can generate a new result. The store suite passes
24/24 including both paths.

## 3. Historical/current separation

The repair keeps two identities explicit:

- **historical evidence identity** — immutable source rows and authority bytes
  recorded by the accepted attempt; and
- **current validator identity** — the exact reviewed successor source allowed
  to replay that history from another checkout.

The complete-parity registry independently content-identifies current
validators and tests. Therefore neither a stale historical implementation nor
an unenumerated live successor can pass merely because the historical result
is unchanged.

No file under these accepted authority/evidence roots changed:

- `docs/plan/lean-execution-process-v1.json` and its evidence root;
- `docs/plan/lean-execution-store-v1.json` and its evidence root;
- `docs/plan/lean-execution-acceptance-v1.json` and its evidence roots;
- TL0.6.3 official-execution authorities and evidence; and
- M2 R1/R3/R5/R6 authorities and evidence.

## 4. Validation

The repair checkpoint passed:

1. 118 focused unit tests across process, store, acceptance, base U2,
   U2 R2/R3/result replay, and M2 contracts (`OK`, one expected skip);
2. exact TL0.7.3 result replay over all 16 retained SIGKILL cells;
3. current-worktree complete-parity generation/check;
4. detached-worktree complete-parity `--check` at the different absolute root;
5. JSON generation and current-source hash refresh without historical
   authority regeneration; and
6. `git diff --check`, pathspec commits, push, and local/tracking/remote
   equality at `2267f41b3a64eaf35ac684aa01c864cab8039cd5`.

The repair commits are:

| Commit | Scope |
|---|---|
| `c3f068ea` | ROOT-relative retained process attribution and historical/current U2 input separation |
| `09e1dcd2` | ROOT-relative store worker/environment attribution and historical replay separation |
| `2267f41b` | clean tracked Git representation for committed read-only M2 evidence |
| `98d85098` | exact historical replay plus current-revision result generation |

## 5. Continuing invariant and nonclaims

Any later Lean parity checkpoint that changes a validator or source identity
must keep both checks green:

1. the focused semantic/replay suites in the owning worktree; and
2. `python3 scripts/gen-lean-complete-parity.py --check` from a clean checkout
   whose absolute root differs from the evidence-producing worktree.

Passing the second check proves only relocation of the registered retained
state. It does not prove provider portability, platform parity, complete U2
execution, native Lean behavior, or complete Lean 4 parity. The terminal claim
remains disabled until every U0-U9 population, A0-A11 axis, paired cell, and
G1-G10 gate satisfies the complete-parity contract.
