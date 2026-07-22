# Lean strict positivity: M0 source freeze

Status: complete; no new official or Axeyum product observation

Date: 2026-07-22

Parent:
[TL2.11 execution plan](lean-strict-positivity-tl2.11-plan-2026-07-22.md)

Decision:
[proposed ADR-0352](../research/09-decisions/adr-0352-preregister-lean-strict-positivity.md)

Machine registration:
[`lean-strict-positivity-v1.json`](lean-strict-positivity-v1.json)

## Frozen population

M0 freezes the exact official-source population before kernel implementation or
new official execution:

| Source | SHA-256 | Expected role |
|---|---|---|
| existing construct-matrix positive | `08c6eeaed9d980a631dff14b30de1e3d8da37011b8ad03b84dbdc03c90bff13d` | direct-recursive, recursive-indexed, and reflexive positive controls |
| existing negative-domain source | `4c94c6563583b34cbd500075bb76b6a71b7476e7694bcff91253c460d718c71b` | family occurrence in a function domain |
| new mixed-polarity source | `0722ce6898bdbf5335b4ee77e62ef8ecdfb0654e1a421b4acc892c0fcb312ffc` | both negative-domain and positive-codomain occurrences in one field |
| new deep-negative source | `89b1909580a979ca2645297f07fd0379b4837e67b54cfd0471e5014d39bbec13` | family occurrence nested inside the domain of an outer function field |

The six ordered case identities and rule classes are:

1. direct recursion — positive direct application;
2. recursive-indexed — positive valid indexed application;
3. reflexive/higher-order — positive `Pi` codomain;
4. negative domain — non-positive `Pi` domain;
5. mixed polarity — non-positive `Pi` domain wins;
6. deep negative — non-positive outer `Pi` domain.

The two new files total 389 bytes. Their content, module names, expected
official outcomes, and diagnostic substring are hash-bound. No observed exit
status, stderr, RSS, kernel result, importer result, or generated summary is
registered at this stage.

## Frozen execution boundary

The registration pins:

- Lean toolchain `leanprover/lean4:v4.30.0` and commit
  `d024af099ca4bf2c86f649261ebf59565dc8c622`;
- one Lean worker;
- `MemoryHigh=3G`, `MemoryMax=4G`, and `MemorySwapMax=512M` through a user
  systemd scope;
- at most two Rust build jobs;
- `/usr/bin/time -v <pinned-lean> -j1 -o <module>.olean <module>.lean` in a
  fresh temporary directory.

The exact Lean source checkout in `references/lean4` is gitignored and pinned to
the same commit; it is an implementation reference, not a committed dependency.

## Fail-closed gate

[`check-lean-strict-positivity.py`](../../scripts/check-lean-strict-positivity.py)
recomputes all source hashes and rejects drift in:

- schema/stage, paths, pins, resources, and command vectors;
- source population/order, fields, outcomes, and diagnostics;
- case population/order/identity, rule class, and source linkage;
- repository `lean-toolchain`;
- any premature official, product, kernel, importer, or generated observation.

Eight mutation/contract tests cover the committed positive, source drift, case
removal/reordering/duplication, rule-class drift, pin/resource/command drift,
diagnostic removal, case/source disagreement, and premature observations. The
checker and tests are now part of `parity-docs` and the plain-shell check path.

## Next gate

M1 adds separate typed non-positive and invalid-occurrence errors plus the
single-family positivity preflight before provisional environment insertion.
It must not broaden recursive-indexed or reflexive admission.
