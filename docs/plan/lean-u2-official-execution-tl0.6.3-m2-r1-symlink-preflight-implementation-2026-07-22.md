# Lean U2 TL0.6.3 M2 R1 symlink-preflight implementation checkpoint

Status: **bounded correction implemented, validated, committed, and pushed;
no new work root, harness, discovery, prelaunch, or child process exists**

Date: 2026-07-22

Preregistered plan:
[M2 R1 symlink-preflight correction plan](lean-u2-official-execution-tl0.6.3-m2-r1-symlink-preflight-plan-2026-07-22.md), committed and pushed at
`3e761588eb8487dab510906e6d5fc3c90cc08fef`, SHA-256
`e0fd948ee39e0f1808eec459a18766683d3781e602cc481c8fa10a70e9a0d5f9`.

## 1. Publication boundary

Commit `9d5d40c8183deea85cf5f50d1ae380ccf7a99462` implements only the
preregistered selected-runner correction and is pushed with local, tracking,
and remote branch equality. The implementation records both the full
preregistration commit and plan digest and fails its offline check if the plan
bytes drift.

No new private work root was created while implementing or validating R1. The
stopped pre-R1 root remains retained at
`/home/mjbommar/.cache/axeyum-tl063-m2-519d91c1`; the official evidence root
remains absent. Therefore no M2 harness, discovery, prelaunch, child process,
JUnit result, case record, or completion was created, and the parent plan's
single process attempt remains unconsumed.

## 2. Exact implementation identities

| Source | SHA-256 |
|---|---|
| `scripts/lean_u2_official_execution_m2_run.py` | `5763298bb33c97baacc0c29d6cc67a8df2ece796f7ea182c59957f5be59eb593` |
| `scripts/tests/test_lean_u2_official_execution_m2_run.py` | `dd8db7fc2f65b99f0ba6ad11d863a29927463544b6fabf5b2dd836d928f4f2e8` |

The correction resolves a candidate link lexically from its source-manifest
row. It never follows the captured filesystem symlink. Absolute targets and
any `..` that escapes the manifest root reject. Resolution must terminate in
one registered regular-file row; symlink chains and non-regular targets reject.

For the selected compile-bench registrations, acceptance additionally requires
byte-exact equality with both frozen official rows:

- `tests/compile_bench/run_test.sh`: symlink mode `0777`, 22 target bytes,
  digest `674a6c537535d76d6f10d195c61ad8da8de97e903f2735326e4a927a7e0d3299`,
  target `../compile/run_test.sh`;
- `tests/compile/run_test.sh`: regular mode `0644`, 1,212 bytes, digest
  `557fe4726ec23d812a0649c56def2c22daa89faeddc58b7e49b118f3ab123396`.

All existing regular-runner validation remains unchanged. No command,
registration, source tree, shard, toolchain, environment, resource, timeout,
JUnit, artifact, store, outcome, or credit rule changed.

## 3. Validation

The focused runner suite now has six tests. Its exact synthetic manifest
validates all 64 selected registrations, including all 24 compile-bench rows.
It rejects missing, renamed, regularized, absolute, escaping, chained, and
wrong-target links; link mode/byte/hash drift; and missing or altered target
kind/mode/byte/hash. The helper separately proves the expected lexical
resolution and rejects absolute and root-escaping targets.

The complete Lean/parity documentation surface passed:

- 268 tests, with one intentional skip;
- every Lean authority generator and `--check` validator;
- the complete-parity generator and focused registry tests;
- all strict-positivity, recursive-IH, mutual-inductive, and nested-inductive
  retained controls; and
- `PARITY_DOCS` at 992 files, 753 decisions, 680 comparisons, and zero recorded
  disagreement within those named fixtures.

The regenerated parity authority still reports 0 complete populations, 0
complete axes, 0 paired cells, 0 satisfied gates, and `terminal_ready=false`.

## 4. Non-claims and next gate

This implementation checkpoint establishes no live execution, official
outcome, shard completion, provider reproduction, Axeyum outcome, matched pair,
performance row, population, axis, gate, or Lean parity.

Next publish the documentation checkpoint, require clean local/tracking/remote
equality at that new revision, and repeat the exact external read-only
preflight. The new private work root must include that revision and must not
reuse the stopped pre-R1 root. Only if every source, toolchain, local-tool,
storage, authority, work-root, and evidence-root gate remains exact may the
single process attempt proceed.
