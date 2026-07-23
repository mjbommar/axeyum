# Lean U2 TL0.6.3 M2 R1 symlink-preflight correction plan

Status: **preregistered after preflight stop; no M2 harness, discovery, or test
process has run**

Date: 2026-07-22

Parent plan:
[M2 shard-0001 execution plan](lean-u2-official-execution-tl0.6.3-m2-shard-0001-plan-2026-07-22.md)
at SHA-256
`4cef4ba9c57820f5bff82e4cfdfdc524b3d0d54665a947cf2b27560767ec81dd`.

## 1. Exact stopped invocation

The one-shot runner was implemented and pushed at
`431d3959ae5c3d7bbabf25c1d3a3aa6ab88f6f4c`; its documentation checkpoint
was pushed at `519d91c15e7f4ab587c94611e8da7ebe668670db`. A read-only
preflight at the latter revision validated:

- Lean source commit `d024af099ca4bf2c86f649261ebf59565dc8c622` and tree
  `0271450d1b109f9a0e5fadea2b6044160e9af7dd`;
- the released toolchain's exact 13,916-file manifest at digest
  `f7c5f7e97e4bafaf61d829564d4be99ab72fabcf7c985e75da40602d615ac6f8`;
- local-tools record
  `80dc19a99d0b5cba598add36ef311d1aebb76dc3f07ccfd6f33b548c2914e3c9`;
- storage descriptor
  `f84fca0b265075d1ab9dbe3a0b1d3681532f582e6e3f47b7a61f3bd7730f07be`;
  and
- new proposed work and evidence roots.

The first `run-m2` invocation then created only the private work root and exact
Lean source archive. Source validation stopped with 24 messages of the form:

```text
M2 selected runner missing: compile_bench/<case>.lean
```

There is no M2 evidence root. The runner had not captured the toolchain,
created a harness, run CTest discovery, installed a prelaunch record, or
launched a child process. Therefore the plan's single process attempt remains
unconsumed. The private stopped root is retained at
`/home/mjbommar/.cache/axeyum-tl063-m2-519d91c1`; R1 must use a new root and
must not reinterpret that directory as attempt evidence.

## 2. Root cause and exact official identities

All 24 `compile_bench` registrations name command element 2 as
`$LEAN_ROOT/tests/compile_bench/run_test.sh`. In the pinned source tree this is
an intentional symlink, not a regular manifest row:

| Path | Kind | Mode | Bytes | SHA-256 | Target |
|---|---|---:|---:|---|---|
| `tests/compile_bench/run_test.sh` | symlink | `0777` | 22 | `674a6c537535d76d6f10d195c61ad8da8de97e903f2735326e4a927a7e0d3299` | `../compile/run_test.sh` |
| `tests/compile/run_test.sh` | file | `0644` | 1,212 | `557fe4726ec23d812a0649c56def2c22daa89faeddc58b7e49b118f3ab123396` | - |

The source capture was correct. The new validator introduced at `431d3959`
incorrectly required every selected registration runner's manifest `kind` to
equal `file`, even though direct execution resolves this pinned in-tree link to
the same compile runner already used by the compile family.

## 3. Frozen correction

R1 changes only selected-runner source validation:

1. a regular-file runner remains accepted exactly as before;
2. a symlink runner is accepted only when its manifest row is a safe relative
   link whose lexical resolution stays inside the source manifest and resolves
   directly to a registered regular-file row;
3. the exact official compile-bench link and target identities above must be
   asserted explicitly; and
4. absolute targets, escaping `..`, missing targets, symlink chains,
   non-regular targets, altered link bytes/hash/target, and altered target
   bytes/hash remain fail-closed.

No command, registration, shard, source tree, toolchain, environment, worker,
resource, timeout, JUnit, artifact, store, credit, or result rule changes.

## 4. Required offline validation

Before another invocation, tests must demonstrate:

- all 64 selected source registrations validate against a synthetic exact
  manifest containing the official symlink;
- the 24 compile-bench rows resolve to the one exact pinned target;
- missing/renamed/regularized/absolute/escaping/chained/wrong-target symlinks
  reject;
- regular compile/docparse runners retain their prior rule;
- full M2 contract/store/runner tests and every parity generator/check pass;
  and
- the corrected runner, tests, and this plan are committed and pushed with
  local/tracking/remote equality before any new work root is created.

## 5. R1 invocation and stop rules

After the correction is pushed, repeat the read-only external preflight at the
new full implementation revision. Use a new private work root whose name
contains that revision. The evidence root and process attempt ID remain those
in the immutable parent plan because no child process or prelaunch evidence was
created by the stopped invocation.

Stop again before harness construction if selected source validation differs
in any other way. Once a harness or discovery exists, do not repair or retry
under R1. If the child process launches, it consumes the parent plan's single
attempt regardless of outcome.

## 6. Non-claims

This preflight stop and correction plan establish no official outcome, shard
completion, provider reproduction, Axeyum result, matched pair, performance
row, population, axis, gate, or Lean parity. Every such counter remains zero.
