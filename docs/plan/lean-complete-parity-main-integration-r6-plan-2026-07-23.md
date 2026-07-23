# Lean complete-parity current-main integration R6 plan

Date: 2026-07-23

Status: **complete and validated on `main`; no process or parity credit**

Result: [R6 integration result](lean-complete-parity-main-integration-r6-result-2026-07-23.md)

Contract: [complete Lean 4.30 parity](lean4-complete-parity-contract-2026-07-22.md)

## 1. Purpose and exact inputs

R6 prepares one reviewable, green integration candidate without modifying or
merging the integrator-owned `main` worktree. It combines, in order:

1. current remote `main` at
   `ddd709697544be3e8083452b472518d3c0cd6da3`;
2. the detached-mount portability repair branch
   `agent/lean/portability-main-r4` at
   `ca9c2ec96ad415519998bca3cd816d478cc6e0b4`; and
3. the held complete-parity/U2 classification branch
   `agent/lean/complete-parity-u2-classification` at
   `d0e23c6ca5be89511c95c875855080cb399fed92`.

The parity branch contains 69 commits not ancestral to current `main`. A direct
merge preview identifies four content conflicts: `STATUS.md`, the generated
complete-parity JSON, and the base/M2 official-execution validators. R6 exists
to resolve those conflicts explicitly and validate the resulting tree before
an integrator decides whether to merge it.

## 2. Resolution rules

R6 must preserve these invariants:

- retain current-main changes and append the Lean changelog/status material
  without deleting another lane's entries;
- never hand-author a generated authority: resolve its source inputs, then
  regenerate `docs/plan/generated/lean-complete-parity.json` with the committed
  generator;
- retain the merged ROOT-relative process/store/acceptance semantics and R4's
  same-observed-mount fixture correction;
- retain the parity branch's U2 native-surface, dependency, matched-execution,
  typed-normalization, and axis-contract validation only where its complete
  source/test/authority chain survives the merged tree;
- preserve immutable historical evidence identities while requiring current
  validator/source identities for new generation; and
- keep every real outcome, Axeyum outcome, paired cell, performance row,
  completed population/axis/gate, and parity-credit counter unchanged unless
  already supported by retained accepted evidence.

No conflict may be resolved by accepting both sides mechanically, weakening a
validator, deleting a mutation control, or rewriting retained evidence.

## 3. Required validation

Before push, R6 must pass:

1. `git diff --check` and an explicit merge-tree/conflict audit;
2. the focused process, store, acceptance, U2 official/M2, native-dependency,
   normalization, and complete-parity unit suites;
3. every affected generator under `--check`, including the terminal registry;
4. exact process/store/acceptance result replay;
5. `just parity-docs` and `just links`;
6. a differently rooted clean detached-checkout replay of the focused suites,
   terminal generator, and documentation/link gates; and
7. repository-wide `just check`, or an exact component-by-component result
   that records any unrelated pre-existing format failure separately without
   rewriting files outside this lane.

The final branch must be clean, pushed, and byte-equal to its tracking ref.
Only the integration owner may merge it to `main`.

## 4. Nonclaims and stop conditions

R6 authorizes no official Lean, Axeyum, M2.1--M2.7, SMT-solver, network, or
retained-evidence execution. It creates no new semantic observation or parity
credit. Stop and document rather than continue if the merge requires changing
an accepted historical authority, inventing missing source identity, choosing
between incompatible semantic policies without an accepted ADR, or launching
an external process.

The terminal statement must remain false unless the generated registry proves
all U0--U9 populations, A0--A11 axes, paired cells, and terminal gates. This
integration is plumbing for honest future measurement, not complete Lean 4
parity.
