# Lean complete-parity current-main integration R6 result

Date: 2026-07-23

Status: **integration is on `main`; post-merge validation is still in progress;
no process or parity credit**

Plan: [R6 preregistration](lean-complete-parity-main-integration-r6-plan-2026-07-23.md)

Contract: [complete Lean 4.30 parity](lean4-complete-parity-contract-2026-07-22.md)

## 1. Integrated identities

The integration started from remote `main` at
`ddd709697544be3e8083452b472518d3c0cd6da3` and combined, in order:

1. `agent/lean/portability-main-r4` at
   `ca9c2ec96ad415519998bca3cd816d478cc6e0b4`; and
2. `agent/lean/complete-parity-u2-classification` at
   `d0e23c6ca5be89511c95c875855080cb399fed92`.

The isolated integration commits were:

- `9b560d77` -- preregister R6;
- `1b635b81` -- merge the detached-mount portability replay; and
- `a61bf52b` -- merge the 69-commit complete-parity stack.

The integration owner then merged the exact resulting tree to `main` as
`27828c40abac311d6ac93b868b4f5600a2c05ada` (`git diff` between the isolated
candidate and that `main` tree was empty). This places the ROOT-relative
worktree-path repair, its fresh retained-mount replay, and the previously held
complete-parity stack on `main` together.

## 2. Conflict resolution

The portability branch merged without conflict. The complete-parity branch
had four conflicts, resolved under the preregistered policy:

- `STATUS.md`: retain current-main SMT/CAS entries and append the Lean status
  and changelog material;
- `docs/plan/generated/lean-complete-parity.json`: regenerate from its source
  authorities instead of hand-merging generated JSON;
- `scripts/lean_u2_official_execution.py`: retain the newer current-main
  resume-contract identity; and
- `scripts/lean_u2_official_execution_m2.py`: bind the final merged base
  validator identity.

The final merged base-validator SHA-256 is
`2fe3ecf1c57db598060a82061ba4fa45fa3ca84b89ef673d8aba8636b4d4ed50`.
No accepted historical evidence was rewritten.

## 3. Validation completed so far

Before the merge commit:

- 246 focused process/store/acceptance, official/M2, native-surface,
  native-content, native-dependency, header, normalization, and terminal
  tests passed with one expected skip and zero failures;
- `just parity-docs` and `just links` passed; and
- `git diff --check` passed.

A fresh detached checkout rooted under `/tmp` then passed 176 focused tests
with one expected skip, followed by a complete `just parity-docs && just links`
replay. The detached worktree was clean and removed after the check.

On the exact post-merge `27828c40` tree:

- `cargo check --workspace --all-targets --all-features` passed;
- `just clippy doc` passed;
- `just benchmark-repetition-tests foundational-resources rules-as-code
  smtcomp-resume` passed;
- `just qfbv-profile reflection-semantics-gate` passed; and
- `just test` remains in progress. Every completed crate and integration suite
  has passed so far, including the CAS, CNF, solver, Lean-kernel,
  nested-inductive, evidence, arithmetic, quantifier, and differential suites.
  Expected ignored diagnostic, measurement, and release-only stress tests are
  not failures.

`cargo fmt --all --check` found only pre-existing formatting drift in nine
unrelated Rust files:

- `crates/axeyum-bench/examples/audit_dominance.rs`;
- `crates/axeyum-cas/src/combinatorics.rs`;
- `crates/axeyum-cas/src/gosper.rs`;
- `crates/axeyum-cas/src/lib.rs`;
- `crates/axeyum-cas/src/ntheory_advanced.rs`;
- `crates/axeyum-cas/src/ntheory_more.rs`;
- `crates/axeyum-cas/src/orthopoly.rs`;
- `crates/axeyum-cas/src/series.rs`; and
- `crates/axeyum-cas/src/special.rs`.

R6 changes no Rust and does not reformat another lane's files. The final
result will record the complete `just test` and Glaurung QF_BV gate outcomes.

## 4. Parity truth after integration

The regenerated authorities remain deliberately zero-credit:

```text
LEAN_COMPLETE_PARITY|populations=10|complete_populations=0|axes=12|complete_axes=0|paired_cells=0|gates_satisfied=0|terminal_ready=false
```

Supporting generated summaries likewise report zero real Lean outcomes, zero
Axeyum outcomes, zero matched pairs, and zero parity credit. The retained M2 R6
authority records 64 fixture passes but only a local shard: it has no accepted
parent/provider observation and therefore creates no official-process credit.

No official Lean, Axeyum, M2.1--M2.7, SMT-solver, network, or retained-evidence
execution was launched by R6. Integration removes the worktree-path blocker;
it does not establish complete Lean 4 parity.
