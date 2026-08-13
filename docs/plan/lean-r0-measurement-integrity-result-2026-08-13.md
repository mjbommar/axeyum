# Lean R0.1 measurement-integrity result

Status: implemented and locally verified; real-Lean CI execution pending

Date: 2026-08-13

Requirements:
[`lean-kernel-requirements-2026-08-13.md`](lean-kernel-requirements-2026-08-13.md),
R0.1.

## Finding

The enforced real-Lean lane was only partly fail-closed. With
`AXEYUM_REQUIRE_LEAN=1`, a deliberately missing `AXEYUM_LEAN_BIN`, and no Lean
on `PATH`, all four kernel differential suites and the representative solver
suite failed. The representative suite reported 70 modules not checked. Three
other named solver suites ran one test but returned success after printing a
skip:

```text
diophantine_lean_reconstruct|exit=0|running 1 test|[skip] diophantine
int_inequality_lean_reconstruct|exit=0|running 1 test|[skip] int_inequality
regex_emptiness_lean_reconstruct|exit=0|running 1 test|[skip] regex-emptiness
```

The CI job also omitted `real_lean_structure_eta_crosscheck` and those three
solver suites. Its 70-module representative check was already non-vacuous: CI
matches an exact summary containing `modules=70|checked=70|failed=0`.

## Change

Each formerly optional-only solver suite now treats a missing Lean executable
as an assertion failure when `AXEYUM_REQUIRE_LEAN=1`, including all three
real-Lean tests in `int_inequality_lean_reconstruct`. Optional local runs still
print the existing skip and pass when the variable is not set.

The real-Lean CI job now invokes all eight suites named by R0.1. The four added
commands run structure eta and one exact real-Lean module from each of the
Diophantine, integer-inequality, and regex reconstruction suites. The generated
complete-parity source identity was regenerated from the workflow change.

## Evidence

The four kernel missing-Lean controls each ran one test and exited 101 with
`AXEYUM_REQUIRE_LEAN=1 but no Lean binary was found`. The representative solver
control did the same while reporting 70 modules not checked. After the repair,
the three formerly inert controls report:

```text
diophantine_lean_reconstruct|exit=101|running 1 test|... (1 module NOT checked)
int_inequality_lean_reconstruct|exit=101|running 1 test|... (1 module NOT checked)
regex_emptiness_lean_reconstruct|exit=101|running 1 test|... (1 module NOT checked)
```

Ordinary no-Lean local execution remains green: 5 Diophantine, 14 integer
inequality, and 4 regex tests passed (23 total). Focused warning-denied Clippy
for the three test targets passed. `cargo fmt --all --check`, generated
complete-parity `--check`, plan authority, documentation links, and
`git diff --check` passed.

An all-solver-test Clippy attempt reached unrelated existing dead-code warnings
for `fp_literal` and `ground_quotient` in `tests/fp_ground_division.rs`; it is
not credited as a broad pass. `actionlint` parsed the edited workflow but
reported the pre-existing unregistered `ubuntu-26.04` runner label at line 85.

## Remaining gate

This host has no real Lean executable, so it cannot supply positive execution
evidence for the four newly enforced commands. R0.1's missing-tool fail-closed
behavior and nonzero-count contract are locally established; the updated job's
real-Lean outcomes remain pending until hosted CI executes the committed SHA.
