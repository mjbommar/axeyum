# Lean complete-parity current-main integration R2 incomplete result

Date: 2026-07-23

Status: **stopped at acceptance replay; no integration handoff or parity credit**

Plan: [R2 integration plan](lean-complete-parity-main-integration-r2-plan-2026-07-23.md)

Base: `ec1e469680ee3aaed6efc66484969fdc08dc3053`

## Result

R2 successfully extracted the prerequisite historical/current acceptance-input
split and all four accepted ROOT-relative repair commits onto current `main`.
The exact retained process check now passes:

```text
LEAN_PROCESS_RESULT|controls=8|files=40|real_outcomes=0|paired_cells=0|parity_credit=0
```

Current-main SMT commit `60f98ae9` had also changed
`scripts/smtcomp_repro/resume_contract.py` by adding
`solver_environment_sha256`. R2 bound that exact current successor separately
from the historical U2 source row, then propagated the resulting exact current
U2 validator identity into M2. Historical result source hashes remain unchanged.

Two copied-evidence tests also assumed that Git would preserve source-worktree
`0444` modes. Their temporary fixtures now explicitly recreate creation-time
read-only permissions before testing live-store validation. The complete
retained-evidence stack passed 169 tests with one expected skip, and the
terminal generator reached its unchanged honest result:

```text
LEAN_COMPLETE_PARITY|populations=10|complete_populations=0|axes=12|complete_axes=0|paired_cells=0|gates_satisfied=0|terminal_ready=false
```

## Stop condition

`just parity-docs` passed the process and store result checks, then stopped at
`scripts/lean_execution_acceptance.py result --check`. The current checkout
uses group-writable non-executable mode `0664` under the repository's shared
Git configuration. Acceptance replay recognizes only live `0444` or exact
filesystem `0644`, even when Git records a clean tracked `100644` blob.

Consequently:

- all 41 exact failed-attempt files reported invalid mode; and
- the four retained preparation stdout/stderr sidecars reported build-log
  identity drift through the same mode helper.

No content, manifest, seal, path, Git-index, or result-authority drift was
reported. R2 stops without a green branch, detached replay, push, integration
handoff, external process, or parity credit. A new source-first correction must
define the portable Git representation before changing acceptance validation.

## Nonclaims

The passing focused tests and process/store checks do not make the branch
merge-ready. The retained acceptance result, full parity-doc gate, link gate,
`just check`, and differently rooted replay remain mandatory.
