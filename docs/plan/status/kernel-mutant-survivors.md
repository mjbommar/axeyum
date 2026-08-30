# Lane: kernel-mutant-survivors

**Status:** IN PROGRESS (first commit, investigation notes only — no conclusion yet)

## Charter

Close the four SURVIVED entries in
`artifacts/kernel-differential/mutant-kill-table.json` (ADR-0780, ADR-0717 S5).
The `inductives` survivor is unexplained and is the priority; `projections`,
`literals` and `quotient` have named corpus gaps with known shapes.

## Where I am

- Merged local `main` into this worktree — the differential landed there and
  was not on `origin/main` when the lane opened.
- Read `check_group_positive_occurrence`
  (`crates/axeyum-lean-kernel/src/inductive.rs:1917`) and the corpus case
  `inductives::non_positive_occurrence_negative`
  (`crates/axeyum-lean-kernel/tests/kernel_differential.rs:805`).

### Working hypothesis for the `inductives` survivor

The mutation gates the `NonPositiveInductiveOccurrence` `Err` behind
`false &&`. With that gone, `check_group_positive_occurrence` on the field
`Bad -> Codomain` descends into the Pi body `Codomain`, which does not mention
the family, and returns `Ok`. So positivity itself no longer rejects — yet the
case did not flip. Something ELSE in `add_inductive` must reject it. The next
step is to print the actual `KernelError` the UNMUTATED kernel returns for that
construction; if it is not `NonPositiveInductiveOccurrence`, the mutation was
aimed at a guard the case never reaches.

Nothing measured yet. This commit is notes, not a finding.
