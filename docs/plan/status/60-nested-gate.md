# Lane: agent-nested-gate — adversarial coverage for the fourth admission gate

<!-- plan-section: lane-status -->

**Round 4: `restore_nested_inductive_group` now has adversarial coverage, and
the reason it did not was a defect in the instrument, not a property of Lean
(`DONE`, agent-nested-gate, 2026-08-18).** Round 3 left the fourth admission
gate uncovered and stated why: a NESTED group's *undamaged* stream failed on
`axeyum_wire_rose.rec_1`, read as "`addDeclCore` regenerates the group's own
recursor but not the auxiliary one, so every field of an auxiliary recursor is
a byte Lean never reads". Stopping there was right; the reading was wrong.

Detail moved to [`../notes/60-nested-gate.md`](../notes/60-nested-gate.md).

<!-- plan-section: landed-changes -->

| 2026-08-18 | (this change) | Round 4: the fourth admission gate (`restore_nested_inductive_group`) gains adversarial coverage — the auxiliary recursor was never unread by Lean's kernel, only by `Environment.find?`, the elaborator's lookup; the replay script now asks `env.toKernelEnv`, a nested group is on the wire, and 14 `ind.aux-*` families cover it. 0 violations in 274 and 752 mutants, 80 families; residue measured exhaustively and is one non-type-checking field |
