# Lane: agent-nested-gate — adversarial coverage for the fourth admission gate

<!-- plan-section: lane-status -->

**Round 4: `restore_nested_inductive_group` now has adversarial coverage, and
the reason it did not was a defect in the instrument, not a property of Lean
(`DONE`, agent-nested-gate, 2026-08-18).** Round 3 left the fourth admission
gate uncovered and stated why: a NESTED group's *undamaged* stream failed on
`axeyum_wire_rose.rec_1`, read as "`addDeclCore` regenerates the group's own
recursor but not the auxiliary one, so every field of an auxiliary recursor is
a byte Lean never reads". Stopping there was right; the reading was wrong.

- **Lean's kernel does build the auxiliary recursor.** What does not know about
  it is `Environment.find?` — the *elaborator's* lookup, which
  `scripts/lean/replay-lean4export.lean` was using. `addDeclCore` republishes
  only `Declaration.getNames` into the async constant map, and that function's
  own docstring says the list "does not include ... auxiliary recursors computed
  by the kernel for nested inductive types". Measured on one environment value
  under pinned 4.30.0: `env.find? …rec_1` is `none`, `env.constants.find?
  …rec_1` is a recursor with two motives, three minors and both ι-rules. The
  script now looks constants up in `env.toKernelEnv`. **One line; no exemption.**
  All three official nested fixtures replay clean where each previously failed
  with exactly one disagreement, and all seventeen official fixtures pass.
- **This is the repository's own gotcha, one level down.** An empty answer from
  a tool that was never pointed at your subject is indistinguishable from a
  strong negative result. `Environment.find?` ran, exited 0, and returned a
  correct `none` — to a question about the elaborator that had been asked about
  the kernel. The instrument has now lied about the kernel twice (an inert gate,
  and a lookup answering the wrong question); the solver still has not.
- **Coverage landed.** `axeyum_wire_rose` is on the wire (`inductive
  axeyum_wire_rose | node : axeyum_wire_list axeyum_wire_rose ->
  axeyum_wire_rose`), and fourteen new `ind.aux-*` mutation families damage the
  auxiliary recursor *specifically* — one family per field, so the stratifier
  cannot sample only main recursors and read as covered, and the exhaustive
  family list makes a family that stops generating a test failure.
  66 -> 80 families, 4,747 -> 5,172 mutants generated.
- **0 violations.** 274 checked at the default budget and 752 at
  `AXEYUM_WIRE_MUTANTS=1600`, 80 families, `stricter_than_lean` 0 and 1,
  17 of 17 auxiliary-recursor mutants discriminated by Lean's kernel both times.
  Plus 57 checks on official `lean4export` nested bytes (3 undamaged fixtures +
  54 auxiliary-recursor mutants, every one discriminated). Pinned
  `leanprover/lean4:v4.30.0`, `matches_pin=true`; 4.34.0-rc1 is installed and
  was not used.
- **The residue is measured, not asserted, and it is one non-type-checking
  field.** Exhaustively over the nested `inductive` record: 42 of 42 mutants,
  ours declined 42, Lean discriminated 42, 0 violations. Over the expression
  records only the auxiliary recursor reaches — 33 of this development's 888,
  the auxiliary analogue of round 2's 37% hole — all 178 mutants were checked:
  Lean discriminated 160 and accepted 18, and all 18 are `expr.binder-info`,
  which this suite documents as *expected* to agree because binder info is
  elaborator metadata neither kernel type-checks.
- **Both new guards were driven to failure, and neither masks the other.**
  Reverting the lookup to `Environment.find?` kills
  `the_official_nested_fixtures_reach_the_auxiliary_recursor` on the *undamaged*
  fixture; adding the exemption round 3 refused (skip a constant Lean did not
  publish) kills the same test on the *damaged* one; both together leave the
  main sweep's `MIN_AUX_RECURSOR_DISCRIMINATED` reporting 1 of 17 against a
  floor of 12, with no earlier floor firing first.
- **Still genuinely unreachable through this instrument:** `quot` records.
  `addDeclCore` ignores a quotient package's carried types and adds its own, so
  it accepts every damaged quotient record. That is a property of the interface,
  not of where we looked.

Next: the same lookup question applies to anything else Lean's kernel derives
but does not announce; and the auxiliary recursor is now comparable, so a
nested group with more than one auxiliary family (repeated / indexed containers)
is the cheapest next widening.

<!-- plan-section: landed-changes -->

| 2026-08-18 | (this change) | Round 4: the fourth admission gate (`restore_nested_inductive_group`) gains adversarial coverage — the auxiliary recursor was never unread by Lean's kernel, only by `Environment.find?`, the elaborator's lookup; the replay script now asks `env.toKernelEnv`, a nested group is on the wire, and 14 `ind.aux-*` families cover it. 0 violations in 274 and 752 mutants, 80 families; residue measured exhaustively and is one non-type-checking field |
