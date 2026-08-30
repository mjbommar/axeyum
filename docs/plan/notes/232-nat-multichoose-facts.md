# Notes: 232-nat-multichoose-facts

Detail moved out of [`../status/232-nat-multichoose-facts.md`](../status/232-nat-multichoose-facts.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

The statement TEXT does match exactly (`Nat.multichoose_zero_right`,
`_one`, `_one_right` — same names, same universally-quantified shape,
verified against `formal.statement` in each `ml430` JSON and each theorem's
`Kernel::render_lean`'d type), so the boundary values are the same and both
libraries' theorems are true of both functions. What differs is the function
symbol they are about, which is exactly what "flip" would misrepresent.

Verification run: `cargo test -p axeyum-lean-kernel --lib nat_prelude` — 117
passed, 0 failed (includes `the_build_is_deterministic`, pinned at
`85 + 429`, unchanged; `every_nat_declaration_is_checked_and_axiom_free`;
`multichoose_evaluates_correctly`). `cargo fmt --all --check` clean. No
source files touched by this lane — the definition and the three theorems
were already complete and correct.

**Skipped, as instructed:** `F:ml430-mutation-edb05acf07d9ef3f9f8232fc`
(`n.choose n = 0`, false — `choose_self` proves it is 1).

**Budget-permitting factorial bridge: not attempted.** No `ml430` fact names
a multichoose-in-terms-of-factorial identity to close (searched
`artifacts/facts/*multichoose*factorial*` and `*ml430*multichoose*` —
only the three zero-right/one/one-right mirrors exist), so there was no
concrete target to hang new proof work on without manufacturing a fact that
was not asked for.
