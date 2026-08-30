# Lane: nat-lor-assoc-exec -- `Nat.lor_assoc` executed and closed

<!-- plan-section: lane-status -->

**`F:ml430-nat-lor-assoc-82c4d0fd` is now `proved`.** This lane executed
`docs/plan/status/266-nat-lor-assoc.md`'s fully hand-traced,
Python-simulated derivation, verifying every step against the actual
`guarded`/`agree_by_fuel_induction`/`agree_by_double_fuel_induction`
signatures rather than trusting the prose. All four traced pieces held on
the first kernel-check attempt after one self-caught wiring bug (below);
`lor_aux_le_add` -- the ONE piece the tracing lane flagged as not
sub-step-verified in Python -- held exactly as specified, with no break.

## What was built (`rec_agreement.rs`)

Detail moved to [`../notes/267-nat-lor-assoc-exec.md`](../notes/267-nat-lor-assoc-exec.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-lor-assoc-exec | Closed `F:ml430-nat-lor-assoc-82c4d0fd` (`Nat.lor_assoc`) via new native `F:nat-lor-assoc` -- executed `docs/plan/status/266-nat-lor-assoc.md`'s full trace (`lor_bit_assoc`, `lor_aux_assoc_of_fuel`, `lor_aux_le_add`, `lor_assoc`) verbatim; every traced step held, including `lor_aux_le_add`, the one piece the tracing lane had not sub-step-verified in Python. One transcription bug (a `y_succ_case` closure closing over the wrong dichotomy's binders) found and fixed by self-review before the first compile; kernel accepted on the first check thereafter. `nat_prelude::` 152 -> 153 tests, axiom-free, `the_build_is_deterministic` pin `93+505 -> 93+508` |
