# Lane: nat-testbit-bitwise — the `Nat.testBit` x bitwise-operator bridge

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (1 of 4 landed as a new local fact; 3 blocked from
an ml430 flip by verified reasons independent of proof difficulty)`,
nat-testbit-bitwise, 2026-08-29).**

Before writing any kernel code, verified (Step 0 of the brief) whether the
four assigned facts are actually closeable, and found a same-day blocker the
brief was not aware of: `docs/plan/status/235-nat-bitwise-facts.md` (a full
triage of all 19 `natural-bitwise` facts, landed earlier in this session)
already establishes that **none of the four facts this lane was assigned can
be honestly closed as pinned `ml430` mirrors**, for two independent reasons,
both re-verified directly against the current tree rather than trusted from
the doc:

1. **Genuine codomain mismatch.** Mathlib's `Nat.testBit (n i : Nat) : Bool`
   (confirmed at use sites — `testBit_land` states
   `testBit (m &&& n) k = (testBit m k && testBit n k)` using `Bool.&&`).
   Our `Nat.testBit` (`nat_prelude/binary.rs`, `testBitAux`) is
   `Nat -> Nat -> Nat`, returning `{0,1}` as a `Nat` (confirmed by reading
   `declare_test_bit_defs` and `test_bit_le_one` directly). This is not an
   alternate construction of the same type — closing a Bool-typed pinned
   `formal.statement` with a Nat-valued proof would be "manufacturing a
   flip" against CLAUDE.md's own honest-flip criterion.
2. **A live gate would break regardless of provability.**
   `scripts/gen-autogenesis-bitwise-family-projection.py` (invoked by
   `just autogenesis-bitwise-semantic-law-demand`, confirmed present in
   `justfile:667`, NOT part of `just check`'s dependency chain) hard-`raise`s
   if `F:ml430-nat-testbit-land-dfef7ca4` / `-lor-` / `-ldiff-`
   `epistemic_status != "open"`. This applies independently of (1) — even a
   fully honest Bool-valued proof would still break this named recipe.

`F:ml430-nat-zero-of-testbit-eq-false-e244c9a1` is not in that gate script's
mapping, but still has problem (1): its statement is
`(∀ i, n.testBit i = false) → n = 0`, Bool-valued.

Detail moved to [`../notes/244-nat-testbit-bitwise.md`](../notes/244-nat-testbit-bitwise.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-testbit-bitwise | Verified all four assigned facts are blocked from an `ml430` flip (codomain mismatch; 3 of 4 additionally by a live gate script); landed `F:nat-zero-of-testbit-eq-zero` as a new local fact (`Nat.testBit_of_zero`, `Nat.sumRange_const_zero`, `Nat.zero_of_testBit_eq_zero`); sized the `testBit_land`/`_lor`/`_ldiff` fuel/index bridge in full detail for the next lane |
