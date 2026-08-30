# Lane: nat-lor-assoc -- `Nat.lor_aux_ne_zero_of_right_ne_zero` landed, `lor_assoc` characterized in full but not closed

<!-- plan-section: lane-status -->

**Your lane's block (`OPEN`, nat-lor-assoc, 2026-08-29).** `Nat.land_assoc`
closed today after five lanes (`docs/plan/status/261-nat-land-assoc-finish.md`).
This lane's task was the `lor` counterpart, explicitly flagged as **not** a
transport — and it is not: the direct analogue of land's zero-propagation
lemma is FALSE for `lor`, confirmed by exhaustive Python simulation before
any Rust. What landed: the correct replacement invariant, kernel-verified
and tested, plus a complete, numerically-cross-checked derivation for
everything else `lor_assoc` needs. `F:ml430-nat-lor-assoc-82c4d0fd` remains
`open` — this lane did not close it, but leaves the hard mathematical
content (the invariant) done and the remaining assembly fully traced.

## What landed and is kernel-checked

**`Nat.lor_aux_ne_zero_of_right_ne_zero : ∀ fuel m n, Not (Eq n 0) →
Not (Eq (lorAux fuel m n) 0)`** (`rec_agreement.rs`), unconditional in
`fuel` — at `fuel = 0`, `lorAux 0 m n` is defeq `n` regardless of `m`
(the zero-fuel row ignores its first value argument entirely), so the
statement AT `fuel = 0` is literally the identity function on the
hypothesis. Built via `agree_by_fuel_induction`:

Detail moved to [`../notes/266-nat-lor-assoc.md`](../notes/266-nat-lor-assoc.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-lor-assoc | `Nat.lor_aux_ne_zero_of_right_ne_zero` — the invariant that replaces "zero propagates" for `lor_assoc`'s hard leaf, kernel-verified and tested (land's direct analogue is FALSE for `lor`, confirmed numerically before any Rust: `lor a b = 0` forces `a=b=0`, so `lor a (lor b c)` collapses to `c`, not `0`); a complete, numerically-cross-checked derivation for the rest of `lor_assoc` (the full `lor_aux_assoc_of_fuel` case tree — SIMPLER than `land`'s hard leaf once this invariant exists, since `X`/`Y` are unconditionally positive rather than needing a real zero/nonzero dichotomy — plus the one remaining new lemma `lor_bit_assoc` and the refuel bound `lor_aux_le_add`, both fully specified); `F:ml430-nat-lor-assoc-82c4d0fd` remains open |
