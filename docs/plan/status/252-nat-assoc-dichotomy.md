# Lane: nat-assoc-dichotomy — the missing arithmetic + a verified proof plan for `land_aux_assoc_of_fuel`

<!-- plan-section: lane-status -->

**Your lane's block (`OPEN`, nat-assoc-dichotomy, 2026-08-29).** Neither
`F:ml430-nat-land-assoc-ad4775b8` (`Nat.land_assoc`) nor
`F:ml430-nat-lor-assoc-82c4d0fd` (`Nat.lor_assoc`) closed this session —
this is the third lane to stop at this wall. What landed: the missing
arithmetic item `docs/plan/status/247-nat-bitwise-assoc.md` named
(`Nat.add_eq_zero`) plus a second piece its own diagnosis needed but did
not name (`Nat.zero_or_succ`), both kernel-checked, tested, and
registered — and, more valuably, a **fully worked, numerically-verified
proof plan** for `land_aux_assoc_of_fuel` that goes well past the prior
diagnosis: it identifies the exact case tree, shows 6 of 8 base leaves
close by pure computation with **no new lemma at all**, and shows the
remaining hard leaf needs one more substantial theorem (not yet built)
whose own proof I traced through completely by hand and cross-checked in
Python.

**Why the actual `land_aux_assoc_of_fuel`/propagation-lemma code is NOT in
this commit, even though I have a verified plan for it:** both belong in
`rec_agreement.rs` (where their siblings `land_aux_comm_of_fuel`,
`land_aux_le_left` already live), and the brief that opened this lane
explicitly named `rec_agreement.rs`, `land.rs`, `lor.rs`, `ldiff.rs`,
`binary.rs` as files sibling lanes are in RIGHT NOW. Writing a
~300-400 line addition into a file under active concurrent edit is exactly
the shared-file collision this repository's multi-agent hygiene section
warns about, so I did not. Everything below is written so the next lane
into `rec_agreement.rs` can implement it directly without re-deriving any
of it.

## What landed and is kernel-checked

Detail moved to [`../notes/252-nat-assoc-dichotomy.md`](../notes/252-nat-assoc-dichotomy.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-assoc-dichotomy | `Nat.add_eq_zero`/`Nat.zero_or_succ` (the two remaining arithmetic pieces `land_aux_assoc_of_fuel` needs); a fully worked, numerically-verified proof plan showing 6 of 8 base leaves close by pure computation and the hard leaf needs exactly one new theorem (`land_aux_eq_zero_of_left_eq_zero`, fully traced) plus a 3-leaf (not 4- or 8-leaf) top structure; `land_assoc`/`lor_assoc` remain open — `lor_assoc` explicitly flagged as NOT a mechanical transport of this plan |
