# Lane: nat-xor-cancel — `Nat.xor_xor_cancel_left`/`_right`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (Nat.xor_xor_cancel_left/_right landed, axiom-free; F:ml430-nat-lt-xor-cases-c43a1e85 stays open, 1 sub-target remains: Nat.xor_ne_zero_iff)`, nat-xor-cancel, 2026-08-29).**

## What landed

Both remaining sub-targets of piece 4 (`docs/plan/status/264-nat-xor-algebra.md`
diagnosed the route and left these two, plus the round-trip lemma, for this
lane):

```
Nat.xor_xor_cancel_left  : ∀ a b, Eq (xor a (xor a b)) b
Nat.xor_xor_cancel_right : ∀ a b, Eq (xor (xor a b) b) a
```

Both admitted axiom-free on the first successful attempt after one bisected
fix (see below), both with concrete-discriminating + symbolic evaluation
tests, both registered as new local facts (`F:nat-xor-xor-cancel-left`,
`F:nat-xor-xor-cancel-right`; neither has an `ml430` mirror — same reasoning
as `F:nat-xor-assoc`, recorded in full there).

All new code lives in `crates/axeyum-lean-kernel/src/nat_prelude/xor_algebra.rs`
(the file the brief assigned this lane), plus the minimal `nat_prelude.rs`
NameId registration and `nat_prelude_tests.rs` coverage-list/test additions
the brief said were expected.

## The `y <= 1` round-trip lemma — exact statement and route

`round_trip_le_one(d, p, y, h_le) : Eq (digitize (beq y 1)) y`, given
`h_le : Le y 1`, where `digitize(cond) := bool_select_nat cond 1 0`.

Detail moved to [`../notes/268-nat-xor-cancel.md`](../notes/268-nat-xor-cancel.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-xor-cancel | Landed `Nat.xor_xor_cancel_left` (via `Nat.testBit_xor` + a new per-bit cancel lemma needing a new `y <= 1` round-trip lemma the natural identity does not hold without, since it is FALSE for general `y : Nat`) and `Nat.xor_xor_cancel_right` (transported from `_left` via `Nat.xor_comm` twice, no new per-bit argument); both axiom-free with concrete+symbolic evidence, both new local facts (no `ml430` mirrors, same reasoning as `F:nat-xor-assoc`); a mislabeled chain intermediate in the theorem-level wiring found via a throwaway bisecting probe rather than by reading a 152-test poisoned failure list; `F:ml430-nat-lt-xor-cases-c43a1e85` stays `open` — only `Nat.xor_ne_zero_iff` remains of piece 4's four sub-targets, and its forward direction does NOT need the cancel lemmas (a direct corollary of `Nat.eq_of_testBit_eq` + `Nat.testBit_xor` + the same `{0,1}` case-split shape), while its reverse direction and `Iff` packaging were not attempted |
