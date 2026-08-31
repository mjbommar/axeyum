# Lane: quadratic-residue-two — Euler's criterion necessary direction, toward the second supplementary law

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, quadratic-residue-two, 2026-08-31).** Landed
`Int.euler_criterion_residue_imp_one` (residue ⟹ half-power `≡ 1`, not
merely `≡ ±1`) and `Int.euler_criterion_neg_one_imp_not_residue` (odd-prime
non-residue detector), both axiom-free, in a new
`crates/axeyum-lean-kernel/src/int_prelude/qr_criterion.rs`. Full details,
route, and exact remaining work in
[ADR-0960](../research/09-decisions/adr-0960-euler-criterion-necessary-direction-lands-second-supplementary-law-stays-open.md).

**The second supplementary law (2 is a QR mod `p` iff `p ≡ ±1 mod 8`) is NOT
reached and is not reachable from what landed here alone.** It needs one of:
(1) the full converse of Euler's criterion — a primitive root or an
`x^m - 1`-has-at-most-`m`-roots argument, neither buildable with this
kernel's inductive list (no `List`/`Finset`/polynomial carrier); or (2)
Gauss's lemma — a `Nat.countRange`-shaped least-residue sign-count, also
absent. Either route, once built, still needs a four-way case split on
`p mod 8` to pin the sign for `a := 2` specifically. None of this was
attempted; it is real, multi-session work, sized (not just gestured at) in
ADR-0960's "What remains" section for whichever lane picks it up next.

Verification run this session: `cargo test -p axeyum-lean-kernel --lib
int_prelude::` (52 passed, 0 failed), `cargo clippy -p axeyum-lean-kernel
--lib -- -D warnings` (clean), `theorem_axiom_footprint --release` on both
new names (0 each), `python3 scripts/check-autogenesis-holdout-isolation.py`
(PASS before and after — `artifacts/autogenesis/` untouched this session).

<!-- plan-section: landed-changes -->

| 2026-08-31 | quadratic-residue-two | `Int.euler_criterion_residue_imp_one` + `Int.euler_criterion_neg_one_imp_not_residue` land axiom-free in new `int_prelude/qr_criterion.rs`, extending Euler's criterion toward the second supplementary law (ADR-0960); the law itself stays open, sized for the next lane. |
