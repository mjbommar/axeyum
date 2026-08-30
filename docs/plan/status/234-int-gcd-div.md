# Lane: int-gcd-div — the last three `integer-gcd-div` facts

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for this pass`, int-gcd-div, 2026-08-29).** One of
three facts landed, fully kernel-checked; the other two are re-scoped open
with a concrete, verified reason each — not "hard", a named missing lemma.

**Landed: `F:ml430-nat-exists-mul-mod-eq-gcd-8bf9ec7e`
(`Nat.exists_mul_mod_eq_gcd`).** The second-lane refutation in the brief
("this needs genuine Int/Nat mod-arithmetic bridging, not a corollary of the
Bezout witnesses") held under my own construction: `declare_exists_mul_mod_eq_gcd`
(`crates/axeyum-lean-kernel/src/int_prelude/gcd.rs`) reduces the Bezout
coefficient `Nat.gcdA n k` modulo `k` through `Int.modEq_add_mul_left` /
`Int.ModEq.mul_left` / `Int.mod_modEq` / `Int.ModEq.symm` (all pre-existing in
`modeq.rs`/`modeq_family.rs`) plus one call to `super::wilson::emod_eq_self_of_in_range`
(already `pub(super)`), then descends the resulting `Int` equation to the
stated `Nat` equation via `natAbs`. No new axiom, no infrastructure change
outside `gcd.rs` + one `IntPrelude` field + one build-order line. Verified:
`cargo test -p axeyum-lean-kernel --lib int_prelude::` — 40 passed, including
`every_int_declaration_is_checked_and_axiom_free` and
`derived_laws_have_no_axiom_footprint` — plus the fact's own
`theorem_axiom_footprint` grep checker, both run by hand before landing.
`cargo fmt --edition 2024 --check` and `cargo clippy -p axeyum-lean-kernel
--all-targets -- -D warnings` both clean. `python3 scripts/validate-facts.py`:
0 errors.

**Not landed, re-scoped open, both for the SAME underlying reason:**

Detail moved to [`../notes/234-int-gcd-div.md`](../notes/234-int-gcd-div.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | int-gcd-div | closed `F:ml430-nat-exists-mul-mod-eq-gcd-8bf9ec7e` via `declare_exists_mul_mod_eq_gcd`; `Int.gcd_div`/`Int.gcd_div_gcd_div_gcd` re-scoped open with a named blocking lemma gap each, not attempted half-finished |
