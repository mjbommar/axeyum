# Lane: int-dvd-mirrors — ℤ divisibility/gcd/`ModEq` `ml430` mirrors

<!-- plan-section: lane-status -->

**Fourteen of twenty dispatchable mirrors closed (`WIP` -> mostly done,
int-dvd-mirrors, 2026-08-30).**

- **Two pure flips, no new proof.** `F:ml430-int-dvd-coe-gcd-6bda035e` is
  `Int.dvd_gcd` (our internal name), which is Mathlib's `Int.dvd_coe_gcd`
  (an **Int**-typed divisor, cast around `a.gcd b`) — predates this lane
  (`gcd.rs`'s `declare_dvd_gcd`). `F:ml430-int-modeq-add-right-fa8f7abe` is
  `Int.modEq_add_right` (rendered name is camelCase, not the Rust field's
  snake_case `mod_eq_add_right`) — already unconditional in the modulus,
  predates this lane. Both closed by evidence only, no code.
- **Twelve new proofs**, all in the new file
  `crates/axeyum-lean-kernel/src/int_prelude/dvd_gcd_mirrors.rs`, wired in
  with one `dvd_gcd_mirrors::declare_all` call at the very end of
  `build_int_prelude`'s sequence (after every dependency):
  `Int.dvd_gcd_nat`/`Int.dvd_gcd_nat_iff` (Mathlib's actual `Int.dvd_gcd`/
  `.dvd_gcd_iff` — Nat-typed divisor, distinct from the coe form above),
  `Int.dvd_coe_gcd_iff`, both `Int.ediv_gcd_ne_zero_*` facts,
  `Int.mod_eq_add`, `Int.mod_eq_add_right_cancel` (single-`c` form,
  Mathlib's `.add_right_cancel'`), `Int.mod_eq_add_left_cancel_general` /
  `Int.mod_eq_add_right_cancel_general` (4-variable forms — **not** the
  same propositions as the existing single-`c` `mod_eq_add_left_cancel`,
  despite the name overlap), `Int.mod_eq_dvd`, `Int.mod_eq_emod_eq`, and
  `Int.mod_eq_mul_general` (Mathlib's `Int.ModEq.mul`, genuinely
  UNCONDITIONAL — the existing `p.mod_eq_mul` needs `0 < n`).

Detail moved to [`../notes/335-int-dvd-mirrors.md`](../notes/335-int-dvd-mirrors.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | `f93339c90` | New `int_prelude/dvd_gcd_mirrors.rs` draft (not yet compiled). |
| 2026-08-30 | `3d10a5644` | Fix E0499 double-mutable-borrow; `cargo check` passes. |
| 2026-08-30 | `13447b182` | Register 11 new declarations in `derived_laws`, recount pin 196 -> 207. |
| 2026-08-30 | `c30820148` | Close 13 ml430 facts (2 flips, 11 new) + `depends_on` cascade fix. |
| 2026-08-30 | `290cb422f` | Unconditional `Int.ModEq.mul` (`mod_eq_mul_general`); recount pin 207 -> 208. |
| 2026-08-30 | `9279ffe52` | Close `F:ml430-int-modeq-mul-6736aa2e` + `depends_on` cascade fix. |
