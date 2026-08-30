# Lane: nat-gcd-dvd-mirrors — ℕ gcd/divisibility `ml430` mirrors

<!-- plan-section: lane-status -->

**Eleven mirrors closed (`WIP` -> mostly done, nat-gcd-dvd-mirrors,
2026-08-30).** Of the nineteen dispatchable in this area, closed:

- **Two pure flips, no new proof.** `F:ml430-nat-dvd-gcd-e5184fc5` and
  `F:ml430-nat-dvd-gcd-iff-b8485987` are `Nat.dvd_gcd`/`Nat.dvd_gcd_iff`,
  which predate this session (`declare_gcd_semantics`, `nat_prelude/gcd.rs`).
  The rendered type matches `formal.statement` exactly; closed by evidence
  only.
- **Nine new proofs**, all in the new file
  `crates/axeyum-lean-kernel/src/nat_prelude/gcd_dvd_mirrors.rs`, wired in
  with one `declare_gcd_dvd_mirrors` call:
  `Nat.dvd_mul_left`, `Nat.dvd_mul_left_of_dvd` (not in the original
  nineteen-item list but dispatchable in the same shape-search sweep and
  equally cheap — `dvd_mul_right_of_dvd` + `mul_comm`),
  `Nat.eq_zero_of_gcd_eq_zero_{left,right}`, `Nat.dvd_mod_iff_gen`,
  `Nat.div_mul_cancel`, `Nat.dvd_iff_mod_eq_zero`, and
  `Nat.div_gcd_pos_of_pos_{left,right}`.

All nine new declarations are axiom-free (`nat: axiom=0 opaque=0
quotient=0`), registered in `theorem_names`/`the_build_is_deterministic`'s
pin (669 -> 676 after the first seven, -> 678 (`93 + 585`) after the two
`div_gcd_pos_of_pos_*` theorems), and covered by the environment-derived
`every_nat_declaration_is_checked_and_axiom_free` assertion. Full
`nat_prelude::` sweep: 181 passed, 0 failed.

Every fact's `checker_command` was run directly (not just written): the
exact-name `grep -Ec '^Nat\.<name>[[:space:]]'` was checked to discriminate
against the substring-overlapping sibling in each case that has one
(`dvd_gcd` vs `dvd_gcd_iff`, `div_mul_cancel` vs `div_mul_cancel_of_dvd`,
`div_gcd_pos_of_pos_left` vs `_right`), and `nat_axiom_inventory
--require-axiom-free nat` was run and confirmed `nat: axiom=0 opaque=0
quotient=0` after every batch.

Partition check before touching any fact: all eleven are `train`/
`development` in `artifacts/autogenesis/nursery-v2-extension.json` — none
held-out.

Detail moved to [`../notes/331-nat-gcd-dvd-mirrors.md`](../notes/331-nat-gcd-dvd-mirrors.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | `b410fb749` | New `nat_prelude/gcd_dvd_mirrors.rs`: seven theorems, one `declare_*` call. |
| 2026-08-30 | `c20464d53` | Register the seven in `theorem_names`, recount `the_build_is_deterministic` pin. |
| 2026-08-30 | `935dde5e2` | Close nine ml430 facts (two flips, seven new) + depends_on cascade fix (24 files). |
| 2026-08-30 | `d92fb202d` | `div_gcd_pos_of_pos_{left,right}` — two more theorems, shared helper. |
| 2026-08-30 | `126aee313` | Close the two `div_gcd_pos_of_pos_*` facts + depends_on fix. |
| 2026-08-30 | `d255ef6e2` | rustfmt fix. |
