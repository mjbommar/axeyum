# Lane: gcd-mul-right — `Nat.gcd_mul_right` and its three ml430 mirrors

<!-- plan-section: lane-status -->

**Done (`gcd-mul-right`, 2026-08-30).** `docs/plan/status/331-nat-gcd-dvd-mirrors.md`
left three `ml430` facts open, all blocked on one missing distributive lemma:
`Nat.gcd_mul_right : ∀ a b c, gcd (a*c) (b*c) = gcd a b * c`.

**Verified the lemma was genuinely absent, not a naming miss**, before writing
any induction: grepped `nat_prelude/gcd.rs` and `nat_prelude/lcm_gcd_lemmas.rs`
in full for any `gcd_mul_*` spelling (nothing), and `int_prelude/gcd.rs`'s own
module doc (around its `Int.gcd_div` construction) states explicitly that
neither `Nat.gcd_mul_left` nor `gcd_mul_right` exists in this development and
that building either needs a fresh strong-induction principle over `gcd`'s
well-founded recursion. (`Int.gcd_mul_right`, in that same file, is an
unrelated coprimality-descent proposition sharing the Mathlib name — checked
and ruled out as a transportable shortcut.)

**Built it**: `crates/axeyum-lean-kernel/src/nat_prelude/gcd_mul_right.rs`,
well-founded induction on the first argument mirroring `declare_gcd_bezout`'s
WF-fix scaffolding (`bezout.rs`) exactly — same relation (`lt_well_founded`),
same `family`/`step_motive`/`step` pattern. Two supporting pieces, both new:

- `mul_mod_mul_right_eq : mod(n*c, m*c) = (mod n m)*c` for positive `m` (built
  via `div_mod_reconstructed` + `div_mod_unique`, mirroring `mod_mul_eq`'s
  proof shape in `mod_mul_lemmas.rs`).
- `gcd_unfold_pos : gcd x y = gcd (mod y x) x` for arbitrary positive `x`,
  generalizing `gcd_succ` (which needs its first argument literally of shape
  `succ _`) the same way `div_mod_reconstructed` generalizes `div_mod_exec`.

Wired in as the LAST `declare_*` call in `build_nat_prelude`.

Detail moved to [`../notes/336-gcd-mul-right.md`](../notes/336-gcd-mul-right.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | `9a773bac4` | wip: `Nat.gcd_mul_right` proof term, not yet registered in coverage list. |
| 2026-08-30 | `dcd876d2c` | `Nat.gcd_mul_right` admitted, axiom-free, registered, tested (concrete + symbolic). |
| 2026-08-30 | `4b9d27239` | New `nat_prelude/gcd_mul_right_mirrors.rs`: all three ml430 mirrors, registered, tested. |
| 2026-08-30 | `52dbe8dad` | Flip the three facts to `proved` + `depends_on` cascade fix (3 files). |
