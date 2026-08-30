# Lane: nat-mod-mul — the ml430 Nat mod/mul digit-decomposition family

<!-- plan-section: lane-status -->

**Done (`DONE`, nat-mod-mul, 2026-08-29).** All five targets closed; none
were already proved under these names (checked `nat_theorem_inventory
--release` before starting -- `mod_mul`, `mod_mul_left_mod`,
`mod_mul_right_mod`, `mod_mul_left_div_self`, `mod_mul_right_div_self` all
came back absent; no existing lemma in `division.rs`/`parity.rs` covered the
same shape either, confirmed by grepping proof bodies for `mod_mod`/`mod_mul`).

New file `crates/axeyum-lean-kernel/src/nat_prelude/mod_mul_lemmas.rs`
(`declare_mod_mul_family`, called right after
`declare_add_div_of_dvd_add_add_one` in `build_nat_prelude`, which sits on the
same dependency set). One reusable helper covered all five:

- `double_decompose(a, pos_a, b, pos_b, x)` reconstructs
  `divMod (a*b) x ((x/a)/b) (x%a + a*(x/a%b))` for positive `a`, `b` from two
  `div_mod_exec` decompositions (`x` at `a`, then `x/a` at `b`), combined via
  `left_distrib`/`mul_assoc`/`add_assoc`/`add_comm`. `mod_mul_eq` compares it
  against the canonical decomposition of `x` at `a*b` via `div_mod_unique` to
  get `Nat.mod_mul` directly (`F:ml430-nat-mod-mul-beaccbad`).
- `mod_of_dvd_mod(dvsr, mult, e, e_eq, a)` is the general "`e` a multiple of
  `dvsr` implies `a % e % dvsr = a % dvsr`" fact, built the same way (a second
  `divMod dvsr a _ rd` decomposition compared via `div_mod_unique`) rather
  than derived from `mod_mul`. Closes `mod_mul_left_mod` and
  `mod_mul_right_mod` (the two differ only in which of `b`/`c` is `dvsr`, and
  whether `e_eq` needs a `mul_comm` bridge or is `refl`).
- `mod_mul_div_self(n, k, m, e, e_eq)` chains `mod_mul_eq` +
  `add_mul_div_left` (already declared, same dispatch batch) + a third local
  helper `div_of_lt` (the generic "a value below the divisor divides to `0`"
  fact) to get `div (mod m e) n = mod (div m n) k`. Closes
  `mod_mul_left_div_self` and `mod_mul_right_div_self`.

Detail moved to [`../notes/298-nat-mod-mul.md`](../notes/298-nat-mod-mul.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-mod-mul | `0f07031a6` new `nat_prelude/mod_mul_lemmas.rs`: `mod_mul`, `mod_mul_left_mod`, `mod_mul_right_mod`, `mod_mul_left_div_self`, `mod_mul_right_div_self`, kernel type-checked. |
| 2026-08-29 | nat-mod-mul | `99c59c0c1` register the five names in `theorem_names`, bump `the_build_is_deterministic`'s pin 93+538 -> 93+543, fix rustfmt mod/use order, fix a clippy too-many-arguments miss. `cargo test --lib nat_prelude::` 169 passed. |
| 2026-08-29 | nat-mod-mul | `46ddfaf3e` flip all five `F:ml430-nat-mod-mul-*` facts to `proved` with kernel-term + axiom-footprint evidence; `validate-facts.py` 0 errors. |
