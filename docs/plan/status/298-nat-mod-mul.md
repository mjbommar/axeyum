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

Every degenerate case (a factor `= 0`) is handled by `cases_zero_succ` nested
case splits that collapse via `zero_mul`/`mul_zero`/`mod_zero`/`div_zero`/
`zero_mod`/`add_zero`/`zero_add` congruence -- none of these five Mathlib
statements carry a positivity hypothesis, so all had to hold unconditionally.

**What cost the most time, for whoever writes the next family like this:**
nested `d.foo(d.bar(...))` calls do not borrow-check (`&mut NatDev` twice) --
every one has to be flattened into a `let` first, and `cargo check` catches
every instance of that. It does **not** catch a `d.chain(start, steps)` whose
first supplied step proves `Eq(something_else, next)` rather than
`Eq(start, next)` -- that is a real bug (found one in `mod_of_dvd_mod`'s main
equation chain, and a similar collapsed-double-`mod_zero` step bug in
`mod_mul_left_mod`'s `a=0` branch) that only the kernel's own
`add_declaration` type-checking catches, at `cargo test`. Both were fixed
before the first full green run.

Evidence: each fact carries a `kernel-term` row (`nat_theorem_inventory`,
anchored `grep -Ec '^Nat\.<name>[[:space:]]'`, verified to return exactly 1 on
the real name and 0 on a nonexistent one -- the anchor is safe against the
`mod_mul`/`mod_mul_left_mod` prefix collision because the pattern requires
whitespace immediately after the name, not an underscore) and an
`exhaustive-enumeration` row (`nat_axiom_inventory --require-axiom-free nat`,
exit 0). `depends_on` for all five was filled in with
`scripts/check-fact-depends-derived.py --fix` after a hand-written first pass
missed several transitively-used lemmas the checker derives directly from the
kernel proof term (`Nat.add_lt_add_left`, `Nat.mul_le_mul_left`,
`Nat.mul_succ`, `Nat.one_le_mul`, …) -- trust the checker's derivation over a
hand-assembled list here.

Checks run: `cargo check -p axeyum-lean-kernel` (clean); `cargo test -p
axeyum-lean-kernel --lib nat_prelude::` -> 169 passed, 0 failed (matches the
brief's expected count; includes `the_nat_prelude_declares_no_axioms`,
`the_build_is_deterministic` after bumping its rendered-count pin from
`93 + 538` to `93 + 543` off the panic's own mismatch, and
`every_nat_declaration_is_checked_and_axiom_free` after registering the five
new names in `theorem_names`); `cargo clippy -p axeyum-lean-kernel
--all-targets -- -D warnings` (clean, needed
`#[allow(clippy::too_many_arguments)]` on `mod_mul_div_self` and
`mod_of_dvd_mod`); `rustfmt --edition 2024 --check` on all three touched Rust
files (clean); `python3 scripts/check-test-attribute-integrity.py` (0
findings); `python3 scripts/validate-facts.py` -> 2074 facts checked, 0
errors. Did not run the workspace-wide gate (out of scope per the brief).

Nothing left blocked in this family -- all five targets closed, no partial
work.

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-mod-mul | `0f07031a6` new `nat_prelude/mod_mul_lemmas.rs`: `mod_mul`, `mod_mul_left_mod`, `mod_mul_right_mod`, `mod_mul_left_div_self`, `mod_mul_right_div_self`, kernel type-checked. |
| 2026-08-29 | nat-mod-mul | `99c59c0c1` register the five names in `theorem_names`, bump `the_build_is_deterministic`'s pin 93+538 -> 93+543, fix rustfmt mod/use order, fix a clippy too-many-arguments miss. `cargo test --lib nat_prelude::` 169 passed. |
| 2026-08-29 | nat-mod-mul | `46ddfaf3e` flip all five `F:ml430-nat-mod-mul-*` facts to `proved` with kernel-term + axiom-footprint evidence; `validate-facts.py` 0 errors. |
