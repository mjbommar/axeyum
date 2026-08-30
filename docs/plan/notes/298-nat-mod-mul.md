# Notes: 298-nat-mod-mul

Detail moved out of [`../status/298-nat-mod-mul.md`](../status/298-nat-mod-mul.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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
