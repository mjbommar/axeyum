# Notes: 297-nat-mul-order

Detail moved out of [`../status/297-nat-mul-order.md`](../status/297-nat-mul-order.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Checks run (foreground): `cargo fmt --all --check` clean;
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` clean;
`env -u RUST_MIN_STACK scripts/cargo-serialized.sh test -p axeyum-lean-kernel
--lib nat_prelude::` → **170 passed, 0 failed** (169 pre-existing + 1 new);
`python3 scripts/check-test-attribute-integrity.py` → 0 findings.

Facts closed (`open` → `proved`): `F:ml430-nat-mul-lt-mul-left-af33301e`,
`F:ml430-nat-mul-lt-mul-right-de5b6046`,
`F:ml430-nat-lt-of-mul-lt-mul-left-234e8530`,
`F:ml430-nat-lt-of-mul-lt-mul-right-54c1120b`,
`F:ml430-nat-div-lt-of-lt-mul-818dc4c7`. Each carries three evidence rows
(exact rendered-type match against `nat_theorem_inventory`, axiom-footprint
via `nat_axiom_inventory --require-axiom-free nat`, coverage via
`every_nat_declaration_is_checked_and_axiom_free`); every `checker_command`
verified to pass on the real name and fail (count 0) on a nonexistent one.
`depends_on` edges added via `scripts/check-fact-depends-derived.py --fix`.
`python3 scripts/validate-facts.py` → 0 errors.

Not attempted: no further targets in this family were assigned. Next lane
picking up `Nat` order work should re-run `prelude_theorem_inventory
--release` step 0 before starting, per the standing rule.
