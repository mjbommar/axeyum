# Lane: fermat-mirrors — `ml430` mirrors against `Nat.fermatNumber`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for 3 of 4, 1 open`, fermat-mirrors, 2026-08-30).**
Closed three of the four dispatched `fermatNumber` mirrors with new,
axiom-free kernel constructions in
`crates/axeyum-lean-kernel/src/nat_prelude/fermat_number_mirrors.rs`:

- `F:ml430-nat-fermatnumber-ne-one-91232d67` (`Nat.fermatNumber_ne_one`) — CLOSED.
- `F:ml430-nat-fermatnumber-mono-b051cee6` (`Nat.fermatNumber_mono`) — CLOSED.
- `F:ml430-nat-coprime-fermatnumber-fermatnumber-161e79c7`
  (`Nat.coprime_fermatNumber_fermatNumber`, Goldbach's coprimality theorem) —
  CLOSED. Route: for `m < n`, `a := 2^(2^m)`, `t := n-m > 0`; `2^(2^n) =
  (a^2)^j` (`j := 2^(t-1)`) via `pow_add` + a locally-built `pow_mul_eq`;
  `modEq (a+1) (a*a) 1` by an EXPLICIT witness (`u=1, v=a`, no subtraction);
  `Nat.mod_eq_pow` + `mod_eq_add_right` give `fermatNumber n ≡ 2 (mod
  fermatNumber m)`; `Nat.ModEq.gcd_eq` + `fermatNumber m` odd
  (`coprime_two_left`) close it. All symbolic (no concrete Fermat number ever
  formed; largest numeral touched is `2`).

All three type-checked by `Kernel::add_declaration` on the FIRST attempt —
no failed intermediate attempts to report. Each is verified: (1) symbolically,
over a genuinely free variable via `infer_in` + `LocalContext` (not just
concrete instantiation — see CLAUDE.md's "concrete instantiation can hide the
bug a symbolic one exposes" entry); (2) at two small concrete pairs
(`fermatNumber 0/1 = 3/5`, `1/2 = 5/17`, the second exercising the theorem's
other case branch and its `coprime_symmetric` swap); (3) against a REFLEXIVE
NEGATIVE CONTROL for the coprime theorem confirming its `Ne m n` hypothesis
is load-bearing: `gcd(fermatNumber 0, fermatNumber 0) = gcd(3,3) = 3`,
explicitly asserted NOT defeq to `1`.

New test: `nat_prelude_tests.rs::
fermat_number_mirrors_apply_at_free_and_concrete_instances_with_a_reflexive_negative_control`.
`cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 208 passed (was 204
before this lane), 0 failed. `cargo clippy -p axeyum-lean-kernel --all-targets
--all-features -- -D warnings` — clean. `cargo fmt --all --check` — clean.

Detail moved to [`../notes/370-fermat-mirrors.md`](../notes/370-fermat-mirrors.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | fermat-mirrors | `Nat.fermatNumber_ne_one`/`_mono`/`coprime_fermatNumber_fermatNumber` — three new axiom-free kernel theorems (`nat_prelude/fermat_number_mirrors.rs`), facts flipped to `proved` with evidence, 208 `nat_prelude::` tests passing (was 204). |
