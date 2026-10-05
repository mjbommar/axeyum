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

**Held-out check, run before and after: NONE of the nine dispatchable
`fermatNumber` facts were held-out.** ADR-0542-style amendment in
`artifacts/autogenesis/nursery-v2-extension.json`'s `amendments` array (dated
2026-08-30, referencing commit `0065c83b1`) had already moved the WHOLE
`fermat-numbers` family from held-out to `development` before this lane
started — confirmed by reading each of the nine target facts' `partition`
field directly in that manifest (all `"development"`), not merely by the
dispatchable-frontier script. `python3
scripts/check-autogenesis-holdout-isolation.py` reports
`settled=0|references=0|verdict=PASS` unchanged from before this lane's first
commit to after its last.

**`F:ml430-nat-fermat-primefactors-one-lt-58343c6f` — LEFT OPEN, genuinely
blocked, not merely unattempted.** Statement: `1 < n -> Prime p -> p |
n.fermatNumber -> exists k, p = k * 2^(n+2) + 1` (Lucas's refinement of the
classical Fermat-divisor theorem). This needs, in order: (1) a theory of the
multiplicative order of an element mod `p` (minimality + "order divides any
exponent making the power ≡ 1", itself a nontrivial induction) — ABSENT from
this kernel (checked: no `order_of`/`orderOf`/`multiplicative_order` name
anywhere in `nat_prelude.rs` or `int_prelude.rs`); (2) from `p |
fermatNumber n`, that the order of 2 mod p is EXACTLY `2^(n+1)`, giving
`2^(n+1) | p-1` via Fermat's little theorem (`Nat.pow_prime_modeq_self`
EXISTS and would supply this half); (3) the STRONGER `2^(n+2) | p-1` needs
knowing 2 is a quadratic residue mod `p` when `p ≡ 1 (mod 8)` — the second
supplementary law of quadratic reciprocity. `int_prelude/euler.rs` has
`Int.IsQuadraticResidue` and the UNCONDITIONAL half of Euler's criterion
(`a^m ≡ ±1`), but its own module doc says explicitly: "The full criterion —
that the SIGN decides quadratic-residue-hood — needs a primitive root or a
counting argument neither this file nor `wilson.rs` builds." That missing
sign-determination is exactly what step (3) needs. This is a multi-day
formalization project on its own (an order-of-element theory plus enough of
quadratic reciprocity to fix the sign), not a next slice. Left `open`, no
code written against it, no fact touched.

<!-- plan-section: landed-changes -->

| 2026-08-30 | fermat-mirrors | `Nat.fermatNumber_ne_one`/`_mono`/`coprime_fermatNumber_fermatNumber` — three new axiom-free kernel theorems (`nat_prelude/fermat_number_mirrors.rs`), facts flipped to `proved` with evidence, 208 `nat_prelude::` tests passing (was 204). |
