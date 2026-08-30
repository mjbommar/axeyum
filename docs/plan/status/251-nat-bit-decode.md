# Lane: nat-bit-decode — the `Nat.bit` decode bridge, `land_bit` closed

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-bit-decode, 2026-08-29).** `Nat.land_bit`
is landed (`F:ml430-nat-land-bit-b9ab7475` flipped open → proved), plus the
reusable `Nat.bit` decode bridge two prior lanes
(`docs/plan/status/237-nat-fuel-irrelevance.md`,
`docs/plan/status/239-nat-fuel-transport.md`) each independently named as
the blocker and did not attempt. `Nat.lor_bit`/`Nat.ldiff_bit` remain open
— see "What is still needed" below for a precise diagnosis of what each
needs beyond this lane's work.

**The construction, in `crates/axeyum-lean-kernel/src/nat_prelude/bit_decode.rs`
(new file, per the brief — did not touch `land.rs`/`lor.rs`/`ldiff.rs`/
`rec_agreement.rs`).** `land m n := landAux m m n` uses `m` itself as fuel,
and `bit a m` is not syntactically `zero`/`succ`-shaped for symbolic `a`,
`m` (`add (mul 2 m) (cond a 1 0)`, stuck), so the canonical fuel cannot be
unfolded by one `Nat.rec` step. The fix swaps the fuel via
`Nat.land_aux_eq_land_of_le` for an artificially chosen `succ`-shaped one
(`base := mul 2 m`, `k1 := succ base = bit true m`, `fuel := succ k1`),
both bounds (`Le (bit a m) fuel`, `Le m k1`) holding unconditionally
(`a = true` makes `bit a m` DEFEQ `k1` exactly; `m ≤ mul 2 m ≤ k1` via
`two_mul_eq_add_self` + `le_add_right` + `le_succ`). One `Nat.rec` step
then unfolds to the shared `guarded` combinator (reproduced locally rather
than made `pub(super)` in `rec_agreement.rs`, to avoid a cross-lane edit to
that file) at the raw `div`/`mod` subterms, decoded back to `(m, n)` by two
new lemmas — `Nat.bit_div_two`, `Nat.bit_mod_two`, each one
`div_mod_unique` call against `Nat.div_mod_exec` (the reconstruction
equation is `bit`'s own definition, closed by `refl`; the bound
`cond test 1 0 < 2` is a two-leaf `Bool` split) — after which the recursive
occurrence swaps back to canonical `land m n` via `land_aux_eq_land_of_le`
again.

Detail moved to [`../notes/251-nat-bit-decode.md`](../notes/251-nat-bit-decode.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-bit-decode | Land the `Nat.bit` decode bridge (`nat_prelude/bit_decode.rs`, new file): artificially-chosen sufficient fuel + `Nat.bit_div_two`/`Nat.bit_mod_two` decode + a `Bool`-first guard-resolution case tree; close `F:ml430-nat-land-bit-b9ab7475` via `Nat.land_bit`. `lor_bit`/`ldiff_bit` remain open — the fuel-swap machinery transports unchanged, but each needs its own per-bit combine agreement lemma (NOT a mechanical transport of `and_cond_mul_eq_cond`; `ble`'s combine needs a further split on `b`) |
