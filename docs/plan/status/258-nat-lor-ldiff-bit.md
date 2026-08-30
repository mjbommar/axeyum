# Lane: nat-lor-ldiff-bit — Nat.lor_bit + Nat.ldiff_bit, closing the `Nat.bit` decode bridge trio

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-lor-ldiff-bit, 2026-08-29).** `Nat.lor_bit`
(`F:ml430-nat-lor-bit-a2f98c7c`) and `Nat.ldiff_bit`
(`F:ml430-nat-ldiff-bit-6be49bb8`) are both landed, closing the trio
`docs/plan/status/251-nat-bit-decode.md` opened with `Nat.land_bit` and left
open for a follow-up lane. All three `Nat.bit`-decode facts are now `proved`.

**What transported unchanged from `nat-bit-decode`'s construction**
(`nat_prelude/bit_decode.rs`, new functions appended, `land.rs`/`lor.rs`/
`ldiff.rs`/`rec_agreement.rs`/`bitwise.rs` untouched): the fuel-swap machinery
(`base := mul 2 m`, `k1 := succ base`, `fuel := succ k1`, both `Le` bounds,
the `Nat.bit_div_two`/`Nat.bit_mod_two` decode via `div_mod_unique`) is
byte-for-byte the same shape for all three operators — it never inspects an
operator's absorbing-zero behaviour, only `Nat.bit`'s own encoding.

**What was new per operator (the actual task):**

Detail moved to [`../notes/258-nat-lor-ldiff-bit.md`](../notes/258-nat-lor-ldiff-bit.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-lor-ldiff-bit | `Nat.lor_bit` + `Nat.ldiff_bit` (`nat_prelude/bit_decode.rs`): transport the `Nat.bit` decode bridge's fuel-swap machinery unchanged from `land_bit`; new per-operator guard-tree leaves (`lor`'s pass-through rows, `ldiff`'s hybrid) and per-bit combine agreements (`or_cond_max_eq_cond`, `ldiff_cond_eq_cond`). Closes `F:ml430-nat-lor-bit-a2f98c7c` + `F:ml430-nat-ldiff-bit-6be49bb8`, proved axiom-free. Also fixed a pre-existing misplaced `#[test]` attribute in the same test file (unrelated to this lane's subject, needed for a clean clippy gate). |
