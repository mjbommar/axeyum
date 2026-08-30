# Lane: nat-ldiff — land `Nat.ldiff` (bitwise AND-NOT), completing the bitwise trio

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-ldiff, 2026-08-28).** Landed `Nat.ldiff`/
`Nat.ldiffAux` in `nat_prelude/ldiff.rs`, following `land.rs`'s/`lor.rs`'s
structural fuel recursion (`Nat.rec` on the fuel argument, `ldiffAux m m n`).

**Worked out the absorbing-zero asymmetry on paper before writing kernel
terms, exactly as the `lor` lane did.** `Nat.ldiff m n` (bitwise "`m` AND NOT
`n`") has an absorbing zero on exactly ONE side: `ldiff 0 n = 0`, but
`ldiff m 0 = m`, not `0`. That determined every shape choice:

Detail moved to [`../notes/226-nat-ldiff.md`](../notes/226-nat-ldiff.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-ldiff | `Nat.ldiff`/`Nat.ldiffAux` (fuel recursion, `land`-shaped fuel-exhaustion base case, hybrid land/lor succ-row guard, `beq`+`bool_select_nat` per-bit step) + 4 boundary theorems incl. the asymmetry pair in `nat_prelude/ldiff.rs`; wired into `nat_prelude.rs`; `nat_prelude_tests.rs` coverage + dedicated evaluation test + pinned render count `492->498`; 4 new `F:nat-ldiff-*` facts |
