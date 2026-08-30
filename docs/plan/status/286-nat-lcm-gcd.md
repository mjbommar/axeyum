# Lane: nat-lcm-gcd — the `ml430` `Nat` lcm/gcd family

<!-- plan-section: lane-status -->

**Lane block (`DONE for this dispatch`, nat-lcm-gcd, 2026-08-29).**

**The task.** Ten dispatchable `ml430` mirrors:

```
F:ml430-nat-lcm-comm-d5f8aae0        F:ml430-nat-lcm-assoc-cb00bb43
F:ml430-nat-lcm-div-eb5d8892         F:ml430-nat-lcm-dvd-07899eea
F:ml430-nat-dvd-lcm-left-c83bcebc    F:ml430-nat-dvd-lcm-right-18ab8e2f
F:ml430-nat-eq-zero-of-lcm-eq-zero-d09b7af7
F:ml430-nat-gcd-dvd-mul-81cb13df     F:ml430-nat-gcd-le-mul-7e3800f7
F:ml430-nat-gcd-mul-lcm-b7217ace
```

**Closed, 10 of 10.**

**Step 0 found five already proved under the identical statement**, before
any new proof work: `nat_prelude/lcm.rs` already declared `Nat.lcm_comm`,
`Nat.lcm_dvd`, `Nat.dvd_lcm_left`, `Nat.dvd_lcm_right`, and
`Nat.gcd_mul_lcm`, each matching its fact's `formal.statement` verbatim
(confirmed via `nat_theorem_inventory`'s rendered type, not by reading the
Rust source). Pure status flip plus evidence for these five, no proof work.

**Five new theorems**, all in a new file
`crates/axeyum-lean-kernel/src/nat_prelude/lcm_gcd_lemmas.rs`:

Detail moved to [`../notes/286-nat-lcm-gcd.md`](../notes/286-nat-lcm-gcd.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-lcm-gcd | `Nat.gcd_dvd_mul`, `Nat.gcd_le_mul`, `Nat.eq_zero_of_lcm_eq_zero`, `Nat.lcm_assoc`, `Nat.lcm_div` — 5 new axiom-free theorems (`nat_prelude/lcm_gcd_lemmas.rs`), plus 5 status-flip closures of pre-existing `Nat.lcm_comm`/`Nat.lcm_dvd`/`Nat.dvd_lcm_left`/`Nat.dvd_lcm_right`/`Nat.gcd_mul_lcm`. 10 of 10 dispatched `ml430` lcm/gcd mirrors closed. |
