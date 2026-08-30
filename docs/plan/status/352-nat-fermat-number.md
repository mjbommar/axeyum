# Lane: nat-fermat-number — declare `Nat.fermatNumber`, definition only

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (Nat.fermatNumber declared, definition and
evaluation test only; Mathlib.NumberTheory.Fermat now screens READY at
13/13, ready-family count 17 -> 18)`, nat-fermat-number, 2026-08-30).**

Dispatched per
[ADR-0653](../../research/09-decisions/adr-0653-declaring-the-unblocking-constant-contaminated-the-family-it-opened.md):
draw 7 needs one more constant to reach the two new held-out-safe families
`check-dispatchable-frontier.py` requires, and `Nat.fermatNumber` was the
cheapest of the three measured there. The task was narrowly scoped on
purpose — ADR-0653 exists because a sibling lane's `Nat.dist` unblock
proved seven supporting theorems and spent the very family it opened.

## What landed

`crates/axeyum-lean-kernel/src/nat_prelude/fermat_number.rs` (new file):
`Nat.fermatNumber n := add (pow 2 (pow 2 n)) 1`, wired in as the LAST
`declare_*` call in `build_nat_prelude` (needs only `Nat.pow`/`Nat.add`,
both declared far above). Struct field `fermat_number: NameId` and its
constructor line added to `NatPrelude`; `p.fermat_number` added to
`nat_prelude_tests.rs`'s `definition_names` list so the environment-coverage
test (`every_nat_declaration_is_checked_and_axiom_free`) sees it.

**No theorem about it was declared** — per ADR-0653's rule, this is the
entire point of the task.

### Mathlib's actual definition, read at the pinned toolchain

`scripts/provision-lean-import-toolchain.sh --verify` (needs no network,
~instant since already provisioned):

```
LEAN_IMPORT_TOOLCHAIN|mathlib=c5ea00351c28e24afc9f0f84379aa41082b1188f|...|verdict=PASS
```

`/data0/axeyum/lean-import-toolchain/mathlib4/Mathlib/NumberTheory/Fermat.lean:34`:

```
def fermatNumber (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 1
```

Single explicit `Nat` argument, base `2` fixed, nested exponent. Confirmed
against the file directly rather than inferred from ADR-0653's paraphrase.

### Hand-computed evaluation values, and their cost

`fermatNumber 0 = 2^(2^0)+1 = 2^1+1 = 3`
`fermatNumber 1 = 2^(2^1)+1 = 2^2+1 = 5`
`fermatNumber 2 = 2^(2^2)+1 = 2^4+1 = 17`

Detail moved to [`../notes/352-nat-fermat-number.md`](../notes/352-nat-fermat-number.md).

