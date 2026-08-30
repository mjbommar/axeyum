# Lane: nursery-refill-exec -- the positive "statable here" screen, and the refill

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (the statable-here screen landed; 80 rows
preregistered; the empty-queue gate is green at 50 dispatchable)`,
nursery-refill-exec, 2026-08-29).**

---

## Step 0 -- re-measurement

`scripts/check-dispatchable-frontier.py` was **red on `main`**, as briefed, and
the number is one lower than the previous lane recorded (a mirror closed in
between):

```
FAIL: G4 empty-dispatchable-set
open ml430 mirrors: 58
  held-out (blind evaluation, do not dispatch): 35
  mutation negative controls (never closable):  12
  structurally blocked by a divergence:         11
  DISPATCHABLE:                                 0
```

### One correction to the previous lane's record

[`275-autogenesis-refill.md`](275-autogenesis-refill.md) names the pinned
statement source as `mathlib-v4.30.0-nat-int-statement-inventory-v1.ndjson`.
**The pinned artifact is `-v2`**, and the two are different files:

| file | sha256 | pinned by |
| --- | --- | --- |
| `…-inventory-v1.ndjson` | `b3569d54…` | nothing in the tree |
| `…-inventory-v2.ndjson` | `4285e551…` | ADR-0479, `mathlib-statement-source-v1.json`, and 15 scripts |

Both carry 9,729 records, which is why the substitution is invisible from a
record count. This lane reads **v2** and pins its sha256 in the generator.

---

## (1) The positive "statable here" screen

### The idea

The divergence registry is a **negative** screen: it names constructions whose
axeyum counterpart diverges. It says nothing about whether a proposition can be
*expressed* here at all, which is why hundreds of `Std.PRange`, `Finset` and
`LinearOrder` rows pass it.

The positive screen answers the complementary question **from
`kernel.environment()`**, never from a theorem inventory (which lists no
`Definition`s -- `Nat.add` returns zero rows from `prelude_theorem_inventory`
and certainly exists).

A pinned statement's `type_repr` is a structural `Lean.Expr` dump, so its Lean
constants are extractable mechanically (`Lean.Expr.const `Nat.fib []` ->
`Nat.fib`). A candidate is **statable here** iff every constant is admissible:

```
  env      2,207 declaration names read from kernel.environment()
           (examples/shape_search --include-constructed, all six populated
           kinds; snapshot in artifacts/autogenesis/kernel-environment-snapshot-v1.json)
+ bridge      70 Lean surface constants NOT in the environment but appearing in
           the pinned statement of a mirror we have ALREADY CLOSED
```

Detail moved to [`../notes/278-nursery-refill-exec.md`](../notes/278-nursery-refill-exec.md).

