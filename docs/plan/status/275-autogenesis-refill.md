# Lane: autogenesis-refill -- the flywheel's input queue has emptied

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (the empty-queue gate and the divergence screen landed; refill and drift are written proposals)`, autogenesis-refill, 2026-08-29).**

Status: **(1) and (2) landed; (3) and (4) are written proposals, deliberately
not executed — see "What this lane did NOT do".**

Everything below was re-measured in this worktree after `git merge main`, not
read from the design-review note. Where the note and the measurement differ, the
measurement is stated and the difference is named.

---

## Step 0 — re-measurement (2026-08-29)

The numbers in
[`docs/research/11-design-review/2026-08-29-the-mirror-population-is-consumed.md`](../../research/11-design-review/2026-08-29-the-mirror-population-is-consumed.md)
reproduce exactly.

| | measured |
| --- | --- |
| facts total | 1,949 |
| `ml430` population | 214 |
| `ml430` proved | 155 (72.4%) |
| `ml430` open | 59 |
| open, all facts | 64 — so the **non-mirror open set is 5** |
| nursery entries | 216 (train 78 / development 99 / held-out 37 / longitudinal 2) |

Two things the note does not say, both of which sharpen it.

**The dispatchable set is 1, not ~12.** The note's "~12 dispatchable, of which
11 are structurally blocked" is right, and the residue is a single row:
`F:ml430-nat-lt-xor-cases-c43a1e85`, which is in flight. Eleven blocked rows,
four constructions:

```
Nat.testBit      codomain             5 rows
Nat.multichoose  definitional         3 rows
Nat.minFac       algorithmic          1 row
Nat.fastFib      recursion-principle  1 row  (+ Nat.testBit accounts for
                                              testbit_eq_inth, the 11th)
```

**The 37 open held-out rows are exactly two families.** Not spread across the
population — `natural-logarithm` (21) and `natural-square-root` (16). Every
other held-out family is fully closed. Confirmed against
`mathlib-nursery-split-policy-v1.json`, whose `family_partitions` assigns
exactly those two to `held-out` out of twelve families. So the blind evaluation
population is not merely off-limits; **what remains of it tests exactly two
capabilities**, and a refill that does not add held-out breadth leaves the
evaluation narrow even if it never spends a row.

---

## (1) The selection mechanism — what would have reported an empty queue

Answer: **nothing would have, and one thing that comes close has been red on
`main` with nobody running it.**

### `scripts/fact-frontier.py` — prints the bands, cannot report emptiness

It is the tool that turns the ledger into a queue, and it is better than the
note implies: it already annotates every held-out row with a ⛔ marker naming
ADR-0542's cost, marks every mutation control, and prints

Detail moved to [`../notes/275-autogenesis-refill.md`](../notes/275-autogenesis-refill.md).

