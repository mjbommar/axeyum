# Lane: retire-generic-1 — the retirement ADR-1584 measured and did not take

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, retire-generic-1, 2026-09-03).** ADR-1584 found
six carrier-specific hand proofs matching a generic `Alg.*` theorem by type
(`Int.add_left_cancel`, `Rat.neg_neg`, `Rat.sub_self`,
`Int.mul_le_mul_of_nonneg_left`, `Rat.mul_le_mul_of_nonneg_left`,
`Rat.pow_add`) but deleted none, because the build-position check ADR-1581
requires was never done. This lane does that check for real, and lands the
first retirement it clears end to end. In progress; this stub records the
first landed piece.

<!-- plan-section: landed-changes -->

| 2026-09-03 | retire-generic-1 | status stub |
