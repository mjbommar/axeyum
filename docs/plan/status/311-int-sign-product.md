# Lane: int-sign-product — five `Int` sign-of-a-product mirrors

<!-- plan-section: lane-status -->

**DONE (`int-sign-product`, 2026-08-30).** Closed all five assigned facts:
`Int.mul_pos_iff`, `Int.mul_neg_iff`, `Int.mul_nonneg_iff`, `Int.mul_nonpos_iff`,
`Int.mul_nonneg_of_nonneg_or_nonpos`. New file
`crates/axeyum-lean-kernel/src/int_prelude/sign_product.rs`: one shared sign
case-split (`Int.le_total zero a` / `Int.le_total zero b`) plus six quadrant
facts (two already existed as `Int.mul_nonneg`/`Int.mul_pos`; the other four
built from a sign-flip helper, `neg_mul_neg` reusing `gcd.rs`'s
`neg_mul`/`neg_neg`, and `mul_le_mul_of_nonneg_left` at `c := 0`). All five
are `Theorem`s with empty `axiom_footprint`; `integer` prelude trusted surface
stays 0. `int_prelude::` sweep: 49 passed, 0 failed (was 44 before this lane's
5 additions). `derived_laws` pin recounted 187 -> 192 via
`scripts/recount-pinned-inventory.py`. `clippy -D warnings` clean,
`rustfmt --edition 2024` applied. Facts flipped `open` -> `proved`,
`depends_on` populated by `check-fact-depends-derived.py --fix` (66 edges),
`validate-facts.py` 0 errors, `check-mirror-statement-fidelity.py` PASS. Did
not run the full workspace gate (`just check`/`./scripts/check.sh`) —
scoped to the `int_prelude::` sweep, clippy, fmt and the fact-ledger
validators per the task brief.

Nothing blocked. No follow-up known for this specific family.

<!-- plan-section: landed-changes -->

| 2026-08-30 | int-sign-product | New `int_prelude/sign_product.rs`: `Int.mul_pos_iff`, `Int.mul_neg_iff`, `Int.mul_nonneg_iff`, `Int.mul_nonpos_iff`, `Int.mul_nonneg_of_nonneg_or_nonpos`, all built from one sign case-split; 5 facts flipped open->proved |
