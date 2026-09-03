# Lane: contracts-test-heldout-drift — fix the stale held-out-overlap literal in the producer-contracts test

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, contracts-test-heldout-drift, 2026-09-03).** Started:
`scripts/tests/test_validate_producer_contracts.py` is red on main because
`nat-coprime-family-v1`'s held-out overlap grew by one row
(`omega-1`/`ebddccf27`, ADR-1561, draw 19) and `KNOWN_HELD_OUT_SHAPE_MATCHES`
is a literal that did not move. In progress: replacing the literal with a
derivation from the live manifests plus a reviewed-overlap field in each
contract's sizing block, per the evidence-and-checker-discipline rule that a
test named "every X" must derive X from the authority.

<!-- plan-section: landed-changes -->

| 2026-09-03 | contracts-test-heldout-drift | early stub: reproducing the red test before fixing |
