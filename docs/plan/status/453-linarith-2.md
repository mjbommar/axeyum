# Lane: linarith-2 — extend the ℤ fragment (strictness, mul) and retire order-lemma call sites

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, linarith-2, 2026-09-03).** Continuing `omega-1`'s
`crate::linarith`: fixing the `Int.add_le_add_left`/`_right` doc comments,
recovering ℤ `<`-hypothesis strictness and numeral multiplication, then
retiring the highest-value order-lemma call sites in `nat_prelude`/`int_prelude`
against the 4,737-site census ADR-1576 measured. In progress.

<!-- plan-section: landed-changes -->

| 2026-09-03 | linarith-2 | (placeholder, updated at close-out) |
