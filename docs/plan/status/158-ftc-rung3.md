# Lane: ftc-rung3 — the Fundamental Theorem, rung 3

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, ftc-rung3, 2026-08-27).** In progress. Absence of
all three lemmas named by `157-ftc.md` re-verified against `creal.rs`'s name
registry (the authoritative interning site: every `CReal.*` name is
`kernel.name_str(creal, …)` there and nowhere else — confirmed by grep across
`crates/axeyum-lean-kernel/src/`). The lattice surface is exactly
`le_max_left`, `le_max_right`, `max_le`, `min_le_left`, `min_le_right`,
`le_min`, `max_congr`, `min_congr` — **no monotonicity lemma and no
`max_sub_min`**.

<!-- plan-section: landed-changes -->

| 2026-08-27 | ftc-rung3 | WIP |
