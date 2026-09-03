# Lane: omega-1 — a linear-arithmetic decision procedure that EMITS kernel terms

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, omega-1, 2026-09-03).** Building `linarith`: a
Presburger-fragment (quantifier-free linear order/arithmetic over ℕ and ℤ)
decision procedure inside `axeyum-lean-kernel` that produces kernel proof terms
from a Farkas certificate. It is a *producer* in ADR-0601's sense — untrusted
search, trusted checking: every emitted term goes through `Kernel::infer` /
`add_declaration`, and the procedure's own tests assert that a CORRUPTED
certificate is rejected by the kernel, not by the procedure.

The metric is hand-written proof lines retired. Coordinator's 2026-09-03 count:
4,737 order-lemma call sites (`nat_prelude` 1,546, `int_prelude` 378,
`rat_prelude` 601, `creal` 2,212) and no `omega`/`linarith`/Farkas-shaped
procedure anywhere in tree.

Status: stub committed; step 0 (existing-lemma inventory) next.

<!-- plan-section: landed-changes -->

| 2026-09-03 | omega-1 | lane status stub for the linear-arithmetic term producer |
