# Lane: audit-refresh — the published proof-gap metric was reporting stale audits

<!-- plan-section: lane-status -->

**All 35 dominance audits re-run at `496288979`; the fully-dominant UNSAT count
is 269 / 326, not 262 / 324, and five of the fifteen "Lean-reconstruction gap"
rows were stale records rather than gaps** (`DONE`, agent-audit-refresh,
2026-08-21).

Every committed audit was stamped between `2e207eba5` and `562b65f13` — all of
them before today's reconstruction work landed — so the artifact said "gap"
about instances the code had already closed. Four rows moved and 31 are
identical in every summary field, which is what makes the two runs comparable.

**+5 of the +7 dominant outcomes are capability; +2 are the instrument.**

- Capability, QF_NRA `qf-nra-cvc5-regress-clean` 21/32 → 24/32:
  `coeff-unsat-base` and `simple-mono` reconstruct as `RealProduct`
  (`71f1c29a0`), `ones` as `MonomialBound` (`77c70d3e0`).
- Capability, QF_S `qf-s-cvc5-regress-clean` 9/93 → 11/93: `r0_QF_SLIA_str004`
  and `r0_QF_S_str005` gained a kernel-checked `StringLength` module
  (`b495a396e`).
- Instrument, QF_NRA `qf-nra-synthetic-graduated` 31 → 33 audited: the two
  `d01` instances were being billed for a process-wide ~32 s `CReal` prelude
  build inside a 10 s per-instance cap. `562b65f13` moved that build outside the
  timer. A/B, corpus and cap fixed: `1fff66825` 31, `cfc5f8078` 31,
  `71f1c29a0` 33, `71f1c29a0` with the warm suppressed **31**, HEAD 33, HEAD
  with the warm suppressed **33** — the last row because `0887ab652` made the
  prelude cheap enough to pay for inside the cap. This is the whole baseline
  denominator movement, 324 → 326.

Detail moved to [`../notes/114-audit-refresh.md`](../notes/114-audit-refresh.md).

<!-- plan-section: landed-changes -->

| 2026-08-21 | (pending) | All 35 dominance audits re-run at `496288979` from a `lane-snapshot` tree; `dominant_unsat` 262 / 324 → **269 / 326**, `lean-reconstruction-gap` 15 → **10**, certified/checked 278 → 280. Four rows moved: QF_NRA cvc5 (+3, `RealProduct`×2 + `MonomialBound`), QF_S (+2, `StringLength`), QF_NRA synthetic (+2, the prelude-warm instrument fix, proved by an A/B with the warm suppressed at two revisions), QF_SEQ (a `parse-error` became `sat`, no dominance change). `gen-proof-gap-matrix`, `gen-proof-gap-shape-census`, `gen-dominance-scoreboard` and `gen-autogenesis-baseline` regenerated; the six moved markers in `PROJECT-STATE.md` and the gap analysis renumbered **with** the account of what moved them, and the ten remaining Lean-reconstruction gaps recorded one line each with the fragment's own decline reason rather than the fallback route's. |
