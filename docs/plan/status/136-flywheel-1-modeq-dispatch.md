# Lane: flywheel-1 — first producer-contract-driven dispatch, executed

<!-- plan-section: lane-status -->

**Executed the first machine-selected, contract-matched dispatch** (`DONE`,
flywheel-1, 2026-08-27): `scripts/fact-frontier.py --json` selected
`F:ml430-int-add-modeq-left-ee732b5b` via `producer-contract-int-modeq-family-v1`
(route `kernel-lane`, landed same-day by the `producer-contracts` lane,
[`135-producer-contracts.md`](135-producer-contracts.md)). Checked the
nursery partition first (`train`, not held-out) per ADR-0542, then ran the
contract's own recipe for real: authored an s5-side Lean statement adapter
(`AxeyumAutogenesisIntAddModEqLeftV1.lean`, a new file, not an edit to the
shared family adapter), verified the pinned Mathlib
(`c5ea00351c28e24afc9f0f84379aa41082b1188f`) and lean4export
(`a3e35a584f59b390667db7269cd37fca8575e4bf`) commits, exported via
`lake env lean` + `lean4export` (clean, 6,138 records, zero-byte stderr),
imported cleanly (208 declarations, 0 axioms — independently reconfirms the
`Nat.div_rec_lemma` cascade from docs 241/242 is still bridged), and ran the
shape-generic checker (`modeq_family_operation`).

**Result: honest decline, not a proof.** `propose_modeq_family` returned
`DeclineReason::TerminalNotClosed` — the goal is an *unconditional* additive
identity (`n + a ≡ a [ZMOD n]`, no hypothesis to symm/trans over), unlike the
four family members this exact producer already proves
(refl/symm/trans/comm, all of which manipulate an already-given equality).
Mathlib's own proof is `:= by simp`, not `rfl`, independently confirming this
was never a definitional identity. Cross-checked against this kernel's own
`Int.ModEq.add_left`/`add_right` (`int_prelude/modeq.rs`): both require
`0 < n` via `modEq_iff_dvd`, while the Mathlib target is unconditional — the
same `0 < n` gap two sibling facts (`F-ml430-int-modeq-one-01d9de39.json`,
`F-ml430-int-modeq-neg-d6ff57b6.json`) already record in their own `notes`.
Fixing it needs a natAbs-based generalization of `Int.emod_lt_of_pos`
(`int_prelude/division.rs`) — real kernel-level work, out of this lane's
scope (`crates/axeyum-lean-kernel/src/` off-limits per brief).

Detail moved to [`../notes/136-flywheel-1-modeq-dispatch.md`](../notes/136-flywheel-1-modeq-dispatch.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | `PENDING` | First real execution of a producer-contract dispatch (`F:ml430-int-add-modeq-left-ee732b5b`): clean s5 export/import, honest producer decline (`TerminalNotClosed`), recorded as a decline artifact + fact note rather than a fabricated admission. No fact status changed, no operation registered. |
