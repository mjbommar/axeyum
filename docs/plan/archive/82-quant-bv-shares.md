# Lane: quant-bv-shares — the 1 of 70 proof families a real Lean rejected

<!-- plan-section: lane-status -->

**70 of 70 proof families now check in a real Lean; the gate's exclusion is gone
(`WIP`, quant-bv-shares, 2026-08-14).** `lean_crosscheck`'s
`quant_bv_source_instance_set` rejection was a **printer defect, not a
reconstruction defect** — the in-tree kernel's term was well typed throughout,
and the whole fix is in the Lean *writer*. The compact proof-sharing pass hoisted
a *proper prefix* of a recursor spine into its own definition
(`def axeyum_proof_share_149 := @Or.rec P`); Lean makes an inductive's parameters
and a recursor's motive implicit, so that definition inherits them as **leading
implicit binders** and the bare reference `axeyum_proof_share_149 Q` silently
re-inserted metavariables for both, putting `Q` in the `inl` minor-premise slot.
The unknown-identifier errors were the cascade — a `def` that fails to elaborate
never enters the environment. `lean_pp::hoisting_exposes_implicit_binders` now
refuses to hoist an under-applied application whose spine head is a constant Lean
regenerates; module size is unaffected (+2.2% bytes, −32% lines) because
saturated spines and their arguments stay shareable. Measured after: 70/70
representative modules and **163/163** exhaustive modules accepted by Lean
4.30.0, `#print axioms` clean. `scripts/check-lean-gate.sh` with no environment
variables set: **12 suites, 49 tests, 112 real-Lean checks** (was 40), floor
raised 35 → 105. No fact and no ADR are owed: nothing the kernel accepted was
ill-typed.

Next, in priority order: (1) nothing still enforces that a NEW suite shelling out
to `lean` reaches the gate's manifest — the hole `lean-gate-honesty` named, one
level up, and the only reason this defect needed a human to notice it; (2) the
`maxRecDepth 100000` these modules carry inline is a silent dependency on Lean's
elaborator bound — a Lean whose default changed would move the pass/fail line
without any of our gates saying so; (3) the same implicit-binder rule should be
audited for `write_decl_command_with_at`'s *local* `let` shares, which are
covered by the fix but have no dedicated fixture.

Found and repaired on the way, both `a5975725f`'s debt and both confirmed against
a `git archive HEAD` snapshot before being touched:
`lean_pp::tests::renders_self_contained_module` still asserted `axiom False :
Prop` (the only failing test in `axeyum-lean-kernel` on HEAD), and all 15
`crates/axeyum-solver/tests/fixtures/lean-modules/*.lean` byte-stability fixtures
were stale (7 failing `reconstruct::tests::*_is_byte_stable` on pristine HEAD).
Re-blessed and re-checked through real Lean; the fixture diff contains zero
`proof_share` lines, i.e. none of it came from this lane's change. Four
`(length, fnv1a)` pins over generated modules (`quant_affine_growth_lean`,
`quant_counterexample_cover`, `quant_eq_partition_lean`, `quant_residue_lean`)
were stale for the same reason — three of the four render byte-identically with
and without this lane's change, the fourth 513 bytes smaller. Re-pinned only
after each module was put through Lean 4.30.0 and accepted with a clean
`#print axioms`, because two integers cannot tell "the printer improved" from
"the printer broke".

<!-- plan-section: landed-changes -->

| 2026-08-14 | `b4604bae7` | The compact Lean writer keeps regenerated-constant spines saturated; `quant_bv_source_instance_set` checks in real Lean and `lean_crosscheck` joins the gate (40 → 112 real-Lean checks). |
