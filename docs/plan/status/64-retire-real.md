# Lane: agent-retire-real — retiring the last 30 axioms, and what actually stops it

<!-- plan-section: lane-status -->

**No shipped route BUILDS the `Real` axiom package, and a counter says so
(`WIP`, agent-retire-real, 2026-08-18).** The ledger's 30 does not move;
ADR-0509 says why rather than working around it. What that number stood for is
now measured and gated.

**The hole found.** `a6ee37c6a` moved the front door to `CReal` and the claim
went out as axiom-free. `ProofFragment::IntFarkas` — also shipped — still built
`LraReconstructCtx::new()`, refuted over the 30, abstracted them back out and
instantiated at ℤ. Its module named no `Real` axiom and its footprint was empty,
so every footprint-shaped check passed while the route built the whole trusted
surface **twice** per query (the scan trial-builds to classify).
`front_door_carrier --require-axiom-free`, the gate for exactly this claim, has
three fixtures, all real-typed: it never reached that arm.

**Fixed by an instance already there.** `IntPrelude` carries all 30 signature
fields with every law proved, so `RingSignature: From<IntPrelude>` is the
interface at ℤ with the kernel's own `Eq` — the corner `Real` (30 axioms) and
`CReal` (defined equality) cannot occupy. All 30 integer declarations are
footprint-empty against 30 non-empty for `Real` in the same test; the four
integer tests take **1.0 s** to the `CReal` tests' **98 s**. IntFarkas refutes
directly there; Lean still accepts the module (172,934 bytes).

**Measured, not argued.** `arith_prelude_builds()` counts calls to
`build_arith_prelude`. Through `prove_unsat_to_lean_module`: **0** on `Lra`,
`Sos`, `DisjunctiveLra`, `IntFarkas`; **1** for the control in the same process.
`F:shipped-front-door-reaches-no-real-axiom`, 7 rows, each proven to fail on
mutated output first.

**Why 30 stays.** They are the digest-pinned kernel statement of the interface
three constructed carriers are checked against, and the NEGATIVE CONTROL for
every axiom-freedom measurement here — delete them and no such claim can fail.
ADR-0509 names the bounded route to declared = 0: move the specification onto
the axiom-free 30-binder telescope the abstraction already produces, then shrink
the control from 30 axioms to one.
[Notes](../notes/64-retire-real.md).

<!-- plan-section: landed-changes -->

| 2026-08-18 | 61c466b53 | **The shipped front door reaches no `Real` axiom, measured at `build_arith_prelude` itself.** `RingSignature: From<IntPrelude>` + `try_new_over_integers`; `reconstruct_int_farkas_to_lean_module` off the `Real` package. `arith_prelude_builds()` = 0 across all four arithmetic arms, 1 for the control. Mutation-checked twice, exactly one test dead each — and all 9 tests of the suite named for that route pass under both mutations. Fact + ADR-0509 (declared vs reached). Also unbroke `clippy` on STABLE, red on `main` since `94d51fbc6`. |
