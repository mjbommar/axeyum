# Lane: agent-axreal — the axiomatized reals are renamed before they are retired

<!-- plan-section: lane-status -->

**`Real` -> `AxReal` (ADR-0522 step 1), and it turned a passing assertion red on
the first run (`WIP`, agent-axreal, 2026-08-19).** The trusted surface is
unchanged and re-measured, not assumed: `complex 0 · creal 0 · integer 0 ·
logic 0 · nat 0 · rat 0 · string 0 · real 30`, with the 30 rows now spelled
`AxReal`/`AxReal.*`.

**What the rename caught.** `the_theory_front_door_accepts_the_farkas_route`
asserted `source.contains("Real.add_le_add")` on a module the shipped route
emits over the **constructed** carrier, and passed — `CReal.add_le_add` contains
`Real.add_le_add`. The test could not tell the two carriers apart and would have
kept passing if the route were switched back. `CReal` does not contain `AxReal`,
so the rename failed it immediately; it is now two-sided (`CReal.add_le_add`
present, `axiom AxReal : Sort` absent), like its sibling. A second one was in
`examples/infeasibility_farkas_lean.rs`, whose "carries ordered-field content"
scan matched `ty.contains("Real.le")` — satisfied by `CReal.le` — and which is
the checker command of the `proved` fact `F:schedule-critical-chain-infeasible`;
that fact's notes had transcribed the collision as fact. Both now name the
carrier in full, and the fact's `26 = 17 prelude + 4 variable + 5 hypothesis` is
re-derived. Third and fourth instances of one collision; only the first was ever
noticed, and it was worked around rather than fixed.

**A rename is not a retirement, and the ledger now has the verb for it.**
`--accept-population-change` would have dropped 30 rows to `unclassified` and
filed them as **retired**, publishing a 30-row reduction in the trusted surface
that never happened (the generated headline would read 65 retirements for 35
real ones). `gen-lean-axiom-ledger.py --accept-rename OLD=NEW` re-keys live rows,
carries their authored classification across, and takes the canonical type and
digest from the measurement, so a mis-stated rename fails rather than lands:
`rows=30 | Real->AxReal`, then `total=30 … retired=35 … unclassified=0`.

**Measured.** `-p axeyum-solver --lib --features full` 1223 passed;
`gen-lean-axiom-ledger.py --check` green; its suite 39 -> 43 tests; 13 ledger
mutation controls, no survivors, the three new guards `killed 1` each — the
prefix guard SURVIVED first and was rewritten before it counted. Two golden Lean
fixtures re-blessed, rename-only diffs.

**Next.** ADR-0522 step 2, the retirement: three relative-consistency models as
telescope instantiations, two facts restated, a home for
`arith_prelude_builds()`, and the one-shot ledger population swap (`real 30` out
and the constructed control in must be a single change, or the published surface
briefly *grows* to 31). Historical documents keep the old spelling on purpose.
[Notes](../notes/71-axreal.md).

<!-- plan-section: landed-changes -->

| 2026-08-19 | `c26e492b1` | **The axiomatized reals are renamed `AxReal` (ADR-0522 step 1), and two green assertions were reading the wrong carrier.** `CReal` contains `Real`: a front-door test asserting `contains("Real.add_le_add")` was satisfied by `CReal.add_le_add`, and `infeasibility_farkas_lean`'s ordered-field-content scan by `CReal.le` — the latter is the checker command of a `proved` fact. Both fixed two-sided and re-derived. One string literal moves the whole 30-row package (stored name, not a render-time remap like `AxNat`). `gen-lean-axiom-ledger.py --accept-rename OLD=NEW` is new, because routing a rename through `--accept-population-change` would have published 30 retirements that never happened and dropped 30 classifications; 3 guards, each mutation-checked to kill exactly one test. Trusted surface unchanged and re-measured; kernel 393, solver 1223, controls non-vacuous. |
