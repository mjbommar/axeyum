# Lane: structures-ordered-setoid — AlgS.Group-level theorems and AlgS.OrderedRing, so linarith::generic reaches ℝ

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, structures-ordered-setoid, 2026-09-03).**
Starting point: ADR-1590 named two open gaps — no `AlgS.Group`-level
generic theorem (so `Alg.neg_neg` could not derive from `AlgS`), and no
`AlgS.OrderedRing` at all (so `linarith::generic`, ADR-1585, could not
reach `CReal`). This lane closed both — see ADR-1592.

**Gap 1**: `AlgS.inv_unique`/`AlgS.invInv` (the `AlgS.Group`-level pair,
setoid twins of `Alg.groupInvUnique`/`Alg.neg_neg`), proved once,
instantiated at `Int` (via `ofAlg`) and at `CReal` via a NAMED
`CReal.addGroupS` projection (`AlgS.CommGroup.toGroupS(AlgS.CommRing.
toCommGroupS(CReal.commRingS))`, both projections new and named, not the
earlier test-only `ring_s_additive_group_value` builder). `Alg.neg_neg`'s
own proof is now DERIVED from `AlgS.invInv` via `AlgS.Group.ofAlg`,
declared type measured byte-identical (existing `neg_neg_applies_
concretely_at_int_and_symbolically_at_rat`/`retirement_rat_neg_neg` tests,
unmodified, both still pass).

**Gap 2**: `AlgS.OrderedRing` — 29 fields (`AlgS.Ring`'s 22, NOT `AlgS.
CommRing`'s 23: `Alg.OrderedRing` itself has no `mulComm`, so a
`CommRing`-based record would make `AlgS.OrderedRing.ofAlg` ill-typed,
measured by attempting it first) plus `le`, `leCongr` (new field, no
`Eq`-flavored counterpart — `Eq`'s congruence is free), `le_refl`,
`le_trans`, `le_antisymm_equiv` (concludes `equiv`, not `Eq`),
`add_le_add_left`, `mul_nonneg`. `AlgS.OrderedRing.ofAlg` synthesizes
`leCongr` via two `subst` transports; every other field the source
`Alg.OrderedRing` selector unchanged. `rat_prelude/ordered_ring_ext_s.rs`
(new): `AlgS.OrderedRing.ofNat`/its two laws, and the three derived order
lemmas — each shorter than the `Eq`-flavored version because `leCongr`/
`addCongr` are first-class fields. `AlgS.Int.orderedRingS`/`AlgS.Rat.
orderedRingS` via `ofAlg`; retirement-style `def_eq` checks against
`Int.add_le_add_right`/`Int.add_le_add` pass. **`CReal.orderedRingS`
landed** — every field an existing `CReal` theorem, no law missing
(`le_congr`/`equiv_of_le_le`/`mul_nonneg` already had exactly the right
shape; `add_le_add_left` derived from `add_le_add`+`le_refl`), wired into
the generated `creal` build (`scripts/creal-declare-deps.py`: 214 steps,
`--check --strict --self-check` exit 0).

**`linarith::generic` reaches ℝ**: extended (not forked) with a `Backend`
enum threaded through the five wrapper methods (`refl`/`symm`/`trans`/
`congr`/`substp`) and one parser (`as_eq`) every normalizer call site
already funnelled through — zero behavior change to the `Eq`-flavored
path (all 72 pre-existing `linarith` tests pass unmodified).
`Problem::new_s`/`prove_s`/`emit_le_from_certificate_s` are the setoid
entry points. Test battery, all release-mode kernel-checked: 3 ℚ goals
re-proved through `Rat.orderedRingS`; **5 goals at `CReal.orderedRingS`**
— transitivity, sum-of-nonneg, slack+1, a 3-hypothesis `add_le_add_three`
combination, and `Equiv a b` proved by antisymmetry (the `Shape::Eq`
route, a fact no `Eq`-flavored route could ever reach); 3 false `CReal`
goals decline; 2 corrupted `CReal` certificates rejected by the kernel.

**5 `creal/` retirements**: `creal/integral.rs::{le_add_nonneg_right,
rle_add_right}`, `creal/sqrt.rs::rat_le_add_nonneg`, `creal/
supremum.rs::rat_le_add_right` (all the SAME `x≤x+y` shape, hand-built
independently four times, TWO in the same file), and `creal/
completeness.rs::moduli_shift_le` (two-sided `add_le_add`) — all routed
through `linarith::generic::prove_s` over `AlgS.Rat.orderedRingS` via a
new shared bridge, `creal/linarith_bridge.rs`. Function signatures/return
types unchanged; full `creal::` suite green before and after.

**A real bug the retirement surfaced**: `Problem::ofnat_numeral`
recognises a literal zero by SYNTACTIC `ExprId` equality against its own
selector-built `self.zero`, not `def_eq` — the bridge's first version
built its hypothesis's zero from the bare `Rat.zero` constant instead
(`def_eq`, but a different `ExprId`), so every `rat_le_add_right` call
inside a REAL prelude build panicked with `Decline::NoCertificate`, caught
only by `cargo run --example theorem_dependency_inventory` (the full
prelude), not the isolated unit tests. Fixed; see ADR-1592's Evidence.

Running retirement total: ADR-1589's 62 + this lane's 5 = **67** (plus
whatever `tactic-list-int` landed separately, not re-counted here — see
that lane's own status file for its own total).

SHAs: `186eb83f1` (status stub), `638a15909` (deliverable 2: `AlgS.Group`
theorems + `Alg.neg_neg` derivation), `3dba85b46` (deliverable 3+4:
`AlgS.OrderedRing` + `linarith::generic` setoid backend), plus this
close-out commit (`CReal.addGroupS`, the 5 retirements, facts, this
status file, `PLAN.md`, the ADR index).

**Did not run / not attempted**: `just check`/`./scripts/check.sh` (the
full aggregate gate — out of scope for a single-lane close-out per
`multi-agent-operations.md`; ran the specific pre-merge gates this lane's
changes touch instead, listed above). No further `creal/*.rs` retirement
beyond the 5 named (2,212 order-lemma call sites total per ADR-1576's
original count; this is a first slice). The `<`/strict fragment over
`AlgS.OrderedRing` (still no `lt` field on either `Alg.OrderedRing` or
`AlgS.OrderedRing` — the same gap ADR-1585 left open). `Complex.
orderedRingS` (Complex has no order at all today).

<!-- plan-section: landed-changes -->

| 2026-09-03 | structures-ordered-setoid | status stub opened |
| 2026-09-03 | structures-ordered-setoid | `AlgS.inv_unique`/`AlgS.invInv` over `AlgS.Group`, `Alg.neg_neg` derived via `AlgS.Group.ofAlg`, two new named projections (`AlgS.CommRing.toCommGroupS`, `AlgS.CommGroup.toGroupS`) |
| 2026-09-03 | structures-ordered-setoid | `AlgS.OrderedRing` (29 fields, Ring-based), `ofAlg` with `leCongr` synthesis, `rat_prelude/ordered_ring_ext_s.rs`, `CReal.orderedRingS` wired into the creal build, `linarith::generic` extended with a `Backend` enum reaching `CReal` — full test battery green |
| 2026-09-03 | structures-ordered-setoid | `CReal.addGroupS` (named), 5 `creal/*.rs` order-chain retirements via `creal/linarith_bridge.rs`, 4 new facts, ADR-1592, close-out |
