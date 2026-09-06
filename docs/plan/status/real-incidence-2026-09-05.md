# Lane `real-incidence` — the real plane as a model of `Geo.Incidence`

<!-- plan-section: lane-status -->

Date: 2026-09-06 (dispatched 2026-09-05)
Base: local `main` at `fd9cce8e7` (contains `992de4c54`)
ADR: [ADR-1652](../../research/09-decisions/adr-1652-the-real-plane-is-a-model-and-it-needs-no-case-split.md)
Roadmap: W3-8, second slice

## Status

`Geo.rplane : Geo.Incidence` **landed** — the ℝ² model ADR-1635 shaped the
record's `apart` field for and did not build. `Geo.Incidence` now has two
models with structurally different point equalities (`Eq` over ℚ,
`CPoint.Equiv` over ℝ) and different apartness notions, and its five derived
theorems instantiate at both.

Playfair (`Geo.Affine`) **did not land**. Existence is easy in both models;
uniqueness needs a route to `Parallel l m → Equiv (a*B − b*A) 0`, and over ℝ
the only route this lane found passes through a negation, whose removal is
tightness (`Not (Apart x y) → Equiv x y`) — which `creal.rs` documents as
absent by design. Over ℚ it is reachable (the explicit intersection point plus
`Geo.Rat.eqOrNe` on the denominator) but needs a new file, because this lane
must not edit `qplane.rs`. ADR-1652 § 5 sizes both.

## What landed

New file `crates/axeyum-lean-kernel/src/geo/rplane.rs`, registered from
`geo.rs`; 41 declarations, every one axiom-free.

| group | declarations |
| --- | --- |
| carriers | `Geo.RLine0` + `mk`/`rec`/`a`/`b`/`c`, `Geo.RLine0.Nondeg`, `Geo.RLine` |
| incidence | `Geo.RPlane.onRaw`, `.on`, `.Apart` |
| line equality | `Geo.RLine.Equiv` + `equiv_refl`/`equiv_symm`/`equiv_trans` |
| `PosBound` | `Geo.RPlane.posBoundCongr`, `.notZeroOfPosBound`, `.cancelPosBound` |
| point setoid | `Geo.RPlane.pointRefl`, `.pointSymm`, `.pointTrans` |
| congruences | `Geo.RPlane.onPoint`, `.onLine`, `.apartNe`, `.apartSymm`, `.apartCongr` |
| the join | `Geo.RPlane.join`, `.joinOnLeft`, `.joinOnRight`, `.joinNondeg`, `.joinExists` |
| the algebra | `Geo.RPlane.pivotAB`, `.defectAC`, `.defectBC`, `.defectSwap`, `.onOfDefects` |
| uniqueness | `Geo.RPlane.joinUnique` |
| existence | `Geo.RPlane.twoPointsRaw`, `.twoPoints`, `.triangle` |
| the model | `Geo.rplane` |

## The finding worth exporting

**The ℝ model needs no case split, and is therefore cheaper than the ℚ one.**
`Geo.qplane` uses ℚ's decidable equality twice, both times to decide *which* of
a line's two leading coefficients is nonzero. The ℝ model divides only by
`distSq P Q` (from `Apart`) and `a*a + b*b` (from `Nondeg`) — sums of two
squares the hypothesis already witnesses as positive — so the pivot never has
to know which summand is large, and a line's first point is one formula rather
than a branch. Where a ℚ development reaches for `eqOrNe`, ask first whether
the quantity actually divided by is the *sum*.

The second measured detail: `CPoint.distSq P Q` is **definitionally**
`(x P − x Q)² + (y P − y Q)²`, so `pivotAB`'s conclusion and `Apart`'s witness
are the same term after δ/ι and `cancelPosBound` consumes the witness with no
transport at all. That defeq is pinned on its own
(`dist_sq_unfolds_to_the_coordinate_difference_squares`) because the whole of
`joinUnique` rests on it.

## The measurement hazard this lane hit

**A negative control over `CReal` must not be a `def_eq` refutation between two
arithmetic terms.** The first `distSq` and `onRaw` shape pins asserted
`!def_eq(correct, wrong)` over `CReal` expressions; both ran past **ten
minutes** in `--release` on an otherwise-green run and were killed, while the
identical ℚ pins in the same file finish in seconds. Failing `def_eq` over
`CReal` is a search: congruence fails, and the kernel then unfolds both sides
into `CReal.mk` with their regularity proofs and compares sequences under a
binder. Refuting at `CReal.Equiv` is worse again — `Equiv` itself unfolds to a
`∀ n` over `Rat` arithmetic.

The rule the rewritten pins follow: over `CReal`, assert `def_eq` only where it
**succeeds**, and do the discriminating half by comparing the stored
`Definition` value as an interned `ExprId` — exact, `O(1)`, and strictly
stronger than `def_eq` for a shape claim. CLAUDE.md already says a pathological
negative control is worth deleting; what this adds is that over the constructive
reals the pathology is the default, not the exception.

## Gates

| gate | result |
| --- | --- |
| `cargo test -p axeyum-lean-kernel --release --lib -- geo:: --test-threads=2` | **20 passed, 0 failed**, 117.22 s |
| `cargo test -p axeyum-lean-kernel --lib -- geo::geo_tests::geo_prelude_builds --test-threads=1` (debug) | 1 passed, 0 failed, 435.72 s |
| `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` | exit 0 |
| `shape_search --include-constructed --ns Geo` | FOUND **119**, and the pinned count is `FIELD_COUNT + 11 + 46 + 41 = 21 + 11 + 46 + 41 = 119` |
| `cargo check -p axeyum-lean-kernel --all-targets` | exit 0, 1 m 12 s |
| `cargo fmt --all --check` | exit 0 |
| `python3 scripts/validate-facts.py` | exit 0, 2927 facts, 0 errors |
| `python3 scripts/check-settled-fact-statements.py` | PASS (after `--write`), settled=2652 pinned=2652 drifted=0 |
| `python3 scripts/check-kernel-trusted-core.py` | exit 0, 5 guards, 0 failures |
| `python3 scripts/check-autogenesis-holdout-isolation.py` | PASS, held_out=206, references=0 |
| `scripts/check-merge-hygiene.sh` | PASS (guard 6, `check-shape-duplicates.py --prebuilt`, SKIPPED: no `shape_search` binary on this host) |
| `./scripts/check-links.sh` | exit 0 |

## A second hazard, and a measurement that names it

`Geo.RPlane.pointRefl`/`pointSymm`/`pointTrans` are the **third** copies of
those three propositions: `metric.rs` already has
`Metric.CPoint.equivRefl`/`equivSymm`/`equivTrans`. They are kept deliberately
(the geo prelude builds `cpoint`, not `metric`), but the search that missed them
is worth naming, because the tool answered confidently:

```text
shape_search --name-like equivRefl                       → ABSENT
    groups=[logic,nat,axreal,integer,ipc,rat,characterization,string]
    declarations=3275   (positive control: any-kind=3275)
shape_search --include-constructed --name-like equivRefl → FOUND 20,
    including Metric.CPoint.equivRefl : ∀ P, CPoint.Equiv P P
```

**Without `--include-constructed` the index covers none of `creal`, `cpoint`,
`metric`, `geo`, `complex`, `intspace`, `rn`, `top`** — yet its `declarations=`
count (3275) clears the 3,050 floor a brief asks a lane to check. An ABSENT
verdict from the default index is not a statement about any of those
namespaces.

## Landed changes

| commit | what |
| --- | --- |
| `d69e35d83` | scaffold: carriers, `Nondeg` as an apartness witness, incidence, line equality, the `PosBound` lemmas, the congruences, the algebraic core |
| `7122b520f` | `join`, `joinUnique`, `twoPoints`, `triangle`, `Geo.rplane`, `CPoint.Equiv`'s setoid laws; the sweep's 41 new names |
| `5014f32bb` | the evaluation pins, ADR-1652, this file |
| `39df0535b` | regenerated PLAN, the ADR index, the census and the statement pins |
| `6ec73cfdd` | `Geo.Incidence.Parallel`, `parallel_symm`, `parallel_irrefl`, and the finding that the negative form is the wrong primitive for Playfair |
| `a82b4eabf` | the shape pins rewritten as stored-term comparisons after the `def_eq`-over-`CReal` measurement above |
| `2e5e6759d` | the `def_eq`-over-`CReal` hazard recorded in the ADR and here |
| `1904e43fc` | the point setoid laws are a THIRD copy (`metric.rs` has them); corrected in the open |
| `d924eec4d` | both real-model mutants registered in the `geo-incidence` mutation suite |
