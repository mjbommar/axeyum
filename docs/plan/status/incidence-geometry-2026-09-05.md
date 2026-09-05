# Lane: incidence-geometry — synthetic incidence geometry as a record, with the coordinate plane as a model (W3-8)

<!-- plan-section: lane-status -->

**Your lane's block (`IN PROGRESS`, incidence-geometry, 2026-09-05).** W3-8's
record landed and is green; the rational model and the `ring::rat` capability
it forced are in the same branch. `Geo.Incidence` is a **21-field record over
two carriers**, declared through the ADR-1578 `declare_record` spine at
`Sort 2` with the ADR-1595 setoid discipline — each carrier its own
equivalence, the incidence relation a congruence field for each, no `funext`
and no `Quot.sound`
([ADR-1635](../../research/09-decisions/adr-1635-incidence-geometry-needs-apartness-in-exactly-one-axiom-and-the-rational-ring-normalizer-could-not-cancel.md)).
All of it in NEW files (`crates/axeyum-lean-kernel/src/geo.rs`,
`src/geo/qplane.rs`) registered from `lib.rs`, so a concurrent lane's merge
into the kernel stays additive; `creal_point.rs` was not touched at all.

**The finding the brief asked for: exactly one axiom needs apartness.**
Hilbert I.1's uniqueness half (`joinUnique`) is the only axiom that *consumes*
distinctness; `joinExists`, `twoPoints` and `triangle` only produce it. Over ℚ
the consumption is a field cancellation and `(P = Q) → False` supplies it; over
ℝ the consumption is a division by `distSq P Q`, which is `CReal.inv`, which is
`PosBound`-indexed — the wall `CPoint.collinear_of_area_zero` already
documents in its own doc comment. So `apart` is a **field** of the record with
three laws (`apartNe`, `apartSymm`, `apartCongr`), and each model supplies its
own notion. `apartNe` is what stops the abstraction being vacuous: without it
`apart := True` satisfies every axiom.

**The unbudgeted cost was not the geometry, it was the producer.**
`ring::rat` declined *every* coordinate identity in this lane, for two
independent reasons neither of which was visible before the goals were put to
it:

1. It had no `cancel_pairs`. Its module doc said, verbatim, "None of the five
   ℚ targets produce an `x + (-x)` summand pair, so it was not built." Every
   identity here produces nothing else — each one asserts that a determinant
   expansion collapses.
2. It had no way to drop a `Num(0)`. `scale_item` emits `Item::Num(0)` for
   every `x * 0` and the additive normalizer never merges two `Num`s, so
   `a*0 + b*0 + c` normalized to three items against `c`'s one. Every
   statement about the triangle `(0,0), (1,0), (0,1)` has that shape.

Both passes are now in `ring::rat::Problem::cancel_pairs` (the first ported
from `ring::int`, the second new), with three matched tests including a
negative control (`x*y + -(x*x) = 0` must still decline `NotAnIdentity`) that
dies if the pass stops comparing factor lists. This is the ADR-0601 shape: the
geometry did not get a bespoke proof, the producer got a capability, and the
capability is guarded by a control that can fail.

**What the ℚ model costs, and where.** The whole model factors through ONE
algebraic lemma, `Geo.QPlane.onPivot`, and the `a ≠ 0 ∨ b ≠ 0` case split uses
it in *both* branches (the `b` branch is the same lemma with `(u,v,s,t)` and
`(U,V)` swapped, so the second case is three `ring` rearrangements rather than
a second proof). `Geo.QPlane.joinProp` — every line through `P` and `Q` is
proportional to the explicit join — needs **no non-degeneracy hypothesis at
all**; the three relations are three unconditional ring identities with the two
incidence left-hand sides added as summands on either side, and all three were
verified by hand before being encoded. Distinctness is spent in exactly one
place, `Geo.QPlane.joinNondeg`. `twoPoints` needs the case split only for the
FIRST point: the second is the first plus the direction `(-b, a)`, whose
incidence is one ring identity and whose apartness needs `Nondeg` alone —
`Rat.inv` appears at exactly ONE site in the whole model, inside
`Geo.QPlane.basePoint`'s branch closure (which runs for both cases of the
split, so the emitted term has two copies and the source has one).

**Mutation table (both mutants RUN, not predicted).** Baseline green, 12
tests, `scripts/cargo-serialized.sh test -p axeyum-lean-kernel --lib geo::`.

| mutant | outcome | kill count |
| --- | --- | --- |
| axiom I.1's uniqueness half loses its distinctness hypothesis (`geo.rs`, `join_unique_field`) | **killed** | 9 of 12 |
| the join's `a` and `b` coefficients are swapped (`geo/qplane.rs`, `declare_join`) | **killed** | 9 of 12 |

The three survivors in each case are the three tests that never build the
prelude (`field_list_matches_the_suffix_table`,
`field_indices_name_their_fields`, `the_record_is_refused_at_sort_one`), which
is the correct outcome and not a gap: both mutants fail at PRELUDE-BUILD time,
so no test that does not build it can see them. `git status` is clean after
the run — the harness restored the tree byte-for-byte.

**The mutation harness's first run was UNMEASURABLE, and the reason is worth
recording.** `mutation_controls.py`'s `Cargo` runner passes no
`--test-threads`, so libtest used every core and this suite's five
prelude-building tests ran at once; the run produced `running 12 tests` and no
`test result:` line, which the harness correctly reported as `INCONSISTENT`
rather than as a kill. It is a real classification, not a false negative — but
it is also a trap any memory-heavy kernel suite will hit. The second run set
`RUST_TEST_THREADS=2` in the environment (which `_capture` merges) and was
green. A later lane adding a kernel suite here should set that variable rather
than assume the default is safe.

**Line equality is extensional and that is the load-bearing choice.** With
`Equiv l m := ∀ P, (on P l → on P m) ∧ (on P m → on P l)`, reflexivity,
symmetry and transitivity are free and `onLine` is an `And.left`. The
alternative — proportionality of coefficient triples — needs the nonzero case
split three times just for transitivity, once per conjunct.

**What did NOT land: the ℝ² instance.** It is a `Geo.Incidence` instance and
not a parallel development, which is the point of the record, but nothing of it
is written. The sized obstruction is `joinUnique`, and only `joinUnique`:
`CPoint.collinear_of_area_zero` (`∀ A B C k, PosBound (distSq A B) k →
Equiv (cross A B C) zero → Collinear A B C`) is the theorem it has to route
through, and it takes a `PosBound` witness, so `apart P Q` for the ℝ model has
to be `∃ k, PosBound (distSq P Q) k` and the ℝ analogue of `Geo.QPlane.onPivot`
has to consume that witness through `CReal.inv` rather than through
`Rat.mul_eq_zero`. The other three axioms are cheaper than their ℚ twins, not
harder: `joinExists` is the same coordinate computation over `CReal.Equiv`,
`twoPoints` is the same shift, and `triangle` has `CPoint.cross_self_left` and
`CPoint.NonCollinear` already built. Nothing about the record blocks it.

<!-- plan-section: landed-changes -->

| 2026-09-05 | `7ec964eab` | `Geo.Incidence` — a 21-field incidence record over two carriers with Hilbert I.1 (split into `joinExists`/`joinUnique`, this kernel having no `ExistsUnique`), I.2 and I.3, plus `apart` and its three laws; and five theorems derived once over an arbitrary `I : Geo.Incidence` — `Collinear` (a Definition), `collinear_intro`, `collinear_perm`, `distinct_lines_meet_once` (which IS "two distinct lines meet in at most one point") and `triangle_not_collinear`. 7 tests. Every one of the 29 names is asserted present AND axiom-free with `Environment::contains` checked FIRST, and the declaration list is derived from `RecordNames::field_count` rather than a literal. |
| 2026-09-05 | `054cb3e38` | `Geo.qplane : Geo.Incidence` — the rational plane, 46 declarations: `Geo.QPoint`/`Geo.QLine0` with their projections, `eta` and `ext`; `Geo.QLine = Subtype Geo.QLine0 Geo.QLine0.Nondeg`; extensional line equality with its three laws; `Geo.QPlane.onPivot` and `onOfProp` (the one algebraic lemma, used in BOTH branches of the nonzero split); `joinProp` (proportionality with NO non-degeneracy hypothesis); `joinNondeg`, `joinExists`, `joinUnique`, `shift`/`shiftOn`/`shiftApart`, `basePoint`, `twoPoints`, `triangle`. Plus `Geo.Rat.eqOrNe` from `Rat.lt_trichotomy` — the only place the model uses ℚ's decidability. In the same commit: two new passes in `ring::rat::Problem::cancel_pairs` with three matched tests (19 ring::rat tests pass), and `geo::qplane::congr_cross`, the two-carrier congruence `structures::congr_arg` cannot express. |
| 2026-09-05 | `8a1ad873a` | Five more tests. `the_handle_names_every_live_geo_declaration` derives the population from `Environment::iter` and requires SET EQUALITY against the handle (measured: 75 live names, vacuity floor 70); four evaluation tests, one per definition family, each with its negative half — including the join-coefficient swap the mutation suite runs, pinned at FREE VARIABLES because a concrete point pair can make two coefficients coincide. The `geo-incidence` mutation suite is registered with the brief's two mutants. |
| 2026-09-05 | `3243d58e8` | Two curated facts — `F:geo-incidence-model-rational-plane` (the consistency witness, checked by `kernel_declaration_projection --require-declaration Geo.qplane --require-kind definition`, the only in-tree tool that can assert a DEFINITION exists) and `F:geo-distinct-lines-meet-once`. `Geo` added to `validate-facts.py`'s `KERNEL_THEOREM_RE` namespace alternation, with BOTH halves pinned in the allowlist's own control suite: `Geo.qplane` accepted, `Geometry.qplane` and bare `Geo` still rejected. |
| 2026-09-05 | `e15cef034` | Regenerated `artifacts/autogenesis/kernel-dependency-projection-v1.json` (declarations 4291 → 4485), because `check-merge-hygiene.sh` guard 10 compares it against the live `shape_search` count with a tolerance of 100 and `Geo.*` adds 75. |
