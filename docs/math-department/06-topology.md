# 06 — Topology

Reviewer: a topologist — point-set and algebraic
Verdict, 2026-09-06: **the shelf exists — 97 metric declarations and 53 frame
declarations, all axiom-free — and it is a shelf with no separation, no
connectedness, and one instance of its own carrier**
Last measured: 2026-09-06 at `5f4c38c32`

> "There is no topology here. Not a thin topology, not an unusual topology.
> Zero declarations. I am the shortest review in the department and the one
> that blocks the most people."
>
> **Revised 2026-09-04:** "You built the metric layer instead of asking me
> which topology to build, and the answer fell out: nothing in your record is
> a subset, so my objection to membership predicates never applied. I withdraw
> the blocking status. I still have no topological space."
>
> **Revised again 2026-09-06:** "You have a topological space now, and I was
> wrong twice. I said three fields were blocked behind me; measure, geometry
> and ℝⁿ all landed while I had nothing, so they were never blocked. And I said
> nothing in the record was a subset; `Subtype` landed the next day and
> `Metric.subspace` carves one. What I would say now is narrower and harder:
> `Top.ballFrame` is one instance, it cannot separate two points, and nothing
> in this library is connected."

> **AUDITED 2026-09-04.** Every absence claim in this file was re-checked
> against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for the evidence, and the
> corrections marked **[AUDIT]** below. Across the twelve files, 11 of 76
> absence claims were false and 12 more overstated the gap; the cause is that
> the ledger characterises only 38% of its proved facts and does not cover 430
> kernel theorems at all (ADR-1605).

> **Retired 2026-09-06 (ADR-1674):** the 430 is not reproducible by its own
> method - three later readings give 599, 620, 721 and 973 on three different
> denominators. The measured, gated figure is **721 of 3,079 registered
> kernel theorem names uncovered**, ratcheted by `gen-ledger-coverage`.

## The persona

Thinks in open sets, continuity as preimages, compactness, and connectedness,
then in fundamental groups, homology, and covering spaces. Regards topology
less as a subject than as the language every other analytic and geometric
subject is written in. Their test is whether you can say "f is continuous"
without mentioning ε.

## What the library has today

Measured at `5f4c38c32` from `shape_search --include-constructed`, which
indexed **4,765 declarations** across sixteen prelude groups — 30 axioms (every
one of them `AxReal.*`, the axiomatised-reals sandbox), 1,222 definitions,
3,272 theorems. Freshness control that postdates every claim below:
`Complex.holomorphic_pow`, admitted this morning at `2758e7b18`, is in the
index (`verdict: FOUND 1`).

| namespace | declarations | what it is |
|---|---|---|
| `Metric` | 97 (52 theorems, 42 definitions, the record with its constructor and recursor) | the constructive metric carrier: `dist`, the four laws, uniform and pointwise continuity, Cauchy and `Complete`, total boundedness, `Compact`, the EVT, `subspace` |
| `Top` | 53 (24 theorems, 26 definitions, the record with its constructor and recursor) | `Top.Frame`, a 16-field setoid record with countable joins, and `Top.ballFrame`, the open-ball frame of ℝ |
| `RN` | 58 | ℝⁿ at symbolic dimension, with `RN.metric` a `Metric` instance |
| `IntSpace` | 98 | integration, and `IntSpace.bundledL1` a `Metric` instance on L¹ |

Carriers that are metric spaces on main, counted by the instance declaration
rather than by prose: **ℝ** (`Metric.creal`), **the Euclidean plane**
(`Metric.cpoint`), **ℝⁿ at symbolic dimension** (`RN.metric`), **L¹**
(`IntSpace.bundledL1`, with `crealFiniteL1` and `crealIntervalL1` as its two
concrete instances). Plus two constructions: `Metric.subspace` (carrier
`Subtype M.carrier P`, `subspace_dist` an `Eq.refl`) and `Metric.prod`.

**Sixteen facts in the ledger cover this shelf** — 7 `F-metric-*`, 4 `F-top-*`,
3 `F-rn-*`, 2 `F-intspace-l1-*` — and all sixteen are `epistemic_status:
proved` with `axiom_footprint: []` and `kernel-term` evidence. Read from the
fact files, not from a rendered name.

**What is absent, measured in the same 4,765-declaration invocation** — the
index itself is the positive control, since the same run answered `FOUND 53`
for `--ns Top`:

| searched | matches |
|---|---|
| `hausdorff` | 0 |
| `connected` / `Connected` | 0 |
| `completion` | 0 |
| `homotopy`, `homology`, `fundamental` | 0 each |
| `funext`, `Quot.sound` | 0 each |

And the intermediate value theorem is still exactly where it was: **20
declarations whose names contain `ivt`, every one of them `CReal.ivt*`**, none
in `Metric` and none in `Top`.

### One measured defect, and it is the third time on this shelf

**All twelve `Metric.prod*` declarations are invisible to the retrieval
index.** `crates/axeyum-lean-kernel/src/metric_prod.rs` declares twelve owned
names (`Metric.prod`, `prod_fst`, `prod_snd`, the two projection
uniform-continuity lemmas, the two continuity-into-the-product lemmas,
`prod_complete`, and the four `cpoint_of_prod` / `prod_of_cpoint` bridges).
`crates/axeyum-lean-kernel/examples/shape_search.rs` builds
`build_metric_prelude` under `--include-constructed` but never
`build_metric_prod_prelude`, and its group list has no `metric_prod` entry. So
`--ns Metric` returns 97, `Metric.prod` is not among them, and a lane that asks
whether the product metric exists is told, confidently, that it does not.

This is the same defect twice repaired on this same shelf: the `b7df58b7b`
history row records "two retrieval tools were found blind to the new prelude
and would have reported a confident ABSENT for all 49; both fixed", and the
`992de4c54` row records a third copy of `Metric.CPoint` lemmas built because
the tool was blind again. The pattern is not a bug in one tool — it is that a
new prelude module gets registered in `lib.rs` and in its own test file, and
the retrieval index has to be told separately, by hand, in a list nothing
derives.

## Their verdict

The design bet of ADR-1602 has paid, and the measurements that could have
refuted it did not. Continuity over an arbitrary pair of metric spaces reaches
ℝ **definitionally** — `Metric.dist creal x y` reduces to `abs (x + -y)` and
`UniformlyContinuousOn`'s modulus was already in the `1/(k+1)` shape, so the
two predicates are the same proposition, at zero estimates. Bishop compactness
was built without covers and the interval EVT re-derived from the general one
is the **same interned term** the direct proof produces. Completeness
generalised off ℝ at a cost of two bridge lemmas that already existed. Four
carriers now share one vocabulary where this library previously shared none.

What the reviewer will not concede is that this makes a topology. `Top.Frame`
is a carrier with **one** instance. `Top.ballFrame` is the frame *presented by*
the rational-ball basis, not the lattice of open subsets of ℝ: its elements are
arbitrary sets of basic balls, so two sets whose unions coincide are different
formal opens, and getting the real lattice means quotienting by the covering
relation, which nobody has attempted — ADR-1643 says so plainly. It cannot
separate two points: `Top.ball_separated` is the geometry half and the index
selection from `CReal.Apart` is not proved. And there is no `Connected`
anywhere in 4,765 declarations, so the IVT is still a theorem about `CReal` on
an interval and not an instance of anything.

Two claims this reviewer made in September and now withdraws, because the
record refutes them:

- **"Three of the twelve reviewers are blocked behind this file."** They were
  not. `IntSpace` (98 declarations, the integral and L¹), `Geo` (119, incidence
  geometry in two models) and `RN` (58) all landed while this shelf was empty
  or nearly so. Nothing waited. What topology bought those shelves came
  *afterwards* — L¹ became a metric space because `Metric` existed, not before.
- **"Nothing in your record is a subset."** `Subtype` landed at `c0054fd3b`
  with 7 declarations, and `Metric.subspace` carves one. The narrower true
  statement is that the *frame* still avoids point-membership predicates:
  `Top.Opens` is `Rat → Nat → Prop`, a predicate on a **countable index of
  basic balls**, and `Top.MemOpen : CReal → Top.Opens → Prop` is the separate
  map to points. The constructive difficulty — deciding whether a real lies in
  a set — is pushed into `MemOpen` and never asked of the lattice operations.
  That is the design working, not the objection evaporating.

One correction the reviewer wants recorded against a live document: ADR-1643's
"What did NOT land" says the point-of-a-frame construction "needs a `Subtype`
the kernel does not have". `Subtype` landed at `c0054fd3b`, **fourteen hours
before** the frame lane's own commit `e0f0be745`, and `c0054fd3b` is an
ancestor of it. That blocker was already stale when it was written down.

## What they would say is missing

- **Separation.** Hausdorff for `Top.ballFrame` from `CReal.Apart`. ADR-1643
  sizes the missing half as index selection, not geometry: one `Or.rec`, two
  `Exists.rec`s, an Archimedean application and about four rational
  rearrangements, against lemmas that all exist — 250–400 lines with no design
  question in front of them.
- **Connectedness**, and the IVT re-derived as an instance. Zero declarations
  today.
- **A second frame instance.** One instance does not exercise a carrier. The
  obvious candidate is the ball frame of an arbitrary `Metric`, which would
  also say whether `Top` and `Metric` are two shelves or one.
- **The covering quotient**, or an ADR saying it is out of scope. Until then
  `Top.ballFrame` is not the topology of ℝ and every theorem about it has to
  say so.
- **`Metric.completion`.** ADR-1625 measured 1 of 33 declarations reusable and
  sized it at four `CReal.limit` lemmas plus a `speedup` bridge. Until it
  exists, L¹ is a metric space that is not known complete, and `CReal` is not
  the completion of ℚ in this library — there is no `Metric.rat`, because
  `dist` is `CReal`-valued.
- **Compactness transfer through the product**, and the converse direction of
  continuity into a product. Named as residue by ADR-1639, still absent.
- **Algebraic topology.** Fundamental group, homology. Far away; needs group
  quotients, hence [04-algebra.md](04-algebra.md). ADR-1595 decided quotients
  are setoids and `Quot.sound` stays out, so this is a setoid-of-loops
  construction or nothing.

## The blocker

**Nothing, and that is the finding.** The design decision is made (ADR-1602),
the carrier is built (ADR-1643), `Subtype` and `Sigma` exist, and every
remaining item on the list above is bounded term-building against lemmas that
are already in the kernel. There is no missing kernel primitive and no open
design fork on the critical path.

Two secondary constraints survive, and both are now decisions rather than gaps:

- **No `funext`, by policy.** `funext` is absent from the index and ADR-1601
  keeps classical principles as hypotheses rather than axioms. Function spaces
  with their own topology are therefore setoid constructions — the same fork
  [04-algebra.md](04-algebra.md) resolved by building `AlgS` over setoids.
- **Algebraic topology needs quotients**, and ADR-1595 answered that with
  setoid quotients. That half of the subject is not gated on a kernel change;
  it is gated on somebody doing it.

## Next five, in their priority order

All five of the reviewer's original items are landed. The list is kept for the
record; the reissued list follows.

- [x] **1. Choose the constructive topology and write the ADR.** *Done
      2026-09-04, ADR-1602: metric first, pointfree later, open sets never.*
      Original framing: Open sets, apartness spaces, or locales. Their view:
      this one decision is worth more than any five theorems, because it
      determines whether the analysis shelf ever generalizes.
- [x] **2. A metric-space carrier with ℝ and `CPoint` as instances**, and
      completeness lifted from the existing `converges_of_cauchy`. *Done
      2026-09-04; the namespace measures 97 declarations at `5f4c38c32` with
      four carriers, not two. Completeness did generalize, at a cost of two
      bridge lemmas that already existed.*
- [x] **3. Bishop compactness — total boundedness plus completeness — on
      intervals**, then the extreme value theorem re-derived as an instance
      rather than re-proved. *Done 2026-09-04; `Metric.creal_evt_approx_max`
      and `Metric.creal_evt_approx_max_via_metric` are both in the index and
      the derivation was pinned as the same interned term.*
- [x] **4. Continuity as a topological notion**, with the existing
      `UniformlyContinuousOn` proved to imply it. *Done 2026-09-04;
      `Metric.continuousOn_of_uniformlyContinuousOn` and
      `Metric.creal_uniformly_continuous_on` are in the index and the bridge is
      definitional.*
- [x] **5. Products and subspaces.** *Both halves landed by 2026-09-05:
      `Metric.subspace`, `subspace_carrier` and `subspace_dist` are in the
      index; the twelve `Metric.prod*` declarations are on main in
      `metric_prod.rs` but **not** in the retrieval index — see the defect
      above. Marked done against the source, not against the search.*

## The next five, reissued 2026-09-06

- [ ] **1. Hausdorff separation for `Top.ballFrame`.** From `CReal.Apart`,
      through index selection. `Top.ball_separated` is the half that landed;
      ADR-1643 sizes the rest at 250–400 lines against `Rat.natDivSucc_add`,
      `Rat.add_le_add`, `Rat.lt_of_le_of_lt` and `CReal.lt_cotrans`, all
      present. Their reason for ranking it first: a space that cannot tell two
      points apart is not yet doing any work.
- [ ] **2. Connectedness, and the IVT as an instance.** Zero `connected`
      declarations in a 4,765-declaration index, and 20 `CReal.ivt*` names none
      of which mention `Metric` or `Top`. The EVT is the precedent and it
      worked: that instance derivation was checkable as term identity, not as a
      hope.
- [ ] **3. `Metric.completion`, and where `CReal` sits relative to it.** Sized
      by ADR-1625 at four `CReal.limit` lemmas plus a `speedup` bridge, with
      the measurement that 1 of 33 existing declarations is reusable because
      they are all stated about `CReal` alone. Until this lands, "complete
      metric space" is a phrase the library can say once.
- [ ] **4. A second `Top.Frame` instance, and a decision on the saturation.**
      The ball frame of an arbitrary `Metric` is the natural second instance
      and would settle whether `Top` and `Metric` are one shelf. Separately, an
      ADR should either build the covering quotient or state that
      `Top.ballFrame` is permanently the presented frame — right now that
      caveat lives only in ADR-1643's prose and in one fact's `notes`.
- [ ] **5. Teach the retrieval index the product metric.** Not the reviewer's
      mathematics, and they say so, but it is their shelf carrying the defect
      for the third time. `shape_search.rs` should build
      `build_metric_prod_prelude`, and its group list should be derived from
      the build calls rather than hand-written — the file already carries a
      cross-check that the two agree, and it passes precisely because both
      halves omit `metric_prod`.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: zero topology declarations, confirmed against a positive control. Three other reviewers blocked behind this file. | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Next Five items 1 and 2 both landed** (roadmap W0-3 and W2-1). The design question is answered by ADR-1602 — metric layer first, pointfree frames for topology proper when needed, open-set spaces never — and it was answered by *building* rather than deciding. 49 `Metric` declarations, all footprint 0, with ℝ and the Euclidean plane as instances and completeness generalized off ℝ. Two things the build taught that no argument would have: **nothing in the record is a subset**, so this reviewer's objection to membership predicates never arose; and the plane's **unsquared** triangle inequality landed on the first kernel run, **refuting `CPointPrelude::cauchy_schwarz`'s own doc comment** that the statement 'is not expressible, let alone provable, here' — a stale blocker predating `CReal.sqrt`. | `b7df58b7b`; `metric::` 17 passed |
| 2026-09-04 | **Next Five items 3 and 4 landed** (roadmap W2-3, W2-2), and both were the cases that could have refuted ADR-1602. Continuity over an arbitrary pair of metric spaces, with the `CReal` bridge costing **zero estimates** because the metric distance reduces to `abs (x + -y)` and `UniformlyContinuousOn`'s modulus was already in the right shape — the two predicates are definitionally the same proposition. Bishop compactness as total boundedness plus completeness, no covers; the EVT proved over any totally bounded subset of any metric space with completeness never used, and **the interval EVT re-derived from it as the same interned term** that the direct proof produces. 44 declarations, 43 admitted first time. The reviewer's item 5 (products and subspaces) remains split: products buildable, subspaces on `Subtype`. | `5bb30b809`; `metric::` 29 passed |
| 2026-09-05 | **Item 5's subspace half opened** (roadmap W0-5): `Metric.subspace M P` with carrier `Subtype M.carrier P`, every other field the ambient one restricted, and `subspace_dist` an `Eq.refl` — "the distance is the ambient one" is now a theorem, not a construction. `[a,b] ⊂ ℝ` is the first instance. What remains is a decision about migrating the existing `*On` forms, which has real proof cost. | `c0054fd3b` |
| 2026-09-05 | **Item 5 landed** (roadmap W2-10, ADR-1639): `Metric.prod` with the max metric, uniformly continuous projections, continuity into the product from both components, and completeness transfer; 12 declarations, footprint 0. ℝ² as `CPoint` is a carrier equivalence with `prod creal creal`, not an isometry. Compactness transfer and the converse continuity direction are the residue. | `84320ce9e` |
| 2026-09-05 | **The topological carrier exists, as a frame** (roadmap W2-21, ADR-1643, the deferred half of item 1's decision): `Top.Frame` as a setoid record with countable joins, the generic frame theorems, and the open-ball frame of ℝ as the first instance with density and separation lemmas; 53 axiom-free declarations and not one kernel refusal during development. Two design facts worth keeping: a frame's equivalence is derived from the order, so instances owe six fewer proofs than metric spaces; and indexing opens by centre and radius avoids the pairing function whose content is a held-out family. Hausdorff from apartness is the residue. The frame is the one presented by the basis, not the lattice of all opens. | `e0f0be745`; `top_frame::` 11 passed in the lane |
| 2026-09-06 | **Re-measured, not re-built: nothing has touched this shelf since `e0f0be745`.** The commit log over `metric*` and `top_frame*` since 2026-09-04 ends at 2026-09-05 15:15. Against a fresh index of 4,765 declarations: `Metric` 97, `Top` 53, `RN` 58, `IntSpace` 98; 30 axioms, all `AxReal.*`; 16 ledger facts on this shelf, every one `proved` with `axiom_footprint: []`. Three claims in this file were **refuted by the record and withdrawn**: the three "blocked" reviewers were never blocked (measure, geometry and ℝⁿ landed anyway); "nothing in the record is a subset" (`Subtype`, 7 declarations, and `Metric.subspace` carves one); and ADR-1643's "needs a `Subtype` the kernel does not have" was stale fourteen hours before it was written. One defect found by measuring: **the twelve `Metric.prod*` declarations are absent from `shape_search --include-constructed`**, because it builds `build_metric_prelude` and not `build_metric_prod_prelude` — the third recurrence of retrieval blindness on this shelf. The file's own `## How to re-measure` block was **broken in both directions** and has been replaced: it reported the `metric.rs` doc comment quoting this file's 2026-09-04 baseline as evidence of topology, and its `topology` search missed `top_frame.rs`, whose first line reads "a topological carrier built as a frame". | `5f4c38c32`; `shape_search --include-constructed --ns Top` = `FOUND 53`, `--ns Metric` = `FOUND 97`, freshness control `--name-contains holomorphic_pow` = `FOUND 1` |

## How to re-measure

The `grep`-over-source block this section used to carry was retired on
2026-09-06 because it was wrong in both directions. It counted **files**, and
its hits for `topology`, `open_set`, `homotopy`, `homology` and
`fundamental_group` were all the same one file —
`crates/axeyum-lean-kernel/src/metric.rs`, whose doc comment at lines 2–7
*quotes this file's own 2026-09-04 baseline* — so the instrument reported the
record of an absence as a presence. And a case-sensitive search for `topology`
misses `top_frame.rs`, whose first line is "a **topological carrier built as a
frame**". Its positive control was pinned at `riemann` = 16 files; that search
now returns 28, so the pin was stale as well.

Measure declarations, not words:

```sh
# The census. Reports the namespace counts and, in its first two lines, the
# coverage and the total -- read BOTH: a group it never builds gives a
# confident, wrong ABSENT for everything in that group.
target/release/examples/shape_search --include-constructed --list-namespaces

# The two namespaces this file is about. Expect FOUND 53 and FOUND 97.
target/release/examples/shape_search --include-constructed --ns Top    --limit 300
target/release/examples/shape_search --include-constructed --ns Metric --limit 300

# Freshness control that must POSTDATE the claim you are checking: pick a
# declaration from the newest kernel commit and require FOUND 1. A stale
# prebuilt binary reports a confident ABSENT in every direction.
target/release/examples/shape_search --include-constructed --name-contains holomorphic_pow

# KNOWN BLIND SPOT, 2026-09-06: shape_search does not build
# `build_metric_prod_prelude`, so the twelve `Metric.prod*` declarations return
# ABSENT although they are on main. Read the source list instead until fixed:
grep -n 'Metric[.]prod' crates/axeyum-lean-kernel/src/metric_prod.rs

# The ledger side. Every fact on this shelf should be `proved` with an empty
# axiom_footprint; read the fact file, never a rendered name.
ls artifacts/facts/F-top-*.json artifacts/facts/F-metric-*.json
python3 scripts/validate-facts.py
```

## Related

- [03-classical-analysis.md](03-classical-analysis.md),
  [08-probability-and-statistics.md](08-probability-and-statistics.md),
  [05-geometry.md](05-geometry.md) — named in September as blocked behind this
  file; measured 2026-09-06 as having advanced without it
- [02-constructive-analysis.md](02-constructive-analysis.md) — the theorems
  that would become instances
- [04-algebra.md](04-algebra.md) — the setoid-quotient decision (ADR-1595) that
  algebraic topology inherits
