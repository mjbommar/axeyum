# 04 — Algebra

Reviewer: an algebraist — groups, rings, fields, representation theory
Verdict, 2026-09-06 (re-measured): **the spine grew a shelf — quotient groups, the first isomorphism theorem in both forms, the polynomial ring, modules, subgroups, constructive fields and vector spaces — and there is still not one ideal in the library**
Last measured: 2026-09-06 at `1de0edfc6`

> "You have written down the axioms of a group and proved that inverses are
> unique. Come back when you can form G/N." — 2026-09-04
>
> **Revised the same day:** "You formed G/N without a quotient type, by keeping
> the carrier and coarsening the equivalence, and the first isomorphism theorem
> cost three lines more than it would have with `Quot.sound`. I withdraw the
> objection to the method. The shelf is still nearly empty."
>
> **2026-09-06:** "Two days later I count 407 declarations on the setoid spine
> and 115 theorems over it, up from a couple of dozen. The group side is
> genuinely done to the first isomorphism theorem, in both the setoid form and
> the classical `G/ker f ≅ Im f` form. The ring side stopped at the polynomial
> ring: there is no ideal, no `R/I`, and therefore no field extension and no
> Galois theory. You built the half of the subject that setoids made cheap."

> **AUDITED 2026-09-04.** Every absence claim in the 2026-09-04 reading was
> re-checked against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for the evidence, and the
> corrections marked **[AUDIT]** below. Across the twelve files, 11 of 76
> absence claims were false and 12 more overstated the gap; the cause is that
> the ledger characterises only 38% of its proved facts and does not cover 430
> kernel theorems at all (ADR-1605). **This file was re-measured again on
> 2026-09-06** against `1de0edfc6`; what changed is in the last progress-log
> row.

> **Retired 2026-09-06 (ADR-1674):** the 430 is not reproducible by its own
> method - three later readings give 599, 620, 721 and 973 on three different
> denominators. The measured, gated figure is **721 of 3,079 registered
> kernel theorem names uncovered**, ratcheted by `gen-ledger-coverage`.

## The persona

Works with quotients constantly and without thinking about it: quotient
groups, quotient rings, ideals, modules over a ring, field extensions,
representations. Their first move on any new structure is to find its
congruences and quotient by them. Judges a formalization by whether the
isomorphism theorems are stated, because everything after them assumes them.

## What the library has today

Measured at `1de0edfc6`. The kernel index reports **4,839 declarations** across
sixteen prelude groups (**3,340** across the eight non-constructed ones, which
is where all of this reviewer's material lives). The namespaces they care
about: **`AlgS` 407**, **`Alg` 193**, **`CatS` 107**. The ledger holds **2,963
facts, 2,687 proved, 1,585 landmark**.

**Two spines, eleven records each, and a real layer of theory on top of the
setoid one.**

The `Alg` spine is an `Eq`-based record hierarchy at `Sort 2`:

```
Magma → Semigroup → Monoid → CommMonoid → Group → CommGroup
                          → Semiring → Ring → CommRing → Field
                                            → OrderedRing
```

with forgetful projections, and a parallel `AlgS` spine carrying an explicit
`equiv` field plus congruence obligations, for carriers where equality is not
syntactic. `Alg` is derivable from `AlgS` via `ofAlg`, never the reverse.

The two spines are no longer the same size, and that is the finding of the last
two days:

| | records | theorems | total declarations |
|---|---|---|---|
| `Alg` (over `Eq`) | 11 | **15** | 193 |
| `AlgS` (over an explicit `equiv`) | 11 | **115** | 407 |

Everything built since 2026-09-04 is on the `AlgS` side, and the reason is
measured rather than stylistic: an `Eq` spine cannot even *state* a polynomial
ring, because commutativity of coefficient functions is an equality of two
lambdas and needs `funext`. Zero declarations in the index match `funext`.

Where the 115 setoid theorems sit:

| layer | theorems | what it is |
|---|---|---|
| `AlgS.OrderedRing` | 32 | numerals, order, and the generic finite-probability layer (W1-10) |
| `AlgS.Poly` | 16 | the polynomial ring over an abstract `AlgS.CommRing` |
| `AlgS.Subgroup` | 15 | subgroups as a meet-semilattice; the kernel is one |
| `AlgS.Module` | 11 | modules, `linComb`, `spans`, `linearIndependent`, `isBasis` |
| `AlgS.Index` | 10 | `le`, `removeAt`, `insertAt` and their defining equations |
| `AlgS.*` (top level) | 10 | groups and rings: cancellation, `x·0 = 0`, `x·(−1) = −x`, … |
| `AlgS.Hom` | 9 | homomorphisms, kernels, images, both isomorphism statements |
| `AlgS.Field` | 5 | apartness, its congruences, uniqueness of the inverse, cancellation |
| `AlgS.Exchange` | 4 | the linear-combination split the Steinitz exchange needs |
| `AlgS.VectorSpace` | 3 | `solve_smul`, `smul_left_cancel`, `basis_zero_unique` |

The named pieces an algebraist would actually ask about:

- **Quotient groups and the first isomorphism theorem, twice.**
  `AlgS.Hom.quotient` builds `G/ker f` **with the same carrier and a coarser
  equivalence** — `equiv := fun a b => H.equiv (f a) (f b)` — so there is no
  carrier of equivalence classes and no `Quot` anywhere. `AlgS.Hom.firstIso`
  states the setoid form; `AlgS.Hom.firstIsoClassical` states `G/ker f ≅ Im f`
  as three conjuncts about two group objects, with `AlgS.Hom.imageGroup` a
  genuine group over `Subtype H.carrier (image f)`. Sixteen `AlgS.Hom.*`
  declarations, footprint empty.
- **Subgroups as a meet-semilattice**: `IsSub`, `le`, `inter`, `top`, `bot`,
  the lattice laws, and `ker_isSub`. **Join is absent** — it needs a
  word-closure inductive, which is also what would make a *normal* subgroup
  statable.
- **The polynomial ring as a full `AlgS.CommRing`**: `AlgS.Poly.commRing`, all
  23 fields, over an arbitrary abstract `AlgS.CommRing`, with the additive
  `commGroup` and `AlgS.Module.polyModule` beside it. Multiplication is an
  antidiagonal walk (`Nat.sub` does not exist at the `AlgS` build position).
- **Constructive fields**: `AlgS.Field`, 29 fields, whose inverse is
  **existential** — `mulInvEx : ∀ a, apart a zero → ∃ b, a·b ~ 1` — because
  `CReal.inv` takes its modulus as data and no `Prop` apartness witness
  survives large elimination. `AlgS.Field.IsTight` is a *predicate*, not a
  record field: `Rat.fieldS_isTight` proves it and `CReal` cannot.
- **Vector spaces**: `AlgS.VectorSpace.IsVectorSpace`, `Rat.vectorSpaceS`,
  and the atomic Steinitz step `solve_smul`.
- **The index calculus toward invariance of dimension** (2026-09-06,
  ADR-1657): `AlgS.Index.{le, removeAt, insertAt}` with ten defining equations
  as ι-reductions, and `AlgS.Exchange.linComb_removeAt_insertAt`, the split of
  a linear combination at an arbitrary index. 17 declarations, footprint 0.
- **The category of groups** (ADR-1626): `CatS.grp` and `CatS.mon` with
  morphisms bundled as `Subtype (G.carrier → H.carrier) (IsGrpHom G H)`,
  `CatS.forgetGrpMon` as a functor, and `CatS.grp_isProduct` — the product of
  two groups is a categorical product.

Instances, on the setoid side: `Rat.commRingS`, `Rat.fieldS`,
`Rat.vectorSpaceS`, `AlgS.Rat.orderedRingS`, `AlgS.Int.orderedRingS`,
`CReal.commRingS`, `CReal.orderedRingS`, `CReal.addGroupS`,
`CReal.fieldS`, `Complex.commRingS`. On the `Eq` side: ℕ, ℤ, ℚ.

Concrete algebra off the spine, unchanged: linear algebra over ℚ
(`rowEchelon`, `isEchelon`, `rank`, `nullity`, determinants at symbolic
dimension, Cramer's rule, matrix row operations) and polynomial arithmetic over
ℚ and ℂ (`polyEval`, `polyAdd`, `polyMul`, `polyScale`, degree bounds,
`hornerFromTop`, `factorQuotient`). `Rat.polyEval_mul` is still absent — an
~800-line port not reachable from the abstract theorem, and ℚ[X] is still not a
*named* prelude instance of `AlgS.Poly.commRing`.

**On the producer side, and it counts for nothing here yet.** `axeyum-cas`
landed matrix groups over ℚ (`classify_rational_matrix_group`: finiteness, the
element list and the order, four re-derivable infiniteness routes) and a
character-table checker over ℚ(ζ) verified on S3, S4, A4, A5 and Q8, on
2026-09-06 at `5a7355b2a`. **No fact registers any of it**: a search of
`artifacts/facts/` for "character table", "matrix group", "matgroup" and
"chartable" returns nothing, with "smith normal form" as the positive control
in the same search (it hits). Under [ADR-0601](../research/09-decisions/adr-0601-three-producers-one-trust-anchor.md)
that is `cas-internal` — a producer's output with no kernel evidence — and this
reviewer counts it as zero representation theory. The ledger-wide figure is
**61 `cas-certificate` facts, 16 kernel-reconstructed, 45 `cas-internal`
(73.8%)**. The new `axeyum-arith` crate (ADR-1710: `Normalize`, `HenselLift`,
`AlgebraicNumber`, ~196 KB of source) is the same story one level lower — real
exact-arithmetic engineering, no kernel statement.

## Their verdict

The elementary theorems are still elementary: inverses unique, cancellation,
`x·0 = 0` are the first ten minutes of a first course. What changed is that
they are no longer *all* there is. The first isomorphism theorem is proved in
the form an algebraist would demand — an isomorphism between two group objects,
not a statement about a coarsened relation — and the polynomial ring is a
genuine `CommRing` over an arbitrary commutative ring, not a coefficient-list
convenience over ℚ.

The reason the shelf was empty was identified immediately and it was
**quotients**. The kernel's declaration language supports Lean's quotient
package — `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` are the four variants of
`QuotKind` in `env.rs` — and there is no `Sound`. Measured today, it is
stronger than that: the index carries **zero declarations of quotient kind at
all**, across all sixteen prelude groups. Nothing in this library is a
quotient type.

**That objection was answered on 2026-09-04, and not the way the reviewer
expected.** The route is not to add the axiom but to stop asking for a carrier
of classes: a quotient group is *the same carrier under a coarser
equivalence*, which the `AlgS` spine can express because it carries `equiv` as
a field. The revised position is at the top of this file.

Two of the reviewer's own complaints have since been retired by measurement,
and both retirements are corrections *against* this file's earlier text:

- **"No `funext`, so function spaces cannot be given their standard
  structure"** — false as stated. Over setoids they can, and only over
  setoids: `AlgS.Poly` is a carrier of coefficient *functions*, and it is a
  commutative ring. What `funext` blocks is the `Eq` spine, not the library.
- **"`Subtype` and `Sigma` are absent"** — true when ADR-1595 was written that
  morning, false by that evening (ADR-1613, `c0054fd3b`). The index now
  reports `Sigma` 8, `PSigma` 5, `Subtype` 7.
  The classical isomorphism theorem was then proved *through* `Subtype`, at
  three membership proofs, because `Subtype.val` ι-reduces and fourteen of the
  image group's fifteen fields came free.

What remains true is the second half of the original complaint, and it is now
sharply localized. **The group side went to the isomorphism theorem; the ring
side did not start.** Absent from the index, each checked in one dump of all
**4,839** declarations (`--include-constructed`) with the 600 `Alg`/`AlgS`
names in the same dump as the positive control:

- **ideals** — zero matches for `ideal` or `Ideal`, so no `R/I`, no prime or
  maximal ideals, no quotient fields
- ℤ/n **as a ring** — `Nat.modAdd_isGroup` gives the additive group only
- **localization, tensor products, quotient modules** — zero matches
- **field extensions, splitting fields, Galois theory** — zero matches for
  `extension`, `splitting`, `galois`/`Galois`
- **representation theory** — zero matches for `representation` or `character`
- **group actions** — zero matches for `action`, `orbit`, `stabiliz`, `sylow`
- **the second and third isomorphism theorems** — zero matches for `secondIso`
  or `thirdIso`; the first is the only one
- **normal subgroups** — zero matches for `Normal`; the seven lowercase
  `normal` hits are `Rat.normalize` (rational reduction) and one `CReal` sum
  bound. Likewise the only three `Quot` hits in the whole index are
  `Complex.factorQuotient*`, which is synthetic division.

Their one genuine compliment, unchanged and now better supported: the `AlgS`
setoid spine is the right response to not having quotients, and building it
deliberately — with congruence as an explicit field rather than as an
afterthought — is more disciplined than most libraries manage. It is a
workaround, and it is a good one, and it is now carrying the whole subject.

## What they would say is missing

In dependency order.

- [x] **Quotient structures** — the gate on all of it. Decided by measurement
      (ADR-1595) and built: `AlgS.Hom.quotient`, with no `Quot` in the index.
- [x] **Homomorphisms as a first-class notion**, with kernels and images, and
      the isomorphism theorems. **[AUDIT] present as of 2026-09-04**; sixteen
      `AlgS.Hom.*` declarations at `1de0edfc6`, including `firstIso` and
      `firstIsoClassical`. **The second and third isomorphism theorems remain
      absent**, and both need a normal subgroup, which needs the join of the
      subgroup semilattice.
- [~] **Subobjects**: subgroups, subrings, ideals, submodules, and the lattice
      structure on them. Subgroups landed as a *meet*-semilattice (15
      theorems); join, subrings, ideals and submodules are all absent from the
      index.
- [ ] **Group actions**, orbits, stabilizers, the orbit-stabilizer theorem,
      Sylow. Zero matches for any of the four names.
- [x] **Polynomial rings as rings** — `AlgS.Poly.commRing`, all 23 fields, over
      an abstract `AlgS.CommRing` (ADR-1618). **Irreducibility, unique
      factorization and quotients by an irreducible are all absent**, and they
      are absent for the same reason as the whole ring shelf: there is no
      ideal.
- [~] **Linear algebra over an abstract field**: vector spaces, bases,
      dimension, linear maps, eigenvalues. `AlgS.Field`, `AlgS.VectorSpace`
      and `Rat.vectorSpaceS` exist; `dim` is deliberately **not** declared
      (zero matches), because its well-definedness is unproved. Linear maps
      and eigenvalues are not started.
- [ ] **Field extensions and Galois theory**, which is where the subject's
      landmark results are. Zero matches, and structurally blocked on ideals.

## The blocker — resolved 2026-09-04, and what replaced it

**Decided:
[ADR-1595](../research/09-decisions/adr-1595-quotients-stay-setoids-and-quot-sound-stays-out.md),
`Status: Proposed`: quotients stay setoids and `Quot.sound` stays out.** The
decision was made by building the theorem, not by weighing the arguments below,
and the arguments are kept because the ADR is reversible on evidence — a named
theorem shown unreachable over setoids reopens it. **Two days of building have
produced no such theorem**: `AlgS.Poly.commRing` cost zero setoid overhead,
`CatS.grp` cost one new proof for the whole category, and the classical
isomorphism theorem cost three membership proofs.

**The measurement that decided it.** Of `AlgS.Group`'s fifteen fields, exactly
**three** (`equivRefl`, `equivSymm`, `equivTrans`, one line each) were
discharged by hand that `Quot` plus `Eq` would have given free. The two
substantial congruence proofs do *not* disappear under `Quot.sound`; they
reappear as the well-definedness side conditions of `Quot.lift₂` and
`Quot.lift`. The five group laws are *cheaper* over setoids — one `fCongr`
application each, against a `Quot.ind` induction. **Net cost of not having the
axiom, on this theorem: three lines.**

**Two findings that settled it beyond the cost — one of which has since
expired.** First, `Quot.sound` is *five* footprint entries, not one:
`Kernel::axiom_footprint` filters the dependency closure to
`Axiom | Opaque | Quotient`, so anything routed through `Quot` names the whole
package. That still holds. Second, it was argued that `Quot.sound` would not
reach the classical statement anyway, because the image needs a subtype and
`Subtype` and `Sigma` were both absent. **That premise died the same evening**
(ADR-1613): both landed, the classical statement was proved over setoids the
next day, and the argument is now only history. The decision rests on the cost
measurement alone — which is the stronger of the two anyway.

The original arguments, preserved:

The case for adding it:

- It unlocks the entire subject above, which is a plurality of undergraduate
  and graduate mathematics.
- ℝ could become a genuine quotient rather than a setoid, removing the
  congruence obligation that every ℝ construction currently carries by hand
  and that required the whole `AlgS` spine to manage.
- Lean itself has it. Parity claims against Mathlib are weaker without it.
- It is one axiom, and it is the *conservative* one: `Quot.sound` alone does
  not give excluded middle or choice.

The case against:

- The headline metric is the empty axiom footprint. Measured at `1de0edfc6`,
  the whole kernel index carries **30 axioms and they are all `AxReal.*`** —
  the axiomatized-reals development that nothing on this shelf touches; the
  `Alg`, `AlgS` and `CatS` namespaces contain none. Adding a *used* axiom means
  every downstream footprint names it, and "axiom-free" becomes "axiom-free
  except one" — a real loss of a claim no competitor can currently match. (Correction,
  2026-09-06 evening: the per-fact footprint IS a structured top-level field,
  `axiom_footprint`, on every one of the 2,687 proved facts, and
  `validate-facts.py` gates on it; the chair's re-reading scanned it and found
  **2,584 of the 2,687 proved facts empty, all of them on the `kernel-lean`
  route** — the only route that can make the claim, since the validator rejects
  an empty footprint on the other five. Of the 103 remaining, 101 are on those
  five routes and 2 are named `kernel-lean` exceptions, so "all `kernel-lean`
  facts are axiom-free" is false by exactly two (ADR-1674). So "empty across all proved facts" is false as worded and
  checkable in one pass; the earlier sentence here said the opposite.)
- The setoid route demonstrably works. ℝ, ℂ, and the `AlgS` spine are proof
  that a large development can be carried without quotients, and that is
  itself a research result.
- Once admitted, its use is not confined; it will appear everywhere, and the
  discipline that produced the current footprint record does not come back.

A third option the reviewer would not think of but the library should: keep
`Quot.sound` out of the kernel and carry quotient constructions **over
setoids**, generalizing what ℝ already does. This was the Bishop-style answer,
it preserves the footprint, and it was expected to be more work per theorem.
It was tested on exactly the example named here, the first isomorphism theorem
over `AlgS.Group`, and it cost three lines. **This is the option that was
taken.**

**The blocker that replaced it is a different animal, and it is mathematics,
not plumbing.** Invariance of dimension does not hold over an arbitrary
constructive field. The Steinitz exchange step needs *some* coefficient apart
from zero; linear independence supplies only `¬(∀ i, c_i ~ 0)`, and
constructively that is weaker. Closing the gap is exactly
`AlgS.Field.IsTight`, which ℚ proves and `CReal` cannot from anything in the
tree (ADR-1627, ADR-1657). So the honest statement is

```text
AlgS.Field.IsTight F → IsVectorSpace F M smul →
  linearIndependent u m → spans w n → AlgS.Index.le m n
```

**and ℝ is not an instance of it.** That is a fact about the shelf, not a
budget note, and it is the most interesting thing on this page.

## Next five, in their priority order — the 2026-09-04 list

- [x] **1. Resolve the quotient question in an ADR.** *Done 2026-09-04, ADR-1595: setoid quotients.* Add `Quot.sound`, or
      commit to setoid quotients, or admit `Quot.sound` in a labelled second
      tier whose footprints are reported separately. Everything below depends
      on the answer and nothing should be built until it exists.
- [x] **2. The first isomorphism theorem over `AlgS.Group`.** *Done 2026-09-04, `AlgS.Hom.firstIso`; the classical form `AlgS.Hom.firstIsoClassical` 2026-09-05, both footprints empty.* Original framing:, by whichever
      route (1) selects. This is the empirical test: if it lands at acceptable
      cost over setoids, the whole subject is reachable without an axiom.
- [x] **3. Homomorphisms, kernels, images, and subgroups** — **[AUDIT] the
      homomorphism, kernel and image layer landed with item 2**; subgroups
      landed as a meet-semilattice 2026-09-04 (`ecbf403f0`), 15 theorems.
      Join is still absent. Original framing: Prerequisite for everything and useful
      even before quotients exist.
- [x] **4. Polynomial rings as a structure** — *done 2026-09-04, a full 23-field `AlgS.CommRing` (ADR-1618).*, with the existing ℚ and ℂ
      coefficient arithmetic as instances, then irreducibility and division.
      `Complex.factorQuotient` already proves the degree drop, so the concrete
      half is done. Irreducibility and division did **not** land, and ℚ[X] is
      still not a named prelude instance.
- [~] **5. Vector spaces over an abstract field, with bases and dimension** — *modules 2026-09-04; `AlgS.Field` with apartness, `AlgS.VectorSpace` and dimension at zero 2026-09-05; the index calculus and the exchange split 2026-09-06 (ADR-1657). General invariance of dimension still open, and it is a theorem about TIGHT fields.*,
      and the existing ℚ rank/nullity work as the first instance. Their view:
      the fastest way to convert a large body of concrete matrix theorems into
      general ones.

## Next five, re-ranked 2026-09-06

Four of the five above are closed, so here is the list this reviewer would
write today, in their own priority order.

- [ ] **1. An ideal, and `R/I`.** The whole ring half of the subject is behind
      this one definition, and the group half already proved the method works:
      a quotient ring is the same carrier under a coarser equivalence, and
      `AlgS.Hom.quotient` is the template. Nothing in the tree blocks it —
      there is simply no `Ideal`.
- [ ] **2. Finish invariance of dimension over a tight field.** Three sized
      pieces (ADR-1657): `linComb_smul`/`linComb_add`, the one-step exchange,
      and the outer induction in refutation form via
      `AlgS.Index.le_dichotomy`. Only then declare `dim`. This is the item
      whose *statement* is the research result — the theorem is about tight
      fields and ℝ is not one.
- [ ] **3. Normal subgroups, and the second and third isomorphism theorems.**
      Needs the join of the subgroup semilattice, which needs a word-closure
      inductive. This is the honest cost of having stopped at `inter`.
- [ ] **4. Group actions, orbits, stabilizers, orbit-stabilizer.** Zero
      declarations today, no stated obstruction, and it is the cheapest route
      to a theorem an algebraist would cite. It is also what would let the
      CAS's matrix-group work reach a kernel statement instead of staying
      `cas-internal`.
- [ ] **5. ℤ/n as a ring, and ℚ[X] as a named instance.** Two small
      completions that turn existing work into instances of the abstract
      shelf: `Nat.modAdd_isGroup` is only the additive group, and
      `AlgS.Poly.commRing` has no named ℚ/ℝ/ℂ instantiation in a prelude even
      though all three were verified in a test-local kernel.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: `Alg` and `AlgS` spines Magma→Field with ℕ/ℤ/ℚ/ℝ/ℂ instances; ~24 generic theorems, all elementary. No quotients, no homomorphisms, no ideals, no field extensions. `Quot.sound` absent from the kernel. | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Next Five items 1 and 2 both landed** (roadmap W0-1 and W2-8). ADR-1595 decides the quotient question by measurement: setoid quotients, `Quot.sound` stays out. `AlgS.Hom.*` adds 12 declarations including `firstIso`, all with empty footprint. The construction is that a quotient group is the same carrier under a coarser equivalence, so there is no carrier of classes and no `Quot`. Measured cost of not having the axiom on this theorem: three lines. Verdict revised. | `2a640c9b6`; `structures_setoid` 18 passed, `first_iso` 5 passed |
| 2026-09-04 | **Next Five items 4 and 5 landed in part, and item 3's residue closed** (roadmap W2-9, W3-2, W1-11): 58 declarations, footprint 0, one kernel rejection across all of them and that one a Rust-side universe slip. Polynomial rings over an abstract `AlgS.CommRing` with the additive group instance and distributivity (not yet a `CommRing` instance — three reindexing lemmas for the convolution walk, open concretely over ℚ too); modules with self and polynomial instances and a basis layer; subgroups as a meet-semilattice with the kernel proved a subgroup. **The finding this reviewer should weigh most**: the `Eq` route cannot state a polynomial ring at all, because commutativity of coefficient functions is an equality of two lambdas and needs `funext`, which `Quot.sound` would not supply. The complaint in this file that function spaces "cannot be given their standard structure" is retired — over setoids they can, and only over setoids. Two obstructions to vector spaces, neither about quotients: one universe level per record field kind, and `AlgS.Field` needing `Apart`. (ADR-1609.) | `ecbf403f0`; poly/module/subgroup 8+8+8 passed, `rat_prelude::` 273 |
| 2026-09-04 | **Item 4 completed** (roadmap W2-9, ADR-1618): `AlgS.Poly.commRing`, all 23 fields, twelve declarations admitted on first submission. The three reindexing lemmas ADR-1609 named were proved for the walk directly; the recommended `Nat.sub` restatement was tried and declined because no `sumRange` lemma in the tree is over an abstract carrier. `mulAssoc` needed no three-index exchange — the right motive made it a one-index induction. **Setoid cost: zero**, again. ℚ[X], ℝ[X], ℂ[X] instantiate. Still open and sized honestly: `Rat.polyEval_mul` (an 800-line port, not reachable from the abstract theorem) and the named prelude declarations for the three concrete rings. | `be87f45ca`; poly_setoid 17 passed, `rat_prelude::` 273, `complex::` 58 |
| 2026-09-05 | **The classical form of the first isomorphism theorem is now stated and proved** (roadmap W0-5, ADR-1613): `AlgS.Hom.imageGroup` is a group object over `Subtype H.carrier (image f)`, and `firstIsoClassical` is `G/ker f ≅ Im f` as three conjuncts about two group objects. Fourteen of the image group's fifteen fields are free because `Subtype.val` ι-reduces; the whole cost is three membership proofs. The subtype's equivalence is inherited from `H.equiv` on `val`, never `Eq`. So the reviewer's original objection is answered in both forms: the setoid form yesterday at three lines, the classical form today at three proofs. | `c0054fd3b` |
| 2026-09-05 | **Item 5, the field half** (roadmap W3-2, ADR-1627): `AlgS.Field` with apartness, `AlgS.VectorSpace`, instances at ℚ (setoid cost zero) and ℝ (two theorems), every declaration admitted first time, footprint 0. The inverse is an existential (`mulInvEx`), because `CReal.inv` takes its modulus as data and no `Prop` apartness witness survives large elimination — the Bishop definition, and nothing downstream needs the inverse as a term. Tightness is a predicate: ℚ has it, ℝ cannot from the tree, and `creal.rs`'s label of it as Markov's principle was the converse. `basis_zero_unique` needs no vector-space hypothesis at all. **Open**: general invariance of dimension, blocked on index surgery over a coefficient family (`Nat.lt`/`Nat.beq` undeclared at the `AlgS` build position). | `53c851e5b`; setoid spine 59, `rat_prelude::` 295, `creal::` 243 passed in the lane |
| 2026-09-06 | **Toward invariance of dimension** (roadmap W3-2, ADR-1657): the index calculus for removing and inserting a coordinate, with its defining equations by reduction, and the exchange lemma splitting a linear combination at any index; 17 axiom-free declarations. The theorem itself waits on tightness of the field: constructively, independence gives only that not every coefficient is zero, and the exchange step needs one coefficient apart from zero, so the statement will carry a tightness hypothesis that the rationals satisfy and the reals do not. | `a0ecf3fcf`; `vector_space` 25 passed in the lane |
| 2026-09-06 | **Re-measured against `main`, verdict moves.** Kernel index rebuilt from this commit (`--include-constructed`, 4,839 declarations across sixteen groups; 3,340 across eight without). Corrections: the "roughly two dozen" generic theorems is now **`Alg` 15 + `AlgS` 115 = 130**, over 193 + 407 declarations; `AlgS.Hom.*` is **16**, not 12; **zero declarations of quotient kind exist in the index at all**, which is stronger than "`Quot.sound` is absent"; the `Subtype`/`Sigma` half of ADR-1595's second finding expired the evening it was written (ADR-1613) and is now marked as history; `Rat.vectorSpaceS`, `Rat.fieldS_isTight`, `CatS.grp_isProduct` added to what exists. Absences re-verified in one dump of all 4,839 names with the 600 `Alg`/`AlgS` names as the same-invocation positive control: **zero** matches for `ideal`, `localiz`, `tensor`, `galois`, `extension`, `splitting`, `irreducib`, `orbit`, `stabiliz`, `sylow`, `action`, `Normal`, `secondIso`, `thirdIso`, `dim`, `representation`, `character`, `funext`. The CAS's matrix groups and character tables (`5a7355b2a`) register **no fact**, so under ADR-0601 they are `cas-internal` and count as zero here; ledger-wide the `cas-certificate` residue is 45 of 61. Ledger: 2,963 facts, 2,687 proved, 1,585 landmark; 28 facts whose title says "abstract", all proved. Kernel axioms: 30, all `AxReal.*`, none in `Alg`/`AlgS`/`CatS`. What this re-measure could NOT check mechanically: per-fact axiom footprints, which are recorded in evidence prose rather than as a structured field. Next Five items 1–4 closed, item 5 partial; a re-ranked list added, headed by an ideal. | `1de0edfc6`; `shape_search` rebuilt in-lane, `count-landmark-facts.py`, `check-cas-internal-residue.py` |
| 2026-09-06 | **The ideal, and R/I** (next-five item 1 of the 09-06 list, ADR-1676): `AlgS.Ideal.IsIdeal` as a predicate with the zero, unit and principal ideals as instances, and the quotient ring built as a setoid coarsening — 31 axiom-free declarations, plus nine generic commutative-ring lemmas the spine was missing. Measured: an ideal is one field more than an additive subgroup, and the quotient's ten ring laws are free because the coset relation is coarser than the ring's own equivalence; six congruence obligations are not. The ring form of the first isomorphism theorem did not land — the group form quantifies over `AlgS.Group`, four module-private helpers are hard-coded to five group binders where a ring homomorphism needs seven, and the image side needs its own ring. | `790553bef`; `ideal_setoid_tests` 11 passed |

## How to re-measure

```sh
# is Quot.sound still absent? (it is a kernel primitive question, not a grep)
grep -n 'enum QuotKind' -A8 crates/axeyum-lean-kernel/src/env.rs

# ...and does anything DECLARE a quotient? `--kind quot` reports UNANSWERABLE
# when the index carries none, which is the answer: zero.
cargo run --release -p axeyum-lean-kernel --example shape_search -- \
  --kind quot --limit 10

# the two spines, by size and by kind. `Alg` and `AlgS` are separate namespace
# roots, so `--ns Alg` does NOT include `AlgS`.
cargo run --release -p axeyum-lean-kernel --example shape_search -- \
  --list-namespaces --include-constructed
cargo run --release -p axeyum-lean-kernel --example shape_search -- \
  --ns Alg --limit 900
cargo run --release -p axeyum-lean-kernel --example shape_search -- \
  --name-contains 'AlgS.' --limit 500

# what does the spine prove generically?
python3 - <<'PY'
import json, glob
for f in glob.glob('artifacts/facts/*.json'):
    d = json.load(open(f)); t = d.get('title') or ''
    if 'abstract' in t.lower(): print(d.get('epistemic_status'), t[:90])
PY

# the CAS half is a producer, not a proof: how much of it reconstructs?
python3 scripts/check-cas-internal-residue.py
```

## Related

- [02-constructive-analysis.md](02-constructive-analysis.md) — the setoid
  workaround, working at scale
- [09-category-theory.md](09-category-theory.md) — the other reviewer who
  wants abstraction, and who now has `CatS.grp`
- [13-computer-algebra.md](13-computer-algebra.md) — the matrix groups and
  character tables that have no fact behind them yet
- [ADR-0512](../research/09-decisions/adr-0512-real-is-constructed-as-a-setoid-over-the-rationals.md)
  — why ℝ is a setoid, in the kernel's own words
- [ADR-1657](../research/09-decisions/adr-1657-the-surgery-recurses-on-the-index-and-the-fold-recurses-on-the-length.md)
  — why invariance of dimension is a theorem about tight fields
