# 04 — Algebra

Reviewer: an algebraist — groups, rings, fields, representation theory
Verdict, 2026-09-04 (revised, same day): **the blocker is decided and the first isomorphism theorem is proved — still a thin shelf, no longer a blocked one**
Last measured: 2026-09-04 at `1856cdb3c`

> "You have written down the axioms of a group and proved that inverses are
> unique. Come back when you can form G/N."
>
> **Revised the same day:** "You formed G/N without a quotient type, by keeping
> the carrier and coarsening the equivalence, and the first isomorphism theorem
> cost three lines more than it would have with `Quot.sound`. I withdraw the
> objection to the method. The shelf is still nearly empty."

> **AUDITED 2026-09-04.** Every absence claim in this file was re-checked
> against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for the evidence, and the
> corrections marked **[AUDIT]** below. Across the twelve files, 11 of 76
> absence claims were false and 12 more overstated the gap; the cause is that
> the ledger characterises only 38% of its proved facts and does not cover 430
> kernel theorems at all (ADR-1605).

## The persona

Works with quotients constantly and without thinking about it: quotient
groups, quotient rings, ideals, modules over a ring, field extensions,
representations. Their first move on any new structure is to find its
congruences and quotient by them. Judges a formalization by whether the
isomorphism theorems are stated, because everything after them assumes them.

## What the library has today

**A structure spine, two of them, instances, and — as of 2026-09-04 — quotients
that quotient, carried over setoids rather than over `Quot`.**

The `Alg` spine is an `Eq`-based record hierarchy at `Sort 2`:

```
Magma → Semigroup → Monoid → CommMonoid → Group → CommGroup
                          → Semiring → Ring → CommRing → Field
                                            → OrderedRing
```

with forgetful projections, and a parallel `AlgS` spine carrying an explicit
`equiv` field plus congruence obligations, for carriers where equality is not
syntactic. Instances: ℕ, ℤ, ℚ on the `Eq` side; `CReal.commRingS`,
`CReal.orderedRingS`, `CReal.addGroupS`, `Complex.commRingS` on the setoid
side. `Alg` is derivable from `AlgS` via `ofAlg`, never the reverse.

Theorems proved generically over the spine, roughly two dozen, including:

- in an abstract group: uniqueness of the identity, left cancellation, a left
  inverse equals a right inverse, double inversion
- in an abstract monoid: `npow` distributes over exponent addition
- in an abstract ring: `x·0 = 0`, `x·(−1) = −x`, `a − a = 0`
- in an abstract ordered ring: numeral monotonicity and distribution
- each of the above again over `AlgS`, up to equivalence
- the 1×1 determinant over an abstract commutative ring

**Added 2026-09-04 (roadmap W2-8, ADR-1595):** `AlgS.Hom.*`, twelve
declarations, empty footprint. `AlgS.Hom.quotient` builds the quotient of a
group by a homomorphism's kernel **with the same carrier and a coarser
equivalence** — `equiv := fun a b => H.equiv (f a) (f b)` — so there is no
carrier of equivalence classes and no `Quot` anywhere. `AlgS.Hom.firstIso`
then states the first isomorphism theorem: the quotient's equivalence is
exactly the kernel congruence, the induced map is a homomorphism out of it,
and it is onto the image. A negative control confirms the kernel-congruence
proof is load-bearing: substituting the source group's own `opCongr` is
rejected.

Concrete algebra that does exist, off the spine: linear algebra over ℚ
(`rowEchelon`, `isEchelon`, `rank`, `nullity`, determinants, Cramer's rule,
matrix row operations) and polynomial arithmetic over ℚ and ℂ (`polyEval`,
`polyAdd`, `polyMul`, `polyScale`, degree bounds, `hornerFromTop`, and
`factorQuotient` — division by a linear factor with the degree drop proved).

## Their verdict

The spine is a competent record hierarchy and the theorems on it are the
first ten minutes of a first course. Every one of them — inverses unique,
cancellation, `x·0 = 0` — is a warm-up exercise. Nothing in the file is a
theorem an algebraist would cite.

The reason was not laziness, and the reviewer identified it immediately:
**there were no quotients.** The kernel admits Lean's quotient package —
`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` — but **not `Quot.sound`**, the rule
that says related representatives become equal. You can form the type and lift
a function; you cannot prove `Quot.mk a = Quot.mk b` from `a ~ b`. A quotient
you cannot compute equalities in is not a quotient.

**That objection was answered on 2026-09-04, and not the way the reviewer
expected.** The route is not to add the axiom but to stop asking for a carrier
of classes: a quotient group is *the same carrier under a coarser
equivalence*, which the `AlgS` spine can express because it carries `equiv` as
a field. The first isomorphism theorem follows, with an empty footprint. The
reviewer's revised position is at the top of this file. What remains true is
the second half of their complaint — the shelf above the isomorphism theorem is
still nearly empty:

- G/N, and with it the three isomorphism theorems
- R/I, ideals, prime and maximal ideals, quotient fields
- ℤ/n as a ring (the library uses an explicit `ModEq` relation instead, which
  works and does not generalize)
- localization, tensor products, quotient modules
- field extensions, splitting fields, Galois theory
- representation theory, which needs modules over a group ring

The reviewer would also note the second consequence: **no `funext`.** Two
functions that agree pointwise are not equal, so function spaces, module
homomorphism sets, endomorphism rings, and anything whose elements are maps
cannot be given their standard structure.

Their one genuine compliment: the `AlgS` setoid spine is the right response to
not having quotients, and building it deliberately — with congruence as an
explicit field rather than as an afterthought — is more disciplined than most
libraries manage. It is a workaround, and it is a good one.

## What they would say is missing

Everything. In dependency order:

- **Quotient structures** — the gate on all of it.
- ~~**Homomorphisms as a first-class notion**, with kernels and images, and the
  isomorphism theorems.~~ **[AUDIT] present as of 2026-09-04**: twelve
  `AlgS.Hom.*` declarations including `firstIso` (audit row A9). The second
  and third isomorphism theorems remain absent.
- **Subobjects**: subgroups, subrings, ideals, submodules, and the lattice
  structure on them.
- **Group actions**, orbits, stabilizers, the orbit-stabilizer theorem,
  Sylow.
- **Polynomial rings as rings**, rather than the concrete coefficient-list
  arithmetic that exists over ℚ and ℂ; then irreducibility, unique
  factorization, and quotients by an irreducible.
- **Linear algebra over an abstract field**: vector spaces, bases, dimension,
  linear maps, eigenvalues. The ℚ matrix work is concrete and does not
  generalize.
- **Field extensions and Galois theory**, which is where the subject's
  landmark results are.

## The blocker — resolved 2026-09-04

**Decided:
[ADR-1595](../research/09-decisions/adr-1595-quotients-stay-setoids-and-quot-sound-stays-out.md),
`Status: Proposed`: quotients stay setoids and `Quot.sound` stays out.** The
decision was made by building the theorem, not by weighing the arguments below,
and the arguments are kept because the ADR is reversible on evidence — a named
theorem shown unreachable over setoids reopens it.

**The measurement that decided it.** Of `AlgS.Group`'s fifteen fields, exactly
**three** (`equivRefl`, `equivSymm`, `equivTrans`, one line each) were
discharged by hand that `Quot` plus `Eq` would have given free. The two
substantial congruence proofs do *not* disappear under `Quot.sound`; they
reappear as the well-definedness side conditions of `Quot.lift₂` and
`Quot.lift`. The five group laws are *cheaper* over setoids — one `fCongr`
application each, against a `Quot.ind` induction. **Net cost of not having the
axiom, on this theorem: three lines.**

**Two findings that settled it beyond the cost.** First, `Quot.sound` is *five*
footprint entries, not one: `Kernel::axiom_footprint` filters the dependency
closure to `Axiom | Opaque | Quotient`, so anything routed through `Quot` names
the whole package. Second, it would not reach the classical statement anyway —
"`G/ker f ≅ Im f` as two group objects" needs a subtype for the image, and
`Subtype` and `Sigma` are both absent from the kernel, while the setoid route
has no such gap because the quotient *is* the image.

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

- The headline metric is that the axiom footprint is empty across 2,487
  proved facts. Adding a used axiom means every downstream footprint names
  it, and "axiom-free" becomes "axiom-free except one" — a real loss of a
  claim no competitor can currently match.
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

## Next five, in their priority order

- [x] **1. Resolve the quotient question in an ADR.** *Done 2026-09-04, ADR-1595: setoid quotients.* Add `Quot.sound`, or
      commit to setoid quotients, or admit `Quot.sound` in a labelled second
      tier whose footprints are reported separately. Everything below depends
      on the answer and nothing should be built until it exists.
- [x] **2. The first isomorphism theorem over `AlgS.Group`.** *Done 2026-09-04, `AlgS.Hom.firstIso`, footprint empty.* Original framing:, by whichever
      route (1) selects. This is the empirical test: if it lands at acceptable
      cost over setoids, the whole subject is reachable without an axiom.
- [x] **3. Homomorphisms, kernels, images, and subgroups** — **[AUDIT] the
      homomorphism, kernel and image layer landed with item 2**; subgroups as
      a lattice remain absent. Original framing: Prerequisite for everything and useful
      even before quotients exist.
- [x] **4. Polynomial rings as a structure** — *done 2026-09-04, a full `CommRing` instance.*, with the existing ℚ and ℂ
      coefficient arithmetic as instances, then irreducibility and division.
      `Complex.factorQuotient` already proves the degree drop, so the concrete
      half is done.
- [~] **5. Vector spaces over an abstract field, with bases and dimension** — *modules and a basis layer landed 2026-09-04; vector spaces blocked on a field record, which needs `Apart`.*,
      and the existing ℚ rank/nullity work as the first instance. Their view:
      the fastest way to convert a large body of concrete matrix theorems into
      general ones.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: `Alg` and `AlgS` spines Magma→Field with ℕ/ℤ/ℚ/ℝ/ℂ instances; ~24 generic theorems, all elementary. No quotients, no homomorphisms, no ideals, no field extensions. `Quot.sound` absent from the kernel. | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Next Five items 1 and 2 both landed** (roadmap W0-1 and W2-8). ADR-1595 decides the quotient question by measurement: setoid quotients, `Quot.sound` stays out. `AlgS.Hom.*` adds 12 declarations including `firstIso`, all with empty footprint. The construction is that a quotient group is the same carrier under a coarser equivalence, so there is no carrier of classes and no `Quot`. Measured cost of not having the axiom on this theorem: three lines. Verdict revised. | `2a640c9b6`; `structures_setoid` 18 passed, `first_iso` 5 passed |
| 2026-09-04 | **Next Five items 4 and 5 landed in part, and item 3's residue closed** (roadmap W2-9, W3-2, W1-11): 58 declarations, footprint 0, one kernel rejection across all of them and that one a Rust-side universe slip. Polynomial rings over an abstract `AlgS.CommRing` with the additive group instance and distributivity (not yet a `CommRing` instance — three reindexing lemmas for the convolution walk, open concretely over ℚ too); modules with self and polynomial instances and a basis layer; subgroups as a meet-semilattice with the kernel proved a subgroup. **The finding this reviewer should weigh most**: the `Eq` route cannot state a polynomial ring at all, because commutativity of coefficient functions is an equality of two lambdas and needs `funext`, which `Quot.sound` would not supply. The complaint in this file that function spaces "cannot be given their standard structure" is retired — over setoids they can, and only over setoids. Two obstructions to vector spaces, neither about quotients: one universe level per record field kind, and `AlgS.Field` needing `Apart`. (ADR-1609.) | `ecbf403f0`; poly/module/subgroup 8+8+8 passed, `rat_prelude::` 273 |
| 2026-09-04 | **Item 4 completed** (roadmap W2-9, ADR-1618): `AlgS.Poly.commRing`, all 23 fields, twelve declarations admitted on first submission. The three reindexing lemmas ADR-1609 named were proved for the walk directly; the recommended `Nat.sub` restatement was tried and declined because no `sumRange` lemma in the tree is over an abstract carrier. `mulAssoc` needed no three-index exchange — the right motive made it a one-index induction. **Setoid cost: zero**, again. ℚ[X], ℝ[X], ℂ[X] instantiate. Still open and sized honestly: `Rat.polyEval_mul` (an 800-line port, not reachable from the abstract theorem) and the named prelude declarations for the three concrete rings. | `be87f45ca`; poly_setoid 17 passed, `rat_prelude::` 273, `complex::` 58 |
| 2026-09-05 | **The classical form of the first isomorphism theorem is now stated and proved** (roadmap W0-5, ADR-1613): `AlgS.Hom.imageGroup` is a group object over `Subtype H.carrier (image f)`, and `firstIsoClassical` is `G/ker f ≅ Im f` as three conjuncts about two group objects. Fourteen of the image group's fifteen fields are free because `Subtype.val` ι-reduces; the whole cost is three membership proofs. The subtype's equivalence is inherited from `H.equiv` on `val`, never `Eq`. So the reviewer's original objection is answered in both forms: the setoid form yesterday at three lines, the classical form today at three proofs. | `c0054fd3b` |

## How to re-measure

```sh
# is Quot.sound still absent? (it is a kernel primitive question, not a grep)
grep -n 'enum QuotKind' -A8 crates/axeyum-lean-kernel/src/env.rs

# what does the spine prove generically?
python3 - <<'PY'
import json, glob
for f in glob.glob('artifacts/facts/*.json'):
    d = json.load(open(f)); t = d.get('title') or ''
    if 'abstract' in t.lower(): print(d.get('epistemic_status'), t[:90])
PY
```

## Related

- [02-constructive-analysis.md](02-constructive-analysis.md) — the setoid
  workaround, working at scale
- [09-category-theory.md](09-category-theory.md) — the other reviewer who
  wants abstraction
- [ADR-0512](../research/09-decisions/adr-0512-real-is-constructed-as-a-setoid-over-the-rationals.md)
  — why ℝ is a setoid, in the kernel's own words
