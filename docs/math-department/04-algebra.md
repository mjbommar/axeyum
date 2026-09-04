# 04 — Algebra

Reviewer: an algebraist — groups, rings, fields, representation theory
Verdict, 2026-09-04: **dismissive, and correctly so**
Last measured: 2026-09-04 at `1856cdb3c`

> "You have written down the axioms of a group and proved that inverses are
> unique. Come back when you can form G/N."

## The persona

Works with quotients constantly and without thinking about it: quotient
groups, quotient rings, ideals, modules over a ring, field extensions,
representations. Their first move on any new structure is to find its
congruences and quotient by them. Judges a formalization by whether the
isomorphism theorems are stated, because everything after them assumes them.

## What the library has today

**A structure spine, two of them, and instances. No quotients that quotient.**

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

The reason is not laziness and the reviewer would identify it immediately.
**There are no quotients.** Not "no quotient groups yet": the construction is
unavailable. The kernel admits Lean's quotient package — `Quot`, `Quot.mk`,
`Quot.lift`, `Quot.ind` — but **not `Quot.sound`**, the rule that says related
representatives become equal. You can form the type and lift a function; you
cannot prove `Quot.mk a = Quot.mk b` from `a ~ b`. A quotient you cannot
compute equalities in is not a quotient.

Everything an algebraist does next therefore does not start:

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
- **Homomorphisms as a first-class notion**, with kernels and images, and the
  isomorphism theorems.
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

## The blocker

**`Quot.sound`, and it is the largest open decision in the library.**

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
setoids**, generalizing what ℝ already does — a `Setoid` carrier with
congruence-respecting maps, and the isomorphism theorems stated up to the
equivalence. This is the Bishop-style answer, it preserves the footprint, and
it is more work per theorem. Whether the algebra shelf can be built this way
at reasonable cost is an empirical question nobody has tested, and testing it
on one nontrivial example — the first isomorphism theorem over `AlgS.Group` —
would settle a lot.

## Next five, in their priority order

- [ ] **1. Resolve the quotient question in an ADR.** Add `Quot.sound`, or
      commit to setoid quotients, or admit `Quot.sound` in a labelled second
      tier whose footprints are reported separately. Everything below depends
      on the answer and nothing should be built until it exists.
- [ ] **2. The first isomorphism theorem over `AlgS.Group`**, by whichever
      route (1) selects. This is the empirical test: if it lands at acceptable
      cost over setoids, the whole subject is reachable without an axiom.
- [ ] **3. Homomorphisms, kernels, images, and subgroups** as a reusable
      layer over the existing spine. Prerequisite for everything and useful
      even before quotients exist.
- [ ] **4. Polynomial rings as a structure**, with the existing ℚ and ℂ
      coefficient arithmetic as instances, then irreducibility and division.
      `Complex.factorQuotient` already proves the degree drop, so the concrete
      half is done.
- [ ] **5. Vector spaces over an abstract field, with bases and dimension**,
      and the existing ℚ rank/nullity work as the first instance. Their view:
      the fastest way to convert a large body of concrete matrix theorems into
      general ones.

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: `Alg` and `AlgS` spines Magma→Field with ℕ/ℤ/ℚ/ℝ/ℂ instances; ~24 generic theorems, all elementary. No quotients, no homomorphisms, no ideals, no field extensions. `Quot.sound` absent from the kernel. | ledger snapshot at `1856cdb3c` |

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
