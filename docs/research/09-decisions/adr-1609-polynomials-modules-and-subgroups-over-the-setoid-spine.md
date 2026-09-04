# ADR-1609: polynomial rings, modules and subgroups over the setoid spine

Status: proposed
Date: 2026-09-04
Lane: `algebra-structures`
Roadmap: W2-9 (polynomial rings as a structure), W3-2 (vector spaces over an
abstract field), W1-11 (subobjects — the half `AlgS.Hom.*` did not cover)

Index-summary: the three algebra shelves ADR-1595 unblocked were built, and
they landed: **58 declarations across `AlgS.Poly.*` (15), `AlgS.Module.*`
(23) and `AlgS.Subgroup.*` (20), every one with an empty
`Kernel::axiom_footprint`, at a total cost of ONE kernel rejection** — and
that rejection was a Rust-side `Nat.rec` universe slip, not a mathematical
obstruction. The measured setoid tax is **one field per structure**
(`AlgS.Module.smulCongrP`, `AlgS.Subgroup.IsSub`'s `respects`; the polynomial
ring's three `equiv*` fields are one line each), and each is discharged in one
application at every instance. **The finding that changes ADR-1595's balance
runs the other way**: the polynomial ring is not merely cheaper over setoids,
it is *unreachable* over the `Eq` spine, because its carrier is a function
space and `Alg.CommGroup`'s law fields would be equalities of lambdas —
`funext`, which the kernel does not have and `Quot.sound` would not supply.
Three obstructions were hit and all three are `Quot`-independent: no record
can hold another record (`FieldSpec` fixes one universe per `FieldKind`), so a
module is a `Prop` and not a record; `AlgS.Field` does not exist (it needs
`Apart`), which is the gate between modules and *dimension*; and convolution's
`mulAssoc`/`mulComm`/`mulOne` need reindexing lemmas that are equally missing
in the concrete `ℚ` development. **No evidence to reopen ADR-1595.**
Index-status: proposed

## Context

[ADR-1595](adr-1595-quotients-stay-setoids-and-quot-sound-stays-out.md) decided
that quotients are carried as setoids and `Quot.sound` stays out, and it
measured the cost of that decision on exactly one theorem — the first
isomorphism theorem over `AlgS.Group` — at three lines. It closed with a
standing invitation:

> **This decision is reversible and should be re-opened on evidence**, not on
> preference: the trigger is a *named, attempted* theorem shown to be
> unreachable over setoids, with the obstruction stated as a specific
> obligation the kernel could not discharge.

Its own downstream table named three items as "proceed":

| roadmap item | ADR-1595's expectation |
|---|---|
| **W2-9** polynomial rings as a structure | proceed over `AlgS.CommRing`; coefficient equality is the ring's `equiv`, and `AlgS.Hom.*` is the template |
| **W3-2** vector spaces, bases, dimension | proceed; needs W2-9 and an `AlgS.Field` (which needs `Apart` — a *separate* open question) |
| **W1-11** subgroups as a lattice | the residue of the item whose homomorphism/kernel/image half landed with `AlgS.Hom.*` |

This ADR is the report from building all three. It records the designs, the
setoid cost at each step (which is the running evidence for or against
ADR-1595), what landed, and where it stopped.

## What was built

Three new modules under `crates/axeyum-lean-kernel/src/nat_prelude/`, declared
at the **`AlgS` build position** inside `build_nat_prelude_uncached` — where
only `LogicPrelude` exists, so `Nat`, `Nat.zero`, `Nat.succ` and `Nat.rec` are
available and `Nat.add`, `Nat.sub` and `Nat.lt` are **not**. That constraint
shaped two designs and is called out below where it did.

### `polynomial_setoid.rs` — `AlgS.Poly.*`, 15 declarations (W2-9)

A polynomial over `R` is a **coefficient function** `Nat -> R.carrier`, the
representation `Rat.polyEval` already uses over `ℚ` (`rat_prelude/polynomial.rs`:
"this kernel has no `List` and no tuple type"), lifted to an abstract carrier.

| name | kind | what it is |
|---|---|---|
| `AlgS.add_add_add_comm` | theorem | the middle-four exchange `(a+b)+(c+d) ~ (a+c)+(b+d)` |
| `AlgS.Poly.equiv` | definition | `fun p q => forall n, R.equiv (p n) (q n)` |
| `AlgS.Poly.add` / `zero` / `neg` / `one` / `smul` | definitions | pointwise, plus `1` as `R.one` at index 0 |
| **`AlgS.Poly.commGroup`** | definition | **the additive group of `R[X]`, a full 16-field `AlgS.CommGroup`** |
| `AlgS.Poly.antidiagFrom` | definition | the antidiagonal walk |
| `AlgS.Poly.mul` | definition | convolution |
| `AlgS.Poly.antidiagFrom_congr` / `antidiagFrom_add` | theorems | the walk respects `equiv`, and is additive |
| `AlgS.Poly.mulCongr` / `distribL` / `distribR` | theorems | three more `AlgS.CommRing` fields of `R[X]` |

**The build position forced the convolution's shape.** `Nat.sub` does not
exist yet, so the textbook `Σ_{i≤n} p i · q (n−i)` cannot be written. Instead
`antidiagFrom` walks the antidiagonal with the two indices moving *in step*:

```text
antidiagFrom g zero     j ≡ g zero j
antidiagFrom g (succ i) j ≡ R.add (g (succ i) j) (antidiagFrom g i (succ j))
```

so `antidiagFrom g n 0 = g n 0 + (g (n−1) 1 + (… + g 0 n))`, and
`AlgS.Poly.mul R p q n` is that walk at `g i j := R.mul (p i) (q j)`. This
needs no arithmetic at all. It is a better shape than the subtraction form for
the two lemmas that were proved on it, because the induction hypothesis is
available at *every* second index (the motive is `fun i => forall j, …`),
which is exactly what the walk's successor step consumes.

### `module_setoid.rs` — `AlgS.Module.*`, 23 declarations (W3-2)

A module is carried the way `AlgS.Hom.*` carries a homomorphism: data as
explicit arguments, axioms as a `Prop`.
`AlgS.Module.IsModule R M smul` is a five-fold `And` over `smulCongrP`,
`smulAddP`, `addSmulP`, `mulSmulP` and `oneSmulP`, with five accessor
theorems. Beyond that: `AlgS.idem_eq_e` (a new `AlgS.Group` lemma: `x ~ x·x`
forces `x ~ e`), the three generic theorems `smul_zero`, `zero_smul`,
`neg_smul`, the two instances below, and a basis layer (`linComb`,
`coeffAgree`, `spans`, `linearIndependent`, `isBasis`, `linComb_congr`).

**The two instances are the payoff, and they are nearly free:**

| instance | the five axioms are… |
|---|---|
| `AlgS.Module.selfModule` — `R` over itself | one SELECTOR each: `mulCongr`, `distribL`, `distribR`, `mulAssoc`, `mulOneL` |
| `AlgS.Module.polyModule` — `R[X]` over `R` | one APPLICATION each of `R`'s corresponding field at the coefficient index |

`coeffAgree` is a structural recursion (`True` at zero, one `And` per index
after) rather than `forall i, i < n -> …`, again because `Nat.lt` is not
declared yet at this build position.

### `subgroup_setoid.rs` — `AlgS.Subgroup.*`, 20 declarations (W1-11)

A subgroup is a **predicate** `S : G.carrier -> Prop` with closure conditions —
this kernel has no `Subtype` and no `Sigma` (verified ABSENT by ADR-1595), so
it cannot be a carrier, and this is the shape `AlgS.Hom.ker`/`image` already
use. `IsSub` bundles four conjuncts; `le`/`inter`/`top`/`bot` give the order,
the meet and the two bounds; `le_refl`, `le_trans`,
`inter_le_left`/`inter_le_right`/`le_inter`, `le_top`, `bot_le` give the
bounded meet-semilattice; `inter_isSub`, `top_isSub`, `bot_isSub` close `IsSub`
under all three constructions; and **`ker_isSub`** — the kernel of a
homomorphism is a subgroup — joins this half of W1-11 to the half that landed
with `AlgS.Hom.firstIso`.

`bot G := fun a => G.equiv a G.e` is **the equivalence class of the identity,
not the singleton**. That is forced: a subgroup must be closed under
`G.equiv`, and `fun a => Eq a G.e` is not, over a carrier whose equality is a
defined relation.

## The measurement — setoid cost, construction by construction

This is the section ADR-1595 asked for. Each row states what the setoid
presentation *adds* relative to an `Eq`-flavored one, whether `Quot.sound`
would remove it, and what it actually cost.

### 1. `AlgS.Poly.commGroup` — the additive group of `R[X]`

| # | field | supplied by | free under `Eq`? |
|---|---|---|---|
| 0 | `carrier` | `Nat -> R.carrier` | free either way |
| 1 | `equiv` | `AlgS.Poly.equiv R` | the `Eq` spine has no such field |
| 2–4 | `equivRefl` / `Symm` / `Trans` | `fun p n => R.equivRefl (p n)`, and the two analogues | **YES** — 3 one-liners |
| 5 | `op` | `AlgS.Poly.add R` | free either way |
| 6 | `opCongr` | one `R.addCongr` at the index | **YES** (`congrArg`) |
| 7–9 | `e`, `inv`, `invCongr` | `Poly.zero`, `Poly.neg`, one `R.negCongr` | `invCongr` free under `Eq` |
| 10 | `assoc` | one `R.addAssoc` at the index | not free either way |
| 11 | `identL` | `equivTrans (addComm …) (addZero …)` — 2 steps | not free; `AlgS.CommRing` is right-sided only |
| 12 | `identR` | one `R.addZero` | not free |
| 13 | `invL` | 2 steps, same reason as `identL` | not free |
| 14 | `invR` | one `R.negAdd` | not free |
| 15 | `comm` | one `R.addComm` | not free |

Naive reading: **five obligations** (`equivRefl`, `equivSymm`, `equivTrans`,
`opCongr`, `invCongr`) that an `Eq`-flavored spine gets free, each one line.

**That reading is wrong, and this is the finding.** The `Eq` route does not
pay five lines here; it *cannot state the structure at all*. `Alg.CommGroup`'s
law fields are literal `Eq (op a b) (op b a)`, so `Alg`'s `comm` field for
polynomials would be

```text
Eq (fun n => R.add (p n) (q n)) (fun n => R.add (q n) (p n))
```

— an equality of two lambdas, provable only from **function extensionality**,
which this kernel does not have. `Quot.sound` does not supply `funext`
(ADR-1595 records this explicitly for the category-theory reviewer's separate
request). So for any structure whose carrier is a **function space** —
polynomials, power series, coordinate spaces, module homomorphism sets,
endomorphism rings — the setoid spine is not a cheaper route, it is the only
route the kernel has.

`04-algebra.md`'s own verdict already names this as a consequence of not
having `funext` ("function spaces … cannot be given their standard
structure"). It is no longer true of the `AlgS` spine.

### 2. `AlgS.Module.IsModule` — one extra conjunct

| conjunct | free under `Eq`? |
|---|---|
| `smulCongrP` — `a ~ a' -> v ~ v' -> a•v ~ a'•v'` | **YES** (`congrArg`/`Eq.subst`) |
| `smulAddP`, `addSmulP`, `mulSmulP`, `oneSmulP` | no — these are the module axioms |

**Cost: one conjunct.** And it is one application at every instance —
`R.mulCongr` for `selfModule`, `fun a a' p p' ha hp n => R.mulCongr … (hp n)`
for `polyModule`. It is also not dead weight: `linComb_congr`'s successor step
consumes it, and any statement about a linear combination built from
equivalent coefficients needs it.

### 3. `AlgS.Subgroup.IsSub` — one extra conjunct

| conjunct | free under `Eq`? |
|---|---|
| `forall a b, G.equiv a b -> S a -> S b` | **YES** (`Eq.subst`) |
| `S G.e`, `closedOp`, `closedInv` | no |

**Cost: one conjunct**, and it is load-bearing rather than bureaucratic:
`bot_le` (the trivial subgroup sits inside every subgroup) is *exactly* a
transport along `G.equiv`, because `bot` is the identity's equivalence class.
A test refuses `bot_le`'s proof term against the statement with the `IsSub`
hypothesis removed, and a second test refuses `IsSub` as definitionally equal
to the three-conjunct `Eq`-flavored form. Both are read from the kernel.

### 4. The aggregate

| measure | value |
|---|---|
| declarations added | **58** (11 definitions, 47 theorems), across three namespaces |
| axiom footprint | **empty on all 58**, read from `Kernel::axiom_footprint` |
| kernel rejections during the build | **1** |
| what that rejection was | `AlgS.Module.coeffAgree` passed `Nat.rec` at level 0; the recursion returns a `Prop`-VALUED object, so the motive is `fun _ => Prop` whose codomain is `Sort 1`. A Rust-side level slip, surfacing as `TypeMismatch { expected: Sort 0 }` |
| tests added | 21 (7 per module), all reading `add_declaration`'s verdict, `axiom_footprint`, or `def_eq` |
| rejection controls | 7, each with a positive twin in the same test |
| `structures_setoid` suite | 18 passed, unchanged |
| `first_iso` suite | 5 passed, unchanged |

**One rejection across 58 declarations** is the number to compare against
ADR-1595's "three lines". The setoid discipline did not slow this work down in
any measurable way; the things that did slow it down were the build position
(no `Nat` arithmetic) and one universe-level mistake in Rust.

## Where each shelf stopped, and why

Every obstruction below was **hit**, not anticipated, and every one is
independent of `Quot.sound`.

### `AlgS.Poly` is not an `AlgS.CommRing` instance

Twenty of the record's 23 fields are supplied. The missing ones are
`mulOneL`/`mulOneR`, `mulComm` and `mulAssoc`, and each needs a *reindexing*
lemma for `antidiagFrom`:

| field | the missing lemma | size |
|---|---|---|
| `mulOneL` / `mulOneR` | a vanishing-tail collapse: if `g i j ~ R.zero` for every `i` above the head, the walk collapses to its last cell. Needs a shift lemma (`antidiagFrom g n (succ j) ~ antidiagFrom (fun i j => g i (succ j)) n j`) because the index `j + n` cannot be written without `Nat.add` | ~2 induction lemmas |
| `mulComm` | the reversal `antidiagFrom g n 0 ~ antidiagFrom (fun i j => g j i) n 0` | 1 induction with a generalized statement |
| `mulAssoc` | the two-dimensional exchange for a triple convolution | the hard one |

None of these is made harder by the setoid discipline: they are statements
about a `Nat`-indexed fold and would read identically with `Eq`. **They are
also open concretely**: `rat_prelude/diagonal.rs` exists to build exactly this
machinery over `ℚ` and `Rat.polyEval_mul` still does not exist, for the same
reason (its own module doc: "the corner does not simplify to a `polyEval`").
`Quot.sound` supplies none of them.

**Recommended next step**: move `AlgS.Poly` to a build position after `Nat`
arithmetic (or declare `Nat.add`/`Nat.sub` earlier), restate `antidiagFrom` as
`sumRange (fun i => g i (n − i)) (succ n)`, and reuse the `ℚ` reindexing
proofs' shape. That is a bigger, cleaner slice than pushing the walk form.

### `AlgS.Module` is a `Prop`, not a record — a universe obstruction

A record holding the triple `(R : AlgS.CommRing, M : AlgS.CommGroup, smul)`
cannot be built with `nat_prelude::structures::declare_record`. The reason is
neither quotients nor `funext`:

- `declare_record` admits a **parameterless** inductive at `Sort 2` whose
  constructor fields are `FieldKind::CarrierSort` (`Sort 1`),
  `FieldKind::Data` (`Sort 1`) or `FieldKind::Law` (`Sort 0`) — **one fixed
  level per kind**.
- A `ring : AlgS.CommRing` field lives in `Sort 2`, which pushes the record to
  `Sort 3`.
- Shifting every level up wholesale (passing `(l0, l2, l3)`) does not work:
  the module's own carrier would land at `Sort 2`, where `Nat -> R.carrier`
  (a `Sort 1`) can no longer sit, because this kernel's `Sort` hierarchy is
  **not cumulative**.

**Sizing the fix**: add a per-field universe to `FieldSpec` (a fourth
`FieldKind`, or a level on the existing ones), and give `declare_record` a
`Sort 3` path — its ADR-1578 universe control currently asserts that the same
field list is *refused* at `Sort 1`, which for a `Sort 3` record must become a
refusal at `Sort 2`. That is a change to the shared `Alg` machinery
(`structures.rs`), which every lane's prelude build goes through, so it wants
its own lane and its own mutation control. Until then, the `AlgS.Hom.*`
presentation — data as explicit arguments, axioms as a `Prop` — is the right
shape, and it is the shape ADR-1595 already validated.

An alternative that needs no `structures.rs` change: `add_inductive` accepts
`num_params`, and a *parameter* does not raise an inductive's universe in
Lean's rule, so `AlgS.Module : AlgS.CommRing -> Sort 2` with the module's own
16 abelian-group fields inlined would fit — at the cost of a bespoke
`declare_record`-equivalent (constructor plus ~22 recursor-built selectors) in
this file. Not obviously better than the `Prop`; recorded so it is not
re-derived.

### Dimension needs `AlgS.Field`, which needs `Apart`

`isBasis` is stated and `linComb_congr` proves the easy half of independence,
but **invariance of basis number** — the theorem that makes "dimension"
well-defined — needs to divide, i.e. a field. `AlgS.Field` does not exist:
ADR-1588 stopped short of `Field` because a constructive field needs an
apartness relation (`x # 0` rather than `¬ (x = 0)`), and ADR-1595 recorded
that as a **separate open question**, not part of the quotient decision.

So W3-2's honest status is: **modules over an abstract commutative ring,
landed; vector spaces, blocked on a field record; dimension, blocked on that
plus a real theorem.** The `ℚ` bridge (`rowEchelon`, `rank`, `nullity`,
Cramer) is *not* blocked by the same thing — see the next section.

### The `ℚ` bridge, sized

`AlgS.Module.polyModule` gives `Nat -> R.carrier` as an `R`-module, and ℚ's
matrices are already `Nat -> Nat -> Rat` (`Rat.Mat`), so the coordinate space
matches the existing representation exactly. What is missing to connect
`Rat.rank`/`Rat.nullity` to `AlgS.Module.linearIndependent`:

1. an `AlgS.CommRing` value for `ℚ` — free, via
   `AlgS.CommRing.ofAlg Rat.commRing`, so the module instance is immediate;
2. agreement lemmas between `Rat.sumRange`-based linear algebra and
   `AlgS.Module.linComb` (the two folds have the same convention — exclusive
   bound, new term on the right — so these should be `Eq.refl`-adjacent);
3. the actual content: `rank + nullity = n` restated as a statement about
   `spans`/`linearIndependent`, which needs `rowEchelon_isEchelon`
   (ADR-1554 obligation 4, still open) before it means anything.

Item 3 is the real cost and it is a `ℚ`-side obligation that predates this
lane. **Do not price the bridge as small until (3) is closed.**

### The subgroup JOIN

`inter` is the meet and `IsSub` is closed under it; the **join** — the
subgroup generated by a union — is absent, because it needs a word closure,
i.e. an inductive family over `G.carrier` (`Generated : (G.carrier -> Prop) ->
G.carrier -> Prop` with constructors for membership, the identity, products
and inverses). That is a parameterized inductive, which `add_inductive`
supports; it was not attempted here. Sizing: one inductive plus a recursor-based
minimality theorem, so a small lane. It is also the first place a
**normal** subgroup and the quotient-by-a-subgroup would become statable, at
which point `AlgS.Hom.quotient` generalizes from "quotient by a kernel" to
"quotient by a normal subgroup" — the natural W2-8 follow-on.

## Decision

1. **Adopt the three designs above**: polynomials as coefficient functions with
   pointwise `equiv`; modules as explicit data plus an `IsModule` `Prop`;
   subgroups as closure predicates ordered by implication.
2. **ADR-1595 is not reopened.** No obligation in this work was blocked by the
   absence of `Quot.sound`, and one — the polynomial ring's additive
   structure — is reachable *only* because the spine carries `equiv` as a
   field. The evidence moves in ADR-1595's favour, not against it.
3. **`AlgS.Poly` stays a partial ring for now**, with the three missing fields
   recorded above as reindexing obligations rather than as a quotient
   question. Whoever takes them should move the build position first.
4. **Record the two genuinely open foundational questions separately**, so
   neither gets attributed to the quotient decision: the per-field universe on
   `FieldSpec` (blocks a module *record*), and `AlgS.Field`/`Apart` (blocks
   vector spaces and dimension).

## Verification

Everything in this ADR is reproducible from the tree:

```sh
# the three suites, each must print a NONZERO count
scripts/cargo-serialized.sh test --release -p axeyum-lean-kernel \
  --lib poly_setoid_tests -- --test-threads=4          # 7 passed
scripts/cargo-serialized.sh test --release -p axeyum-lean-kernel \
  --lib module_setoid_tests -- --test-threads=4        # 7 passed
scripts/cargo-serialized.sh test --release -p axeyum-lean-kernel \
  --lib subgroup_setoid_tests -- --test-threads=4      # 7 passed

# nothing upstream moved
scripts/cargo-serialized.sh test --release -p axeyum-lean-kernel \
  --lib structures_setoid -- --test-threads=4          # 18 passed
scripts/cargo-serialized.sh test --release -p axeyum-lean-kernel \
  --lib first_iso -- --test-threads=4                  # 5 passed

# the declaration count, against a FRESHLY BUILT binary
scripts/cargo-serialized.sh build --release -p axeyum-lean-kernel \
  --example shape_search
target/release/examples/shape_search --ns AlgS --name-contains Poly --expect 14
target/release/examples/shape_search --ns AlgS --name-contains Module --expect 22
target/release/examples/shape_search --ns AlgS --name-contains Subgroup --expect 20
```

`--name-contains Poly` returns 14 rather than 15 and `Module` 22 rather than
23 because `AlgS.add_add_add_comm` and `AlgS.idem_eq_e` are declared into the
`AlgS` root, not into the sub-namespace — they are general ring and group
lemmas that happen to have been needed here.

## Related

- [ADR-1595](adr-1595-quotients-stay-setoids-and-quot-sound-stays-out.md) — the
  decision this work was done under, and the one this ADR reports evidence for.
- [ADR-1588](adr-1588-a-setoid-flavored-alg-spine-for-creal.md) — the `AlgS`
  spine, and the reason it stops short of `Field`.
- [ADR-1592](adr-1592-algs-group-and-orderedring-close-the-gaps-adr-1590-named.md)
  — `AlgS.inv_unique` and `AlgS.add_left_cancel`, which `AlgS.idem_eq_e` and
  `AlgS.Module.neg_smul` are built on.
- [ADR-1578](adr-1578-an-abstract-algebraic-structure-spine.md) — `declare_record`
  and the `FieldKind` universe rule this ADR sizes a change to.
- [04 algebra](../../math-department/04-algebra.md) — Next Five items 4 and 5,
  and the `funext` consequence this work partly answers.
