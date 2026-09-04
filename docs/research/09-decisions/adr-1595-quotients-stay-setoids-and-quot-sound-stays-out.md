# ADR-1595: quotients stay setoids; `Quot.sound` stays out of the kernel

Status: proposed
Date: 2026-09-04
Lane: `quotient-decision`
Roadmap: W0-1 (convergence C1 — reviewers 04.1, 09.3, 12.1)

Index-summary: three reviewers independently asked for `Quot.sound`. The
decision was made by measurement, not by argument: the first isomorphism
theorem over `AlgS.Group` (roadmap W2-8) was **built by the setoid route and
it landed** — twelve declarations, 1,061 lines of term-building Rust, an
empty `Kernel::axiom_footprint` on every one, 0.44 s of test time. The whole
cost of the setoid route on this theorem is **three one-line obligations**
(`equivRefl`/`equivSymm`/`equivTrans` on the quotient record) that `Quot` +
`Eq` would give free; the two real congruence proofs (`kerEquivOpCongr`,
`kerEquivInvCongr`) do **not** go away under `Quot.sound` — they reappear as
`Quot.lift₂`/`Quot.lift`'s well-definedness side conditions — and the five
group laws are *cheaper* here (one `fCongr` application each) than the
`Quot.ind` induction they would need. Two further measurements decide it:
`Kernel::axiom_footprint` counts `Declaration::Quotient` as trusted base, so
adding `Quot.sound` puts **five** names (`Quot`, `Quot.mk`, `Quot.lift`,
`Quot.ind`, `Quot.sound`) into every downstream footprint, not one; and
`Quot.sound` does not even unlock the classical statement, because the
*image* side needs a subtype and this kernel has no `Subtype` and no `Sigma`
(both verified ABSENT). **Recommendation: option (b), commit to setoid
quotients.** Revisit only if a measured theorem is shown to be unreachable
this way.
Index-status: proposed

## Context

The kernel admits Lean's privileged four-declaration quotient package —
`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` (`src/quotient.rs`,
`QuotKind::{Type, Ctor, Lift, Ind}`) — and deliberately not `Quot.sound`.
There is no `funext`, no `propext` and no choice. ADR-0512 priced this once
already, for ℝ, and chose a Bishop setoid over a Cauchy quotient on exactly
these grounds.

Three of the twelve standing reviewers asked, independently, for the question
to be settled:

- **04 algebra** — "`Quot.sound`, and it is the largest open decision in the
  library"; the whole quotient shelf (first isomorphism theorem, polynomial
  rings, vector spaces) sits behind it. Verdict: *dismissive* until W0-1 is
  decided and W2-8 lands.
- **09 category theory** — the same fork plus `funext`: build categories over
  setoids with morphism equality as an explicit equivalence, or wait for
  function extensionality. Verdict: *absent, opposed*.
- **12 the chair** — would sign the report once W0-1 and W0-2 are *written*.

The algebra reviewer stated the case on both sides fairly and then named the
third option itself: keep `Quot.sound` out and carry quotients over setoids,
generalizing what ℝ and the `AlgS` spine already do. It closed with the
sentence this ADR is an answer to:

> Whether the algebra shelf can be built this way at reasonable cost is an
> empirical question nobody has tested, and testing it on one nontrivial
> example — the first isomorphism theorem over `AlgS.Group` — would settle a
> lot.

So it was tested.

## The measurement

### What was built

`crates/axeyum-lean-kernel/src/nat_prelude/structures_setoid.rs`, commit
`5337d192b`. Twelve declarations in a new `AlgS.Hom.*` namespace, all
admitted by `Kernel::add_declaration`:

| declaration | kind | what it is |
|---|---|---|
| `AlgS.Hom.ker` | definition | the kernel, as a **predicate** on `G.carrier` |
| `AlgS.Hom.kerEquiv` | definition | the induced equivalence `fun a b => H.equiv (f a) (f b)` |
| `AlgS.Hom.image` | definition | the image, as a **predicate** on `H.carrier` (`Exists`) |
| `AlgS.Hom.mapOne` | theorem | `H.equiv (f G.e) H.e` |
| `AlgS.Hom.mapInv` | theorem | `H.equiv (f (G.inv a)) (H.inv (f a))` |
| `AlgS.Hom.kerEquivOpCongr` | theorem | **congruence obligation 1** — the quotient's `opCongr` |
| `AlgS.Hom.kerEquivInvCongr` | theorem | **congruence obligation 2** — the quotient's `invCongr` |
| `AlgS.Hom.quotient` | definition | `... -> AlgS.Group` — **the quotient group itself** |
| `AlgS.Hom.quotient_equiv` | theorem | its `equiv` selector reduces definitionally to `kerEquiv` |
| `AlgS.Hom.quotient_equiv_iff_ker` | theorem | `a ~ b` in the quotient iff `a·b⁻¹ ∈ ker f` |
| `AlgS.Hom.image_mem` | theorem | every `f a` is in the image |
| `AlgS.Hom.firstIso` | theorem | the assembled first isomorphism theorem |

The construction that makes it work: **a quotient group is the same carrier
under a coarser equivalence, not a new carrier of equivalence classes.**
`AlgS.Hom.quotient`'s `carrier` field is `G.carrier` unchanged, its `op` is
`G.op` unchanged, and the entire quotient happens in the `equiv` field. This
is what the `AlgS` spine (ADR-1588) was built for and it is the first time it
has been used for something other than moving an existing `Eq`-flavored
theorem across.

`AlgS.Hom.firstIso`'s rendered type, read from the kernel:

```text
(G : AlgS.Group) -> (H : AlgS.Group)
  -> (f : AlgS.Group.carrier G -> AlgS.Group.carrier H)
  -> (fCongr : (a b : carrier G) -> AlgS.Group.equiv G a b
                 -> AlgS.Group.equiv H (f a) (f b))
  -> (fMul : (a b : carrier G) -> AlgS.Group.equiv H
                 (f (AlgS.Group.op G a b))
                 (AlgS.Group.op H (f a) (f b)))
  -> And ((a b : carrier G) ->
            Iff (AlgS.Group.equiv (AlgS.Hom.quotient G H f fCongr fMul) a b)
                (AlgS.Hom.ker G H f (AlgS.Group.op G a (AlgS.Group.inv G b))))
     (And ((a b : carrier G) -> AlgS.Group.equiv H
              (f (AlgS.Group.op (AlgS.Hom.quotient G H f fCongr fMul) a b))
              (AlgS.Group.op H (f a) (f b)))
          ((a : carrier G) -> AlgS.Hom.image G H f (f a)))
```

Read: **the quotient's equivalence is exactly the kernel congruence
(`a ~ b ⟺ a·b⁻¹ ∈ ker f`), the induced map is a homomorphism out of it, and
it is onto the image.** Injectivity is the `mpr` of the first conjunct, which
is why there is no fourth component.

### 1. Did it land? Yes.

Every one of the twelve has an **empty axiom footprint**, read from
`Kernel::axiom_footprint`, not from a name:

```
test first_iso_tests::first_isomorphism_theorem_is_axiom_free ... ok
test first_iso_tests::first_isomorphism_theorem_admits_by_the_setoid_route ... ok
test first_iso_tests::the_quotients_equiv_reduces_to_the_kernel_congruence ... ok
test first_iso_tests::the_quotient_is_rejected_without_the_kernel_congruence_proof ... ok
test first_iso_tests::first_isomorphism_theorem_types_render ... ok
test result: ok. 5 passed; 0 failed; finished in 0.44s
```

`shape_search`, rebuilt after the change, moves from `declarations=2674` to
`declarations=2686` — **+12 exactly**, `definition` 638→642 and `theorem`
1843→1851. The positive control for binary freshness was
`Nat.Finset.pigeonhole` (landed `164e4d329`, the most recent kernel
declaration commit in the tree).

The negative control is what makes the count trustworthy:
`the_quotient_is_rejected_without_the_kernel_congruence_proof` rebuilds the
quotient instance with the **source group's own `opCongr`** — congruence for
`G.equiv`, not for the coarser kernel congruence — in slot 6, and requires
`add_declaration` to reject. It does. So `kerEquivOpCongr` is demonstrably
load-bearing and the obligation count below is not decoration.

`quotient_equiv` is a second deliberate probe rather than a convenience
lemma: it is proved by `Iff.intro (fun h => h) (fun h => h)`, so its
admission is precisely the statement that `AlgS.Group.equiv` applied to the
quotient *instance* reduces definitionally to `AlgS.Hom.kerEquiv`. It
admits, which means downstream users of the quotient never have to unfold it
by hand.

### 2. What it cost

| measure | value |
|---|---|
| Rust added, term-building | 1,061 lines |
| Rust added, tests | 281 lines |
| declarations added | 12 (4 definitions, 8 theorems) |
| `first_iso_tests` wall clock | **0.44 s** (`--release`, `--test-threads=4`) |
| whole `structures_setoid` suite | **16.41 s**, 18 passed (13 pre-existing + 5) |
| `linarith` suite | 96.32 s, 99 passed, 1 ignored — unchanged |
| clippy `-p axeyum-lean-kernel --all-targets -D warnings` | clean |
| `cargo check --workspace --all-targets` | clean |

**The congruence-obligation count — the whole point of the experiment.**
`AlgS.Group` has fifteen fields. Here is every one, what supplied it, and
whether a genuine `Quot`-with-`Eq` quotient would have supplied it free:

| # | field | supplied by | free under `Quot` + `Eq`? |
|---|---|---|---|
| 0 | `carrier` | `G.carrier`, reused | no — `Quot` makes a new type |
| 1 | `equiv` | `fun a b => H.equiv (f a) (f b)` | no — the relation is still needed *to form* `Quot` |
| 2 | `equivRefl` | `H.equivRefl (f a)`, 1 line | **YES** (`Eq.refl`) |
| 3 | `equivSymm` | `H.equivSymm`, 1 line | **YES** (`Eq.symm`) |
| 4 | `equivTrans` | `H.equivTrans`, 1 line | **YES** (`Eq.trans`) |
| 5 | `op` | `G.op`, reused | no — needs `Quot.lift₂` |
| 6 | `opCongr` | `kerEquivOpCongr`, 7 steps | **no** — same content is `Quot.lift₂`'s side condition |
| 7 | `e` | `G.e`, reused | free either way |
| 8 | `inv` | `G.inv`, reused | no — needs `Quot.lift` |
| 9 | `invCongr` | `kerEquivInvCongr`, 6 steps | **no** — same content is `Quot.lift`'s side condition |
| 10 | `assoc` | `fCongr _ _ (G.assoc a b c)`, 1 application | *cheaper here* — `Quot` needs `Quot.ind` ×3 |
| 11 | `identL` | 1 application | *cheaper here* — `Quot.ind` ×1 |
| 12 | `identR` | 1 application | *cheaper here* — `Quot.ind` ×1 |
| 13 | `invL` | 1 application | *cheaper here* — `Quot.ind` ×1 |
| 14 | `invR` | 1 application | *cheaper here* — `Quot.ind` ×1 |

So, precisely:

- **3 obligations were discharged by hand that a real quotient would have
  discharged for free** — `equivRefl`, `equivSymm`, `equivTrans`, one line
  each, each a direct application of the codomain group's own field.
- **2 obligations do not go away under `Quot.sound`.** `kerEquivOpCongr` and
  `kerEquivInvCongr` are exactly the well-definedness arguments
  `Quot.lift₂`/`Quot.lift` demand before `G.op` and `G.inv` may descend.
  They are the mathematics of the theorem, not a tax on the encoding.
- **5 obligations are cheaper on the setoid route** — each group law is one
  `fCongr` application, where the `Quot` route needs a `Quot.ind` induction
  to get back to representatives first.

**Net cost of not having `Quot.sound`, on this theorem: three lines.**

### 3. Two measurements that were not asked for and change the answer

**(i) `Quot.sound` is not one footprint entry, it is five.**
`Kernel::axiom_footprint` (`src/lean_pp.rs:1297`) filters the transitive
dependency closure to `Declaration::Axiom | Declaration::Opaque |
Declaration::Quotient`. The quotient package is *already* counted as trusted
base. Today that costs nothing because nothing uses it — `shape_search`
reports `quot=0` across every constructed prelude, and `add_quotient_package`
is called only from `axeyum-lean-import` and from the kernel's own
differential tests. The moment a library construction goes through `Quot`,
its footprint names `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` and (under
option (a)) `Quot.sound`. The headline metric is currently **2,385 of 2,387
kernel-lean facts axiom-free, of 2,487 proved** (`scripts/validate-facts.py`,
2026-09-04); the algebra reviewer priced option (a) as "one axiom", and the
kernel prices it at five names on every downstream fact.

**(ii) `Quot.sound` does not unlock the statement it is claimed to unlock.**
The classical first isomorphism theorem is an isomorphism between two group
*objects*, `G/ker f` and `Im f`. `Quot.sound` supplies the left one. The
right one needs a carrier `{y : H.carrier // ∃ a, f a ≈ y}` — a subtype.
`shape_search --name-like subtype` and `--name-like sigma` both return
ABSENT against a freshly built binary (positive control: `any-kind=2686`).
So option (a) buys half a theorem and leaves the other half needing a second
kernel addition it does not provide.

The setoid route has no such gap, because in it the image never needs a
carrier at all: the quotient *is* the image, presented on `G.carrier`, and
"onto the image" is `AlgS.Hom.image_mem` plus the definitional converse.
This is not a workaround; it is the Bishop presentation, and it is why the
statement above is complete as written.

## The three options, priced in the project's own terms

### (a) Add `Quot.sound` as an axiom

| | |
|---|---|
| **buys** | quotient types with `Eq` as their equality; the `AlgS` twin spine becomes unnecessary for quotient constructions; parity with Lean's own foundation |
| **costs** | 5 names in the footprint of every downstream fact (`Quot`, `.mk`, `.lift`, `.ind`, `.sound`), measured, not 1; "axiom-free across 2,385 facts" becomes "axiom-free except the quotient package" for the whole algebra shelf and everything above it |
| **does not buy** | the image side — still needs `Subtype`/`Sigma`, both ABSENT |
| **saves, measured** | 3 one-line obligations on the theorem that was built |

### (b) Commit to setoid quotients

| | |
|---|---|
| **buys** | the footprint claim intact; W2-8 landed today with an empty footprint; the image side needs nothing new; the `AlgS` spine already exists and now has a second, non-trivial customer |
| **costs** | the standing `AlgS`-vs-`Alg` tax, already measured in ADR-1588: 23 fields at `CommRing` against `Alg`'s 16 — 4 equiv-infrastructure fields plus 3 congruence fields per structure — and a second spine (233 `AlgS.*` declarations) that must be kept in step with the first |
| **costs, per theorem** | 3 one-line obligations, as measured above |
| **risk** | a future theorem may genuinely need `Quot.sound`; nothing in this experiment proves one does not exist |

### (c) Admit `Quot.sound` in a labelled second tier

| | |
|---|---|
| **buys** | both claims, if the tiering is honest and enforced |
| **costs** | a real mechanism, not a label: `axiom_footprint` already returns the names, so the tier boundary would have to live in the fact ledger (a `trusted_tier` field) *and* in a gate that refuses tier-2 evidence for a tier-1 fact. That gate does not exist and is not free |
| **the trap** | this is the option that reads best and measures worst. Once `Quot.sound` is in the environment, nothing but discipline keeps a tier-1 proof from routing through it, and CLAUDE.md's own rule applies: a checker that cannot fail is worse than no checker. The tier would have to be mutation-tested — delete one guard, require exactly one test to die — before it could be quoted |
| **when it becomes right** | if and when a measured theorem is shown unreachable by route (b). Not before |

## Decision

**Option (b). Quotients are carried as setoids. `Quot.sound` stays out of the
kernel.**

The empirical question the algebra reviewer posed has an answer: yes, the
algebra shelf can be built this way, and the measured cost on the hardest
example anyone named is three lines. The reviewer's strongest argument for
option (a) — "it is one axiom, and it is the conservative one" — is false as
measured in this kernel: it is five names on every downstream footprint, and
it does not reach the classical statement anyway without a subtype former
nobody has asked for.

Two supporting judgements, stated so they can be argued with:

1. **`Quot.sound` mostly moves work, it does not remove it.** Of the five
   obligations the setoid route made explicit, two survive verbatim into the
   `Quot` route as `Quot.lift`'s side conditions and five get *harder*
   (`Quot.ind` instead of one application). The genuinely saved work is the
   three equivalence-infrastructure fields.
2. **The setoid presentation is a research result, not a workaround.** It is
   the thing this library can say that Mathlib cannot: a complete quotient
   construction with an empty trusted base. That is an uncontested axis in
   the Pareto sense of
   [07-the-cost-model-and-pareto-position.md](../../formalized-math-2026-08/07-the-cost-model-and-pareto-position.md),
   and option (a) spends it for three lines.

**This decision is reversible and should be re-opened on evidence**, not on
preference: the trigger is a *named, attempted* theorem shown to be
unreachable over setoids, with the obstruction stated as a specific
obligation the kernel could not discharge. This ADR's own method is the
template for that.

## What changes downstream

| roadmap item | under (b) — recommended | under (a) | under (c) |
|---|---|---|---|
| **W2-8** first isomorphism theorem over `AlgS.Group` | **landed** (`5337d192b`), empty footprint | would need rebuilding on `Quot`, plus a subtype former for the image | as (a), plus tier plumbing |
| **W2-9** polynomial rings as a structure | proceed over `AlgS.CommRing`; coefficient equality is the ring's `equiv`, and `AlgS.Hom.*` is the template | quotients by ideals become `Quot`; footprint tainted | as (a) |
| **W3-2** vector spaces, bases, dimension | proceed; needs W2-9 and an `AlgS.Field` (which needs `Apart` — ADR-1588 stopped short of `Field` for exactly this reason, and that is a *separate* open question, not this one) | same, plus the taint | as (a) |
| **W3-3** categories, functors, natural transformations | **unblocked today.** Morphism equality is an explicit `equiv` field, matching `AlgS`. `funext` is not needed and is not on this ADR's table | would still need `funext` separately — `Quot.sound` does not give function extensionality | as (a) |
| **W3-4** products and coproducts as universal properties | follows W3-3 unchanged | follows W3-3 | as (a) |

Reviewers unblocked by **(b)**:

- **04 algebra** — its stated trigger is "W0-1 is decided *and* W2-8 lands".
  Both are true as of this ADR. The verdict should move off *dismissive* on
  the next reconciliation, and the reviewer is owed the honest note that its
  preferred option was priced and declined on measurement.
- **09 category theory** — the setoid answer it named as "available today and
  the honest continuation" is now the decided one, and W3-3 has no remaining
  foundational blocker. Its `funext` request is **not** granted and is **not**
  answered by this ADR; it is a separate decision, and W3-3 is reachable
  without it.
- **12 the chair** — its trigger is that W0-1 and W0-2 are *written*. This is
  W0-1. W0-2 (the classical-axiom policy) is still open.

## The consequence for ℝ

**Would `Quot.sound` let `CReal` become a genuine quotient?** Yes, in
principle: `CReal := Quot CReal.Equiv`, and every `CReal.Equiv x y` in the
library becomes `Eq x y`. That is the construction ADR-0456 priced and
ADR-0512 declined.

**What would migrating cost?** Sized, not attempted:

| | measured |
|---|---|
| `CReal.*` declarations | **610** (`shape_search --include-constructed --ns CReal`) |
| declarations whose **type** mentions `CReal.Equiv` | **209** — every one restated |
| the `AlgS` spine that exists to serve `CReal` | **233** declarations, 3,488 lines before this change; ADR-1588's stated purpose was exactly that `CReal` cannot be an `Alg.*` instance |
| the footprint claim | every `CReal` fact, and everything above it (`Complex`, `CPoint`, the integral, the analysis shelf), would carry the 5-name quotient footprint |

So the migration is roughly 209 restated types, an unknown but large number
of reworked proofs beneath them, and the retirement of a 233-declaration
spine — in exchange for `Eq` instead of `CReal.Equiv` and the loss of the
headline metric on the entire real-analysis shelf. **Do not migrate.** This
ADR sizes it so the question does not have to be re-opened from zero, and
records that the answer is no on cost, not on principle.

## Alternatives considered and rejected

- **Add `funext` instead**, on the theory that most of what the reviewers
  want is function extensionality rather than quotients. Out of scope here:
  09 asks for it, but W3-3 was shown reachable without it, so there is no
  measured demand yet. If it is proposed, it should be proposed the same way
  — with a theorem that was attempted and stopped.
- **State the isomorphism between two `AlgS.Group` values** (`G/ker f` and
  `Im f` as separate objects). Attempted and abandoned before writing code:
  it requires a subtype carrier for the image, and `Subtype`/`Sigma` are
  ABSENT. Under the setoid presentation the two objects coincide, which is
  why `firstIso`'s first conjunct carries the content instead.
- **A `Setoid` record generalizing the pattern**, so `AlgS.Hom.quotient`
  would be an instance of a generic quotient former. Deliberately not built:
  one customer is not a boundary (ADR-0001's rule), and the right time is
  after W2-9 supplies a second.

## Verification

Everything in this ADR is reproducible from the tree:

```sh
# the theorem, its footprint, and the negative control (5 tests, nonzero)
scripts/cargo-serialized.sh test --release -p axeyum-lean-kernel \
  --lib first_iso_tests -- --test-threads=4 --nocapture

# the twelve declarations, and the +12 declaration count
cargo run -q --release -p axeyum-lean-kernel --example shape_search \
  -- --ns AlgS --name-contains Hom --expect 12

# the ABSENT results this ADR leans on (each prints its own positive control)
... --example shape_search -- --name-like subtype --expect-absent
... --example shape_search -- --name-like sigma   --expect-absent

# the headline metric
python3 scripts/validate-facts.py
```

## Related

- [ADR-0512](adr-0512-real-is-constructed-as-a-setoid-over-the-rationals.md)
  — the same fork, decided the same way, for ℝ. This ADR generalizes its
  finding from one carrier to the quotient construction itself.
- [ADR-0456](adr-0456-real-is-an-ordered-ring-modelled-by-int.md) — where the
  "Cauchy quotient needs `Quot.sound`" price tag was first written.
- [ADR-1588](adr-1588-a-setoid-flavored-alg-spine-for-creal.md) — the `AlgS`
  spine, and the measured 23-vs-16 field cost this decision commits to.
- [ADR-1592](adr-1592-algs-group-and-orderedring-close-the-gaps-adr-1590-named.md)
  — `AlgS.inv_unique` and `AlgS.add_left_cancel`, which `AlgS.Hom.mapOne` and
  `AlgS.Hom.mapInv` are built on.
- [The department roadmap](../../math-department/00-roadmap.md) — W0-1, and
  the C1 convergence this closes.
- [04 algebra](../../math-department/04-algebra.md) § The blocker — the
  argument on both sides, and the sentence that specified this experiment.
- [09 category theory](../../math-department/09-category-theory.md)
  § The blocker — the same fork from the categorical side.
