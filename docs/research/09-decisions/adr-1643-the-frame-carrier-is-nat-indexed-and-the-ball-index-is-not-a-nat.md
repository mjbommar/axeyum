# ADR-1643: the topological carrier is a frame with `Nat`-indexed joins, and the ball index is a pair, not a `Nat`

Status: proposed
Date: 2026-09-05
Lane: `frame-carrier`
Roadmap: W2-21 (a topological-space carrier, ℝ as the first instance), executing
[ADR-1602](adr-1602-the-metric-layer-first-then-pointfree-and-not-open-sets.md)'s
recommendation. Reviewer 06 (topology); downstream 05 (geometry, manifolds).

Index-summary: ADR-1602 decided that topology proper, when it is built, is
built **pointfree** — a frame, not a family of open subsets — and left the
construction to W2-21. This ADR is that construction, and it reports three
things the plan did not predict. **(1)** The setoid equivalence a frame needs is
NOT independent data the way `Metric`'s is: on a poset antisymmetry forces it,
so `Top.Frame.Equiv a b := le a b ∧ le b a` is a DERIVED definition and
`equivRefl`/`equivSymm`/`equivTrans` plus every congruence obligation are
theorems, removing six fields from every future instance at zero cost. **(2)**
Only ONE direction of the frame distributive law is an axiom; the converse
`sup (a ⊓ fₙ) ≤ a ⊓ sup f` holds in every complete lattice and is proved here
once (`Top.Frame.le_inf_sup`), so an instance that supplied both halves would be
supplying a theorem. **(3)** The planned representation of an open — a decidable
predicate `Nat → Bool` on ball indices, re-indexed through `Nat.pair` — is
**doubly unavailable**, and both reasons are findings rather than preferences.
A `Nat → Bool` carrier is not closed under the countable joins a frame is
DEFINED by (`sup f i = ∃ n, f n i` is not a `Bool`), and the pairing route
would require `unpairLeft (pair a b) = a`, which is the content of the family
`natural-avg-pair` (`Batteries.Data.Nat.Bisect` + `Mathlib.Data.Nat.Pairing`),
registered **held-out with ten rows** — `Nat.pair` and `Nat.unpairLeft` are in
this kernel as constructions with no theorem about either for exactly that
reason (ADR-1060, ADR-1220). Indexing a ball by its centre AND radius directly
(`Top.Opens := Rat → Nat → Prop`) removes the need for a pairing, and with it
the need for a surjective `Rat.enum : Nat → Rat` that the plan sized as its own
commit. The ℝ instance is `Top.ballFrame`, and the reals prelude's
`CReal.density` turns out to BE the covering property of the frame: the
restatement type-checks by δβ with no new estimate.
Index-status: proposed

## Context

[ADR-1602](adr-1602-the-metric-layer-first-then-pointfree-and-not-open-sets.md)
closed W0-3 by building the metric carrier and measuring that it needed no
topology. Its fourth decision point was about what to do when a topological
carrier is eventually wanted:

> **Topology proper, when it is needed, is a frame.** A frame is an algebraic
> structure — a complete lattice with one distributivity law — and this lane
> just demonstrated that `declare_record` builds an arbitrary setoid-flavored
> structure at zero design cost. A *family of open subsets*, by contrast, needs
> closure under **arbitrary** unions, which means quantifying over an index
> type … The record machinery is shaped for the algebra and against the subsets.

It also marked W2-21 **not on the critical path**. So this lane is a carrier and
one instance, not a theory of ℝ, and the interesting output is the cost table
and the three surprises.

## What was built

`crates/axeyum-lean-kernel/src/top_frame.rs`, registered from the crate root.
Nothing under `metric.rs`, `metric_prod.rs`, `creal.rs` or `creal/` was touched.

### `Top.Frame`, a sixteen-field record at `Sort 2`

| # | field | type |
|---|---|---|
| 0 | `carrier` | `Sort 1` |
| 1 | `le` | `carrier → carrier → Prop` |
| 2 | `leRefl` | `∀ a, le a a` |
| 3 | `leTrans` | `∀ a b c, le a b → le b c → le a c` |
| 4 | `inf` | `carrier → carrier → carrier` |
| 5 | `top` | `carrier` |
| 6 | `bot` | `carrier` |
| 7 | `sup` | `(Nat → carrier) → carrier` |
| 8 | `infLeLeft` | `∀ a b, le (inf a b) a` |
| 9 | `infLeRight` | `∀ a b, le (inf a b) b` |
| 10 | `leInf` | `∀ a b c, le c a → le c b → le c (inf a b)` |
| 11 | `leTop` | `∀ a, le a top` |
| 12 | `botLe` | `∀ a, le bot a` |
| 13 | `leSup` | `∀ f n, le (f n) (sup f)` |
| 14 | `supLe` | `∀ f a, (∀ n, le (f n) a) → le (sup f) a` |
| 15 | `frameLe` | `∀ a f, le (inf a (sup f)) (sup (fun n => inf a (f n)))` |

Built with the `AlgS` spine's own `declare_record` (`nat_prelude::structures`),
unchanged — including its ADR-1578 universe control, which requires the same
field list to be **refused** at `Sort 1`.

### Derived, generic in the frame

`Top.Frame.Equiv`, `equiv_refl`, `equiv_symm`, `equiv_trans`, `sup_mono`,
`sup_const`, `le_inf_sup`, `frame_law`, `inf_comm`.

### The ℝ instance

`Top.Opens := Rat → Nat → Prop` with pointwise `And` / `True` / `False` /
`Exists`; the ten laws as `Top.Opens.*`; the instance `Top.ballFrame`; and the
selector-reduction probe `Top.ballFrame_inf`.

### The frame's points

`Top.MemBall`, `Top.MemOpen`, `Top.ball_mem_self`, `Top.ball_density`,
`Top.mem_top`, `Top.mem_open_mono`, `Top.ball_separated`.

## Decision

1. **A frame's setoid equality is derived, not a field.** `Metric` carries
   `equiv` and three laws and a `distCongr` because `CReal.Equiv` is genuinely
   independent of `dist` (ADR-0512). A frame is a poset, and on a poset
   `a ~ b ↔ a ≤ b ∧ b ≤ a` is forced. So `Top.Frame` carries neither `equiv`
   nor congruence fields, and an instance discharges six fewer obligations.
   Any later carrier should ask which of the two situations it is in before
   copying `Metric`'s field list.
2. **Joins are `Nat`-indexed, and that is a description of ℝ, not a
   restriction.** ADR-1612's predicativity constraint says an arbitrary join
   over a `Sort`-indexed family must be stated at a fixed universe. A
   `(I : Sort 1) → (I → carrier) → carrier` field would push the record up and
   buy nothing for the one instance built here, because ℝ is **second
   countable**. The place the countability is visible is `sup_const`, whose
   `a ≤ sup (fun _ => a)` half needs an inhabitant of the index — `Nat.zero`.
   A genuinely uncountable frame needs a new field shape, not a new law.
3. **One direction of the frame law is an axiom; the other is a theorem.**
   `frameLe` is the field; `Top.Frame.le_inf_sup` is proved from `supLe`,
   `infLeLeft`, `infLeRight`, `leSup` and `leTrans` alone; `Top.Frame.frame_law`
   glues them into the equivalence the textbook states.
4. **An open is a predicate on `(centre, radius index)` pairs, NOT on `Nat`.**
   See the two obstructions below. `Top.Opens := Rat → Nat → Prop`.
5. **Do not prove anything about `Nat.pair`/`Nat.unpairLeft`.** The pairing
   round-trip belongs to a held-out family. Any future construction that wants a
   countable code for a compound index should widen the index type instead.

## The two obstructions the plan did not have

### `Nat → Bool` is not closed under the joins that define a frame

ADR-1624 established that a subset here is a predicate, and `Nat.Subsets` makes
it a **decidable** one (`Nat → Bool`), which is why it is the natural first
guess for "a set of ball indices". It does not work. Meet is pointwise
`Bool.and` and is fine; the join of a countable family is

```text
sup f i  =  ∃ n, f n i
```

and that is a `Prop`, not a `Bool`. Deciding it is deciding a countable
disjunction, which is exactly the constructive taboo (`LPO`) the reals prelude's
own `omniscience` module records as unavailable. There is no re-indexing that
repairs this, because the problem is the codomain, not the index. So the carrier
is `Prop`-valued and `sup` is `Exists` — at which point no re-indexing is needed
at all, and the frame law becomes distributivity of `∧` over `∃`, which is one
`Exists.rec` and two `And` projections.

### The pairing round-trip is held out

The planned route indexes basic balls by a single `Nat` decoding to
(rational centre, radius), and re-indexes a countable union through
`Nat.pair`/`Nat.unpairLeft`. Every step of that needs
`unpairLeft (pair a b) = a` and its partner.

`artifacts/autogenesis/drawn-population-component-census-v1.json` registers the
family **`natural-avg-pair`**, modules `Batteries.Data.Nat.Bisect` and
`Mathlib.Data.Nat.Pairing`, with `"partitions": {"held-out": 10}` and ten rows.
`nat_prelude.rs` says the same thing from the other side: `Nat.avg` and
`Nat.pair` are declared as "**Construction only, ADR-0653 — no theorem about
either is declared here**", and `unpair.rs` follows the same rule. Proving the
round-trip would spend a blind evaluation population that is not this lane's to
spend, and the partition check the lane ran before writing any term is what
caught it.

The repair costs nothing: a ball is `(q : Rat, k : Nat)` and the carrier is a
predicate on that pair. No `Nat` code, no pairing, no
`Rat.enum : Nat → Rat`, and no surjectivity proof — the plan had sized the
enumeration as its own commit and it is simply not needed. It is worth naming
the general shape, because it is the third instance of it this quarter:
**when a construction needs a code for a compound index, widening the index type
is usually cheaper than encoding it into `Nat`, and it never touches a
number-theoretic family.**

## `CReal.density` IS the covering property

`Top.MemBall x q k` is written as `creal/density.rs`'s own two-sided sandwich

```text
CReal.le x (CReal.ofRat (Rat.add q (Rat.natDivSucc 1 k)))
CReal.le (CReal.ofRat (Rat.sub q (Rat.natDivSucc 1 k))) x
```

rather than as `|x − q| < ε`, for the reason that module records: the `abs`
form routes the difference through `CReal.add`, which samples at Bishop's
shifted index `2n+1`, and buys nothing. With that encoding

```text
Top.ball_density : ∀ x k, ∃ q, Top.MemBall x q k
```

is proved by `CReal.density x k` and nothing else — the restatement type-checks
by δβ. That is not a shortcut, it is the result: **the density of ℚ in ℝ and the
covering property of the open-ball frame are the same statement**, and the
frame's vocabulary was chosen to make that visible rather than to hide it behind
a re-derivation. `Top.mem_top` (every real is in the frame's top element) and
`Top.mem_open_mono` (the points-of-an-open assignment is monotone for the
frame's own order) are the two statements that genuinely need the frame and not
just `CReal`.

## What did NOT land

**Hausdorff separation from `CReal.Apart` is not proved.** What landed is
`Top.ball_separated`: if the upper bracket of one ball is strictly below the
lower bracket of another, no point lies in both. Four steps, no arithmetic
(`le_trans` through the shared point, `lt_of_le_of_lt`, `lt_irrefl`).

The missing half is **index selection, not geometry**: given `Apart x y`, choose
`k`, `m` and the two centres so that the brackets separate. `CReal.Apart` is
`lt x y ∨ lt y x` and `CReal.lt` carries its gap as a rational witness, so the
step is: eliminate the `Or`, read the gap `g`, use the Archimedean property to
find `k` with `4/(k+1) < g`, then take the centres from `CReal.density` at that
`k` and discharge two `Rat` inequalities of the form `q + 1/(k+1) < r − 1/(k+1)`.
Sized: one `Or.rec`, two `Exists.rec`s, one Archimedean application, and roughly
four rational-arithmetic rearrangements of the kind `creal/density.rs`'s
`widen_to_double` is one instance of — call it 250–400 lines of term building
against lemmas that all exist (`Rat.natDivSucc_add`, `Rat.add_le_add`,
`Rat.lt_of_le_of_lt`, `CReal.lt_cotrans`). It is bounded work with no design
question in front of it; it was left out because the deliverable is the carrier.

**No point-of-a-frame (completely prime filter) construction.** The brief put it
out of scope and this lane agrees: it needs a `Subtype` the kernel does not
have, which ADR-1595 and ADR-1602 both record.

**The frame is the FREE frame on the basis, not the topology of ℝ.**
`Top.Opens` elements are arbitrary sets of basic balls, so two different sets
whose unions of balls coincide are different formal opens. Getting the actual
lattice of open subsets of ℝ means quotienting by the covering relation (formal
topology's saturation), which is a genuinely bigger construction and is not
attempted. The honest reading of `Top.ballFrame` is: *the frame presented by the
rational-ball basis*, with `Top.MemOpen` the map from formal opens to sets of
points. Every theorem here is stated about that object and none of them claims
more.

## Cost, counted

Measured 2026-09-05 in this lane's own worktree, `--release --test-threads=4`.

| measure | value |
|---|---|
| Rust added (`top_frame.rs`, term building + docs) | 2,485 lines |
| Rust added (`top_frame/top_frame_tests.rs`) | 606 lines |
| declarations added | **53** — 1 inductive, 1 constructor, 1 recursor, 26 definitions (16 of them the record's selectors), 24 theorems |
| `top_frame_theorem_inventory --defs` | **50 rows, 0 with a nonempty axiom footprint** |
| axioms in the footprint of any of the 53 | **0**, read from `Kernel::axiom_footprint` |
| `top_frame::` suite | **11 passed, 0 failed**, 48.7 s (first run), 45.1 s (after the statement fold) |
| kernel refusals during development | **0** — every proof term was admitted on its first kernel run |

That last row is the one worth explaining rather than boasting about. It is not
evidence that the proofs are clever; it is evidence that **this carrier is
almost pure `Prop` plumbing**. Nine of the ten `Top.Opens` laws are `And`/`Or`
projections and `Exists.rec`, the frame law is distributivity of `∧` over `∃`,
and the two `CReal` facts are `CReal.density` applied and a four-step chain
through `le_trans`/`lt_of_le_of_lt`/`lt_irrefl`. Compare `Metric`, where the
same lane-shaped task needed eight new `CReal` lemmas because the reals prelude
did not have them. **A frame is cheap here for the same reason ADR-1602
predicted it would be: it is algebra over a carrier, and nothing in it is an
estimate.**

## The mutation table

Seven mutants, each **RUN** — one edit, rebuild, the whole `top_frame::` suite,
recording which tests die — driven by a script that restores the file and
verifies the restore by **SHA-256** before the next mutant, so no mutant is on
disk for any other build. Baseline: 11 passed, 0 failed.

| # | mutation | tests killed |
|---|---|---|
| MUT-0 | none (baseline) | **0 of 11** |
| MUT-A | the frame law's two sides exchanged in the **record field** — `le (sup (fun n => inf a (f n))) (inf a (sup f))` | **11 of 11** |
| MUT-B | the ball radius is `1/k` instead of `1/(k+1)` (divides by zero at `k = 0`) | **11 of 11** |
| MUT-C | `the_frame_law_slot_is_load_bearing` is handed the **correct** `Top.Opens.frame_le` instead of the wrong-typed `Top.Opens.le_refl` | **exactly 1** — itself |
| MUT-D | the radius control's `degenerate` flag is ignored, so both halves ask the same question | **exactly 1** — itself |
| MUT-E | the separation control's `reversed` flag is ignored | **exactly 1** — itself |
| MUT-F | the reduction probe's `honest` flag is ignored | **exactly 1** — itself |
| MUT-G | `Top.Opens.inf s t` forgets its second argument (`And (s q k) (s q k)`) | **11 of 11** |

**MUT-C through MUT-F are the discriminating rows.** Each kills exactly one test
and it is the intended one, so those four controls distinguish the right answer
from a wrong one at the same slot and would not survive being handed the right
answer. They are what makes `the_frame_law_slot_is_load_bearing`,
`the_ball_radius_must_carry_the_plus_one`,
`ball_separation_needs_the_hypothesis_in_the_right_direction` and
`the_ball_frame_reduction_probe_is_not_vacuous` evidence rather than decoration.

**MUT-A, MUT-B and MUT-G are reported as what they are: not discriminating.**
All three mutate the *prelude*, one bad declaration poisons the shared build, and
every test that touches the memoised environment dies with it. That is exactly
ADR-1602 §6's MUT-E finding recurring one shelf later, and the lesson it drew
applies here verbatim: **any future mutation testing against this record has to
mutate the instance arguments or the tests, not the field shapes or the
definitions, or it will keep measuring the same 11.** The three rows are still
worth having — they establish that the field, the radius and `inf`'s second
argument are each load-bearing *at build time* — but they attribute nothing, and
the number 11 in those rows must not be read as "11 checks caught it".

MUT-G is the sharpest of the three for a different reason. `Top.Opens.inf` is a
`Definition`, and **the trusted gate cannot tell a `Definition` is wrong**: `fun
s t q k => And (s q k) (s q k)` has exactly the right type. What refuses it is
`Top.Opens.inf_le_right`, whose statement is the only thing in the file that
mentions `inf`'s second argument in a position the kernel has to check. So the
guard against a wrong meet is not the definition and not the record — it is one
theorem, and if that theorem were deleted the mutant would be admitted silently.

## Two shared files this lane repaired in passing

Both are the same defect, and both are the "prose hunks are not additive" hazard
landing in code:

- `examples/shape_search.rs` carried **two copies** of its coverage sentence and
  of its `--include-constructed` usage line, one ending `… and intspace` and one
  ending `… and rn`. Two lanes each appended their group to the same line and a
  "keep both sides" resolution kept both halves, so the tool documented two
  different, each-incomplete group lists. Collapsed into one line naming all
  seven.
- `scripts/validate-facts.py`'s `KERNEL_THEOREM_RE` carries the same duplication
  (`…|Metric|IntSpace|` and `…|Metric|RN|` on consecutive lines). Here it is
  harmless — a regex alternation is a union, so both namespaces work — so this
  lane **added its own line rather than restructuring a shared regex mid-flight**
  and records the duplication instead of silently collapsing it.

## Consequences

- Reviewer 06's topology shelf gains a pointfree carrier and a real instance, so
  ADR-1602's fourth recommendation is executed rather than pending.
- W2-21's dependency on W0-3 is discharged: the decision was already made, and
  building against it cost no new decision.
- Reviewer 05's manifolds still need more than this (charts need subspaces, and
  subspaces need `Subtype` — ADR-1613's route through `metric/subspace.rs` is
  the metric-side answer and has no frame-side analogue yet).
- **A standing rule from the pairing finding**: before encoding a compound index
  into `Nat`, check whether the encode/decode lemmas fall inside a held-out
  family. Two of the three natural encodings in this kernel (`Nat.pair`,
  `Nat.avg`) do.

## Related

- [ADR-1602](adr-1602-the-metric-layer-first-then-pointfree-and-not-open-sets.md)
  — the decision this executes.
- [ADR-1588](adr-1588-a-setoid-flavored-alg-spine-for-creal.md) — the
  `declare_record` machinery reused unchanged.
- [ADR-1612](adr-1612-the-integral-is-primitive-and-measure-is-derived-predicatively.md)
  — the predicativity constraint that makes the join countable.
- [ADR-1624](adr-1624-a-subset-is-a-predicate-because-the-split-law-has-to-be-refl.md)
  — the `Nat → Bool` subset representation this carrier could not use.
- ADR-1060 / ADR-1220 — why `Nat.pair` and `Nat.unpairLeft` carry no theorems.
