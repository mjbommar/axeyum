# ADR-1613: dependent pairs are an ordinary inductive, and the universe guard never refused them

Status: proposed
Date: 2026-09-04
Lane: `sigma-subtype`
Roadmap: W0-5 (the fifth Wave-0 decision) — the blocker ADR-1595, ADR-1602 and ADR-1612 each hit independently

Index-summary: three ADRs in one day recorded the same obstruction —
`Sigma` and `Subtype` are absent from the kernel — and a fourth (ADR-1606)
declined a design for it. The question was whether the absence was an
oversight or ADR-1495's constructor-field universe guard refusing a
`Sort (max u v)` result. **It was an oversight.** The guard rejects a field
whose universe is strictly ABOVE the family's result universe, and every
field of a dependent pair sits at or below it: `u ≤ max u v` and
`u ≤ max 1 u` are discharged symbolically by `Kernel::level_leq`, with no
instantiation and no weakening. `Sigma`, `PSigma` and `Subtype` are declared
in the logic prelude through the ordinary `add_inductive` gate, with
projections, defining equations and eta as theorems — **zero axioms**. The
deciding measurement was to re-test the three blocked sites, and the count is
**3 of 3**: the metric subspace, the L¹-ready bundled carrier, and — the one
that was supposed to be hard — the first isomorphism theorem restated as
`G/ker f ≅ Im f` between two `AlgS.Group` objects. Fourteen of the image
group's fifteen fields are free, because `Subtype.val` ι-reduces; the whole
cost is three membership proofs. `Fin` was NOT added: `Nat.Fin` already
exists, already in the subtype form.

Index-status: proposed

## Context

Three ADRs, all dated 2026-09-04, hit the same wall from three different
directions:

- **ADR-1595** (`quotients stay setoids`) found that the classical statement
  of the first isomorphism theorem, `G/ker f ≅ Im f`, is an isomorphism
  between two **group objects**. The quotient side was already available —
  `AlgS.Hom.quotient` keeps `G.carrier` and changes only `equiv`, so no
  `Quot.sound` is needed. The image side was blocked, and
  `structures_setoid.rs` records why verbatim: it needs a carrier
  `{y : H.carrier // ∃ a, H.equiv (f a) y}`, "and this kernel has no
  `Subtype` and no `Sigma`".
- **ADR-1602** (`metric-first topology`) found that a **subspace** needs the
  same thing: `Metric.dist` is total on its carrier, so a subspace's distance
  is the ambient one *restricted*, and a restriction needs a carrier built
  from a predicate. W2-10 was split because of it, and every notion in
  `metric/continuity.rs` and `metric/compactness.rs` comes in a relativized
  `*On P` form as the workaround.
- **ADR-1612** (`the integral is primitive`) found that **L¹ as a completion**
  needs `Sigma` to bundle an integrability witness into a carrier, because
  `Metric.dist` is total but `IntSpace.Integrable` is a side condition — and,
  decisively, `Integrable` is `Sort 1` **data**, not a `Prop`.

**ADR-1606** (`ℝⁿ is a function carrier`) is the fourth: it rejected a
`Fin n → CReal` carrier on the ground that the subtype route is closed.

Dependent pairs are not an axiom. `Sigma (α : Sort u) (β : α → Sort v) :
Sort (max u v)` is an ordinary one-constructor inductive, and nothing in the
setoid discipline (ADR-1595) or the predicativity constraint (ADR-1612)
forbids one. So the absence had exactly two possible causes: nobody had tried,
or ADR-1495's constructor-field universe guard
(`KernelError::ConstructorFieldUniverseTooBig`) refuses a `max`-valued result
level. **This ADR's method was to find out by trying.**

## Decision

**Declare `Sigma`, `PSigma` and `Subtype` in the logic prelude, through the
ordinary `add_inductive` gate, and leave ADR-1495's guard exactly as it is.**

```text
inductive Sigma.{u,v} (α : Type u) (β : α → Type v) : Type (max u v)
  | mk : (fst : α) → (snd : β fst) → Sigma α β
inductive PSigma.{u,v} (α : Sort u) (β : α → Sort v) : Sort (max u v)
  | mk : (fst : α) → (snd : β fst) → PSigma α β
inductive Subtype.{u} (α : Sort u) (p : α → Prop) : Sort (max 1 u)
  | mk : (val : α) → (property : p val) → Subtype α p
```

plus `Sigma.fst`/`Sigma.snd` (dependent), `Subtype.val`/`Subtype.property`,
their defining equations `fst_mk`/`snd_mk`/`val_mk`, and `mk_eta` for both.
Eighteen names, all in `crates/axeyum-lean-kernel/src/sigma_prelude.rs`, every
one with an empty `Kernel::axiom_footprint`.

### Why the guard does not fire, stated so it cannot be weakened by accident

ADR-1495's guard exists because an inductive that stores its own universe
(`U : Sort 1` with `mk : Sort 1 → U`) plus large elimination makes `Sort u` a
retract of an inhabitant of `Sort u` — the `Type : Type` precondition for
Girard's paradox. It rejects a constructor field whose type's universe is
**strictly above** the family's own result universe, `Prop` exempt.

Every field of every family above sits **at or below** its result universe,
and `Kernel::level_leq` discharges each obligation *symbolically*:

| family | result universe | field | field universe | why `≤` holds |
| --- | --- | --- | --- | --- |
| `Sigma.{u,v}` | `Sort (max u v + 1)` | `α : Type u` | `Sort (u+1)` | `u ≤ max u v` |
| | | `β fst : Type v` | `Sort (v+1)` | `v ≤ max u v` |
| `PSigma.{u,v}` | `Sort (max u v)` | `α : Sort u` | `Sort u` | `u ≤ max u v` |
| | | `β fst : Sort v` | `Sort v` | `v ≤ max u v` |
| `Subtype.{u}` | `Sort (max 1 u)` | `α : Sort u` | `Sort u` | `u ≤ max 1 u` |
| | | `p val : Prop` | `Sort 0` | `0 ≤ anything` |

Nothing here stores its own universe. **The guard and a dependent pair are
different shapes, and this ADR only measures that they are.** The guard is not
touched, not relaxed, and not made conditional.

### `PSigma` is the measured asymmetry, and it is not a defect

`add_mutual_inductive` grants large elimination when the result universe is
*provably* non-zero. `Sigma`'s is a successor and `Subtype`'s is a `max` with
a literal `1` in it, so both get a recursor with a fresh motive level:
`Sigma.rec.{w,u,v}`, `Subtype.rec.{w,u}`.

`PSigma.{u,v} : Sort (max u v)` does not, because `max u v` **is** zero at
`u = v = 0`: `PSigma.{0,0}` genuinely is a `Prop`, and a recursor eliminating
into an arbitrary `Sort w` would be unsound at that instantiation — it would
be `Exists` with a `fst` projection, which is exactly the large-elimination
hole `Exists` is denied. So `PSigma.rec.{u,v}` eliminates only into `Prop`,
and **`PSigma` gets no projections**. It is declared anyway, because it is the
right carrier for a pair whose first component may be a proposition and
because recording the asymmetry is worth more than hiding it: a consumer that
wants projections uses `Sigma` (data/data) or `Subtype` (data/proof).

The recursor universe-parameter counts — 3, 2, 2 — are asserted in
`sigma_prelude_tests` precisely because that count IS the kernel's own
per-family verdict, not the author's belief about it.

### `Fin` is deliberately not added

`Nat.Fin` already exists (`nat_prelude/finite.rs`), and it is *already the
subtype form*: `⟨val : Nat, isLt : val < n⟩`, a `Type 0` family with a data
field and a dependent `Prop` field over it, with `Nat.Fin.val`,
`Nat.Fin.isLt` and the evaluation theorem `Nat.Fin.val_mk`. A second, generic
`Fin` would be a duplicate carrier with no consumer. This is also the clearest
evidence that the guard was never the obstruction: **the kernel has admitted
two specializations of exactly this shape all along** — `Nat.Fin`, and `CReal`
(`⟨seq, regular⟩`). What was missing was only the universe-polymorphic form.

## The deciding measurement: 3 of 3

Each of the three ADRs named a statement it could not write. Each is now
written, admitted by the trusted gate, and axiom-free.

### (a) ADR-1595 — the first isomorphism theorem between two group objects

`crates/axeyum-lean-kernel/src/nat_prelude/image_group.rs`.

```text
AlgS.Hom.imageCarrier G H f := Subtype.{1} H.carrier (AlgS.Hom.image G H f)
AlgS.Hom.imageGroup   G H f fCongr fMul : AlgS.Group
AlgS.Hom.induced      G H f fCongr fMul : G.carrier → imageCarrier G H f
AlgS.Hom.firstIsoClassical G H f fCongr fMul :
    (∀ a b, Q.equiv a b ↔ I.equiv (u a) (u b))                   -- well-defined AND injective
  ∧ (∀ a b, I.equiv (u (Q.op a b)) (I.op (u a) (u b)))           -- a homomorphism
  ∧ (∀ y : I.carrier, ∃ a : Q.carrier, I.equiv (u a) y)          -- surjective
```

with `Q := AlgS.Hom.quotient …` and `I := AlgS.Hom.imageGroup …`, **both of
type `AlgS.Group`**. That is `G/ker f ≅ Im f`.

**Fourteen of the image group's fifteen fields are free.** `Subtype.val`
ι-reduces on `Subtype.mk`, so `(op x y).val` is definitionally
`H.op x.val y.val`, `e.val` is `H.e`, `(inv x).val` is `H.inv x.val` — and
`assoc`, `identL`, `identR`, `invL`, `invR`, `opCongr`, `invCongr` and the
three equivalence laws each reduce to exactly the statement `H`'s own field
already proves. **The entire cost is three membership proofs**, one `Exists`
elimination plus one `H.equivTrans` each:

| slot | obligation | proof |
| --- | --- | --- |
| `e` | `∃ a, H.equiv (f a) H.e` | witness `G.e`, `AlgS.Hom.mapOne` |
| `op` | `∃ a, H.equiv (f a) (H.op x.val y.val)` | witness `G.op a b`, `fMul` then `H.opCongr` |
| `inv` | `∃ a, H.equiv (f a) (H.inv x.val)` | witness `G.inv a`, `AlgS.Hom.mapInv` then `H.invCongr` |

The three eliminations are legal because every target is a `Prop`
(`AlgS.Hom.image` is `Prop`-valued). This is worth stating because it is *not*
free in general — `Exists` in this kernel has no large elimination, and that
is exactly the wall ADR-1595's `Type`-valued constructions hit.

The three conjuncts are then nearly free: conjunct 1 is
`Iff.intro (fun h => h) (fun h => h)` because both sides reduce to
`H.equiv (f a) (f b)`; conjunct 2 is `fMul` verbatim; conjunct 3 is
`Subtype.property`, because `y.property` IS `∃ a, H.equiv (f a) y.val`.

**That is the finding, not a disappointment.** It is what "the obstruction was
the carrier, not the mathematics" means, and it is measured rather than
asserted: the load-bearing test compares the two statements' rendered types and
requires that `firstIsoClassical` mentions `imageGroup` and `induced` while the
pre-existing `firstIso` mentions **neither**, with both mentioning `quotient`
so the comparison is between two real statements.

**The setoid subtlety ADR-1595 flagged is real and is handled as it predicted:**
the subtype's equivalence is *inherited* — `I.equiv x y := H.equiv x.val y.val`
— not `Eq` on the subtype. Nothing anywhere claims two elements of `Im f` with
equivalent values are equal.

### (b) ADR-1602 — the metric subspace

`crates/axeyum-lean-kernel/src/metric/subspace.rs`.

```text
Metric.subspace (M : Metric) (P : M.carrier → Prop) : Metric
  carrier := Subtype.{1} M.carrier P
  dist    := fun x y => M.dist x.val y.val
Metric.subspace_carrier : (Metric.subspace M P).carrier = Subtype M.carrier P
Metric.subspace_dist    : (Metric.subspace M P).dist x y = M.dist x.val y.val
Metric.crealIntervalSpace : CReal → CReal → Metric
```

All eleven non-carrier fields are `M`'s own applied to `Subtype.val`, for the
same ι-reduction reason as (a), so there is **no congruence obligation, no side
condition, and no hypothesis on `P`** — a subspace of a metric space is a
metric space for any predicate, including the empty one, because none of the
twelve fields asserts the carrier is inhabited. Both equations are `Eq.refl`:
"the distance is the ambient one restricted" is now a definitional fact of the
kernel rather than a sentence in a design note.

`Metric.crealIntervalSpace a b := Metric.subspace Metric.creal
(Metric.Interval a b)` is the first instance, and is why this is not an empty
generality: `Metric.Interval` was usable only as the `P` of a `*On` form and is
now a metric space that `Metric.Complete`, `Metric.Cauchy` and the rest of the
layer apply to directly.

**W2-10's subspace half is open, not blocked on anything else.** What this ADR
does *not* do is migrate the existing `*On` forms; `Metric.CompactOn`,
`Metric.TotallyBoundedOn`, `Metric.CompleteOn` and the continuity family keep
their relativized statements. Whether they should be restated over
`Metric.subspace` is a separate decision with real proof cost, and only its
*expressibility* is established here.

### (c) ADR-1612 — the bundled carrier

`crates/axeyum-lean-kernel/src/intspace/bundled.rs`.

```text
IntSpace.Bundled S := Sigma.{0,0} S.carrier (IntSpace.Integrable S)
IntSpace.bundledIntegral : Π S, S.Bundled → CReal        -- ∫ as a TOTAL function
IntSpace.bundledIntegral_bundle : bundledIntegral (bundle f h) = integral f h
IntSpace.bundledDist : Π S, S.Bundled → S.Bundled → CReal
```

This needs `Sigma` and **not** `Subtype`: `IntSpace.Integrable` is `Sort 1`
data, not a `Prop` — which is itself a consequence of `Sigma` having been
absent (ADR-1612 chose `Sort 1` because an integrable set could not be
bundled). Both components are `Type 0`, so the pair is `Sort 1`: **exactly the
universe `declare_record` fixes a carrier at**, which is the claim the site
turns on and is asserted against `Sort 2` as its negative control.

`IntSpace.integral` takes two arguments and is therefore not a function of the
carrier; on the bundled carrier it is one, and
`bundledIntegral_bundle` (an `Eq.refl`) says the bundle loses nothing.

**What is NOT built, stated precisely.** `bundledDist` is `|∫b₁ − ∫b₂|`. It is
a genuine `Bundled S → Bundled S → CReal` — the shape `Metric.dist` demands,
which was unwritable before — and it is **not the L¹ seminorm**, which is
`‖f − g‖₁ = ∫|f − g|`. Nor is it claimed to satisfy the metric axioms: it does
not separate points. The L¹ seminorm stays blocked, and on something this ADR
does not touch: `IntSpace` has `fadd` and `fscale` (so `f − g` is expressible)
but **no absolute value on the carrier**, and no integrability witness for
`|f|` given one for `f`. That is the lattice/`|·|`-closure gap `intspace.rs`
already names as standing between `IntSpace` and a Petrakis–Zeuner
pre-integration space. `Sigma` was one of the two missing pieces; the other is
named and unchanged.

## Consequences

- The trusted base is unchanged in kind: eighteen new logic-prelude names, all
  inductives, definitions and theorems, **no axiom**. The three consuming
  layers add fifteen more, also axiom-free.
- `LogicPrelude` gains one registry field (`sigma: SigmaNames`), so
  `crates/axeyum-py/src/kernel/prelude_fields.rs` is regenerated: the `logic`
  table goes 86 → 109 names.
- ADR-1606's stated ground for rejecting a `Fin n → CReal` carrier ("the
  subtype route is closed") **no longer holds**. This ADR does not reopen that
  decision — ADR-1606 has other reasons, and re-deciding ℝⁿ's carrier is a
  separate question — but the record should not keep citing a closed route
  that is now open.
- `Exists` is still the odd one out: it is `Prop`-valued with a non-`Prop`
  field that does not appear in its result, so it has no large elimination and
  no `fst`. Where a *data* first component is wanted, the answer is now `Sigma`
  or `Subtype`, and (a) is the worked example of converting such a use.

## Alternatives considered

- **Weaken ADR-1495's guard.** Not needed, and it would have been the wrong
  answer even if it had been: the guard never fired. Had it fired, this ADR
  would have recorded the exact rejection and recommended a separate,
  soundness-focused decision — never a change made in passing.
- **A bespoke `Image` inductive per site.** Rejected: the reason fourteen of
  fifteen fields of the image group are free is precisely that `Subtype.val`
  ι-reduces on `Subtype.mk`, so a one-off carrier would have re-paid that cost
  at every site and shared nothing between (a), (b) and (c).
- **An `AlgS.Iso` record**, bundling the map, its inverse and the round trips.
  Deferred deliberately: an isomorphism notion should be decided once for the
  whole `AlgS` spine, not invented for one theorem. `firstIsoClassical`'s three
  conjuncts are the unbundled form of exactly that, stated where it can be
  checked today.
- **Threading the new `AlgS.Hom.*` names into `NatPrelude`.** Rejected,
  following the `AlgS.Poly.*` precedent (ADR-1609): nothing later in the
  prelude consumes them and widening `StructuresSExtraNames` would change a
  struct that `axeyum-py`'s generated field registry mirrors.

## An unrelated finding, recorded because it is a live gap

`scripts/gen-py-prelude-fields.py` matches a prelude field with
`^\s{4}pub (\w+): ([A-Za-z0-9_<>, ]+),$`. A **path-qualified** field type
contains `:` and so does not match at all — the line is silently skipped, which
is exactly the "silent amputation" that script's own docstring says must never
happen again (ADR-1512, `8dd580a1c`). Measured 2026-09-04 while writing this
ADR: a `pub sigma: crate::SigmaNames` field on `LogicPrelude` was dropped and
the generator still printed `logic=86`, its pre-change count. Writing the field
as a bare `SigmaNames` fixed it here (`logic=109`).

**The gap is still open for `ComplexPrelude.poly: poly::PolyNames`**, whose
fields are absent from the Python surface today. Fixing it is not a one-line
regex change: `PolyNames` is defined in **both** `complex/poly.rs` and
`nat_prelude/polynomial_setoid.rs`, which is why that field is written
qualified, so the generator would have to resolve the module path relative to
the declaring file rather than by scanning for the bare name. That is a change
to a script another lane owns, and it is recorded here rather than made.
