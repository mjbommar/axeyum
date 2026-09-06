# ADR-1657: the surgery recurses on the index and the fold recurses on the length

Status: proposed
Date: 2026-09-06
Lane: `invariance-of-dimension`
Roadmap: W3-2 (vector spaces over an abstract field, bases, dimension — third slice)

Index-summary: The obstruction
[ADR-1627](adr-1627-a-constructive-field-has-an-existential-inverse-because-creal-cannot-have-a-functional-one.md)
named — index surgery over a coefficient family, blocked because `Nat.lt` and
`Nat.beq` are undeclared at the `AlgS` build position — is **removed**.
`AlgS.Index.{le, removeAt, insertAt}` are built from `Nat.rec` alone (route
(b)); route (a), threading `Nat.lt`/`Nat.beq`/`Nat.ble` in as `deps`, **does
not exist as stated**: a `dep` is a `NameId` already in the environment and
those four are declared ~60 lines *later* in `nat_prelude.rs`, so route (a) is
a reordering of the shared prelude build, not a parameter. Seventeen
declarations land (3 definitions + 14 theorems), **every one admitted on first
submission except one, every footprint empty**, ending in
`AlgS.Exchange.linComb_removeAt_insertAt` — the split
`linComb c v (succ n) ~ (linComb (removeAt i c) (removeAt i v) n) · (c i • v i)`
for `i ≤ n`, which is the lemma ADR-1627 sized. The measured finding is an
**asymmetry**: the surgeries recurse on the INDEX, `linComb` recurses on the
LENGTH, and only the length induction closes — the `removeAt` form leaves
`removeAt (succ i') c n'` stuck on a variable at every step, so the `insertAt`
form is what is proved and the `removeAt` form is a corollary one `trans` away.
**The Steinitz exchange itself did NOT land**, and the obstruction is not
index surgery any more: it is that the exchange step needs
`Σ c_i w_i # 0 → ∃ i, c_i # 0`, which for a general constructive field needs
`AlgS.Field.IsTight` — deliberately NOT a field of the record (ADR-1627), and
a property `CReal` cannot prove. Invariance of dimension over this shelf is
therefore a theorem about **tight** fields, and ℝ is not one of them.
Index-status: proposed

## Context

[ADR-1609](adr-1609-polynomials-modules-and-subgroups-over-the-setoid-spine.md)
landed `AlgS.Module.*` with a basis layer — `linComb`, `coeffAgree`, `spans`,
`linearIndependent`, `isBasis`.
[ADR-1627](adr-1627-a-constructive-field-has-an-existential-inverse-because-creal-cannot-have-a-functional-one.md)
landed `AlgS.Field`, `AlgS.VectorSpace`, `solve_smul` (the atomic Steinitz
step: `a # 0 → a•v ~ w → ∃ c, v ~ c•w`) and `basis_zero_unique` — invariance of
basis number **at length zero**. It stopped there and sized the general
theorem, naming one obstruction:

> the Steinitz exchange rewrites the *indexing* of a coefficient family
> (replace `v i` by `w`, reindex the rest), and at the `AlgS` build position
> `Nat.lt`, `Nat.beq` and every `sumRange` reindexing lemma are undeclared

That is a real obstruction and this lane's first job was to remove it. Its
second job — the Steinitz exchange and invariance of dimension — is where the
lane stopped, for a reason that is not the one anybody expected.

## Decision

**1. Index surgery is built from `Nat.rec` at the `AlgS` build position
(route (b)). Route (a) — threading `Nat.lt`/`Nat.beq`/`Nat.ble` in as `deps` —
is not a route.**

The brief offered two routes and asked for a measurement. The measurement is
that route (a) does not exist in the form proposed. A `dep` in this codebase
(`ModuleDeps`, `FieldDeps`, `PolyDeps`, `SubgroupDeps`) is a `NameId` of a
declaration **already in the environment**. `Nat.le`, `Nat.lt`, `Nat.beq` and
`Nat.ble` are not: `nat_prelude.rs` interns them at the
`kernel.name_str(nat, "le")` call, roughly sixty lines *after* the whole `AlgS`
block runs. Making them available to `AlgS` means moving either the `Nat`
arithmetic block up or the `AlgS` block down — a reordering of the shared
prelude build, which the
[2026-08-27 architecture review](../11-design-review/2026-08-27-architecture-review.md)
names as the recurring source of phase-order bugs, and which every other lane's
build shares. That is not a `dep`; it is a refactor with a blast radius, and it
buys nothing route (b) does not already give.

Route (b) is additive, needs no dep at all, and has a property route (a) would
not have had: **all ten defining equations are ι-reductions**, so the lemmas
above them are `Eq.refl`.

```text
le zero n                        ≡ True
le (succ i) zero                 ≡ False
le (succ i) (succ n)             ≡ le i n
removeAt α zero v j              ≡ v (succ j)
removeAt α (succ i) v zero       ≡ v zero
removeAt α (succ i) v (succ j)   ≡ removeAt α i (fun t => v (succ t)) j
insertAt α zero w v zero         ≡ w
insertAt α zero w v (succ j)     ≡ v j
insertAt α (succ i) w v zero     ≡ v zero
insertAt α (succ i) w v (succ j) ≡ insertAt α i w (fun t => v (succ t)) j
```

The shape that makes this work: `removeAt`/`insertAt` recurse on the index
returning a family **transformer** (`(Nat → α) → (Nat → α)`), not a family, so
the recursive call can be made at the shifted family `fun t => v (succ t)`.
A motive of `fun _ => Nat → α` does not admit that call.

**2. The surgeries recurse on the INDEX; `linComb` recurses on the LENGTH; only
the length induction closes. The `insertAt` form is proved and the `removeAt`
form is a corollary.**

This is the finding. `linComb R M smul c v n` folds on the right —
`linComb … (succ j) ≡ M.op (linComb … j) (smul (c j) (v j))` — so an induction
over it peels `n`. `removeAt (succ i')` peels `i`. Attempting the
`removeAt` statement by induction on the length leaves
`removeAt (succ i') c n'` applied to a *variable* `n'`, where the inner
`Nat.rec` is stuck: the term does not reduce and neither side of the goal can
be brought to the other. The `insertAt` form does close, because at the top
index `AlgS.Index.le_succ_cases` splits exactly the two cases the fold
distinguishes:

- `le i n'` — the inserted value is strictly inside the prefix, the top term is
  `c n'` shifted (`insertAt_above`), the induction hypothesis applies at the
  **same** families, and one `op_swap_last` finishes it;
- `i = succ n'` — the inserted value IS the top term (`insertAt_at`) and the
  whole prefix is untouched (`insertAt_below`), so `linComb_ext_below` closes
  it with no induction hypothesis at all.

The `removeAt` form then costs one `trans`, because
`AlgS.Index.insertAt_removeAt` is **unconditional and pointwise**: deleting
index `i` and putting `v i` back rebuilds the family at every index, with no
order side condition. So the split inherits its bound from the sum's length and
not from the surgery.

**3. Invariance of dimension over this shelf is a theorem about TIGHT fields,
and the obstruction is no longer index surgery.**

The Steinitz exchange did not land. Its remaining obstruction is stated here
because it is a mathematical fact about the shelf and not a budget note.

The exchange step needs: `u_j ~ Σ_{i<n} c_i w_i`, and some `c_i` apart from
zero, so that `solve_smul` can solve for `w_i`. Independence of `u` gives
`¬(∀ i, c_i ~ 0)` — a negation. Constructively, `¬(∀ i, c_i ~ 0)` does **not**
yield `∃ i, c_i # 0`. Cotransitivity (`AlgS.Field.apartCotrans`, field 25) does
not help: it turns an apartness into a disjunction, but there is no apartness
to start from — `AlgS.CommGroup` carries no apartness relation at all, so
"`u_j` is apart from zero" is not even expressible on the vector side.

The route that does work runs the whole bound as a refutation. Prove
`natLe (succ n) m → False` and resolve it with `AlgS.Index.le_dichotomy`; then
the inner argument may assume `∀ i, ¬(c_i # 0)` and needs to conclude
`∀ i, c_i ~ 0`. That step is exactly **`AlgS.Field.IsTight`**, which ADR-1627
deliberately made a predicate and not a record field, because ℚ proves it and
`CReal` cannot prove it from anything in the tree.

So the honest statement of the general theorem on this shelf is

```text
AlgS.Field.IsTight F -> IsVectorSpace F M smul ->
  linearIndependent u m -> spans w n -> AlgS.Index.le m n
```

and its instantiation at ℝ is blocked by the same missing `CReal.lt`
introduction rule ADR-1627 recorded, not by anything about dimension.
`AlgS.Index.le_dichotomy` was proved in this lane specifically so that the
refutation form can be resolved back to a bound; it is the only route, because
this shelf has no `Decidable` instance for its order.

## Evidence

Every number below was read from a run, not from source text.

**Seventeen declarations, in `AlgS.Index` and `AlgS.Exchange`.** Rendered types
from `target/release/examples/nat_theorem_inventory` (which builds the whole
`Nat` prelude and dumps `render_lean` of the admitted type):

| name | kind |
|---|---|
| `AlgS.Index.le` | definition |
| `AlgS.Index.removeAt` | definition |
| `AlgS.Index.insertAt` | definition |
| `AlgS.Index.le_zero_eq` | theorem |
| `AlgS.Index.le_refl` | theorem |
| `AlgS.Index.le_succ_right` | theorem |
| `AlgS.Index.le_dichotomy` | theorem |
| `AlgS.Index.le_succ_cases` | theorem |
| `AlgS.Index.insertAt_at` | theorem |
| `AlgS.Index.insertAt_below` | theorem |
| `AlgS.Index.insertAt_above` | theorem |
| `AlgS.Index.removeAt_insertAt` | theorem |
| `AlgS.Index.insertAt_removeAt` | theorem |
| `AlgS.Exchange.op_swap_last` | theorem |
| `AlgS.Exchange.linComb_ext_below` | theorem |
| `AlgS.Exchange.linComb_insertAt` | theorem |
| `AlgS.Exchange.linComb_removeAt_insertAt` | theorem |

`nat_theorem_inventory -- AlgS.Index.` prints 10 theorems and
`-- AlgS.Exchange.` prints 4; the three definitions are not theorems and do not
appear there, which is the documented behaviour of that example.

**Sixteen of seventeen were admitted on first submission.** The one rejection
was `linComb_removeAt_insertAt`, and it was not a mathematical error: `symm`
was applied at `(lhs, mid)` where `linComb_ext_below` supplies `equiv mid lhs`.
`TypeMismatch { expected: ExprId(287872), got: ExprId(287898) }` named nothing,
so a per-declaration harness was added
(`vector_space_steinitz_tests::each_result_is_admitted_on_its_own`) which
declares each result on its own in dependency order — the bundled `expect`
cannot say which declaration a rejection came from, and one bad declaration
poisons the shared build.

**Every footprint is empty**, asserted in
`the_index_layer_is_axiom_free` and `the_exchange_layer_is_axiom_free`, each of
which asserts `Environment::get(name).is_some()` FIRST, because a missing name
also returns an empty footprint.

**Evaluation tests, at small discriminating arguments.** `insertAt 2 3 id` must
enumerate `0, 1, 3, 2, 3`: the inserted value `3` is deliberately a value the
identity family already takes, so the test cannot pass by matching the wrong
occurrence, and index 3 must be the shifted `2`, which no shift-free or
shift-by-two reading produces.

**Mutation, all RUN.** Baseline `cargo test --release -p axeyum-lean-kernel
--lib -- nat_prelude::vector_space`: 25 tests, 25 passed, exit 0. Each mutant
was applied to the source, built, run against the same 25-test collection, and
restored byte-for-byte (`git status` clean afterwards).

| mutant | change | outcome |
|---|---|---|
| A | `removeAt`'s base case off by one: `v (succ j)` → `v j` | **killed 18 of 25** |
| B | the split lemma's bound reversed: `le i n` → `le n i` | **killed 7 of 25** |
| C | `le (succ i) zero` returns `True` instead of `False` | **killed 18 of 25** |

The survivors are the correct ones in each case. Mutant B is confined to
`AlgS.Exchange` (7 tests) because the reversed bound is rejected by the kernel
where the split hands its hypothesis to `linComb_insertAt`, and nothing in
`AlgS.Index` depends on it. Mutants A and C change a **`Definition`**, which
the trusted gate cannot object to — the mutated `removeAt` still has exactly
the right type — so their kills come from the evaluation tests and from the
downstream theorems whose `Eq.refl` stops holding. That split is the point: a
definition mutant is only caught by evaluation, and this module has evaluation
tests because of it.

## Alternatives

**Route (a), moving the `Nat` arithmetic block above `AlgS`.** Rejected: see
Decision 1. It is not a `dep`, it is a reordering of a build every lane shares,
and route (b) costs less and reduces better.

**Universe-polymorphic `removeAt`/`insertAt` over `Sort u`.** Rejected. Every
family this library forms is `Nat → <record>.carrier`, and a record carrier is
`Sort 1` by construction (`structures.rs`'s `carrier_field`), so a `Sort u`
version buys nothing and would need `imax` levels on four `Nat.rec` motives.
The definitions take an explicit `α : Type` instead.

**Proving the `removeAt` split directly by induction.** Rejected by
measurement: the recursion directions do not match (Decision 2). This is the
finding, not a preference.

**`linComb_ext_below` over `equiv` hypotheses instead of `Eq`.** Rejected.
Every consumer gets its pointwise agreement from an `AlgS.Index` lemma, and
those conclude `Eq` because the surgeries are ordinary functions. Weakening the
lemma to `equiv` would have forced every caller to transport first.

**Adding tightness to the `AlgS.Field` record so the exchange lemma needs no
extra hypothesis.** Rejected, and this is ADR-1627's decision, not a new one:
it would make ℝ not a field. The consequence — invariance of dimension is a
theorem about tight fields — is recorded rather than engineered away.

## Consequences

Easier:

- The index calculus is now available to any `AlgS` shelf at the same build
  position, with defining equations that reduce. `AlgS.Index.le` in particular
  is the first order relation that exists there at all.
- `AlgS.Exchange.linComb_removeAt_insertAt` is the reindexing step every
  Gaussian-elimination-shaped argument over `linComb` needs, not only Steinitz.
- `AlgS.Exchange.op_swap_last` is a plain `AlgS.CommGroup` fact and is reusable
  off the module shelf, the way `AlgS.idem_eq_e` is.

Harder / next:

- The Steinitz exchange still needs three things this lane did not build:
  `linComb_smul` and `linComb_add` (linearity of the fold, both straightforward
  `Nat.rec` inductions over `smulAdd`/`addSmul`), the one-step exchange
  (`spans w n` and `c i # 0` give `spans (insertAt i x (removeAt i w)) n`), and
  the outer induction in refutation form resolved by `le_dichotomy`.
- Whoever takes that on should state it with `AlgS.Field.IsTight` as a
  hypothesis from the start. Stating it without tightness is not a harder
  version of the same theorem; it is a different one, and this ADR's Decision 3
  is the reason.
- `AlgS.VectorSpace.dim` is not declared, and should not be until the exchange
  lands: a `dim` whose well-definedness is unproved is a name that asserts
  something the kernel has not checked.
