# ADR-1310: The aggregate absence is an inventory, not a law — and a finite sum needs a FOLD over its index set, not a type

Status: accepted
Date: 2026-08-31
Index-summary: Twelve documents state "this kernel has no `List`/`Finset`/`Prod`,
so a finite family is a function plus a bound" as a LAW; it is an INVENTORY.
`Nat.Pair` and `Nat.Primrec` were both declared this week, `add_inductive` is an
ordinary gate, and an inductive contributes **zero** rows to `axiom_footprint`
(`Inductive`/`Constructor`/`Recursor` are filtered out; `TRUSTED_KINDS` is
`{axiom, opaque, quotient}`). The decision is nonetheless to add NO aggregate:
`Nat.Fin` already exists with 4 declarations and **zero non-test consumers**, so
the development has already declined an indexed type once. The load-bearing
correction is different and is landed as a theorem — **a finite sum does not
need its index set to exist as a type, it needs a FOLD over the index set, and a
fold is a function.** `Int.sumMaps m n F` folds `Int.add` over every
`g : [0,m) -> [0,n)` by `Nat.rec` with a higher-order motive, and
`Int.prodRange_sumRange_expand` (the generalized distributive law, exactly the
Cauchy–Binet expansion step ADR-1135 called inexpressible) is admitted
axiom-free at symbolic `m`, `n`, `c`. So determinant multiplicativity is NOT
blocked by a missing aggregate. What blocks it is the alternating property and
the sign under a row swap at general `n`, which arrive after general-row
expansion (ADR-1135's law 3) and are ordinary cofactor inductions.
Index-status: accepted

## Context

Twelve documents and several lane briefs carry a sentence of this shape:

> There is no `List`, `Finset`, `Prod` or vector type. A finite family is a
> **function plus a bound**.

Sometimes as an observation, sometimes as a constraint that "is not negotiable"
and is "structural rather than a matter of effort". [ADR-1135](adr-1135-a-determinant-congruence-is-what-the-absence-of-funext-costs.md)
used it to close determinant multiplicativity:

> - The Leibniz route sums over permutations of `[0,n)`. ADR-1120 already
>   records that there is no type in which to write that sum […] and that is not
>   a gap to be filled by a lemma.
> - The Cauchy-Binet / multilinearity route expands `det (A*B)` as a sum over
>   *functions* `[0,n) -> [0,n)` […] the index set of the outer sum is a
>   function space, not a `Nat` range, so `Rat.sumRange` cannot express it.
> - The elementary-operations route […] needs an induction on a factorization
>   whose *length* is data this kernel has no way to carry.

This lane was opened to decide, with evidence, what the right aggregate is —
`List`, `Nat.Fin`-indexed functions, or `Prod` — and whether one of them
unblocks multiplicativity.

## Measurement 1: the absence is an inventory

The live inductive census is `True False And Or Iff Eq Exists Acc Bool Nat
Decidable`, `Nat.le`, `Nat.Fin`, `Nat.Pair`, `Nat.Primrec`, `Char`, `Str`, and
the carriers `Int Rat CReal Complex CPoint` plus three `CReal` predicates.
**`Nat.Pair` was declared 2026-08-29 and `Nat.Primrec` 2026-08-31** — the latter
an inductive `Prop` with seven constructors and a function-typed index. This
kernel adds inductives routinely.

`Kernel::add_inductive` (`inductive.rs:239`) is an ordinary gate:
`(name, uparams, num_params, ty, ctors)`, with the recursor auto-generated and
its own type `infer`-checked, and a strict Lean-4.30 positivity check
(`check_group_constructor_positivity`, `inductive.rs:1860`) that runs before any
provisional insert. Nothing about `List` or `Prod` would strain it.

## Measurement 2: an inductive costs NOTHING in the axiom ledger

`Kernel::axiom_footprint` (`lean_pp.rs:1297`) walks the dependency closure and
then filters:

```rust
matches!(
    self.environment().get(n),
    Some(Declaration::Axiom { .. } | Declaration::Opaque { .. } | Declaration::Quotient { .. })
)
```

`Inductive`, `Constructor` and `Recursor` are traversed and **discarded**.
`scripts/check-trust-closure.py:114` agrees (`TRUSTED_KINDS = {"axiom",
"opaque", "quotient"}`), and `examples/nat_axiom_inventory.rs:202` maps only
those three kinds and returns `None` for everything else.

So the brief's premise that "a new inductive is trusted surface" is **false as
the ledger accounts for it**. Two real costs remain, and neither is an axiom:

- The positivity checker and recursor self-check are inside the measured
  trusted CODE core (`scripts/check-kernel-trusted-core.py` names `inductive.rs`
  explicitly). Adding a type does not enlarge that; using it does not either.
- **An inductive `Prop` admits no evaluation test**, which is `primrec.rs`'s own
  caveat: a constructor with a transposed or weakened index type-checks exactly
  as happily as the intended one, and `axiom_footprint`, the prelude build and
  the environment-derived coverage assertion are all blind to it.

## Measurement 3: this kernel already ran the experiment, and declined

`Nat.Fin` exists. Declared 2026-08-23 in `nat_prelude/finite.rs:70`, one
parameter, one constructor `mk : Π (n val : Nat), Lt val n → Fin n`, with
`Fin.val`, `Fin.isLt`, `Fin.val_mk` and the generated `Fin.rec`. Four
declarations plus the recursor.

Measured today, references to any `Fin` name outside its declaring file and the
prelude's name registry:

```
grep -rn 'p\.fin\b|p\.fin_mk|p\.fin_val|p\.fin_is_lt|p\.fin_val_mk|\.fin_rec'
  -> 7 hits, ALL in nat_prelude_tests.rs
     (6 are inventory-list entries; 1 is a val_mk round-trip)
```

**Zero proofs consume it.** The whole finite-combinatorics apparatus built
*around* it — `Nat.injectiveOn`, `Nat.surjectiveOn`, `Nat.mapsInto`,
`Nat.injective_on_imp_surjective_on` (the pigeonhole), `Nat.restrict_injective`,
`Nat.restrict_maps_into` — is stated over plain `Nat → Nat` with bounded
quantifiers, in the same file, by the same lane. The module doc says why:
reasoning here is over bounded `Nat` quantifiers, never over `Fin n → X`.

That is the strongest evidence available on the question this ADR was opened
for. An indexed finite type was added, and the development that had the best
reason to use it did not.

## The actual correction, and it is not about types

The three "blocked" routes above share a premise that does not survive
inspection:

> **A finite sum needs its index set to exist as a type.**

It does not. A finite sum needs a **fold** over the index set, and a fold is a
function. `Rat.sumRange`/`Int.sumRange` fold over `[0,n)` because `Nat.rec`
gives that fold; nothing about the definition of a sum requires the index set to
be reified. For a function space, the fold is a *nested* one, and `Nat.rec` with
a higher-order motive gives it directly:

```text
Int.sumMaps : Nat → Nat → ((Nat → Nat) → Int) → Int

sumMaps 0       n F = F (fun _ => 0)
sumMaps (m + 1) n F = sumRange (fun k => sumMaps m n (fun g => F (cons k g))) n
```

The motive is `fun _ : Nat => ((Nat → Nat) → Int) → Int` — constant in the
index and not `Int`. That is not a new device: `Rat.det`'s motive is already
`fun _ : Nat => (Nat → Nat → Rat) → Rat`, for the same reason (its recursive
call is at a different matrix). ADR-1135 relied on that trick two sections
before declaring the function-space sum impossible.

`cons k g` is built **inline** as `fun i => Nat.rec.{1} (fun _ => Nat) k
(fun j _ => g j) i`, so both of its equations hold by ι-reduction alone. That is
load-bearing rather than tidy: the obvious alternative — "write index `m` of `g`
using `Nat.beq i m`" — puts an `i < m` side condition on every step of every
proof below, and buys nothing.

## What landed

Eight declarations in `crates/axeyum-lean-kernel/src/int_prelude/sum_maps.rs`,
all admitted by the trusted gate, all with an empty `Kernel::axiom_footprint`
(checked from `Kernel::axiom_footprint`, not from a list — see
`sum_maps_tests::the_sum_maps_family_is_axiom_free`).

| declaration | statement |
| --- | --- |
| `Int.sumRange_mul_right` | `∀ f z n, sumRange (fun k => f k * z) n = sumRange f n * z` |
| `Int.sumRange_mul_left` | `∀ z f n, sumRange (fun k => z * f k) n = z * sumRange f n` |
| `Int.sumMaps` | `Nat → Nat → ((Nat → Nat) → Int) → Int` (Definition) |
| `Int.sumMaps_zero` | `∀ n F, sumMaps 0 n F = F (fun _ => 0)` |
| `Int.sumMaps_succ` | `∀ m n F, sumMaps (m+1) n F = sumRange (fun k => sumMaps m n (fun g => F (cons k g))) n` |
| `Int.sumMaps_congr` | `∀ n m F G, (∀ g, F g = G g) → sumMaps m n F = sumMaps m n G` |
| `Int.sumMaps_mul_left` | `∀ n z m H, sumMaps m n (fun g => z * H g) = z * sumMaps m n H` |
| **`Int.prodRange_sumRange_expand`** | `∀ n m c, prodRange (fun i => sumRange (c i) n) m = sumMaps m n (fun g => prodRange (fun i => c i (g i)) m)` |

The last is the **generalized distributive law**: a product of `m` sums of `n`
terms expands into a sum over all `n^m` functions `[0,m) → [0,n)`. It is exactly
the expansion step of the Cauchy–Binet / multilinearity proof of
`det (A·B) = det A · det B` — the step ADR-1135's second bullet says
`sumRange` "cannot express".

It lands over `Int` rather than `Rat` only because `Int` is where both aggregates
already live (`Int.prodRange` since Wilson's theorem, `Int.sumRange` since
ADR-1260, yesterday). `Rat.prodRange` does not exist; nothing structural is in
the way of it.

### Why the induction has the shape it has

Both `sumMaps_congr` and `prodRange_sumRange_expand` quantify the *thing being
folded* inside the motive, not outside it:

```text
motive m := ∀ c, prodRange (fun i => sumRange (c i) n) m
                   = sumMaps m n (fun g => prodRange (fun i => c i (g i)) m)
```

This is forced: the successor step applies the induction hypothesis at
`fun i => c (succ i)`, a **different** coefficient family. It is the same shape
`Int.prodRange_permute` needs for its `σ` and `Rat.det_congr` needs for its
matrices, and the third time this development has arrived at it.

Both ends of the step peel their FIRST factor with
`Int.prodRange_shiftFront`, which is what makes `cons`'s two `Eq.refl`
equations line up with no side conditions. Peeling the LAST factor (the shape
`prodRange_succ` hands you) would have required writing index `m` of the map,
and with it the `Nat.beq` machinery this construction avoids.

### The evaluation tests, and one thing deliberately not tested

The gate cannot tell you a `Definition` is wrong, so five tests reduce
`Int.sumMaps` at concrete arguments (largest magnitude formed: 9):

- **Cardinality** at seven `(m, n)` pairs: `sumMaps m n (fun _ => 1)` must be
  `n^m`. Both `n = 0` cases are included — `sumMaps 0 0 _ = 1` (the empty map
  exists) and `sumMaps 2 0 _ = 0` (nothing maps into an empty range).
- **Full product vs diagonal**: `sumMaps 2 3 (fun g => g 0 * g 1)` is
  `(0+1+2)² = 9`, asserted NOT to be the diagonal's `0+1+4 = 5`. That is the
  plausible defect for a fold that threads one map through two nested levels: a
  `cons` that overwrote instead of extending visits only `g 0 = g 1`.
- Both defining equations, with the base map pinned as the constant zero.
- `prodRange_sumRange_expand` at a concrete instance, both sides computed
  independently to 9, each with a neighbouring-value negative.

**A transposed index is deliberately NOT tested, because it cannot be.** A sum
over *every* map is invariant under permuting the `m` indices whenever each
draws from the same `[0,n)`, so no total discriminates one. A test varying
`g 0` against `g 1` in the summand would look rigorous and measure nothing —
the vacuous-control shape this repository keeps rediscovering. It is recorded in
the module doc instead of being written.

## Decision

**Add no aggregate type. Keep the function-plus-bound idiom, and when an
argument needs an index set the range does not supply, build the FOLD.**

Concretely, on the three options the lane was given:

- **`List α`** — declined. Not because it cannot be declared (it can; it costs
  zero axioms) but because every `List` lemma is new surface with this kernel's
  `Nat`-recursion idioms to re-establish from scratch — which argument the
  recursion eats, which equations are `refl` and which are theorems, the
  equation-lemma discipline for a stuck recursor. `Nat.Fin`'s zero adoption is
  the measured prior for how that goes. ADR-0001's "add a boundary only when use
  proves it" applies, and this lane's whole result is that the use in question
  did not need one. If a genuinely order-sensitive multiset statement (unique
  factorization) ever becomes the priority, revisit **then**, with that
  statement as the driver.
- **`Nat.Fin`-indexed functions** — this IS the established idiom, minus the
  `Fin`. What the idiom cannot express is nothing that came up: the permutation
  case, the sharp test the lane was pointed at, is answered by
  `Int.prodRange_permute` (reindexing under an injective self-map with no
  permutation type) and now by `sumMaps` (summing over a function space with no
  function-space type). `nat_prelude/permutation.rs` already carries the full
  symmetric group as `Nat.comp`/`Nat.id`/`Nat.permInverse` over `BijectiveOn`.
- **`Prod`** — declined, and the third-mechanism argument is decisive.
  `Nat.Pair` landed 2026-08-29 as an actual inductive; the `Bool`-selected
  function (`Nat.xgcdAux (sel : Bool)`, `Nat.divModState`, `creal/ivt.rs`'s
  `Bool → CReal`) is the standing workaround and is used in three preludes. Two
  answers to one need is already one too many.

## Determinant multiplicativity: reachable, and the wall was never the aggregate

This is the question that motivated the lane, so it gets a precise answer.

**Route 2 (Cauchy–Binet / multilinearity) is unblocked at the step ADR-1135
named.** `prodRange_sumRange_expand` is that step, admitted. What remains, in
dependency order:

1. **General-row expansion** — `det A n` expanded along row `i`, not only row 0.
   ADR-1135 lists this as law 3, unattempted, not blocked by a missing type.
2. **The alternating property** — `det A n = 0` when two rows of `A` agree. The
   classical induction expands along a row other than the two that agree, so it
   needs (1) first.
3. **Sign under a row swap** — `det` of a row-permuted matrix is `sgn · det`,
   which follows from (2) by the standard `det(A + swap) = 0` argument.
4. **Multiplicativity** — (1)–(3) plus the landed expansion.

None of (1)–(3) is an aggregate question. All three are cofactor inductions over
`Nat → Nat → Rat` matrices, and all three will need `Rat.det_congr` wherever
they relate a minor to a matrix named elsewhere, exactly as ADR-1135 says. **So
the honest description of multiplicativity is now "three substantial theorems
away", not "needs a type this kernel does not have".**

Two corrections to ADR-1135's other bullets, both stated as *arguments* here
rather than as landed work — I did not build either, and a later lane should
verify rather than inherit:

- **The Leibniz sum is expressible.** `sumMaps n n` sums over all maps
  `[0,n) → [0,n)`; the permutations are the injective ones, and injectivity on a
  bounded range is decidable by `Nat.beq`, so a `sgnOrZero g n` returning `0` at
  non-injective `g` is definable. `leibniz A n := sumMaps n n (fun g =>
  sgnOrZero g n * prodRange (fun i => A i (g i)) n)` is then a well-formed term
  today. ADR-1120's "there is no type in which to write that sum" and
  ADR-1135's restatement of it are both wrong on this point. *Whether that
  `leibniz` agrees with `Rat.det` is a separate and hard theorem, and nothing
  here says it is cheap.*
- **The elementary-operations route does not need a factorization length as
  data.** A length is a `Nat` and a sequence of operations is a function plus a
  bound — the idiom this whole ADR is about. What that route actually needs is
  (2) and (3) above, the same as every other route. It has no independent
  advantage and should not be attempted first.

## Consequences

- **`sumMaps` is general.** Nothing in it mentions determinants. Any argument
  that sums or products over "all assignments of `m` indices from a range of
  `n`" — inclusion–exclusion, multinomial expansions, counting over a product
  of finite sets — can use it directly, and `sumMaps_congr` /
  `sumMaps_mul_left` are the two rewriting tools such an argument needs first.
- **A `Rat` copy is straightforward and is NOT landed.** `Rat.prodRange` does
  not exist; a `Rat.sumMaps` for the determinant work needs it plus the same
  seven lemmas. That is ordinary work, deliberately not done here — this lane's
  deliverable was the decision, and one carrier demonstrates it.
- **Do not write "this kernel cannot express X because it has no aggregate"
  again without checking whether X needs the SET or only a FOLD over it.** That
  is the question ADR-1135, ADR-1120 and ten module docs all skipped, and it is
  the question that decides the answer. The documents corrected by this lane are
  listed below.
- The genuinely permanent obstruction in this family is unchanged and is a
  different one: **multiset equality** (unique factorization, the characteristic
  polynomial's root multiset) really does quantify over an aggregate rather than
  fold over one, and no fold reaches it. `nat_prelude/factorization.rs`'s module
  doc stays as it is. What changes is that this is now a *narrow* claim about
  statements that compare two unordered collections, not a general claim about
  finite families.

## Documents corrected

Each carries a dated correction quoting the stale text, per the convention those
files already use:

- `docs/research/09-decisions/adr-1135-…-funext-costs.md` — the three-route
  wall.
- `docs/research/09-decisions/adr-1120-the-general-n-determinant-is-a-function-plus-a-bound.md`
  — "no type in which to write that sum", and "the encoding is forced".
- `docs/curriculum/DEPTH-PROPOSAL-number-theory-and-linear-algebra.md` —
  "structural rather than a matter of effort".
- `docs/curriculum/03-destinations/number-theory.md` — "no `List`, `Finset`,
  product type or quotient by permutation in which to state multiset equality"
  (kept, scoped).
- `docs/curriculum/foundational-books/spivak.md` — "this kernel has no `List`".
- `docs/curriculum/graded-statement-families-number-theory-and-linear-algebra.md`
  — already the most self-aware file on this question; its §3 already said "the
  gap is **not** a missing type", and the correction points its §1.2(b) at this
  ADR.
- `crates/axeyum-lean-kernel/src/rat_prelude/matrix_det.rs` — the module doc's
  "a finite family is a function plus a bound and nothing else".
- `crates/axeyum-lean-kernel/src/nat_prelude/permutation.rs` — option (b), the
  `n!`-indexing route, recorded as unattempted-for-scope.
- `docs/plan/status/general-n-determinant.md` — "not merely unproved but **not
  expressible**".

## What this ADR does NOT claim

- Multiplicativity is not proved, and neither is any of (1)–(3).
- The Leibniz-sum construction is argued, not built. No `sgnOrZero` exists.
- `sumMaps` gives a summation *schedule* over the function space. It does not
  give a permutation type, an injectivity predicate over that schedule, or a
  sign — and the Cauchy–Binet proof needs all three next.
- Nothing here says a `List` would be *bad*. It says the use has not proven the
  boundary, and that the specific uses cited as proving it did not.
