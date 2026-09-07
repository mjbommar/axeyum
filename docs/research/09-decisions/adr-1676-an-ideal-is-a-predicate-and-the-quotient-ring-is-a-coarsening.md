# ADR-1676: An ideal is a predicate, and `R/I` is a coarsening — the ten ring laws come free, `absorb` buys exactly one field

Status: accepted
Date: 2026-09-06
Index-summary: `ideal` occurred ZERO times in the kernel source before this lane (same-invocation positive control: 981 `AlgS.` references); so did `subring`, `submodule`, `quotientRing`, `localiz`, `tensor`, `irreducib`, `splitting`. `AlgS.Ideal.*` lands 31 axiom-free declarations: nine generic `AlgS.CommRing` lemmas the spine lacked, `IsIdeal` as a five-conjunct PREDICATE (matching `AlgS.Subgroup.IsSub`'s four plus the absorbing law — so "ideal over additive subgroup" costs exactly ONE field), three instances (`bot` as the equivalence CLASS of zero, `top`, and the principal ideal `(g)`), and `AlgS.Ideal.quotient : forall R I hI, AlgS.CommRing` built as a coarsening on `R`'s own carrier. The measured split of the quotient's 23 fields: 6 are `R`'s own unchanged, 1 is the coset relation, 6 are hand-discharged congruence obligations, and the ten ring LAWS are all free through one four-step lemma `AlgS.Ideal.ofEquiv`, because the coset relation is COARSER than `R.equiv`. `absorb` is load-bearing in exactly one place and `closedNeg` in exactly one other, each verified by a mutant the kernel actually refused. Deliverable 3 (the first isomorphism theorem in ring form) did NOT land: `AlgS.Hom.firstIso` quantifies over `AlgS.Group` only, its `HomCtx`/`close_hom` binder machinery is private to `structures_setoid.rs`, and there is no coercion between the two records — the obstruction is gated as a test, not asserted in prose.
Index-status: accepted

## Context

Topic 4, carrier 3 of the algebra shelf. Reviewer 04 measured `ideal` at **zero
occurrences** in the whole kernel source, against a 4,839-declaration dump with
600 `Alg`/`AlgS` names as the same-invocation positive control, and named it the
single thing standing between the algebra shelf and a second course. This lane
re-ran that measurement before starting: one case-insensitive hit for `ideal`
(the word "ideal" in a comment in `creal/rolle.rs`), 981 `AlgS.` references as
the positive control, and zero for `subring`, `submodule`, `quotientRing`,
`localiz`, `tensor`, `irreducib` and `splitting`.

The prerequisite was already there and was the hard part.
[ADR-1595](adr-1595-quotients-stay-setoids-and-quot-sound-stays-out.md) built
`AlgS.Hom.quotient` by **coarsening the equivalence on the same carrier** rather
than by a quotient type — this kernel has no `Quot` at all, and that is settled
policy — and [ADR-1609](adr-1609-polynomials-modules-and-subgroups-over-the-setoid-spine.md) built
`AlgS.Subgroup.*` as predicates for the same reason. What was missing was the
ring-theoretic subobject.

## Decision

### 1. An ideal is a PREDICATE, not a record

`AlgS.Ideal.IsIdeal : forall (R : AlgS.CommRing), (R.carrier -> Prop) -> Prop`,
a right-nested `And` of five conjuncts, with five projection theorems
(`respects`, `mem_zero`, `closedAdd`, `closedNeg`, `absorb`).

The alternative — a one-constructor record bundling the predicate with its
closure proofs — was rejected for three reasons, in decreasing order of weight:

1. **It would be the only subobject in the spine shaped that way.**
   `AlgS.Hom.ker`, `AlgS.Hom.image` and `AlgS.Subgroup.IsSub` are all
   predicates. A record here would mean the ideal lattice and the subgroup
   lattice could never share a lemma.
2. **A hypothesis is the shape the quotient wants.** `AlgS.Ideal.quotient`
   takes `hI : IsIdeal R I` as a binder, exactly as `AlgS.Hom.quotient` takes
   `fCongr` and `fMul` as binders. A record would have to be projected in
   every one of the six congruence proofs, which is the same `And.left`/
   `And.right` chain wearing a different name.
3. `Subtype` exists now (ADR-1613), so the record *is* buildable — this is a
   choice, not a limitation. The record's one real advantage is that
   `Ideal R` would be a TYPE, which is what an ideal *lattice as a poset
   object* would need.

**What it costs the next lane, stated plainly:** prime and maximal ideals will
be `And (IsIdeal R I) (…)` rather than record fields, and there is no type of
ideals, so the ideal lattice can be built as a meet-semilattice of predicates
(exactly as `AlgS.Subgroup.*` is) but not as a `CatS` object without first
bundling through `Subtype`. Everything in `AlgS.Subgroup.*`'s lattice layer —
`le` as implication, `inter` as intersection, `top`, `bot`, the
greatest-lower-bound triple — transfers shape-for-shape.

### 2. The five conjuncts, and why `closedNeg` stays explicit

| # | conjunct | free under `Eq`? | in `AlgS.Subgroup.IsSub`? |
|---|---|---|---|
| 0 | `forall a b, R.equiv a b -> I a -> I b` | **YES** (`Eq.subst`) | yes |
| 1 | `I R.zero` | no | yes |
| 2 | `forall a b, I a -> I b -> I (R.add a b)` | no | yes |
| 3 | `forall a, I a -> I (R.neg a)` | no | yes |
| 4 | `forall r a, I a -> I (R.mul r a)` | no | **no — this is the ideal** |

So the measured cost of "ideal" over "additive subgroup" is **one field**, and
the setoid tax on the whole layer is the same **one field** it is for subgroups
(conjunct 0).

Conjunct 3 is **derivable** from conjunct 4: `-a ~ (-1) * a`, via
`AlgS.Ideal.mulNegL`. It is kept explicit anyway, and the reason is a
measurement rather than taste. With `closedNeg` present, the two conjuncts are
load-bearing in **disjoint** places — `absorb` in the quotient's
`mulCongr` and nowhere else, `closedNeg` in the quotient's `equivSymm` and
nowhere else — and each mutant therefore kills exactly one obligation while the
other still admits as a positive control. Deriving `closedNeg` from `absorb`
would have made the absorbing law's mutant break both, and a mutant that breaks
everything localizes nothing.

### 3. `R/I` is `R`'s carrier under `x ~ y := x - y ∈ I`

`AlgS.Ideal.quotEquiv R I x y := I (R.add x (R.neg y))`, and
`AlgS.Ideal.quotient R I hI : AlgS.CommRing` has `carrier := R.carrier`,
`equiv := quotEquiv R I`. `quotient_equiv` is proved by
`Iff.intro (fun h => h) (fun h => h)`, so it passes only if the record selector
on the instance reduces definitionally — a deliberate test, not a convenience
lemma, exactly as `AlgS.Hom.quotient_equiv` is.

**The measured cost, per field.** This is the deliverable, and it is readable
off the source because all 23 arguments are listed with their labels in
`declare_quotient`:

| the 23 fields | how discharged | count |
|---|---|---|
| `carrier`, `zero`, `one`, `add`, `mul`, `neg` | `R`'s own, unchanged | 6 |
| `equiv` | the coset relation | 1 |
| `equivRefl` | `AlgS.Ideal.ofEquiv` at `refl` | 1 |
| `equivSymm` | `closedNeg` + `negAddDist` + `neg_neg` + `addComm` | 1 |
| `equivTrans` | `closedAdd` + `addRegroup` + `negAddL` + `zeroAdd` | 1 |
| `addCongr` | `closedAdd` + `addSwapMid` + `negAddDist` | 1 |
| `mulCongr` | **`absorb` twice** + `closedAdd` + regrouping, 8 chain steps | 1 |
| `negCongr` | `closedNeg` + `negAddDist`, ONE `respects` | 1 |
| `addAssoc`, `addComm`, `addZero`, `mulAssoc`, `mulOneL`, `mulOneR`, `distribL`, `distribR`, `negAdd`, `mulComm` | **all free** via `ofEquiv` | 10 |

**The ten free law fields are the finding.** `AlgS.Ideal.ofEquiv` is a
four-step theorem: `R.equiv x y -> I (x + (-y))`, by `addCongr` then `negAdd`
then `equivSymm` then `respects` at `memZero`. Because the coset relation is
COARSER than `R.equiv`, every law `R` already proves transports through it, and
**no ring law is re-proved in the quotient**. Compare `AlgS.Hom.quotient`,
where five of fifteen group fields are laws pushed through `fCongr` — same
mechanism, and this ADR records that it scales to a 23-field record without
degrading.

The other half of the honest accounting: **six obligations had to be
discharged by hand** (`equivRefl`/`Symm`/`Trans`, `addCongr`, `mulCongr`,
`negCongr`), against three for the group quotient (`opCongr`, `invCongr`, and
the equivalence infrastructure, which the group case got from `H`'s own
`equivRefl`/`Symm`/`Trans` because its relation was `H.equiv (f a) (f b)`).
Quotienting by an IDEAL rather than by a homomorphism's kernel is what makes
the three equivalence fields real work: there is no codomain setoid to borrow
them from.

### 4. Nine generic `AlgS.CommRing` lemmas landed as a side effect

The spine had `AlgS.sub`, `sub_self`, `neg_neg`, `mul_zero`, `mul_neg_one`,
`add_left_cancel`, `inv_unique`, `invInv`. It did not have: `zeroAdd`
(`0 + a ~ a` — the record only carries `addZero` on the right), `negAddL`
(`(-a) + a ~ 0` — same asymmetry), `negZero`, `zeroMul`, `mulNegR`, `mulNegL`,
`negAddDist`, `addSwapMid`, `addRegroup`. They are declared under
`AlgS.Ideal.*` rather than the bare `AlgS` root to keep namespace allocation
lane-local; **they deserve promotion to `AlgS.*` once a second consumer
appears**, and this ADR is the record of that debt.

One of them is worth stating because the obvious route is four times longer.
`negAddDist : -(a+b) ~ (-a) + (-b)` is **three steps through `-1`**:
`-(a+b) ~ (a+b)*(-1)` (symm `mul_neg_one`), `~ a*(-1) + b*(-1)` (`distribR`),
`~ (-a) + (-b)` (`addCongr` of `mul_neg_one` twice). The additive route —
build `(a+b) + ((-a)+(-b)) ~ 0` and cancel — is thirteen `equivTrans` steps.
`mul_neg_one` is the lever, and it is reached at `AlgS.CommRing.toRingS R`,
the same route `field_setoid` uses.

### 5. Deliverable 3 did NOT land, and the obstruction is gated as a test

The brief asked for `R/ker f ≅ im f` in ring form *if it is within reach from
`AlgS.Hom.firstIso`'s shape*, and to STOP and report the exact obstruction
otherwise. It is not within reach, for four measured reasons:

1. **`AlgS.Hom.firstIso` and `firstIsoClassical` quantify over `AlgS.Group`
   only.** Verified live in
   `the_group_first_isomorphism_theorem_says_nothing_about_rings`, which reads
   the rendered types from the kernel and asserts neither mentions
   `AlgS.CommRing`, with `AlgS.Ideal.quotient` as the positive control in the
   same invocation. If a later lane makes the ring form a transport after all,
   that test goes red and says so.
2. **There is no coercion between `AlgS.Group` and `AlgS.CommRing`.** The
   spine is nine independent records by design (ADR-1588); `toCommGroupS`
   projects a ring to its ADDITIVE group, which is a forgetful map in the
   wrong direction — the resulting object has no multiplication and therefore
   cannot *be* `R/ker f` as a ring.
3. **The binder machinery is private.** `HomCtx` (line 2833),
   `hom_ctx` (2867), `close_ghf` (2972) and `close_hom` (2992) in
   `structures_setoid.rs` are all module-private and hard-coded to the FIVE
   group binders `G H f fCongr fMul`. A ring hom needs **seven**
   (`R S f fCongr fAdd fMul fOne`), so a ring-flavoured context is a new
   binder stack, not a parameterization of the existing one.
4. **The image side needs a new object.** `AlgS.Hom.imageGroup` is
   `Subtype H.carrier (image f)` with 14 of 15 fields free by
   `Subtype.val` ι-reduction and **three** membership proofs (`e`, `op`,
   `inv`). The ring analogue needs **five** (`zero`, `one`, `add`, `mul`,
   `neg`) and 23 fields.

**Sizing for the next lane**, so this is a queue item and not a wall. Four
declarations, in order, none of them requiring an edit to `structures_setoid.rs`:

- `AlgS.RingHom.*` — the seven-binder context, plus `mapZero` and `mapNeg`
  (mirroring `AlgS.Hom.mapOne`/`mapInv`, which are ~20 chain steps each).
- `AlgS.RingHom.ker_isIdeal : IsIdeal R (ker f)` — the absorbing conjunct is
  `f(r·a) ~ f(r)·f(a) ~ f(r)·0 ~ 0`, i.e. `fMul` then `S`'s `mulCongr` then
  `AlgS.mul_zero`. The other four conjuncts are `AlgS.Subgroup.ker_isSub`'s
  proofs restated additively.
- `AlgS.RingHom.quotEquiv_iff : quotEquiv R (ker f) x y <-> S.equiv (f x) (f y)`
  — the bridge from THIS lane's quotient to the kernel congruence. Needs
  `f(x + (-y)) ~ f x + (- f y)`, i.e. `fAdd` and `mapNeg`.
- `AlgS.RingHom.imageRing : AlgS.CommRing` over `Subtype S.carrier (image f)`,
  then `inducedRing` and the same three conjuncts `firstIsoClassical` uses.

Once those exist the theorem itself is nearly free, for the reason
`image_group.rs` records: the obstruction is the carrier, not the mathematics.

## Consequences

**What the next lane gets for free.**

- **Prime and maximal ideals** are one `And` away:
  `IsPrime R I := And (IsIdeal R I) (forall a b, I (R.mul a b) -> Or (I a) (I b))`,
  `IsMaximal` similarly. Both are statable today.
- **The ideal lattice** transfers shape-for-shape from `AlgS.Subgroup.*`:
  `le` as implication, `inter` as intersection, `top`/`bot` already declared
  here with their `IsIdeal` proofs. The JOIN is absent for the same reason it
  is absent for subgroups — the ideal generated by a union needs a closure
  construction, i.e. a parameterized inductive over `R.carrier`.
- **ℤ/n as a RING, not just an additive group.** `Nat.modAdd_isGroup` is
  currently the only `modAdd` name in the tree, so ℤ/n is additive-group-only
  today. With `AlgS.Ideal.principal (ofAlg Int.commRing) n` and
  `AlgS.Ideal.quotient`, ℤ/n is now a genuine `AlgS.CommRing` value — the
  evaluation test in this lane already instantiates `principal` at ℤ and
  proves `4 ∈ (2)` with witness `2`.
- **The nine ring lemmas** (§4), which any further `AlgS.CommRing` work will
  want.

**What this deliberately does not do.** No ideal lattice (only `bot`, `top`
and `principal` with their proofs — enough to make the predicate non-vacuous,
which is what the brief asked for). No quotient-by-a-normal-subgroup
generalization of `AlgS.Hom.quotient`. No `AlgS.Iso` record; the ring form of
the first isomorphism theorem is sized above, not invented here.

## Evidence

31 declarations, all admitted through `Kernel::add_declaration`, all with an
**empty** `Kernel::axiom_footprint` read from the kernel (not from source text
or this document). Eleven tests in `ideal_setoid_tests`, ~15 s in release.

Three mutants **RUN**, each rebuilding a weakened `IsIdeal` under a scratch
namespace and asking the kernel; every one is a kernel REJECTION, and each is
paired with a positive control in the same test:

| mutant | predicted | RUN — what actually died |
|---|---|---|
| `absorb` dropped from `IsIdeal` | `quotMulCongr` unprovable | `quotMulCongr` REFUSED by the kernel; `quotSymm` still admits (positive control) |
| `closedNeg` dropped from `IsIdeal` | `quotSymm` unprovable | `quotSymm` REFUSED; `quotMulCongr` still admits (positive control) |
| `quotSymm`'s last leg reversed (`addComm y (-x)` for `addComm (-x) y`) | rejected | REFUSED; the unreversed build accepted in the SAME invocation |

All three are kernel rejections rather than test failures, which proves the
statements are load-bearing but says nothing about the tests. The
counterweight is the **evaluation test**, which is a case the kernel ADMITS:
`AlgS.Ideal.principal` at `AlgS.CommRing.ofAlg(Int.commRing)` unfolds by
reduction to exactly `Exists Int (fun r => R.equiv 4 (R.mul r 2))`,
`Exists.intro 2 (Eq.refl 4)` proves `4 ∈ (2)` — which type-checks only because
`Int.mul 2 2` reduces to `4` — and, in the same invocation, witness `1` does
**not**, because `1 * 2` is `2`. A `principal` that ignored its generator would
accept both. Magnitudes 1, 2 and 4 only: every `Nat` numeral underneath is
unary.

One real defect was found and fixed on the way, and it is the kind this
codebase keeps producing: `declare_principal_is_ideal` used `A_FV` for the
principal ideal's GENERATOR, and the conjunct builders bind `A_FV` inside
`respects`, `closedAdd` and `absorb`. The statement's own `pi_over` swallowed
the generator, and the kernel refused with an opaque
`TypeMismatch { expected, got }` naming nothing. The generator now has its own
`G_FV`, outside the range the statement builders bind, with a comment saying
why.

Gates run, with counts: `ideal_setoid_tests` 11 passed; `cross_prelude_collision_tests`
8 passed (including `every_declaration_a_prelude_introduces_is_checked_and_axiom_free`,
whose ownership is derived from the build-order diff and so covers these 31
without a hand-maintained list); `nat_prelude_tests::every_nat_declaration_is_checked_and_axiom_free`
1 passed; `cargo clippy -p axeyum-lean-kernel --all-targets --all-features -D warnings`
exit 0; `cargo check --workspace --all-targets` exit 0;
`cargo fmt --all --check` exit 0.
