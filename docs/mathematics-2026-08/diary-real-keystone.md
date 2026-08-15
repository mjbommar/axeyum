# Diary: what ℝ actually costs, and why ℤ was the answer

Lane: `real-keystone`. Date: 2026-08-15.

## The brief, and why I did not follow it

The strand item said ℝ was the whole of the remaining keystone: 30 axioms, 0
derived theorems, "asserted, not constructed", exactly where ℤ was two days ago.
The hard question I was told to answer first was whether ℝ needs a trusted
`Quotient`, and to quantify the cost if so.

I answered it, and the answer moved the goalposts twice. Both moves came from
reading the environment instead of the prose about it.

## Measurement 1 — the `Real` prelude is not an axiomatization of ℝ

I enumerated the 30 declarations rather than trusting the module's own summary,
which calls them "an axiomatized **linear ordered field**":

| group | n |
|---|---|
| carrier + operations (`Real`, `add`, `mul`, `neg`, `zero`, `one`, `le`, `lt`) | 8 |
| order laws | 7 |
| additive laws | 6 |
| multiplicative laws | 9 |

There is no `inv` and no `div`, so it is **not a field**. There is no
completeness (supremum) axiom, no Archimedean axiom, no density axiom — so
**nothing in it distinguishes ℝ from ℚ**. There is not even a totality axiom
(`le_total` is absent), so it is not stated as *linear* either.

What the package actually axiomatizes is an **ordered commutative ring with 1**.
Every one of its 22 laws is true of ℤ.

That is a bigger finding than it looks, because it changes the question from
"how do we construct ℝ" to "what is this thing for". It is the trusted base for
Farkas/LRA and degree-2 SOS reconstruction, and neither of those reasoning
routes ever divides. The carrier's *name* was doing the work its axioms were not,
and everyone downstream — including this strand item, including me for the first
hour — read the name as a description of the assumptions.

## Measurement 2 — `Quot.sound` does not exist in this kernel

Three places in this repository say a setoid construction is possible but
expensive because "`Quot`/`Quot.sound` are admitted as `Declaration::Quotient`",
so `Quot.sound` would sit in every footprint forever: `int_prelude.rs:25`,
`int_prelude/defs.rs:8`, and the ℤ lane's own diary. The strand brief repeats it.
It is the recorded justification for ℤ's normalized-pair representation.

It is false about *this* kernel. `quotient.rs` admits a package of
`PACKAGE_LEN = 4` — `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` — enforced by a
test literally named `canonical_package_admits_exactly_four_and_is_idempotent`.
There is no `Quot.sound` contract, no `QuotKind` variant for it, and **no prelude
calls `add_quotient_package` at all** (only `axeyum-lean-import` does, for
foreign modules).

Without `Quot.sound` nothing can prove `Quot.mk r a = Quot.mk r b` from `r a b`.
A quotient carrier here has a quotient's shape and none of its content. So:

> **A Cauchy-sequence construction of ℝ is not expensive in this kernel. It is
> inexpressible.**

The ℤ decision was right, for a stronger reason than the one recorded. I have
corrected all three comments and pinned the measurement as a test
(`the_quotient_package_has_no_soundness_primitive`), because the next lane will
otherwise re-derive it from prose that was describing Lean's package rather than
ours. This is the CLAUDE.md lesson in its purest form: a message in the codebase
outlived the thing it described, and four documents inherited it.

Dedekind cuts do not rescue the route either. A cut is a predicate `ℚ → Prop`,
and proving two cuts with the same members equal needs `propext` and `funext`,
neither of which exists — the logic prelude is intuitionistic at *zero* trusted
declarations, which is exactly why `Int.eq_em` had to be restricted decidable
equality rather than excluded middle. That route costs two new axioms where the
quotient route costs one new primitive.

## What I built instead

Given both measurements, constructing ℝ would have meant enlarging the trusted
surface to discharge axioms **about a carrier no consumer needs**. So I did the
thing that was actually available: I built the model.

`build_int_model_of_arith` takes each of the 22 `Real` laws, computes its type
with the eight carrier/operation constants substituted — from the environment,
never typed by hand — and admits a theorem of that type whose proof is the
corresponding `Int` theorem. The kernel type-checks each one.

```
Real: 30 trusted declarations = 8 interpreted symbols + 22 modelled laws;
22/22 witnesses have an EMPTY axiom footprint,
22/22 are syntactically the Int law
```

21 of the 22 were already ℤ theorems with empty footprints, courtesy of the
`int-keystone` and `int-remainder` lanes. The 22nd, `sq_nonneg`, I proved:
`Int: 50 → 51 derived, all 51 with an empty footprint`, one still asserted
(`euclidean_decomposition`, untouched).

The `identical` column is the part I did not expect. The substituted `Real`
axiom is not merely definitionally equal to the `Int` law — it is the **same
interned term**, in all 22 cases. Two preludes written months apart, one by
hand-computed de Bruijn indices in `arith_prelude.rs` and one through
`statements.rs`'s shared builders, agree to the term. That is the sharing
discipline the ℤ lane insisted on paying off across a boundary it was not
designed for.

## `sq_nonneg`, and why it is not `mul_nonneg`

`0 ≤ a·a` unconditionally; `mul_nonneg` needs both factors nonnegative and says
nothing when `a` is negative. In most developments this is a sign case analysis.
Here it is not, and the reason is structural: `Int.mul` sends **both** same-sign
branches into `Int.ofNat` (`ofNat m * ofNat m ≡ ofNat (m*m)`,
`negSucc m * negSucc m ≡ ofNat (succ m * succ m)`), and a square is always
same-sign. So neither branch has a hypothesis to use or to refute, and both close
with `Nat.zero_le`. The whole proof is nine lines.

Worth stating as a pattern, because it recurs in this development: *the
constructor the answer lands in is where the mathematics went*. `Int.le`'s mixed
branches reduce to `False`/`True` and that is why ten order laws fell out in the
first lane; `Int.mul`'s same-sign branches collapse into one constructor and that
is why this one has no case analysis at all.

## What this licenses, stated narrowly

It is **relative consistency**: the `Real` axiom set has a model whose theory is
derived from nothing, so no Farkas or SOS reconstruction is vacuous on account of
a contradictory axiom package. That risk was real and unmeasured — a
contradictory package makes every reconstruction "valid" while every gate stays
green, which is precisely the failure shape this repository keeps writing about.

Three limits I am not going to blur:

1. The kernel checks the interpretation of each **axiom**. The step from "every
   axiom translates" to "every *derivation* translates" is the ordinary
   homomorphism argument over the term language and is **not** machine-checked —
   the kernel cannot state it.
2. It is **not** a discharge. `real: axiom=30` is unchanged and I did not touch
   it. A theorem about `Int` is weaker than the same theorem about ℝ.
3. `ℤ` is not `ℝ`. Nothing here says otherwise, and `Real := Int` would have
   silently weakened every reconstructed LRA theorem while every gate stayed
   green. That was the one alternative I rejected outright rather than deferred.

## Where ℚ belongs

ℚ is the right carrier for LRA and I did not build it, deliberately.

The mathematical reason it is right: for linear systems with rational
coefficients, satisfiability over ℚ and over ℝ coincide, so certifying UNSAT over
ℚ is exactly as strong as over ℝ. LRA never needs a real number.

The reason I did not build it: **no axiom in the package asks for it.** ℚ would
discharge exactly the same 22 laws ℤ already models, at the cost of a
gcd-normalization sub-development. Building it today would be paying for a
capability nothing consumes.

The crux lemma, recorded so the next lane does not have to find it. ℚ *is*
quotient-free constructible — numerator `Int`, denominator `Nat`, normalized by
`Nat.gcd`, which the `Nat` prelude has with its universal property and Bézout
certificates, and which avoids `Int` division entirely (so it does not wait on
`euclidean_decomposition`). Every operation must normalize, so every
associativity and distributivity law reduces to one obstruction:

> `normalize` is a function of the cross-multiplication class:
> `a·d = c·b ⊢ normalize (a,b) = normalize (c,d)`, together with
> `normalize (n·k, d·k) = normalize (n, d)`.

That is the ℚ analogue of `subNatNat`'s borrow — one obstruction wearing four
laws' clothing. Build it when a `Real` axiom mentioning `inv`, `div`, a supremum
or Archimedean-ness is proposed; the test
`the_real_package_has_no_inverse_completeness_or_archimedean_axiom` fires on that
day.

## The route that actually eliminates the 30, and it is not constructing ℝ

Worth writing down because I only saw it after the model was built.

If a Farkas refutation only ever uses ordered-ring laws — and by construction it
does, that is what the package is — then the reconstruction can take those laws
as **hypotheses** instead of axioms:

```
∀ (R : Type) (add mul : R → R → R) (neg : R → R) (zero one : R)
  (le lt : R → R → Prop), <the 22 laws> → <the refutation>
```

That theorem has an empty footprint, is *stronger* than today's `Real`-specific
statement, and recovers the current statement by instantiation at `Real`. It
makes the 30 axioms **unnecessary** rather than proved, and it is a change to
`axeyum-solver/src/reconstruct/arithmetic.rs`, not to the kernel. Constructing a
carrier is the expensive way to reach a weaker place.

## Controls

- `nat_theorem_inventory`: **119 theorems, byte-identical**, diff clean.
- `nat_axiom_inventory`: `logic 0, nat 0, real 30, integer 1, string 1` —
  unchanged, including `real: 30`, which is the honest reading of what this lane
  did and did not do.
- `int_theorem_inventory`: 50 → **51 derived, 51 with an empty footprint**, 1
  asserted.
- `cargo test -p axeyum-lean-kernel`: 255 lib tests (249 + 6 new) plus every
  integration suite, green. Clippy `-D warnings` clean.
  `RUSTDOCFLAGS="-D warnings" cargo doc`: clean.
- `scripts/check-lean-gate.sh`: **12 suites, 49 tests, 112 real-Lean checks
  (floor 105)**, green — unchanged, because `Int.sq_nonneg` is not reachable from
  any export root, so no golden module hash moved.
- `validate-facts.py`: 96 facts, 0 errors, `kernel-lean=31, 30 axiom-free`.

## What I would tell the next person

**Enumerate the axiom package before deciding what it needs.** An hour of my
session went into planning a ℚ construction for a field axiomatization that has
no division in it. The list was thirty lines long and I read a doc comment
instead.

**A comment describing a dependency's design will outlive the difference.**
`Quot.sound` is in Lean's quotient package and not in ours; four documents said
otherwise, and the one that mattered was the *justification for a decision*.
Justifications rot in the same way measurements do, and they are worse, because
nobody re-runs a justification.

**"It has a model" is a different claim from "it is proved", and both are
worth having.** The model does not shrink `real: axiom=30` by one. It does
eliminate the possibility that the 30 are contradictory, which is the failure
mode that would have made every LRA certificate in this repository worthless
without any gate noticing.
