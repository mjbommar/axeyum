# ADR-0456: The `Real` prelude is an ordered ring, and `ℤ` is its checked model

Status: accepted
Date: 2026-08-15
Index-summary: `Real`'s 30 axioms need no field, completeness or Archimedean property; `ℤ` models all 30 with empty footprints, and `Quot.sound` does not exist here

## Context

`build_arith_prelude` declares 30 trusted constants under `Real` and calls them
"an axiomatized **linear ordered field**". They are the trusted base for LRA
`la_generic` (Farkas) and degree-2 SOS reconstruction. `nat_axiom_inventory` has
reported `real: axiom=30` unchanged through every campaign, while `nat` reached
`axiom=0 / 119 theorems` and `integer` went `34 → 6 → 1`.

The strand item
[`01-int-real-keystone.md`](../../refactor-2026-08/01-int-real-keystone.md) put
the question as: construct `ℝ`, or say plainly what `ℝ` costs. The received
answer in this repository — recorded in `int_prelude.rs`, in `defs.rs`, and in
[`diary-int-keystone.md`](../../mathematics-2026-08/diary-int-keystone.md) — was
that a setoid-quotient construction is possible but expensive, because
"`Quot`/`Quot.sound` are admitted as `Declaration::Quotient`", so `Quot.sound`
would enter every footprint forever.

Two measurements were taken before any code was written, and both changed the
question.

## Decision

**`Real`'s axiom package is a linear ordered commutative ring, not a field, and
we model it in the constructed `ℤ` rather than construct `ℝ`.** Concretely:

1. The package is left at 30 axioms. Interpreting `Real` as `ℤ` does **not**
   discharge them and we do not pretend otherwise.
2. `build_int_model_of_arith` admits, for each of the 22 `Real` **laws**, a
   theorem whose type is that axiom's type with the eight carrier/operation
   constants substituted — computed from the environment, never typed by hand —
   proved by the corresponding `Int` theorem and type-checked by the kernel.
   All 22 witnesses have an **empty** `axiom_footprint`.
3. `ℝ` is **deferred with a price tag**, stated below, rather than attempted.
4. `ℚ` is named as the next carrier to build, and the trigger for building it is
   named: the first `Real` axiom that mentions an inverse, a division, a
   supremum, or Archimedean-ness.

## Evidence

### Measurement 1 — the package has no field or completeness axiom

Enumerated from the environment (`arith_model_tests.rs`, and the count is
re-derived there rather than quoted):

| group | count | names |
|---|---|---|
| carrier + operations | 8 | `Real`, `add`, `mul`, `neg`, `zero`, `one`, `le`, `lt` |
| order laws | 7 | `le_refl`, `le_trans`, `lt_irrefl`, `lt_trans`, `lt_of_lt_of_le`, `lt_of_le_of_lt`, `le_of_lt` |
| additive laws | 6 | `add_comm`, `add_assoc`, `add_zero`, `add_neg`, `add_le_add`, `add_lt_add_of_le_of_lt` |
| multiplicative laws | 9 | `mul_comm`, `mul_assoc`, `mul_one`, `mul_zero`, `left_distrib`, `mul_nonneg`, `sq_nonneg`, `mul_le_mul_of_nonneg_left`, `zero_lt_one` |

There is **no** `inv`, no `div`, no supremum/completeness axiom, no Archimedean
axiom, no density axiom, and — worth noting separately — no totality axiom
either, so the package is not even stated as *linear*. Every one of the 22 laws
is true of `ℤ`.

The doc comment calling this "a linear ordered field" is the kind of message
this repository has learned not to trust: the description named the intended
carrier, and everyone downstream read it as a description of the assumptions.

### Measurement 2 — `Quot.sound` does not exist in this kernel

`quotient.rs` admits a package of `PACKAGE_LEN = 4`: `Quot`, `Quot.mk`,
`Quot.lift`, `Quot.ind`, enforced by
`canonical_package_admits_exactly_four_and_is_idempotent`. There is no
`Quot.sound` contract, no `QuotKind` variant for it, and no prelude calls
`add_quotient_package` at all (only `axeyum-lean-import` does, for external
modules).

Without `Quot.sound` there is no rule that makes `Quot.mk r a` equal to
`Quot.mk r b` from `r a b`, so a quotient carrier has the *shape* of a quotient
and none of its content. **A Cauchy-sequence construction of `ℝ` is therefore
not merely expensive here, it is inexpressible.** Three places in this
repository say otherwise; they were describing Lean's quotient package, not
ours. Pinned by `the_quotient_package_has_no_soundness_primitive`.

### Measurement 3 — `ℤ` models the whole package, axiom-free

`cargo run --release -q -p axeyum-lean-kernel --example arith_model_witness`:

```
Real: 30 trusted declarations = 8 interpreted symbols + 22 modelled laws;
22/22 witnesses have an EMPTY axiom footprint,
22/22 are syntactically the Int law
```

21 of the 22 laws were already `Int` theorems with empty footprints. The 22nd,
`sq_nonneg`, is proved here: `Int.mul` sends *both* same-sign branches into
`Int.ofNat`, and a square is always same-sign, so neither branch has a
hypothesis to use or to refute and both close with `Nat.zero_le`. `Int` goes
**50 → 51 derived theorems, all 51 with an empty footprint**, one still asserted
(`euclidean_decomposition`, untouched).

The interpretation is not only definitionally accepted but **syntactically
identical** to the `Int` law in all 22 cases — the substituted `Real` axiom and
the `Int` theorem are the same interned term. That is the sharing discipline
`statements.rs` established for `ℤ`, holding across two preludes written months
apart.

### What the model licenses, precisely

It is a **relative consistency** result: the `Real` axiom set has a model whose
theory is derived from nothing, so no `Real`-based reconstruction is vacuous on
account of a contradictory axiom package. The kernel checks the interpretation
of each **axiom**; the step from "every axiom translates" to "every derivation
translates" is the ordinary homomorphism argument over the term language and is
**not** machine-checked — the kernel cannot state it. Recorded in the module
docs rather than left for a reader to assume.

It is **not** a discharge. A theorem about `Int` is weaker than the same
theorem about `ℝ`.

## Alternatives

**Construct `ℝ` by Cauchy sequences.** Rejected: needs `Quot.sound`, which does
not exist (Measurement 2). Adding it means extending a validated,
byte-contracted trusted package with a fifth declaration — a deliberate
enlargement of the trusted surface, not a footprint line item. **Price tag, so
it is on the record:** all 22 laws would become theorems, `real: axiom=30` would
become `axiom=0 quotient=5`, and every real fact's footprint would read
`[Quot.sound]` — plus whatever the Cauchy development itself needs. Nothing in
the current package asks for it.

**Construct `ℝ` by Dedekind cuts.** Rejected: a cut is a predicate `ℚ → Prop`,
and proving two cuts with the same members equal needs `propext` and `funext`.
Neither exists here; the logic prelude is intuitionistic at **zero** trusted
declarations, which is why `Int.eq_em` had to be the *restricted* decidable
equality rather than excluded middle. This route costs two new axioms where the
quotient route costs one primitive.

**Construct `ℚ` first.** Deferred, not rejected — see Consequences. `ℚ` is the
right carrier for LRA (real and rational satisfiability coincide for linear
systems with rational coefficients, so certifying UNSAT over `ℚ` is exactly as
strong as over `ℝ`), and it is quotient-free constructible by the same
normalized-pair trick that worked for `ℤ`: numerator `Int`, denominator `Nat`,
normalized by `Nat.gcd`, which the `Nat` prelude has with its universal property
and Bézout certificates. It is not built today because **no axiom in the package
needs it**: `ℚ` would discharge exactly the same 22 laws `ℤ` already models, at
the cost of a gcd-normalization sub-development. The crux lemma, identified and
recorded so the next lane does not have to find it: `normalize` is a function of
the cross-multiplication class (`a·d = c·b ⊢ normalize (a,b) = normalize (c,d)`),
and every associativity/distributivity law follows from it plus
`normalize (n·k, d·k) = normalize (n, d)`.

**Redefine `Real := Int`.** Rejected outright as dishonest: it would silently
weaken every reconstructed LRA theorem into a statement about integers while
every gate stayed green.

## Consequences

- The `Real` axiom count stays at 30 and is now *understood*: it is the size of
  an ordered-ring interface, not a debt against `ℝ`. Reporting it next to
  `nat: 0` and `integer: 1` without that context has been misleading.
- The vacuity risk on every LRA/SOS reconstruction is eliminated, and the
  elimination is a checked artifact rather than an argument.
- `Int.sq_nonneg` exists, so the SOS route now has an integer counterpart to its
  nonnegativity primitive.
- **The real elimination route is now visible and is not "construct `ℝ`":**
  parameterise the consumers over the ordered-ring interface, so a Farkas
  refutation becomes `∀ (R : Type) (add mul neg …) (zero one : R) (le lt : R → R → Prop),
  <22 law hypotheses> → <refutation>` — a theorem with an empty footprint that
  is *stronger* than today's `Real`-specific statement, and which recovers the
  current statement by instantiation at `Real`. That makes the 30 axioms
  unnecessary rather than proved. It is a change to
  `axeyum-solver/src/reconstruct/arithmetic.rs`, not to the kernel.
- Revisit when: a `Real` axiom mentioning `inv`, `div`, a supremum or
  Archimedean-ness is proposed (build `ℚ`, then reconsider `ℝ`), or when
  `Quot.sound` is proposed for the quotient package (redo this accounting
  first). `the_real_package_has_no_inverse_completeness_or_archimedean_axiom`
  and `the_quotient_package_has_no_soundness_primitive` fail loudly in both
  cases.
