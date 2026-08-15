# Lane: real-keystone — what ℝ costs, and the checked model of the `Real` axioms

<!-- plan-section: lane-status -->

**Lane state (`WIP`, real-keystone, 2026-08-15).** The strand item said ℝ was the
whole of the remaining keystone — 30 axioms, 0 derived theorems. Two
measurements taken before writing code changed what the item is.

**1. The `Real` prelude is not an axiomatization of ℝ.** Enumerated rather than
read off the module's own "axiomatized linear ordered field" summary: 8 carrier
and operation declarations, 22 laws, and **no `inv`, no `div`, no completeness,
no Archimedean, no density, not even totality**. It is an **ordered commutative
ring with 1**. Nothing in it distinguishes ℝ from ℚ, and every one of the 22 laws
is true of ℤ. The carrier's *name* was doing the work its axioms were not, and
the strand item inherited that reading.

**2. `Quot.sound` does not exist in this kernel.** `quotient.rs` admits a package
of `PACKAGE_LEN = 4` — `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` — pinned by
`canonical_package_admits_exactly_four_and_is_idempotent`, and no prelude calls
`add_quotient_package` at all. Without `Quot.sound` nothing proves two `Quot.mk`s
equal, so **a Cauchy-sequence ℝ is not expensive here, it is inexpressible**.
Three comments and the ℤ diary say otherwise (that a quotient would merely put
`Quot.sound` in every footprint); they describe Lean's package, not ours. All
three corrected, and the measurement is now a test.

**What landed instead of a construction.** `build_int_model_of_arith`
(`src/arith_model.rs`) computes each `Real` law's type with the eight
carrier/operation constants substituted — from the environment, never typed by
hand — and admits a theorem of that type proved by the corresponding `Int`
theorem, kernel-checked at admission:

```
Real: 30 trusted declarations = 8 interpreted symbols + 22 modelled laws;
22/22 witnesses have an EMPTY axiom footprint,
22/22 are syntactically the Int law
```

21 were already ℤ theorems. The 22nd, **`Int.sq_nonneg`**, is proved here:
`int_theorem_inventory` goes **50 → 51 derived, all 51 with an empty footprint**,
1 still asserted (`euclidean_decomposition`, untouched). The `identical` column
is stronger than admission — the substituted `Real` axiom is the *same interned
term* as the `Int` law in all 22 cases, two preludes written months apart
agreeing to the term.

**Stated narrowly, because it is easy to overclaim.** This is **relative
consistency**: the `Real` axiom set has a model whose theory is derived from
nothing, so no Farkas/SOS reconstruction is vacuous on account of a
contradictory package — a real, previously unmeasured risk, since a
contradictory package makes every reconstruction "valid" while every gate stays
green. It is **not** a discharge: `real: axiom=30` is unchanged and untouched,
ℤ is not ℝ, and the step from "every axiom translates" to "every derivation
translates" is a homomorphism argument the kernel cannot state.

**Controls held.** `nat_theorem_inventory` **byte-identical** (119 theorems, diff
clean); `nat_axiom_inventory` unchanged at `logic 0, nat 0, real 30, integer 1,
string 1`; `cargo test -p axeyum-lean-kernel` green (255 lib tests, 249 + 6 new,
plus every integration suite); clippy `-D warnings` and
`RUSTDOCFLAGS="-D warnings" cargo doc` clean;
`scripts/check-lean-gate.sh` green and **unchanged at 12 suites, 49 tests, 112
real-Lean checks (floor 105)** — no golden module hash moved, because
`Int.sq_nonneg` is not reachable from any export root. `validate-facts.py`: 96
facts, 0 errors.

**Next, and the trigger is named rather than guessed.** ℚ is the right carrier
for LRA — real and rational satisfiability coincide for linear systems with
rational coefficients — and it *is* quotient-free constructible (`Int` numerator,
`Nat` denominator, normalized by `Nat.gcd`, which sidesteps
`euclidean_decomposition` entirely). It is not built because **no axiom in the
package asks for it**. Build it when a `Real` axiom mentioning `inv`, `div`, a
supremum or Archimedean-ness is proposed;
`the_real_package_has_no_inverse_completeness_or_archimedean_axiom` fails on that
day. The crux lemma is recorded so the next lane does not rediscover it:
`normalize` must be a function of the cross-multiplication class
(`a·d = c·b ⊢ normalize (a,b) = normalize (c,d)`), the ℚ analogue of
`subNatNat`'s borrow.

**The route that actually eliminates the 30 is not constructing ℝ.** Parameterise
`axeyum-solver/src/reconstruct/arithmetic.rs` over the ordered-ring interface, so
a Farkas refutation becomes `∀ (R : Type) …, <the 22 laws> → <refutation>` — an
empty-footprint theorem *stronger* than today's `Real`-specific statement, which
recovers it by instantiation. That makes the 30 axioms unnecessary rather than
proved, and it is a solver change, not a kernel one.

Full reasoning: [ADR-0456](../../research/09-decisions/adr-0456-real-is-an-ordered-ring-modelled-by-int.md)
and [`docs/mathematics-2026-08/diary-real-keystone.md`](../../mathematics-2026-08/diary-real-keystone.md).

<!-- plan-section: landed-changes -->

| 2026-08-15 | (pending) | `Real`'s 30 axioms measured as an ordered-ring package (no inverse/completeness/Archimedean) and modelled in the constructed ℤ: `build_int_model_of_arith` admits 22 kernel-checked witnesses, all with an empty axiom footprint and all syntactically the `Int` law. `Int.sq_nonneg` proved (`Int: 50 → 51` derived, 51 empty footprints). Measured and pinned that this kernel has **no `Quot.sound`**, so a quotient ℝ is inexpressible, not merely expensive — correcting three comments and the ℤ diary. ADR-0456. |
