# ADR-1584: forgetful projections, more cross-carrier theorems, a retirement measurement, and `Alg.OrderedRing` (amends ADR-1578)

Status: accepted
Date: 2026-09-03
Lane: `structures-2`

Index-summary: ADR-1578 built the ten-record `Magma..Field` spine with no
inheritance — applying a `Monoid` theorem to a `CommMonoid` instance is a
`TypeMismatch`, measured. This ADR closes that gap with seven forgetful
projection `Definition`s (`CommMonoid.toMonoid`, `Group.toMonoid`,
`CommGroup.toGroup`, `Ring.toMonoid`, `Ring.toCommGroup`, `CommRing.toRing`,
`Field.toCommRing`), six more generic theorems (`mul_left_cancel`, `neg_neg`,
`sub_self` with a generic `Alg.sub`, `mul_neg_one`, `pow_add` with a generic
`Alg.npow`, `mul_le_mul_of_nonneg_left`), a retirement measurement against
existing ℕ/ℤ/ℚ hand proofs (three genuine type-level matches: `Int.
add_left_cancel`, `Rat.neg_neg`, `Rat.sub_self`, plus `Int.mul_le_mul_of_
nonneg_left`/`Rat.mul_le_mul_of_nonneg_left` both — five total, none deleted
per ADR-1581's rule), and `Alg.OrderedRing` (a `Ring` plus `le` and five
order laws) with ℤ/ℚ instances. Every declaration is axiom-free and admits
through the trusted kernel gate on the first attempt after direction bugs in
the proof terms were fixed by the kernel's own `TypeMismatch` messages.
Index-status: accepted

## Context

ADR-1578's own Evidence section measured the gap this ADR closes: "applying
the theorem (typed over `Alg.Monoid`) to the `Alg.CommMonoid` instances is a
real `TypeMismatch`, because this spine has no inheritance." The spine is
flat by design (no coercion, no instance resolution — see ADR-1578's
Alternatives section), so the only way a `Monoid`-level theorem reaches a
`CommMonoid` value is an explicit forgetful projection the caller applies by
hand. Building those, and using them for a real payoff (`mul_neg_one`
below), is this ADR's first deliverable.

ADR-1578 also proved three generic theorems and left the retirement
question — which existing hand-proved carrier-specific lemmas a generic
theorem could replace — entirely open. ADR-1581 (a sibling lane, same day)
found the general form of the answer building generic order-chain theorems
for `linarith`: **a hand proof's citations are necessary but not sufficient
for retirement** — a candidate can match by type and still be blocked
because something else in the build sequence cites the specific declaration
being replaced, or because the replacement itself needs its own prerequisites
declared earlier than the site allows. This ADR applies that same standard
to structure-level retirement rather than order-chain retirement, and does
not delete anything — see Decision §3.

## Decision

### 1. Seven forgetful projections, all `Definition`s at height 1

`<Record>.mk` applied to the source record's own selectors, in the target
record's field order. Four are literal PREFIX projections (the target's
field list is a prefix of the source's, in the same order, because the
spine was built by literally extending the earlier record's field-spec list
— see ADR-1578's `comm_monoid_fields()` etc.): `CommMonoid.toMonoid`,
`CommGroup.toGroup`, `CommRing.toRing`, `Field.toCommRing`. Two select a
non-contiguous subset with no derivation: `Group.toMonoid` (Monoid's six
fields are Group's fields at indices 0,1,2,4,5,6 — INV dropped) and
`Ring.toMonoid` (the multiplicative reading: carrier/mul/one/mulAssoc/
mulOneL/mulOneR, every one a direct Ring selector).

**`Ring.toCommGroup` (additive) is the one projection needing derivation**:
`CommGroup`'s `identL`/`invL` have no `Ring` primitive (`Ring` carries only
`addZero`/`negAdd`, the RIGHT-handed unit/inverse laws). Both are derived
inline from `addComm` + the RIGHT-handed field, the exact `derive_left_unit`
shape ADR-1578's own instance builders use for `Rat`'s missing `one_mul`
and `Int`'s missing `zero_add` — generalized here to a second helper,
`derive_inv_left`, for the two-sided-inverse law rather than a unit law.

**Evaluation test and negative control** (deliverable 2's explicit ask):
`int_comm_ring_projects_to_monoid_and_mul_one_reduces` projects
`Int.commRing` down to a `Monoid` (`CommRing.toRing` then `Ring.toMonoid`)
and reads `mulOneR`'s type off the projection BY REDUCTION, `def_eq`-compared
against `Int.mul_one`'s own rendered type (not a doc comment). The negative
control: the projected `Monoid`'s `carrier` selector is `def_eq` to `Int`
itself, not a fresh/opaque carrier — a projection that silently produced an
unrelated carrier would still type-check as `Monoid`, since `carrier :
Sort 1` accepts anything, so this is a real check, not decoration.

**The payoff `monoid_ident_unique_applies_through_the_comm_monoid_to_monoid_
projection`** closes the exact gap ADR-1578 measured: `Alg.monoidIdentUnique
(CommMonoid.toMonoid Nat.commAddMonoid) 0 Nat.add_zero` type-checks and
reduces to `Eq Nat 0 0`, where the bare (unprojected) application is a
`TypeMismatch`.

### 2. Six more generic theorems

- **`Alg.mul_left_cancel`** (`Group`): `op a b = op a c -> b = c`. The
  `b = e·b = (a'·a)·b = a'·(a·b) = a'·(a·c) = (a'·a)·c = e·c = c` chain
  (`a' := inv a`), the same shape `mul_left_cancel_of_pos`'s conditional
  Nat version approximates without a true inverse.
- **`Alg.neg_neg`** (`Group`): `inv (inv a) = a`. Not new proof engineering
  — a DIRECT instantiation of `Alg.groupInvUnique` at `(x := inv a, b :=
  inv (inv a), c := a)`, `h1 := invL(inv a)`, `h2 := invL a`.
- **`Alg.sub`** (`Definition`, `Ring`): `sub a b := add a (neg b)`, matching
  `Rat.sub`'s/`Int.sub`'s own definitions exactly (`group.rs`'s
  `declare_subtraction` module doc). **`Alg.sub_self`**: `sub x x = zero`,
  proved by `negAdd x` alone (the statement unfolds by beta+delta to
  `add x (neg x)`).
- **`Alg.mul_neg_one`** (`Ring`): `mul x (neg one) = neg x`. Built via the
  projections rather than deriving `mul a (neg b) = neg (mul a b)` directly
  — `Ring.toCommGroup` then `CommGroup.toGroup` gives an additive `Group`,
  and `Alg.groupInvUnique` applied there (with `add (mul x (neg one)) x =
  zero` derived from `distribL` + the already-proved `Alg.ringMulZero` +
  `mulOneR`, and `add x (neg x) = zero` being `negAdd x` directly) gives the
  result. This is the projections' payoff use case the brief asked for.
- **`Alg.npow`** (`Definition`, `Monoid`): `Nat.rec` over the record's own
  `op`, RIGHT-multiplying (`npow x (succ n) = op (npow x n) x`), matching
  `Rat.pow`'s/`Int.pow`'s own recursion convention exactly (not the
  left-multiplying convention a first draft used, which forces an extra
  self-commutation lemma the right-multiplying form does not need — see
  below). Concrete evaluation at `x := 4`, `n := 0,1,2` (three discriminating
  small-magnitude points) confirms `0, 4, 8`.
- **`Alg.pow_add`** (`Monoid`): `npow x (m+n) = op (npow x m) (npow x n)`,
  by induction on `n` (the argument `Nat.add` recurses on). The base case
  needs only `identR`; the step needs only `assoc` and the induction
  hypothesis — **no self-commutation lemma**, because `npow`'s own
  right-multiplying recursion matches `add`'s own recursion direction
  exactly (the step reduces to one `congr_arg` on the IH plus one direct
  `assoc` application, nothing more). A first design (left-multiplying
  `npow`) would have needed `x` to commute with its own power, an extra
  induction this ADR avoided entirely by matching the recursion direction to
  `Nat.add`'s instead.

  **Measured, not assumed**: `Alg.npow(Rat.commMulMonoid, x, n)` IS `def_eq`
  to `Rat.pow(x, n)` at SYMBOLIC `x, n` — the whole recursion, not merely at
  one value the way ADR-1578's `detR`/`Rat.det` measurement was (`n = 1`
  only). Both are literally the same `Nat.rec` application once `Monoid`'s
  selectors reduce through the projection chain to `Rat.mul`/`Rat.one`.

### 3. The retirement measurement — five genuine matches, nothing deleted

Grepped the three preludes for the hand-proved carrier-specific mirror of
each new generic theorem (`kernel_theorem_inventory`-style, not source text —
compared by TYPE, checked with `Kernel::infer` + `Kernel::def_eq`, never by
reading a doc comment):

| generic theorem, instantiated | hand-proved target | result |
| --- | --- | --- |
| `mul_left_cancel(Int.addGroup)` | `Int.add_left_cancel` | **same type** — retirement candidate |
| `mul_left_cancel(?, multiplicative)` | `Nat.mul_left_cancel` | **absent under this name**; only `Nat.mul_left_cancel_of_pos` exists, a CONDITIONAL (positivity-hypothesis) shape — `Nat`'s multiplicative monoid has no two-sided inverse, so this theorem does not generalize it at all |
| `neg_neg(Rat.addGroup)` | `Rat.neg_neg` | **same type** — retirement candidate |
| `neg_neg(Int.addGroup)` | `Int.neg_neg` | **absent as a kernel theorem**: `int_prelude/gcd.rs`'s `neg_neg` is a private Rust proof-term HELPER (`pub(super) fn neg_neg`), never declared into the kernel environment — so this instantiation is a NEW top-level fact for `Int`, not a retirement |
| `sub_self(Rat.ring)` | `Rat.sub_self` | **same type** — retirement candidate (`Rat.sub` already IS `add a (-b)`, matching `Alg.sub` exactly, not a coincidence) |
| `mul_neg_one(?)` | `Int.neg_one_mul` | **wrong direction**: `neg_one_mul` is the MIRRORED LEFT form (`(-1)·x = -x`), not this theorem's RIGHT form (`x·(-1) = -x`); bridging needs `mul_comm`, which this theorem is deliberately stated without (it holds at `Ring`, not only `CommRing`) |
| `mul_neg_one(?)` | `Rat.mul_neg_one`/`Rat.neg_one_mul` | **absent entirely** on either carrier |
| `mul_le_mul_of_nonneg_left(Int.orderedRing)` | `Int.mul_le_mul_of_nonneg_left` | **same type** — retirement candidate |
| `mul_le_mul_of_nonneg_left(Rat.orderedRing)` | `Rat.mul_le_mul_of_nonneg_left` | **same type** — retirement candidate |
| `pow_add(Rat.commMulMonoid)` | `Rat.pow_add` | **`def_eq`** at symbolic `x, m, n` (stronger than a type match — the two THEOREM STATEMENTS are the identical term), because `npow` and `Rat.pow` are themselves `def_eq` (§2) |

**Five type-level matches** (`Int.add_left_cancel`, `Rat.neg_neg`,
`Rat.sub_self`, `Int.mul_le_mul_of_nonneg_left`,
`Rat.mul_le_mul_of_nonneg_left`), plus one full `def_eq` match
(`Rat.pow_add`, six candidates total). **None were deleted.** Per ADR-1581's
rule, a type match is necessary, not sufficient: `Int.mul_le_mul_of_
nonneg_left` in particular is named in `linarith`'s own `int.rs` emitter
vocabulary (`sign_product.rs` cites it directly), and ADR-1581 §2's rule —
"a lemma the emitter depends on cannot be retired to the emitter" — means
retiring it needs checking whether `linarith::declare`'s own build-sequence
position would still resolve, which this lane did not check. The other four
were not checked against the FULL build-sequence-position question either
(ADR-1581 §1's finding: a type match says nothing about whether the
replacement's own prerequisites are declared early enough at the retirement
site). Recording this as blocked-pending-check, not as blocked outright —
the type match itself is real and reproducible (see the `retirement_*`
tests).

### 4. `Alg.OrderedRing`: `Ring`'s 15 fields restated, plus `le` and five laws

`le : α -> α -> Prop`, `le_refl`, `le_trans`, `le_antisymm`,
`add_le_add_left : ∀ a b c, le a b -> le (add c a) (add c b)`, `mul_nonneg :
∀ a b, le zero a -> le zero b -> le zero (mul a b)` — 21 fields total,
admitted at `Sort 2` with the same `Sort 1`-refused universe control every
other record in the spine carries (`ordered_ring_fields()` in
`structures.rs`, following the exact `FieldSpec`/`declare_record` machinery
ADR-1578 built, with two new field-shape combinators, `rel_field` for the
`α -> α -> Prop` relation type and four Law-kind combinators for the order
axioms — the relation's own type lives at `Sort 1` by the same `imax`
argument `binop_field` already relies on, so it is a `Data`-kind field, not
`Law`).

**Instances**: `Int.orderedRing` (every field a direct `Int.*` selector —
`Int` already has all six order-law names under exactly these types) and
`Rat.orderedRing` (`add_le_add_left` has no `Rat` primitive and is derived
from `add_le_add` + `le_refl`: `add_le_add(c,c,a,b,le_refl c,hab) : le
(c+a)(c+b)`).

**`Alg.mul_le_mul_of_nonneg_left`**: `0 <= a -> b <= c -> a*b <= a*c`. Proof
avoids ever computing `mul a (neg b)`: `d := add (neg b) c` is shown `>= 0`
(`add_le_add_left` plus a transport of the resulting `le` fact along the
derived `add (neg b) b = zero`, using a new generic `subst` helper —
`Eq.rec` transport for an ARBITRARY predicate, not only `Eq`, generalizing
`congr_arg`'s shape); `b + d = c` (`assoc` + `negAdd` + a derived additive
left-unit); so `a*c = a*b + a*d` (`distribL`); `a*d >= 0` (`mul_nonneg`), so
`a*b <= a*b + a*d = a*c` (`add_le_add_left` again, this time at
`(zero, a*d, a*b)`).

### 5. Would `linarith`'s emitter re-target at `Alg.OrderedRing`?

**Structurally reachable, but not with the record as built here, and this
ADR does not attempt it.** `linarith`'s certificate SEARCH
(`crate::linarith`, `Coeff`/atom-index arithmetic) is already carrier-agnostic
— it knows nothing about `Nat`/`Int` types. Only the EMISSION layer
(`linarith::nat`, `linarith::int`) is per-carrier, and it works by citing
FIXED `NatPrelude`/`IntPrelude` constants (`p.add_le_add_left`,
`ip.le_trans`, …) rather than taking a structure VALUE and projecting
through its selectors. Retargeting at `Alg.OrderedRing` needs three things,
none done here:

1. **The record itself is missing fields the emitter's fixed chain cites.**
   ADR-1581 names `add_le_add_right`, `le_of_add_le_add_right`, and the
   entire `lt`/strict fragment (`add_lt_add_of_le_of_lt`, `mul_pos`) as part
   of `linarith::int`'s documented vocabulary — `Alg.OrderedRing` as built
   here has none of them. Some are cheaply derivable from what exists
   (`add_le_add_right` from `add_comm` + `add_le_add_left`, the same
   `derive_*` pattern used throughout this ADR); the `lt` fragment is a
   genuinely new set of fields, not a derivation.
2. **A generic numeral-construction routine.** `linarith`'s literal-multiplier
   unrolling (ADR-1581 §3, `Int.mul` via repeated `left_distrib`+`mul_one`)
   currently builds a numeral as an `Int`-specific term. Over an abstract
   `OrderedRing` the same unrolling is available (`distribL`/`mulOneR` are
   both record fields), but it has to build `n` as `R.add R.one (R.add R.one
   …)` generically rather than reaching for `Nat.succ`/`Int`'s own literal
   representation.
3. **Decoupling the emission closures from `IntDev`/`NatDev`.** `linarith::
   declare`'s builder closures are typed against the concrete dev-helper
   structs (the same "dev-helper layer hardcodes a carrier" hazard
   `kernel-proof-engineering.md` documents), not against an abstract
   structure argument — this is a real refactor, not a drop-in swap.

None of this is attempted here; the record and the one generic theorem built
in this ADR are the first building block a future lane pointed at this
question would need, not the retargeting itself.

## Alternatives

**Give the spine real inheritance instead of hand-built projections.**
Rejected, same reasoning as ADR-1578's own Alternatives section: no
coercion mechanism exists in this kernel, and nesting one record inside
another means every consumer projects through the nested record anyway —
no reduction benefit, and it would be a much larger change to land now.

**Retire the five type-matched hand proofs immediately.** Rejected per
ADR-1581's explicit rule — a type match is necessary, not sufficient. Left
as future work with the exact blocker named (build-sequence position,
unchecked here) rather than silently deferred.

**Build `Alg.npow` left-multiplying (matching a naive first reading of
`Monoid.npow`'s usual mathlib convention).** Rejected after measuring the
cost: it forces an extra self-commutation lemma (`x` commutes with its own
power) that the right-multiplying convention, matching `Rat.pow`'s own
recursion, does not need at all — and the right-multiplying form also turns
out to be `def_eq` to `Rat.pow`, which the left-multiplying form would not
have been.

## Evidence

Measured 2026-09-03 on this host. `cargo test -p axeyum-lean-kernel --lib --
rat_prelude::algebra_ext:: --test-threads=4`: 15 tests, all green — the
projection evaluation test + negative control, the `CommMonoid.toMonoid`
payoff test, one evaluation test per new `Definition` (`Alg.sub` symbolic
`def_eq`, `Alg.npow` concrete at three points), one concrete-and-symbolic
(or symbolic-only, where the concrete half is the structure instantiation
itself) instantiation test per generic theorem at two carriers each, and
five retirement-measurement tests. `cargo test -p axeyum-lean-kernel --lib
-- nat_prelude::structures:: rat_prelude::algebra_instances::
--test-threads=4`: 6 tests, all still green (ADR-1578's own suite
unaffected). Full sweeps: `cargo test -p axeyum-lean-kernel --lib --
rat_prelude:: --test-threads=4`: **258 passed, 0 failed**; `cargo test -p
axeyum-lean-kernel --lib -- nat_prelude:: --test-threads=4`: **424 passed, 0
failed**. `cargo clippy -p axeyum-lean-kernel --lib --tests -- -D warnings`:
clean. Every new declaration's `axiom_footprint` is `[]` (confirmed by a
throwaway dump example, run and discarded, and independently by
`validate-facts.py`'s own footprint field per fact below).

**Two real direction bugs the kernel caught on the first build attempt**,
worth recording because they are exactly the failure class
`kernel-proof-engineering.md`'s `le_congr`/direction-bug entry predicts: (1)
the derived `Rat.orderedRing.add_le_add_left` term's lambda-binder order
did not match the record field's own stated `∀ a b c` order (`c` was bound
outermost instead of `a`) — a genuine `TypeMismatch` on `rat_prelude_builds`,
the whole-prelude smoke test, not merely a narrow unit test; (2) two
`symm_of` calls in `build_mul_neg_one`/`build_mul_le_mul_of_nonneg_left` had
their `(a, b)` arguments in the wrong order relative to the hypothesis's
actual inferred type. Both were found and fixed by reading the kernel's own
`TypeMismatch { expected, got }` output, not by manual proof review.

**Fact ledger.** Six new facts, one per generic theorem carrying real
mathematical content (no fact for the seven projections or the two new
`Definition`s, `Alg.sub`/`Alg.npow`, matching ADR-1578's own precedent of
not fact-ing the record declarations or `sumR`/`altSignR`/`detR`):
`F:alg-mul-left-cancel`, `F:alg-neg-neg`, `F:alg-sub-self`,
`F:alg-mul-neg-one`, `F:alg-pow-add`, `F:alg-mul-le-mul-of-nonneg-left`.
`python3 scripts/validate-facts.py`: 2733 facts, 0 errors.
`check-fact-depends-derived.py --fix`: one missing edge added
(`F:alg-mul-neg-one` -> `F:eq-symm`). `check-settled-fact-statements.py
--write`: `unpinned=0`.

## Consequences

**Easier.** A future "even later" structure (an `OrderedField`, a module
over a ring) has both the projection pattern and the `subst` transport
helper (generalizing `congr_arg` to an arbitrary predicate, not only
`Eq`-of-`f`) ready to reuse, and the retirement-measurement discipline
(`retirement_*` tests comparing by `Kernel::infer` + `Kernel::def_eq`, never
by reading a doc comment) is now a repeatable pattern with five worked
examples.

**Harder.** `linarith`'s emitter is now a NAMED, concrete future target
(§5) rather than an open question, but actually retargeting it is real work
this ADR explicitly scoped out — a future lane reading "OrderedRing exists
now, why doesn't linarith use it" needs this section, not just the record.

**Revisit when** a lane retires one of the five type-matched hand proofs
(checking the build-sequence-position question ADR-1581 names) or attempts
the `linarith`-over-`OrderedRing` retargeting named in §5.
