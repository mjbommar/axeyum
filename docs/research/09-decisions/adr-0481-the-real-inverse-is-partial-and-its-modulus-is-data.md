# ADR-0481: the real inverse is partial, its modulus is data, and both halves of that are theorems

Status: accepted
Date: 2026-08-18
Index-summary: ℚ becomes a **field** (`Rat.mul_inv_cancel`, axiom-free — `Rat.inv` had existed with no law about it since the prelude was written) and ℝ gets Bishop **apartness**; the partiality of `x⁻¹` is recorded as two proved obstructions rather than a scoping note — `CReal.no_total_inverse` refutes every total inverse, and `pos_of_pos_bound`/`pos_bound_of_lt` show `0 < x` and `∃ k, 1/(k+1) ≤ x` are the same `Prop`, so the separating **modulus** must be data while the proof need not be

## Context

[ADR-0468](adr-0468-real-is-constructed-as-a-setoid-over-the-rationals.md) built
ℝ as a Bishop setoid of regular ℚ-sequences at **zero** trusted declarations and
closed all 22 ordered-commutative-**ring** laws over it;
[ADR-0479](adr-0479-complex-is-a-pair-setoid-over-creal-and-carries-no-order.md)
did the same for ℂ. What neither has is any *field* structure: no multiplicative
inverse, no division, no `abs`, no `sqrt`, no completeness.

The inverse is the first operation in the whole tower that is **not defined
everywhere**, and it is the first place where the constructive discipline stops
being bookkeeping. Classically the domain is `{x | x ≠ 0}`; constructively
`¬(x ≈ 0)` is too weak to compute with and the domain is `{x | x # 0}` — the
reals *apart* from zero. Turning the second into the first is Markov's
principle, which this kernel does not have.

Two things had to be measured before any of that could be built.

**First, ℚ was not a field.** `Rat.inv` has existed since the rational prelude
was written, as a definition — a three-way dispatch on the numerator's sign,
`inv 0 = 0` by the usual total convention — and **nothing anywhere said it
inverted anything**. `Rat.div a b := a · b⁻¹` inherited that. So the development
had 22 ordered-*ring* laws and an operation named `inv`, and the gap between
those two is exactly the gap between a ring and a field. Any real inverse rests
on the rational one, so this was a prerequisite that no plan had listed.

**Second, the shape of the partiality was unmeasured.** "The inverse needs
`x # 0`" is a sentence that could mean several different things in a kernel with
no classical axioms, and getting it wrong in either direction is expensive: too
strong a reading forbids a definition that is in fact available, too weak a one
invents a total operation that cannot exist.

## Decision

**Apartness is `lt` both ways; the inverse's partiality is recorded as two
proved obstructions; and the thing that must be data is the modulus, not the
proof.**

### 1. ℚ is a field

`Rat.mul_inv_cancel : ∀ q, 0 < q → q · q⁻¹ = 1`, axiom-free. It is the only
proof in the field development that touches the representation, because
`Rat.inv q` is stuck until `Rat.num q` is in constructor form:

- `num q = ofNat 0` — `eq_zero_of_num_zero` gives `q = 0` and `lt_irrefl` closes;
- `num q = negSucc m` — `Int.lt Int.zero (negSucc m)` **ι-reduces to `False`**,
  `Int.lt` being a four-case definition and this the mixed-constructor case, so
  the branch is `False.rec` with no lemma at all;
- `num q = ofNat (k+1)` — `q⁻¹` **is** `normalize (den q) (k+1)`, and
  `num q · num q⁻¹ = ofNat (den q · den q⁻¹)` in three steps, after which
  `mul_cross` plus `int_mul_right_cancel` leave
  `num (q·q⁻¹) = ofNat (den (q·q⁻¹))`, i.e. `eq_of_cross` against `1/1`.

The dispatch is **not transcribed into the proof**: `rat_prelude::defs::inv_body`
is factored out of the definition, `Rat.inv q` is `inv_body q (num q)` by
definition, and the case split's motive names the same construction the
definition does.

The hypothesis is `0 < q` and not `q ≠ 0` deliberately. Over ℚ the two are one
*proved* case split apart (`Rat.le_or_lt`); over ℝ they are not, and stating the
rational law positively is what lets the real construction consume it without a
sign decision it cannot make. The negative branch is left unproved —
`inv q = -(inv (-q))` recovers it when something needs it.

Everything else derives from that law and the 22 alone, in `group.rs`'s
discipline (no numerator, no denominator, no cross-multiplication), so each is a
theorem of *ordered fields* that transcribes one level up unchanged:
`inv_pos`, `sub_mul`, `mul_inv_sub_one`, `inv_sub_inv`, `inv_le_of_pos_le`.

### 2. `CReal.Apart x y := lt x y ∨ lt y x`

Bishop's apartness verbatim, not an encoding of it: `CReal.lt` already carries
the separation as a **rational gap** (`∃ q, 0 < q ∧ x + q ≤ y`), which is
exactly the data `#` carries. Consequently every law — `apart_symm`,
`apart_irrefl`, `apart_congr`, `not_equiv_of_apart` — is a rearrangement of the
strict order rather than a new estimate, and none needed a new ℚ lemma.

`not_equiv_of_apart : Apart x y → ¬(Equiv x y)` is **one-way on purpose**. The
converse is Markov's principle; it is neither proved nor assumed.

The rejected shape is `Apart x y := ¬(Equiv x y)`, which satisfies symmetry,
irreflexivity and the congruence just as happily and is precisely the relation
the inverse cannot be defined over.

### 3. The partiality is two theorems, not a scoping note

- **`CReal.no_total_inverse : ∀ (f : CReal → CReal), ¬ ∀ x, x · f x ≈ 1`.**
  Evaluate at `zero`. This is the field analogue of ADR-0479's
  `Complex.no_compatible_order`: the missing structure is missing as a proved
  obstruction, so "the inverse is partial" cannot quietly become "the inverse is
  not built yet".
- **`CReal.pos_of_pos_bound` and `CReal.pos_bound_of_lt`** say `0 < x` and
  `∃ k, 1/(k+1) ≤ x` are the **same proposition**. The separating modulus
  therefore always exists — and it exists inside an `Exists`, which is a `Prop`,
  so `Exists.rec` eliminates only into `Prop` and that `k` can never be
  extracted into a `CReal`.

### 4. What must be data is the **modulus**, not the proof

This is the measurement that changed the design, and it corrects the obvious
reading. A function may **take** a `Prop` argument and return a `Type`; what it
may not do is **branch** on one. So:

- `inv : (x : CReal) → Apart x zero → CReal` is **not** definable. `Apart` is an
  `Or`, and choosing which of the two reciprocals to compute eliminates a
  disjunction into `Type`. That is the reason CoRN carries apartness in `CProp`,
  a `Type`-valued logic, rather than in `Prop`.
- `inv : (x : CReal) → (k : Nat) → PosBound x k → CReal` **is** definable, with
  `PosBound x k := le (ofRat (natDivSucc 1 k)) x` — no disjunction anywhere. The
  representative sequence depends on `k` alone; the proof is used only to
  discharge `CReal.mk`'s `Prop`-valued regularity field.

`CReal.PosBound` is therefore admitted as the inverse's domain predicate, with
the modulus explicit, and that signature is the one the construction will use.

## Consequences

- `Rat` gains seven declarations, `CReal` eleven; both trusted surfaces stay at
  **0**, measured with `nat_axiom_inventory --include-constructed` and pinned by
  value in `gen-lean-axiom-ledger.py --check`.
- `Rat.div` finally has a law behind it, since it is defined through `Rat.inv`.
- The 22 ordered-ring laws are untouched: no field law is one of them, so no
  count moves and the `Real` package's 30 axioms are unaffected (ADR-0468 retires
  those by deletion in phase R4, not by exhibiting a model).
- **`CReal.inv` itself is not built by this ADR.** Its design is fixed here and
  the ℚ-side lemmas it needs are proved; the remaining work is index arithmetic,
  costed in `docs/plan/notes/creal-field.md`.

## What this ADR deliberately does not do

- **No `Rat.inv` law on the negatives.** One case split away, unneeded.
- **No `abs`, `max`, `min`.** They need no completeness and are reachable —
  `Rat.abs q := normalize (ofNat (natAbs (num q))) (den q)` is a definition, not
  a case split — but they are order theory, not field theory, and belong with a
  separate slice.
- **No cotransitivity of `lt`** (`x < y → ∀ z, x < z ∨ z < y`), the law that most
  sharply distinguishes real apartness from mere inequality. It is provable
  constructively and it costs two full estimates of `le_add_of_nonneg`'s size,
  because the third point has to be compared at an index computed from the gap.
- **No `sqrt`, no completeness, no supremum.** Each is its own ADR. Note that
  ℂ's `abs` needs `sqrt` needs completeness, so ADR-0479's gap does not close
  here.
- **No Markov's principle**, in any disguise. `¬(x ≈ 0) → x # 0` is not proved,
  not assumed, and not used.

## Alternatives considered

**Apartness as `¬(Equiv x y)`.** Cheapest to state, satisfies the three laws,
and useless: it is not the domain of any inverse and it makes
`not_equiv_of_apart` a triviality instead of a one-way bridge.

**Apartness in a `Type`-valued logic (CoRN's `CProp`).** Would make
`inv : (x : CReal) → Apart x zero → CReal` definable by carrying the disjunction
as data. Rejected: it duplicates the whole logic prelude for one operation, and
the measurement in §4 shows the same effect is had by making the *modulus*
explicit — a `Nat` argument — while leaving every proposition in `Prop`.

**A total `CReal.inv` with `inv 0 = 0`, mirroring `Rat.inv`.** This is what the
ℚ layer does, and it is right there because ℚ's equality is decidable, so the
convention costs nothing and no theorem is weakened. Over ℝ it is not available:
deciding `x ≈ 0` is not constructive, so a total `inv` would have to be defined
by a case analysis that does not exist. `no_total_inverse` records the outcome
rather than the reasoning.

**Stating `mul_inv_cancel` over `q ≠ 0`.** Equivalent over ℚ, and one case split
more expensive at every use site in the real construction, which never has a
`≠` to hand — it has a positive rational gap.
