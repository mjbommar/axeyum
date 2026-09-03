# ADR-1588: a Setoid-flavored `AlgS.*` spine, so `CReal` can be an instance

Status: accepted
Date: 2026-09-03
Lane: `structures-setoid`

Index-summary: ADR-1587 §4 measured the gap and named the fix: `CReal`'s
carrier equality is `CReal.Equiv`, never `Eq`, so it cannot be an `Alg.*`
(ADR-1578) instance — every law field there is `Eq (op a b) (op b a)`, the
wrong proposition for a setoid. This ADR builds a second, independent spine
`AlgS.Magma .. AlgS.CommRing` (stopping short of `Field`, which needs
`Apart` — out of scope) whose records carry `carrier`, a caller-supplied
`equiv` relation with `equiv_refl`/`equiv_symm`/`equiv_trans`, the
operations, explicit congruence fields per operation (`opCongr`/`addCongr`/
`mulCongr`/`negCongr` — what `Eq` gets for free and a setoid must carry by
hand), and every law restated with `equiv` in place of `Eq`. No coercion
exists between the two spines (this kernel has none); instead
`AlgS.<Record>.ofAlg` projects an `Alg.<Record>` value into an `AlgS.<Record>`
one with `equiv := @Eq carrier`, built once per record from `Eq.refl`/
`Eq.symm`/two nested `congr_arg` applications — never duplicating a theorem.
`CReal.commRingS : AlgS.CommRing` is the payoff: every field is an *existing*
`CReal` theorem (the ADR-0512 laws plus `add_congr`/`mul_congr` from
`creal/congruence.rs`), two derived by one `equiv_trans` composition each
(`mulOneL` from `mul_comm`+`mul_one`; `distribR` from `mul_comm`+
`left_distrib`+`add_congr`) — nothing new proved in `creal`. Three generic
theorems (`AlgS.mul_zero`, `AlgS.neg_neg`, `AlgS.sub_self`) are proved once
over `AlgS.Ring` and instantiated at `Int` (through `ofAlg`) and at
`CReal.commRingS` directly, closing ADR-1587's named gap end to end.
Index-status: accepted

## Context

ADR-1578 built a ten-record `Alg.*` spine (`Magma → … → Field`) with every
law stated as `Eq`. ADR-1584/1587 extended it and ran a retirement census;
ADR-1587 §4's widened search hit `CReal.mul_zero`, `CReal.
mul_le_mul_of_nonneg_left`, `CReal.pow_add` and found none is a candidate:
`CReal`'s carrier equality is `CReal.Equiv`, a *defined* relation (ADR-0512),
never literal `Eq`. ADR-0512 itself measured why: 9 of ℝ's 22
ordered-ring laws are stated over `Equiv` (`add_comm`, `add_assoc`,
`add_zero`, `add_neg`, `mul_comm`, `mul_assoc`, `mul_one`, `mul_zero`,
`left_distrib`); the other 13 (the order fragment) are `Eq`-free already.
`docs/research/11-design-review/2026-08-27-architecture-review.md` §3b names
the general pattern this project already uses elsewhere for exactly this
situation — carrying an equivalence and its congruence lemmas explicitly
(the "unrestricted congruence regime") rather than reaching for `Eq.rec`
transport, which only ever works for the kernel's own primitive `Eq`.

`Alg.*`'s design (no inheritance, no coercion, no instance resolution — see
ADR-1578's Alternatives) is a decision worth keeping for the same reasons
there; this ADR does not revisit it, only adds a second spine built the same
way.

## Decision

### 1. A second, independent spine: `AlgS.Magma .. AlgS.CommRing`

Nine records (stopping at `CommRing`; `Field` needs `Apart`, out of scope),
each a fresh `Sort 2` record (same universe-guard shape ADR-1578
established — `carrier : Sort 1` forces it), field-built with the same
`FieldSpec`/`declare_record` machinery ADR-1578 built, adapted so every LAW
field applies the record's own `equiv` VALUE directly (`app2(k, equiv, lhs,
rhs)`, which beta-reduces to `Eq carrier lhs rhs` when `equiv := @Eq
carrier` — the fact the `ofAlg` projections below exploit) instead of the
kernel's `Eq` constant. Field layout, each record independent (no
inheritance, matching `Alg.*`):

| record | fields (index : name) |
| --- | --- |
| `Magma` | 0 carrier, 1 equiv, 2 equivRefl, 3 equivSymm, 4 equivTrans, 5 op, 6 opCongr (7 fields) |
| `Semigroup` | Magma + 7 assoc (8) |
| `Monoid` | 0-6 as Magma, 7 e, 8 assoc, 9 identL, 10 identR (11) |
| `CommMonoid` | Monoid + 11 comm (12) |
| `Group` | 0-6 as Magma, 7 e, 8 inv, 9 invCongr, 10 assoc, 11 identL, 12 identR, 13 invL, 14 invR (15) |
| `CommGroup` | Group + 15 comm (16) |
| `Semiring` | 0-4 equiv infra, 5 zero, 6 one, 7 add, 8 mul, 9 addCongr, 10 mulCongr, 11 addAssoc, 12 addComm, 13 addZero, 14 mulAssoc, 15 mulOneL, 16 mulOneR, 17 distribL, 18 distribR (19) |
| `Ring` | Semiring + 19 neg, 20 negCongr, 21 negAdd (22) |
| `CommRing` | Ring + 22 mulComm (23) |

Every congruence field is a genuine field a caller must supply — the tax
ADR-0512 and the architecture review both name. `Magma`/`Semigroup`/
`Monoid`/`CommMonoid` carry one (`opCongr`); `Group`/`CommGroup` carry two
(`opCongr`, `invCongr`); `Semiring`/`Ring`/`CommRing` carry two
(`addCongr`, `mulCongr`) plus `Ring`/`CommRing`'s `negCongr` — five
congruence fields total across the whole spine that `Alg.*`'s `Eq`-flavored
version gets for free from `congr_arg`.

**Field-count cost, measured**: `AlgS.CommRing` has 23 fields against
`Alg.CommRing`'s 16 — 7 more, all equiv-infrastructure (4) or congruence
(3: add/mul/neg — `Magma`..`Group`'s own congruence fields are absorbed into
earlier counts). Proportionally the earlier records pay more: `AlgS.Magma`
is 7 fields against `Alg.Magma`'s 2 (3.5×) because the equiv infrastructure
is fixed overhead independent of how many operations a record has, while
`AlgS.CommRing` is 23 against 16 (1.44×) because by `CommRing` the
operation/law count has grown enough to dilute the fixed cost. This is the
concrete, measured shape of "9 of 22 laws pay the setoid tax" from
ADR-0512, generalized: the tax is per-*record* overhead (4 equiv fields)
plus per-*operation* overhead (1 congruence field each), not per-law.

### 2. `AlgS.<Record>.ofAlg : Alg.<Record> -> AlgS.<Record>`, one per record

No coercion exists in this kernel (ADR-1578's own Alternatives section), so
this is nine `Definition`s, each `<Record>S.mk` applied to:

- `carrier`, and every operation/element field (`op`, `e`, `inv`, `zero`,
  `one`, `add`, `mul`, `neg`) — the SAME selector from the source `Alg.*`
  value, verbatim (an `Alg.*` instance's carrier and operations need no
  change to serve an `AlgS.*` role).
- `equiv := @Eq carrier` (the source record's own `carrier` selector applied,
  partially applied to the `Eq` constant — a value of type `carrier ->
  carrier -> Prop`, since `app2(k, equiv, a, b)` then beta-reduces to `Eq
  carrier a b`).
- `equivRefl`/`equivSymm`/`equivTrans` — built ONCE per projection (not per
  record-specific proof) from the existing `refl_of`/`symm_of`/`trans_of`
  helpers applied to fresh bound variables and closed with `lam_over`,
  mirroring `nat_prelude::structures::build_mul_left_cancel_generic`'s own
  "close a proof built at fresh fvars into a Pi-bound value" pattern.
- every congruence field (`opCongr`/`invCongr`/`addCongr`/`mulCongr`/
  `negCongr`) — synthesized generically from `congr_arg` (one application
  for a unary operation, two nested applications plus one `trans_of` for a
  binary one — the standard `congr2` shape), never hand-proved per record.
- every LAW field — the source record's own selector, **unchanged**. This
  is the load-bearing fact this ADR measured rather than assumed: an
  `AlgS.*` law field's type, e.g. `Ring`'s `negAdd : ∀ a, equiv (add a (neg
  a)) zero`, BETA-REDUCES to `∀ a, Eq carrier (add a (neg a)) zero` once
  `equiv := @Eq carrier` is substituted — the SAME term
  `Alg.Ring`'s own `negAdd` selector already has. So the projection needs
  no proof term for any law field at all, only the four `Eq`-infrastructure
  fields and the per-operation congruence fields — the kernel's own
  definitional unfolding (`add_declaration`'s type-check) confirms the
  selector is accepted at the `AlgS` field's (unfolded) type.

**Why no coercion, restated for this ADR's shape specifically**: an
`Alg.CommRing` and an `AlgS.CommRing` are different inductive types with
different field counts (16 vs 23) — nothing about `ofAlg` is a subtyping
relation, it is a genuine transformation that MANUFACTURES four new proof
terms (the equiv infrastructure) and three-to-five new ones (the
congruences) the source value never carried. Duplicating the *theorems*
(the 22 ADR-0512-style laws) would be the alternative this ADR explicitly
avoids — see Alternatives.

### 3. `AlgS.CommRing.toRingS` — the one forgetful projection this ADR needs

Same "prefix projection" shape ADR-1584 built for `Alg.CommRing.toRing`:
`CommRing`'s first 22 fields ARE `Ring`'s field list verbatim (the spine was
built by literally extending the field-spec list), so `toRingS` is
`RingS.mk` applied to the source's own selectors 0..21, no derivation. This
is what lets `CReal.commRingS` (a `CommRing`, §4) serve as a `Ring` for the
generic theorems in §5, and what lets `AlgS.CommRing.ofAlg(Int.commRing)`
do the same for `Int`.

### 4. `CReal.commRingS : AlgS.CommRing` — every field an existing theorem

Built in `creal/algebra_instance.rs` (not `nat_prelude`/`rat_prelude` — it
needs `CRealPrelude`, which only exists once `creal.rs` has built). Field by
field, checked against `CRealPrelude`'s own documented types
(`creal.rs`'s doc comments, cross-checked against the declarations
themselves):

| `AlgS.CommRing` field | `CReal` source | how |
| --- | --- | --- |
| carrier | `CReal` | selector |
| equiv | `CReal.equiv` | selector |
| equivRefl/Symm/Trans | `CReal.equiv_refl`/`equiv_symm`/`equiv_trans` | selector |
| zero, one, add, mul | `CReal.zero`/`one`/`add`/`mul` | selector |
| addCongr, mulCongr | `CReal.add_congr`, `CReal.mul_congr` | selector, verbatim |
| addAssoc | `CReal.add_assoc` | selector, verbatim |
| addComm | `CReal.add_comm` | selector, verbatim |
| addZero | `CReal.add_zero` | selector, verbatim (right form, matches `unit_right_field`) |
| mulAssoc | `CReal.mul_assoc` | selector, verbatim |
| mulOneR | `CReal.mul_one` | selector, verbatim (right form) |
| mulOneL | **derived**: `equiv_trans(mul_comm(one,a), mul_one(a))` | one `equiv_trans` application, no new `creal` proof |
| distribL | `CReal.left_distrib` | selector, verbatim |
| distribR | **derived**: `equiv_trans(mul_comm(add a b, c), equiv_trans(left_distrib(c,a,b), add_congr(mul_comm(c,a), mul_comm(c,b))))` | three `equiv_trans`/one `add_congr` application |
| neg | `CReal.neg` | selector |
| negCongr | `CReal.neg_congr` | selector, verbatim |
| negAdd | `CReal.add_neg` | selector, verbatim (`∀x, Equiv(add x(neg x)) zero` matches `neg_add_field`'s shape exactly) |
| mulComm | `CReal.mul_comm` | selector, verbatim |

**No field is missing.** Every field ADR-0512's 22 laws plus the two named
congruence obligations (`add_congr`, `mul_congr`) needed was already
present; the two "derived" fields are pure term-composition (an
`equiv_trans` application, not a new proof search) exactly the way
`rat_prelude/algebra_instances.rs`'s `derive_left_unit` derives `Rat`'s
missing `one_mul` from `mul_comm`+`mul_one` for the `Eq`-flavored spine —
this ADR's `derive_left_unit_equiv`/`derive_distrib_right_equiv` are the
same technique, generalized to `equiv_trans` in place of `Eq`'s `trans_of`.

### 5. Three generic theorems over `AlgS.Ring`, proved once

- **`AlgS.mul_zero`**: `∀ (R:Ring)(a:carrier), equiv (mul a zero) zero`.
  Proof avoids the multiplicative identity (matching `Alg.ringMulZero`'s own
  discipline): `x := mul a zero`; `equiv(x, add x x)` from `mulCongr` (at
  `a,a,zero,(add zero zero)`, using `symm(addZero zero)`) composed with
  `distribL(a,zero,zero)`; then the additive-group chain `zero -> add(neg
  x) x -> add(neg x)(add x x) -> add(add(neg x) x) x -> add zero x -> x`
  (five `equiv_trans` steps using `negAdd`, `addComm`, `addAssoc`,
  `addCongr`, `addZero`), symm'd to `equiv(x, zero)`.
- **`AlgS.neg_neg`**: `∀ (R:Ring)(a:carrier), equiv (neg (neg a)) a`. The
  same additive-group chain without the multiplicative step: `neg(neg a) ->
  add zero (neg(neg a)) -> add(add a(neg a))(neg(neg a)) -> add a(add(neg
  a)(neg(neg a))) -> add a zero -> a` (five `equiv_trans` steps using
  `negAdd` applied at both `a` and `neg a`, `addComm`, `addAssoc`,
  `addCongr`, `addZero`).
- **`AlgS.sub`** (`Definition`): `sub R a b := add a (neg b)`, matching
  `Alg.sub`'s shape. **`AlgS.sub_self`**: `∀ (R:Ring)(x), equiv (sub R x x)
  zero` — proved by `negAdd x` alone (the statement unfolds by beta+delta
  to `equiv (add x (neg x)) zero`, exactly `Alg.sub_self`'s own discipline).

Each instantiated at `Int` (`AlgS.Ring.ofAlg(Int.ring)` or
`AlgS.CommRing.toRingS(AlgS.CommRing.ofAlg(Int.commRing))`) and at `CReal`
(`AlgS.CommRing.toRingS(CReal.commRingS)`), concrete AND symbolic per
`kernel-proof-engineering.md`'s rule. The measurement this ADR reports (not
assumed in advance): whether `AlgS.mul_zero` applied at `AlgS.CommRing.
toRingS(CReal.commRingS)` has `CReal.mul_zero`'s exact type by `def_eq` — see
Evidence.

## Alternatives

**Duplicate the 22 laws as `Eq`-restated theorems and give `CReal.Eq` a
fake reflexive-only equality.** Rejected outright — this would silently
misrepresent `Eq CReal` as the equality of real numbers, exactly what
ADR-0512 §3 says this project "never pretend[s]".

**Give the `Alg.*` spine a type-parameter for the equality relation instead
of building a second spine.** Considered and rejected: it would force every
existing `Alg.*` consumer (ADR-1578's three theorems, ADR-1584's six, the one
retirement in ADR-1587) to thread an extra relation argument and a
congruence proof through call sites that currently need neither — the
`Eq`-flavored spine's whole value is that ordinary equality costs nothing.
A second, independent spine (this ADR) costs nothing to `Alg.*`'s existing
15 declarations and adds the tax only where a setoid carrier actually needs
it, matching this project's stated method elsewhere (the "two congruence
regimes" finding: reach for the regime the situation demands, do not force
one shape everywhere).

**Route `CReal`'s congruence through `Eq.rec` transport (`congr_arg`/
`subst`), the way the `Eq`-flavored spine does.** Not possible: `Eq.rec`
transports along a proof of `Eq`, and `CReal.Equiv` is not `Eq` — there is
no `Eq.rec`-shaped principle for an arbitrary defined relation without
`propext`/`funext` recovering it as `Eq` first, which is exactly the axiom
cost ADR-0512 built the setoid to avoid. This is why every congruence
obligation in `AlgS.*` is a genuine field, carried explicitly, not derived.

## Evidence

See `docs/plan/status/464-structures-setoid.md` for the measured field
counts, the `def_eq` result at `CReal.commRingS`, and test/build output —
recorded there rather than duplicated here since this ADR was written
alongside the implementation in the same lane.

## Consequences

**Easier.** A future setoid carrier (a quotient-avoiding construction for
another domain) has both the field-builder pattern and the `ofAlg`
projection technique ready to reuse without re-deriving how to turn an
`Eq`-flavored law into a value-level `equiv` application.

**Harder.** Two independent spines now exist under the same `Alg`/`AlgS`
naming convention; a future reader must check which one a given theorem is
stated over before assuming `Eq` is available. `AlgS.*`'s nine records are
not free — every future `AlgS` consumer pays the congruence-field tax this
ADR measured, and `Field`/`Apart` remain unbuilt.

**Revisit when** a lane wants `AlgS.Field` (needs `Apart`, a genuine new
design question — constructive apartness, not decidable disequality) or
wants to retarget `linarith`/`ring` at the setoid spine for `CReal` the way
ADR-1587 §5 scoped out for `Alg.OrderedRing`.
