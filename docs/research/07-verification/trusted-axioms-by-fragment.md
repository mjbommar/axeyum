# Trusted axioms by fragment (Lean reconstruction)

Status: governance ledger — keep in sync with `axeyum-lean-kernel`'s preludes
Last updated: 2026-06-21
Relates to: ADR-0031 (the *reduction* trust ledger, `trust-ledger.md`), ADR-0036
(the kernel), ADR-0040/0042 (the ℝ / ℤ preludes), and `reconstruct.rs` /
`int_reconstruct.rs`.

There are **two distinct trust surfaces** in this stack, and they must not be
conflated:

1. **The reduction trust ledger** (`docs/research/08-planning/trust-ledger.md`,
   generated from `TrustId`): which *solver reductions* (bit-blast, Ackermann,
   array-elim, Farkas, SOS, Diophantine, …) a result relied on, and whether that
   run carried an independent certificate. That is the **decision-side** trust.
2. **This file**: which *Lean-kernel axioms* a reconstructed proof depends on. When
   a fragment reconstructs to a kernel-checked `False`, the proof is checked against
   the kernel's axioms; this table makes that **proof-side** trusted base explicit
   and auditable, so proof complexity does not outrun the ledger.

The kernel itself is small and Lean-faithful (ADR-0036): `whnf`/`def_eq`/`infer`
and the inductive machinery are ported from nanoda. A reconstructed term is
*checked*, never trusted — a wrong reconstruction fails `infer`/`def_eq False` and
yields **no** certificate. So the only trusted base a proof can rest on is (a) the
kernel checker and (b) the declared axioms below.

## The kernel trusted base

### Logic foundation — NOT added trust (Lean's own definitions)

`build_logic_prelude` declares `True`, `False`, `And`, `Or`, `Iff`, `Eq` as
**inductive types** through the same `add_inductive` gate Lean uses, and `Not p :=
p → False` as a **definition**. These are *exactly* Lean's standard logical
connectives; declaring them adds no axiomatic commitment beyond what the inductive
gate type-checks. (`Eq.rec`, `And.intro`, `Or.rec`, `False.rec` are the generated
recursors/constructors, also checked.)

- **`Classical.em : ∀ (p : Prop), Or p (Not p)`** — the *one* genuine logical
  axiom (declared on demand in `reconstruct.rs`). It is the law of excluded middle,
  identical to Lean/mathlib's `Classical.em`; a standard classical commitment.
  Used by the Boolean/clausal/QF_BV reconstructions (Tseitin gate tautologies,
  bit-level case splits). The arithmetic fragments below do **not** require it.

### ℝ ordered-field axioms — `build_arith_prelude` (ADR-0040)

Signature (uninterpreted symbols — language, no propositional content): carrier
`R`, `add, mul, neg, zero, one`, `le, lt`.
Axioms (each a **theorem of ℝ**, mirroring mathlib's `LinearOrderedField`/its
ordered-ring core): `le_refl, le_trans, lt_irrefl, lt_trans, lt_of_lt_of_le,
lt_of_le_of_lt, le_of_lt, add_le_add, add_comm, add_assoc, add_zero, add_neg,
add_lt_add_of_le_of_lt, mul_le_mul_of_nonneg_left, zero_lt_one, mul_comm,
mul_assoc, mul_one, mul_zero, left_distrib, mul_nonneg, sq_nonneg`.

### ℤ discretely-ordered-ring axioms — `build_int_prelude` (ADR-0042)

Signature: carrier `Z`, `add, mul, neg, zero, one`, `le, lt`.
Axioms (each a **theorem of ℤ**, mirroring mathlib's `LinearOrderedCommRing` core
plus discreteness): the same order + commutative-ring axioms as ℝ (minus
`sq_nonneg`), **plus** `le_total` (ℤ is a linear order), `lt_of_le_of_ne`, and the
integer-specific **`no_int_between : ∀ (x : Z), Not (And (lt zero x) (lt x one))`**
— no integer strictly between 0 and 1.

## By-fragment table

| Fragment (Lean reconstruction) | Logic inductives | `Classical.em` | ℝ prelude | ℤ prelude | Notes |
|---|:---:|:---:|:---:|:---:|---|
| QF_BV (bitwise + arithmetic bitblast) | ✓ | ✓ | — | — | Closed over `assume + em`; bit-iffs kernel-checked. |
| QF_UF (EUF congruence) | ✓ | ✓ | — | — | `eq_congruent`/resolution to `False`. |
| QF_UFBV, QF_ABV, datatypes | ✓ | ✓ | — | — | Via the BV/array/datatype reductions. |
| ∀ / ∃ (quantifier unsat / skolem) | ✓ | ✓ | — | — | |
| QF_LRA (general Farkas `la_generic`) | ✓ | — | ✓ | — | Ring cancellation via kernel `Eq` rewrites. |
| **NRA degree-2 SOS** (ADR-0040) | ✓ | — | ✓ | — | `mul_nonneg`/`sq_nonneg` + the degree-2 ring normalizer; both strict directions, rational weights, 3-var AM-GM. |
| **QF_LIA Diophantine** (equality systems, ADR-0042) | ✓ | — | — | ✓ | `no_int_between` + `le_total` + `lt_of_le_of_ne`; discreteness close. |
| **QF_LIA integer-interval** (`c≤k·x≤d`, ADR-0042) | ✓ | — | — | ✓ | Same ℤ axioms, no new ones (reuses the Diophantine machinery). |

## Soundness argument

Every axiom above is a **theorem of its standard model** (ℝ for the `R` prelude,
ℤ for the `Z` prelude, classical logic for `em`). Therefore each axiom *set* has
that model, so it is **consistent** — `False` cannot be derived from the axioms
alone; a reconstructed `False` genuinely encodes "the query's assertions are
contradictory." Each axiom's *type* is type-checked at admission through the
trusted `add_declaration`/`add_inductive` gate (a green `build_*_prelude` is the
well-formedness proof), and the prelude tests build proof terms on the axioms and
`infer`-check them.

External validation: the `lean_crosscheck` tests render each fragment's module and
run the **real `lean` binary**; `#print axioms axeyum_refutation` confirms each
module depends only on the prelude axioms + the query-hypothesis assumptions (the
asserted atoms, introduced via `hyp_axiom` — these are *premises*, not trusted
axioms) and **no `sorryAx`**.

## Keeping this honest (the rule)

- A **new kernel axiom** may be added ONLY if it is a genuine theorem of its model;
  it must be type-checked at admission, unit-tested by a proof term, and **added to
  the table above** in the same change.
- After any `reconstruct.rs` / prelude change, run the 7 `lean_crosscheck`
  real-`lean` tests; an unexpected axiom dependency (or `sorryAx`) is a regression.
- Do not let "fragment X reconstructs to Lean" imply "fragment X is fully proven":
  reconstruction covers the *shapes the table's fragments decide*, not the whole
  fragment (e.g. NRA is degree-2 SOS, not general NRA; QF_LIA is GCD/Diophantine +
  single-variable interval cuts, not general integer-cut). The support matrix
  (`support-matrix.md`) must split these sub-fragments, not claim a broad row.
