# ADR-0042: Integer prelude (discretely-ordered commutative ring) for integer-arithmetic Lean reconstruction

Status: accepted (axioms; reconstruction is a follow-up)
Date: 2026-06-21
Relates to: [ADR-0036](adr-0036-lean-kernel-crate.md) (the in-tree Lean kernel),
the LRA arith prelude (`crates/axeyum-lean-kernel/src/arith_prelude.rs`,
ADR-0015-era), P2.4 (the `DiophantineCertificate` for integer-systems
infeasibility), and the reconstruction module
(`crates/axeyum-solver/src/reconstruct.rs`).

## Context

P3.7 reconstructs nine fragments to a kernel-checked `False`, but a listed
hard-frontier gap is **integer-cut / Diophantine QF_LIA**: an integer system that
is *rational*-feasible yet *integer*-infeasible (e.g. `x+y=0 ∧ x−y=1 ⇒ 2x=1`). The
in-tree `DiophantineCertificate` (P2.4) already refutes these with an independent
re-check, but it has no Lean reconstruction — and it **cannot** reuse the real
ordered-field `R` prelude: `2x=1` is real-feasible (`x=½`), contradictory only
because `x ∈ ℤ`. The kernel today has only the logic prelude and the field `R`
prelude; there is no integer apparatus.

## Decision

Add `build_int_prelude` declaring the integers as a **discretely-ordered
commutative ring** — the minimal sound foundation for integer-infeasibility proofs.
Carrier `Z : Type` with `add, mul, neg, zero, one`, relations `le, lt`, and these
axioms (each a theorem of ℤ, type-checked at admission through the trusted
`add_declaration` gate, exactly as the `R` prelude's are):

Order: `le_refl`, `le_trans`, `lt_irrefl`, `lt_trans`, `lt_of_lt_of_le`,
`lt_of_le_of_lt`, `le_of_lt`.
Additive group: `add_comm`, `add_assoc`, `add_zero`, `add_neg`, `add_le_add`,
`add_lt_add_of_le_of_lt`.
Multiplicative commutative monoid + distributivity: `mul_comm`, `mul_assoc`,
`mul_one`, `mul_zero`, `left_distrib`, `mul_le_mul_of_nonneg_left`.
Constants/order link: `zero_lt_one`.
**The integer-specific axiom — discreteness:**

- `no_int_between : ∀ (x : Z), Not (And (lt zero x) (lt x one))`
  — there is no integer strictly between `0` and `1`.

This single axiom is what the field `R` lacks and is the crux of every
integer-infeasibility proof. Combined with the ordered-ring structure it gives the
"step" lemma `0 < x ⇒ 1 ≤ x` (derivable, no extra axiom) used to refute
`g·m = r, 0 < r < g`.

Soundness: every axiom holds in ℤ, so the axiom set has ℤ as a model and is
consistent; `no_int_between` is the standard discreteness fact `¬∃n:ℤ, 0<n<1`. The
prelude is admitted through the same trusted, type-checking gate as the `R`
prelude (a green build is the well-formedness proof), and tests build integer
proof terms on it and `infer`-check them.

## Consequences

- Unblocks integer-arithmetic Lean reconstruction. The follow-up
  `reconstruct_diophantine_proof` will: encode the original equalities as
  hypotheses over `Z`-typed variables, prove the certificate's integer linear
  combination reduces (via the ring axioms + the existing `normalize_deg2`-style
  machinery) to `g·m = r` with `0 < r < g` and `m : Z` an integer combination, and
  close with `no_int_between` (after the derived `0<x ⇒ 1≤x` step) to `False`. This
  reuses the ring/cast/fold machinery built for SOS/LRA; only the carrier and the
  discreteness axiom are new.
- Trusted-base growth is one new carrier + a standard discretely-ordered-ring axiom
  set (mirroring `R`), with `no_int_between` the only genuinely new *kind* of
  axiom. No divisibility/`Dvd` predicate is needed — discreteness subsumes the
  `gcd ∤ c` argument via the `g·m=r, 0<r<g ⇒ 0<m<1` reduction.
- Higher integer reasoning (full divisibility, modular arithmetic, Gomory-cut
  proofs) remains future work; this prelude is scoped to the
  linear-combination-to-discreteness pattern the `DiophantineCertificate` produces.
