# ADR-0040: SOS certificate → Lean reconstruction via ring axioms + a degree-2 normalizer

Status: accepted (plan; implementation is a staged keystone)
Date: 2026-06-21
Relates to: [ADR-0039](adr-0039-degree-2-sos-psd-certificate.md) (the degree-2
SOS/PSD decision), [ADR-0036](adr-0036-lean-kernel-crate.md) (the in-tree Lean
kernel), the reconstruction path (`crates/axeyum-solver/src/reconstruct.rs`), and
the research note
[`sos-certificate-proofs.md`](../07-verification/sos-certificate-proofs.md).

## Context

The degree-2 SOS/PSD route (ADR-0039) decides a strict quadratic inequality
`p < 0` (or `p > 0`) UNSAT, and as of `11da791` carries an exported, self-checking
`Evidence::UnsatSos` certificate: the `LDLᵀ` factorization `M = L·D·Lᵀ` with
`D ≥ 0`, i.e. the explicit sum-of-squares witness `p(x) = Σₖ D[k]·ℓₖ(x)²`. That
certificate is re-checkable *inside* axeyum (`SosCertificate::verify`), but it is
not yet a **Lean-grade** certificate: `reconstruct.rs` has eight fragments that
reconstruct to a kernel-checked `False`, and **none covers NRA**. The QF_LRA
fragment is purely linear and cannot witness the *nonlinear* ring identity
`p = Σ D[k]·ℓₖ²`.

The kernel's arithmetic prelude (`arith_prelude.rs`) axiomatizes a **linear
ordered field**: `add, mul, neg, zero, one, le, lt`; order axioms (`le_refl`,
`le_trans`, `lt_trans`, `lt_irrefl`, `lt_of_lt_of_le`, …); additive axioms
(`add_le_add`, `add_comm`, `add_assoc`, `add_zero`, `add_neg`); the scaling axiom
`mul_le_mul_of_nonneg_left`; and `zero_lt_one`. It has **no** `mul_comm`,
`mul_assoc`, distributivity, `mul_one`/`mul_zero`, or `mul_nonneg` — none of the
multiplicative ring machinery an SOS proof needs.

## Decision

Reconstruct SOS refutations **in the Lean kernel** (option 1 of the research
note), not via an Alethe SOS rule (Alethe's `la_*` rules are linear; Carcara has
no SOS rule). The kernel is the small trusted anchor and **checks every
reconstructed term**, so a buggy reconstruction yields *no* certificate, never an
unsound one — the reconstruction code is untrusted-but-checked.

### Kernel additions (the only trusted-base change; each a sound ordered-field theorem)

Extend `ArithPrelude` with the minimal commutative-ordered-ring axioms, each
type-checked at admission and mathlib-faithful (the existing prelude is already an
axiomatized ordered field; these complete its multiplicative/order fragment):

- `mul_comm   : ∀ a b, mul a b = mul b a`
- `mul_assoc  : ∀ a b c, mul (mul a b) c = mul a (mul b c)`
- `mul_one    : ∀ a, mul a one = a`   (and `one_mul` or derive via `mul_comm`)
- `mul_zero   : ∀ a, mul a zero = zero`
- `left_distrib  : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)`
  (and `right_distrib`, or derive via `mul_comm`)
- `mul_nonneg : ∀ a b, le zero a → le zero b → le zero (mul a b)`

`sq_nonneg : ∀ a, le zero (mul a a)` then follows from `mul_nonneg` by case split,
or is added directly (it is the only square fact the proof needs and is itself a
standard ordered-field theorem). These are the entire trusted-base delta; **no
axiom mentions SOS, polynomials, or the certificate** — they are generic ring/order
facts, so the trusted base does not grow in surface area beyond a commutative
ordered ring.

### Reconstruction (untrusted, kernel-checked)

Add a `ProofFragment::Sos` and `reconstruct_sos_proof` mirroring
`reconstruct_lra_proof`. Driven by the `SosCertificate` `(p, L, D, strict_lt)`:

1. **Build terms** for `p`, the affine forms `ℓₖ = Σⱼ L[j][k]·yⱼ` (`y = [x;1]`),
   and the rational constants `D[k]`.
2. **Ring identity `p = Σ D[k]·ℓₖ²`.** A bounded *degree-2 ring normalizer*:
   expand each `ℓₖ²` and each `D[k]·ℓₖ²` to a canonical monomial sum via
   `left_distrib`/`mul_comm`/`mul_assoc`, sum them, and produce a kernel `Eq` proof
   that the normal form equals `p`'s normal form (both sides normalize identically
   because the certificate's reconstruction already holds over ℚ — the normalizer
   only has to *witness* an equality axeyum already verified numerically). This is
   the one new engine; it is degree-2-bounded, so it terminates and stays small.
3. **Nonnegativity `0 ≤ Σ D[k]·ℓₖ²`.** Each `D[k] ≥ 0` is a literal rational sign
   (a `le zero D[k]` proof from the constant axioms); each `ℓₖ² ≥ 0` is `sq_nonneg`;
   each product `0 ≤ D[k]·ℓₖ²` is `mul_nonneg`; the sum is folded by `add_le_add`
   from `0`.
4. **Contradiction.** Rewrite `0 ≤ Σ D[k]·ℓₖ²` along the identity to `0 ≤ p`;
   combine with the asserted `p < 0` via `lt_of_le_of_lt`/`lt_irrefl` to infer
   `False`. `Evidence::UnsatSos` additionally emits the Lean module.

## Consequences

- The SOS unsat route gains a Lean-grade certificate, advancing the Lean-parity
  front from "self-checking exported artifact" to "kernel-checked proof" for the
  degree-2 quadratic-form fragment. `TrustId::Sos` stays `certified`; the new claim
  is the *external* Lean check.
- The trusted base grows by a fixed set of standard commutative-ordered-ring
  axioms (no SOS-specific axiom). Each is type-checked at admission and unit-tested
  by building small proof terms on it, exactly as the existing ordered-field axioms
  are.
- The degree-2 ring normalizer is the new reconstruction engine; higher-degree
  SOS, the Positivstellensatz, and full nonlinear `ring`-style normalization remain
  out of scope here (consistent with ADR-0039's degree-2 boundary).

### Staged implementation (each a bounded, kernel-checked, separately-committable step)

1. Add the ring/order axioms to `ArithPrelude` + admission/proof-term unit tests
   (no reconstruction yet) — the only trusted-base change, landed and reviewed in
   isolation.
2. The degree-2 ring normalizer (`p`-side and `Σ D[k]·ℓₖ²`-side to a shared normal
   form) with `Eq`-proof output, unit-tested on the AM–GM forms.
3. `ProofFragment::Sos` + `reconstruct_sos_proof` + the contradiction assembly;
   wire `Evidence::UnsatSos` to emit the Lean module; end-to-end test that a 2-/3-
   var AM–GM refutation produces a kernel-`infer`-checked `False`.
