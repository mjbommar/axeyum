# SOS (sum-of-squares) certificate proofs for NRA

Status: research note (scopes the next proof-track slice)
Date: 2026-06-20
Relates to: [ADR-0039](../09-decisions/adr-0039-degree-2-sos-psd-certificate.md)
(the degree-2 SOS/PSD decision), the Lean reconstruction path
(`crates/axeyum-solver/src/reconstruct.rs`), and the Alethe emitter
(`crates/axeyum-solver/src/alethe_lra.rs`).

## Where we are

The degree-2 SOS/PSD certificate (ADR-0039) decides a strict quadratic inequality
`p < 0` UNSAT when the Gram matrix `M` (with `p(x) = [x;1]ᵀ M [x;1]`) is positive
semidefinite. As of `2d53d8e` that decision carries a **self-checked `LDLᵀ`
certificate**: `try_ldlt` records `L` (unit lower-triangular) and `D ≥ 0` with
`M = L·D·Lᵀ`, and `ldlt_reconstructs` independently confirms the factorization.
The factorization *is* an explicit sum-of-squares witness:

```
p(x) = [x;1]ᵀ M [x;1] = [x;1]ᵀ L D Lᵀ [x;1] = Σₖ D[k] · ℓₖ(x)²
```

where `ℓₖ(x) = (Lᵀ[x;1])ₖ` is an affine form and `D[k] ≥ 0`. So the refutation of
`p < 0` is the one-line argument: `p = Σ D[k]·ℓₖ² ≥ 0`, contradicting `p < 0`.

This is sound and self-checked **inside** axeyum. What is missing for **Lean
parity** ("every unsat carries a machine-checkable certificate accepted by a
Lean-grade kernel") is an *external* checkable proof of that argument.

## The gap

`reconstruct.rs` reconstructs eight fragments to a kernel-checked `False`
(QF_BV, QF_UF, QF_UFBV, QF_ABV, datatypes, ∀, ∃, QF_LRA). The QF_LRA fragment
(`reconstruct_lra_proof`) builds the **linear** Farkas combination and checks it
infers to `False`. There is **no NRA fragment**, and the LRA machinery is purely
linear: it cannot witness `p = Σ D[k]·ℓₖ²`, which is a **nonlinear** (degree-2)
ring identity requiring square expansion.

Likewise the Alethe emitter handles linear Farkas `:args`; Alethe's
`la_generic` / `la_*` rules are linear-arithmetic, so the SOS ring identity is not
directly expressible there either.

Key safety property that makes this tractable to build incrementally: **the kernel
checks every reconstructed term.** A buggy reconstruction infers to something that
is *not* def-eq to `False`, so it is rejected and yields **no certificate** — never
an unsound one. Reconstruction is untrusted-but-checked; the kernel is the small
trusted anchor. So the work can proceed without risking a wrong proof.

## Options (to be chosen by ADR before implementation)

1. **Lean-kernel ring reconstruction (preferred end state).** Add an `Nra`/`Sos`
   `ProofFragment`. Reconstruct the real terms for `p`, the affine forms `ℓₖ`, and
   the constants `D[k]`; prove the ring identity `p = Σ D[k]·ℓₖ²` by the kernel's
   definitional/`ring`-style normalization (this is the piece the kernel does not
   yet have for nonlinear terms — it needs commutative-ring normalization over the
   reals, or a checked expansion of each `ℓₖ²`); prove `ℓₖ² ≥ 0` (square
   nonnegativity) and `D[k] ≥ 0` (a literal rational sign), combine to
   `Σ D[k]·ℓₖ² ≥ 0`, and discharge `p < 0` to `False`. **Prerequisite primitive:**
   real square-nonnegativity (`∀ r, 0 ≤ r²`) and a ring-normalizer or per-monomial
   checked expansion. This is the genuinely new capability.

2. **Alethe + a dedicated SOS rule.** Emit the witness `(L, D)` and let a checker
   verify `p = Σ D[k]·ℓₖ²` by polynomial expansion plus the nonneg facts. Carcara
   does not have a built-in SOS rule; this would require either an extension or
   encoding through existing rules, and is likely harder than (1) given the linear
   bias of `la_*`.

3. **Self-contained checkable artifact (bridge).** Emit the `(p, L, D, variable
   order)` certificate as a standalone JSON/term artifact plus an *independent*
   re-checker (expand `Σ D[k]·ℓₖ²`, confirm equality to `p` and `D ≥ 0`) — exactly
   what `ldlt_reconstructs` already does internally, but exported and re-runnable.
   This raises assurance and is cheap, but it is an axeyum-checked artifact, not a
   Lean-grade certificate; it is a stepping stone, not parity.

## Recommended increment

Land **(3) the exported, independently re-checkable SOS artifact** first (small,
no kernel changes, immediately raises the trust ledger for the SOS route from
"ledgered trust note" to "self-checking exported certificate"), then pursue **(1)**
by first building the two kernel primitives — real square-nonnegativity and a
checked degree-2 ring expansion — as their own tested slice, and only then wiring
the `Sos` reconstruction fragment. Each is a bounded, kernel-checked (hence
soundness-safe) step. Open an ADR to choose between (1) and (2) before writing the
fragment.
