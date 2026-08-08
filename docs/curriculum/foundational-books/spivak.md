# Spivak, *Calculus* — Chapter 1 through the Decidability Lens

Spivak's Chapter 1, "Basic Properties of Numbers," founds the whole book on the
**ordered-field axioms P1–P12** and a few **foundational inequalities**. This is
the part of Spivak axeyum can actually *check* — the order axioms are linear
(LRA) and the inequalities are fixed-degree polynomial (NRA / real-closed
fields). Chapters 2+ (limits, continuity, derivatives, integrals, series) are
ε-δ and **Lean-horizon**. Worked as
`crates/axeyum-solver/tests/spivak_inequalities.rs`.

## The ordered-field axioms (P1–P12)

| Axiom | Statement | Class |
|---|---|---|
| P1 | `a + (b + c) = (a + b) + c` | LRA (equational) |
| P2 | `a + 0 = a` | LRA |
| P3 | `a + (−a) = 0` | LRA |
| P4 | `a + b = b + a` | LRA |
| P5 | `a · (b · c) = (a · b) · c` | NRA (products) |
| P6 | `a · 1 = a` (`1 ≠ 0`) | LRA |
| P7 | `a ≠ 0 ⇒ a · a⁻¹ = 1` | NRA |
| P8 | `a · b = b · a` | NRA |
| P9 | `a · (b + c) = a·b + a·c` (distributivity) | NRA |
| P10 | trichotomy: exactly one of `a∈P`, `a=0`, `−a∈P` | LRA |
| P11 | `a,b ∈ P ⇒ a + b ∈ P` | LRA |
| P12 | `a,b ∈ P ⇒ a · b ∈ P` | NRA |

The order axioms (P10–P12) and their linear consequences — e.g. transitivity
`a < b ∧ b < c ⇒ a < c` — are proved with a **re-checked Farkas certificate** via
the `prove` front door.

## The Chapter-1 inequalities

Measured against `crates/axeyum-solver/tests/spivak_inequalities.rs` and the
focused SOS evidence/reconstruction suites:

| Inequality | Statement | Class | axeyum verdict (measured) |
|---|---|---|---|
| Order transitivity | `a<b ∧ b<c ⇒ a<c` | LRA | **Proved** (Farkas, re-checked) ✓ active test |
| Monotonicity (threshold-1) | `x≥1 ∧ y≥1 ⇒ x·y≥1` | NRA | **Proved** by NRA ✓ active test |
| Triangle inequality | `\|a+b\| ≤ \|a\|+\|b\|` | LRA + abs case split | not pinned by the focused Spivak regression; do not infer a proof claim from other LRA coverage |
| Square nonnegativity | `a² + b² ≥ 2ab` (`(a−b)²≥0`) | NRA (degree 2) | **Proved**; active NRA regression, checked SOS/PSD evidence, and kernel-reconstructed supported form |
| AM–GM, n=2 (sqrt-free) | `(a+b)² ≥ 4ab` | NRA (degree 2) | covered by the degree-2 SOS/PSD route; focused evidence and reconstruction tests include the two-variable sum form |
| Bernoulli, fixed n=2 | `(1+x)² ≥ 1+2x` (`x²≥0`) | NRA (degree 2) | algebraically in the SOS class, but not a named Spivak regression cell; keep the claim at route level |
| Cauchy–Schwarz, n=2 | `(a₁b₁+a₂b₂)² ≤ (a₁²+a₂²)(b₁²+b₂²)` | NRA (degree 4) | outside the degree-2 SOS certificate; no Spivak-specific checked-proof claim |
| Bernoulli, ∀n | `(1+x)ⁿ ≥ 1+nx` | induction | **Lean-horizon** |
| AM–GM, general n | `(Σaᵢ)/n ≥ (Πaᵢ)^{1/n}` | induction + roots | **Lean-horizon** |

## Findings, and what was fixed (measured, not assumed)

1. **LRA→NRA dispatch — FIXED (#14).** The `prove`/`produce_evidence` front door
   used to reject a nonlinear real goal as `Unsupported`; it now falls back to
   the NRA engine (`produce_nra_evidence`) when the linear route hits a nonlinear
   product. Pinned by `prove_dispatches_nonlinear_real_to_nra`; the soundness
   probe `nra_must_not_claim_x_squared_negative_is_sat` confirms NRA doesn't
   return a spurious model on the way.
2. **NRA wall-clock timeout — FIXED (#15).** NRA's spatial branch-and-bound had
   no deadline (only a magnitude bound), so it could run far past the configured
   budget (the `a²+b²≥2ab` / AM–GM cases hung 60s+). A `deadline` is now threaded
   through `branch_and_bound` and the per-box refinement loop, so the engine bails
   to `Unknown` promptly. The frontier test `square_nonnegativity_is_the_nra_frontier`
   is now active (returns `Unknown` in ~5s instead of hanging).
3. **The degree-2 SOS frontier moved.** Axeyum now extracts a quadratic form,
   checks an exact rational LDL-transpose/PSD certificate, and reconstructs
   selected two- and three-variable AM–GM forms through the Lean-core checker.
   The remaining frontier is broader: higher-degree Positivstellensatz-style
   evidence, general CAD proof production, and source-bound reconstruction for
   polynomial shapes outside the admitted SOS slice.

## Why this matters for axeyum

Spivak Chapter 1 is, quite literally, a curriculum of ordered-field and
fixed-degree-polynomial reasoning — i.e. a hand-curated **LRA + NRA benchmark**
of foundational, human-meaningful theorems. It exercises exactly the arithmetic
the proof track cares about, and it cleanly separates checked LRA/SOS evidence,
decision-only or incomplete NRA routes, and the Lean horizon.
