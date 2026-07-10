# Foundational Books through the Decidability Lens

How canonical mathematics texts project onto what axeyum can actually *check*.
Each book is mostly **proof** — quantified statements an SMT solver cannot
decide — so the honest question is: *which fragment of this book is decidable or
computable, and therefore a self-checkable exercise / benchmark for axeyum?*
The rest is the **Lean-horizon** (proof-reconstruction, P3.6/P3.7), not a
benchmark. See [../DEPTH.md](../DEPTH.md) for the scope ceiling.

## The pattern

For every text the split is the same three buckets:

- **LRA** — linear (in)equalities over ordered fields: order axioms, linear
  consequences. Decided with Farkas certificates (`check_with_lra` / `prove`).
- **NRA / RCF** — fixed-degree polynomial (in)equalities: Tarski-decidable in
  principle. axeyum's NRA (ADR-0024) is sound but incomplete (linearization +
  monotonicity lemmas, not CAD): it proves *monotonicity-shaped* facts (e.g.
  `x≥1 ∧ y≥1 ⇒ xy≥1`) but **not** the *sum-of-squares* inequalities — even
  degree-2 `a²+b² ≥ 2ab` is currently the **NRA frontier** (it abstracts the
  squares to independent variables, losing the SOS correlation). SOS facts need a
  positivstellensatz/CAD path (P2.5). Measured, not assumed — see the Spivak page.
- **Induction / ε-δ / ∀-general** — statements quantified over ℕ or over all
  reals/functions. **Lean-horizon**: not decidable, only a fixed instance is.

## The Lean-horizon end

[**proof-assistants.md**](proof-assistants.md) — the reference curriculum for the
`lean-horizon` material (ε-δ analysis, induction, program-correctness proofs):
**Software Foundations** (Pierce et al.), *now being translated from Rocq to
Lean* (2026), and **Verso** (Lean's doc-authoring tool). Where the
non-SMT-decidable nodes go when the proof track (P3.6/P3.7) is ready.

## Extracted source TOCs

[**source-tocs.md**](source-tocs.md) holds the full tables of contents of the
open/computational texts we can draw from — **Stein** (*Elementary Number
Theory*), **Shoup** (*Computational Introduction to Number Theory and Algebra*),
and **Boyd–Vandenberghe** (*Introduction to Applied Linear Algebra*) — each
chapter tagged ✅ drawable / ◐ partial / ✗ horizon, with a "what to port next, by
yield" synthesis.

## Books

| Book | Decidable fragment we touch | Lean-horizon (the bulk) |
|---|---|---|
| **[Spivak, *Calculus*](spivak.md)** | Ch.1 order axioms + transitivity (LRA, Farkas); a monotonicity inequality (NRA). The SOS inequalities (`a²+b²≥2ab`, AM–GM₂, Cauchy–Schwarz) are the **NRA frontier** | limits/continuity/derivatives/integrals (ε-δ); Bernoulli ∀n, AM–GM ∀n (induction); + the SOS frontier until SOS/CAD lands |
| **Rosulek, [*The Joy of Cryptography*](https://joyofcryptography.com/)** | finite games, BV xor algebra, modular arithmetic, finite-field tables, small transcript verification, finite probability tables; see the [provable-security integration note](../../plan/provable-security-integration.md) | asymptotic negligible bounds, reductions under computational assumptions, zero-knowledge simulation/extraction, random-oracle reasoning, and real post-quantum hardness claims |
| Rudin, *Principles of Mathematical Analysis* | the same algebraic/order core | metric-space topology, convergence, measure — all ε-δ |
| Apostol, *Calculus* | linear/area axioms; polynomial identities | the integral as a limit; series |
| Landau, *Foundations of Analysis* | Peano/field defining equations (instances) | the inductive constructions ℕ→ℤ→ℚ→ℝ themselves |
| Hardy & Wright, *Theory of Numbers* | gcd/Bézout, congruences, fixed-modulus facts (BV/LIA) | ∀-theorems: infinitude of primes, reciprocity |

## Why this is double-duty

The decidable fragment of these books is **precisely** axeyum's arithmetic
theories — LRA, NRA, LIA, BV. So porting the decidable exercises both (a) teaches
the foundational material with a machine-checked answer key and (b) builds the
structured arithmetic corpus axeyum needs — most pointedly the NRA corpus that
[P2.5](../../research/08-planning/foundational-example-suites.md) records as
missing. The Spivak page is the first worked example
(`crates/axeyum-solver/tests/spivak_inequalities.rs`).
