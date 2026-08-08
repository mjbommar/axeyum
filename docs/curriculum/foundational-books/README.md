# Foundational Books through the Decidability Lens

How canonical mathematics texts project onto what axeyum can actually *check*.
Each book is mostly **proof** — quantified statements an SMT solver cannot
decide — so the honest question is: *which fragment of this book is decidable or
computable, and therefore a self-checkable exercise / benchmark for axeyum?*
The rest is the **Lean-horizon**: proof-oriented material, not a solver
benchmark. See [../DEPTH.md](../DEPTH.md) for the scope ceiling.

## The pattern

For every text the split is the same three buckets:

- **LRA** — linear (in)equalities over ordered fields: order axioms, linear
  consequences. Decided with Farkas certificates (`check_with_lra` / `prove`).
- **NRA / RCF** — fixed-degree polynomial (in)equalities. Axeyum now combines a
  complete CAD decision side with a sound-incomplete fallback and a checked
  degree-2 SOS/PSD route. The SOS route carries an independently rechecked exact
  certificate and selected kernel reconstruction; general CAD UNSAT results do
  not yet carry that proof artifact. See the live [support
  matrix](../../research/08-planning/support-matrix.md) for the exact boundary.
- **Induction / ε-δ / ∀-general** — statements quantified over ℕ or over all
  reals/functions. **Lean-horizon**: not decidable, only a fixed instance is.

## The Lean-horizon end

[**proof-assistants.md**](proof-assistants.md) — the reference curriculum for the
`lean-horizon` material (ε-δ analysis, induction, program-correctness proofs):
**Software Foundations** (Pierce et al.), *now being translated from Rocq to
Lean* (2026), and **Verso** (Lean's doc-authoring tool). Where the
non-SMT-decidable nodes connect to proof-oriented curriculum and the bounded
kernel/reconstruction surface.

## Extracted source TOCs

[**source-tocs.md**](source-tocs.md) holds the full tables of contents of the
open/computational texts we can draw from — **Stein** (*Elementary Number
Theory*), **Shoup** (*Computational Introduction to Number Theory and Algebra*),
and **Boyd–Vandenberghe** (*Introduction to Applied Linear Algebra*) — each
chapter tagged ✅ drawable / ◐ partial / ✗ horizon, with a current depth-first
synthesis.

## Books

| Book | Decidable fragment we touch | Lean-horizon (the bulk) |
|---|---|---|
| **[Spivak, *Calculus*](spivak.md)** | Ch.1 order axioms and transitivity (LRA/Farkas), nonlinear monotonicity, and checked degree-2 SOS examples such as two- and three-variable AM–GM | limits/continuity/derivatives/integrals (epsilon-delta), general induction families, and polynomial claims outside a checked reconstruction route |
| **Rosulek, [*The Joy of Cryptography*](https://joyofcryptography.com/)** | finite games, BV xor algebra, modular arithmetic, finite-field tables, small transcript verification, finite probability tables; see the [provable-security integration note](../../plan/provable-security-integration.md) | asymptotic negligible bounds, reductions under computational assumptions, zero-knowledge simulation/extraction, random-oracle reasoning, and real post-quantum hardness claims |
| Rudin, *Principles of Mathematical Analysis* | the same algebraic/order core | metric-space topology, convergence, measure — all ε-δ |
| Apostol, *Calculus* | linear/area axioms; polynomial identities | the integral as a limit; series |
| Landau, *Foundations of Analysis* | Peano/field defining equations (instances) | the inductive constructions ℕ→ℤ→ℚ→ℝ themselves |
| Hardy & Wright, *Theory of Numbers* | gcd/Bézout, congruences, fixed-modulus facts (BV/LIA) | ∀-theorems: infinitude of primes, reciprocity |

## Why this is double-duty

The decidable fragment of these books is **precisely** axeyum's arithmetic
theories — LRA, NRA, LIA, BV. So porting the decidable exercises both (a) teaches
the foundational material with a machine-checked answer key and (b) builds the
structured arithmetic corpus Axeyum needs. The historical
[example-suites note](../../research/08-planning/foundational-example-suites.md)
explains why that double duty was adopted; current breadth and assurance belong
in the generated matrices. The Spivak page is the first worked example
(`crates/axeyum-solver/tests/spivak_inequalities.rs`).
