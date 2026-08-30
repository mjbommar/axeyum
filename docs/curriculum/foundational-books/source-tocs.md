# Source Tables of Contents (with drawability annotations)

Extracted TOCs of the open/computational texts we can draw curriculum from, each
chapter tagged by how much of it is a **decidable, self-checkable** axeyum
exercise vs. **Lean-horizon** (proof-track) material. Tags:

- **✅ drawable** — maps onto a decidable axeyum family today (BV / LIA / LRA /
  finite-domain); compute-and-check or exhaustive.
- **◐ partial** — a fixed-size / fixed-modulus instance is drawable; the general
  statement is not.
- **✗ horizon** — analytic / asymptotic / ∀-general / numerical-optimization;
  Lean-horizon or out of scope (→ proof track, or P4.3 optimization).

TOCs are factual lists; both books below are freely available (Stein: free PDF;
Shoup: CC BY-NC-ND). See [README](README.md) for the books' roles.

## What these tags do and do not measure (2026-08-30)

**The ✅/◐/✗ tags classify chapters by what the SOLVER can decide at fixed
instances. In graded-family terms (ADR-0603) that is ROW 3 only.** The taxonomy
has no way to record "row 1 landed as a general kernel theorem", so a chapter
can be tagged ◐ *"at fixed `n`"* while the corresponding universal statement is
proved, quantified and axiom-free in the Lean kernel.

That is not hypothetical. Stein ch. 1–2 and Shoup ch. 1–2 are tagged for fixed
instances, and `Nat.exists_prime_gt` (infinitude of primes),
`Nat.exists_prime_factorization`, `Nat.euclid_lemma`,
`Nat.pow_prime_modeq_self` (Fermat, all `a`) and
`Nat.totient_mul_of_coprime` are all landed at 0 axioms.

The tags are **not** re-scored below, because they are correct for what they
measure. Read them alongside the row-1 status in
[`../graded-statement-families-number-theory-and-linear-algebra.md`](../graded-statement-families-number-theory-and-linear-algebra.md),
which states all four rows per family for number theory and linear algebra, and
[ADR-0716](../../research/09-decisions/adr-0716-row-two-of-a-decidable-subject.md),
which explains why row 2 is empty for these subjects and what carries the
dominance argument instead.

One tag that does need qualifying rather than re-scoring: **Boyd–Vandenberghe's
`computable` framing survives contact with the kernel's type theory.** There is
no `List`, `Finset` or product type, but a vector is a finite function plus a
dimension, and `Rat.dotN_cauchy_schwarz` is proved at *arbitrary* `n`. The real
bound is that `funext` is absent, so matrix identities must be stated pointwise
rather than as equality of functions — see
[`../03-destinations/linear-algebra.md`](../03-destinations/linear-algebra.md).

---

## Stein, *Elementary Number Theory: Primes, Congruences, and Secrets*

Free PDF: <https://wstein.org/ent/>. Computational throughout (Stein authored
SageMath). The **highest-yield NT source** for us — Ch. 1–4 are almost entirely
drawable.

| Ch | Title | Sections | Drawable? |
|---|---|---|---|
| 1 | Prime Numbers | Prime Factorization · Sequence of Primes | ◐ (factorization / primality at fixed `n`) |
| 2 | The Ring of Integers Modulo n | Congruences · **CRT** · Quickly Computing Inverses & Huge Powers · Primality Testing · Structure of (Z/pZ)\* | **✅✅ core** (our modular/BV + gcd families) |
| 3 | Public-key Cryptography | Diffie–Hellman · RSA · Attacking RSA | ✅ (modexp / RSA round-trip at fixed keys) |
| 4 | Quadratic Reciprocity | Euler's Criterion · proofs · **Finding Square Roots** | ◐ (Legendre symbol & sqrt mod `p` at fixed `p`) |
| 5 | Continued Fractions | Finite/Infinite CF · Quadratic Irrationals · **Sums of Two Squares** | ◐ (finite CF expansion; sum-of-two-squares = SAT witness) |
| 6 | Elliptic Curves | Group law · ECM factorization · ECC · curves over ℚ | ◐ (point-addition / group-law identities at fixed curve) |

**Current scenario coverage from Ch. 2–4:** CRT witnesses, Fermat at fixed
modulus, quadratic residue/non-residue examples, modular inverses, fixed-key RSA
round trips, and related finite checks are implemented. Add another row only
when it contributes a distinct proof shape, learner boundary, or solver stress.

---

## Shoup, *A Computational Introduction to Number Theory and Algebra*

Free (CC BY-NC-ND): <https://shoup.net/ntb/>. Rigorous + algorithmic; bridges NT
→ algebra → finite fields, so it also feeds the **algebra / finite-field / matrix
/ polynomial** families.

| Ch | Title | Drawable? |
|---|---|---|
| 1 | Basic Properties of the Integers (divisibility, ideals, gcd) | ✅ |
| 2 | Congruences (linear congruences, residue classes, Euler φ, arithmetic functions) | ✅ (φ, σ at fixed `n`; CRT) |
| 3 | Computing with Large Integers (complexity) | ✗ (meta) |
| 4 | Euclid's Algorithm (extended Euclid, modular inverse, CRT) | **✅✅** (already our Bézout/inverse family) |
| 5 | The Distribution of Primes (Chebyshev, Bertrand) | ✗ (analytic) |
| 6–7 | Discrete Probability · Probabilistic Algorithms | ✗ |
| 8 | Abelian Groups (subgroups, cosets, homomorphisms) | ◐ (finite-group axioms → Algebra family) |
| 9 | Rings | ◐ (finite rings → Algebra family) |
| 10 | Probabilistic Primality Testing (Miller–Rabin) | ◐ (primality at fixed `n`) |
| 11 | Generators & Discrete Logs in Z\*ₚ | ◐ (fixed instances) |
| 12 | Quadratic Residues & Quadratic Reciprocity | ◐ (fixed `p`) |
| 13 | Computational Problems re Quadratic Residues | ◐ |
| 14 | Vector Spaces and Algebras | ◐ (over finite fields) |
| 15 | **Matrices over Fields** | ✅ (our LinearAlgebra family, 𝔽ₚ) |
| 16 | Subexponential Algorithms (DL, factoring) | ✗ |
| 17 | More Rings | ◐ |
| 18 | **Polynomial Arithmetic and Applications** | ✅ (our Polynomial family, over fields) |
| 19–20 | Finite Fields · Algorithms for Finite Fields | ◐ (𝔽_q arithmetic at fixed `q`) |
| 21 | Deterministic Primality Testing (AKS) | ◐ (at fixed `n`) |

---

## Boyd & Vandenberghe, *Introduction to Applied Linear Algebra* (VMLS)

Free PDF: <https://web.stanford.edu/~boyd/vmls/>. The **applied/computational** LA
text; Parts I–II are the drawable matrix core, Part III is numerical optimization
(→ axeyum's optimization track, P4.3, not the decidable family).

**Part I — Vectors**
| Ch | Title | Drawable? |
|---|---|---|
| 1 | Vectors (addition, scalar mult, **inner product**) | ✅ (vector identities over ℚ) |
| 2 | Linear functions (Taylor approx, regression) | ◐ (linearity at fixed size) |
| 3 | Norm and distance (norm, distance, std dev, **angle**) | ◐ (fixed exact forms; degree-2 SOS has checked evidence, broader norm theory does not) |
| 4 | Clustering (k-means) | ✗ (numerical) |
| 5 | Linear independence (basis, orthonormal, **Gram–Schmidt**) | ◐ (independence/rank at fixed size = ✅) |

**Part II — Matrices**
| Ch | Title | Drawable? |
|---|---|---|
| 6 | Matrices (transpose, addition, matrix-vector mult) | ✅ (our LA family) |
| 7 | Matrix examples (geometric transforms, incidence, convolution) | ◐ |
| 8 | **Linear equations** (systems `Ax=b`) | ✅ (solvability + witness over ℚ) |
| 9 | Linear dynamical systems | ✗ |
| 10 | Matrix multiplication (**associativity**, QR) | ✅ (assoc identity — we have it) |
| 11 | **Matrix inverses** (left/right, solving, pseudo-inverse) | ✅ (inverse via `Ax=b`, fixed size over ℚ) |

**Part III — Least squares** (ch. 12–19: least squares, data fitting,
classification, multi-objective / constrained / nonlinear LS) — **✗ horizon for
the decidable family**: these are numerical optimization over ℝ. They map to
axeyum's optimization surface (OMT/MILP, P4.3), not the self-checking corpus —
*except* the exact normal-equations identity at fixed size (◐).

---

## Synthesis: what to deepen next, by yield

1. **Number theory:** connect existing CRT/residue/RSA/field examples to distinct
   checked evidence and learner pages instead of duplicating fixed instances.
2. **Polynomials and finite fields:** deepen quotient, factorization, and field
   examples when they add a proof route or reusable solver regression.
3. **Linear algebra:** connect exact rational and finite-field matrix packs to
   residual, rank, factorization, and proof-producing contradiction lessons.
4. **Theorem horizon:** keep analytic number theory, convergence, general
   optimization, and abstract structure theorems explicitly proof-oriented.

The executable queue is [the curriculum backlog](../BACKLOG.md); the broader
resource queue is the [math curriculum build
sequence](../../foundational-resources/MATH-CURRICULUM-RESOURCE-BUILD-SEQUENCE.md).
