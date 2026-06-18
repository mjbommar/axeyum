# Formal Mathematics Tour (Curriculum DAG)

Status: draft
Last updated: 2026-06-17

## Engine findings from the Spivak Ch.1 benchmark (2026-06-17)

Building the [Spivak Chapter 1 benchmark](../../curriculum/foundational-books/spivak.md)
(`crates/axeyum-solver/tests/spivak_inequalities.rs`) surfaced two concrete,
actionable engine gaps — measured, not assumed:

1. **`prove` has no LRA→NRA dispatch.** A real-valued goal containing a nonlinear
   product is rejected by the QF_LRA front door (`Unsupported`) instead of being
   routed to NRA. Candidate fix: dispatch nonlinear real goals to `check_with_nra`
   inside `produce_evidence`.
2. **NRA cannot prove sum-of-squares inequalities — even `a²+b² ≥ 2ab` — and the
   search does not promptly terminate.** The linearization NRA (ADR-0024)
   abstracts `a²,b²,ab` to independent variables, discarding the SOS correlation.
   This is the sharp, foundational motivation for an **SOS / positivstellensatz
   (or CAD/nlsat)** path in P2.5, and for tightening the NRA refinement loop's
   timeout honoring. axeyum *does* prove monotonicity-shaped facts
   (`x≥1 ∧ y≥1 ⇒ xy≥1`).

## Purpose

Answer a specific question: if you start from **calculus, number theory, and
linear algebra** and work *backward* to foundational sequencing, what is the
prerequisite DAG — and which of it can axeyum actually **formalize and test**?
This is the *mathematical-content* companion to the *solver-capability* concept
DAG already built in `axeyum-scenarios::concept`
([ADR-0033](../09-decisions/adr-0033-double-duty-educational-artifacts.md)), and
it is governed by the same decidability lens as the
[example-suites note](foundational-example-suites.md): a node is a *testable*
axeyum artifact only where its content has a decidable or computable fragment.

It informs a new curriculum module (`axeyum-scenarios::mathtour`) and a sequence
of self-checking math exercise families, the first of which (number theory) is
built alongside this note.

**The deep version of this curriculum is a structured knowledge graph at
[`docs/curriculum/`](../../curriculum/README.md)**: an authoritative
machine-readable graph (`curriculum.toml`) plus one markdown file per node
(across foundations → number systems → structures → destinations), each with its
axeyum-testable fragment. The `axeyum-scenarios::mathtour` Rust table mirrors
that graph and tests its invariants. This note is the rationale; the curriculum
tree is the content.

## The backward-derived DAG

Working backward from the three destinations to the bridge-course foundations
(confirmed against Lean Mathlib's algebraic hierarchy, Metamath's ZFC→ℝ→ℂ build,
and standard "transition to proof" curricula — see Source Pointers):

```text
Layer 0 — Foundations (the "bridge"):
  Propositional logic → Predicate logic → Proof methods → Induction
  Sets → Relations & functions → Cardinality

Layer 1 — Number systems:
  Naturals (Peano) → Integers → Rationals → Reals (completeness) → [Complex]

Layer 2 — Core structures & tools:
  Divisibility & Euclidean algorithm (gcd, Bézout)
  Modular arithmetic & congruences
  Groups → Rings → Fields        (Mathlib's algebraic hierarchy)
  Polynomials
  Sequences & limits
  Counting / combinatorics

Layer 3 — Destinations:
  Number theory   ⟸ divisibility, modular arithmetic, induction, integers
  Linear algebra  ⟸ fields, functions, systems of linear equations
  Calculus        ⟸ reals, sequences & limits, functions
```

Every arrow is a prerequisite: e.g. abstract algebra presupposes the division
algorithm, the Euclidean algorithm, unique factorization, equivalence relations,
functions, and induction (the standard bridge-course prerequisite list).

## The decidability lens (what axeyum can self-check per node)

The DAG is a reading list; the *testable* slice is the decidable/computable
fragment of each node. This is the load-bearing filter — and the payoff is that
the testable slice maps directly onto axeyum's arithmetic theories, so math-tour
exercises double as the comprehensive corpora those theories currently lack
(especially NRA / P2.5).

| Node | Self-checkable fragment | axeyum theory |
|---|---|---|
| Propositional logic | tautologies/contradictions (complete) | Bool/SAT ✓ (`Family::Logic`) |
| Predicate logic | finite-domain instances | quantifiers (finite) |
| Induction | base + step *instances* as decidable checks (not the schema) | LIA/BV |
| Sets / relations / functions | finite-set identities, function properties on finite domains | BV / enumeration |
| Naturals / integers | concrete arithmetic, ordering, parity | LIA / BV ✓ |
| Rationals / reals | exact rational arithmetic, linear facts | LRA ✓ |
| Divisibility & Euclid | gcd & Bézout (compute-and-check); linear Diophantine (un)solvability | BV / LIA + GCD test ✓ |
| Modular arithmetic | congruence identities, inverses, CRT instances | BV ✓ / LIA |
| Groups / rings / fields | finite (Cayley-table) identities, 𝔽_p arithmetic | BV / enumeration |
| Polynomials | polynomial identities (fixed degree), factor checks | NRA / exact |
| Sequences & limits | algebraic limit *values* (fixed), monotonicity instances | LRA / NRA |
| Number theory | bounded instances (Fermat's little theorem at fixed p, FTA via factor check), Diophantine | BV / LIA |
| Linear algebra | fixed-size matrix identities, system solving, det/eigen identities over ℚ | LRA / NRA + exact |
| Calculus | symbolic-derivative-rule checks, polynomial/rational identities, RCF inequalities (AM-GM/Cauchy-Schwarz at fixed n) | NRA |

**Lean-horizon (not testable, by design):** the ∀-quantified general theorems —
infinitude of primes, fundamental theorem of arithmetic in general, completeness
of ℝ, general vector-space/dimension theorems, ε–δ continuity. These are
proof-reconstruction targets for P3.6/P3.7 and the substance of the "limits of
automation" lesson, not benchmark instances.

## Build / import / test strategy

- **Import the sequencing, not the content.** The DAG above is the canon; cite
  Mathlib / Metamath / bridge courses as authority rather than reinventing. Do
  **not** ingest a formal library or a textbook wholesale (no Lean/Coq frontend;
  consistent with the example-suites and ADR-0008 rules).
- **Build a `MathConcept` curriculum DAG** in `axeyum-scenarios::mathtour`,
  mirroring the solver `concept` DAG: nodes, prerequisites, topological teaching
  order, a decidability classification per node, and a mapping to self-checking
  exercise families.
- **Build self-checking exercise families bottom-up, decidable-first.** Each is
  oracle-free per ADR-0008 (SAT by concrete execution; UNSAT by bounded/exhaustive
  enumeration; or a rational/witness check), rendered as an `Exercise`, and graded
  by the trusted evaluator.
  1. **Number theory** (first, built with this note): Bézout's identity
     (`a·x + b·y = gcd`, witness from extended Euclid), modular inverse
     (`a·a⁻¹ ≡ 1`), "product of consecutive integers is even", "x² ≡ x (mod 2)".
     Maps to BV — already decided by `sat-bv`.
  2. **Linear algebra** (next): fixed-size matrix identities over ℚ/𝔽₂, linear
     system solving (LRA), 2×2/3×3 determinant identities. Pressures LRA/NRA.
  3. **Calculus** (then): polynomial/rational identities, symbolic-derivative-rule
     checks, RCF inequalities at fixed n. The corpus P2.5/NRA is missing.

## Risks

- **Undecidability mistaken for a benchmark.** Most named theorems are ∀-general
  and undecidable. Mitigation: the decidability table; Lean-horizon nodes are
  reconstruction targets, never benchmark instances.
- **Overclaiming "we formalized calculus".** We self-check a *decidable fragment*
  per node; the conceptual layer is narrative + (eventually) Lean. State this
  plainly in every module.
- **Curriculum sprawl.** Mitigation: build decidable-first, one family at a time,
  each wired into the coverage audit so gaps stay visible and honest.

## Open Questions

- [ ] Should `MathConcept` be a second DAG (clean) or unified with the solver
      `concept` DAG (one graph)? (Leaning: a second DAG — different audience,
      different mapping; both can share the `Exercise`/grading/render layer.)
- [ ] For the unbounded-integer Diophantine *unsolvability* cases (UNSAT over ℤ,
      not finitely enumerable), is the GCD-test certificate the self-check, or do
      we keep number theory to BV/bounded instances first?
- [ ] Which linear-algebra base field first — ℚ (LRA, exact), 𝔽₂ (BV), or both?

## Source Pointers

- ADR-0033 (double-duty educational artifacts): ../09-decisions/adr-0033-double-duty-educational-artifacts.md
- Example-suites note (decidability lens, tiers): foundational-example-suites.md
- Solver concept DAG: ../../../crates/axeyum-scenarios/src/concept.rs
- Lean Mathlib (algebraic hierarchy, coverage): https://leanprover-community.github.io/mathlib-overview.html
- Metamath Proof Explorer (ZFC → ℝ/ℂ): https://us.metamath.org/mpeuni/mmset.html
- Mathematics in Lean (Avigad et al.): https://leanprover-community.github.io/mathematics_in_lean/
- "Transition to Higher Mathematics" (bridge-course canon): https://www.math.wustl.edu/~mccarthy/SandP2.pdf
