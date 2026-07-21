# Computer Algebra System (CAS) — proof-carrying symbolic mathematics

Status: **active research + design** (kickoff 2026-07-20)
Last updated: 2026-07-20

> This section plans a new major capability: **a computer algebra system in
> axeyum with the compute-side functionality of SymPy / Mathematica** —
> differentiate, simplify, factor, expand, solve, integrate, series, limits,
> summation, and symbolic linear algebra — built the axeyum way. It is
> research-and-design first: nothing lands without semantics, a checker, and a
> self-checking test, exactly as the [foundational
> DAG](../08-planning/foundational-dag.md) and
> [ADR-0008](../09-decisions/adr-0008-consumer-scenario-models.md) require.

## The one-sentence thesis

Every mainstream CAS *computes* a transformed expression and asks you to trust
it; axeyum already *decides and certifies* mathematical facts. A CAS built on
axeyum is therefore the first **proof-carrying CAS**: it returns
`transform(expr)` **and** — wherever the fragment is decidable — a checkable
witness that `transform(expr)` is equal to (or a sound normalization of) `expr`,
with `unknown`/`uncertified` as a first-class, honestly-labeled outcome
everywhere else.

This is axeyum's "untrusted search / trusted checking" identity
([north star](../00-orientation/north-star.md)) applied to algebra. It is not a
reimplementation of Mathematica; it is the thing Mathematica cannot be — a CAS
that tells you exactly which of its answers carry a machine-checked proof.

## Why this is tractable now (not a decade-scale moonshot)

The reason a *correct* CAS is historically a decades-long problem is not writing
`diff` — it is *knowing the transforms are right across mathematics*. axeyum has
already built the hard half:

1. **The expression substrate exists.** The hash-consed `axeyum-ir` `TermArena`
   is exactly Mathematica's `head[args...]` DAG. `axeyum-rewrite` is a
   denotation-preserving rewrite engine with a `RewriteManifest`; `axeyum-egraph`
   is congruence closure / equality saturation; `axeyum-ir::poly` is exact
   rational polynomial algebra (`rat_derivative`, `rat_gcd`, `squarefree_part`,
   …). (Exact inventory: [substrate-map.md](substrate-map.md).)
2. **The correctness oracle exists.** The self-checking scenario corpus
   (`axeyum-scenarios`), the [curriculum knowledge graph](../../curriculum/), and
   the [formal-mathematics tour](../08-planning/formal-mathematics-tour.md) are a
   curriculum-organized, **self-grounded** (oracle-free at small width; see
   [ADR-0008](../09-decisions/adr-0008-consumer-scenario-models.md)) corpus of
   machine-checkable mathematical identities — i.e. a **test harness for a CAS**.
3. **The decision procedures are the checker.** The [capability
   matrix](../08-planning/capability-matrix.md) shows certified procedures across
   QF_BV/UF/LIA/LRA/NRA/NIA/FP/arrays/datatypes/quantifiers, with DRAT / Alethe /
   Lean-kernel certificates. Polynomial zero-testing, RCF decision, exact linear
   algebra, and bounded number theory — the certifiable core of a CAS — are
   already decided here.

The remaining work is the **compute side** (the transformation functions), which
is comparatively mechanical *when every output can be checked against an existing
oracle*. That is the whole bet.

## The decidability spine (the load-bearing distinction)

The [decidability lens](../08-planning/foundational-example-suites.md) governs
everything. CAS operations split cleanly:

- **Certifiable core** (axeyum returns a checked witness): polynomial arithmetic,
  GCD, square-free/factor over ℚ and 𝔽ₚ, **differentiation of rational
  functions** (purely algebraic), polynomial/rational **canonical form and
  zero-testing**, exact linear algebra (Bareiss, Smith/Hermite), linear &
  polynomial equation solving, bounded/modular number theory, RCF-decidable
  inequalities.
- **Heuristic / undecidable frontier** (axeyum computes, labels `uncertified`,
  and certifies *only what it can decide*): general simplification of elementary
  expressions (**Richardson's theorem** — zero-testing is undecidable),
  transcendental integration (Risch — decidable for elementary functions with
  real caveats), transcendental equation solving, general limits & summation.

The differentiator is the boundary itself: axeyum is the CAS whose every result
is tagged `checked` / `validated` / `computed-uncertified`, and which uses its
own SMT/RCF engine as the zero-tester wherever zero-testing is decidable, instead
of SymPy's heuristic `simplify`.

## Relationship to existing plans

This initiative **extends**, and must not starve, the solver + Lean-parity
mission ([PLAN.md](../../../PLAN.md), [STATUS.md](../../../STATUS.md)). It is the
compute-side realization of destinations the research tree already names:

- [north-star.md](../00-orientation/north-star.md) — general reasoning/proving.
- [formal-mathematics-tour.md](../08-planning/formal-mathematics-tour.md) — the
  backward-derived math DAG and its per-node decidable fragment. **The CAS is the
  engine that makes those nodes *computational*, not just checkable.**
- [foundational-example-suites.md](../08-planning/foundational-example-suites.md)
  — double-duty artifacts; the oracle-free ground-truth contract.
- [capability-matrix.md](../08-planning/capability-matrix.md) — the certified
  decision procedures the CAS uses as its checker.

## Documents in this section

| File | Purpose | State |
|---|---|---|
| [diary.md](diary.md) | Running research + design + prototyping log with references | live |
| [vision.md](vision.md) | The full vision, thesis, and non-goals | done |
| [substrate-map.md](substrate-map.md) | Exact inventory of existing CAS-relevant code (file:line) | done |
| [cas-architecture-survey.md](cas-architecture-survey.md) | How SymPy / Mathematica / Symbolica are built; capability taxonomy | done |
| [decidability-map.md](decidability-map.md) | Per-capability decidable? / complete? / certificate route | done |
| [curriculum-coverage.md](curriculum-coverage.md) | Node-by-node map of the CAS onto the full 23-node curriculum (+ complex, ODEs, geometry) | done |
| [oracle-as-test-harness.md](oracle-as-test-harness.md) | Why the existing corpus is a non-circular CAS test harness | done |
| [gap-analysis.md](gap-analysis.md) | Substrate vs. target; 16 build units | done |
| [build-plan.md](build-plan.md) | Phased (C0–C7), decidable-first, TDD sequence with exit gates | done |
| [rational-integration.md](rational-integration.md) | `∫ P/Q dx` algorithm (Horowitz) + certification + log-part roadmap | done |

**Decisions:** [ADR-0301](../09-decisions/adr-0301-cas-layer-reduce-to-decide.md)
(the `axeyum-cas` layer + reduce-to-decide certifier).

**Code:** `crates/axeyum-cas` — Phase C0 certified polynomial kernel
(`differentiate` / `normalize` / decidable `equal`), 11 tests + doctest passing,
clippy-clean, WASM-green. See [diary.md](diary.md) entry 2.

## Standing rules for this initiative (inherited, non-negotiable)

- **Decidable-first, thin vertical slice first** ([ADR-0001](../09-decisions/adr-0001-vertical-slice-first.md)):
  the first slice is the certified polynomial kernel (canonicalize + differentiate
  + decidable equality), end to end, before any transcendental breadth.
- **Every transform ships with its checker and a self-checking scenario.** No
  compute function is public until its output is either denotation-preserving by
  a manifested rewrite rule or checked by a decision procedure, with a test.
- **`unknown`/`uncertified` is first-class.** Never present a heuristic result as
  certified; label the trust route per result (cf. the [trust
  ledger](../08-planning/trust-ledger.md)).
- **No oracle laundering.** SymPy/Mathematica/Z3 may be *differential oracles* in
  tests, never the ground truth of a shipped answer.
- **WASM-safe by default.** Pure Rust; the CAS runs where the solver runs.
