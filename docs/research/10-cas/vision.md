# Vision — a proof-carrying computer algebra system

Status: vision (2026-07-20)
Last updated: 2026-07-20

## The vision

Build, in axeyum, the compute-side functionality of SymPy / Mathematica —
differentiate, simplify, expand/factor/collect, solve, integrate, series, limits,
summation, symbolic linear algebra, number theory — as **the first proof-carrying
CAS**: an engine that returns a transformed expression **together with a
first-class, machine-checkable trust tag** saying whether that answer is
`certified` (a witness is attached and re-checkable), `decidable-uncertified`
(a complete algorithm produced it), or `heuristic` (may fail to find a true
answer; never asserts a false one).

The engine is **pure Rust, WASM-deployable**, and reuses axeyum's certified
decision procedures as its checker. It is the compute-side realization of the
research tree's north star — *general reasoning, logic, and proving with untrusted
search and trusted checking* — extended from *deciding* facts to *computing and
certifying* transformations.

## Why axeyum, and why now

Three assets that took axeyum years to build are exactly the hard three-quarters
of a CAS, and no other project has all three (see
[substrate-map.md](substrate-map.md), [oracle-as-test-harness.md](oracle-as-test-harness.md),
[capability-matrix](../08-planning/capability-matrix.md)):

1. **The expression substrate** — a hash-consed `head[args]` term DAG (identical
   to SymPy's `func`/`args` and Wolfram's `head[e…]`), exact rational + algebraic
   number arithmetic, univariate polynomial algebra (derivative/GCD/squarefree/
   resultants/Sturm), a denotation-preserving canonicalizer, and a
   congruence-closure e-graph.
2. **The correctness oracle** — a self-grounded, non-circular, curriculum-organized
   corpus of machine-checkable identities (`Scenario::self_check`: exhaustive at
   ≤20 bits, exact witnesses otherwise), i.e. a genuine *test harness for a CAS*.
3. **The certifier** — certified decision procedures (DRAT / Alethe / Lean-kernel)
   across BV / UF / LIA / LRA / NRA / NIA / FP / arrays / datatypes / quantifiers,
   which decide precisely the zero-testing obligations a CAS's certified core
   reduces to.

The remaining quarter — the transform functions — is the mechanical part, and it
becomes tractable and *safe* precisely because every output can be checked against
(2) and (3) as it is written. The historical reason a correct CAS took decades was
not the algorithms; it was establishing correctness across mathematics. axeyum
starts with the correctness machinery already built.

## The differentiator (what only axeyum can be)

- **SymPy / Mathematica / Maple** compute and ask for trust; they *cannot* be
  complete on general simplification/equality (Richardson's theorem), and they
  hide the trust boundary. **Symbolica** leads on raw polynomial performance but
  is proprietary and does not target the decision-procedure surface.
- **axeyum's CAS** uses its own SMT/RCF engine as the **zero-tester** wherever
  zero-testing is decidable (instead of SymPy's heuristic `simplify`), and it
  **surfaces the decidability boundary as the product**: every answer is tagged,
  and `certified` answers carry a witness a third party can re-check without
  trusting axeyum. The flagship demonstration is integration: *finding* an
  antiderivative may be heuristic, but *checking* it is differentiation + a
  decidable zero-test — so axeyum can return a **certified** integral even when the
  search that found it was a heuristic.

This is not "reimplement Mathematica." It is the CAS Mathematica cannot be: one
whose answers come with proofs where proofs are possible, and with honesty where
they are not.

## Scope and non-goals

**In scope (built decidable-first):** the certified core of
[decidability-map.md](decidability-map.md) — rational-function differentiation and
canonical form/zero-testing; multivariate polynomial algebra, GCD, factorization,
Gröbner; exact linear algebra; rational-function and (where the constant field is
decidable) elementary integration via differentiate-and-check; Gosper/Zeilberger
summation; series; bounded/certified number theory; and the honestly-labeled
heuristic frontier around them (general `simplify`, transcendental solving) with
per-substep certification.

**Non-goals / deferred:**
- **Not** extending the solver IR with transcendental heads — the CAS is a
  separate layer that *lowers to* the decidable IR core (see below).
- **Not** competing on raw polynomial throughput with Symbolica; correctness +
  certification + deployability is the axis, not benchmarks-per-second.
- **Not** authoring pedagogy/prose; the engine computes, certifies, and (via the
  double-duty artifacts) grades — narrative stays human/LLM-authored.
- **Not** claiming a complete `simplify` or a complete transcendental solver —
  those are undecidable; the honest label is the feature.
- **Must not starve** the solver + Lean-parity mission ([PLAN.md](../../../PLAN.md));
  this initiative is sequenced to reuse and reinforce it, not compete for it.

## Architecture in one paragraph

A new `axeyum-cas` crate carries the **broad** expression algebra (a superset of
the IR heads: transcendental functions, symbolic matrices, unevaluated
integrals/sums/limits, polynomials over a domain tower). Transforms operate on
this algebra. **Certification is a lowering**: to certify `transform(e) ≡ e`, the
engine lowers the obligation into the **narrow** decidable IR core
(`poly.rs` / `real_algebraic.rs` / an SMT theory) and discharges it with an
existing decision procedure, attaching the returned witness. The CAS is broad; the
certifier stays narrow and clean. This keeps the solver IR confined to decidable
theories while giving the CAS unlimited surface. (Ratified in the first-slice ADR.)

## The measure of success

1. **Correctness, certified**: every `certified` answer carries a witness that
   re-checks under an independent checker, with zero unsound certificates (the
   capability-matrix discipline, applied to compute).
2. **Honesty at the boundary**: no heuristic result is ever presented as
   certified; the trust tag is always right.
3. **Coverage that co-evolves with its oracle**: every shipped transform adds a
   self-checking scenario; the curriculum coverage audit shows no certified
   capability without a test.
4. **Deployability**: the CAS runs everywhere the solver runs (pure Rust, WASM).
5. **A capability surface approaching SymPy's** on the decidable core, reached one
   evidence-gated, decidable-first slice at a time.
