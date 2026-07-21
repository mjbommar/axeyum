# CAS architecture survey — SymPy, Mathematica, Symbolica, and the algorithm taxonomy

Status: research note (2026-07-20)
Last updated: 2026-07-20

How mainstream computer-algebra systems are built, what their capability surface
is, and which algorithms/decidability class each capability sits in. Feeds
[decidability-map.md](decidability-map.md), [gap-analysis.md](gap-analysis.md),
and [build-plan.md](build-plan.md). Sourced; URLs at the end.

## 1. The two dominant architectures

### SymPy — typed class hierarchy over a shared `args` protocol
- **`Basic` → `Expr`**: every object is a `Basic`; `Expr` adds arithmetic
  (`Add`/`Mul`/`Pow`). The universal representation is the **`.args` tree** with
  the invariant **`expr == expr.func(*expr.args)`** (head applied to children
  reproduces the node; atoms have empty `args`). This is the single most
  important structural idea, and axeyum's `TermNode::App{op, args}` +
  `rebuild_with_args` already satisfies exactly this contract.
- **Immutable + interned + cached** — enables structural hashing and memoization;
  maps directly onto axeyum's hash-consed arena.
- **Automatic vs manual simplification (a sharp, deliberate line):** construction
  time does only *cheap, always-terminating* canonicalization (flatten nested
  same-head, sort commutative args, combine numeric coefficients, `x+x→2x`).
  Everything expensive is **opt-in and directed**: `expand`, `factor`, `cancel`,
  `together`, `trigsimp`, plus the heuristic `simplify`. The reason the automatic
  layer is weak is **Richardson's theorem** (§3): no canonical form exists for
  general elementary expressions, so a complete always-on `simplify` is
  impossible.
- **Assumptions system**: three-valued (`True`/`False`/unknown) predicates
  (`positive`, `integer`, `real`, …) that *derive* over composite expressions and
  gate domain-sensitive rewrites (`sqrt(x²)→x` only when `x≥0`). This is how a CAS
  stays sound about branch cuts.
- **`polys` is a dedicated subsystem, not a wrapper**: a distinct dense/sparse
  polynomial representation over an explicit **coefficient domain tower**
  (`ZZ`, `QQ`, `GF(p)`, `ZZ[x]`, `QQ⟨a⟩`), with `as_expr()` back-conversion.
  Gröbner bases are first-class (Buchberger + FGLM, selectable monomial orders).
- **`integrate` is a portfolio with fallthrough**: polynomial → table/pattern →
  `manualintegrate` → `heurisch` (heuristic Risch) → `risch_integrate`
  (Risch–Norman) → Meijer-G for definite/non-elementary. No single implemented
  engine is both complete and fast, so it is a cascade. Summation mirrors this
  (Gosper → Zeilberger).

### Mathematica / Wolfram — uniform-expression term rewriting to fixed point
- **Everything is `head[args...]`**; computation is repeated pattern-directed
  **rewriting until no rule applies** (fixed point).
- **Attributes drive canonicalization declaratively**: `Flat` (associativity →
  auto-flatten), `Orderless` (commutativity → canonical arg sort — exactly
  SymPy's `Add`/`Mul` sort, but as an attribute), `Listable`, `HoldFirst/HoldAll`.

**Takeaway for axeyum.** The `head[args]` model is already the arena. The right
design blends both: a **uniform CAS expression node** (Wolfram-style, with
`Flat`/`Orderless` realized as canonicalization passes — axeyum's
`COMMUTATIVE_ORDER` rule is already this) plus **typed fast-path representations**
(polynomials, matrices) SymPy-style for the domains where a normal form exists.
Symbolica (below) takes the rewriting-engine route.

## 2. Rust ecosystem (state of the art + the opening)

- **Symbolica** — the only production-grade Rust CAS: uniform `Atom` +
  specialized rational-polynomial rep, global append-only symbol table with
  namespacing, Wolfram-style pattern matching/rewrites, world-class multivariate
  GCD/factorization, numeric codegen. **But source-available proprietary**
  (paid for commercial use). At 1.0 it spun out two **MIT** crates — `numerica`
  (number types, finite fields, autodiff, matrices, numerical integration) and
  `graphica` (graph canonicalization) — reusable, but the symbolic core is not.
- **Everything else is early-stage**: `cas-rs`, `rusymbols`, `rust-cas`,
  `mathhook` (educational). Gröbner crates: `groebner` (Buchberger + F4),
  `polynomial-ring`, `rustnomial`. (Note: a crate named `calcu-rs` could not be
  confirmed maintained.) Julia's `Groebner.jl` (F4 + tracing) is the best modern
  algorithmic reference even though not Rust.
- **The opening (why this is genuinely new):** there is **no permissively-licensed
  Rust CAS** with a domain-tower polynomial system, a Risch/integration stack, an
  assumptions engine, or F4/F5 Gröbner. **And none — in any language — makes the
  trust status of each answer a first-class, machine-checkable output.** That is
  axeyum's differentiator, not raw polynomial speed (where Symbolica leads).

## 3. Capability taxonomy (algorithm · decidable? · complete?)

Condensed; the certificate route per capability is in
[decidability-map.md](decidability-map.md).

| Capability | Core algorithm | Decidable? | Complete? |
|---|---|---|---|
| Polynomial +,×,÷ | classical/Karatsuba/FFT; long division | Yes | Yes |
| Polynomial GCD | Euclid → **subresultant PRS** (tames coeff. blow-up) | Yes | Yes |
| Factor over 𝔽ₚ | **Berlekamp** / Cantor–Zassenhaus | Yes | Yes |
| Factor over ℤ/ℚ | **Berlekamp–Zassenhaus** + Hensel + **LLL/van Hoeij** recombination | Yes | Yes |
| Gröbner / ideal membership | **Buchberger**, **F4/F5**, FGLM | Yes | Yes (doubly-exp worst case) |
| Differentiation | mechanical sum/product/chain rules | Yes | Yes |
| Simplify / canonical form (general) | directed rewriters + heuristic search | **No** | **No** (Richardson) |
| Zero-testing / equality (elementary) | normal form where one exists; else heuristic | **No** (with sin/exp/abs) | **No** |
| Integration (elementary) | **Risch** decision proc; Risch–Norman; heurisch; Meijer-G | **Conditional** (needs constant-field zero-test oracle) | complete only over computable constant fields |
| Linear solve / det (exact) | **fraction-free Bareiss** | Yes | Yes |
| Polynomial system solving | Gröbner elimination + resultants | Yes | Yes (alg. closed field) |
| Transcendental equation solving | pattern/substitution/LambertW; else numeric | **No** | **No** |
| Limits | **Gruntz** (mrv, exp-log Hardy fields) | Yes (on exp-log) | complete on that class |
| Series (Taylor/Laurent/Puiseux) | formal power series to order | Yes (finite order) | Yes |
| Indefinite hypergeometric sum | **Gosper** | Yes | Yes |
| Definite hypergeometric sum | **Zeilberger** (creative telescoping) | Yes on holonomic | complete on holonomic |
| Eigen / char. poly (exact) | fraction-free Faddeev–LeVerrier / Berkowitz | char.poly Yes | roots limited (Abel–Ruffini) |
| Integer matrix normal forms | **Smith / Hermite** (Bareiss-extended) | Yes | Yes |
| Primality | Miller–Rabin / **AKS** / **ECPP** (certificate) | Yes | Yes |
| Integer factorization | trial → Pollard-ρ/p−1 → **ECM** → QS/GNFS | Yes (no poly-time known) | Yes |
| Diophantine (general) | — | **No** (MRDP) | **No** |
| Special functions / branch cuts | definitions + branch conventions + assumptions | convention-dependent | **No** (CAS disagree) |

Engineering notes to carry: **subresultant PRS** (not naive Euclid) for GCD;
**Bareiss** for all exact linear algebra (intermediates stay in the domain);
**F4/F5** recast S-poly reduction as sparse linear algebra.

## 4. The load-bearing theorems (Section 5 of the research)

- **Richardson's theorem (1968).** For expressions over ℚ, π, ln 2, x, +, −, ×,
  composition, and **sin, exp, |·|**, deciding **identity-to-zero is undecidable**
  (reduction from Hilbert's 10th / MRDP). ⇒ *no* algorithm for general expression
  equality, *no* canonical form for elementary expressions, *no* complete
  `simplify`. A correct normal form never asserts a false identity but may fail to
  prove a true one.
- **Zero-testing hierarchy** (the pivot for certification):
  - **Decidable + witness**: polynomials/rational functions/algebraic numbers/
    finite fields — a normal form exists and *is* the certificate. ← axeyum's zone.
  - **Decidable but expensive**: restricted radical/exp-log constant towers.
  - **Unknown / undecidable**: general elementary constants (the "constant
    problem"); provably undecidable once `abs` is admitted.
- **Risch is decidable *relative to* a constant-field zero-test oracle**: over a
  computable constant field (ℚ, ℚ(rational functions)) it is a complete decision
  procedure (returns an elementary antiderivative or *proves none exists*);
  otherwise only a semi-algorithm. ⇒ integration is certifiable exactly when the
  constants live in a field with a decidable zero-test.

**The design consequence** (this is the whole thesis): attach a **trust tag** to
every result — `certified` (witness attached), `decidable-uncertified` (correct
algorithm, no witness emitted), `heuristic` (may fail to find a true answer; never
asserts a false one). axeyum already has this discipline (the capability matrix's
checked/validated/sound-incomplete levels, the trust ledger); the CAS makes it a
first-class per-answer output. No existing CAS does this.

## Key references
- SymPy: Meurer et al. 2017, PeerJ CS 3:e103 (DOI 10.7717/peerj-cs.103) —
  https://peerj.com/articles/cs-103/ · core https://docs.sympy.org/latest/modules/core.html ·
  args invariant https://docs.sympy.org/latest/tutorials/intro-tutorial/manipulation.html ·
  assumptions https://docs.sympy.org/latest/guides/assumptions.html ·
  polys https://docs.sympy.org/latest/modules/polys/index.html ·
  Gröbner thesis https://mattpap.github.io/masters-thesis/html/src/groebner.html ·
  integrals https://docs.sympy.org/latest/modules/integrals/integrals.html ·
  solveset https://docs.sympy.org/latest/modules/solvers/solveset.html
- Wolfram evaluation model: https://reference.wolfram.com/language/tutorial/EvaluationOfExpressions.html ·
  term rewriting walkthrough https://www.stephendiehl.com/posts/exotic_02/
- Richardson: https://en.wikipedia.org/wiki/Richardson's_theorem ·
  original https://dl.acm.org/doi/pdf/10.1145/321850.321856
- Risch: https://en.wikipedia.org/wiki/Risch_algorithm
- Gruntz limits: https://algo.inria.fr/seminars/sem92-93/gruntz.html
- Berlekamp–Zassenhaus: https://mathworld.wolfram.com/Berlekamp-ZassenhausAlgorithm.html
- Subresultant GCD (Collins): https://people.eecs.berkeley.edu/~fateman/282/readings/collins.pdf
- Buchberger / F4–F5: https://en.wikipedia.org/wiki/Faug%C3%A8re's_F4_and_F5_algorithms
- Bareiss: https://grokipedia.com/page/Bareiss_algorithm · fraction-free→Smith/Hermite https://arxiv.org/pdf/2005.12380
- Gosper/Zeilberger: https://mathworld.wolfram.com/GospersAlgorithm.html · Chyzak https://specfun.inria.fr/chyzak/Publications/Chyzak-2014-ACT.pdf
- AKS primality: https://en.wikipedia.org/wiki/AKS_primality_test
- Symbolica: https://symbolica.io/ · 1.0 (numerica/graphica MIT) https://symbolica.io/posts/stable_release/ · license https://symbolica.io/license/
- Hash-consing for symbolic computation: https://arxiv.org/pdf/2509.20534
- Groebner.jl: https://arxiv.org/pdf/2304.06935
- Branch-cut CAS discrepancies: https://arxiv.org/pdf/2201.09488
