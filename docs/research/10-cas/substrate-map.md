# CAS substrate map — what already exists (file:line inventory)

Status: grounded inventory (2026-07-20)
Last updated: 2026-07-20

Source: read-only survey of the tree at kickoff. Paths under
`crates/`. This is the factual base for [gap-analysis.md](gap-analysis.md) and
[build-plan.md](build-plan.md); update it when the substrate changes.

## Already present (the hard half)

### Term representation — Mathematica's `head[args]` DAG, already built
- `axeyum-ir/src/term.rs` — hash-consing key `TermNode` (`:344`), operator space
  `Op` (`:78`, ~120 variants across Bool/BV/Int/Real/Array/Datatype/UF/FP/Seq),
  `Copy` u32 id handles (`TermId`, `SymbolId`, `FuncId`, …). `App{op, args:Box<[TermId]>}`.
- `axeyum-ir/src/sort.rs` — `Sort` (`:121`): Bool, BitVec(≤2^16, incl. wide),
  Int, Real, Array, Datatype, Uninterpreted, Float, Seq (String = Seq(BV18)).
- `axeyum-ir/src/arena.rs` — `TermArena` (`:25`): implicit interning in every
  builder (identical build sequences → identical ids), sort-checked constructors
  for every `Op`, `declare_fun`/`apply` (UF), datatypes, `rebuild_with_args`
  (`:478`), `replace_subterms` (structural id replacement).

### Exact arithmetic + univariate polynomial algebra — the certifiable core
- `axeyum-ir/src/rational.rs` — `Rational` i128/i128, overflow-graceful
  `checked_*`.
- `axeyum-ir/src/poly.rs` — exact univariate `RatVec = Vec<Rational>` (LSB-first):
  `rat_derivative` (`:56`, **formal derivative**), `rat_rem` (`:70`),
  `rat_gcd` (`:105`, Euclidean), `rat_make_monic`, `rat_exact_div`,
  `squarefree_part` (`:180`, `p/gcd(p,p′)`), `ratpoly_mul/add/neg`,
  `eval_rat_poly` (Horner), `rat_to_int_poly` (denominator clearing),
  `sturm_chain` (`:343`), `count_roots_in` (`:399`, **exact distinct real-root
  count**), `sylvester_matrix`/`sylvester_determinant` (`:692`/`:485`,
  **resultants** via Bareiss+Newton, Leibniz oracle at `:456`).
- `axeyum-ir/src/poly_big.rs` — bignum mirror (algebraic-number `+`/`×` via
  resultants), `big_determinant`, `combine_retry` (interval refinement).
- `axeyum-ir/src/real_algebraic.rs` — `RealAlgebraic` (`:84`, defining poly +
  isolating interval): `sign_at`, `compare_*`, **field arithmetic** `neg`/`add`/`mul`
  (deg ≤ 24). This is a real algebraic-number engine.

### Semantics, canonicalization, equality
- `axeyum-ir/src/eval.rs` — `eval` (`:214`) total ground interpreter over all
  sorts (functional arrays/UF); `value.rs` `Value` incl. `RealAlgebraic`. The
  executable denotation reference (**not** a symbolic simplifier).
- `axeyum-rewrite/src/canonical.rs` — fixed bottom-up **denotation-preserving**
  canonicalizer, ~60 hard-coded rules (`default_rules()` `:303`): const-fold,
  Boolean/BV identities, BV slice algebra, `COMMUTATIVE_ORDER` AC-flatten/sort
  (`:581`). Metadata manifest (`RewriteRule`, `Preservation::Denotation`,
  `ModelProjection`). Also preprocessing passes: `solve_eqs` (Gaussian equality
  elimination + `ModelReconstructionTrail`), array/function elimination,
  int-blasting, quantifier instantiation.
- `axeyum-egraph/src/lib.rs` — backtrackable **congruence-closure** e-graph:
  `add`/`merge`/`find`/`explain` (proof forest), `Pattern`/`ematch*` e-matching,
  `EMatchIndex`. **No** cost function, extraction, or saturation loop — patterns
  match but rewrites are never applied inside it.

### Decision procedures usable as the checker (via `axeyum-solver`)
- `nra_real_root.rs` — `decide_real_poly_constraint` (`:336`), Sturm isolation,
  `SosCertificate`/`verify` (`:6458`, sum-of-squares). Plus `nra_sos.rs`,
  `nia_square.rs`, `lia_gcd.rs`. RCF/NRA decision consuming `poly.rs`.
- Full certified capability set in
  [capability-matrix.md](../08-planning/capability-matrix.md).

### Adjacent symbolic machinery
- `axeyum-strings/src/regex/derivative.rs` — Brzozowski/Antimirov regex
  derivatives (symbolic *automata*, not calculus).
- `axeyum-lean-kernel` — Lean type-theory kernel (whnf/def-eq) for proof
  reconstruction.

## Missing (the compute side — what this initiative builds)

| Capability | Status | Nearest existing asset |
|---|---|---|
| Symbolic differentiation over terms (`d/dx` on the DAG, chain/product rule) | **absent** | `poly.rs::rat_derivative` (numeric univariate only) |
| Symbolic simplification returning a term (`expand`/`collect`/`factor`/normal form) | **absent** | fixed denotation canonicalizer (const/identity only) |
| Multivariate polynomials, Gröbner bases, multivariate GCD/factorization | **absent** | univariate `RatVec` only |
| Univariate factorization over ℚ/ℤ (Berlekamp/Zassenhaus/LLL), partial fractions | **absent** | `squarefree_part`, `rat_gcd` |
| General rewrite engine / equality saturation (apply + cost-extract) | **absent** | e-graph matches but never rewrites/extracts |
| Transcendental **operators** in the algebra (exp/log/sin/cos/sqrt as heads) | **absent** | `sqrt` only as a real-algebraic *value* |
| Integration, summation, limits, series, ODE / equation solving | **absent** | — |
| Public symbolic linear algebra (matrix type, rref/solve/det/eigen) | **absent** | internal `Vec<Vec<RatVec>>` for resultants only |
| Substitution / pattern match-and-rewrite API on the IR | **absent** | `replace_subterms` (structural id only) |

## Architectural implication (the load-bearing decision)

The IR has **no transcendental function operators** and is deliberately confined
to decidable theories. Two ways to add CAS breadth:

- **(A) Extend `axeyum-ir::Op`** with elementary functions — invasive to the
  solver core, and those heads are undecidable in general (Richardson). Rejected
  as the default.
- **(B) A new `axeyum-cas` expression layer** carrying the broad surface
  (transcendental heads, symbolic matrices, unevaluated integrals), which
  **lowers to the decidable IR core** (poly/RCF/SMT + `real_algebraic`) precisely
  where certification happens. The CAS is broad; the *certifier* stays narrow.

**Decision (proposed): (B).** It preserves the clean, decidable solver IR; reuses
`poly.rs`/`real_algebraic.rs`/`eval.rs`/the decision procedures as the trusted
checker; and makes the decidability boundary an explicit lowering boundary — the
CAS certifies an answer exactly when it can lower the equality obligation into a
theory the solver decides. To be ratified in the initiative's first ADR.
