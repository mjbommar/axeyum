# ADR-0039: Degree-2 sum-of-squares / PSD nonnegativity certificate for NRA

Status: accepted
Date: 2026-06-20

## Context

The NRA path ([ADR-0024](adr-0024-nra-linear-abstraction.md)) abstracts each
nonlinear product to a fresh variable and strengthens the relaxation with sign /
sum-of-squares *lemmas*, McCormick envelopes, and spatial branch-and-bound. To
stay within a deterministic memory bound it **declines** (`Unknown`) once a query
has more than `MAX_CROSS_PRODUCTS = 2` distinct-operand products — the dense
disjunctive lemma set over three or more cross-products can OOM the relaxation
inside a single solve call.

That admission bound is sound but coarse. It declines an entire class of *easy*,
genuinely valid inequalities that Z3 proves instantly — most visibly multivariate
**AM–GM**:

- 2-var `x² + y² ≥ 2xy` — refutation `x² + y² − 2xy < 0`, i.e. `(x−y)² < 0`.
- 3-var `a² + b² + c² ≥ ab + bc + ca` — refutation
  `a²+b²+c²−ab−bc−ca < 0`, i.e. `½((a−b)²+(b−c)²+(c−a)²) < 0` (three
  cross-products → previously declined at the admission bound).

These are exactly the polynomial geometry goals on the parity ladder (the
`geometry_portfolio` example, the curriculum's `Family::Polynomial`). Each is a
**quadratic form that is globally nonnegative**, so its strict-`< 0` refutation is
`Unsat` — decidable exactly, with no search and no relaxation blow-up.

## Decision

Add a **degree-2 sum-of-squares certificate** to the exact polynomial decider
(`decide_real_poly_constraint`, `crates/axeyum-solver/src/nra_real_root.rs`),
which runs *before* the abstraction search and its `MAX_CROSS_PRODUCTS` decline.
For a strict polynomial inequality atom `p ⋈ 0` whose polynomial has total degree
≤ 2, the decider tests global sign-definiteness of the quadratic form and decides
`Unsat` when it holds.

### The certificate

Write `p(x) = [x; 1]ᵀ M [x; 1]` with the `(n+1)×(n+1)` symmetric rational matrix

- `M[i][i]` = coefficient of `xᵢ²`,
- `M[i][j] = M[j][i]` = ½ · coefficient of `xᵢxⱼ` (i ≠ j),
- `M[i][n] = M[n][i]` = ½ · coefficient of the linear term `xᵢ`,
- `M[n][n]` = the constant term.

Then:

- **M positive-semidefinite ⇒ `p(x) ≥ 0` for all x** ⇒ a strict `p < 0` atom is
  **Unsat**.
- **−M positive-semidefinite (M negative-semidefinite) ⇒ `p(x) ≤ 0` for all x** ⇒
  a strict `p > 0` atom is **Unsat**.

These are **sufficient** conditions (`M ⪰ 0 ⇒ p ≥ 0` because
`p(x) = [x;1]ᵀM[x;1] ≥ 0` for every `x`); they are not necessary, and that is
acceptable — anything not covered **declines** to the unchanged search. Soundness,
not completeness, is the contract.

### Scope guards (soundness)

- **Strict only.** PSD yields `p ≥ 0`, *not* `p > 0`, so non-strict `p ≤ 0` is
  *satisfiable* at the form's zero and must **not** be reported `Unsat`. Only the
  strict refutation shapes (`p < 0` with `M ⪰ 0`, `p > 0` with `M ⪯ 0`) conclude
  `Unsat`.
- **Degree ≤ 2 only.** If any monomial has total degree ≥ 3 the form is not
  quadratic; decline.
- **Never `Sat`.** The certificate only ever refutes; a satisfiable or
  indefinite form declines (e.g. `x² − y² < 0`, `xy < 0` are indefinite and stay
  decidable by other means or `Unknown`, never a wrong `Unsat`).

### Exact PSD test (no floating point)

Positive-semidefiniteness is decided by symmetric `LDLᵀ` (Gaussian) elimination
over exact `Rational` pivots: a symmetric matrix is PSD iff it reduces with every
diagonal pivot `≥ 0` and every **zero** pivot accompanied by a zero remaining
row/column (a zero pivot with a nonzero off-diagonal refutes PSD). All arithmetic
uses the checked `Rational` methods; any `i128` overflow **declines** (consistent
with the solver-wide overflow-safety discipline — see the never-crash rule). No
float ever touches the decision.

## Consequences

- 2- and 3-variable AM–GM (and other globally-(non)negative quadratic forms,
  e.g. `(x−1)² ≥ 0`) are now decided `Unsat` instantly, where the engine
  previously declined at the cross-product admission bound — a measured step
  toward NRA parity on the polynomial-geometry corpus.
- The certificate is a **decision** only; it does not yet emit an Alethe/Lean
  *proof object*. An SOS proof certificate (the rational `LDLᵀ` decomposition is
  itself the witness `p = Σ dₖ · ℓₖ²`) is a natural future slice on the proof
  track, deferred here.
- Higher-degree SOS, the Positivstellensatz (constrained nonnegativity over a
  set of hypotheses, not just global), and full multivariate CAD/nlsat remain the
  documented multi-session NRA frontier ([ADR-0038](adr-0038-real-algebraic-numbers.md)
  slices 2–4); this ADR deliberately scopes to the global, unconstrained,
  degree-2 case that is both common and cheap.
