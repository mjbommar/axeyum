# Axeyum

**Axeyum answers hard questions about logic, math, and programs — and *proves*
its answers instead of asking you to trust them.**

Give it a claim ("this bit-vector formula can never be satisfied", "this Rust
function can't panic", "the derivative of x² + c is 2x") and Axeyum decides it.
When the answer is *yes*/*no*, it hands back a small, independently re-checkable
certificate — a model you can evaluate yourself, or a proof a tiny checker (or a
Lean-grade kernel) can verify without trusting the search that found it.

It's written entirely in Rust, has **no C or C++ in the default build**, and
**runs in the browser via WebAssembly** — no server, no install, same trust
guarantees client-side as native.

> **The one idea:** *untrusted fast search, trusted small checking.* Finding the
> answer is allowed to be big and clever; being *sure* of the answer is done by
> code small enough to audit.

## Four familiar tools, one proof-carrying stack

If you already use these, here's where Axeyum fits:

| If you reach for… | …Axeyum is | What's different |
|---|---|---|
| **Z3 / cvc5** (SMT solvers) | a pure-Rust SMT solver | every `unsat` carries a machine-checkable proof, not just a verdict |
| **Lean / Coq** (proof assistants) | a certificate-first prover with an in-tree Lean-style kernel | fast automated search *emits* proofs a small kernel checks — the search never enters the trusted base |
| **Mathematica / SymPy** (computer algebra) | a **proof-carrying CAS** | differentiate / factor / integrate / solve return results *certified* by lowering to the decidable core — out of fragment it declines, never guesses wrong |
| **a textbook + a lab** | a built-in library of tutorials, rules, axioms, and worked theorems | the same artifacts that *teach* a concept also *test* an Axeyum theory (double-duty) |

All four share one typed core, one trust boundary, and one pure-Rust,
WASM-clean build.

## Honest status

Axeyum today is a **broad, evidence-backed foundation** — decidable theories and
arithmetic, end to end, with checkable evidence, plus a working proof-carrying
CAS and consumer-facing verifiers. It is **not yet**:

- a **performance-parity** replacement for Z3/cvc5 (the pure-Rust path *decides* a
  real slice of public QF_BV; head-to-head speed on real corpora is the open gate);
- **full SMT-LIB breadth** (unbounded strings and quantified arithmetic are partial);
- **Lean parity** (bit-vector-reducible `unsat` carries DRAT/Farkas certificates
  today; exporting those as Lean-checkable proof *terms* is a built-but-incomplete
  ladder — the in-tree kernel currently has the term language and de Bruijn
  machinery, with reduction/def-eq/type-checking as the next slices).

The followable roadmap from here to Z3 + Lean parity is [PLAN.md](PLAN.md); the
live tracker is [STATUS.md](STATUS.md). 300+ decision records (ADRs) capture the
design. The authoritative, golden-tested inventory (capability × assurance ×
evidence) is the
[capability matrix](docs/research/08-planning/capability-matrix.md).

---

## The four angles in detail

### 1. SMT solver (the Z3 / cvc5 angle)

A typed term IR → rewriting → query planning → solver backends, with a
**dependency-free pure-Rust path**: bit-blast to AIG → Tseitin CNF → a custom
CDCL SAT core. Theories, each wired end to end (IR → evaluator → decision
procedure → SMT-LIB 2 I/O):

- **QF_BV** — full scalar operator set, widths to 2¹⁶; `unsat` carries a
  DRAT-checked proof.
- **Arrays** (QF_ABV, eager elimination), **uninterpreted functions** (QF_UF,
  Ackermann), and their composition **QF_AUFBV**.
- **Linear arithmetic** — `QF_LRA` (exact-rational simplex, Farkas-certified
  `unsat`), `QF_LIA` (bit-blast + branch-and-bound simplex), mixed `QF_LIRA`
  (MILP); Boolean combinations via lazy SMT / DPLL(T) over a shared
  congruence-closure **e-graph** (`axeyum-egraph`).
- **Floating point** (QF_FP) — IEEE 754 arithmetic for **F16/F32/F64/F128** and
  ML formats, differentially validated against native `f32`/`f64` and
  `rustc_apfloat`.
- **Datatypes** (algebraic, recursive), **nonlinear** arithmetic (QF_NRA/NIA,
  sound-incomplete), **quantifiers** (finite-domain complete + E-matching/MBQI),
  and **strings / sequences** (`axeyum-strings`, the cvc5 normal-form procedure;
  bounded QF_S is BV-lowered today).

**Where Z3/cvc5 fit:** they are the differential oracle and the parity yardstick,
not a runtime dependency. The pure-Rust stack is the product; native backends
(`z3` first) are optional feature-gated leaves used for cross-checking and
head-to-head benchmarking (ADR-0002). Parity is a *measured* claim, kept honest
against public corpora.

### 2. Prover & proof assistant (the Lean angle)

Every `sat` is checkable by evaluation; every supported `unsat`/`valid` aims to
carry a **machine-checkable proof** a Lean-grade kernel would accept:

- `unsat` over the bit-vector-reducible core (QF_BV/ABV/UF/AUFBV/bounded-LIA/
  datatypes) → an externally re-checkable **DRAT** certificate (in-tree RUP+RAT
  checker, the `drat-trim` analogue), which also certifies the bit-blasting
  faithful vs an independent reference — closing the term→CNF gap.
- `QF_LRA` `unsat` → a **Farkas** refutation (exact-rational, self-verifying).
- **k-induction** safety proofs emit a DRAT certificate for *each* obligation.

The endgame is Lean parity: `axeyum-lean-kernel` is an in-tree Rust
reimplementation of the Lean 4 kernel (lifetime-free interned `Name`/`Level`/
`Expr` + de Bruijn ops today; WHNF, definitional equality, and type checking are
the next slices), and the **prover track** (designed; ADR-0167) extends
certificate-first reasoning from *formulas* to *goals* — a tactic is an untrusted
procedure that emits a certificate a small checker turns into a kernel-checked
term. The tactic never enters the trusted base.

### 3. Computer algebra (the Mathematica / SymPy angle)

`axeyum-cas` is a **proof-carrying CAS** (ADR-0301): pure Rust, WASM-safe,
oracle-free. Where a mainstream CAS *computes* a transformed expression and asks
you to trust it, Axeyum *decides and certifies*. Results are exact; certified
operations carry a machine-checked backstop (a decidable zero-test, or
differentiate-and-check), so an out-of-fragment case **declines rather than
returns a wrong answer**. Current surface (167 tests, clippy-clean):

- **Calculus** — `differentiate`/`differentiate_n`, `integrate` (polynomial, full
  rational via Horowitz + Rothstein–Trager, `∫p·eˣ`, `∫p·sin|cos`),
  `definite_integrate` (FTC), `limit`, `series`/`series_at` (Taylor), summation.
- **Algebra** — `expand`, `simplify`, `factor` (full ℤ/ℚ, Berlekamp–Zassenhaus),
  `cancel`, `apart`, `poly_gcd`, `resultant`, `discriminant`, `solve` (rational,
  quadratic, complex, factorable degree ≥ 3), Gröbner bases, radical simplification.
- **Linear algebra** — matrices (determinant, RREF, inverse, null space, rank,
  trace), characteristic/minimal polynomials, eigenvalues/eigenvectors; vector
  calculus (gradient, Jacobian, divergence, curl).
- **Number theory** — primality, factorization, φ, CRT, Legendre/Jacobi,
  primitive roots, discrete log (BSGS), continued fractions, Pell.
- **ODEs** — constant-coefficient linear (homogeneous + polynomial-forcing
  undetermined coefficients), plus complex arithmetic and exact statistics.

The coverage target is *at least* SymPy's compute surface, aiming at
Mathematica's, measured against the 23-node
[formal-mathematics curriculum](docs/curriculum/README.md). See the
[CAS notes](docs/research/10-cas/README.md).

### 4. The pre-built library (tutorials, rules, axioms, theorems)

Axeyum ships a curated, machine-readable knowledge layer — not just a solver but
a *place to learn and to encode*:

- **[Formal Mathematics Tour](docs/curriculum/README.md)** — a curriculum
  knowledge graph worked backward from calculus, number theory, and linear
  algebra to their prerequisites, plus a **K-12 layer** teaching logic +
  reasoning + math + CS as one subject. Double-duty: each node both teaches a
  concept and tests a theory (ADR-0033).
- **[Proof Certificate Cookbook](docs/proof-cookbook/README.md)** — recipes that
  take a tiny formula, show the solver route, the evidence artifact, the checker,
  and whether it reconstructs to Lean.
- **[Rules-as-Code Verification Lab](docs/rules-as-code/README.md)** — a
  disciplined workflow for formalizing laws, policies, and eligibility/compliance
  rules: cite the source, encode a small model, check consistency and edge cases,
  replay counterexamples, state the trust boundary.
- **[SMT Fragment Atlas](docs/atlas/README.md)** — the machine-readable map of
  what Axeyum can parse, solve, replay, prove, and measure.
- **[Learn](docs/learn/README.md)** — SAT/SMT/proof concepts via tiny examples and
  diagrams, and the [foundational resources](docs/foundational-resources/) query
  packs across algebra, analysis, discrete math, geometry, and dynamics.

---

## What it does today, in code

**Symbolic execution & reachability** are first-class on the warm incremental
engine (`IncrementalBvSolver`): `push`/`pop`/`assume`, **assumption-core path
pruning**, **all-SAT reachable-state enumeration**, and **symbolic memory**. A
`SymbolicExecutor` driver exposes DFS-shaped exploration (`assume` / `branch` /
`enter`+`backtrack` / concrete test-input `model` / `enumerate_inputs` /
`minimize`/`maximize`), with a three-valued `PathStatus` so an undecided path is
never wrongly pruned. On top of these, **bounded model checking** over a
`TransitionSystem` returns replay-checked counterexample traces, and
**k-induction** lifts that to *unbounded* safety proofs — `Safe`, a
counterexample, or an honest `Inconclusive` (never a wrong `Safe`).

**Consumer applications** built on that engine:

- **`axeyum-verify`** — a `#[axeyum::verify]` proc-macro that symbolically
  bounded-checks a Rust function (over a whitelisted subset) for panics / integer
  overflow / `unwrap` failures / assertion violations, emitting a **runnable
  failing `#[test]`** or a re-checked bounded-verified certificate. Anything
  outside the subset is a clean compile error, never silently mis-modeled.
- **`axeyum-evm`** — an EVM bytecode symbolic bug-hunter over symbolic calldata:
  a replayable calldata witness on a bug (re-checked by concrete re-execution),
  or a Lean-checkable no-bug certificate when a function is proven safe to a bound.
- **`axeyum-property`** — a typed prove-or-counterexample SDK over Axeyum evidence
  and model replay.

Everything routes through a few entry points in `axeyum-solver`:

| Call | Purpose |
|---|---|
| `solve` / `solve_smtlib` | decide any supported query (terms or SMT-LIB 2 text) |
| `prove` | prove a goal by a **checkable refutation** of its negation |
| `produce_evidence` | decide *and* package a self-checking certificate |
| `export_qf_{bv,abv,uf,aufbv,lia}_unsat_proof`, `export_datatype_unsat_proof` | emit a `drat-trim`-checkable DIMACS+DRAT certificate |
| `IncrementalBvSolver` | warm push/pop/assume + path-pruning core + all-SAT + symbolic memory |
| `unsat_core` / `Evidence::check` | minimal core; independently re-validate any result |

The incremental solver owns its state, implements `Send`, and uses no shared
global context — one `TermArena` + `IncrementalBvSolver` per worker scans
independent queries in parallel. See the
[Rust embedding guide](docs/user-guide/rust-embedding.md).

## Runs in the browser (WebAssembly)

The default library stack builds for `wasm32-unknown-unknown` and WASI
(ADR-0017): the pure-Rust core has no C/C++ and no native clock dependency (a
`web-time` shim covers wasm targets). `axeyum-cas` and `axeyum-strings` are
WASM-safe by construction. `axeyum-wasm` exposes a tiny JSON surface over the
QF_BV backend so a **static page solves a query client-side** — no server, no
install — and a returned `sat` is already replay-verified: **the trust boundary
is preserved across the WASM boundary**. Try it in the
[playground](docs/playground/README.md).

```sh
cargo build --target wasm32-unknown-unknown -p axeyum-solver
```

## Workspace

The crate split is deliberately minimal — boundaries are added only once proven
by use (each is accepted in an ADR).

**Core IR & solving**

| Crate | Purpose |
|---|---|
| [`axeyum-ir`](crates/axeyum-ir) | Sorts, terms, interning, ground evaluation, LSB-first value/bit conversion. |
| [`axeyum-egraph`](crates/axeyum-egraph) | Incremental congruence-closure e-graph — the shared equality bus with a Nieuwenhuis–Oliveras proof forest and backtrackable trail. |
| [`axeyum-aig`](crates/axeyum-aig) | AIG circuit graph with deterministic structural hashing, evaluation, ASCII AIGER export. |
| [`axeyum-bv`](crates/axeyum-bv) | Term-to-AIG bit lowering with explicit term-bit and symbol-input maps. |
| [`axeyum-cnf`](crates/axeyum-cnf) | Tseitin CNF encoding, DIMACS I/O, BatSat-backed solving, replay maps, and a proof-producing CDCL core with an in-tree DRAT checker. |
| [`axeyum-fp`](crates/axeyum-fp) | IEEE 754 floating-point formula builders (F16–F128 + ML formats). |
| [`axeyum-query`](crates/axeyum-query) | Query object, structural cache keys, conservative slicing, replay checks. |
| [`axeyum-rewrite`](crates/axeyum-rewrite) | Rewrite manifest contracts, denotation-preserving canonicalizer, array elimination (QF_ABV → QF_BV). |
| [`axeyum-strings`](crates/axeyum-strings) | Word-level string/sequence theory (cvc5 normal-form procedure) over the typed IR. |
| [`axeyum-solver`](crates/axeyum-solver) | Backend trait, results, models, capability ledger; `solve`/`prove`/`produce_evidence`; warm incremental engine + symbolic-execution primitives; DRAT exporters; native backends behind feature flags. |

**Higher layers: algebra, proofs, applications**

| Crate | Purpose |
|---|---|
| [`axeyum-cas`](crates/axeyum-cas) | Proof-carrying computer algebra (differentiate/factor/integrate/solve/linear algebra/number theory), certified by lowering to the decidable core. |
| [`axeyum-lean-kernel`](crates/axeyum-lean-kernel) | In-tree Rust Lean kernel — interned `Name`/`Level`/`Expr` + de Bruijn machinery (the proof-export target). |
| [`axeyum-property`](crates/axeyum-property) (+ [`-macros`](crates/axeyum-property-macros)) | Typed prove-or-counterexample SDK over Axeyum evidence and model replay. |
| [`axeyum-verify`](crates/axeyum-verify) (+ [`-macros`](crates/axeyum-verify-macros)) | `#[axeyum::verify]` bounded Rust verifier — panics/overflow/`unwrap`/assertions → failing test or certificate. |
| [`axeyum-evm`](crates/axeyum-evm) | EVM bytecode symbolic bug-hunter with replayable calldata witnesses and no-bug certificates. |
| [`axeyum-wasm`](crates/axeyum-wasm) | WebAssembly binding — the browser playground engine. |

**Tooling & corpora**

| Crate | Purpose |
|---|---|
| [`axeyum-scenarios`](crates/axeyum-scenarios) | Self-checking, oracle-free consumer workloads (SAT by execution, UNSAT by bounded-verified identities). |
| [`axeyum-smtlib`](crates/axeyum-smtlib) | SMT-LIB 2 reader/writer: benchmark ingestion, sharing-preserving export. |
| [`axeyum-bench`](crates/axeyum-bench) | Corpus benchmark harness with PAR-2 scoring, backend selection, JSON artifacts. |

## Start here

- [PLAN.md](PLAN.md) / [STATUS.md](STATUS.md) — master plan + live tracker; the
  single entry point for resuming work.
- [How Axeyum solves a query](docs/learn/07-how-axeyum-solves-a-query.md) — the
  best single page: the pipeline and the untrusted-search / trusted-checking
  boundary, with diagrams.
- [Capability matrix](docs/research/08-planning/capability-matrix.md) and
  [support matrix](docs/research/08-planning/support-matrix.md) — the
  golden-tested inventories (capability × assurance × evidence; per-fragment
  parser/IR/solver/proof status).
- [docs/README.md](docs/README.md) — reader-friendly front door (also builds into
  a searchable mdBook site with Mermaid diagrams).
- [docs/research/](docs/research/README.md) — the research foundation, and
  [09-decisions/](docs/research/09-decisions/README.md), the ADRs.

| You are… | Start here |
|---|---|
| **New to SAT/SMT/proofs** | [docs/learn/](docs/learn/README.md) |
| **A user** | [docs/user-guide/](docs/user-guide/README.md) — run a query, read a model, [limitations](docs/user-guide/limitations.md) |
| **Curious about internals** | [docs/internals/](docs/internals/README.md) — [architecture](docs/internals/architecture.md), trust boundary |
| **Want to try it now** | [docs/playground/](docs/playground/README.md) — solve a query **in your browser** (WASM) |

## Development

```sh
just check          # fmt + clippy + test + doc + foundational resources + docs link check
cargo fmt --all --check
cargo clippy --workspace --all-targets --all-features -- -D warnings
cargo test --workspace --all-features
cargo doc --workspace --all-features --no-deps
cargo build --target wasm32-unknown-unknown -p axeyum-solver   # WASM target (ADR-0017)
cargo deny check                                               # requires cargo-deny

# Benchmarks
cargo run -p axeyum-bench -- corpus/micro --backend sat-bv --timeout-ms 1000 --out /tmp/micro-sat-bv.json
cargo run -p axeyum-bench --features z3 -- corpus/micro --backend z3 --timeout-ms 1000 --out /tmp/micro-z3.json
just bench-public-qfbv-sat-bv-compare     # public QF_BV sat-bv vs Z3 slice
```

The pure-Rust default build has no C or C++ dependency; native solver backends
(Z3 first) are optional features. Reference solver/checker sources can be cloned
locally for study with [`scripts/fetch-references.sh`](scripts/fetch-references.sh).
Local default toolchain may be nightly; CI runs stable plus an MSRV (1.88) check.
Edition 2024, resolver 3.

## License

Dual-licensed under [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE), at your
option. Contributions are accepted under the same terms.
