# Decision Records

Status: draft
Last updated: 2026-06-11

## Purpose

The research-questions register says every open question should resolve into
"an ADR, benchmark, implementation result, or explicit deferral" — this
directory is where those resolutions live. Research notes describe the option
space; decision records close questions.

## Process

- One file per decision: `adr-NNNN-short-slug.md`, numbered sequentially.
- Status is one of: `proposed`, `accepted`, `superseded by adr-NNNN`,
  `deferred`.
- Each ADR links the research-questions entries it closes; the closed
  question in `08-planning/research-questions.md` gets a link back.
- ADRs are immutable once accepted; reversals get a new ADR that supersedes
  the old one.

## Template

```markdown
# ADR-NNNN: Title

Status: proposed | accepted | superseded by adr-NNNN | deferred
Date: YYYY-MM-DD

## Context

What question this closes and why it must be decided now.
Link the research notes and register entries involved.

## Decision

The decision, stated as a single committed sentence, then detail.

## Evidence

Benchmarks, prototypes, references, or reasoning that justified it.

## Alternatives

What was rejected and why.

## Consequences

What becomes easier, what becomes harder, what gets revisited and when.
```

## Index

| ADR | Title | Status |
|---|---|---|
| [0001](adr-0001-vertical-slice-first.md) | Vertical slice before horizontal layers | accepted |
| [0002](adr-0002-ground-up-identity-oracle-bootstrap.md) | Ground-up identity, oracle as bootstrap scaffolding | accepted |
| [0003](adr-0003-m0-ir-representation.md) | M0 IR representation choices | accepted |
| [0004](adr-0004-defer-second-native-backend.md) | Defer the second native backend | accepted |
| [0005](adr-0005-phase3-query-evidence-rewrite-contracts.md) | Phase 3 query, evidence, and rewrite contracts | accepted |
| [0006](adr-0006-phase4-bit-order-and-lowering-entry-contract.md) | Phase 4 bit order and lowering entry contract | accepted |
| [0007](adr-0007-first-pure-rust-sat-adapter.md) | First pure Rust SAT adapter | accepted |
| [0008](adr-0008-consumer-scenario-models.md) | Consumer scenario models for testing and optimization | accepted |
| [0009](adr-0009-incremental-sat-and-solving.md) | Incremental SAT and incremental solving | accepted |
| [0010](adr-0010-arrays-via-eager-elimination.md) | Arrays (QF_ABV) via eager elimination to QF_BV | accepted |
| [0011](adr-0011-drat-unsat-proof-checking.md) | DRAT UNSAT proof format with an in-tree checker | accepted |
| [0012](adr-0012-proof-producing-sat-core.md) | First proof-producing pure-Rust SAT core | accepted |
| [0013](adr-0013-uninterpreted-functions.md) | Uninterpreted functions (EUF) via Ackermann reduction | accepted |
| [0014](adr-0014-first-arithmetic-fragment.md) | First arithmetic fragment: linear integer arithmetic, bit-blasted | accepted |
| [0015](adr-0015-linear-real-arithmetic.md) | Linear real arithmetic via exact-rational simplex | accepted |
| [0016](adr-0016-quantifiers-binder-representation.md) | Quantifiers: named binders and finite-domain semantics | accepted |
| [0017](adr-0017-wasm-target-support.md) | WebAssembly as a supported target (browser + WASI) | accepted |
| [0018](adr-0018-smtlib-text-front-door.md) | SMT-LIB text front door (`solve_smtlib`) in the solver crate | accepted |
| [0019](adr-0019-swappable-solving-strategies.md) | Swappable solving strategies (high-memory eager vs low-memory oracle) | accepted |
| [0020](adr-0020-unbounded-lia-branch-and-bound.md) | Unbounded QF_LIA via branch-and-bound over the simplex | accepted |
| [0021](adr-0021-boolean-structured-lia-dpll.md) | Boolean-structured QF_LIA via lazy-SMT over the integer simplex | accepted |
| [0022](adr-0022-first-class-datatype-sort.md) | First-class datatype sort in the IR (recursive datatypes) | accepted |
| [0023](adr-0023-floating-point-bv-lowering.md) | Floating-point (IEEE 754) as bit-vector formula builders, non-arithmetic core first | accepted |
| [0024](adr-0024-nra-linear-abstraction.md) | Nonlinear real arithmetic via linear abstraction + replay (sound, incomplete) | accepted |
| [0025](adr-0025-bounded-strings-bv-lowering.md) | Bounded-length strings by bit-vector lowering (BMC fragment) | accepted |
| [0026](adr-0026-first-class-float-sort.md) | First-class floating-point sort in the IR (disambiguates FP conversions) | accepted |
| [0027](adr-0027-milp-branch-and-bound.md) | Mixed integer/real arithmetic by branch-and-bound over the Farkas-checked LRA engine | accepted |
| [0028](adr-0028-fp-arithmetic-validation-oracle.md) | A software-float oracle (`rustc_apfloat`) for validating wide-format FP arithmetic | accepted |
