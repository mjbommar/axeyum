# ADR-0036: Standalone in-tree Lean kernel crate (`axeyum-lean-kernel`)

Status: accepted

Date: 2026-06-17

## Context

The north star is **Z3 + Lean parity** ([PLAN.md](../../../PLAN.md)): every
`unsat`/`valid` result should carry a machine-checkable proof a **Lean-grade
kernel** accepts, produced by an untrusted search and validated by small
independent checkers. The proof track so far is the *on-ramp*: a trust ledger
(ADR-0031), DRAT/LRAT checkers, and an Alethe emitter cross-checked by the Rust
Carcara checker (P3.1–P3.3). The *destination* (P3.6/P3.7) is an in-tree Rust
**Lean kernel** plus an Alethe→Lean reconstruction, so an axeyum proof can be
re-checked by the same trusted core that underlies Lean/Mathlib — the strongest
possible "trusted small checking" anchor. This track is currently entirely
unstarted; nothing in the workspace represents Lean terms or kernel type-checking.

The plan names `axeyum-lean-kernel` (P3.6) and identifies the reference port
source: `references/nanoda_lib` (a Rust reimplementation of the Lean 4 kernel —
`src/{name,level,expr,tc}.rs`). nanoda is a faithful, compact kernel, but it is
arena-allocated with **lifetime-tagged pointers** (`Level<'a>`, `ExprPtr<'a>`),
which directly conflicts with axeyum's Hard Rule that term handles are
lifetime-free `Copy` IDs and that no arena lifetimes leak into public APIs.

## Decision

Add **`axeyum-lean-kernel`** as a standalone workspace crate — the boundary the
roadmap (P3.6) designates, the same way ADR-0032 accepted `axeyum-egraph` and
ADR-0006 accepted the circuit/lowering crates: a clean, named boundary that the
upcoming Alethe→Lean reconstruction (P3.7) exercises.

It **ports nanoda's kernel *semantics*** — `Name`, universe `Level`
(`Zero`/`Succ`/`Max`/`IMax`/`Param`), `Expr` (de Bruijn `BVar`, `FVar`, `Sort`,
`Const`, `App`, `Lam`, `Pi`, `Let`, literals), de Bruijn operations
(instantiate/abstract/lift), WHNF reduction, and type checking/inference — but
**adapts them to axeyum's idioms**:

- **Lifetime-free `Copy` interned IDs** (a `Vec`-backed interner returning
  `NameId`/`LevelId`/`ExprId`, hash-consed for structural sharing), mirroring
  `axeyum-ir`/`axeyum-egraph`. No `'a` lifetimes in public APIs (Hard Rule).
- `unsafe_code` denied; deterministic (stable interner order, no hash-map
  iteration in output); pure Rust, **no C/C++** (so it stays in the default
  build, unlike depending on `lean4` itself).
- A leaf crate: it depends only on `std` (and at most shared primitives), not on
  the solver — the kernel is a *trusted checker*, independent of the untrusted
  search.

Fidelity to Lean's kernel is a **soundness obligation**, not a convenience: the
entire value is that this core accepts exactly what Lean's kernel does. The port
is therefore staged and tested against nanoda's own test expectations where
possible: (1) data structures + de Bruijn ops [this slice], (2) WHNF + definitional
equality + type checking, (3) the environment/declaration layer, then (4) P3.7
reconstruction (Alethe → Lean proof terms the kernel checks).

## Consequences

- **Positive.** Opens destination 3 (Lean parity), the half of the north star
  with no prior code. Gives the proof track a Lean-grade trusted checker target,
  the natural endpoint above Carcara. Pure-Rust, leaf, no new default-build risk.
  Reuses axeyum's proven interning idiom rather than nanoda's lifetime arena.
- **Negative / cost.** A new trusted codebase whose **correctness is
  soundness-critical** (a wrong type-checker would wrongly accept proofs) — so it
  must be ported faithfully and tested hard, and it is large (multi-slice). Until
  P3.7 lands it is infrastructure with no end-to-end consumer, the same
  foundation-first shape as the e-graph (ADR-0032) and the GF(2) layer.
- **Scope guard.** This ADR authorizes the crate + the kernel *port*; it does not
  yet wire reconstruction into the solver (P3.7) and adds no public solver
  surface. The kernel is built and tested standalone first.

## Alternatives considered

- **Depend on `lean4` directly.** It is C++, violating the no-C/C++ default-build
  rule; and FFI lifetimes would leak. Rejected.
- **Reimplement from the Lean kernel spec, not nanoda.** Slower and more
  error-prone than porting a compact, working Rust kernel. nanoda is the
  reference precisely so the port is faithful.
- **Keep it a module inside an existing crate.** No existing crate is a natural
  home (it is neither IR, solver, nor proof-format); a trusted-checker boundary is
  exactly the kind ADR-0001 admits once named by the roadmap.
