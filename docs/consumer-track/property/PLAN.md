# axeyum-property — PLAN

> **App B**, the foundation of the [consumer track](../README.md). A typed,
> bounded-property SDK: state a property over bounded ints / bit-vectors, get
> `Proved | Counterexample | Unknown`, where `Proved` carries a re-checked
> certificate (and a standalone Lean module when in the reconstructable fragment).
> Worked backwards from: *the cleanest, most idiomatic Rust way to prove a small
> property and trust the result* — beating raw `z3.rs` ergonomics, adding the
> certificate no competitor surfaces.

## Goal (worked backwards)

A Rust dev writes a property over typed, bounded inputs as a plain closure and
gets a trustworthy verdict in one call — no solver boilerplate, no runtime sort
errors, and a *checkable proof* on success:

```rust
let outcome = property()
    .forall::<(Bv<32>, Bv<32>)>()
    .assuming(|(a, b)| a.ult(Bv::lit(1 << 31)) & b.ult(Bv::lit(1 << 31)))
    .certificate(true)
    .check(|(a, b)| (a + b).uge(*a));        // sum never wraps below a
match outcome {
    Outcome::Proved(cert)        => { cert.verify()?; cert.to_lean_module(); }
    Outcome::Counterexample((a,b)) => panic!("overflow at a={a}, b={b}"),
    Outcome::Unknown(reason)     => eprintln!("undecided: {reason:?}"),
}
```

## Why it's the foundation / lowest effort
No program frontend: the "lowering" is a *typed wrapper* over `axeyum-ir`
`TermArena` builders that already exist and are tested; the decide/cert/model
paths are `evidence::prove` / `produce_evidence` / `prove_unsat_to_lean_module`,
all public and **already re-checked**. A & C reuse this crate's typed-term and
certificate plumbing.

## API surface (target)
- **Typed handles, type-level widths:** `Bv<const W: u32>`, `Int`, `Bool` —
  phantom-typed wrappers over the `Copy` `TermId`. A width mismatch is a *compile*
  error (z3.rs's `BV::new_const("x",32)` is a runtime panic). Std operator traits
  (`+`, `-`, `&`, `|`, `^`, `<<`, …) + methods (`.ult`/`.ule`/`.uge`/`.slt`/…,
  `.wrapping_add`, `.equals` — no `_eq`/`PartialEq` footgun).
- **`Symbolic` trait** = the `Arbitrary` analogue: `fn fresh(&mut Builder) -> Expr`;
  `#[derive(Symbolic)]` for input structs/tuples. `Bounded<T, LO, HI>` newtype emits
  its range `assume` automatically.
- **Entry:** `property() -> PropertyBuilder` (timeout / node_budget / seed /
  certificate(bool)) `.forall::<T>() -> Forall<T>` `.assuming(pre) .check(prop) -> Outcome<T>`.
- **`Outcome<T>`:** `Proved(Box<Certificate>)` | `Counterexample(T)` | `Unknown(UnknownReason)`.
  `Certificate { report: EvidenceReport, lean: Option<LeanModule> }` — `verify()`
  re-runs `Evidence::check`; `to_lean_module()` is **best-effort** (`Option`), never
  a false promise (DOMINANCE.md: BV/UFBV strong, LIA ~25%, LRA ~0%, NRA ~6%).

## axeyum mapping (no solver logic added)
| SDK | axeyum call |
|---|---|
| `forall::<T>()` / `Bv<W>` / `Int` decl | `TermArena::{bv_var, int_var, bool_var}` (auto-unique names) |
| operators | `TermArena::{bv_add, bv_ult, bv_and, eq, ite, int_add, …}` incl. overflow predicates |
| `assuming`+`check` | `prove(arena, &[bounds, pre], goal, &cfg)` — refutes `hyps ∧ ¬goal` |
| `Proved` | `ProofOutcome::Proved(EvidenceReport)` (already re-checked) + `prove_unsat_to_lean_module` |
| `Counterexample(T)` | `ProofOutcome::Disproved(Model)` lifted via `Model::get` + typed `Value` accessors |
| `Unknown` | `ProofOutcome::Unknown` + `SolverConfig` budgets |

## Phases (each compiles, gates fmt+clippy `-D warnings`, has tests)
- **v0 (first):** `Bool + Bv<W> + Int`; builder + `forall`/`assuming`/`check`;
  `Outcome` with scalar BV/Int counterexample lifting; `Proved` carries the
  re-checked `EvidenceReport`; `to_lean_module()` best-effort. A handful of worked
  examples (overflow-safe add, abs≥0, a known-`Counterexample`). Doc tests.
- **v1:** `#[derive(Symbolic)]` for structs/tuples; `Bounded<T,LO,HI>`; the
  `counterexample → runnable #[test]` layer (shared with A/C).
- **v2:** small fixed arrays/slices (`Sort::Array`); UF; richer cert surfacing;
  the per-app SDK scoreboard (construction-known graduated property corpus, no
  oracle) under `docs/consumer-track/property/SCOREBOARD.md`.

## Success criteria (the four, per the track charter)
1. **Clean** — idiomatic typed API, new-crate-only, `#![forbid(unsafe_code)]`.
2. **Functional** — proves/refutes real properties end to end; `Counterexample`
   reconstructs the user's typed input; `Unknown` never lies.
3. **SOTA-measured** — a committed property corpus with construction-known status;
   metric = proved-rate + **fraction of `Proved` carrying a verified Lean cert**
   (the differentiator) + CE-found rate; **DISAGREE = 0**.
4. **Certifying where it can** — `Proved` always re-checks the in-process cert;
   emits a `.lean` module *when in fragment* (honest `Option`).

## Coordination
New-crate-only (`crates/axeyum-property`), built on the `consumer-track` worktree
off committed `axeyum-solver` (stable; never touches the solver agent's in-flight
IR). Capability wishes → [02-research-synthesis §Notes](../02-research-synthesis.md),
filed as notes, never core reach-ins.
