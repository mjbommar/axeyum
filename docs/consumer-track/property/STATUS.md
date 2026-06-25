# axeyum-property — STATUS

Live tracker for the bounded-property SDK (App B). See [PLAN.md](PLAN.md).

## Current focus

- **2026-06-25 — v0 landed.** The full v0 SDK is implemented and green
  (`cargo test -p axeyum-property`: 5 integration tests + 2 doc tests + 1
  `compile_fail` width-safety doc test; clippy `-D warnings` and `cargo doc
  -D warnings` clean). Modules: `ctx` (the `Ctx` arena owner), `handle`
  (`Bv<W>`/`Int`/`Bool` typed handles + std operators), `property`
  (`PropertyBuilder`/`Forall`/`Symbolic`/`Outcome`/`Certificate`). Three worked
  examples verified: overflow-safe add (Proved + re-checked cert), `abs ≥ 0`
  over bounded `Int` (Proved), unrestricted 8-bit `a+b ≥ a` (Counterexample,
  asserted to genuinely wrap). A 4th proves a 2-bit comparison theorem that
  **carries a real standalone Lean module**.

## Next actions (v1)
1. `#[derive(Symbolic)]` for structs/tuples beyond arity 3; `Bounded<T,LO,HI>`
   newtype that emits its range `assume` automatically.
2. Counterexample → runnable `#[test]` codegen layer (shared with A/C).
3. The construction-known graduated property corpus + `SCOREBOARD.md`
   (proved-rate, fraction of `Proved` carrying a verified Lean cert, CE-found
   rate; DISAGREE = 0).

## Capability gaps filed (solver-agent notes)
- **`QF_BV` Lean reconstruction is shape-sensitive.** `prove_unsat_to_lean_module`
  reconstructs a `QF_BV` `unsat` only when the contradiction is supplied as
  *separate top-level conjuncts* (e.g. `[a<=b, b<a]`); a single `and(..)` term or
  a `not(not(..))` wrapper is declined (verified empirically). `prove`'s contract
  appends one `not(goal)` assertion, so the SDK works around this **client-side**
  by flattening the `hyps ∧ ¬goal` query into conjuncts (splitting top-level
  `BoolAnd`, stripping `¬¬`) before the best-effort Lean attempt — no core change.
  A solver-side improvement (normalize/flatten inside the reconstructor) would let
  more shapes emit a Lean cert without the client dance. The in-process
  `EvidenceReport` certificate is unaffected and always re-checked.

## Gates / discipline
- `#![forbid(unsafe_code)]`; fmt + clippy `-D warnings` per increment.
- No core edits; consume `axeyum-solver` as a black box.
- DISAGREE = 0 once the SDK corpus/scoreboard exists.

## Changelog
- **2026-06-25** — crate scaffolded; links solver; `cargo check` green. PLAN/STATUS
  written. Next: the typed-handle layer (v0).
- **2026-06-25** — **v0 complete.** Typed handles with type-level BV widths
  (`Bv<32> + Bv<64>` is a compile error, asserted via a `compile_fail` doctest);
  std operators (`+ - * & | ^ << >>`, `Neg`/`Not`) + comparison/overflow methods;
  `property().forall::<T>(&ctx).assuming(..).check(..) -> Outcome<T>`; `Symbolic`
  for `Bv`/`Int`/`Bool` + tuples to arity 3; `Certificate { report, lean }` with
  `verify()` (re-runs `Evidence::check`) and best-effort `to_lean_module()`;
  counterexample lifting via `Model::get` + typed `Value` accessors. All gates
  green. Capability gap on `QF_BV` Lean reconstruction shape-sensitivity filed
  above (worked around client-side).
