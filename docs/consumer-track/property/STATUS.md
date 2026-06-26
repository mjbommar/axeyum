# axeyum-property — STATUS

Live tracker for the bounded-property SDK (App B). See [PLAN.md](PLAN.md).

## Current focus

- **2026-06-26 — v1+v2 landed.** The derive macro, `Bounded`, fixed `BvArray`,
  and the counterexample→`#[test]` reproduction layer are implemented and green
  (`cargo test -p axeyum-property -p axeyum-property-derive -p axeyum-consumer-bench`;
  clippy pedantic `-D warnings`, fmt, and `cargo doc -D warnings` clean). New
  public surface:
  - `#[derive(Symbolic)]` (new `axeyum-property-derive` crate, re-exported) for
    structs / tuple-structs of any arity — generates a lifetime-free
    `<Name>Concrete` companion carrying the counterexample (the field
    `Symbolic::Concrete` is referenced through `Symbolic<'static>` so the value
    outlives the `Ctx` borrow). Tuple impls also widened to arity 6.
  - `Bounded<const LO: i128, const HI: i128>` — a range-constrained `Int` that
    auto-emits `LO <= x <= HI` via a new `Ctx` auto-assume channel drained by
    `forall` (no manual precondition). `.value()` / `Deref` expose the `Int`.
  - `BvArray<const EW: u32, const N: usize>` — fixed-length symbolic BV array over
    `Sort::Array` (index width 32): static `get(i)`, symbolic `select(idx)`
    (auto in-bounds guard `idx <u N`), functional `store`; counterexample lifts
    to `[u128; N]`.
  - `reproduce` module — `Witness` trait, `WitnessBinding`, `Reproduction`,
    `render_reproduction_test(..)`; renders a runnable `#[test]` from a
    counterexample. App-agnostic (EVM calldata / verify fn-args both consume it).
  - Scoreboard widened 17→**28 cases**, **DISAGREE = 0**, Lean-cert coverage up
    **8.3% → 25.0%** (5/20 proved) by adding QF_BV comparison theorems in the
    reconstructable conjunct shape (`bv4-{ult,ule,slt}-*`, the derived XOR
    identity).

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

## Next actions (v2 remainder / consumer-side)
1. **Wire the reproduce layer into A/C**: have `axeyum-evm` and `axeyum-verify`
   build a `Witness` over their counterexample and emit a reproduction `#[test]`
   (the SDK piece is done; the per-app glue is theirs).
2. **UF inputs** (`v2`): a typed uninterpreted-function handle (`Sort::Func`)
   over the IR's declared funcs, so a property can range over an abstract `f`.
3. **Richer cert surfacing** (`v2`): expose the proof fragment / theory on
   `Certificate` so the scoreboard can break Lean coverage down by fragment.
4. **Push Lean coverage further**: the LIA/`Bounded` and array `should-prove`
   rows still emit no Lean module (capped by the reconstructable fragment, U1/U4).
   When the upstream reconstructor flattens internally / widens LIA, drop the
   client-side `flatten_conjuncts` dance and re-measure.

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
