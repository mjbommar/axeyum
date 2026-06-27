# Iteration 2 — research synthesis (2026-06-25)

Three opus research agents scoped the top candidates against the real SOTA tools
and against axeyum's *actual, file-cited* API. **Headline: every candidate is
tractable and not blocked on a missing solver capability.** The frontends are new
crates that consume `axeyum-solver` as a black box.

## Per-app findings (distilled)

### A. EVM bug-hunter — `axeyum-evm` · Leverage 5 / Tractability 4 / Moat 5 / Demand 5
- **Unblocked.** The clean EVM core *is* QF_BV/QF_ABV (axeyum's 88–100% rows).
  Already present: `BV256` (width cap 65536), full BV op set, **native overflow
  predicates** `bv_uaddo/usubo/umulo`, symbolic array memory/storage (ROW +
  Ackermann, no 2²⁵⁶ blowup), `declare_fun` for uninterpreted **keccak**, the
  `SymbolicExecutor` DFS explorer, BMC-with-memory for multi-tx invariants,
  Alethe/Lean evidence.
- **MVP:** raw runtime bytecode + a tiny harness (skip Solidity/Foundry). ~140
  must-have opcodes (arith/logic/stack/concrete-memory/control/calldata/storage).
  **Havoc** keccak/CALL/gas → `PathStatus::Unknown` (sound, never wrong-pruned —
  exactly what halmos/hevm defer). Bug class 1 = overflow / assertion-violation
  (REVERT/INVALID/`Panic(0x11)`) over symbolic calldata.
- **Frontend-only semantics caveats:** EVM `÷/MOD-by-0 = 0` (≠ SMT-LIB all-ones →
  emit `ite` guard), ADDMOD/MULMOD computed at 512-bit, symbolic `EXP` bounded/havoc.
- **Competitor:** hevm (raw-bytecode, CAV'24) primary, halmos secondary. **Moat:**
  Lean/Carcara-checkable "no-bug" proof (incumbents ship **zero** proofs) + pure-Rust
  WASM in-browser (Python/Haskell + external-solver incumbents structurally can't).
  Honest caveat: edge is *trust + delivery*, not out-running Bitwuzla on keccak-heavy.

### B. Bounded-property SDK — `axeyum-property` · Leverage 5 / Tractability 5
- **Lowest-effort clean artifact: no program frontend at all.** The "lowering" is a
  *typed wrapper* over `TermArena` builders that already exist + re-checked.
- **API that beats z3.rs:** phantom **type-level widths** `Bv<const W>` (mismatch =
  *compile* error, not runtime panic), std operator traits over the `Copy` `TermId`
  handle, auto-unique symbol names (no z3 aliasing footgun), `.equals()` (no
  `_eq`/`eq` shadowing). `property().forall::<T>().assuming(pre).check(prop)` →
  `Outcome::{Proved(Certificate), Counterexample(T), Unknown}`. `Symbolic` trait =
  the `Arbitrary` analogue, `#[derive(Symbolic)]` for structs.
- **Exact axeyum mapping:** `check` → `evidence::prove(arena,&hyps,goal,cfg)` which
  refutes `hyps ∧ ¬goal` and **already re-checks the certificate** before returning;
  `Proved` ← `ProofOutcome::Proved(EvidenceReport)` + best-effort
  `prove_unsat_to_lean_module` (returns `Option<String>` — a standalone `.lean`);
  `Counterexample` ← `Disproved(Model)` lifted via `Model::get` + typed `Value`
  accessors; `Unknown` ← budgets in `SolverConfig`. **The SDK adds zero solver logic.**
- **v0:** `Bool + Bv<W> + Int`, scalar counterexample lifting, best-effort Lean cert.
  *The foundation A/C reuse.*

**Status update (2026-06-27):** the first `axeyum-property` crate slice is
committed on `main`. It provides typed `Bool`, `Bv<W>`, and `Int` handles,
assumptions, proof and minimized-counterexample calls over the existing
evidence APIs, typed scalar model lifting, and unsigned BV overflow helper
predicates. Remaining v0 polish is ergonomic syntax/operator traits, nested or
frontend-specific counterexample replay bodies, and best-effort Lean-module
packaging in the SDK certificate surface.

**Status update (2026-06-27, follow-up):** native scalar counterexample-to-test
rendering is now in the crate. Disproving models become deterministic
`Counterexample` bindings over declared SDK inputs and can render Bool, Int, and
BV<=128 values as Rust let-bindings or a `#[test]` skeleton. Structured/domain
replay remains caller/frontend-owned.

**Status update (2026-06-27, structured replay slice):** direct symbolic
bundles now render Rust aggregate initializer statements:
`render_rust_named_struct_let` for direct named fields and
`render_rust_tuple_struct_let` for contiguous tuple fields. Nested/domain replay
still remains caller/frontend-owned.

**Status update (2026-06-27, Symbolic slice):** the macro-free `Symbolic` trait
now covers scalar Bool/unsigned-BV/Int-backed inputs and 2-/3-tuples. This gives
frontends deterministic declaration and concrete model lifting; follow-up slices
add named fields and derive support.

**Status update (2026-06-27, named-field slice):** `Property::symbolic_struct`
now gives frontends macro-free struct-shaped inputs with stable field names such
as `transfer.amount`; the derive macro now lowers to the same builder.

**Status update (2026-06-27, derive slice):**
`#[derive(axeyum_property::Symbolic)]` now supports named, tuple, and unit
structs over the same builder, including concrete model lifting for the derived
Rust input type.

**Status update (2026-06-27, signed scalar slice):** `i8`/`i16`/`i32`/`i64`
now implement `Symbolic` as two's-complement BV terms with signed model lifting
and signed Rust counterexample literals; `i128` remains mathematical Int.

**Status update (2026-06-27, signed minimization slice):**
`Property::prove_minimized` now passes signed two's-complement objective
metadata for signed symbolic BV inputs through the solver's
`prove_minimized_with_objectives` path, so minimized counterexamples preserve
Rust signed integer intent instead of falling back to unsigned BV order.

**Status update (2026-06-27, measurement slice):** the first committed
graduated SDK corpus, generated `property/SCOREBOARD.md`, and machine-readable
`property/corpus.json` are in place. The gate covers seven workflows (BV proof +
Lean-required certificate, Int assumption proof, unsigned minimized witness,
signed minimized witness, struct-shaped witness, overflow witness, and derived
struct lifting) with 2 proved, 5 disproved, 0 unknown, DISAGREE=0, and 1/1
Lean-required coverage. External proptest/Kani-style comparison remains the
next measurement step.

### C. Rust verifier — `axeyum-verify` · Leverage 4 / Tractability 3 (proc-macro) / Moat 5 / Demand 5
- **Lowest-effort path is a `#[axeyum::verify]` `syn` proc-macro over a restricted
  surface (NOT MIR).** `crates/axeyum-solver/tests/symbolic_execution.rs` is already
  a working symbolic executor for a register VM — the MVP is "swap the toy ISA for a
  small Rust-surface AST + add overflow/`unwrap`/assert/panic checks." Days, not months.
- **Subset:** integer/bool params+locals (`uN/iN`→`Bv<N>`, `bool`→`Bool`),
  arith/bitwise/cmp/`if`/`match`-on-int, `assert!`, `#[unwind(K)]`-bounded loops,
  fixed arrays/slices via `Sort::Array`. Defers heap/traits/closures/floats (same way
  Verus/Flux scope by fragment).
- **Caveat:** BV div is SMT-LIB-total (÷0 = all-ones) ≠ Rust panic → emit explicit
  `÷0` check. Overflow = frontend-built widened-compare miter (a reusable
  `bv_*_overflows` helper would serve A too — *note for solver agent*).
- **Competitor:** Kani (bounded/MIR, same property classes), corpus = Kani's own
  `tests/`. **Moat:** real vs Kani (pure-Rust + WASM + certifying, Kani emits no
  checkable proof); vs Verus/Creusot it's "**no-annotation + single-stack cert**,"
  *not* "proves more." Self-hosting = long-horizon (demo one `axeyum-bv` leaf first).
- MIR (`stable-mir-json`) is the phase-3 coverage upgrade, not the start.

### D. Measurement / QA backbone — shared infra · Leverage 5 / Tractability 4
- **Per-app corpora, NOT SV-COMP** (SV-COMP is C/reachability — off-mission). EVM →
  SWC registry + halmos examples; Rust → Kani `tests/`; SDK → a construction-known
  graduated property corpus (no oracle needed, the `measure_graduated.rs` trick).
- **Harness:** generalize `measure_corpus.rs` — axeyum vs an arbitrary shelled SOTA
  binary, emitting `DISAGREE` (asserted 0) / PAR-2 / `evidence_certified` /
  `lean_checked` / `trust_holes` JSON (exactly what `audit_dominance` already emits) →
  a committed per-app `SCOREBOARD.md`.
- **Outward differential bug-hunter:** random instances, **axeyum (cert-backed) vs a
  fast-but-unproven tool**; a disagreement where axeyum carries a re-checked cert =
  a bug *in the other tool/model*. Generalizes the five existing differential fuzzes.
- **D is the gating discipline:** every app commits a scoreboard + a DISAGREE=0 gate
  before claiming any "vs SOTA" number.

## Cross-cutting layers (E) — build once, reuse
- **Counterexample → runnable `#[test]`** (reused by A and C).
- **WASM delivery** — wrap B/A in the existing playground (client-side).

## Notes filed for the solver agent (capability requests, none blocking)
These are *requests as notes* — the consumer track does **not** reach into the core:
1. **`bv_*_overflows(a,b,width) -> TermId` reusable helper** (frontend currently
   builds the widened-compare miter; reused by EVM + Rust verifier). *Low.*
   **Answered for SDK consumers:** `Bv<W>::{uadd,usub,umul}_overflows` now
   exposes the existing IR predicates through `axeyum-property`; the core
   `bvumulo` builder also avoids doubled-width multiplication terms.
2. **First-class minimal-failing-input (counterexample shrinking)** — SDK can do it
   client-side via `SymbolicExecutor`/`minimize_*`, but a core helper would be clean.
   **Answered for scalar SDK inputs:** `prove_minimized` plus
   `axeyum-property::Property::prove_minimized` return replay-checked minimized
   countermodels over declared Bool/BV<=127/Int variables.
3. **Lean-cert coverage is honest, not universal** (DOMINANCE.md: BV/UFBV strong;
   QF_LIA ~25%, QF_LRA ~0%, QF_NRA ~6%). All apps must surface
   `Proved { lean: Option<..> }` — cert verified in-process always, external `.lean`
   *when in fragment* — never promise a `.lean` for every Proved.
