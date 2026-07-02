# DRY across MIR & LLVM — the shared reflection core

> **Status:** design (2026-07-02). Two front ends now reflect *real compiled code*
> into `axeyum-ir` terms — MIR (`mir_reflection.rs`) and LLVM IR
> (`llvm_reflection.rs`). They duplicate a real core; this note factors out the
> IR-agnostic part so a property/proof/fuzz harness is written **once** and works
> for either platform, and unlocks a **cross-platform equivalence** proof.

## What's genuinely shared vs. front-end-specific

Both front ends do the same *pipeline* — **parse an IR → build an `axeyum-ir`
term → prove/eval a property** — differing only in the parse step:

| Concern | MIR | LLVM | Shared? |
|---|---|---|---|
| **Parse** (syntax → ops) | `switchInt`/`BinaryOp` statements, `bbN` blocks | SSA `%d = op …`, `phi`, `gep`/`load` | **no** (different syntaxes) |
| **Op vocabulary** (`add`→`bv_add`, `ult`→`bv_ult`, `zext`→`zero_ext`, …) | same target ops | same target ops | **yes** |
| **Operand resolve** (register/const → typed term) | `copy _1` / `const 255_u32` | `%x` / `255` | **yes** (logic identical, token forms differ slightly) |
| **Proof harness** (`prove(goal)` → `Proved`/`Disproved`; `matches!` assertions) | identical | identical | **yes** |
| **Fuzz/eval harness** (`eval` a term over an assignment; sample & compare) | identical | identical | **yes** |

So the parsers stay separate (they must), but the **op vocabulary + proof/eval/fuzz
harness** — the bulk of the non-parse code — is one thing duplicated twice.

## The shared module: `tests/reflect_common/mod.rs`

A single source module both integration-test files include (`mod reflect_common;`
— the idiomatic subdir form, so cargo does not compile it as its own test binary):

- `width_of(ty) -> u32`, `int_ty(tok) -> bool` — the `iN` / `uN` type helpers.
- `binop(arena, op, a, b)` — the op-name → arena BV op map
  (`and/or/xor/add/sub/mul/shl/lshr/ashr`).
- `compare(arena, pred, a, b)` — the predicate → arena compare map.
- `prove_goal(arena, goal) -> ProofOutcome`, `is_proved`, `is_disproved`.
- `eval_bv(arena, term, &assignment) -> u128` — the fuzz/eval reader.

DRY payoff: adding an op (say `udiv`) or fixing a lowering benefits **both**
platforms at once; the proof/fuzz idioms are written once; each new front end (a
future `stable_mir`, or a `.wasm` reflector) targets the same core.

## The payoff: cross-platform equivalence (validate rustc's own lowering)

With one harness, the same *source* function can be reflected from **both** its MIR
and its LLVM IR and **proved equivalent** — a translation-validation of rustc's
MIR→LLVM lowering, and the sharpest demonstration that both land in one term
algebra:

- **`lut`** (`match x {0=>5,1=>7,_=>0}`) — reflects in **both today**: MIR
  `switchInt` and LLVM `icmp`+`select` (measured). Prove `mir_lut(x) == llvm_lut(x)`
  for all `u32`.
- **`masked`** (`(x&0xff)|0x100`) — straight-line `BitAnd`/`BitOr` in MIR,
  `and`/`or` in LLVM. After a small MIR `BinaryOp`-rvalue extension (reusing the
  **shared `binop`** — the DRY point made concrete), prove `mir_masked ==
  llvm_masked` for all `u32`.

## Plan

- Q2: create `reflect_common` (extract the op vocabulary + harness from the LLVM
  reflector); refactor `llvm_reflection.rs` to use it; gates green (all LLVM tests
  unchanged).
- Q3: refactor `mir_reflection.rs` onto the shared harness; extend it with
  straight-line `BinaryOp` rvalues via the shared `binop`; add the cross-platform
  equivalence tests (`lut`, `masked`: MIR ≡ LLVM).
- Q4: gates, scoreboard, plan.

**Honest scope:** the shared module is source-level DRY across integration tests
(each test crate compiles its own copy — fine; it is not a public API). Promoting
the reflectors to a real reusable crate/public surface is a larger, ADR-gated step.