# DRY across MIR & LLVM — the shared reflection core

> **Status:** landed (2026-07-02). Two front ends reflect *real compiled code*
> into `axeyum-ir` terms — MIR (`mir_reflection.rs`) and LLVM IR
> (`llvm_reflection.rs`). They duplicated a real core; this note's plan factored
> out the IR-agnostic part so a property/proof/fuzz harness is written **once** and
> works for either platform — and it unlocked a **cross-platform equivalence**
> proof (`cross_ir_equivalence.rs`): the same source function reflected from *both*
> its MIR and its LLVM and proved equal for every input.
>
> Realized surface: `reflect_common/mod.rs` (op vocabulary + proof/eval harness),
> `reflect_common/llvm.rs` (the single-block LLVM reflector), `reflect_common/mir.rs`
> (`reflect_mir_unary`: switchInt + straight-line `BinaryOp`). Gates green:
> cross-IR 3/3, llvm 20/20, mir 5/5, clippy `-D warnings` clean.

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

## Plan — landed

- **Q2 (done, `7b9c9244`):** created `reflect_common` (op vocabulary + proof/eval
  harness, `binop` keyed by *both* LLVM and MIR op spellings); refactored
  `llvm_reflection.rs` onto it — all 20 LLVM tests unchanged and green.
- **Q3 (done, `c659efae`):** moved the LLVM reflector into `reflect_common::llvm`
  (one parser shared by the LLVM suite, the loop/buffer reflectors, and the
  cross-IR suite); added `reflect_common::mir::reflect_mir_unary` handling
  switchInt *and* straight-line `BinaryOp` via the shared `binop`; added
  `cross_ir_equivalence.rs` proving `masked` and `lut` equal across MIR and LLVM,
  plus a negative control (a `|0x200` variant is *refuted* against `|0x100`).
- **Q4 (this note):** gates green (cross-IR 3/3, llvm 20/20, mir 5/5, clippy
  clean); status + plan recorded here.

### Next (follow-ups, not blocking)

- Migrate `mir_reflection.rs`'s own `reflect_mir` onto `reflect_common::mir` so the
  MIR side has a single reflector too (it currently keeps its switchInt-only
  version; the shared one is a superset).
- Grow the cross-IR corpus: multi-statement arithmetic (`add`/`mul`/shifts),
  signed `Shr`→`ashr`, and a `select`/`ite`-bearing function whose MIR keeps the
  branch (not if-converted) — exercising MIR CFG, not just `bb0`.

**Honest scope:** the shared module is source-level DRY across integration tests
(each test crate compiles its own copy — fine; it is not a public API). Promoting
the reflectors to a real reusable crate/public surface is a larger, ADR-gated step.