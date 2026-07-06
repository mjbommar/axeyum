# DRY across MIR & LLVM — the shared reflection core

> **Now first-class:** this prototype series (rounds Q–U below) is the basis on
> which the verified-systems trajectory was adopted as **Track 5**
> ([ADR-0056](../../research/09-decisions/adr-0056-verified-systems-track.md),
> 2026-07-06). The productization plan — crate-ifying these reflectors, a full
> `.ll` parser, MIR extraction, contracts, kernel obligations, the fuzz-oracle
> loop, and a measured external target — is
> [`docs/plan/track-5-verified-systems/`](../../plan/track-5-verified-systems/README.md)
> (this file is P5.1's starting inventory). This note remains the running
> design log of the prototype rounds.
>
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

## Round R (2026-07-02): CFG on both sides — the executors

The follow-ups landed, and further:

- **R1 (`1468170e`):** `mir_reflection.rs` migrated onto `reflect_common::mir` —
  one MIR reflector in the tree.
- **R2 (`baa27854`):** `reflect_common::mir` generalized into a **symbolic
  executor over acyclic MIR CFG** — statements in any block, computed `switchInt`
  scrutinees (incl. bool: arm `0` = the false edge), `goto` joins via recursion
  into `ite`, Storage noise skipped, and **sign-aware lowering** from the
  signature (`Shr` on `i32` → `ashr`; MIR `Gt`/`Lt`/… land on the *same* shared
  `compare` map as LLVM `icmp`, sign-selected). The lookup-table and
  straight-line special cases are subsumed and deleted. New proofs: `sel`
  (branch-preserving MIR diamond == LLVM if-converted `select` — **validates
  if-conversion**) and `sar` (signed `Shr` == `ashr`).
- **R3 (`639612ff`):** the LLVM side gets the mirror executor — `br label`
  follows the edge, `br i1` forks a cloned SSA env and joins as `ite`, `phi`
  resolves by the predecessor label threaded through the recursion; `lower_fn`
  dispatches (CFG when the body branches, the fast single-block path otherwise).
  New proofs: `sel` MIR diamond == LLVM `br`+`phi` diamond (CFG walked by *both*
  executors), and LLVM O0 `br`+`phi` == LLVM O2 `select` — translation-validation
  *within* LLVM (the Alive2 use-case shape) on our stack.
- **R4:** `differential_fuzz_mir_vs_llvm_reflections` — 10 000 deterministic
  pseudo-random inputs per fixture pair, bit-for-bit agreement required between
  the two reflections (the DISAGREE=0 discipline applied to the front ends
  themselves, independent of the prover).

Both executors share the acyclic-only scope: a depth cap turns a cyclic CFG into
a loud panic — loops remain the `TransitionSystem` path (already exercised by the
LLVM loop reflector in `llvm_reflection.rs`).

## Round S (2026-07-02): the follow-ups, closed

- **S1 (`b623a21a`):** multi-parameter reflection on both sides
  (`reflect_mir_into` binds `params[i]` → `_{i+1}` with all signature types
  parsed sign-aware; `llvm::reflect_into` zips the define-line decls). Proof:
  two-param `umin(a,b)` — MIR `Lt`-diamond == LLVM's recognized `@llvm.umin`
  intrinsic, all `(u32,u32)`, corners checked against `u128::min`.
- **S2 (`a015f946`):** MIR `as`-casts (`IntToInt`: widen by *source* sign,
  narrow by extract), `UnaryOp` `Not`/`Neg`, and width-adjusted shift amounts
  (Rust types `x << 1`'s literal as `i32`); LLVM signed-printed constants
  (`xor %x, -1`). Proofs: `ext` (cast+shift == `zext`+`shl`), `notx`
  (`Not` == `xor -1`), `negate` (`Neg` == `sub 0,%x`, incl. `i32::MIN`).
- **S3 (`d3759969`):** the **wrong-transform corpus**
  (`cross_ir_refutation.rs`): five classic miscompile shapes — off-by-one
  strength reduction, `lshr`-for-`ashr`, flipped select arms, dropped mask,
  sign-confused compare — all `Disproved`, and each countermodel
  **replay-checked** (both terms evaluated at the model's input must differ).
  The prover is discriminating, not vacuously accepting.
- **S4 (`70f2dce2`):** LLVM `switch` (multi-line terminator, signed-printed
  values, phi-correct per-case edges). Proofs: MIR `switchInt` == LLVM
  `switch`+phi (both dispatchers), and LLVM O0 switch == O2 selects.

**Measured (debug build, single run, 2026-07-02):** `cross_ir_equivalence` —
15 proofs+fuzz in **3.0 s** (incl. the 60k-eval differential fuzz);
`cross_ir_refutation` — 5 refutations+replays in **< 0.01 s**; the whole
`axeyum-verify` crate sweeps green in under a minute. Each individual
equivalence proof is milliseconds-scale at these widths — cheap enough to run
per-commit as ordinary tests.

## Round T (2026-07-03): panic-freedom, a real module, don't-care UB paths

- **T1+T2 (`29cdb05b`):** debug-profile MIR's own safety checks reflect —
  `*WithOverflow` tuple rvalues (sign-selected `bv_uaddo`/`saddo`/…), field
  projections, and the `assert` terminator whose panic edge becomes a Bool
  **panic-condition term** (`reflect_mir_into_checked -> (value, panic)`).
  On top (`checked_reflection.rs`): `inc_guarded` **proved panic-free for all
  u32** + its total value spec; unguarded `inc` refuted with the witness —
  exactly `u32::MAX` — **replayed against the real compiled Rust** via
  `catch_unwind` (panics at the witness, not at witness−1): the fuzzing loop
  (search → crash → repro) discharged symbolically in milliseconds; and
  `panic ∨ (debug-MIR == release-LLVM)` proved — cross-profile
  translation-validation.
- **T3 (`999f4703`):** the checksum **micro-module** (`checksum_module.rs`):
  `sum16` (one's-complement fold) + `cksum_pair = !sum16` from paired MIR/LLVM
  fixtures. Proved for all `(u16,u16)`: per-function MIR == LLVM, the MIR
  inliner's composition (`cksum_pair == ¬sum16`, both platforms), and the
  protocol receiver property `sum16 + cksum_pair == 0xffff` — the network-stack
  verification shape, on reflected compiled code.
- **T4 (`49cbdfe5`):** LLVM `unreachable` = don't-care (Option-valued executor;
  joins drop `None` branches). `lut3` (total MIR match vs enum-invariant LLVM
  with an unreachable default): equal **under the range hypothesis** `x < 3`,
  refuted without it — UB semantics modeled, not ignored.

**Measured (debug, single run, 2026-07-03):** `checked_reflection` 4 proofs in
< 0.01 s; `checksum_module` 4 tests (6 all-input proofs + 2000-pair oracle) in
0.08 s; `cross_ir_equivalence` 16 tests in ~3 s (fuzz-dominated). The whole
`axeyum-verify` crate: 32 test binaries green.

## Round U (2026-07-03): division, memory safety — the checks rustc ships

- **U1+U3 (`f51d24ad`):** checked **division** — the panic that survives
  release mode. Vocabulary: `udiv`/`sdiv`/`urem`/`srem` (MIR `Div`/`Rem`
  sign-select onto them), bool-typed `BitAnd`/`BitOr` (chained check
  conditions), `usize`/`isize`; LLVM side-effect-only `call void` lines skip,
  so a release panic block (`call core::panicking::*; unreachable`) is the
  don't-care path it is. Proofs (`checked_division.rs`): the **exact panic
  specs** — `div` panics iff `b == 0`; `sdiv` panics iff
  `b == 0 ∨ (a == i32::MIN ∧ b == -1)` (two accumulated asserts, captured
  precisely); witnesses replayed on the real fns (division panics in *every*
  profile, so replay is unconditional — and with `b ≠ 0` hypothesized, the
  witness is *forced* to exactly `(i32::MIN, -1)`); conditional cross-IR
  `panic ∨ (mir == release-llvm)`.
- **U2 (`2d29c942`):** **bounds checks over symbolic byte arrays** —
  `Slot::Bytes` reflects `[u8; N]` params one term per element
  (`reflect_mir_params_checked`), `_1[_2]` lowers to an ite table keyed by the
  64-bit index. `get_clamped` (`buf[i & 3]`): the compiled bounds check proved
  **unreachable for every 64-bit index** and every buffer content; unguarded
  `get`: the OOB witness replayed against the real Rust
  (index-out-of-bounds panic under `catch_unwind`); in-bounds values
  cross-checked concretely. The buffer half of the sel4-direction story.

**Measured (debug, single run, 2026-07-03):** `checked_division` 5 proofs in
0.06 s; `checked_bounds` 3 tests (incl. the all-2^64-indices safety proof) in
< 0.01 s.

### Next (follow-ups, not blocking)

- LLVM `getelementptr`+`load` inside the CFG executor (currently only in the
  dedicated straight-line buffer reflectors); an LLVM-side panic-*condition*
  (branch-to-panic-block reachability) to prove debug-LLVM == debug-MIR panic
  behavior, not just treat panic arms as don't-care.
- Function **calls** in MIR fixtures (currently the MIR inliner's output is the
  composition story); a call-aware reflector would prove the inliner itself.
- Array *writes* (`_1[_2] = v`) and pass-through of modified buffers.
- Promotion out of test-module DRY into a real crate is still ADR-gated.

**Honest scope:** the shared module is source-level DRY across integration tests
(each test crate compiles its own copy — fine; it is not a public API). Promoting
the reflectors to a real reusable crate/public surface is a larger, ADR-gated step.