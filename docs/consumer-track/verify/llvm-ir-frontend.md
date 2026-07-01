# Verifying LLVM IR — feasibility & design

> **Status:** feasibility spike + design (2026-06-30). Extends the
> [real-Rust front end](real-rust-frontend.md) *downward*: Rust compiles
> MIR → **LLVM IR** → machine code, and LLVM IR is the **shared target of the
> whole family** (C, C++, Swift, Zig, Julia, Rust-via-LLVM). Reflecting LLVM IR
> is therefore one front end that reaches *many* languages — and most OS /
> network-stack code is C/C++→LLVM, so it is squarely on the seL4-style goal.

## Environment facts (measured 2026-06-30)

- **clang 21.1.8** and **rustc 1.96-nightly** both emit LLVM IR text driverless
  (`clang -O1 -S -emit-llvm`, `rustc -O --emit=llvm-ir`). **No new dependency.**
- **No `llvm-sys` / `inkwell`** in the registry — and we *avoid* them: they link
  the full **C++ LLVM**, against the lean-build rule (worse than the rustc-driver
  concern). The `.ll`-text path is the lean, driverless analog of how the MIR
  prototype used `-Zunpretty=mir`.
- **The convergence is real.** `unsigned clamp(unsigned x){return x>100?100:x;}`
  (C, clang) and `fn clamp(x:u32)->u32{ if x>100 {100} else {x} }` (Rust, rustc)
  compile to *near-identical* IR — both `%r = call i32 @llvm.umin.i32(%x, 100); ret`.
  Same function, two languages, one IR — the basis for "one front end, the whole
  LLVM family."

## Theory fit (excellent — LLVM is already bit-vector-level)

LLVM IR is *closer to axeyum's native fragment than MIR* — no high-level types to
lower first:

| LLVM IR | axeyum |
|---|---|
| `iN` + `add`/`sub`/`mul`/`and`/`or`/`xor`/`shl`/`lshr`/`ashr` | **QF_BV** ops, directly |
| `icmp PRED` | `bvult`/`bvule`/`eq`/… |
| `select i1 c, a, b` | **`ite`** |
| `call @llvm.umin/umax/…` | `ite` over a compare |
| `zext`/`trunc` | zero-extend / extract |
| `load`/`store`/`getelementptr`/`alloca` | **array theory** (`Array (BV addr) (BV i8)`), `eliminate_arrays` (deferred) |
| `fadd`/`fcmp` | **`axeyum-fp`** (IEEE-754 BV, deferred) |
| `br`/`switch` loops | **PDR / k-induction** (SeaHorn's exact recipe) |

Prior art confirms the architecture: **SeaHorn** (LLVM → CHC → PDR/Spacer over
SMT — almost axeyum's stack), **SMACK** (LLVM→Boogie→Z3), **KLEE** / **Crux-LLVM**
(symbolic execution), **Alive2** / **Vellvm** (LLVM semantics).

## The honest boundaries (where soundness is won or lost)

1. **UB / poison / `nsw` / `nuw` — the soundness minefield.** This prototype models
   arithmetic as **total / wrapping** BV. That is *sound* for the unsigned/wrapping
   ops it targets, but it **ignores** `nsw`/`nuw` flags, where LLVM says overflow is
   *poison* (UB). A property that relies on "overflow can't happen" could be
   mismodeled. **Alive2 exists precisely because this is subtle.** Faithful UB
   modeling is deferred and is the bulk of a real LLVM verifier's work.
2. **Memory.** `load`/`store`/`getelementptr`/`alloca` → array theory; expressible
   but a faithful, scalable model (regions, aliasing, provenance) is substantial.
   This prototype targets **`-O` register-SSA** functions (`mem2reg` promotes most
   memory to registers), sidestepping memory — the same lesson as `-O` cleaning up
   MIR's overflow checks.
3. **Control flow.** Single basic block first (`select`-based); `br`/`switch`/`phi`
   CFG is the next increment (transposes from the MIR `switchInt → ite` work).

## The path

| Increment | Reflects | Status |
|---|---|---|
| **L2** | single-block `.ll` SSA: binops / `icmp` / `select` / `umin`/`umax` / `ret` → BV term, proved symbolically | build now |
| **L3** | **the same function from C *and* Rust `.ll`**, proved equivalent through one reflector | build now |
| L4 | gates, scoreboard, plan | — |
| deferred | `br`/`switch`/`phi` CFG; memory (arrays); UB/poison (Alive2-style); the heavy `llvm-sys` path behind an ADR | documented |

Fixtures are *committed* `.ll` (captured once from clang/rustc) — **not** invoked
at test time, so the tests are toolchain-independent (CI-robust), exactly as the
MIR prototype does. The `.ll` text format is far more stable than `-Zunpretty=mir`,
but pin the fixtures regardless.

## Plan

- L2: the single-block `.ll` reflector + symbolic proofs of `masked`/`pick`/`clamp`
  (binops, select, umin), cross-checked by small-width exhaustive eval.
- L3: reflect `clamp` from the **C** `.ll` and the **Rust** `.ll`; prove each
  `<= 100` and prove the two reflected terms **equivalent** — one front end, two
  languages. Benchmark.

## M — the if-conversion finding, and mixed width (measured 2026-06-30)

Probing what `-O` LLVM IR real branchy code produces changed the CFG plan:

- **`-O` if-converts branches to `select`.** `fn classify(x){ if x<10 {1} else if
  x<100 {2} else {3} }` → *nested `icmp`+`select`* (no `br`/`phi`). A `match`
  (`fn day`) → `icmp` + `add` + `select` (the switch vanished into arithmetic).
  So **the L2 single-block reflector already handles if-converted branchy leaf
  functions** — the "multi-block CFG" gap is largely illusory at `-O`. True
  `br`/`switch`/`phi` blocks appear with **loops** (back-edges), which are the
  **PDR / transition-system** path (unbounded, deferred), *not* acyclic reflection.
- **The real gap is mixed width.** `fn be16(hi:u8, lo:u8)->u16{ ((hi as u16)<<8) |
  (lo as u16) }` → `zext i8 %hi to i16`, `shl nuw i16 …`, `zext`, `or`. Packet /
  header code is width-mixed throughout (byte↔word↔dword field packing), so
  `zext`/`sext`/`trunc` are the high-value, network-relevant addition:
  `zext iA→iB` = `zero_ext(B−A, x)`, `sext` = `sign_ext`, `trunc iA→iB` =
  `extract(B−1, 0, x)`.

**M plan:** add `zext`/`sext`/`trunc`; verify a real **byte↔word field round-trip**
(`be16`: extracting the two bytes back from the packed word equals the inputs),
plus `classify` (nested selects → range property) and `day` (match-as-arithmetic
→ bound) — demonstrating the reflector already spans straight-line + if-converted
+ mixed-width leaf functions, the bulk of a protocol parser's per-field code.
