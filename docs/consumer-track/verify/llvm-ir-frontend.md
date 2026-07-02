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

## N — loops: reflect an LLVM loop into a `TransitionSystem`, prove all iterations

The M finding was that true `br`/`phi` multi-block IR appears with **loops**; N
reflects those into the solver's `TransitionSystem` and proves a property for
*every* iteration via **PDR / k-induction** — connecting the LLVM front end to the
same unbounded-safety machinery used for the protocol FSMs.

**Measured `-O` loop hostility (2026-06-30).** LLVM mangles loops aggressively:
`fn count(n){while i<n {i+=1}}` at `-O` → **`ret %n`** (scalar-evolution closed the
loop away); a capped accumulator → **unrolled ×4 + epilogue + `llvm.assume`** (a
preheader/`unroll_iter`/`xtraiter`/epilogue-phi mess). Real `-O` loop IR is not
reflectable by a simple parser.

**The clean canonical form** comes from `clang -O1 -fno-unroll-loops -fno-vectorize`
— the textbook shape a frontend (or `-O` before unrolling) emits. For
`unsigned capsum(unsigned n){ unsigned acc=0; for(unsigned i=0;i<n;i++){ acc++; if(acc>100) acc=100; } return acc; }`
the loop block carries two `phi`s and a clean body:

```llvm
5:                                    ; the loop header/latch (branches back to %5)
  %6  = phi i32 [ %10, %5 ], [ 0, %1 ]     ; i   : 0 on entry, %10 on back-edge
  %7  = phi i32 [ %9,  %5 ], [ 0, %1 ]     ; acc : 0 on entry, %9  on back-edge
  %8  = tail call i32 @llvm.umin.i32(i32 %7, i32 99)
  %9  = add nuw nsw i32 %8, 1              ; acc' = min(acc,99)+1  (caps at 100)
  %10 = add nuw i32 %6, 1                  ; i'   = i+1
  %11 = icmp eq i32 %10, %0
  br i1 %11, label %3, label %5
```

**The reflection scheme (reusing the `lower_rhs` op-lowering):**

- **state vars** = the loop block's `phi` targets (`i`, `acc`) → one BV symbol each.
- **init** = each `phi`'s *entry* incoming value (the pair NOT labelled with the
  loop block): `i=0 ∧ acc=0`.
- **trans** = seed an env mapping each `phi` name → the *pre*-state symbol, lower
  the loop body (`umin`/`add`/…) via `lower_rhs`, then set each post-state symbol
  to the `phi`'s *back-edge* incoming value (`i' = %10 = i+1`, `acc' = %9 =
  umin(acc,99)+1`).
- **bad** = the safety property (the user's spec, not in the IR): here `acc > 100`.

`prove_safety_pdr` / `prove_safety_k_induction` then prove `acc ≤ 100` for **all
iterations** — a property of *real compiled C loop code*, unbounded. (It is even
1-inductive: `acc' = umin(acc,99)+1 ≤ 100` from any `acc`.)

**Honest scope:** canonical single-loop-block form only; real `-O` IR (unrolled,
SCEV-closed, `llvm.assume`, memory) needs a much larger, SCEV-aware parser — the
deferred frontier. Loops with memory or nested control are out. Fixtures are
committed `.ll` (no clang at test time → CI-robust).

**N plan:** N2 reflect `capsum`'s canonical loop → `TransitionSystem`, prove
`acc ≤ 100` via PDR (all iterations); N3 cross-check bounded BMC vs unbounded PDR
+ scoreboard; N4 gates.

## O — memory: reflect buffer reads (the packet-parser primitive)

Packet parsing *is* `load` + `getelementptr` over a byte buffer. Measured
(2026-07-01), a real parser compiles to exactly the tractable shape:

```llvm
; unsigned short read_be16(const unsigned char *p){ return (p[0]<<8)|p[1]; }
define zeroext i16 @read_be16(ptr noundef readonly captures(none) %0) {
  %2 = load i8, ptr %0, align 1
  %3 = zext i8 %2 to i16
  %4 = shl nuw i16 %3, 8
  %5 = getelementptr inbounds nuw i8, ptr %0, i64 1
  %6 = load i8, ptr %5, align 1
  %7 = zext i8 %6 to i16
  %8 = or disjoint i16 %4, %7
  ret i16 %8
}
```

**Bonus measured finding:** clang strength-reduces `(p[0] & 0x0f) * 4` (the IPv4
IHL-in-bytes computation) to `(p[0] << 2) & 60` — so proving the *compiled* form
equivalent to the *obvious spec* form is a genuine mini translation-validation
over real memory-reading code.

**The reflection scheme (partial evaluation of memory):** a `readonly` pointer
parameter to a buffer of known size N becomes **N fresh `BV8` symbols** (the
buffer bytes) plus a *pointer environment* mapping each pointer-typed SSA register
to a constant byte offset from the base:

- the parameter itself → offset 0;
- `getelementptr … i8, ptr %q, i64 K` → `offset(%q) + K` (element type `i8` only —
  byte addressing; other element sizes are out of scope);
- `load i8, ptr %q` → *the byte symbol at `offset(%q)`* (an ordinary value-env
  entry; everything downstream reuses `lower_rhs`).

This is sound and complete for **constant-offset, read-only, `i8` loads** — and
packet headers are fixed-offset by nature, so that scope *is* the header-parsing
idiom. **Honest boundary:** symbolic indices (`p[i]`) need the array theory
(`select` over `Array (BV64) (BV8)`, `eliminate_arrays`) — deferred; stores /
aliasing / wide loads (`load i16`, endianness) — deferred; no bounds model (the
buffer length is the verifier-supplied N).

**O plan:** O2 implement the pointer env + `load`/`gep` handling; prove the
buffer-reading `read_be16` **equivalent to the value-passing `be16`** from M (two
different compiled functions, one reading memory — same function), and the
compiled IHL trick `(p0<<2)&60` **equivalent to the spec** `zext(p0&0x0f)*4`, plus
range properties; fuzz cross-check vs concrete C-semantics oracles. O3 scoreboard;
O4 gates.

## P — symbolic buffer indices: bounds safety at the LLVM level

O handled *constant* offsets; P handles `p[i]` with a **symbolic** index — which
unlocks the real prize: proving **memory-access bounds safety on compiled code**
(the Heartbleed-shaped check, one level below the Rust `#[verify]` version).

Measured (2026-07-01), `unsigned char get(const u8 *p, unsigned i){ return p[i]; }`
compiles to a `getelementptr` with a *register* offset:

```llvm
%3 = zext i32 %1 to i64
%4 = getelementptr inbounds nuw i8, ptr %0, i64 %3   ; offset is a value, not a constant
%5 = load i8, ptr %4
```

and `p[i & 3]` inserts `%3 = and i32 %1, 3` before the `zext` — the masked
(safe) form.

**Reflection scheme (finite ite-table load, stays in QF_BV):** track each pointer
register's offset as a **BV term** (constant `gep` → `off + K`; register `gep` →
`off + reg`, where `reg` is lowered by the existing `zext`/`and`/… handling). A
symbolic `load i8` over a known-size-N buffer becomes an `ite`-table select over
the N byte symbols (`ite(off==0, b0, ite(off==1, b1, …))`) — no array theory
needed for a fixed-size buffer — *and* the load's offset term is recorded so the
safety property can reference it.

**The bounds demo (the point):** the safety spec is *"every load offset is `< N`"*
(the user's spec, not in the IR). Then:

- `get_masked` (`p[i & 3]`, N = 4): `offset = zext(i & 3)` → **`offset < 4` Proved**
  for all `i` — the mask makes the access provably in-bounds.
- `get` (`p[i]`, unguarded, N = 4): `offset = zext(i)` → **`offset < 4` Disproved**,
  with a concrete out-of-bounds `i ≥ 4` countermodel — the Heartbleed-shaped bug on
  real compiled code.

**Honest scope:** finite fixed-size buffer (the ite-table is `O(N)`); still
read-only `i8`, no stores, no bounds *model* beyond the verifier-supplied N; a
genuinely unbounded/symbolic-size buffer is the array-theory route
(`Sort::Array`, `select`, `eliminate_arrays` — all present in the solver) and is
the deferred next step. Fixtures committed (CI-robust).

**P plan:** P2 the symbolic-index reflector (offset-term tracking + ite-table
load) + the in-bounds proof / OOB-witness pair + value fuzz cross-check; P3
scoreboard; P4 gates.

## P — symbolic indices + bounds safety (discharge `inbounds`, don't trust it)

O handled constant offsets. Real parsers also index with *data*:
`p[i]` compiles (measured 2026-07-01) to `zext i32 %i to i64` →
`getelementptr inbounds n
