# LLVM fixture provenance

These files are committed compiler outputs. Tests never invoke clang or rustc,
so CI does not depend on either toolchain. Do not hand-edit a `.ll` fixture;
regenerate it and record the command and compiler identity here.

## ADR-0282 division diamonds

`clang21_div_diamond.ll` was emitted by Ubuntu clang 21.1.8 (6ubuntu1):

```sh
printf '%s\n' \
  'unsigned pick(unsigned x, unsigned y, _Bool c) { if (c) return x / y; return y / x; }' \
  | clang -O1 -S -emit-llvm -x c -o - -
```

`rustc197_div_diamond.ll` was emitted by rustc 1.97.0-nightly
(`f53b654a8 2026-04-30`). The unchecked intrinsic deliberately makes the two
divisions non-speculatable without introducing Rust panic blocks, leaving the
same scalar branch/PHI shape as clang:

```sh
printf '%s\n' \
  '#![feature(core_intrinsics)] #[unsafe(no_mangle)] pub extern "C" fn pick(x:u32,y:u32,c:bool)->u32 { if c { unsafe { core::intrinsics::unchecked_div(x,y) } } else { unsafe { core::intrinsics::unchecked_div(y,x) } } }' \
  | rustc --crate-type=lib -O --emit=llvm-ir -o - -
```

Both committed files pass the installed LLVM assembler before admission:

```sh
llvm-as clang21_div_diamond.ll -o /dev/null
llvm-as rustc197_div_diamond.ll -o /dev/null
```

## ADR-0286 bounded byte memory

`clang21_read_be16.ll` and `clang21_get_masked.ll` were emitted by Ubuntu clang
21.1.8 (6ubuntu1). `-fno-strict-aliasing` keeps non-semantic TBAA attachments
out of the deliberately self-contained function fixtures:

```sh
printf '%s\n' '#include <stdint.h>' \
  'uint16_t read_be16(const uint8_t *p) { return ((uint16_t)p[0] << 8) | p[1]; }' \
  | clang-21 -O1 -fno-strict-aliasing -S -emit-llvm -x c - -o -

printf '%s\n' '#include <stdint.h>' \
  'uint8_t get_masked(const uint8_t *p, uint32_t i) { return p[i & 3]; }' \
  | clang-21 -O1 -fno-strict-aliasing -S -emit-llvm -x c - -o -
```

`clang21_mem2reg_roundtrip.ll` retains the source store followed by its load by
running only LLVM's SSA promotion pass after clang's unoptimized emission:

```sh
printf '%s\n' '#include <stdint.h>' \
  'uint8_t roundtrip(uint8_t *p, uint64_t i, uint8_t v) { p[i] = v; return p[i]; }' \
  | clang-21 -O0 -Xclang -disable-O0-optnone -fno-strict-aliasing \
      -S -emit-llvm -x c - -o - \
  | opt-21 -passes=mem2reg -S -o -
```

All three source modules and their canonical function projections pass LLVM
21.1.8 `llvm-as` in the ADR-0286 test gate.

## ADR-0291 canonical scalar loop

`clang_capsum8.ll` is the exact canonical loop fixture emitted for:

```c
unsigned char capsum8(unsigned char n) {
    unsigned char acc = 0;
    for (unsigned char i = 0; i < n; i++) {
        acc++;
        if (acc > 100) acc = 100;
    }
    return acc;
}
```

The historical capture used clang's canonical-loop controls:

```sh
clang -O1 -fno-unroll-loops -fno-vectorize -S -emit-llvm capsum8.c -o -
```

The committed function retains the compiler's implicit `%1` entry-block slot,
two loop PHIs, `llvm.umin.i8`, `add nuw nsw`, `add nuw`, and the conditional
self/exit edge. Tests consume the file byte-for-byte; do not add a synthetic
entry label.

## ADR-0292 preregistered multi-block natural loop

`clang21_capdiv_natural_loop.ll` is the unmodified complete module emitted by
Ubuntu clang 21.1.8 (6ubuntu1) for:

```c
#include <stdint.h>
uint8_t capdiv(uint8_t n, uint8_t d) {
    uint8_t acc = 0;
    for (uint8_t i = 0; i < n; i++) {
        if ((i & 1) != 0) {
            uint8_t next = (uint8_t)(acc + i / d);
            acc = next > 100 ? 100 : next;
        }
    }
    return acc;
}
```

```sh
clang-21 -O1 -fno-unroll-loops -fno-vectorize -fno-strict-aliasing \
  -S -emit-llvm -x c capdiv.c -o clang21_capdiv_natural_loop.ll
```

The module freezes the next T5.1.4 input before implementation: implicit `%2`
entry identity; header `%6`; conditional division block `%11`; latch `%15`;
latch PHI `%16`; one `%15 -> %6` back-edge; path-sensitive `udiv`; `umin`; and
`add nuw`. It passes `llvm-as-21` unchanged. No multi-block loop semantics are
implemented under the ADR-0292 zero row.
