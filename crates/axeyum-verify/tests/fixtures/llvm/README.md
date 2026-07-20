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
