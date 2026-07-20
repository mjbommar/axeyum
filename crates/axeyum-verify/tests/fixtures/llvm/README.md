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
