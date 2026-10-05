# Lane: ax-lifter — cindergraph defects lifter: loops, string/malloc/uninit sinks, real inputs (improvement list 2026-09-16 items 10, 11, 12)

<!-- plan-section: lane-status -->

**Done (`ax-lifter`, 2026-09-17).** Three commits on the lane branch, each
verified against the shipped samples before the next.

- **Item 10, MET.** `lift.py` unrolls `for`/`while`/`do` to a stated bound
  (`check.py --unroll K`, default 8; a file's `// axeyum: unroll = N` wins).
  Every normal exit after `k` iterations is a path with the loop condition
  asserted false; `break`/`return` end a path; `continue`/`goto` are refused
  by name. The state needing a `K+1`-th iteration is parked behind a
  `loop-bound` obligation whose `sat` makes the function `bounded: no witness
  within K iterations`, never clean; `// expect: f bounded` pins it. Rows from
  an unrolled function carry `unrolled to K`. A dead branch inside a loop is
  judged over every iteration. Samples `09_loop_off_by_one.c` (`unroll = 17`,
  because `i == n == 16` needs 17 iterations — the brief's default of 8 and
  its `buf[16]` example cannot both hold, and the file's header says so) and
  `10_loop_search.c` (fits the default; the fixed twin is clean, not bounded).
- **Item 11, MET.** `// axeyum: strlen(s) = n` + `strcpy`/`strcat`/`strlen`
  (ASan); `T *p = malloc(size)`/`calloc` with `alloc-size-wrap` via
  `bvuaddo`/`bvumulo` (`-fsanitize=unsigned-integer-overflow`), `NULL`
  tests on an unconstrained address, `free` + `use-after-free` (ASan);
  `uninitialized` reads tracked per path, replayed under `-fsanitize=memory`
  probed by compile-and-run, else valgrind, else `NO RUNTIME ORACLE` counted
  apart (shown with `--cc gcc`). Samples `11_string_and_malloc.c`,
  `12_uninitialized.c`. `SANITIZER_FOR`, the README sink table (now with the
  observing sanitizer column) and `test_lift.py` (14 → 28 tests, each new
  guard mutation-checked to kill exactly its test) updated. Shipped samples:
  33 rows, 18 replayed, 2 dead branches, 13 clean, exit 0 (was 22 / 12 / 2 / 8).
- **Item 12, MET.** `bench-results/cindergraph-defects-real-inputs-20260916/`.
  cindergraph's 25 fixtures, 79 functions: 20 lifted, 59 refused, 9 REPLAYED
  findings on code nobody wrote to be found (`fp_div` by zero,
  `factorial(2^30)` on iteration 7, `isqrt(LONG_MAX)`, INT_MIN corners), 5
  NO RUNTIME ORACLE (decompiler fixtures that do not compile as C), 0 DID NOT
  REPLAY. Glaurung's decompiled C is `tests/fixtures/decompiler_dialects/*.c`
  (7 captured tool outputs, 25 functions): 4 lifted, 21 refused, 5 solver
  findings all without a runtime oracle. Histogram top: pseudo-types 12,
  array parameters without a capacity 10, unmodelled calls 10, non-malloc
  local pointers 8. Two DID NOT REPLAY rows on the first pass were lifter
  bugs and were fixed, not the inputs: a replay must name the finding's kind
  (`REPORT_FOR`) and a sink assumes earlier obligations in its own oracle
  group (`ORACLE_GROUP`); multi-declarator declarations dropped every
  initializer after the first.
- **Coordinator note, done cheaply.** The operator token is taken from
  cindergraph's `op`/`ops` node attribute when present and falls back to the
  gap between sibling spans (tests on synthetic nodes); the lifter's own type
  table stays.

**Next.** From the histogram, in order of cost: a per-dialect type table for
decompiler pseudo-types (12 refusals); `// axeyum: capacity(a) = n * 4`
annotations or a documented convention for array parameters (10 — the row a
buffer finding on real code waits behind); intra-file call summaries (10);
struct members / pointer locals into the frame (10, the memory model). A
finding on decompiler output has no clang oracle by construction; the
evidence would be running the decompiled *binary* under the witness, which is
a Glaurung-side harness.

<!-- plan-section: landed-changes -->

| 2026-09-17 | `3425a51ab` | ax-lifter: the cindergraph-defects pipeline over cindergraph's fixtures and Glaurung's decompiler output with the refusal histogram; replay must name the finding's kind; per-function refusal on a cindergraph diagnostic; multi-declarator declarations (item 12). |
| 2026-09-17 | `8bdccc57b` | ax-lifter: `strcpy`/`strcat`/`strlen` with `// axeyum: strlen`, `malloc`-sized locals with `alloc-size-wrap`, `free`/use-after-free, uninitialised reads under MSan/valgrind/no-oracle; samples 11–12 (item 11). |
| 2026-09-16 | `0afc8ad3d` | ax-lifter: bounded loop unrolling (`--unroll`, `// axeyum: unroll`, `bounded` verdict, `unrolled to K` on every row); samples 09–10; `op` attribute preferred over span gaps (item 10). |
