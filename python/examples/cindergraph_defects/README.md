# Textbook C defects, found by cindergraph + Axeyum and replayed under a sanitizer

Eight small C files, each with the defective function and its fixed twin side
by side. For every function, [cindergraph](https://github.com/mjbommar/cindergraph)
parses the C into a typed AST with declared types and a CFG; `lift.py` walks
that AST with C's own integer semantics and emits one QF_BV query per reachable
sink; `axeyum.smt.solve` (the native Python bindings) answers each query; and a
`sat` model becomes a C `main` that calls the function with exactly those
arguments under AddressSanitizer or UBSan. The sanitizer's report at the
finding's line is the evidence. A witness that does not reproduce is printed as
`DID NOT REPLAY` and fails the run.

```sh
# /tmp is a RAM tmpfs on this fleet; point maturin's wheel output at real disk
export TMPDIR=/data0/axeyum/scratch/py-tmp-$USER && mkdir -p "$TMPDIR"
uv sync --dev
uv run --no-sync maturin develop --release      # builds axeyum._native into .venv
uv pip install "cindergraph @ git+https://github.com/mjbommar/cindergraph.git@main"
.venv/bin/python python/examples/cindergraph_defects/check.py --out /tmp/cindergraph-defects
python3 python/examples/cindergraph_defects/test_lift.py     # the C-semantics rules, stdlib only
```

Exit status is 0 only when every witness replays at its own line and every
`// expect:` line in the samples is met. Queries and harnesses land in `--out`.

`check.py` calls straight into the compiled extension by default. A checkout
that has not built it (or does not want to) can pass `--cli` to shell out to
the `axeyum_cli` example binary instead:

```sh
cargo build --release -p axeyum-bench --example axeyum_cli --features full
.venv/bin/python python/examples/cindergraph_defects/check.py --cli --out /tmp/cindergraph-defects
```

Both routes decide the same queries and produce the same findings — the
switch changes how the verdict and model cross into Python, not what gets
asked of the solver.

## Results, 2026-09-16 (clang 21, `axeyum_cli` at `16087e477`)

| sample | function | finding | where | witness | replay |
|---|---|---|---|---|---|
| 01_length_overflow.c | assemble_bug | buffer | line 20 | `memcpy(dst, src, hdr)` with dst_len=0, src_len=0, hdr=2147483648, body=2147483648 | REPLAYED: AddressSanitizer memcpy-param-overlap (line 20) |
| 01_length_overflow.c | assemble_bug | buffer | line 21 | `memcpy(dst + hdr, src + hdr, body)` with dst_len=65536, src_len=65536, hdr=65536, body=4294901761 | REPLAYED: AddressSanitizer memcpy-param-overlap (line 21) |
| 01_length_overflow.c | assemble_fixed | clean | - | 11 obligations over 3 paths, all unsat | no witness within the model |
| 02_signed_length.c | read_record_bug | buffer | line 16 | `memcpy(dst, src, len)` with len=-1 | REPLAYED: AddressSanitizer negative-size-param (size=-1) (line 16) |
| 02_signed_length.c | read_record_fixed | clean | - | 5 obligations over 2 paths, all unsat | no witness within the model |
| 03_off_by_one.c | lookup_bug | index-negative | line 14 | `table[slot]` with slot=-1 | REPLAYED: AddressSanitizer stack-buffer-underflow (line 14) |
| 03_off_by_one.c | lookup_bug | index-high | line 14 | `table[slot]` with slot=16 | REPLAYED: AddressSanitizer stack-buffer-overflow (line 14) |
| 03_off_by_one.c | lookup_fixed | clean | - | 3 obligations over 2 paths, all unsat | no witness within the model |
| 04_alloc_multiply.c | fill_records_bug | buffer | line 24 | `memcpy(dst + (count - 1) * 16u, src, 16)` with dst_len=0, src_len=0, count=2147483648 | REPLAYED: AddressSanitizer heap-buffer-overflow (line 24) |
| 04_alloc_multiply.c | fill_records_fixed | clean | - | 24 obligations over 5 paths, all unsat | no witness within the model |
| 05_shift_and_divide.c | mask_bug | shift | line 15 | `1u << bits` with bits=-1 | REPLAYED: runtime error: shift exponent -1 is negative (line 15) |
| 05_shift_and_divide.c | mask_fixed | clean | - | 3 obligations over 2 paths, all unsat | no witness within the model |
| 05_shift_and_divide.c | average_bug | divide | line 25 | `total / count` with total=1, count=0 | REPLAYED: runtime error: division by zero (line 25) |
| 05_shift_and_divide.c | average_fixed | clean | - | 3 obligations over 2 paths, all unsat | no witness within the model |
| 06_truncation.c | store_bug | narrowing | line 15 | `unsigned short len = n;` with n=9223372036854775808 | REPLAYED: runtime error: implicit conversion from 'size_t' … to 'unsigned short' changed the value (line 15) |
| 06_truncation.c | store_bug | buffer | line 18 | `memcpy(dst, src, n)` with src_len=65536, n=65536 (dst holds 4096) | REPLAYED: AddressSanitizer heap-buffer-overflow (line 18) |
| 06_truncation.c | store_fixed | clean | - | 9 obligations over 3 paths, all unsat | no witness within the model |
| 07_signed_overflow.c | splice_bug | signed-overflow | line 18 | `offset + len` with offset=1073741824, len=1073741824 | REPLAYED: runtime error: signed integer overflow: 1073741824 + 1073741824 cannot be represented in type 'int' (line 18) |
| 07_signed_overflow.c | splice_bug | buffer | line 20 | `memcpy(dst + offset, src, len)` with dst_len=0, offset=2147450880, len=32769 | REPLAYED: AddressSanitizer SEGV on unknown address (line 20) |
| 07_signed_overflow.c | splice_fixed | clean | - | 14 obligations over 4 paths, all unsat | no witness within the model |
| 08_dead_branch.c | reject_negative | dead-branch | line 14 | `n < 0` true edge is infeasible | proved unreachable |
| 08_dead_branch.c | clamp | dead-branch | line 20 | `v > hi` true edge is infeasible | proved unreachable |

Twelve witnesses, twelve replays at the finding's own line; two branches
proved dead; eight fixed variants with no witness. Witnesses are the smallest
the solver could find (it re-solves under bounds of 1, 16, 256, 4096 and keeps
the first that is still satisfiable), which is why `len=-1` and `slot=16`
appear rather than arbitrary bit patterns; the 2^31 values are witnesses that
cannot be small, because the bug needs the wraparound.

## What each side contributes

**cindergraph** turns tolerant C into something with types and structure: every
binding's declared type (`size_t`, `unsigned short`, `int`), an AST whose
expression nodes are typed by construct (`binary_expr`, `cast_expr`,
`cond_expr`), and a CFG whose back edges say where the loops are. Its spans are
byte offsets; the lifter recovers each operator from the bytes between two
sibling spans.

**Axeyum** decides the query and hands back a model. The lifter's job is to
make the query mean what C means: integer promotion (`unsigned short`
arithmetic happens in `int`), the usual arithmetic conversions (`int` against
`size_t` is an unsigned 64-bit comparison, which is the whole of sample 02),
modular wraparound on unsigned types, `bvsdiv` against `bvudiv`, and
`sign_extend` against `zero_extend` on every widening. Each of those rules is
pinned by a test in `test_lift.py`.

**The sanitizer** is the check on both of them. A model that satisfies the
query but does not reproduce under `-fsanitize=address` or `-fsanitize=undefined`
at the finding's line means the lifter's model of C is wrong somewhere, and the
run says so instead of reporting a finding. Each finding kind is replayed under
the one sanitizer that can observe it, so the report is evidence for that
finding and not for whichever undefined behaviour happens first on the path.

## Sinks and what "clean" means

| kind | the obligation that must hold on every path reaching the sink |
|---|---|
| buffer, buffer-read | `offset >= 0` and `offset + n <= capacity` (128-bit arithmetic, so nothing wraps in the check itself) |
| index-negative, index-high | a signed index is `>= 0`; every index is `< capacity / sizeof(element)` |
| divide | divisor `!= 0`; signed: not `MIN / -1` |
| shift | `0 <= amount < width`; signed `<<`: a non-negative left operand |
| signed-overflow | the mathematical result of `+ - *` on a signed type is representable |
| narrowing | an implicit store into a narrower or differently signed type preserves the value (informational) |
| dead-branch | both edges of an `if` are feasible; an infeasible edge is proved and reported |

A sink's query asserts the path conditions that lead to it, assumes every
earlier obligation whose violation would stop the program (a memory fault, a
division trap) so that execution actually reaches the sink, and negates the
sink's own obligation. It does not assume the earlier obligations the program
survives (a narrowing store, a signed overflow at `-O0`), because the textbook
bugs are exactly the ones where that survived violation defeats a later check:
sample 06's overflow at line 18 needs the truncation at line 15.

**Clean** means every obligation on every path is `unsat` inside this model:
scalar integer parameters, opaque pointers whose capacities are declared by the
`// axeyum: capacity(p) = expr` comment above the function (a parameter name or
a literal; local arrays declare their own), capacities held to at most 65,536
bytes so every witness can be allocated and replayed, no loops (a function with
a back edge in cindergraph's CFG is refused by name), and no calls other than
`memcpy`, `memmove`, `memset`, `strncpy`. Anything outside the subset is
refused with its line and reason. That refusal is a result; a silent
approximation would make "clean" a measurement of the accepted subset.

## Adding a sample

Write the defective function and its fixed twin in one file, annotate pointer
capacities, and add `// expect: <function> finding|clean|refused` lines. Run
`check.py`; a sample whose expectation is not met fails the run. Keep functions
loop-free and scalar; the point of the set is that each file names one mistake
and the fix beside it is what "no witness" looks like.
