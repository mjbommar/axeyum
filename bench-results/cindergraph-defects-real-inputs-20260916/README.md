# The cindergraph-defects pipeline over real inputs, 2026-09-16

Item 12 of [the 2026-09-16 improvement list](../../docs/plan/improvement-list-2026-09-16.md):
run `python/examples/cindergraph_defects/check.py` over C that nobody wrote to
be lifted, and report per function whether it was lifted or refused (with the
reason histogram), and every finding with its replay status. The histogram is
the deliverable: on these inputs it says what to build next.

Setup: lifter at the commit that carries this file (items 10 and 11 landed:
loop unrolling to 8, `strcpy`/`strcat`/`strlen`, `malloc`-sized locals,
uninitialised reads, per-function refusal on a cindergraph diagnostic);
cindergraph as installed by the example's quickstart (GitHub `main` at
`ed5e55e`; the fixtures are read from the local clone at `6971e30`,
read-only); Glaurung local clone at `8b02bd4b` (read-only); clang 21.1.8;
default unrolling bound 8; `--timeout-ms 10000`. The raw rows and histograms
are beside this file as `*.results.tsv` / `*.refusals.tsv`.

```sh
.venv/bin/python python/examples/cindergraph_defects/check.py \
  --samples /home/mjbommar/projects/personal/cindergraph/tests --out /tmp/cg      # (a)
.venv/bin/python python/examples/cindergraph_defects/check.py \
  --samples /home/mjbommar/projects/personal/glaurung/tests/fixtures/decompiler_dialects --out /tmp/gl   # (b)
```

Both runs exit 0: no witness failed to replay, and there are no `// expect:`
lines in these files to miss. Exit 0 here means only that — the coverage
numbers below are the result.

## (a) cindergraph's own C fixtures

25 `.c` files under `cindergraph/tests/`: 14 in `decbench_corpus/src/` (small
hand-written functions, one construct family per file), 4 in `fixtures/`
(parser regression inputs), and 7 captured decompiler outputs in
`fixtures/decompiler_dialects/` (the same family as Glaurung's, see (b);
`angr.c` and `retdec.c` are byte-identical copies).

**90 rows over 79 functions plus 4 file-level diagnostic rows: 20 functions
lifted (25 %), 59 refused. Of the lifted: 9 witnesses REPLAYED at their own
line, 5 witnesses with NO RUNTIME ORACLE (all five in decompiler output that
does not compile as C), 0 DID NOT REPLAY, 7 loops `bounded` at 8 iterations,
6 functions clean within the model.** (Counted from
`cindergraph-tests.results.tsv`: a function is lifted if it has any row other
than `refused`.)

### Findings

| file | function | kind | where | witness | replay |
|---|---|---|---|---|---|
| decbench_corpus/src/arith.c | addmul | signed-overflow | line 1 | `a * b` with a=LONG_MIN, b=LONG_MIN | REPLAYED: signed integer overflow: … cannot be represented in type 'long' |
| decbench_corpus/src/arith.c | shifts | shift | line 2 | `x << n` with x=1, n=-1 | REPLAYED: shift exponent -1 is negative |
| decbench_corpus/src/arith.c | signs | signed-overflow | line 3 | `-a` with a=INT_MIN | REPLAYED: negation of -2147483648 cannot be represented in type 'int' |
| decbench_corpus/src/branches.c | classify | signed-overflow | line 1 | `a-b` with a=0, b=INT_MIN | REPLAYED: signed integer overflow: 0 - -2147483648 |
| decbench_corpus/src/branches.c | nested | signed-overflow | line 2 | `-z` with z=INT_MIN | REPLAYED: negation of -2147483648 |
| decbench_corpus/src/fixedpoint.c | fp_div | shift | line 2 | `(long)a<<16` with a=-1 | REPLAYED: left shift of negative value -1 |
| decbench_corpus/src/fixedpoint.c | fp_div | divide | line 2 | `((long)a<<16)/b` with b=0 | REPLAYED: division by zero |
| decbench_corpus/src/fixedpoint.c | isqrt | signed-overflow | line 3 | `x+1` with n=LONG_MAX; unrolled to 8 | REPLAYED: signed integer overflow: 9223372036854775807 + 1 cannot be represented in type 'long' |
| decbench_corpus/src/loops.c | factorial | signed-overflow | line 2 | `f*=n` with n=1073741824; unrolled to 8 | REPLAYED: signed integer overflow: 1152921503533105152 * 1073741822 cannot be represented in type 'long' |
| fixtures/decompiler_dialects/angr.c | bi_reverse | signed-overflow | line 40 | `i -= 1` with a1=INT_MIN; unrolled to 8 | NO RUNTIME ORACLE: the input does not compile as C |
| fixtures/decompiler_dialects/angr.c | bi_reverse | uninitialized | line 43 | `v5` with a0=1, a1=0; unrolled to 8 | NO RUNTIME ORACLE: the input does not compile as C |
| fixtures/decompiler_dialects/ghidra.c | Base::op | signed-overflow | line 151 | `param_1 + 1000` with param_1=2147483136 | NO RUNTIME ORACLE: the input does not compile as C |
| fixtures/decompiler_dialects/ida.c | bi_reverse | signed-overflow | line 43 | `--a2` with a2=INT_MIN; unrolled to 8 | NO RUNTIME ORACLE: the input does not compile as C |
| fixtures/decompiler_dialects/retdec.c | function_401000 | signed-overflow | line 38 | `v2 += v1 & a2` with a1=a2=1610612736; unrolled to 8 | NO RUNTIME ORACLE: the input calls undefined `__asm_cpuid`, `__pseudo_cond_branch` |

The first number worth quoting: **9 replayed findings on code nobody wrote to
be found**, and not all are `INT_MIN` corners — `fp_div` divides by its
parameter unguarded (`b=0`), `factorial(1073741824)` overflows `long` on its
seventh iteration, which the unroller reaches at the default bound, and
`isqrt(LONG_MAX)` overflows in its very first initializer `y=(x+1)/2`. The
`INT_MIN` negations and `0 - INT_MIN` are real undefined behaviour in the
corpus's own functions and UBSan confirms each at its line; they are the kind
of finding a reviewer discounts, and the table says which rows those are.

The five `NO RUNTIME ORACLE` rows are solver findings the pipeline could not
check: captured decompiler output uses `__int64`, `undefined8`, `__m128i`,
`@<ecx>` register annotations and pseudo-calls, so clang cannot compile the
file and there is no program to run. They are counted apart from the replayed
ones and not claimed.

One row was a lifter bug found by this run and fixed before this file was
written: `arith.c shifts` line 2 is `(x << n) | (x >> (32 - n))`, and the
first run "replayed" a signed-overflow witness for `32 - n` (`n = INT_MIN`)
with a *shift* report at the same line — under `-fsanitize=undefined` with no
recovery the bad shift aborts first. Two changes: the replay now requires the
sanitizer's report to name the finding's own kind, not just its line
(`REPORT_FOR` in `check.py`), and a sink's query now assumes every earlier
obligation in the sink's own oracle group holds (`ORACLE_GROUP` in `lift.py`),
so the witness must reach the sink under the oracle that observes it. The
phantom row is gone (signed-overflow 8 → 7 on this corpus before the dialect
rows were unlocked); the shipped samples are unchanged.

### Bounded and clean

| file | function | result |
|---|---|---|
| decbench_corpus/src/checksum.c | crc32_step | clean: 17 obligations over 9 paths, all unsat; unrolled to 8 (the loop is `i < 8`, so the bound is exact and the loop-bound query is unsat) |
| decbench_corpus/src/fixedpoint.c | fp_mul | clean: 2 obligations over 1 path |
| fixtures/initializer_order.c | identity, chain, independent | clean: 0 / 0 / 2 obligations |
| fixtures/sizeof_local.c | scalar | clean: no obligations |
| decbench_corpus/src/loops.c | sum_to, factorial, count_bits | bounded: `i<n` / `n>1` / `x` can still hold after 8 iterations |
| decbench_corpus/src/fixedpoint.c | isqrt | bounded: `y<x` can still hold after 8 iterations (besides the overflow finding above) |
| fixtures/decompiler_dialects/{angr,ida,retdec}.c | bi_reverse, function_401000 | bounded at 8 |

### Refusal histogram (first blocking construct per function, 63 rows)

| n | reason | what it is on these inputs | what would unlock it |
|---|---|---|---|
| 12 | type `…` is not in the scalar subset | `byte`, `undefined8` (×2), `undefined1`, `HRESULT`, `unsigned __int8`, `signed int64_t` (decompiler pseudo-types, 7); `struct pt` (1); `double` (1); `void` locals (2); `sizeof x` without parentheses read as a type name (1) | a per-dialect type table (Ghidra/IDA/r2dec spellings of fixed-width integers) — cheap and unlocks most of the decompiler output; `double` is a different theory |
| 10 | call to `…` is not modelled | calls to other functions in the same file (`fib`, `ackermann`, `identity`, `chain`, `scalar`, `discard`; 6), decompiler pseudo-calls (`sub_8006EC8`, `__asm_cpuid`, `__fprintf_chk`, `__longjmp_chk`; 4) | intra-file call summaries or inlining for non-recursive callees; pseudo-calls stay refused |
| 10 | subscript on `…` without a known capacity | array parameters `int *a` indexed under a `n` parameter (`sum_array`, `max_array`, `reverse`, `bubble`, `bsearch_i`, `matmul`, `fletcher16`, `fsm`, `str_len`, `rect_area`) | an annotation is the honest route (`// axeyum: capacity(a) = n * 4`); a length-parameter heuristic would make "clean" a guess. This is the row a *buffer* finding on real code is waiting behind |
| 8 | local pointer `…`: only `T *p = malloc(...)` is modelled | decompiler locals (`long *v2`, `char *rax`, `void *var_0`) and `int *p = &x` | pointer locals that alias a parameter or a local's address; decompiler stack-slot pointers need the memory model |
| 1 | unknown name `…` | `true` in dewolf output | a literal. (The first run of this corpus had 6 here: five were multi-declarator declarations `int i=0, j=n-1`, of which the lifter read only the first declarator — silently dropping the others' initializers and any obligation in them. Fixed before this file was written; `isqrt`, `chain`, `independent` are lifted above, `reverse` and `bsearch_i` moved to the array-parameter row) |
| 6 | expression form `comma_expr` | `comma_value.c`, the parser fixture for the comma operator | evaluate left to right, keep the right value — small |
| 5 | cindergraph diagnostic (4 outside every exported function, 1 inside) | the dialect files' header comments and the functions the tolerant parser gave up on | upstream (cindergraph); the per-function refusal is what keeps the rest of each file usable |
| 2 | postfix form `member_suffix` | `p->next`, `p->val` in `linkedlist.c` | struct members: a memory model |
| 2 | unary `*` on a pointer | `*a`, `*s++` in `strops.c` | byte reads through a pointer with an annotated capacity — same machinery as `p[i]`, unbuilt |
| 2 | pointer type is opaque | `sizeof(*x)` on a pointer parameter | element type of a pointer parameter is already known to the lifter; `sizeof` does not consult it |
| 1 | statement form `switch_stmt` | `switch_jt.c` | a `switch` is an `if` chain with fall-through; the `break` machinery from loops applies |
| 1 | parameter `int a1@<ecx>` | IDA `__usercall` register annotation | dialect |
| 1 | assignment to unknown `edx` | r2dec register-named variables | dialect |
| 1 | local pointer `**q`: only one level of indirection | `parameter_address.c` | memory model |
| 1 | `++` on unknown `touched` | file-scope static | global environment |

Reading it as a build order: the dialect type table (12 + the register
spellings) is small and would lift most of what is currently refused for a
*spelling* rather than a *construct*; array parameters (10) are one annotation
each and are exactly the functions where a buffer finding would mean
something; user-function calls (10) and struct members (2 + the linked-list
family) are the two real extensions, and they are the same extension the
decompiler output needs.

## (b) Glaurung's decompiled-C output

Glaurung's tree has three things that could be called decompiled C:

- `tests/fixtures/decompiler_dialects/*.c` — seven files of **captured**
  decompiler output (Ghidra 12.1.3, IDA, Binary Ninja, angr, dewolf, RetDec,
  r2dec; each file's header names the tool, the command, and the binary),
  copied verbatim, provenance-marked. This is the input the item asked for
  and the run below is over it.
- `docs/tutorial/_fixtures/*/repl-decomp*.out` — Glaurung's own decompiler
  view (`fn print_sum { var_4 = arg0; … t33 = (t30 < 0); … }`). It is
  Glaurung's IR rendered as pseudo-C, not C: `fn` blocks, untyped temporaries,
  no declarations. cindergraph does not parse it and the pipeline was not run
  on it. Skipped, with that reason.
- `tests/decompiler_fixtures/src/*.c` and `tests/decbench_corpus/src/*.c` —
  the **source** side of Glaurung's decompiler benchmarks (what gets compiled
  and then decompiled), not decompiler output. Out of scope for (b); the
  decbench sources are the same family as cindergraph's `decbench_corpus`
  measured in (a).

**33 rows over 25 functions plus 4 file-level diagnostic rows: 4 functions
lifted (16 %), 21 refused. 5 solver findings (4 signed-overflow, 1
uninitialised read), every one NO RUNTIME ORACLE because captured decompiler
output is not compilable C; 3 loops bounded at 8; 0 clean; 0 replayed.**
(Counted from `glaurung-decompiler-dialects.results.tsv`.)

| file | function | result |
|---|---|---|
| angr.c | bi_reverse | signed-overflow `i -= 1` (a1=INT_MIN) and uninitialized `v5` on the path with a0=1, a1=0 — no oracle; loop bounded at 8 |
| angr.c | usage, history_def_last | refused: local pointer `*v3` / `*v1` |
| angr.c | `<file>` | 3 diagnostics outside every exported function (a header comment the lexer reads as a literal) |
| binja.c | history_def_last | refused: local pointer `* rax` |
| binja.c | usage, handler | refused: calls to `__fprintf_chk`, `__longjmp_chk` |
| binja.c | bi_reverse | refused: cindergraph diagnostic inside the function |
| binja.c | `<file>` | 3 diagnostics outside every exported function |
| dewolf.c | history_def_last, usage | refused: local pointer `* var_0` / `* var_3` |
| dewolf.c | bi_reverse | refused: unknown name `true` |
| ghidra.c | parse_record, _start, switchD_001011b2::caseD_0, FUN_00108540, DllCanUnloadNow | refused: types `byte`, `undefined8`, `undefined8`, `undefined1`, `HRESULT` |
| ghidra.c | Base::op | signed-overflow `param_1 + 1000` (param_1=2147483136) — no oracle |
| ghidra.c | `<file>` | 5 diagnostics outside every exported function |
| ida.c | bi_reverse | signed-overflow `--a2` (a2=INT_MIN) — no oracle; loop bounded at 8 |
| ida.c | history_def_last, dis_func1, raw_hexrays_fastcall, raw_hexrays_usercall | refused: local pointer `*v2`; call to `sub_8006EC8`; type `unsigned __int8`; parameter `int a1@<ecx>` |
| r2dec.c | bi_reverse, usage | refused: type `signed int64_t`; assignment to unknown `edx` |
| r2dec.c | `<file>` | 2 diagnostics (malformed register annotation) |
| retdec.c | function_401000 | signed-overflow `v2 += v1 & a2` — no oracle (calls undefined `__asm_cpuid`); loop bounded at 8 |
| retdec.c | function_401050 | refused: call to `__asm_cpuid` |

Refusal histogram (25 rows): type not in the scalar subset 7; local pointer
not from `malloc` 6; unmodelled call 4; cindergraph diagnostic 5 (4 file-level,
1 in a function); unknown name (`true`) 1; register-annotated parameter 1;
assignment to a register name 1.

What this says: on decompiler output the lifter's *model* is not the first
wall, the *spelling* is — pseudo-types and register names account for 9 of the
21 function refusals and the 5 diagnostics are the same lexical trouble. The
second wall is the memory model (local pointers into the decompiled frame, 6).
And a finding on decompiler output has no runtime oracle by construction:
the C is not compilable, so the evidence would have to come from running the
*binary* the output was decompiled from under the same witness — which is a
Glaurung-side harness, not a clang one. Until that exists, findings on this
input are solver claims and are labelled as such.

## Lifter fixes made because of these inputs (none to the samples)

- Replay requires the sanitizer's report to name the finding's kind, and a
  sink's query assumes earlier obligations in its own oracle group (above).
- A cindergraph diagnostic refuses the function whose span holds it, not the
  whole file; diagnostics outside every exported function are one `<file>`
  row. Before this, 4 of the 7 dialect files were refused whole for a comment
  in their header.
- The harness includes `<stddef.h>`, `<stdint.h>`, `<stdlib.h>`, `<string.h>`
  before the sample and downgrades clang's implicit-declaration and
  int-conversion errors, so a fixture without includes or prototypes still
  compiles; a sample that still does not compile on its own, or links against
  functions nothing defines, is `NO RUNTIME ORACLE` (the input's fault), while
  a sample that compiles wrapped in a `main` that does not is `DID NOT REPLAY`
  (the harness's fault). The distinction is made by compiling the sample alone.
- A pointer parameter with no annotation and no modelled use gets a small
  zeroed block in the harness instead of a `KeyError` (`Base *this`).
- A declaration with several declarators (`long x=n, y=(x+1)/2;`) lifts every
  declarator in order, each initializer after the previous one; before, only
  the first was read, and a dropped initializer's obligation went with it
  (`isqrt`'s overflow is in the second declarator). 3 functions lifted, 1 new
  replayed finding.
