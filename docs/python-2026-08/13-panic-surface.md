# 13 — The panic surface a Python caller can reach, measured and closed

Status: landed, 2026-08-25. Every number here was measured on this date with
`tools/panic_probe.py`; the census it writes is
[`docs/plan/generated/panic-probe.md`](../plan/generated/panic-probe.md).

## The property

A Rust `panic!` inside a `#[pyfunction]` does not become a Python exception.
PyO3 converts it to `pyo3_runtime.PanicException`, and that class derives from
**`BaseException`**, not `Exception`. So the ordinary thing a caller writes —

```python
try:
    arena.real_ratio(1, 0)
except Exception:
    ...
```

— does not catch it. The traceback escapes to the top of the program, and the
message is a Rust internal naming a file the caller has never heard of. A
library that does this is not typed and is not safe to embed.

The property this goal establishes is therefore narrow and checkable:

> Every call into `axeyum._native` either returns a value or raises an
> `Exception` subclass. Never a `BaseException` that is not an `Exception`.

## Measured, before and after

```
BEFORE   PANIC_PROBE|callables=1299|probed=15084|panics=3|segfaults=19
AFTER    PANIC_PROBE|callables=1303|probed=15103|panics=0|segfaults=2
```

| outcome | before | after | meaning |
|---|---:|---:|---|
| `ok` | 2,642 | 2,659 | returned a value |
| `exception` | 12,420 | 12,442 | raised an `Exception` subclass — the contract |
| `panic` | 3 | **0** | `pyo3_runtime.PanicException` |
| `crash` | 19 | 2 | the process died: abort, segfault, or a hang |

The `panics=3` in the BEFORE line was reported by the tool as `base 3`, not
`panic 3`. That was a bug in the probe and it is worth recording, because it is
this repository's standing failure mode one level down: `pyo3_runtime` is not
importable until PyO3 has converted a panic **at least once**, so a probe that
resolved `PanicException` at worker start got `None` and filed every panic under
"some other `BaseException`". The headline total was right and the census was
wrong — the worse of the two, because the census is what a reader believes. The
classifier now tests the type's own `__module__` and `__name__`, which needs no
import and cannot go stale.

## The rule: preflight first, `catch_unwind` only where preflight is impossible

**A preflight names the caller's mistake. A caught panic can only say that
something broke.** So the order is not a style preference:

1. **Preflight.** Check the argument in the binding and raise the specific type
   — `SortError`, `EpochError`, `ValueError`, `OverflowError`, `BudgetExceeded`
   — *before* calling the Rust path that would panic. The caller learns which
   argument was wrong and why.
2. **`catch_unwind` at the specific call site**, converted to `InternalError`,
   only when a preflight is genuinely unavailable. Never a blanket wrapper
   around the module: a panic somewhere nobody has measured must stay loud.
3. **Neither, where the failure is not a panic at all.** A stack overflow and an
   allocation abort kill the process; `catch_unwind` cannot see either. Those
   need a budget, or more stack.

`InternalError` is a subclass of `AxeyumError`, so `except Exception` catches
it, and its message names the Rust site and states that it is a bug in Axeyum
rather than a usage error. It is loud, just not fatal.

## The sites, and what each raises now

| # | site | what it was | fix | now raises |
|---|---|---|---|---|
| 1 | `ir.Arena.real_ratio(n, 0)` | `PanicException` | preflight | `ValueError` |
| 2 | `ir.Assignment.set_real_div_zero((1,0), …)` | `PanicException` | preflight | `ValueError` |
| 3 | `ir.Assignment.set_real_div_zero(…, (1,0))` | `PanicException` | preflight | `ValueError` |
| 4 | `ir.Assignment.set` binding a `Real` symbol to an object whose `denominator` is `0` | `PanicException` | preflight | `SortError` |
| 5 | `ir.fp.from_real(…, num, 0)` | `PanicException` (same root cause; found by reading, not by the probe) | preflight | `ValueError` |
| 6 | `solver.solve` / `check_auto_explained` / `unsat_core` on `(= s1 s2)` over two `String` symbols | `PanicException` | `catch_unwind` | `InternalError` |
| 7 | `kernel.Kernel().build_cpoint_prelude()` | **SIGSEGV** — silent process death | deep-stack thread | returns |
| 8 | `ir.Arena.render` / `ir.Arena.write_script` / `smt.write_script` on a term ~16k deep | **SIGABRT** | depth preflight | `BudgetExceeded` |
| 9 | `cas.Matrix.identity(70000)` / `cas.Matrix.zeros(70000, 70000)` | **SIGABRT** — allocator | shape preflight | `ValueError` |

### 1–5 — `Rational::checked_new` keeps `new`'s `assert!`

One root cause, five call sites, and **the function's name is what hid it**.
`axeyum_ir::Rational::checked_new` is documented as "the overflow-graceful
counterpart of `new`, returning `None` instead of panicking" — and it keeps
`new`'s `assert!(den != 0)` verbatim (`crates/axeyum-ir/src/rational.rs:69`).
It is graceful about `i128` *overflow* only.

`crates/axeyum-py/src/cas/rational.rs` had already found this and shipped a
`checked()` helper that tests `den == 0` first, with a comment saying exactly
why. Four other call sites in the binding had not: they called `checked_new`
directly, and the name told them they were safe. The four now go through the
same helper.

Site 4 is the one worth remembering: `py_to_value` accepts anything exposing
`.numerator` and `.denominator`. `fractions.Fraction` can never present a zero
denominator, so the site looked unreachable — and a five-line duck-typed class
reaches it.

### 6 — the dispatcher, where a preflight is not available

`(= s1 s2)` over two `String` symbols reaches
`axeyum-bv`'s `unreachable!("sequence terms are rejected before bit lowering
(P2.7)")` through the multi-theory dispatcher.

The obvious preflight — refuse sequence sorts, the way `ir.bv.lower_terms`
already refuses them with `first_unsupported_op`/`first_unsupported_sort` — is
**wrong here**, and the measurement says so: `(= (str.len s) 1)` carries a
sequence term over the same sort in the same query and is dispatched to
arithmetic, answering normally. The sort does not decide the outcome; a route
chosen inside Rust does. Refusing every sequence-bearing query would break
queries that work today.

So the panic is caught at that one call, in `dispatch()` in
`crates/axeyum-py/src/solver/core.rs`, and converted to `InternalError` naming
the entry point. `test_string_length_query_is_still_answered` is the control
that keeps the fix from degenerating into a blanket refusal.

`ir.bv.lower_terms` needed nothing: its two preflight guards were already there
and already correct. The gap was in the *other* route into the same lowerer.

### 7 — a public callable that killed the interpreter with no arguments

`kernel.Kernel().build_cpoint_prelude()` overflowed the 8 MB main-thread stack
and took CPython down with **SIGSEGV, silently** — no traceback, no
`PanicException`, nothing an `except` of any kind could see. It is the only one
of the nine `build_*_prelude` methods that does this; the other eight return on
the default stack. Bisected: fails at 8 MB, returns a 106-name prelude at 16 MB.

There is nothing to preflight — the input is the empty kernel — so the fix is a
scoped thread with 64 MB of stack (`on_deep_stack` in
`crates/axeyum-py/src/kernel.rs`). `join()` additionally converts any panic
*inside* that thread into an `Err`, so the site gets typed error handling
without `catch_unwind` and without widening `unsafe_code`.

This is the finding that most argues for measuring rather than reading. It needs
no adversarial input at all: the first line of a tutorial reaches it.

### 8 — the tree-recursive text routines

`axeyum_ir::render` and `axeyum_smtlib::write_script` recurse once per node.
Measured on an 8 MB stack: depth 16,384 renders, depth 32,768 **aborts**
(SIGABRT). `MAX_RECURSIVE_DEPTH = 8_192` sits a factor of two below the last
depth measured safe, and `check_recursion_depth` refuses above it with
`BudgetExceeded` — a budget refusal, because nothing about the term is wrong.

`TermStats::compute` is used to measure the depth and is itself **iterative**
(an explicit worklist), so the guard cannot overflow the stack the routine it
guards would. `ir.eval` needs no guard: it is already iterative and survives
depth 200,000.

### 9 — an allocation the allocator aborts on

`CasMatrix::identity(n)` allocates `n²` rationals with no fallible path.
`cas.Matrix.identity(70000)` asks for 4.9e9 entries and Rust's allocator aborts
the process. `MAX_MATRIX_ENTRIES = 1 << 24` (~268 MB of `Rational`) refuses the
shape first.

## The deep-`CasExpr` chains: fixed by an operator depth guard

`e = e + Expr.int(1)` fifty thousand times builds a `CasExpr` nested 50,000
deep. `Clone`/`Drop`/`normalize` all recurse once per level over the boxed
tree, and past a few thousand levels that overflowed the thread stack and
**aborted the process** (SIGSEGV) -- the last two crashes the probe found.

The fix is the same shape as the term-depth guard, applied one level earlier.
`MAX_EXPR_DEPTH` (1,024, in `cas/expr.rs`) is the deepest single expression the
binding will *build*: every arithmetic operator (`__add__`, `__radd__`, `__sub__`,
`__neg__`, `__mul__`, `__truediv__`, and their reflected forms) and the `Operand`
extractor screen the operand depth with an ITERATIVE walk (`expr_depth`, which
never recurses) and raise `BudgetExceeded` before the recursive `clone()` runs.
Because nothing deeper than the bound can be constructed through the binding,
the recursive Rust routines downstream (`normalize`, `simplify`, `expand`,
`Display`, `Drop`) never receive a chain deep enough to overflow.

The bound is deliberately well below the empirical crash depth (the recursive
CAS routines survive ~2,000 levels and abort near 3,000 on an 8 MB stack), and
far above any realistic expression: a 1,024-deep expression is a chain of a
thousand `+` operations, and a large flat sum is a `MvPoly`, not a tower of
`Add` nodes. Verified by `test_a_deep_expression_chain_is_a_budget_exceeded_not_a_crash`
and by the meta-test, which now runs the two formerly-excluded cases
in-process: `panics=0`, and the two `cas` aborts are gone (the committed
`panic-probe.md` census regenerates them to `segfaults=0` on its next full run).

## Panics that are unreachable by construction

Read from `docs/python-2026-08/inventories/smt-solver.md` §15 and re-checked
against the current binding on 2026-08-25.

| Rust panic site | why a Python caller cannot reach it |
|---|---|
| `axeyum-smtlib::write_script` on a foreign `TermId` | both bound routes call `resolve_terms`, which checks the arena epoch first; `EpochError` is raised instead. `crates/axeyum-py/src/ir/arena.rs` carries the two unit tests that pin epochs as monotone and distinct. |
| `Script::checked_flat_view`'s `debug_assert!` | **not bound**, deliberately. `smt.Script.flat_view` binds `solvable_flat_view`, which answers `None` for the word-first-fallback parse the `checked_` sibling asserts on. |
| `GenericArrayValue::constant`'s `assert!` | `GenericArrayValue` is `#[pyclass(frozen, skip_from_py_object)]` with **no constructor**. Instances only ever arrive from `value_to_py`, built by the Rust side from a value that already satisfies the assertion. |
| `EGraph::ematch_many_candidates_indexed` length assert | `axeyum-egraph` is a dependency of `axeyum-py` but **nothing in `crates/axeyum-py/src/**` references it**; there is no bound entry point. Re-check this row if an e-graph surface is ever added. |
| `axeyum-aig` / `axeyum-cnf` / `axeyum-query` `u32::try_from(…).expect(…)` | these fire above 4.29e9 entries. Reaching one means allocating tens of gigabytes of AIG nodes first, which aborts on allocation long before the conversion. Not practically reachable, and listed rather than claimed closed. |
| `drat.rs:926`, `tseitin_encode_profiled_with_origins` invariant `expect`s | internal invariants over structures the binding builds itself from a lowering it produced; no Python-supplied value crosses into them. |
| `axeyum-ir::eval`'s `expect("builder guaranteed … operand")` family | `Assignment.set` coerces through `py_to_value` **against the symbol's declared sort**, so a value of the wrong shape is refused at bind time with `SortError`. The probe's `mislift-*` battery drives eight wrong-shape bindings through `ir.eval`; all eight are refused. |
| `cas.Expr.rat(n, 0)` (`inventories/cas.md` §0.6) | already guarded before this work, by `cas::rational::checked`. |

A row here is a claim that something is *unreachable*, which is exactly the kind
of claim that rots. Each one is pinned by a probe case, a bound-surface fact
(`skip_from_py_object`, "not bound", "not referenced"), or a preflight with its
own test — never by reading alone.

## How to re-measure

```sh
uv run python tools/panic_probe.py            # print the census
uv run python tools/panic_probe.py --write    # regenerate the committed report
uv run python tools/panic_probe.py --check    # fail if the report is stale
uv run pytest python/tests/test_no_panic_escapes.py -q
uv run pytest python/tests/test_prop_ir.py -q -k no_route
```

The probe runs every case in a subprocess and resumes past a worker that dies,
so an abort is *recorded* rather than ending the measurement — which is the only
reason sites 7, 8 and 9 are in this document at all. Each worker caps its own
address space at 4 GB, so a probe that asks for a 2^70-bit vector fails inside
its own process instead of inviting the host OOM killer to pick a victim.

## The two things this exercise is evidence for

**A doc comment is not a guard.** `Rational::checked_new`'s own doc string says
it panics on a zero denominator, in a `# Panics` section, and four call sites
used it as if it did not. One of them, in this same crate, had a nine-line
comment explaining the trap — and the other four were written anyway.

**A hand-written battery and a generated one find different bugs.** The
adversarial battery in `panic_probe.py` covers every site the inventory names
and found none of the solver-dispatch panic. The Hypothesis property in
`test_prop_ir.py` — random builder against random sort, asserting only "not a
`BaseException`" — found it on its first run. Neither is redundant.
