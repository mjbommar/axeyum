# Python bindings

`axeyum` is importable from Python through `axeyum._native`, a PyO3 extension
built from [`crates/axeyum-py`](../../crates/axeyum-py). The default build stays
free of C and C++ (ADR-0002): the extension links no `libpython` and the solver
is the same pure-Rust stack the Rust API uses.

**The Python surface is a projection of the Rust API.** Nothing exists here that
does not exist in Rust, and no Python call can admit a fact, write a ledger,
relax a checker, or change an axiom footprint. Two hard rules cross the language
boundary verbatim: `unknown` and `declined` are **values, never exceptions**,
and every `sat` is checkable — `Outcome.replay()` runs the Rust model check.

## Install

Requires Python 3.12+ and [`uv`](https://docs.astral.sh/uv/). The wheel is
`abi3-py312`, so one build serves 3.12, 3.13 and 3.14.

```sh
uv sync --dev                     # venv + maturin, pytest, ruff
uv run --no-sync maturin develop  # build the extension into that venv
uv run --no-sync python -c "import axeyum; print(axeyum.__version__)"
```

`uv sync --dev` is the one-time setup; every command after it uses `--no-sync`
so that running a gate cannot silently mutate `uv.lock` or the venv.

### `TMPDIR` must not be `/tmp` on this fleet

`maturin develop` writes a wheel to `TMPDIR` on **every** rebuild. `/tmp` on
these hosts is a 62 GB RAM-backed tmpfs that has already been a standing
contributor to OOM kills. Point it at real disk before building:

```sh
export TMPDIR=/data0/axeyum/scratch/py-tmp-$USER && mkdir -p "$TMPDIR"
```

`just py-check` does this for you when `TMPDIR` is unset.

## Trust tiers

Submodule = trust tier, and the tier is the point of the split:

| tier | meaning |
|---|---|
| `R` | read / pure — inspection and construction, no search, no writes |
| `P` | propose — **untrusted search**; a proposal is a claim, not a result |
| `C` | check / replay — falsifiable, and exposes counts rather than a bare `bool` |

| module | tier | wraps |
|---|---|---|
| `axeyum.smt` | R + C | `solve_smtlib`, value/assignment readout, `Outcome.replay()` |
| `axeyum.solver` | R + C | solver limits, incremental push/pop/assume, proof and certificate export, `check_drat` |
| `axeyum.ir` | R | sorts, terms over a Python-owned arena, values, the evaluator |
| `axeyum.cas` | R | `Expr`, polynomials, rationals, normalize/simplify/evalf/differentiate/integrate/factor |
| `axeyum.cas.certify` | P + C | geometry, telescoping, SOS, GF(2), Gröbner cofactors — `produce()` / `Certificate.check()` pairs |
| `axeyum.kernel` | R + C | `Kernel`, declarations, prelude construction, axiom footprints and closures, Lean rendering |
| `axeyum.producers` | P | statement import, bounded-induction and mod-equation proposals, circularity audit, `verify_*` receipts |
| `axeyum.knowledge` | R | facts, frontier, operations, overlay, nursery, claims, foundational concepts — **read-only by construction** |
| `axeyum.evidence` | R | canonical JSON, `sha256`, receipt/certificate serialization |

That table is the *target* surface, from
[`docs/python-2026-08/02-python-api.md`](../python-2026-08/02-python-api.md).
The submodules are registered today; they are filled slice by slice, and the
generated stubs below are the honest inventory of what is callable **right
now** — an empty `.pyi` means the submodule exists and is not populated yet.

## Type stubs

A compiled `.so` is opaque to every type checker, so the stub package under
`python/axeyum/_native/` supplies the surface. It is **generated from the Rust
signatures** and must never be hand-edited:

```sh
uv run --no-sync maturin develop            # rebuild the extension
cargo run -p axeyum-py --features stub-gen --bin stub_gen
```

The stubs are typed. `smt.solve` is
`(script: str, *, timeout_ms: int = 10000, …) -> Outcome`, `Outcome.replay()` is
`-> bool`, `cas.factor(expr: Expr, var: str) -> Expr | None`,
`Kernel.axiom_footprint(name: str | NameId) -> list[str]`, and every exact
rational comes back as a `fractions.Fraction`. Measured 2026-08-24: **1,196 of
1,234 parameters carry a real type (96.9%)**, against 9 before.

The 52 that are still `typing.Any` are each listed with a reason in
[`python/axeyum/_native/ANY_ALLOWLIST.txt`](../../python/axeyum/_native/ANY_ALLOWLIST.txt).
They are not a to-do list. `Assignment.get()` returns a value whose Python type
is decided by the term's **sort** at run time, `__eq__` takes any object, and
`Lit.value` is an `int` or a `str` depending on `.kind`. The rule is the one in
`docs/python-2026-08/10-quality-best-practices.md`: a stub type that cannot be
derived stays `Any` and is listed, because a **wrong** type is worse than none.

It is a *package* — `_native/cas/__init__.pyi`, `_native/cas/certify/sos/__init__.pyi`,
one directory per submodule — because a flat `_native/cas.pyi` is a module and
so cannot have a `certify` member. That was a real defect: `axeyum._native.cas.certify`
and `axeyum._native.kernel.identity` exist at run time and were unresolved
imports to a type checker.

Three gates keep the stubs honest, and they check different things:

| gate | what it compares |
|---|---|
| `tools/gen_native_stub.py --check` | the built `.so` against the stubs — names, parameter names, arity. Annotations ignored. |
| `tools/check_stub_types.py` | every `typing.Any` against the committed allowlist; a listed site that stops being `Any` must be removed, so the count only falls |
| `python -m mypy.stubtest axeyum._native` | the stubs against the runtime **as types** — the only one that can see a stub claiming `-> int` for something that returns `str` |

`python/tests/test_native_stub_current.py` and
`python/tests/test_stub_types.py` run the first two in the suite, each with a
negative control that must fail when a guard is deleted.

## The gate

```sh
just py-check
```

Ten steps: `maturin develop`, `pytest python/tests -q`, the stub name/arity
drift check, the stub type ratchet, `stubtest`, `ty`, `ruff check`,
`ruff format --check`, then the C-defect example's controls and the C-defect
gate itself (`scripts/check-cindergraph-defects.sh`, below). **Read the
counts, not the exit status** — each prints one:

```
PYTEST|collected=N
STUBS|modules=M|symbols=S|aliases=A|synthesised_dunders=D
STUB_TYPES|params=P|typed=T|any=A|allowlisted=L|return_any=R
TYPES|target=python/axeyum|diagnostics=N|budget=B|control=C
CINDERGRAPH_DEFECTS|rows=N|replayed=N|dead=N|clean=N|bounded=N|no_oracle=N|failures=N|PASS
```

The last one is the example under
[`python/examples/cindergraph_defects/`](../../python/examples/cindergraph_defects/README.md)
run as a gate: twelve C samples through [cindergraph](https://github.com/mjbommar/cindergraph)
— installed by `uv sync --dev` at the commit `pyproject.toml`'s dev group pins,
and the run's first line says which commit it ran (`cindergraph|version=…|commit=…|pinned=…|match=yes`)
— into QF_BV, every `sat` witness replayed under a sanitizer. The gate does
not trust the driver's exit status: `scripts/check-cindergraph-defects.py`
re-reads `results.tsv` and asserts that every function has an `// expect:`
line and meets it, that the clean/finding counts equal the counts of those
lines, that no witness `DID NOT REPLAY`, that every replayed witness replayed
at **its own** line, that the driver's own control (the first harness judged
at the line after its finding) was refused, and that the cindergraph that ran
is the pinned one. It **refuses** (exit 2) when `axeyum._native` or
`cindergraph` is not importable, and **skips** loudly — `CINDERGRAPH_DEFECTS|SKIPPED|reason=…`,
never `PASS` — on a host without `clang` (`AXEYUM_REQUIRE_CINDERGRAPH_DEFECTS=1`
makes that a failure). Its three subject mutations — a sample's bounds check
deleted, the lifter's `int`-against-`size_t` rule broken, `replay()` saying
yes to everything — each kill exactly one test of
`scripts/tests/test_check_cindergraph_defects.py`
(`python3 scripts/tests/mutation_controls.py cindergraph-defects`).

Both fail on zero. A pytest run that collects nothing exits 5 and prints "no
tests ran", and a drift check pointed at an empty directory would otherwise
report "nothing differed" and exit 0; those are the inert-gate shape this
repository has been bitten by repeatedly, so `python/tests/conftest.py` fails a
session that collected zero tests, `gen_native_stub.py --check` exits 1 when it
compared zero symbols, `check_stub_types.py` exits 1 when it read zero stub
files, and `check_types.py` exits 1 when its positive control produced no
diagnostic.

`scripts/check.sh` runs the same steps only when `uv` **and** a synced `.venv`
are both present, and otherwise prints `py-check: SKIPPED (no uv)` — skipped,
never passed. Which hosts have `uv` is recorded in
[fleet hosts](../contributor-guide/fleet-hosts.md).

## Mathematica-shaped verbs: `axeyum.m`

```python
from axeyum import m
m.Simplify("x*x + 5*x + 6")                 # x^2 + 5*x + 6
m.show(m.Factor("x^2 + 5 x + 6"))           # (x + 2)*(x + 3)
m.Solve("2x + 3 = 7")                       # [Expr("2")]
m.Solve(["x + y = 3", "x - y = 1"], ["x", "y"])   # [{'x': 2, 'y': 1}]
m.D("x^3 + 2 x"); m.Integrate("x^2", ("x", 0, 1))  # 3*x^2 + 2 ; 1/3
m.Sum("k^2", ("k", 1, "n"))                 # (1/3)*n^3 + (1/2)*n^2 + (1/6)*n
[m.interval(i) for i in m.Reduce("x^2 < 4")]      # ['-2 < x < 2']
m.Simplify("exp(ln(x))", assume={"x": "positive"})  # x
m.Equal("(x+2)(x+3)", "x^2 + 5x + 6")       # True -- a certified zero-test, not tree equality
m.parse("x") + 1, 2 * m.parse("x"), m.parse("x") / 2   # mixed int/Fraction arithmetic
```

Strings accept `^` or `**`, implicit multiplication (`5 x`), `Sin[x]`,
rationals as `p/q` and equations with `=`. The layer never guesses: several
free variables raise `ValueError` naming them; a float literal is a
`TypeError` (write `Fraction(1, 2)`); `pi`/`E` are refused because the CAS is
exact over Q; an undecided `Equal` raises rather than answering `False`.
Every result is still a `cas.Expr` with its Rust certificates reachable, and
`None` means the Rust side declined (multivariate `Factor`, a symbolic
exponent -- `CasExpr::Pow` is `u32` -- and similar gaps are real and stated).

## Which model a `sat` returns, and what a check cost

Three surfaces from ADR-2140 (items 6, 7 and 9 of the 2026-09-16 list):

- **`model_preference`** on `smt.solve(...)` and `solver.Config(...)`:
  `"any"` (the default, and byte-for-byte the search as shipped), `"zero"`
  (a replay-checked greedy bit-clearing pass over the witness, so it is a
  local minimum in the unsigned order; bounded by what the solve spent), or
  `"least-unsigned"` (the bounded re-solve below, then the same pass inside
  the winning rung). A preference never moves a verdict; every `sat` still
  replays. `AXEYUM_MODEL_PREFERENCE` sets the same policy for a whole process,
  and `AXEYUM_MODEL_PREFERENCE_PHASE=on` additionally makes the SAT core
  decide every variable `false` first (z3's `phase=always_false`; measured to
  cost search time without moving models, so off by default). A malformed
  value of either refuses rather than running the default arm.
- **`smt.least_witness(script, symbols=[], ...)`** returns a `Witness`: an
  `Outcome` whose model is the first satisfiable rung of the magnitude ladder
  `1, 16, 256, 4096` over the named bit-vector constants (all of them when
  `symbols` is empty), else the unbounded model, with `.bound` saying which.
  The bound is two's-complement magnitude, so `a + b < a` comes back as
  `a = 0xFFFFFFFF, b = 1` at bound 1. This is the ladder
  `python/examples/cindergraph_defects/check.py` used to run by hand.
- **`solver.Incremental(arena, config, profile=True).stats()`** returns a
  typed `IncrementalStats`: `solve_ns`, `bit_blast_ns`, `cnf_encode_ns`,
  `model_lift_ns`, `replay_ns`, `word_rewrite_ns`, the counts, and
  `delta_since(earlier)` for one check's cost. **Without `profile=True` the
  timers and `checks` are zero by contract** — the Rust engine only reads
  the clock when profiling is on — and `IncrementalStats.profiled` says
  which case you are in. `as_dict()` is the `dict` `stats()` returned before
  this type existed.

## See also: C defects through cindergraph

[`python/examples/cindergraph_defects/`](../../python/examples/cindergraph_defects/README.md)
lifts scalar C functions (loops unrolled to a stated bound) from cindergraph's
typed AST into QF_BV queries, has `axeyum.smt.solve` find a witness per sink
(buffer length, array index, divisor, shift amount, signed overflow, narrowing
store, allocation-size wrap, uninitialised read, dead branch), and replays
every witness under AddressSanitizer, UBSan or MemorySanitizer at the finding's
line. Twelve textbook defect/fix pairs ship with it, and since 2026-09-17 it is
a gate of `just py-check` (above), not an example that runs when someone
remembers.
