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

A compiled `.so` is opaque to every type checker, so the stubs under
`python/axeyum/_native/*.pyi` supply the surface. They are **generated** from
the built module by [`tools/gen_native_stub.py`](../../tools/gen_native_stub.py)
and must never be hand-edited: a hand-written stub drifts silently and then
makes the checker confidently wrong about code that changed underneath it.

Every parameter and return is `Any`. That is deliberate and it is what keeps the
stub *sound* — PyO3 exposes arity, parameter names and defaults but no types, so
the stub catches a call with the wrong argument count or a misspelled keyword
and never invents a constraint the Rust side does not impose.

After any change to the Rust surface:

```sh
uv run --no-sync maturin develop
uv run --no-sync python tools/gen_native_stub.py
```

`python/tests/test_native_stub_current.py` regenerates into a temporary
directory and compares byte-for-byte, so a Rust signature change cannot land
with a stale stub still describing the old one.

## The gate

```sh
just py-check
```

Five steps: `maturin develop`, `pytest python/tests -q`, the stub drift check,
`ruff check`, `ruff format --check`. **Read the counts, not the exit status** —
each step prints one:

```
PYTEST|collected=N
STUBS|compared=M
```

Both fail on zero. A pytest run that collects nothing exits 5 and prints "no
tests ran", and a drift check pointed at an empty directory would otherwise
report "nothing differed" and exit 0; those are the inert-gate shape this
repository has been bitten by repeatedly, so `python/tests/conftest.py` fails a
session that collected zero tests and `gen_native_stub.py --check` exits 1 when
it compared zero stubs.

`scripts/check.sh` runs the same steps only when `uv` **and** a synced `.venv`
are both present, and otherwise prints `py-check: SKIPPED (no uv)` — skipped,
never passed. Which hosts have `uv` is recorded in
[fleet hosts](../contributor-guide/fleet-hosts.md).
