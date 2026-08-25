# 10 — Quality plan for the PyO3 / maturin layer, measured against current practice

Status: plan, 2026-08-24. Sources were read that day and are cited inline;
every "today" number was measured on the worktree at `c2ce633ee`.

## What the sources say, and what we do

| topic | current practice (source) | Axeyum today | gap |
|---|---|---|---|
| class design | `#[pyclass(frozen)]` for anything not mutated from Python; frozen + `Sync` lets `Bound::get`/`Py::get` skip the runtime borrow check; `eq`/`hash`/`ord`/`str` derive options instead of hand-written dunders; `from_py_object` for `Clone` classes passed by value; `unsendable` only as a last resort (panics on foreign-thread access) — [PyO3 class guide](https://pyo3.rs/v0.29.2/class.html) | 99 classes, **85 frozen**, 2 `unsendable` (`Config`, `Incremental` — `!Sync` upstream), 1 `eq` derive, hand-written `__eq__`/`__hash__` elsewhere | replace hand-written dunders with the derive options where `PartialEq`/`Hash` exist; audit the 14 non-frozen classes |
| performance | `cast` over `extract` when the error is discarded; take the token from `Bound::py()`; Rust tuples for calls (vectorcall); `Python::detach` for long Rust-only work — and it has a cost, so not for trivial calls; design around bulk operations — [PyO3 performance guide](https://pyo3.rs/v0.29.2/performance.html) | 65 `detach` sites; **190 `.clone()` + 90 `to_owned()`**; `smt.solve` calls the front door twice on `sat` to obtain a replayable model | the audit in `11-zero-copy-audit.md`; a single additive solver entry point returning verdict + arena + model |
| zero-copy | buffer protocol / `PyBytes::new_with` for bytes; `PyBackedStr` for borrowed text; avoid intermediate `Vec` before a `PyList` — [buffer protocol discussion](https://github.com/PyO3/pyo3/discussions/4077), [PyO3 0.29 `PyUntypedBuffer::obj`] | proofs (`dimacs`/`drat`/`lrat`) and DIMACS returned as `str` copies; `declarations()` builds a full owned list | bytes accessors for proofs; names-only inventory + per-name lookup |
| typing / QA | typed `.pyi` from Rust signatures — `pyo3-stub-gen` 0.23.0 (PyO3 `>=0.27,<0.30`) with `#[gen_stub_*]` macros, `PyStubType` mapping, `stubtest` validation ([repo](https://github.com/Jij-Inc/pyo3-stub-gen)); PyO3's own `experimental-inspect` + `maturin generate-stubs` exists but **requires an inline `#[pymodule]`** and is "still in active development" ([type-stub guide](https://pyo3.rs/main/type-stub)); a type checker over the package | introspection-generated stubs: **1,220 `: Any`, 750 `-> Any`, 9 typed parameters**; no `ty`/mypy in the gate | adopt `pyo3-stub-gen`; keep the introspection generator as the *drift* check (names/arity) and add `stubtest` for types; `ty` in `just py-check` |
| testing | hypothesis `@given` for property-based differentials (edge cases generated: zero, negatives, huge ints) ([Hypothesis](https://hypothesis.readthedocs.io/en/latest/), [pytest + Hypothesis](https://pytest-with-eric.com/pytest-advanced/hypothesis-testing-python/)); Rust-side tests under `Python::attach` with `auto-initialize`; `pyo3-testing` for wrapped fns | 1,101 example-based pytest; **0 property tests; 1 Rust unit test** | hypothesis differentials over the evaluator, the CAS ring laws, replay; Rust unit tests for the encoder/epoch/quantifier helpers |
| free-threading | `gil_used = false` is the 0.28+ default and declares thread-safety; abi3 is unavailable on `t` builds — ship an abi3 wheel for the minimum version **plus** a `3.14t` version-specific wheel, then abi3t for 3.15 (PEP 803); mutable classes need `Mutex`/atomics or `frozen` with interior mutability — [free-threading guide](https://pyo3.rs/v0.29.2/free-threading.html) | `gil_used = true` (honest until the `Sync` audit); abi3-py312 only | keep `gil_used = true` until `Config`/`Incremental` are `Sync`; add the 3.14t wheel to the release matrix now |
| distribution | `maturin generate-ci github`; `maturin-action` with `manylinux: 2_28`, `sccache: true`, `interpreter: 3.14t` for the free-threaded wheel; abi3 collapses the interpreter matrix; sdist built and **installed from** as a test — [maturin-action](https://github.com/PyO3/maturin-action), [project layout](https://www.maturin.rs/project_layout) | dev-only `maturin develop`; no wheels, no sdist, no smoke-install | `wheels.yml` on tags/dispatch with a smoke job that imports every built wheel |

## Slices (this goal)

| # | slice | delivers | gate that proves it |
|---|---|---|---|
| Q1 | property-based tests + Rust unit tests + `ty` | hypothesis differentials (evaluator vs SMT-LIB reference incl. degenerate operators; CAS ring/identity laws with certificates; replay invariants), `cargo test -p axeyum-py` > 1, `ty` in `py-check` | counts printed; one property deliberately broken in the *reference* dies |
| Q2 | zero-copy / performance audit | every clone classified (unavoidable / fixed / needs Rust API); `solve_smtlib_with_model` in `axeyum-solver` (additive) ending the double solve; bytes accessors for proofs; micro-benchmarks before/after | equality test of new vs old front door over the corpus; benchmark table |
| Q3 | release wheels | `wheels.yml` (manylinux 2_28 x86_64/aarch64, macOS, Windows, **3.14t**, sdist) + smoke-install job gated before any publish; sdist installed-from locally | wheel tags, `ldd` no libpython, from-sdist install |
| Q4 | close the ledger | the eight open tier-R solver rows as structured records | `PYTHON_COVERAGE|…|tier_r_unreferenced=0` |
| Q5 | typed stubs | `pyo3-stub-gen` annotations across the binding; generated typed `.pyi`; `stubtest` + `ty` green; the introspection generator retained as the arity/name drift gate | `Any` count falls from 1,970 to what is genuinely dynamic; `stubtest` exit 0 |
| Q7 | panic-surface hardening | a probe that calls every public callable with adversarial arguments and counts `PanicException`s (a `BaseException` that escapes `except Exception`, per the PyO3 error-handling guide); typed preflight checks at the boundary, `catch_unwind` only where preflight is impossible and never as a blanket; a hypothesis "no panic" property; a meta-test that fails when a panic returns | `PANIC_PROBE|…|panics=0`; before/after table in `13-panic-surface.md` |
| Q8 | CAS long tail (coverage S5) | ntheory / combinatorics / stats / special / transforms / normal forms / moment provers / ansatz / gf / boolean / algebraic, tested against sympy as an independent oracle where definitions agree; `axeyum.m` verbs for the natural names | `axeyum-cas` referenced count in the coverage ledger; sympy disagreements reported, not resolved silently |
| Q6 | class-design pass | derive `eq`/`hash`/`str` where the Rust types support it; make `Config`/`Incremental` `Sync` (Mutex) so `unsendable` and then `gil_used = true` can go | `unsendable` count 0; a 3.14t import with no `RuntimeWarning` |

Q1–Q4 run in parallel in isolated snapshots; Q5 touches every binding file and follows them; Q6 follows Q5.

## Rules carried forward

- A `frozen` class is the default; a non-frozen one needs a sentence saying what Python mutates.
- No `detach` around work shorter than a Python call; measure, don't guess (Q2 carries the micro-benchmark).
- Property tests compare against an *independent* reference (Python semantics written from the SMT-LIB text, `fractions` arithmetic, a second kernel) — never against the binding's own other route.
- A stub type that cannot be derived stays `Any` and is listed; a wrong type is worse than none.
- Every wheel that builds must import in a fresh venv before it may publish.
