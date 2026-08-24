# PyO3 / maturin for Axeyum — design study

Date: 2026-08-24. Repo at `0874b9e4f`. Everything marked *measured* was run on this host (s4, Python 3.14.4, uv 0.11.1, rustc per workspace toolchain).

## 1. Feasibility — the three constraints that could have blocked it, all measured

| Constraint (CLAUDE.md / ADR) | Result | Evidence |
|---|---|---|
| `unsafe_code = "deny"` workspace-wide; exceptions need an ADR | **PyO3 0.29.2 passes.** `#[pyclass]`, `#[pymethods]`, `#[pyfunction]`, `#[pymodule]` expand without tripping the lint (proc-macro output is exempt) | probe crate with identical `[lints]` block + clippy pedantic `-D warnings` → exit 0 |
| Default build has no C/C++ dependency (ADR-0002) | **Holds.** With `pyo3/extension-module` nothing links `libpython`; PyO3 is pure Rust. The binding crate is a leaf, like `axeyum-wasm` (ADR-0017) | `ldd` on the built `.so`: no libpython |
| MSRV 1.88, edition 2024, resolver 3 | **Compatible.** PyO3 0.28+ MSRV is 1.83 | pyo3 changelog |

Also measured: `maturin 1.15.0` builds `pyo3probe-0.0.0-cp312-abi3-manylinux_2_34_x86_64.whl` (abi3 ≥ 3.12) in one command; the wheel imports on 3.14.4, `__text_signature__` carries `(s, timeout_ms=1000)`; wheel ships a CycloneDX SBOM.

**Consequence: no ADR exception for `unsafe` is needed.** An ADR *is* still warranted — this is a new public surface, and the hard rule says semantics/model/proof-lifting routes must be explicit before a surface goes public. It should be short and mostly say "the Python surface is a projection of the Rust API and carries no authority the Rust API lacks."

## 2. Layout — follow glaurung, with two Axeyum-specific corrections

```
pyproject.toml                       # repo root; [tool.maturin] manifest-path = "crates/axeyum-py/Cargo.toml"
crates/axeyum-py/                    # workspace member; cdylib + rlib; NOT in any default feature
  Cargo.toml                         # pyo3 = "0.29", features = ["abi3-py312"]; extension-module ONLY via maturin
  src/lib.rs                         # #[pymodule] fn _native — registration only
  src/{smt,kernel,cas,evidence}.rs   # one file per submodule, glaurung's register_* pattern
python/axeyum/                       # pure-Python package; module-name = "axeyum._native"
  __init__.py  py.typed  _native/*.pyi (generated)
  smt.py kernel.py cas.py            # thin ergonomic layer + dataclasses
python/tests/                        # pytest; asserts a NONZERO count
tools/gen_native_stub.py             # port of glaurung's (introspection + --check drift gate)
```

Corrections vs. glaurung:

1. **`scripts/` stays stdlib-only.** Measured 2026-08-24: 640 scripts, zero third-party imports; every gate in `just check` runs on a fresh machine without a network install. Nothing under `scripts/` may `import axeyum`. The Python package is for *automation and agents*, the scripts are for *gates*. Cross the line only with JSON on disk.
2. **`extension-module` is never a Cargo default feature.** With it on, `cargo test -p axeyum-py` fails to link (undefined Python symbols). glaurung already does this right: `[tool.maturin] features = ["pyo3/extension-module"]`. Keep the Rust unit tests in this crate minimal; the real tests are pytest against the built module.

Also: **`export TMPDIR` off `/tmp` before `maturin develop`.** It writes a wheel there per rebuild; `/tmp` here is a 62 G RAM tmpfs already flagged as an OOM contributor. glaurung learned this on 2026-08-20. Use `/data0/axeyum/scratch/py-tmp-$AXEYUM_AGENT`.

Build through `scripts/cargo-serialized.sh` with `AXEYUM_CARGO_LOCK` set per tree; the `full` feature pulls cas + egraph + kernel + strings, so the cold build is minutes, not seconds.

## 3. Surface design — the trust boundary is the module boundary

Tiered exactly like the overlay's assurance levels. Each Python submodule maps to one tier, so "what can this call authorize" is answerable from the import path.

### `axeyum.smt` — decide, and replay
- `solve(script: str, *, timeout_ms: int, logic_hint: str | None) -> Outcome` over `solve_smtlib` (the ADR-0052 front door; `full` features). `Outcome.status ∈ {"sat","unsat","unknown"}` — **`unknown` is a value, never an exception** (hard rule). `expected_status` echoed, never consulted.
- `Outcome.model -> dict[str, Value]` with `Value::Bool → bool`, `Value::Bv → int` (width kept as attribute), `WideBv → int` (arbitrary precision is free in Python — this is where the binding is *better* than TSV).
- `Outcome.replay() -> bool` exposing `check_model`, so Python can re-verify any `sat` itself. Every `sat` checkable by evaluating the original term (hard rule) — now from Python.
- Determinism: budgets are explicit kwargs, seeds explicit; no dict built from a HashMap iteration.

### `axeyum.kernel` — construct terms, check, inventory
This is the one that matters for strategies. `Kernel` as a `#[pyclass]` (it is `Send + Sync` — it already lives in `static OnceLock<Option<Kernel>>` slots in `prelude_cache.rs`).
- `Kernel.prelude("nat" | "logic" | "integer" | "rat" | "creal" | "complex" | "string")` — warm from the process-wide cache; the prelude build cost is paid once per Python process, which is the single biggest ergonomic win over the example binaries.
- Ids are plain `int` newtypes (`ExprId`, `NameId`, `LevelId`); constructors `app/lam/pi/const_/lit/sort/bvar/fvar` mirror the Rust names; `render_lean(expr) -> str`.
- `theorems() -> list[Theorem]` (name, canonical type, deps) replacing `nat_theorem_inventory`'s TSV; `axiom_footprint(name) -> list[str]`; `dependency_closure(name) -> set[str]`.
- `add_theorem(name, ty, value)` raises `KernelError` (typed subclasses for `TypeMismatch` etc., with rendered expected/got attached — today those are `eprintln!` behind `BIS_DEBUG`).
- **Not exposed:** anything that writes preludes, ledgers, or facts. There is no write route because the Rust API has none; the binding cannot invent one.

### `axeyum.producers` — untrusted proposers
`bounded_induction(kernel, goal) -> Candidate | Decline`, `modeq_family(...)`. **Prerequisite refactor:** `propose_bounded_induction` and its 3,759-line support module live under `examples/bounded_induction_support/`, not in a library. Promote it to `axeyum_lean_import::producers::bounded_induction` first; the binding then wraps a library function. `Decline` carries the typed `DeclineReason` — the five variants today, the richer obstruction vocabulary later — so decline records become Python objects, not parsed stdout.

### `axeyum.cas`
`Expr.parse / simplify / simplify_under_assumptions / evalf / eval(Rational env)`; `groebner`, `sos`, `telescoping` returning **certificate** objects with `.check()` — the certificate-carrying routes are the ones worth exposing first, because their output is independently checkable evidence, not a number.

### `axeyum.evidence`
`to_json()` on every receipt/certificate/outcome; canonical serialization + `sha256()`; nothing else. Feeds the episode artifact directly.

### Cross-cutting
- One `AxeyumError` root; `unknown`/`declined` are return values, never errors.
- `#[pyclass(frozen)]` for every result object; only `Kernel` and the incremental solver are mutable, and those get explicit `Mutex`-backed interior state so a free-threaded build cannot panic on a concurrent borrow.
- Long calls (`solve`, `add_theorem`, producers) run under `py.detach()` so an agent loop's other threads keep running.
- Free-threading: PyO3 0.28+ defaults to `gil_used = false` (declares thread-safety). **Ship v1 with `#[pymodule(gil_used = true)]`** — honest until the `Sync` audit is done; costs a `RuntimeWarning` on 3.14t only. abi3 wheels do not run on free-threaded builds at all; 3.14t needs a separate non-abi3 wheel later (0.29 adds `abi3t` for 3.15+).

## 4. What this changes for the agent study

The earlier pydantic-ai study's largest engineering item was "almost nothing emits JSON; every tool needs a stdout parser plus a pinned-format contract test." A binding removes that layer entirely: tool adapters call `axeyum.kernel.Kernel.prelude("nat").theorems()` and get typed objects; the `KEY|field=value` line formats stop being an interface anyone depends on. The `target/release/examples/` binaries remain for gates and for measurement, unchanged.

It also relocates the tactic-catalog work: strategy preconditions ("the induction variable occurs in two argument positions") can be prototyped in Python over `Kernel` term structure, measured over the 104 ready facts, and only then ported to Rust once a precondition has proven reach. Untrusted search in Python, trusted checking in Rust — the identity sentence, at the language boundary.

## 5. Gates

- `just py-check`: `maturin develop` → `pytest python/tests` → `tools/gen_native_stub.py --check`. Each step must print a nonzero count (tests run, stubs compared). Record which fleet hosts have `uv` in `docs/contributor-guide/fleet-hosts.md`; hosts without it report *skipped*, never *passed*.
- `cargo deny check` will see pyo3's tree (MIT/Apache-2.0 throughout; `target-lexicon`, `indoc`, `unindent`, `memoffset`, `portable-atomic`) — expect no new license class.
- `cargo test --workspace --all-features` continues to compile `axeyum-py` as an rlib; no `extension-module`, so it links.
- `check-links.sh`, `gen-plan.py` untouched.

## 6. Risks
- **The prelude cache is process-global.** A Python REPL that mutates a cached `Kernel` through `add_theorem` sees the mutation forever. Expose `prelude()` as a *clone* of the cached kernel, or make the cache hand out `Arc<Kernel>` and require `Kernel.fork()` before mutation.
- **Memory.** In-process solving means the Python process is now the thing the OOM killer picks. Keep `solve(..., memory_limit_mb=)` wired to the solver's own limits, and run unbounded *search* from an agent in a subprocess under `cargo-serialized.sh`-style cgroup caps; keep *checking* in-process.
- **Two Python packaging stories** (root `pyproject.toml` for the binding, and the proposed `tools/frontier-agent`). Collapse them: the agent becomes `[project.optional-dependencies] agent = ["pydantic-ai-slim[anthropic]==2.33.0", ...]` on the one package.
- **abi3 vs. performance.** abi3 forfeits a few fast paths (e.g. `PyList` internals); irrelevant here — the heavy work is inside Rust calls.

## 7. Recommended first increment (one week)
1. ADR-05xx: the Python surface is a projection; no authority; tiers = submodules.
2. `crates/axeyum-py` + root `pyproject.toml` + `python/axeyum/`; `just py-check`; TMPDIR note in CLAUDE.md commands block.
3. `axeyum.smt.solve` + `Outcome.replay()`; `axeyum.kernel.Kernel.prelude/theorems/axiom_footprint/dependency_closure/render_lean` (read-only).
4. `tools/gen_native_stub.py` ported, with its drift test.
5. pytest: each function exercised, including a `sat` replayed to `True`, an `unknown` returned as a value, and `theorems()` count equal to `nat_theorem_inventory`'s — the binding must agree with the binary it replaces, measured.
6. Week two: promote `bounded_induction_support` to a library module; expose `producers.bounded_induction` and `Kernel.add_theorem`; the Python agent's Tier-C tools then become in-process calls with typed declines.
