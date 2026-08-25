# 11 — Zero-copy audit of `crates/axeyum-py`

Measured 2026-08-24 against `main` in a `git archive` snapshot. Every count in
this document was produced by a command, not read off a comment; the commands
are named so a referee can re-run them.

Baseline for the audit (before any change here):

```
grep -rc '.clone()' crates/axeyum-py/src            # 190
grep -rcE '\.to_owned\(\)|\.to_string\(\)' …        # 90
grep -rc 'extract::<' crates/axeyum-py/src          # 24
grep -rc 'detach' crates/axeyum-py/src              # 65
114 #[pyclass] declarations, 85 of them `frozen`
```

After the changes described below: **178 clones, 11 `extract::<>`, 69 detach
sites**. The clone count falls by twelve and not by a hundred, and the reason is
the finding, not a shortfall: **97 of the remaining 178 are a value crossing
into a Python-owned object**, which is not a copy that can be removed without
changing what the object *is*.

---

## 1. The `.clone()` / `.to_owned()` census

Classification of all 178 remaining `.clone()` sites; see "Reproducing the
census" below.

| class | count | what it is |
|---|---:|---|
| **(a)** into a Python-owned object | **97** | the value is being placed inside a `#[pyclass]` or a `PyErr`, which owns its data and carries no lifetime |
| **(a)** `Py<T>` refcount bump | **9** | `x.bind(py).clone()` / `clone_ref(py)` — an `INCREF`, not a data copy |
| **(b)** avoidable now | **2** | algorithmic, in the assertion-stack walk |
| **(c)** needs a Rust-side API change — CAS consuming ops | **38** | `axeyum_cas` builders take `CasExpr` **by value** |
| **(c)** needs a Rust-side API change — ownership for `detach` | **20** | the closure must own its input to be `Send` across `Python::detach` |
| **(c)** needs a Rust-side API change — other by-value Rust APIs | **12** | `Model`, `SolverConfig`, `UnsatProof`, `Value` all cross by value |

### (a) — unavoidable, and why

A `#[pyclass]` is a lifetime-free `Copy`-handle boundary by this repository's
own hard rule ("never let backend FFI types or lifetimes leak into public
APIs"). It therefore **owns** its payload, and the only way to build one from a
borrowed field is to clone. `MvPoly::wrap(self.inner.poly.clone())` is not
waste; it is the boundary. The same holds for every `*Error::new_err(x)`: a
Python exception outlives the Rust frame that raised it.

The nine refcount cases are worth separating because they *look* like the
expensive kind and are not: `self.model.bind(py).copy()` and
`self.values.as_ref().map(|v| v.bind(py).clone())` do an `INCREF` on a pointer.

### (b) — fixed in this pass

Twelve owned copies were removed outright by returning a borrow, and thirteen
whole-object clones were removed from `__eq__` (§2). The removals:

| site | was | now |
|---|---|---|
| `producers.rs` `DeclineReason::__str__` | `String` clone | `&str` |
| `producers.rs` `ImportReport::axioms` | `Vec<String>` clone | `&[String]` |
| `producers.rs` `ImportReport::substituted_theorems` | `Vec<String>` clone | `&[String]` |
| `solver/cnf.rs` `SatOutcome::assignment` | `Vec<bool>` clone | `Option<&[bool]>` |
| `cas/certify/telescoping.rs` `samples` | `BTreeMap` clone | `&BTreeMap<..>` |
| `cas/certify/telescoping.rs` `leading_zeros` | `Vec<i64>` clone | `&[i64]` |
| `cas/certify/geometry.rs` `coordinates` | `Vec<String>` clone | `&[String]` |
| `cas/certify/geometry.rs` `conditions_used` | `Vec<String>` clone | `&[String]` |
| `smt.rs` `Outcome::replay_unavailable_reason` | `Option<String>` clone | `Option<&str>` |
| `smt.rs` `Script::commands` get-value pairs | `String` clone per pair | `&str` |
| `convert.rs` `FuncValue::params` | `Vec<PySort>` clone | `PyList::new` from the iterator |
| `kernel.rs` `ExprNode::levels` | `Vec<PyLevelId>` clone | `PyList::new` from the iterator |

The last two are the `Vec`-only-to-convert case. `&PySort` and `&PyLevelId`
have no `IntoPyObject` (they are pyclasses), so a borrow is not available; what
*is* available is skipping the intermediate `Vec` entirely — `PyList::new` over
an `ExactSizeIterator` presizes the list and fills it in place.

The two remaining (b) sites are `stack.clone()` in `smt.rs::active_assertions`,
inside the narrow re-lift fallback (§4). They are O(assertions) per `check-sat`
command on a path that already pays a full re-parse; removing them is not worth
a correctness risk in a fallback.

### (c) — named API changes, not applied

1. **`axeyum_cas` builders consume `CasExpr`** (38 sites, `cas/expr.rs`). Every
   `Expr` method reads `Expr::wrap(self.inner.clone().sin())` because
   `CasExpr::sin(self)` takes ownership, and the pyclass is `frozen` and shared
   so it cannot give ownership away. **The change:** by-reference builders
   (`fn sin(&self) -> CasExpr`) or an `Arc`-backed `CasExpr` node so the clone
   is a refcount. This is the single largest cluster in the crate and it is
   entirely a Rust-side shape.
2. **`Python::detach` requires an owned closure** (20 sites). `py.detach(|| …)`
   needs `Ungil + Send`, so every long CAS/certificate call first does
   `let owned = self.inner.clone();`. **The change:** a scoped detach that can
   borrow a `Sync` payload, or `Arc` payloads as in (1) — the same fix covers
   both clusters.
3. **`Model`, `SolverConfig`, `UnsatProof`, `Value` cross by value** (12 sites,
   `solver/*.rs`, `smt.rs`, `convert.rs`). **The change:** `Arc<Model>` in
   `CheckResult::Sat`, and `&SolverConfig` where a config is only read.

### `to_owned()` / `to_string()` (94 sites)

Dominated by two unavoidable shapes: **`error.to_string()` feeding
`*Error::new_err`** (a Python exception owns its message) and
**`kernel.display_name(id).to_string()`**. The second deserves naming: the
kernel renders a `NameId` through a `Display` **wrapper**, so there is no
borrowable text to hand back — `Kernel::declaration_names` therefore still
allocates one `String` per name and cannot do otherwise without a
`NameId → &str` accessor on the kernel. That is a (c).

### Reproducing the census

```sh
grep -rn '\.clone()' crates/axeyum-py/src        # 178 rows
grep -rnE '\.to_owned\(\)|\.to_string\(\)' crates/axeyum-py/src   # 94 rows
```

---

## 2. `extract::<T>()` that should be `cast::<T>()`

**Thirteen of the twenty-four `extract::<>` sites were `__eq__`**, all with the
identical body:

```rust
other.extract::<Expr>().is_ok_and(|other| other.inner == self.inner)
```

`extract` on a `#[pyclass]` **clones the whole wrapped value** — an entire CAS
expression tree, a multivariate polynomial, a geometry certificate — compares
it, and drops it; and on the ordinary `NotImplemented` path it constructs a
`TypeError` object that is thrown away. All thirteen classes are `frozen`, so
`Bound::get` is a borrow with no runtime borrow check at all:

```rust
other.cast::<Expr>().is_ok_and(|other| other.get().inner == self.inner)
```

Rewritten in `cas/functions.rs` (`Matrix`), `cas/poly.rs` (`Monomial`,
`MvPoly`, `MultiPoly`), `cas/expr.rs` (`Expr`, `ZeroTest`),
`cas/certify/{sturm,telescoping,gf2,geometry,groebner}.rs`. `extract::<>` count
falls 24 → 11.

The eleven that remain are genuine conversions where the error is *used* or the
target is not a pyclass (`extract::<String>`, `extract::<PathBuf>`,
`extract::<Vec<u8>>`, `extract::<i128>`) — `cast` does not apply to those.

---

## 3. `detach`: measured, not guessed

**The round trip costs ~50–60 ns on this host.** Measured by comparing a
kernel method that detaches around trivially short work against two that do
not, in the same process:

| call | detaches | ns/call |
|---|---|---:|
| `Kernel.declaration_count()` | no | 23.1 |
| `Kernel.epoch` (getter) | no | 31.0 |
| `Kernel.def_eq(e, e)` | **yes** | 81.9 |

`def_eq` on identical `ExprId`s short-circuits, so the ~51–59 ns delta is the
handoff.

**Missing on a hot path — fixed.** The whole `axeyum.cas` pure-function surface
(~40 entry points generated by four macros in `cas/functions.rs`) held the GIL
through the entire CAS call. `cas.simplify` measures **~310 µs/call**, four
orders of magnitude above the detach cost, and it serialized every other thread
in the process for the duration. All four macros now detach. Single-threaded
cost is at noise (62.6 ms → 62.9 ms per 200 calls, §5).

**Wrapping trivially short work — none found, and deliberately not added.**
`ir.eval` is ~376 ns/call, about six detach round trips; wrapping it would spend
a sixth of the call on the handoff for no single-threaded gain. The same for the
`Arena` builders. The rule the ratio gives, now written into
`cas/functions.rs`: **detach when the Rust work is at least a few microseconds;
for a per-item surface the fix is a bulk entry point, not a detach.**

---

## 4. The double front-door call

`smt.solve` used to call `solve_smtlib` for the verdict and then
`solve_smtlib_model` a second time to recover an arena to replay against —
because the front door returned a verdict and dropped the arena the decided
terms lived in.

`axeyum_solver::smtlib::solve_smtlib_with_model` (new, additive) *is* the front
door now; `solve_smtlib` is a projection of it (`Ok(solve_smtlib_with_model(…)?.outcome)`),
so the two cannot report different verdicts. It returns `SmtLibSolved { outcome,
script, assertions, model }` — the arena the terms live in, the assertion stack
that was decided, and that run's own model.

**Measured:** the 20-file committed `sat` sweep goes **2432 ms → 1098 ms**
(2.2×). The `unsat` sweep is the control and does not move (13744 → 13587 ms):
`unsat` never paid the second solve.

`assertions`/`model` are populated **only** for the flat bounded-encoding path.
The source-level string/FP routes decide against the raw SMT-LIB expressions and
build no flat view; a model over source symbols replayed against the *packed*
assertions would report `False` — the documented **soundness** signal — whenever
an encoding abstraction symbol completed differently than the source route
assumed. So `SmtLibSolved` reports `None`, and the binding keeps the old re-lift
for exactly that case. Measured over `corpus/regression` at a 1 s budget: **48
`sat` verdicts, 44 replayed from the deciding run with no second solve**, ≤ 4 on
the re-lift, 1 with no replay at all (a quantified LIA negation the ground
evaluator cannot decide).

---

## 5. Zero-copy where the data is bytes

`UnsatProof.dimacs/.drat/.lrat` and `CnfFormula.to_dimacs` return `str`, which
makes CPython scan the whole text for its widest code point to pick a `PyUnicode`
representation — linear in a proof that can reach megabytes, and every consumer
(a file, a hash, a subprocess stdin) wants bytes back immediately.

Added: `UnsatProof.dimacs_bytes()`, `.drat_bytes()`, `.lrat_bytes()` and
`CnfFormula.to_dimacs_bytes()`, each built with `PyBytes::new_with` — one
`memcpy` straight into the returned object's own buffer. `lrat_bytes()` keeps
`None` meaning "no LRAT", never an empty `bytes`.

Measured on a 66 411-byte DIMACS, 200 reads: **0.513 ms → 0.200 ms (2.6×)**.

`Kernel.declarations()` clones every `Declaration` — the full expression tree of
every type and proof — into a Python object. Added `Kernel.declaration_names()`
(names only). The single-name accessor asked for already existed as
`Kernel.get_declaration(name)`. Measured over a built `nat` prelude (358
declarations), 20 calls: `declarations` 0.777 ms, `declaration_names` 0.432 ms,
`get_declaration` 0.003 ms.

`kernel_theorems` in the agent layer does cache per process — **verified**: it
goes through `_kernel_for`, which carries `@lru_cache(maxsize=len(PRELUDES))`
(`python/axeyum/agent/tools.py:414`), so each prelude is built once per process.
Its own `kernel.declarations()` call is NOT replaceable by `declaration_names()`
— it reads `declaration.kind` and `declaration.ty` on every row. The native
`prelude_cache_stats()` confirms the kernel's template cache is live under it
(cold build 117 ms in a fresh interpreter, 7 ms warm, ~16×).

---

## 6. Benchmarks

`python/benchmarks/bench_binding.py`, plain `time.perf_counter`, no
`pytest-benchmark`. Reports the **minimum** of its repeats — the one statistic a
shared box cannot inflate. `--json` emits one record per case.

| case | before | after | |
|---|---:|---:|---|
| `smt.solve` / 20 `sat` files | 2432.4 ms | **1097.8 ms** | 2.22× |
| `smt.solve` / 7 `unsat` files | 13744.1 ms | 13587.2 ms | control, flat |
| `ir.Arena` build ×10k | 6.04 ms | 6.19 ms | flat |
| `ir.eval` ×10k | 3.76 ms | 3.94 ms | flat |
| `cas.simplify` ×200 | 61.1 ms | 62.9 ms | flat (now detached) |
| `Kernel.build_nat_prelude` cold | 117.8 ms | 120.5 ms | flat |
| `Kernel.build_nat_prelude` cached | 6.80 ms | 7.38 ms | flat |
| `Kernel.declarations` ×20 | 0.777 ms | 0.779 ms | flat |
| `Kernel.declaration_names` ×20 | — | **0.432 ms** | new, 1.8× |
| `Kernel.get_declaration` ×20 | — | 0.003 ms | new |
| `UnsatProof.dimacs` ×200 (66 KB) | 0.513 ms | 0.521 ms | flat |
| `UnsatProof.dimacs_bytes` ×200 | — | **0.200 ms** | new, 2.6× |
