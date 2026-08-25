# 12 -- Release wheels: the matrix, the gate, and how to cut one

Status: landed, 2026-08-24. Everything below marked "measured" was measured on
this host (s-class dev box, Linux, glibc 2.39) on that date with maturin 1.15.0,
pyo3 0.29.2 and uv 0.11.1.

Delivers [`.github/workflows/wheels.yml`](../../.github/workflows/wheels.yml),
the classifier/URL metadata in [`pyproject.toml`](../../pyproject.toml), and the
release procedure. Depends on plan [01](01-pyo3-maturin.md), which fixed
`abi3-py312`, `gil_used = true`, and the no-`libpython` promise.

## What ships

| job | artifact tag | why this row exists |
|---|---|---|
| `linux` x86_64 | `cp312-abi3-manylinux_2_28_x86_64` | abi3 collapses 3.12/3.13/3.14 to one build |
| `linux` aarch64 | `cp312-abi3-manylinux_2_28_aarch64` | native `ubuntu-24.04-arm` runner, no QEMU |
| `macos` arm64 | `cp312-abi3-macosx_11_0_arm64` | built on `macos-14` |
| `macos` x86_64 | `cp312-abi3-macosx_10_12_x86_64` | built on `macos-13`, natively, so `smoke` can import it |
| `windows` x64 | `cp312-abi3-win_amd64` | |
| `freethreaded-linux-x86_64` | `cp314-cp314t-manylinux_2_28_x86_64` | abi3 does not exist on free-threaded CPython |
| `sdist` | `axeyum-<version>.tar.gz` | the only artifact a source-install consumer gets |

Seven build jobs, not twenty-one: `abi3-py312` is what makes the interpreter
axis collapse. The free-threaded row is the one place it cannot.

### The abi3 / 3.14t / abi3t ladder

1. **Today.** One `abi3-py312` wheel per platform, covering 3.12 through 3.14,
   plus one version-specific `cp314-cp314t` wheel. This is exactly the
   distribution PyO3's free-threading guide recommends: "update your release
   procedure to also upload a version-specific free-threaded wheel."
2. **When CPython 3.15 lands.** PyO3 gains `abi3t-py315`, a stable ABI for
   free-threaded builds. At that point the 3.14t row becomes an `abi3t` row and
   collapses the same way abi3 did. `pyo3-build-config` already carries
   `MINIMUM_SUPPORTED_VERSION_ABI3T` and prefers `abi3t` when the interpreter is
   at or above it, so this is a feature flag, not a redesign.
3. **3.14t stays version-specific until then**, because 3.14 is below that
   minimum. Nothing to decide; the build config decides it.

### How abi3 gets turned OFF for 3.14t: it does not, and nothing needs to

The obvious guesses are both wrong, and it is worth writing down which:

- **A second Cargo feature** (`default = ["abi3"]`, disabled for the 3.14t job)
  is unnecessary. It would also be a maintenance liability, because
  `crates/axeyum-py` must keep linking under `cargo test --workspace` and every
  feature added there is another way to break that.
- **`PYO3_USE_ABI3_FORWARD_COMPATIBILITY`** is a different knob entirely. It
  permits an abi3 build against a CPython *newer than PyO3 knows about*. It has
  nothing to do with free-threading.

The real mechanism is that **the abi3 feature is a no-op on a free-threaded
interpreter and PyO3 resolves the target ABI from the interpreter**.
`pyo3-build-config-0.29.2/src/impl_.rs:1093`:

```rust
} else if get_abi3_version().is_some() && !gil_disabled {
    builder.stable_abi(StableAbi::Abi3)
} else if gil_disabled {
    builder.free_threaded()
```

and the cross-compile path (`impl_.rs:1348`) explicitly falls back with
*"Targeting an abi3 build but build_flags contains Py_GIL_DISABLED, falling back
to a version-specific free-threaded build"*.

Measured end to end, with `crates/axeyum-py/Cargo.toml` unchanged and
`pyo3 = { version = "=0.29.2", features = ["abi3-py312"] }` still in force:

```
$ uv run --no-sync maturin build --release --out dist -i python3.14t   # `dist/` is gitignored; `dist-ft/` is not
Found CPython 3.14t at /home/.../bin/python3.14t
Found pyo3 bindings with abi3-py3.12 support
Warning: abi3 does not yet support CPython 3.14t ... so the build artifacts
         will be version-specific.
Built wheel for CPython 3.14t to axeyum-0.1.0-cp314-cp314t-manylinux_2_34_x86_64.whl
```

So the CI job differs from the abi3 jobs by exactly one input: `interpreter:
3.14t`. **`crates/axeyum-py/Cargo.toml` needed no change for this plan.**

A warning in a log is not a gate, so the job asserts the artifact instead: the
tag must match `*-cp314-cp314t-*.whl` and there must be no `*abi3*.whl` beside
it. If the fallback ever stops happening, that job goes red rather than shipping
a second copy of the abi3 wheel under a free-threaded name.

### `gil_used = true` and what the free-threaded wheel actually does

Plan 01 chose `#[pymodule(gil_used = true)]` because `Sync` on the mutable
classes has not been audited. The consequence is visible and expected -- from
the built `cp314-cp314t` wheel, in a 3.14t venv:

```
RuntimeWarning: The global interpreter lock (GIL) has been enabled to load
module 'axeyum._native', which has not declared that it can run safely without
the GIL. ...
0.1.0
gil_enabled= True
```

The wheel imports, every documented submodule imports, and
`python/tests/test_import.py` passes 16/16 against it. What it does not do is
run without the GIL. That is why `pyproject.toml` carries **no**
`Programming Language :: Python :: Free Threading` classifier: the wheel exists
so 3.14t users can install it at all, not because free-threaded execution has
been audited. Flipping `gil_used` is a separate, evidence-bearing decision and
is out of scope here.

## The sdist and its buildability test

`maturin sdist` builds the source distribution from the **cargo dependency
graph**, not from a file list. Measured: 1221 entries, 8.1 MB, containing
`Cargo.toml`, `Cargo.lock`, `python/axeyum/**` and exactly the 16 workspace
crates that `crates/axeyum-py` transitively depends on.

The belt-and-braces line this plan was expected to add --
`[tool.maturin] sdist-include = ["crates/**/*", "Cargo.toml", "Cargo.lock"]` --
**is not there, on purpose, because maturin 1.15.0 ignores the key silently.**
Probed both directions:

| directive | maturin output | `deny.toml` in tarball |
|---|---|---|
| `sdist-include = ["deny.toml"]` | *(nothing -- no warning either)* | no |
| `include = [{ path = "deny.toml", format = "sdist" }]` | `Including files matching "deny.toml"` | yes |

A dead directive that reads as a guarantee of sdist completeness is worse than
no directive: it is the checker-that-cannot-fail shape, one layer down in the
packaging. The `include` form with `format = "sdist"` is the live key if a file
ever does need adding.

**What actually proves the sdist is complete is building from it**, which is the
`from-sdist-py312` row of the `smoke` job:

```sh
uv venv --python 3.12 .venv
uv pip install "dist/axeyum-<version>.tar.gz[agent]"
```

Measured cold on this host: 87 s, exit 0, imports, 16/16 tests. That is the test
that catches a workspace member missing from the tarball, and it is the only one
that can.

## `smoke` is the gate

A wheel that builds but cannot import is the failure this job exists to catch,
and it is not hypothetical: the artifact carries a compiled `.so`, generated
`.pyi` stubs, a pure-Python package and an optional extra, and any of the four
can be absent from a wheel maturin reports as built.

Eight rows, one per artifact plus a second interpreter for the abi3 wheel. Every
row installs into a **fresh venv from the artifact only** -- never from the
checkout -- so the checkout's `python/axeyum/` cannot mask a wheel that is
missing files. The checkout is present only for `python/tests/`.

Each row runs:

```sh
python -c "import axeyum, axeyum.smt, axeyum.cas, axeyum.kernel, axeyum.knowledge; print(axeyum.__version__)"
python -m pytest python/tests/test_import.py -q
```

Three details that are load-bearing:

- **`[agent]` is installed**, not skipped. `test_import.py` asserts that every
  documented submodule imports in a fresh interpreter, and `axeyum.agent` raises
  `ModuleNotFoundError` naming the extra when it is absent -- measured: without
  it the smoke run is `1 failed, 15 passed`. Installing the extra also proves
  its exact pins still resolve, which is the other thing that can rot.
- **The zero-collection guard applies.** `python/tests/conftest.py` fails a
  session that collected nothing, so this step cannot pass by collecting no
  tests -- the inert-gate trap this repository has hit repeatedly.
- **`ldd` runs on the shipped artifact**, not the build log. The no-`libpython`
  promise (ADR-0002, plan 01) is a property of the `.so` inside the wheel; the
  step extracts the module path from the installed package and requires zero
  `libpython` rows. Measured locally on the abi3 wheel and on the 3.14t wheel:
  `linux-vdso`, `libgcc_s`, `libm`, `libc`, `ld-linux`. Nothing else.

## Cutting a release

```sh
# 1. version lives in the workspace Cargo.toml; maturin reads it (dynamic).
#    Bump it, land it, then:
git tag py-v0.1.0
git push origin py-v0.1.0
```

The tag triggers `wheels.yml`. `workflow_dispatch` runs the same matrix without
a tag, which is how you test a change to the pipeline itself.

Then:

1. `linux` / `macos` / `windows` / `freethreaded-linux-x86_64` / `sdist` build.
2. `smoke` installs and imports all eight, and fails the release if any wheel
   is unimportable.
3. `release` (tag-only, after `smoke`) stages the artifacts and **fails** unless
   there are exactly 6 wheels and 1 sdist and every filename carries the version
   from the tag. A `py-v0.2.0` tag on a tree whose `Cargo.toml` still says
   `0.1.0` stops here rather than publishing a mislabelled release.
4. `publish` uploads to PyPI via `pypa/gh-action-pypi-publish` with trusted
   publishing (OIDC, `id-token: write`, no stored token) -- **and is skipped
   unless the repository variable `AXEYUM_PYPI_PUBLISH` is exactly `true`.**

Publishing is a separate job rather than a gated step inside `release` so that
the `pypi` deployment environment is never resolved while the variable is unset.
Until someone deliberately sets it, a `py-v*` tag builds, smoke-tests and stages
a release and publishes nothing. To turn it on: set the repo variable, create
the `pypi` environment, and register this repository and this workflow as a
trusted publisher on PyPI.

## What is verified here, and what is not

Verified on this host, 2026-08-24:

| check | result |
|---|---|
| `maturin sdist` | `axeyum-0.1.0.tar.gz`, 8,137,322 B, 1221 entries |
| `maturin build --release` | `axeyum-0.1.0-cp312-abi3-manylinux_2_34_x86_64.whl`, 10,535,160 B |
| `maturin build --release -i python3.14t` | `axeyum-0.1.0-cp314-cp314t-manylinux_2_34_x86_64.whl`, 10,513,783 B |
| fresh venv + abi3 wheel + `[agent]` | imports; `test_import.py` 16 passed |
| fresh venv + 3.14t wheel + `[agent]` | imports with the GIL RuntimeWarning; 16 passed |
| fresh venv, install from sdist | built cold in 87 s; imports; 16 passed |
| `ldd` on both `.so` files | no `libpython` |
| `python3 -c "import yaml; yaml.safe_load(...)"` on the workflow | parses; 8 jobs |

**Not verified here, and nobody should read the workflow as evidence for it:**

- Every cross-platform build. This host is `x86_64-unknown-linux-gnu`. The
  macOS (both arches), Windows and linux-aarch64 rows have never been executed;
  the first `workflow_dispatch` run is what turns them from plausible into
  measured.
- `manylinux: '2_28'`. Local builds are tagged `manylinux_2_34` because they use
  this host's glibc; the 2_28 tag comes from the maturin-action container, which
  has not run here. The choice is deliberate (`auto` would pin the wheel to
  whatever glibc the runner happens to have) but the resulting tag is a
  prediction until CI runs.
- `sccache: true`. Cache behaviour on GitHub runners is unmeasured; it can only
  affect build time, not correctness.
- The `publish` job. It has never run and will not until `AXEYUM_PYPI_PUBLISH`
  is set. Trusted publishing also needs a PyPI-side registration that does not
  exist yet.
- `ubuntu-24.04-arm` and `macos-13` runner availability. Both are assumptions
  about GitHub's fleet; `macos-13` in particular is on a retirement path, and
  when it goes the x86_64 macOS wheel becomes a cross-build that `smoke` cannot
  import. Say so at that point rather than dropping the row quietly.
