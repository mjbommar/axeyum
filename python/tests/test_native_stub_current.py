"""The committed ``axeyum._native`` stubs must name what the extension exports.

``python/axeyum/_native/**/__init__.pyi`` is generated from the RUST signatures
by ``cargo run -p axeyum-py --features stub-gen --bin stub_gen``. Nothing in
that pipeline ever looks at the ``.so`` that actually gets imported, so a name
reaching Python through a runtime call the macros cannot see --
``module.add("MAX_BV_WIDTH", ...)``, a ``#[pyo3(name = ...)]`` alias, a
``#[gen_stub_pyfunction(module = "...")]`` naming the wrong submodule -- exists
in one and not the other with nothing red.

``tools/gen_native_stub.py`` is what compares the two. This suite runs it and
pins its floors. Types are NOT its business: ``tools/check_stub_types.py`` and
``mypy.stubtest`` cover those, and keeping them separate means a type
improvement cannot mask a name regression.

Two of the tests are negative controls on the checker itself, because a drift
checker that cannot fail is worse than no drift checker -- the failure mode this
repository has shipped at three other layers.
"""

from __future__ import annotations

import importlib.util
import sys
import types
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent.parent
CHECKER = ROOT / "tools" / "gen_native_stub.py"
STUB_PKG = ROOT / "python" / "axeyum" / "_native"

# The extension registers 21 modules and well over a thousand symbols. A run
# that compared fewer than this did not compare the surface.
MIN_SYMBOLS = 500
MIN_MODULES = 10


def _load_checker() -> types.ModuleType:
    spec = importlib.util.spec_from_file_location("_gen_native_stub", CHECKER)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


@pytest.fixture(scope="module")
def checker() -> types.ModuleType:
    return _load_checker()


def test_the_checker_and_the_stub_package_are_present() -> None:
    assert CHECKER.is_file(), f"missing {CHECKER}"
    assert STUB_PKG.is_dir(), f"missing {STUB_PKG}"
    assert (STUB_PKG / "__init__.pyi").is_file()
    # The PACKAGE layout is the point: a flat `_native/cas.pyi` is a module and
    # can therefore have no `certify` member, which is exactly why
    # `axeyum._native.cas.certify` was an unresolved import under `ty`.
    assert (STUB_PKG / "cas" / "certify" / "sos" / "__init__.pyi").is_file()
    assert (STUB_PKG / "kernel" / "identity" / "__init__.pyi").is_file()


def test_no_stub_drifts_from_the_built_extension(
    checker: types.ModuleType, capsys: pytest.CaptureFixture[str]
) -> None:
    """The gate as `just py-check` runs it."""
    code = checker.main(["--check", "--quiet"])
    out = capsys.readouterr().out
    assert code == 0, out
    assert "STUBS|modules=" in out, out


def test_the_comparison_actually_covered_the_surface(checker: types.ModuleType) -> None:
    """A floor under the counts, so "no drift" cannot mean "nothing looked at"."""
    drift = checker.run()
    assert not drift.problems, drift.problems
    assert drift.symbols >= MIN_SYMBOLS, f"only {drift.symbols} symbols compared"
    assert getattr(drift, "module_count", 0) >= MIN_MODULES


def test_every_stub_file_parses() -> None:
    """A generated stub that is not valid Python is silently useless.

    Not hypothetical: `pyo3-stub-gen` emitted `def equidistant(from: Pt, ...)`
    because the Rust parameter was named `from`, which is a Python keyword. The
    file did not parse, and no type checker would have said so -- it would have
    fallen back to treating the module as untyped.
    """
    import ast

    files = sorted(STUB_PKG.rglob("*.pyi"))
    assert len(files) >= MIN_MODULES
    for path in files:
        ast.parse(path.read_text(encoding="utf-8"), filename=str(path))


def test_check_fails_when_a_runtime_name_is_missing_from_a_stub(
    checker: types.ModuleType, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Negative control on the drift branch."""
    real = checker.stub_path

    def only_the_top(module_name: str) -> Path:
        # Point every submodule at the top-level stub, which does not define
        # their names: the checker must report it rather than shrug.
        return real("axeyum._native")

    monkeypatch.setattr(checker, "stub_path", only_the_top)
    drift = checker.run()
    assert drift.problems, "the checker accepted stubs that describe a different module"


def test_check_fails_when_nothing_was_compared(
    checker: types.ModuleType, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """Negative control on the inert-gate floor, independent of the drift branch.

    With no modules to walk there is nothing to be stale either, so the drift
    branch is silent and only the ``symbols == 0`` floor can fail the run.
    Deleting that floor kills exactly this test.
    """
    monkeypatch.setattr(checker, "walk_modules", lambda *a, **k: None)
    assert checker.main(["--check", "--quiet"]) == 1
    assert "STUBS|FAIL" in capsys.readouterr().out
