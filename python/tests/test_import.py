"""The extension module imports and exposes plan 01's surface."""

from __future__ import annotations

import axeyum


def test_version_is_the_workspace_version() -> None:
    assert axeyum.version() == axeyum.__version__
    assert axeyum.__version__.count(".") == 2


def test_smt_submodule_is_importable_by_name() -> None:
    # `add_submodule` sets the attribute but not `sys.modules`; both routes must
    # work or every consumer hits the split exactly once.
    import axeyum._native.smt as native_smt

    assert native_smt is axeyum.smt
    assert axeyum.smt.__name__ == "axeyum._native.smt"


def test_exception_hierarchy() -> None:
    assert issubclass(axeyum.SmtLibParseError, axeyum.AxeyumError)
    assert issubclass(axeyum.BudgetExceeded, axeyum.AxeyumError)
    assert issubclass(axeyum.AxeyumError, Exception)


def test_public_names_are_all_present() -> None:
    missing = [name for name in axeyum.__all__ if not hasattr(axeyum, name)]
    assert missing == []
