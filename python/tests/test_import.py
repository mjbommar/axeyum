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


def test_every_submodule_is_importable_by_dotted_name() -> None:
    # `add_submodule` sets the attribute but not `sys.modules`. Both routes
    # must work or every consumer hits the split exactly once.
    import axeyum._native.ir.bits
    import axeyum._native.ir.bv
    import axeyum._native.ir.fp
    import axeyum._native.ir.query
    import axeyum._native.solver.cnf
    import axeyum._native.solver.proofs

    import axeyum._native.ir
    import axeyum._native.solver

    assert axeyum._native.ir is axeyum.ir
    assert axeyum._native.solver is axeyum.solver
    assert axeyum.ir.__name__ == "axeyum._native.ir"


def test_each_submodule_names_its_trust_tier_first() -> None:
    for name in ("ir", "smt", "solver"):
        doc = getattr(axeyum, name).__doc__
        assert doc is not None, name
        assert doc.startswith("tier "), (name, doc[:40])


def test_the_ir_exception_leaves_are_under_the_root() -> None:
    assert issubclass(axeyum.EpochError, axeyum.AxeyumError)
    assert issubclass(axeyum.SortError, axeyum.AxeyumError)


def test_unknown_kind_and_strategy_are_str_enums() -> None:
    assert axeyum.UnknownKind.TIMEOUT == "Timeout"
    assert set(axeyum.solver.UNKNOWN_KINDS) == {kind.value for kind in axeyum.UnknownKind}
    assert set(axeyum.solver.STRATEGIES) == {value.value for value in axeyum.Strategy}
