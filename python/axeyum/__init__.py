"""Python bindings for the Axeyum automated reasoning stack.

The surface is a *projection* of the Rust API: nothing here exists that does not
exist in Rust, and nothing here can admit a fact, write a ledger, relax a
checker, or change an axiom footprint.

Submodules, by trust tier:

* :mod:`axeyum.ir` -- tier R + C. Sorts, terms, values, the trusted ground
  evaluator, bit lowering, floating-point builders, the query planner.
* :mod:`axeyum.smt` -- tier P + C. Decide an SMT-LIB script and replay it.
* :mod:`axeyum.solver` -- tier P + C. Decide term lists, produce evidence, and
  re-check certificates.

Three rules are carried across the language boundary verbatim:

* ``unknown`` is a value, never an exception. A budget-exhausted query returns
  an :class:`Outcome` with ``status == "unknown"``, or a
  ``CheckResult`` with ``status == "unknown"`` and a classified
  ``unknown_kind``.
* Every ``sat`` is checkable by evaluating the original term against the lifted
  model -- ``Outcome.replay()`` and ``CheckResult.replay()`` are that check,
  run in Rust.
* Degenerate operators are **total** with SMT-LIB semantics. ``bvudiv(x, 0)``
  is all-ones, ``int_div(a, 0)`` is ``0`` and ``int_mod(a, 0)`` is ``a``.
  Nothing raises ``ZeroDivisionError``, and a caller expecting one would
  misread a correct answer.
"""

from __future__ import annotations

from enum import Enum

from . import knowledge
from ._native import (
    ArrayValue,
    AxeyumError,
    BudgetExceeded,
    BvValue,
    DatatypeValue,
    FuncValue,
    GenericArrayValue,
    InternalError,
    RealAlgebraicValue,
    ReplayUnavailable,
    SmtLibParseError,
    UninterpretedValue,
    ir,
    machine,
    smt,
    solver,
    version,
)
from ._native.ir import EpochError, SortError
from ._native.smt import Outcome

__version__: str = version()


class UnknownKind(str, Enum):
    """Why a check came back undecided.

    A ``str`` enum so ``result.unknown_kind == UnknownKind.TIMEOUT`` works
    against the plain string the extension returns. **None of these is an
    exception** -- they are the classified shapes of a first-class ``unknown``.
    """

    TIMEOUT = "Timeout"
    RESOURCE_LIMIT = "ResourceLimit"
    MEMORY_LIMIT = "MemoryLimit"
    NODE_BUDGET = "NodeBudget"
    ENCODING_BUDGET = "EncodingBudget"
    INCOMPLETE = "Incomplete"
    OTHER = "Other"


class Strategy(str, Enum):
    """A solving strategy for ``solver.solve_with_strategy``.

    ``ORACLE`` (Z3) is deliberately absent: it is a C/C++ leaf dependency and
    ships only in a separate opt-in wheel (ADR-0002).
    """

    EAGER_PURE_RUST = "eager_pure_rust"
    LAZY_BV_ABSTRACTION = "lazy_bv_abstraction"
    AUTO = "auto"


__all__ = [
    "ArrayValue",
    "AxeyumError",
    "BudgetExceeded",
    "BvValue",
    "DatatypeValue",
    "EpochError",
    "FuncValue",
    "GenericArrayValue",
    "InternalError",
    "Outcome",
    "RealAlgebraicValue",
    "ReplayUnavailable",
    "SmtLibParseError",
    "SortError",
    "Strategy",
    "UninterpretedValue",
    "UnknownKind",
    "__version__",
    "ir",
    "knowledge",
    "machine",
    "smt",
    "solver",
    "version",
]
