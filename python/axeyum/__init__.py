"""Python bindings for the Axeyum automated reasoning stack.

The surface is a *projection* of the Rust API: nothing here exists that does not
exist in Rust, and nothing here can admit a fact, write a ledger, relax a
checker, or change an axiom footprint.

Two rules are carried across the language boundary verbatim:

* ``unknown`` is a value, never an exception. A budget-exhausted query returns
  an :class:`Outcome` with ``status == "unknown"``.
* Every ``sat`` is checkable by evaluating the original term against the lifted
  model -- :meth:`Outcome.replay` is that check, run in Rust.
"""

from __future__ import annotations

from ._native import (
    AxeyumError,
    BudgetExceeded,
    BvValue,
    SmtLibParseError,
    smt,
    version,
)
from ._native.smt import Outcome

__version__: str = version()

__all__ = [
    "AxeyumError",
    "BudgetExceeded",
    "BvValue",
    "Outcome",
    "SmtLibParseError",
    "__version__",
    "smt",
    "version",
]
