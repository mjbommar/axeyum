"""``axeyum.cas`` -- the computer-algebra surface, re-exported from the extension.

This module exists so ``import axeyum.cas`` and ``from axeyum.cas.certify import
geometry`` both resolve. It adds nothing: every name below is the object the
native ``axeyum._native.cas`` module defines, and the whole surface is a
projection of the Rust API.

Two rules cross the language boundary unchanged.

``None`` is a value.
    Across the CAS, ``Option::None`` means *outside the fragment, declined, or
    i128 overflow* -- never an error. ``normalize``, ``factor``, ``integrate``,
    ``MvPoly.add`` and their neighbours return Python ``None`` for it. Exceptions
    are reserved for malformed input (``ValueError``), a malformed artifact or a
    checker that discharged nothing (:class:`CasError`), and a GF(2) budget or
    shape refusal (:class:`Gf2Error`).

A checker returns a report, not a bool.
    Every ``check()`` under :mod:`axeyum.cas.certify` hands back its verdict
    *with the counts it discharged*. A zero count is the fail signal, and a
    checker whose result cannot be falsified is worse than no checker.

Three interval types exist in the Rust crate and are deliberately named apart
here: :class:`RealInterval` is what ``solve_polynomial_inequality`` returns,
``certify.sturm.Interval`` is the arithmetic enclosure primitive, and
``certify.sturm.SetInterval`` is the point-set interval.
"""

from __future__ import annotations

import sys as _sys

from ._native import cas as _cas
from ._native.cas import *
from ._native.cas import (
    certify,
)

# `axeyum.cas` is a *module* shadowing a native submodule, so the dotted names
# below do not resolve on their own. Registering them keeps `import
# axeyum.cas.certify.geometry` working exactly like the `axeyum._native` spelling
# -- the same split plan 01 already paid for once with `axeyum.smt`.
_sys.modules[__name__ + ".certify"] = certify
for _route in ("geometry", "gf2", "groebner", "sos", "sturm", "telescoping"):
    _sys.modules[f"{__name__}.certify.{_route}"] = getattr(certify, _route)

__all__ = [name for name in dir(_cas) if not name.startswith("_")]
