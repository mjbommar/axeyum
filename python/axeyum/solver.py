"""``axeyum.solver`` (tier P + C) -- configs, verdicts, evidence, proofs, CNF.

This module exists so ``import axeyum.solver`` resolves. It adds nothing: every
name is the object the native ``axeyum._native.solver`` module defines, and the
whole surface is a projection of the Rust API (no admission authority).
"""

from __future__ import annotations

import sys as _sys

from ._native import solver as _native_solver

# Re-export every public native name, and let nested native submodules
# (``axeyum._native.solver.<child>``) resolve under this name too.
globals().update({k: v for k, v in vars(_native_solver).items() if not k.startswith("_")})
for _name, _module in list(_sys.modules.items()):
    _prefix = "axeyum._native.solver."
    if _name.startswith(_prefix):
        _sys.modules.setdefault("axeyum.solver." + _name[len(_prefix) :], _module)
__all__ = [_k for _k in sorted(vars(_native_solver)) if not _k.startswith("_")]
