"""``axeyum.smt`` (tier P + C) -- the SMT-LIB front door and model replay.

This module exists so ``import axeyum.smt`` resolves. It adds nothing: every
name is the object the native ``axeyum._native.smt`` module defines, and the
whole surface is a projection of the Rust API (no admission authority).
"""

from __future__ import annotations

import sys as _sys

from ._native import smt as _native_smt

# Re-export every public native name, and let nested native submodules
# (``axeyum._native.smt.<child>``) resolve under this name too.
globals().update({k: v for k, v in vars(_native_smt).items() if not k.startswith("_")})
for _name, _module in list(_sys.modules.items()):
    _prefix = "axeyum._native.smt."
    if _name.startswith(_prefix):
        _sys.modules.setdefault("axeyum.smt." + _name[len(_prefix) :], _module)
__all__ = [_k for _k in sorted(vars(_native_smt)) if not _k.startswith("_")]
