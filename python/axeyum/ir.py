"""``axeyum.ir`` (tier R + C) -- term arenas, sorts, values, the trusted evaluator.

This module exists so ``import axeyum.ir`` resolves. It adds nothing: every
name is the object the native ``axeyum._native.ir`` module defines, and the
whole surface is a projection of the Rust API (no admission authority).
"""

from __future__ import annotations

import sys as _sys

from ._native import ir as _native_ir

# Re-export every public native name, and let nested native submodules
# (``axeyum._native.ir.<child>``) resolve under this name too.
globals().update({k: v for k, v in vars(_native_ir).items() if not k.startswith("_")})
for _name, _module in list(_sys.modules.items()):
    _prefix = "axeyum._native.ir."
    if _name.startswith(_prefix):
        _sys.modules.setdefault("axeyum.ir." + _name[len(_prefix) :], _module)
__all__ = [_k for _k in sorted(vars(_native_ir)) if not _k.startswith("_")]
