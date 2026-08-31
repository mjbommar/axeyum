"""``axeyum.machine`` -- executable teaching semantics projected from Rust.

The forwarding module makes normal dotted imports work. It adds no semantic
operation: every public object is defined by ``axeyum._native.machine``.
"""

from __future__ import annotations

import sys as _sys

from ._native import machine as _native_machine

globals().update(
    {key: value for key, value in vars(_native_machine).items() if not key.startswith("_")}
)
for _name, _module in list(_sys.modules.items()):
    _prefix = "axeyum._native.machine."
    if _name.startswith(_prefix):
        _sys.modules.setdefault("axeyum.machine." + _name[len(_prefix) :], _module)

__all__ = [key for key in sorted(vars(_native_machine)) if not key.startswith("_")]
