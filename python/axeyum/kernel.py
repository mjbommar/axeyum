"""``axeyum.kernel`` (tier R + C) -- the Lean kernel, its preludes, footprints.

Tier R is everything that only *reads* the kernel (preludes, the environment,
rendering, identity hashes); tier C is the checking gate itself --
:meth:`Kernel.infer`, :meth:`Kernel.def_eq` and :meth:`Kernel.add_declaration`,
which is what admits a theorem.

Three rules are carried across the language boundary verbatim.

**Handles belong to one kernel.** ``NameId``, ``LevelId`` and ``ExprId`` are
lifetime-free indices into the kernel that interned them. Rust does not stop you
mixing kernels -- the result is a different term, silently. Every handle here
carries its kernel's ``epoch`` and every consuming call checks it, raising
:class:`EpochError`. :meth:`Kernel.fork` takes a *new* epoch on purpose: the two
kernels agree at the instant of the fork and diverge the moment either interns
anything.

**Nothing found is not the same as not looked at.** The Rust
``axiom_footprint`` answers an *absent* name with an empty vector, which is
byte-identical to the answer for an axiom-free theorem -- this project's
headline claim. Every accessor here raises ``KeyError`` instead, and
:meth:`Kernel.is_axiom_free` is defined only through the footprint, never by a
declaration-variant test (the trusted surface is ``Axiom | Opaque | Quotient``:
an ``Opaque`` has no proof body and the quotient package admits ``Quot.sound``).

**``axreal`` is not ``real``, and ``CReal`` is not ``AxReal``.**
:meth:`Kernel.build_arith_prelude` builds the *axiomatized* ordered field: 30
declared axioms, the repository's only nonzero row, **none of them reached by a
shipped route**. :meth:`Kernel.build_creal_prelude` builds the *constructed*
reals, which measure 0. A substring test for ``"Real."`` matches ``"CReal."``,
so classify a carrier by its declaration, never by a substring.
"""

from __future__ import annotations

from ._native.kernel import (
    BinderInfo,
    Declaration,
    EpochError,
    ExprId,
    ExprNode,
    Kernel,
    KernelError,
    LevelId,
    Lit,
    NameId,
    Prelude,
    PreludeCacheStats,
    identity,
    prelude_cache_enabled,
    prelude_cache_stats,
)

__all__ = [
    "BinderInfo",
    "Declaration",
    "EpochError",
    "ExprId",
    "ExprNode",
    "Kernel",
    "KernelError",
    "LevelId",
    "Lit",
    "NameId",
    "Prelude",
    "PreludeCacheStats",
    "identity",
    "prelude_cache_enabled",
    "prelude_cache_stats",
    "theorem_inventory",
]


def theorem_inventory(kernel: Kernel, name_filter: str = "") -> list[tuple[str, int, str]]:
    """Every theorem in ``kernel``'s environment as ``(name, binders, type)``.

    This is the whole of the ``nat_theorem_inventory`` example binary, which
    exists only because there was no other way to ask: declarations go through a
    helper taking an interned ``NameId``, so grepping the source for
    ``.theorem("...")`` returns zero matches against 139 real Nat theorems.

    ``binders`` is counted off the *rendered* telescope, exactly as the example
    does, so it describes what a consumer pasting the string will see.

    An empty result for a non-empty ``name_filter`` is a **failed** lookup, not
    an empty report -- the caller must treat it as one, which is why this returns
    the rows rather than printing them.
    """
    rows = [
        (name, kernel.render_lean(declaration.ty).count("->"), kernel.render_lean(declaration.ty))
        for name, declaration in kernel.declarations()
        if declaration.kind == "theorem" and (not name_filter or name_filter in name)
    ]
    rows.sort()
    return rows
