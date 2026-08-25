"""Hypothesis properties for ``axeyum.kernel``: typing, epochs, and forks.

The kernel is the trusted base -- what it accepts is what "admitted" means here
-- so the properties are the ones whose failure would be silent: a type that is
inferred but not a `Sort`, a handle that crosses between kernels and denotes a
*different* term rather than raising, and a fork that leaks a declaration back
into its parent.

Handles are the sharp edge. `ExprId`/`NameId`/`LevelId` are indices into one
kernel's tables; the Rust API does not stop you mixing them, so a handle from
kernel A used against kernel B would name whatever happens to sit at that index
-- not an error, a wrong answer. The binding's epoch check is the only thing
standing between a caller and that, which is why it is asserted here over
*every* consuming method rather than over one representative.
"""

from __future__ import annotations

import pytest
from hypothesis import given
from hypothesis import strategies as st

import axeyum
from axeyum import kernel

# Every `Kernel` method below takes at least one handle. The list is spelled out
# rather than discovered, so a new consuming method has to be added here
# deliberately -- an epoch check that was never wired up on a new method is the
# gap this test exists to close.
UNARY_EXPR_METHODS = (
    "infer",
    "whnf",
    "expr_node",
    "has_fvars",
    "has_loose_bvars",
    "num_loose_bvars",
    "render_lean",
    "loose_bvar_range",
)


def build_level(builder: kernel.Kernel, shape: tuple) -> object:
    """Builds a universe level from a drawn shape tree."""
    kind = shape[0]
    if kind == "zero":
        return builder.level_zero()
    if kind == "param":
        return builder.level_param(builder.name(shape[1]))
    if kind == "succ":
        return builder.level_succ(build_level(builder, shape[1]))
    left = build_level(builder, shape[1])
    right = build_level(builder, shape[2])
    return builder.level_max(left, right) if kind == "max" else builder.level_imax(left, right)


levels = st.deferred(
    lambda: st.one_of(
        st.just(("zero",)),
        st.sampled_from([("param", "u"), ("param", "v")]),
        st.tuples(st.just("succ"), levels),
        st.tuples(st.sampled_from(["max", "imax"]), levels, levels),
    )
)


@given(shape=levels)
def test_type_of_a_sort_is_the_next_sort(shape: tuple) -> None:
    """``infer (Sort l) == Sort (l+1)``, definitionally, at every level."""
    k = kernel.Kernel()
    level = build_level(k, shape)
    inferred = k.infer(k.sort(level))
    assert k.expr_node(inferred).kind == "sort"
    assert k.def_eq(inferred, k.sort(k.level_succ(level))) is True


@given(domain=levels, codomain=levels)
def test_type_of_a_pi_of_sorts_is_a_sort(domain: tuple, codomain: tuple) -> None:
    """``infer (Sort a -> Sort b) == Sort (imax (a+1) (b+1))``.

    The `imax` (rather than `max`) is what makes `Prop` impredicative, so a
    kernel that used `max` here would be a different -- and inconsistent-with-
    Lean -- type theory while still inferring "a Sort".
    """
    k = kernel.Kernel()
    a = build_level(k, domain)
    b = build_level(k, codomain)
    pi = k.pi(k.name("A"), k.sort(a), k.sort(b))
    inferred = k.infer(pi)
    assert k.expr_node(inferred).kind == "sort"
    expected = k.sort(k.level_imax(k.level_succ(a), k.level_succ(b)))
    assert k.def_eq(inferred, expected) is True


@given(shape=levels, method=st.sampled_from(UNARY_EXPR_METHODS))
def test_expr_handles_never_cross_kernels(shape: tuple, method: str) -> None:
    """An `ExprId` from one kernel raises `EpochError` against another."""
    origin = kernel.Kernel()
    other = kernel.Kernel()
    expr = origin.sort(build_level(origin, shape))
    with pytest.raises(kernel.EpochError):
        getattr(other, method)(expr)
    # The same call against the kernel that minted it must succeed, or the test
    # above would pass for an unrelated reason (a method that always raises).
    getattr(origin, method)(expr)


@given(shape=levels)
def test_binary_and_builder_methods_check_epochs_too(shape: tuple) -> None:
    """`def_eq`, `app`, `pi`, `lam`, `sort` and `level_succ` all check."""
    origin = kernel.Kernel()
    other = kernel.Kernel()
    level = build_level(origin, shape)
    expr = origin.sort(level)
    name = origin.name("A")
    for call in (
        lambda: other.def_eq(expr, expr),
        lambda: other.app(expr, expr),
        lambda: other.pi(name, expr, expr),
        lambda: other.lam(name, expr, expr),
        lambda: other.sort(level),
        lambda: other.level_succ(level),
    ):
        with pytest.raises(kernel.EpochError):
            call()


@given(shape=levels)
def test_epoch_error_is_an_axeyum_error(shape: tuple) -> None:
    """`EpochError` is catchable through the root, so one `except` covers the
    binding."""
    origin = kernel.Kernel()
    other = kernel.Kernel()
    expr = origin.sort(build_level(origin, shape))
    with pytest.raises(axeyum.AxeyumError):
        other.infer(expr)


@given(name=st.sampled_from(["MyAxiom", "Foo.bar", "Nat.succ_ne_zero"]))
def test_fork_declarations_do_not_reach_the_parent(name: str) -> None:
    """A declaration added to a fork is invisible in the kernel it forked from.

    This is the property the fork exists for: a lane can try an admission
    without the trusted base of the original moving. A fork that leaked would
    change an axiom footprint by a side effect nobody looked at.
    """
    parent = kernel.Kernel()
    before = parent.declaration_count()
    fork = parent.fork()
    sort = fork.sort(fork.level_zero())
    fork.add_declaration(kernel.Declaration.axiom(fork.name(name), [], sort))

    assert fork.declaration_count() == before + 1
    assert parent.declaration_count() == before
    assert fork.contains(fork.name(name)) is True
    assert parent.contains(parent.name(name)) is False


def test_a_fork_is_a_new_epoch() -> None:
    """A fork rejects its parent's handles.

    A fork copies the parent's tables and then diverges, so an index valid in
    the parent is not guaranteed to denote the same term afterwards. The
    binding gives the fork a fresh epoch rather than letting the two share one
    -- the conservative choice, and the one a caller can rely on.
    """
    parent = kernel.Kernel()
    parent_sort = parent.sort(parent.level_zero())
    fork = parent.fork()
    with pytest.raises(kernel.EpochError):
        fork.infer(parent_sort)
    # ... and the fork can still do the same work with its own handles.
    assert fork.expr_node(fork.infer(fork.sort(fork.level_zero()))).kind == "sort"


def test_building_a_prelude_in_a_fork_leaves_the_parent_empty() -> None:
    """The isolation property at the scale it is actually used: a whole prelude."""
    parent = kernel.Kernel()
    fork = parent.fork()
    fork.build_logic_prelude()
    assert fork.declaration_count() > 0
    assert parent.declaration_count() == 0
