"""``axeyum.m`` -- Mathematica-shaped verbs over :mod:`axeyum.cas` (tier R).

``M.Simplify("x*x + 5*x + 6")``, ``M.Factor("x^2 + 5 x + 6")``,
``M.Solve("x^2 - 4", "x")``. Three conveniences the Rust surface does not
have, all of them Python-side and none of them semantic:

* **a parser** -- an expression may be a ``str`` (Python/Mathematica-ish
  syntax: ``^`` or ``**`` for powers, implicit multiplication like ``5 x``,
  ``sin(x)``, ``sqrt(x)``, rationals ``1/3``) or an :class:`~axeyum.cas.Expr`;
* **variable inference** -- verbs that need a variable (``Factor``, ``Solve``,
  ``D``, ``Integrate``) take it from the expression when exactly one is free,
  and raise ``ValueError`` naming the candidates otherwise (never guess);
* **a printer** -- the Rust ``Display`` is faithful, not pretty
  (``(x - (-2))*(x - (-3))``); :func:`show` folds double negatives.

Everything returned is still a :class:`~axeyum.cas.Expr` (or ``None`` where
the Rust side declines -- outside the fragment, or ``i128`` overflow), so
certificates (``cas.equal``, ``cas.integrate(...).certificate``) remain
available on the result. This layer carries no authority of its own.
"""

from __future__ import annotations

import ast
import re
from collections.abc import Callable
from fractions import Fraction
from typing import Any

from . import cas
from .cas import Expr

__all__ = [
    "D",
    "Expand",
    "Factor",
    "Integrate",
    "Limit",
    "N",
    "Series",
    "Simplify",
    "Solve",
    "Together",
    "TrigSimplify",
    "parse",
    "show",
]

_FUNCS: dict[str, Callable[[Expr], Expr]] = {
    "sin": Expr.sin,
    "cos": Expr.cos,
    "tan": Expr.tan,
    "atan": Expr.atan,
    "exp": Expr.exp,
    "ln": Expr.ln,
    "log": Expr.ln,
    "sqrt": Expr.sqrt,
    "abs": Expr.abs,
    "erf": Expr.erf,
    "gamma": Expr.gamma,
}
_MMA_FUNCS = {
    "Sin": "sin",
    "Cos": "cos",
    "Tan": "tan",
    "Exp": "exp",
    "Log": "ln",
    "Sqrt": "sqrt",
    "Abs": "abs",
}


def _normalise(text: str) -> str:
    """Rewrites Mathematica-ish spellings into the Python subset :mod:`ast` reads."""
    s = text.strip()
    for name, py in _MMA_FUNCS.items():
        s = re.sub(rf"\b{name}\[", f"{py}(", s)
    s = s.replace("]", ")")
    s = s.replace("^", "**")
    # implicit multiplication: `5 x`, `2x`, `x y`, `)(`, `2(`, `x(` (a call
    # keeps its parenthesis only when the head is a known function name)
    s = re.sub(r"(\d)\s*([A-Za-z(])", r"\1*\2", s)
    s = re.sub(r"([A-Za-z_]\w*)\s+(?=[A-Za-z_(\d])", r"\1*", s)
    s = re.sub(r"\)\s*(?=[A-Za-z_(\d])", ")*", s)
    return s


def parse(text: str | Expr) -> Expr:
    """Builds an :class:`Expr` from a string, or returns an ``Expr`` unchanged.

    Raises ``ValueError`` for anything outside the supported grammar -- an
    unknown function head, a non-integer exponent, attribute access,
    comparisons -- and ``TypeError`` for a float literal (write a rational as
    ``1/3``).
    """
    if isinstance(text, Expr):
        return text
    if "=" in text:
        # An equation is its difference: `2x + 3 = 7` is the expression whose
        # roots solve it. `==` is accepted as the Python spelling; anything
        # else with `=` (`<=`, `>=`, `!=`, assignments) is outside the grammar.
        sides = re.split(r"(?<![<>!=])==?(?![=])", text)
        if len(sides) != 2 or any(op in text for op in ("<=", ">=", "!=")):
            raise ValueError(f"cannot parse {text!r}: expected one `=` between two expressions")
        return parse(sides[0]) - parse(sides[1])
    try:
        tree = ast.parse(_normalise(text), mode="eval")
    except SyntaxError as error:
        raise ValueError(f"cannot parse {text!r}: {error.msg}") from None
    return _build(tree.body)


def _build(node: ast.AST) -> Expr:
    if isinstance(node, ast.Constant):
        if isinstance(node.value, bool) or not isinstance(node.value, int):
            raise TypeError(
                f"only integer literals are accepted, got {node.value!r}; write a rational as p/q"
            )
        return Expr.int(node.value)
    if isinstance(node, ast.Name):
        return Expr.var(node.id)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return -_build(node.operand)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.UAdd):
        return _build(node.operand)
    if isinstance(node, ast.BinOp):
        left = _build(node.left)
        if isinstance(node.op, ast.Pow):
            if not (
                isinstance(node.right, ast.Constant)
                and isinstance(node.right.value, int)
                and node.right.value >= 0
            ):
                raise ValueError("exponents must be non-negative integer literals")
            return left.pow(node.right.value)
        right = _build(node.right)
        ops: dict[type, Callable[[Expr, Expr], Expr]] = {
            ast.Add: lambda a, b: a + b,
            ast.Sub: lambda a, b: a - b,
            ast.Mult: lambda a, b: a * b,
            ast.Div: lambda a, b: a / b,
        }
        try:
            return ops[type(node.op)](left, right)
        except KeyError:
            raise ValueError(f"unsupported operator {type(node.op).__name__}") from None
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and len(node.args) == 1:
        try:
            fn = _FUNCS[node.func.id]
        except KeyError:
            raise ValueError(
                f"unknown function {node.func.id!r}; known: {sorted(_FUNCS)}"
            ) from None
        return fn(_build(node.args[0]))
    raise ValueError(f"unsupported syntax: {ast.dump(node)[:60]}")


def _var(expr: Expr, var: str | None) -> str:
    if var is not None:
        return var
    names = sorted(expr.variables())
    if len(names) == 1:
        return names[0]
    raise ValueError(f"name the variable explicitly; the expression has {len(names)}: {names}")


_DOUBLE_NEG = re.compile(r"- \(-(\d+(?:/\d+)?)\)")
_PLUS_NEG = re.compile(r"\+ \(-(\d+(?:/\d+)?)\)")
_NEG_ONE_TIMES = re.compile(r"\(-1\)\*")


def show(expr: Expr | list[Expr] | None) -> str:
    """A readable rendering: ``(x + 2)*(x + 3)`` for what Rust prints as ``(x - (-2))*(x - (-3))``.

    Purely textual -- it folds ``- (-c)`` to ``+ c``, ``+ (-c)`` to ``- c``
    and ``(-1)*`` to ``-``. It never re-associates or re-orders, so what it
    prints is the Rust tree, spelled the way a person would.
    """
    if expr is None:
        return "None"
    if isinstance(expr, list):
        return "[" + ", ".join(show(e) for e in expr) + "]"
    s = str(expr)
    s = _DOUBLE_NEG.sub(r"+ \1", s)
    s = _PLUS_NEG.sub(r"- \1", s)
    s = _NEG_ONE_TIMES.sub("-", s)
    return s


_SIGNS = {"positive", "negative", "nonnegative", "nonzero"}


def _assumptions(assume: dict[str, str] | None) -> cas.Assumptions | None:
    if not assume:
        return None
    a = cas.Assumptions()
    for name, sign in assume.items():
        if sign not in _SIGNS:
            raise ValueError(f"assume[{name!r}] must be one of {sorted(_SIGNS)}, got {sign!r}")
        a = getattr(a, sign)(name)
    return a


def Simplify(expr: str | Expr, assume: dict[str, str] | None = None) -> Expr:
    """``Simplify[e]``, or ``Simplify[e, Assumptions -> x > 0]`` as ``assume={"x": "positive"}``.

    Without an assumption ``exp(ln(x))`` stays as it is, because it is only
    ``x`` for positive ``x``; with ``assume={"x": "positive"}`` it simplifies.
    Signs: ``positive``, ``negative``, ``nonnegative``, ``nonzero``.
    """
    e = parse(expr)
    a = _assumptions(assume)
    return cas.simplify(e) if a is None else cas.simplify_under_assumptions(e, a)


def Expand(expr: str | Expr) -> Expr:
    """``Expand[e]``."""
    return cas.expand(parse(expr))


def Factor(expr: str | Expr, var: str | None = None) -> Expr | None:
    """``Factor[e]``; ``None`` when the Rust factoriser declines (e.g. irreducible over Q is returned as is, overflow is ``None``)."""
    e = parse(expr)
    return cas.factor(e, _var(e, var))


def Together(expr: str | Expr) -> Expr:
    """``Together[e]`` / ``Cancel`` -- one rational function with common factors cancelled."""
    return cas.cancel(parse(expr))


def TrigSimplify(expr: str | Expr) -> Expr:
    """``TrigSimplify[e]``."""
    return cas.trigsimp(parse(expr))


def Solve(expr: str | Expr, var: str | None = None) -> list[Expr] | None:
    """``Solve[e == 0, x]`` -- roots of ``e`` in ``x`` (``None`` when the Rust solver declines)."""
    e = parse(expr)
    return cas.solve(e, _var(e, var))


def D(expr: str | Expr, var: str | None = None, n: int = 1) -> Expr:
    """``D[e, x]`` (or ``D[e, {x, n}]``), simplified."""
    e = parse(expr)
    v = _var(e, var)
    return cas.simplify(e.differentiate_n(v, n) if n != 1 else e.differentiate(v))


def Integrate(expr: str | Expr, var: str | None = None) -> Expr | None:
    """``Integrate[e, x]`` -- the antiderivative; its certificate is on ``cas.integrate(...)``."""
    e = parse(expr)
    result = cas.integrate(e, _var(e, var))
    return None if result is None else result.antiderivative


def Series(expr: str | Expr, var: str | None = None, order: int = 4) -> Expr | None:
    """``Series[e, {x, 0, n}]``."""
    e = parse(expr)
    return cas.series(e, _var(e, var), order)


_INFINITIES = {
    "inf": True,
    "+inf": True,
    "infinity": True,
    "oo": True,
    "-inf": False,
    "-infinity": False,
    "-oo": False,
}


def Limit(expr: str | Expr, point: Fraction | float | str, var: str | None = None) -> Any:
    """``Limit[e, x -> a]`` for a rational ``a``, or ``"inf"`` / ``"-inf"`` (also ``float("inf")``)."""
    e = parse(expr)
    if isinstance(point, str) and point.strip().lower() in _INFINITIES:
        positive = _INFINITIES[point.strip().lower()]
        p = cas.LimitPoint.pos_infinity() if positive else cas.LimitPoint.neg_infinity()
    elif isinstance(point, float) and point in (float("inf"), float("-inf")):
        p = cas.LimitPoint.pos_infinity() if point > 0 else cas.LimitPoint.neg_infinity()
    else:
        p = cas.LimitPoint.finite(point)
    return cas.limit(e, _var(e, var), p)


def N(expr: str | Expr, **values: float) -> float | None:
    """``N[e /. {x -> 2.5}]`` -- floating evaluation; ``None`` outside the evaluable fragment."""
    return cas.evalf(parse(expr), dict(values))
