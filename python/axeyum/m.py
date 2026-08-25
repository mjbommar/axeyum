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
    "GCD",
    "LCM",
    "BellB",
    "BernoulliB",
    "Beta",
    "Binomial",
    "CatalanNumber",
    "ChebyshevT",
    "ChebyshevU",
    "ChineseRemainder",
    "CholeskyDecomposition",
    "ContinuedFraction",
    "D",
    "Degree",
    "Discriminant",
    "DivisorSigma",
    "Divisors",
    "Equal",
    "EulerPhi",
    "Expand",
    "Factor",
    "FactorInteger",
    "Fibonacci",
    "Gamma",
    "HermiteDecomposition",
    "HermiteH",
    "Integrate",
    "InverseLaplaceTransform",
    "InverseZTransform",
    "JacobiSymbol",
    "JordanDecomposition",
    "LaguerreL",
    "LaplaceTransform",
    "LegendreP",
    "Limit",
    "LucasL",
    "MatrixExp",
    "Mean",
    "Median",
    "ModularInverse",
    "MoebiusMu",
    "MultiplicativeOrder",
    "N",
    "NRoots",
    "NextPrime",
    "PartitionsP",
    "PolynomialQuotientRemainder",
    "PowerMod",
    "Prime",
    "PrimePi",
    "PrimeQ",
    "PrimitiveRoot",
    "QRDecomposition",
    "Rationalize",
    "Reduce",
    "ReplaceAll",
    "Resultant",
    "Series",
    "Simplify",
    "SmithDecomposition",
    "Solve",
    "StandardDeviation",
    "StirlingS1",
    "StirlingS2",
    "Substitute",
    "Sum",
    "Together",
    "TrigSimplify",
    "Variance",
    "ZTransform",
    "Zeta",
    "interval",
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
_NOT_SYMBOLS = {
    "pi": "`pi` is not a symbol here: the CAS is exact over Q and has no transcendental constant; use a variable name or N()",
    "Pi": "`Pi` is not a symbol here: the CAS is exact over Q and has no transcendental constant",
    "E": "`E` is not a symbol here; write exp(1) or use a variable name",
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
        if node.id in _NOT_SYMBOLS:
            raise ValueError(_NOT_SYMBOLS[node.id])
        if node.id == "I":
            return Expr.imaginary_unit()
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
                raise ValueError(
                    "exponents must be non-negative integer literals: the Rust `CasExpr::Pow` "
                    "carries a u32, so a symbolic power such as 2^k is not representable yet"
                )
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


def Expand(expr: str | Expr) -> Expr | None:
    """``Expand[e]``; ``None`` when the Rust expander declines (overflow)."""
    return cas.expand(parse(expr))


def Factor(expr: str | Expr, var: str | None = None) -> Expr | None:
    """``Factor[e]``; ``None`` when the Rust factoriser declines (e.g. irreducible over Q is returned as is, overflow is ``None``)."""
    e = parse(expr)
    return cas.factor(e, _var(e, var))


def Together(expr: str | Expr) -> Expr | None:
    """``Together[e]`` / ``Cancel`` -- one rational function with common factors cancelled."""
    return cas.cancel(parse(expr))


def TrigSimplify(expr: str | Expr) -> Expr:
    """``TrigSimplify[e]``."""
    return cas.trigsimp(parse(expr))


def D(expr: str | Expr, var: str | None = None, n: int = 1) -> Expr:
    """``D[e, x]`` (or ``D[e, {x, n}]``), simplified."""
    e = parse(expr)
    v = _var(e, var)
    return cas.simplify(e.differentiate_n(v, n) if n != 1 else e.differentiate(v))


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
    elif isinstance(point, float):
        raise TypeError("a finite limit point must be exact: an int or Fraction, not a float")
    elif isinstance(point, str):
        raise ValueError(f"unknown limit point {point!r}; use a number, 'inf' or '-inf'")
    else:
        p = cas.LimitPoint.finite(point)
    return cas.limit(e, _var(e, var), p)


def N(expr: str | Expr, **values: float) -> float | None:
    """``N[e /. {x -> 2.5}]`` -- floating evaluation; ``None`` outside the evaluable fragment."""
    return cas.evalf(parse(expr), dict(values))


def Equal(a: str | Expr, b: str | Expr) -> bool:
    """``a == b`` as MATHEMATICS, not as trees: a certified zero-test of ``a - b``.

    ``m.parse("1 + x") == m.parse("x + 1")`` is ``False`` (structural
    equality, which is what ``==`` on ``Expr`` means); ``Equal`` asks the CAS
    and returns ``True`` only for ``ZeroTest.Certified`` with ``equal``; an
    ``Unknown`` (outside the decidable fragment, or overflow) raises
    ``ValueError`` rather than answering ``False`` -- "could not decide" is not
    "not equal".
    """
    verdict = cas.equal(parse(a), parse(b))
    if verdict.certainty() != cas.Certainty.Certified:
        raise ValueError(
            f"equality of {show(parse(a))} and {show(parse(b))} is undecided: {verdict}"
        )
    return bool(verdict.equal)


def Substitute(expr: str | Expr, **values: str | Expr | int) -> Expr:
    """``e /. {x -> 2, y -> z + 1}``; values may be strings, ``Expr`` or ints."""
    e = parse(expr)
    for name, value in values.items():
        e = e.substitute(name, Expr.int(value) if isinstance(value, int) else parse(value))
    return e


ReplaceAll = Substitute


def _solve_system(
    equations: list[str | Expr], variables: list[str]
) -> list[dict[str, Expr]] | None:
    exprs = [parse(eq) for eq in equations]
    if len(variables) == 2 and len(exprs) == 2:
        pairs = cas.solve_polynomial_system(exprs[0], exprs[1], variables[0], variables[1])
        if pairs is not None:
            return [{variables[0]: a, variables[1]: b} for a, b in pairs]
    rows = cas.solve_linear_system(exprs, variables)
    if rows is None:
        return None
    return [dict(rows)]


def Solve(
    expr: str | Expr | list[str | Expr], var: str | list[str] | None = None
) -> list[Expr] | list[dict[str, Expr]] | None:
    """``Solve[e == 0, x]`` for one expression; ``Solve[{e1, e2}, {x, y}]`` for a system.

    A system returns ``[{"x": Expr, "y": Expr}, ...]`` -- every solution the
    Rust solver found -- via the bivariate polynomial solver when there are
    exactly two equations in two unknowns, else the linear solver. ``None``
    when Rust declines (a univariate solve in a multivariate expression, a
    nonlinear system it does not cover).
    """
    if isinstance(expr, list):
        if not isinstance(var, list) or not var:
            raise TypeError("a system needs its variables as a list, e.g. Solve([...], ['x', 'y'])")
        return _solve_system(expr, var)
    e = parse(expr)
    if isinstance(var, list):
        raise TypeError("one expression takes one variable, not a list")
    return cas.solve(e, _var(e, var))


def Integrate(
    expr: str | Expr, var: str | tuple[str, str | Expr | int, str | Expr | int] | None = None
) -> Expr | None:
    """``Integrate[e, x]`` (antiderivative) or ``Integrate[e, {x, a, b}]`` as ``var=("x", a, b)``.

    Both carry certificates on the Rust result (`cas.integrate(...).certificate`,
    `cas.definite_integrate(...)`); this returns the expression or value.
    """
    e = parse(expr)
    if isinstance(var, tuple):
        name, lower, upper = var
        lo = Expr.int(lower) if isinstance(lower, int) else parse(lower)
        hi = Expr.int(upper) if isinstance(upper, int) else parse(upper)
        result = cas.definite_integrate(e, name, lo, hi)
        return None if result is None else result.value
    result = cas.integrate(e, _var(e, var))
    return None if result is None else result.antiderivative


def Sum(
    expr: str | Expr,
    var: str | tuple[str, str | Expr | int, str | Expr | int | None] | None = None,
) -> Expr | None:
    """``Sum[f, {k, a, b}]`` as ``var=("k", a, b)``; ``b=None`` (or ``"inf"``) is the infinite sum; a bare ``var`` is the indefinite sum.

    Exact: ``Sum("k^2", ("k", 1, "n"))`` is ``n^3/3 + n^2/2 + n/6``. ``None`` when the
    Rust summation declines (outside the polynomial / hypergeometric fragment).
    """
    e = parse(expr)
    if isinstance(var, tuple):
        name, lower, upper = var
        lo = Expr.int(lower) if isinstance(lower, int) else parse(lower)
        if upper is None or (isinstance(upper, str) and upper.strip().lower() in _INFINITIES):
            return cas.infinite_sum(e, name, lo)
        hi = Expr.int(upper) if isinstance(upper, int) else parse(upper)
        return cas.definite_sum(e, name, lo, hi)
    name = _var(e, var)
    result = cas.sum_polynomial(e, name)
    return result if result is not None else cas.gosper_sum(e, name)


_INEQ = re.compile(r"(<=|>=|<|>)")


def Reduce(inequality: str, var: str | None = None) -> list[cas.RealInterval] | None:
    """``Reduce[p < 0, x]`` over the reals: the solution set as disjoint intervals.

    Accepts ``"x^2 - 4 < 0"`` or ``"x^2 < 4"`` (one of ``<``, ``<=``, ``>``, ``>=``);
    the difference of the sides is what is compared with zero. ``None`` when the
    Rust solver declines (not a polynomial in ``var``).
    """
    parts = _INEQ.split(inequality)
    if len(parts) != 3:
        raise ValueError(f"expected exactly one of <, <=, >, >= in {inequality!r}")
    lhs, op, rhs = parts
    e = parse(lhs) - parse(rhs)
    return cas.solve_polynomial_inequality(e, _var(e, var), op)


def interval(i: cas.RealInterval, var: str = "x") -> str:
    """``-2 < x < 2`` for a :class:`~axeyum.cas.RealInterval`, with ``inf`` ends dropped."""
    lo, hi = i.lower, i.upper
    left = "" if lo is None or str(lo) == "-inf" else f"{lo} {'<=' if i.lower_closed else '<'} "
    right = "" if hi is None or str(hi) == "inf" else f" {'<=' if i.upper_closed else '<'} {hi}"
    return f"{left}{var}{right}" if (left or right) else "all reals"


def Rationalize(value: float, max_denominator: int = 10**6) -> Expr | None:
    """``Rationalize[0.5]`` -> ``1/2``: the symbolic value a float stands for, or ``None``."""
    return cas.nsimplify(value, max_denominator)


def NRoots(expr: str | Expr, var: str | None = None, digits: int = 6) -> list[Fraction] | None:
    """``NRoots[p, x]`` -- every real root as a rational within ``10**-digits``, ascending (Sturm-isolated, exact bounds)."""
    e = parse(expr)
    return cas.approximate_real_roots(e, _var(e, var), cas.Rational(1, 10**digits))


def Degree(expr: str | Expr, var: str | None = None) -> int | None:
    """``Exponent[p, x]`` -- the degree, or ``None`` when ``p`` is not a polynomial in ``x``."""
    e = parse(expr)
    return cas.degree(e, _var(e, var))


def Resultant(a: str | Expr, b: str | Expr, var: str) -> Expr | None:
    """``Resultant[a, b, x]``."""
    return cas.resultant(parse(a), parse(b), var)


def Discriminant(expr: str | Expr, var: str | None = None) -> Expr | None:
    """``Discriminant[p, x]``."""
    e = parse(expr)
    return cas.discriminant(e, _var(e, var))


def PolynomialQuotientRemainder(a: str | Expr, b: str | Expr, var: str) -> tuple[Expr, Expr] | None:
    """``PolynomialQuotientRemainder[a, b, x]`` -> ``(quotient, remainder)``."""
    return cas.poly_div(parse(a), parse(b), var)


# ---------------------------------------------------------------------------
# The long tail: number theory, combinatorics, statistics, special functions,
# transforms and matrix normal forms (coverage-plan slice S5).
#
# Every verb below is a thin renaming of one `axeyum.cas` function -- the
# Mathematica spelling for a call the Rust surface already has. None of them
# adds semantics, and every one keeps the `None` the CAS returns for *outside
# the fragment or i128 overflow*. A verb that quietly substituted a default
# there would be inventing an answer, which is the one thing this layer must
# never do.
# ---------------------------------------------------------------------------


def PrimeQ(n: int) -> bool:
    """``PrimeQ[n]``."""
    return cas.is_prime(n)


def FactorInteger(n: int) -> list[tuple[int, int]]:
    """``FactorInteger[n]`` -> ``[(prime, exponent), ...]``; ``[]`` for 0 and 1."""
    return cas.factorize(n)


def Divisors(n: int) -> list[int]:
    """``Divisors[n]``, ascending."""
    return cas.divisors(n)


def DivisorSigma(k: int, n: int) -> int | None:
    """``DivisorSigma[k, n]`` -- the sum of the ``k``-th powers of the divisors."""
    return cas.sigma_k(k, n)


def EulerPhi(n: int) -> int:
    """``EulerPhi[n]``."""
    return cas.euler_phi(n)


def MoebiusMu(n: int) -> int:
    """``MoebiusMu[n]``."""
    return cas.mobius(n)


def GCD(a: int, b: int) -> int:
    """``GCD[a, b]``."""
    return cas.gcd(a, b)


def LCM(a: int, b: int) -> int | None:
    """``LCM[a, b]``; ``None`` on ``i128`` overflow."""
    return cas.lcm(a, b)


def PowerMod(base: int, exponent: int, modulus: int) -> int | None:
    """``PowerMod[b, e, m]``; ``None`` for a non-positive modulus."""
    return cas.mod_pow(base, exponent, modulus)


def ModularInverse(a: int, modulus: int) -> int | None:
    """``ModularInverse[a, m]``; ``None`` when ``a`` and ``m`` are not coprime."""
    return cas.mod_inverse(a, modulus)


def ChineseRemainder(residues: list[int], moduli: list[int]) -> tuple[int, int] | None:
    """``ChineseRemainder[r, m]`` -> ``(residue, modulus)``; ``None`` when inconsistent."""
    return cas.crt(list(zip(residues, moduli, strict=True)))


def JacobiSymbol(a: int, n: int) -> int:
    """``JacobiSymbol[a, n]``."""
    return cas.jacobi_symbol(a, n)


def PrimitiveRoot(n: int) -> int | None:
    """``PrimitiveRoot[n]``; ``None`` when the unit group is not cyclic."""
    return cas.primitive_root(n)


def MultiplicativeOrder(a: int, n: int) -> int | None:
    """``MultiplicativeOrder[a, n]``; ``None`` when ``a`` and ``n`` are not coprime."""
    return cas.multiplicative_order(a, n)


def ContinuedFraction(value: Fraction | tuple[int, int]) -> list[int]:
    """``ContinuedFraction[p/q]``; takes a ``Fraction`` or a ``(num, den)`` pair."""
    if isinstance(value, tuple):
        num, den = value
    else:
        num, den = value.numerator, value.denominator
    return cas.continued_fraction(num, den)


def NextPrime(n: int) -> int | None:
    """``NextPrime[n]``."""
    return cas.next_prime(n)


def Prime(k: int) -> int | None:
    """``Prime[k]`` -- the ``k``-th prime, one-based."""
    return cas.nth_prime(k)


def PrimePi(n: int) -> int:
    """``PrimePi[n]``."""
    return cas.prime_pi(n)


def Binomial(n: int, k: int) -> int | None:
    """``Binomial[n, k]``; ``0`` outside ``0 <= k <= n``, ``None`` on overflow."""
    return cas.binomial(n, k)


def Fibonacci(n: int) -> int | None:
    """``Fibonacci[n]``; ``None`` past the ``i128`` ceiling."""
    return cas.fibonacci(n)


def LucasL(n: int) -> int | None:
    """``LucasL[n]``."""
    return cas.lucas(n)


def CatalanNumber(n: int) -> int | None:
    """``CatalanNumber[n]``."""
    return cas.catalan(n)


def BellB(n: int) -> int | None:
    """``BellB[n]``."""
    return cas.bell(n)


def PartitionsP(n: int) -> int | None:
    """``PartitionsP[n]``."""
    return cas.partition_count(n)


def BernoulliB(n: int) -> Fraction | None:
    """``BernoulliB[n]``, exact.

    The convention is the Bernoulli numbers of the *first kind*: ``B(1)`` is
    ``-1/2``, matching the generating function ``x / (exp(x) - 1)``. SymPy
    (>= 1.13) returns ``+1/2`` there; every other index agrees.
    """
    return cas.bernoulli(n)


def StirlingS1(n: int, k: int) -> int | None:
    """``StirlingS1[n, k]``, unsigned."""
    return cas.stirling_first(n, k)


def StirlingS2(n: int, k: int) -> int | None:
    """``StirlingS2[n, k]``."""
    return cas.stirling_second(n, k)


def Mean(data: list[Fraction | int]) -> Fraction | None:
    """``Mean[data]``, exact; ``None`` for an empty sample."""
    return cas.mean(data)


def Median(data: list[Fraction | int]) -> Fraction | None:
    """``Median[data]``, exact."""
    return cas.median(data)


def Variance(data: list[Fraction | int], population: bool = False) -> Fraction | None:
    """``Variance[data]`` -- the SAMPLE variance by default, as in Mathematica.

    Pass ``population=True`` for the divisor-``n`` form.
    """
    return cas.variance(data) if population else cas.sample_variance(data)


def StandardDeviation(data: list[Fraction | int], population: bool = False) -> Expr | None:
    """``StandardDeviation[data]`` -- the sample form by default, as in Mathematica."""
    return cas.standard_deviation(data) if population else cas.sample_standard_deviation(data)


def Gamma(x: Fraction | int) -> Expr | None:
    """``Gamma[x]`` at an exact rational; ``None`` outside the closed-form fragment."""
    return cas.gamma(x)


def Beta(x: Fraction | int, y: Fraction | int) -> Expr | None:
    """``Beta[x, y]``."""
    return cas.beta(x, y)


def Zeta(s: int) -> Expr | None:
    """``Zeta[s]`` at an integer; ``None`` where no closed form is known (``Zeta[3]``)."""
    return cas.zeta(s)


def LegendreP(n: int, var: str = "x") -> Expr | None:
    """``LegendreP[n, x]``."""
    return cas.legendre(n, var)


def ChebyshevT(n: int, var: str = "x") -> Expr | None:
    """``ChebyshevT[n, x]``."""
    return cas.chebyshev_t(n, var)


def ChebyshevU(n: int, var: str = "x") -> Expr | None:
    """``ChebyshevU[n, x]``."""
    return cas.chebyshev_u(n, var)


def HermiteH(n: int, var: str = "x") -> Expr | None:
    """``HermiteH[n, x]`` -- the physicists' Hermite polynomial."""
    return cas.hermite(n, var)


def LaguerreL(n: int, var: str = "x") -> Expr | None:
    """``LaguerreL[n, x]``."""
    return cas.laguerre(n, var)


def LaplaceTransform(expr: str | Expr, t: str = "t", s: str = "s") -> Expr | None:
    """``LaplaceTransform[f, t, s]``; ``None`` outside the transform table."""
    return cas.laplace_transform(parse(expr), t, s)


def InverseLaplaceTransform(expr: str | Expr, s: str = "s", t: str = "t") -> Expr | None:
    """``InverseLaplaceTransform[F, s, t]``."""
    return cas.inverse_laplace(parse(expr), s, t)


def ZTransform(expr: str | Expr, n: str = "n", z: str = "z") -> Expr | None:
    """``ZTransform[f, n, z]``."""
    return cas.z_transform(parse(expr), n, z)


def InverseZTransform(expr: str | Expr, z: str = "z", n: str = "n") -> Expr | None:
    """``InverseZTransform[F, z, n]``."""
    return cas.inverse_z_transform(parse(expr), z, n)


def JordanDecomposition(m: cas.Matrix, var: str = "t") -> tuple[cas.Matrix, cas.Matrix] | None:
    """``JordanDecomposition[m]`` -> ``(P, J)`` with ``m == P J P^-1``; ``None`` when none exists over Q."""
    return cas.jordan_form(m, var)


def MatrixExp(m: cas.Matrix, t: str = "t") -> cas.Matrix | None:
    """``MatrixExp[m t]``."""
    return cas.matrix_exp(m, t)


def HermiteDecomposition(m: cas.Matrix) -> tuple[cas.Matrix, cas.Matrix] | None:
    """``HermiteDecomposition[m]`` -> ``(U, H)`` with ``U m == H``."""
    return cas.hermite_normal_form(m)


def SmithDecomposition(
    m: cas.Matrix,
) -> tuple[cas.Matrix, cas.Matrix, cas.Matrix] | None:
    """``SmithDecomposition[m]`` -> ``(U, D, V)`` with ``U m V == D``."""
    return cas.smith_normal_form(m)


def QRDecomposition(m: cas.Matrix) -> tuple[cas.Matrix, cas.Matrix] | None:
    """``QRDecomposition[m]`` -> ``(Q, R)`` with ``m == Q R``."""
    return cas.qr_decomposition(m)


def CholeskyDecomposition(m: cas.Matrix) -> cas.Matrix | None:
    """``CholeskyDecomposition[m]`` -> ``L`` with ``m == L L^T``; ``None`` when not SPD over Q."""
    return cas.cholesky_decomposition(m)
