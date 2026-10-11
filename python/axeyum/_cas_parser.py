"""Bounded exact expression parser; never executes Python source."""
from fractions import Fraction
import re

from ._native.cas import Expr


class ParseError(ValueError):
    """Invalid CAS text, with zero-based source offsets."""
    def __init__(self, message: str, start: int, end: int):
        self.start, self.end = start, end
        super().__init__(f"{message} at [{start}:{end}]")


_TOKEN = re.compile(r"\s+|[0-9]+(?:\.[0-9]+)?|[A-Za-z_][A-Za-z_0-9]*|\*\*|[()+*/^\-]|π")
_UNARY = frozenset(("sin", "cos", "tan", "atan", "ln", "exp", "sqrt", "cbrt", "abs", "sign", "floor", "ceiling"))


def parse(text: str) -> Expr:
    """Parse exact arithmetic text into Expr. See ADR-3100 for grammar/limits."""
    if not isinstance(text, str):
        raise TypeError("CAS text must be a string")
    if len(text) > 8192:
        raise ParseError("source limit exceeded", 8192, len(text))
    tokens = []
    offset = 0
    while offset < len(text):
        match = _TOKEN.match(text, offset)
        if match is None:
            raise ParseError("unexpected character", offset, offset + 1)
        value = match.group()
        if not value.isspace():
            if len(tokens) == 512:
                raise ParseError("token limit exceeded", offset, match.end())
            if value[0].isdigit() and sum(c.isdigit() for c in value) > 1024:
                raise ParseError("literal digit limit exceeded", offset, match.end())
            tokens.append((value, offset, match.end()))
        offset = match.end()
    tokens.append(("", len(text), len(text)))
    index = nodes = 0

    def fail(message):
        _, start, end = tokens[index]
        raise ParseError(message, start, end)

    def take(value):
        nonlocal index
        if tokens[index][0] == value:
            index += 1
            return True
        return False

    def node(builder):
        nonlocal nodes
        nodes += 1
        if nodes > 64:
            fail("expression node limit exceeded")
        return builder()

    def expression(minimum=0, depth=0):
        nonlocal index
        if depth > 32:
            fail("expression depth limit exceeded")
        token = tokens[index][0]
        if token in ("+", "-"):
            index += 1
            inner = expression(3, depth + 1)
            left = node(lambda: -inner) if token == "-" else inner
        elif take("("):
            left = expression(0, depth + 1)
            if not take(")"):
                fail("expected closing parenthesis")
        elif token and token[0].isdigit():
            index += 1
            exact = Fraction(token)
            left = node(lambda: Expr.rat(exact.numerator, exact.denominator))
        elif token in ("pi", "π"):
            fail("symbolic pi constructor is not available")
        elif token and (token[0].isalpha() or token[0] == "_"):
            index += 1
            if tokens[index][0] == "(":
                if token not in _UNARY:
                    fail("unknown unary function")
                index += 1
                argument = expression(0, depth + 1)
                if not take(")"):
                    fail("expected closing parenthesis")
                left = node(lambda: getattr(argument, token)())
            else:
                left = node(lambda: Expr.var(token))
        else:
            fail("expected expression")
        while True:
            operator = tokens[index][0]
            precedence = {"+": 1, "-": 1, "*": 2, "/": 2, "^": 4, "**": 4}.get(operator, -1)
            if precedence < minimum:
                return left
            index += 1
            if operator in ("^", "**"):
                sign = -1 if take("-") else 1
                if sign == 1:
                    take("+")
                exponent = tokens[index][0]
                if not exponent or not exponent.isascii() or not exponent.isdigit():
                    fail("expected signed integer exponent")
                index += 1
                magnitude = int(exponent)
                if magnitude > 4294967295:
                    fail("exponent magnitude exceeds 4294967295")
                base = left
                left = node(lambda: base.pow(sign * magnitude))
                if tokens[index][0] in ("^", "**"):
                    fail("chained powers require parentheses")
            else:
                right = expression(precedence + 1, depth + 1)
                base = left
                if operator == "+":
                    left = node(lambda: base + right)
                elif operator == "-":
                    left = node(lambda: base - right)
                elif operator == "*":
                    left = node(lambda: base * right)
                else:
                    left = node(lambda: base / right)

    result = expression()
    if tokens[index][0]:
        fail("unexpected trailing token")
    return result
