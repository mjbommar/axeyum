"""Shared bounded native CAS grammar with Python character diagnostics."""
from ._native.cas import Expr


class ParseError(ValueError):
    """Invalid CAS text, with zero-based character offsets."""
    def __init__(self, message: str, start: int, end: int):
        self.start, self.end = start, end
        super().__init__(f"{message} at [{start}:{end}]")


def parse(text: str) -> Expr:
    """Parse exact text with native byte/AST limits (ADR-6900)."""
    if not isinstance(text, str):
        raise TypeError("CAS text must be a string")
    try:
        encoded = text.encode('utf-8')
    except UnicodeEncodeError as error:
        raise ParseError("invalid Unicode encoding", error.start, error.end) from None
    expression, message, start, end = Expr._parse_text(text)
    if expression is None:
        # Byte caps can end inside a UTF-8 character; count completed prefixes.
        first = len(encoded[:start].decode('utf-8', errors='ignore'))
        last = len(encoded[:end].decode('utf-8', errors='ignore'))
        raise ParseError(message, first, last)
    return expression
