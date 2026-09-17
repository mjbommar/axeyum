"""The C integer semantics the lifter encodes, each pinned by a test that names it.

These run on the standard library alone. The end-to-end sweep (cindergraph,
``axeyum_cli``, a C compiler) is ``check.py``; its exit status is the gate.

    python3 python/examples/cindergraph_defects/test_lift.py
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from lift import (
    INT,
    LONG,
    UINT,
    ULONG,
    CType,
    Term,
    as_bool,
    convert,
    parse_ctype,
    promote,
    usual_arithmetic,
)  # noqa: E402


class Conversions(unittest.TestCase):
    def test_short_promotes_to_int(self) -> None:
        self.assertEqual(promote(CType(16, False)), INT)
        self.assertEqual(promote(CType(8, True)), INT)

    def test_int_and_unsigned_int_is_unsigned(self) -> None:
        # C17 §6.3.1.8: same rank, one unsigned → the unsigned type. This is the
        # rule behind `if (len > 256)` with `int len` against `size_t` bounds.
        self.assertEqual(usual_arithmetic(INT, UINT), UINT)

    def test_long_and_unsigned_int_is_long(self) -> None:
        # The wider signed type represents every unsigned int, so it wins.
        self.assertEqual(usual_arithmetic(LONG, UINT), LONG)
        self.assertEqual(usual_arithmetic(UINT, LONG), LONG)

    def test_int_and_unsigned_long_is_unsigned_long(self) -> None:
        self.assertEqual(usual_arithmetic(INT, ULONG), ULONG)

    def test_widening_signed_sign_extends(self) -> None:
        self.assertEqual(convert(Term("x", INT), LONG).smt, "((_ sign_extend 32) x)")

    def test_widening_unsigned_zero_extends(self) -> None:
        self.assertEqual(convert(Term("x", UINT), LONG).smt, "((_ zero_extend 32) x)")

    def test_narrowing_keeps_the_low_bits(self) -> None:
        self.assertEqual(convert(Term("n", ULONG), CType(16, False)).smt, "((_ extract 15 0) n)")

    def test_same_width_reinterprets(self) -> None:
        self.assertEqual(convert(Term("x", INT), UINT).smt, "x")

    def test_condition_to_int_is_ite(self) -> None:
        self.assertEqual(
            convert(Term("(bvult a b)", None), INT).smt, "(ite (bvult a b) (_ bv1 32) (_ bv0 32))"
        )

    def test_int_to_condition_is_nonzero(self) -> None:
        self.assertEqual(as_bool(Term("x", UINT)).smt, "(not (= x (_ bv0 32)))")


class Types(unittest.TestCase):
    def test_typedefs_and_qualifiers(self) -> None:
        self.assertEqual(parse_ctype("const size_t", 1), ULONG)
        self.assertEqual(parse_ctype("uint8_t", 1), CType(8, False))
        self.assertEqual(parse_ctype("long long", 1), LONG)

    def test_pointers_are_refused_not_guessed(self) -> None:
        from lift import Refused

        with self.assertRaises(Refused):
            parse_ctype("unsigned char *", 7)


class Literals(unittest.TestCase):
    def _lit(self, text: str):
        # Drive the literal rule without cindergraph: a one-node fake AST.
        from lift import Lifter, _Ast

        ast = _Ast(
            text,
            {
                "nodes": [
                    {
                        "id": 0,
                        "tag": "literal",
                        "label": f"literal\n{text}",
                        "span": f"0:{len(text)}",
                    }
                ],
                "edges": [],
            },
        )
        lifter = Lifter.__new__(Lifter)
        lifter.ast = ast
        lifter.src = text
        return lifter.literal(0)

    def test_suffixes_select_the_type(self) -> None:
        self.assertEqual(self._lit("0x7fffffffu").ctype, UINT)
        self.assertEqual(self._lit("10UL").ctype, ULONG)
        self.assertEqual(self._lit("2147483648").ctype, LONG)  # does not fit int
        self.assertEqual(self._lit("16").ctype, INT)
        self.assertEqual(self._lit("'a'").ctype, INT)

    def test_values(self) -> None:
        self.assertEqual(self._lit("0x10").smt, "(_ bv16 32)")
        self.assertEqual(self._lit("010").smt, "(_ bv8 32)")


if __name__ == "__main__":
    unittest.main()
