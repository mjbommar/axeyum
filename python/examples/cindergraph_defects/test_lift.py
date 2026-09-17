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
)


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


def _fake(text: str, nodes: list[tuple], attrs: dict | None = None):
    """A cindergraph-shaped AST without cindergraph: ``(id, tag, label, start, end, parent)``.

    Extra attributes for a node (``op``, ``ops``) come in ``attrs={id: {...}}``;
    the export's newer fields look exactly like that.
    """
    from lift import Lifter, _Ast

    doc: dict = {"nodes": [], "edges": []}
    for i, tag, label, start, end, parent in nodes:
        node = {"id": i, "tag": tag, "label": f"{tag}\n{label}", "span": f"{start}:{end}"}
        node.update((attrs or {}).get(i, {}))
        doc["nodes"].append(node)
        if parent is not None:
            doc["edges"].append({"source": parent, "target": i, "label": ""})
    return Lifter(text, _Ast(text, doc), 0)


def _state(**env):
    from lift import PathState

    return PathState(env={k: Term(k, t) for k, t in env.items()})


class Literals(unittest.TestCase):
    def _lit(self, text: str):
        # Drive the literal rule without cindergraph: a one-node fake AST.
        return _fake(text, [(0, "literal", text, 0, len(text), None)]).literal(0)

    def test_suffixes_select_the_type(self) -> None:
        self.assertEqual(self._lit("0x7fffffffu").ctype, UINT)
        self.assertEqual(self._lit("10UL").ctype, ULONG)
        self.assertEqual(self._lit("2147483648").ctype, LONG)  # does not fit int
        self.assertEqual(self._lit("16").ctype, INT)
        self.assertEqual(self._lit("'a'").ctype, INT)

    def test_values(self) -> None:
        self.assertEqual(self._lit("0x10").smt, "(_ bv16 32)")
        self.assertEqual(self._lit("010").smt, "(_ bv8 32)")


class Operators(unittest.TestCase):
    """The operator token: cindergraph's ``op`` attribute when present, else the gap."""

    def _binary(self, text: str, attrs: dict | None = None):
        #  a - b   (the gap between the two name_refs is the operator's home)
        nodes = [
            (0, "binary_expr", text, 0, len(text), None),
            (1, "name_ref", "a", 0, 1, 0),
            (2, "name_ref", "b", len(text) - 1, len(text), 0),
        ]
        return _fake(text, nodes, attrs)

    def test_gap_recovers_the_operator(self) -> None:
        lifter = self._binary("a - b")
        self.assertEqual(lifter.ast.binary_ops(0, [1, 2]), ["-"])

    def test_op_attribute_wins_over_the_gap(self) -> None:
        # The spans lie (the gap reads "-") but the parser's own token says "+".
        lifter = self._binary("a - b", {0: {"op": "+"}})
        self.assertEqual(lifter.ast.binary_ops(0, [1, 2]), ["+"])

    def test_ops_attribute_on_a_flat_chain(self) -> None:
        text = "a + b - c"
        nodes = [
            (0, "binary_expr", text, 0, len(text), None),
            (1, "name_ref", "a", 0, 1, 0),
            (2, "name_ref", "b", 4, 5, 0),
            (3, "name_ref", "c", 8, 9, 0),
        ]
        lifter = _fake(text, nodes, {0: {"ops": ["+", "-"]}})
        self.assertEqual(lifter.ast.binary_ops(0, [1, 2, 3]), ["+", "-"])
        # Without the attribute the gaps still say the same thing.
        self.assertEqual(_fake(text, nodes).ast.binary_ops(0, [1, 2, 3]), ["+", "-"])

    def test_prefix_op_attribute(self) -> None:
        text = "-x"
        nodes = [(0, "unary_expr", text, 0, 2, None), (1, "name_ref", "x", 1, 2, 0)]
        self.assertEqual(_fake(text, nodes).ast.prefix_op(0, 1), "-")
        self.assertEqual(_fake(text, nodes, {0: {"op": "~"}}).ast.prefix_op(0, 1), "~")


class Obligations(unittest.TestCase):
    def _lifter(self, text: str = "x"):
        return _fake(text, [(0, "name_ref", text, 0, len(text), None)])

    def _kinds(self, state) -> list[str]:
        return [ob.kind for ob in state.obligations]

    def test_unsigned_wrap_is_an_obligation_only_inside_an_allocation_size(self) -> None:
        lifter = self._lifter()
        st = _state(a=UINT, b=UINT)
        lifter.apply("*", Term("a", UINT), Term("b", UINT), 0, st)
        self.assertEqual(self._kinds(st), [])  # plain unsigned wrap is defined behaviour
        lifter.alloc_depth = 1
        lifter.apply("*", Term("a", UINT), Term("b", UINT), 0, st)
        lifter.apply("+", Term("a", UINT), Term("b", UINT), 0, st)
        self.assertEqual(self._kinds(st), ["alloc-size-wrap", "alloc-size-wrap"])
        self.assertEqual(st.obligations[0].holds, "(not (bvumulo a b))")
        self.assertEqual(st.obligations[1].holds, "(not (bvuaddo a b))")

    def test_signed_arithmetic_inside_an_allocation_is_still_signed_overflow(self) -> None:
        lifter = self._lifter()
        lifter.alloc_depth = 1
        st = _state(a=INT, b=INT)
        lifter.apply("*", Term("a", INT), Term("b", INT), 0, st)
        self.assertEqual(self._kinds(st), ["signed-overflow"])

    def test_uninitialised_read_is_a_finding_until_a_store_reaches_it(self) -> None:
        lifter = self._lifter("x")
        st = _state(x=INT)
        st.uninit.add("x")
        lifter.name_ref(0, st)
        self.assertEqual(self._kinds(st), ["uninitialized"])
        self.assertEqual(st.obligations[0].holds, "false")  # reaching the read IS the finding
        lifter.store("x", INT, Term("(_ bv1 32)", INT), 0, st)
        lifter.name_ref(0, st)
        self.assertEqual(self._kinds(st), ["uninitialized"])  # no second one after the store

    def test_null_is_a_64_bit_zero(self) -> None:
        lifter = self._lifter("NULL")
        self.assertEqual(lifter.name_ref(0, _state()), Term("(_ bv0 64)", ULONG))

    def test_a_pointer_as_a_value_is_an_unconstrained_address(self) -> None:
        lifter = self._lifter("p")
        lifter.pointers.add("p")
        self.assertEqual(lifter.name_ref(0, _state()), Term("p_addr", ULONG))
        self.assertIn(("p_addr", ULONG), lifter.consts)

    def test_negating_a_literal_has_no_obligation(self) -> None:
        text = "-1"
        nodes = [(0, "unary_expr", text, 0, 2, None), (1, "literal", "1", 1, 2, 0)]
        st = _state()
        self.assertEqual(_fake(text, nodes).unary(0, st), Term("(bvneg (_ bv1 32))", INT))
        self.assertEqual(self._kinds(st), [])
        text = "-x"
        nodes = [(0, "unary_expr", text, 0, 2, None), (1, "name_ref", "x", 1, 2, 0)]
        st = _state(x=INT)
        _fake(text, nodes).unary(0, st)
        self.assertEqual(self._kinds(st), ["signed-overflow"])
        self.assertEqual(st.obligations[0].holds, "(not (bvnego x))")

    def test_prefix_and_postfix_increment_values(self) -> None:
        text = "i++"
        nodes = [
            (0, "postfix_expr", text, 0, 3, None),
            (1, "name_ref", "i", 0, 1, 0),
            (2, "inc_dec_suffix", "++", 1, 3, 0),
        ]
        st = _state(i=INT)
        self.assertEqual(_fake(text, nodes).postfix(0, st), Term("i", INT))  # the old value
        self.assertEqual(st.env["i"], Term("i_1", INT))
        self.assertEqual(st.defs[-1], ("i_1", INT, "(bvadd i (_ bv1 32))"))
        text = "++i"
        nodes = [(0, "unary_expr", text, 0, 3, None), (1, "name_ref", "i", 2, 3, 0)]
        st = _state(i=INT)
        self.assertEqual(_fake(text, nodes).unary(0, st), Term("i_1", INT))  # the new value

    def test_pointer_arithmetic_counts_elements(self) -> None:
        text = "p + k"
        nodes = [
            (0, "binary_expr", text, 0, 5, None),
            (1, "name_ref", "p", 0, 1, 0),
            (2, "name_ref", "k", 4, 5, 0),
        ]
        lifter = _fake(text, nodes)
        lifter.pointers.add("p")
        lifter.types["p[]"] = UINT
        name, off, scale = lifter.pointer_arith(0, _state(k=INT))
        self.assertEqual((name, off, scale), ("p", Term("k", INT), 4))
        del lifter.types["p[]"]  # an unknown element type is a byte pointer
        self.assertEqual(lifter.pointer_arith(0, _state(k=INT))[2], 1)


class Declarations(unittest.TestCase):
    def test_every_declarator_is_declared_with_its_own_initializer(self) -> None:
        #  int a = 1, b;   (one decl node, two declarators, one initializer)
        text = "int a = 1, b;"
        nodes = [
            (0, "decl", text, 0, 13, None),
            (1, "decl_specifiers", "int", 0, 3, 0),
            (2, "declarator", "declarator", 4, 5, 0),
            (3, "decl_name", "a", 4, 5, 2),
            (4, "initializer", "initializer", 6, 9, 0),
            (5, "literal", "1", 8, 9, 4),
            (6, "declarator", "declarator", 11, 12, 0),
            (7, "decl_name", "b", 11, 12, 6),
        ]
        st = _fake(text, nodes).decl(0, _state())
        self.assertEqual(st.env["a"], Term("a_1", INT))
        self.assertEqual(st.defs, [("a_1", INT, "(_ bv1 32)")])
        self.assertEqual(st.env["b"], Term("b_uninit", INT))
        self.assertEqual(st.uninit, {"b"})  # `b` has no initializer; `a` is not uninitialised


class Annotations(unittest.TestCase):
    def test_file_level_unroll(self) -> None:
        from lift import file_unroll

        self.assertEqual(file_unroll("// axeyum: unroll = 17\nint f(void) {}"), 17)
        self.assertIsNone(file_unroll("// axeyum: capacity(p) = n\n"))


if __name__ == "__main__":
    unittest.main()
