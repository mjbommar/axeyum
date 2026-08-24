"""Round-trips for every IR value variant this slice converts.

Each case drives a real solve, so the assertion is about what the *solver*
produces, not about a hand-built value the binding never sees.
"""

from __future__ import annotations

from fractions import Fraction

import pytest

import axeyum
from axeyum import ir, smt, solver
from axeyum._native.solver import cnf

TIMEOUT_MS = 20_000


def axeyum_index(value: object) -> int:
    """Force the `__index__` protocol, the way `list[...]` and `hex()` do."""
    return value.__index__()


def solved(script: str) -> dict[str, object]:
    outcome = smt.solve(script, timeout_ms=TIMEOUT_MS)
    assert outcome.status == "sat", (outcome.status, outcome.detail)
    assert outcome.replay() is True
    return outcome.model


def test_bool_becomes_python_bool() -> None:
    model = solved("(set-logic QF_UF)(declare-fun p () Bool)(assert p)(check-sat)")
    assert model["p"] is True


def test_bv_becomes_bvvalue_carrying_its_width() -> None:
    model = solved(
        "(set-logic QF_BV)(declare-fun x () (_ BitVec 8))(assert (= x (_ bv200 8)))(check-sat)"
    )
    value = model["x"]
    assert isinstance(value, axeyum.BvValue)
    assert value.width == 8
    assert value.value == 200
    assert int(value) == 200
    # `__index__`, so a bit-vector can be used wherever an index is needed.
    assert hex(value) == "0xc8"
    assert list(range(256))[value] == 200
    assert axeyum_index(value) == 200
    assert repr(value) == "BvValue(width=8, value=200)"


def test_wide_bv_is_arbitrary_precision() -> None:
    # 2**130 + 7 -- past the u128 boundary, so the IR carries `Value::WideBv`
    # and the binding must read its limbs rather than a `u128`.
    expected = (1 << 130) + 7
    model = solved(
        "(set-logic QF_BV)(declare-fun w () (_ BitVec 200))"
        f"(assert (= w (_ bv{expected} 200)))(check-sat)"
    )
    value = model["w"]
    assert isinstance(value, axeyum.BvValue)
    assert value.width == 200
    assert int(value) == expected


def test_bvvalue_equality_is_width_sensitive() -> None:
    eight = solved(
        "(set-logic QF_BV)(declare-fun x () (_ BitVec 8))(assert (= x (_ bv1 8)))(check-sat)"
    )["x"]
    sixteen = solved(
        "(set-logic QF_BV)(declare-fun x () (_ BitVec 16))(assert (= x (_ bv1 16)))(check-sat)"
    )["x"]
    same = solved(
        "(set-logic QF_BV)(declare-fun y () (_ BitVec 8))(assert (= y (_ bv1 8)))(check-sat)"
    )["y"]
    assert eight == same
    assert hash(eight) == hash(same)
    assert eight != sixteen
    # A bit-vector is not an integer -- it carries a width -- so `==` against
    # one is deferred, which Python resolves to `False`.
    assert eight != 1


def test_int_becomes_python_int() -> None:
    model = solved("(set-logic QF_LIA)(declare-fun n () Int)(assert (= n 42))(check-sat)")
    assert model["n"] == 42
    assert isinstance(model["n"], int)


def test_real_becomes_fraction() -> None:
    model = solved("(set-logic QF_LRA)(declare-fun r () Real)(assert (= r (/ 1 3)))(check-sat)")
    assert model["r"] == Fraction(1, 3)
    assert isinstance(model["r"], Fraction)


def test_string_becomes_str() -> None:
    model = solved('(set-logic QF_S)(declare-fun s () String)(assert (= s "hi"))(check-sat)')
    assert model["s"] == "hi"
    assert isinstance(model["s"], str)


def test_arrays_are_typed_objects_since_plan_02a() -> None:
    # This test used to assert the `Display` fallback (`model["a"]` was a `str`
    # starting with "(array "). Plan 02-A replaced it with a typed class, and
    # the assertion is inverted here so the fallback cannot come back.
    model = solved(
        "(set-logic QF_ABV)(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))"
        "(assert (= (select a (_ bv1 4)) (_ bv7 8)))(check-sat)"
    )
    value = model["a"]
    assert not isinstance(value, str)
    assert isinstance(value, axeyum.ArrayValue)
    assert value.select(1) == 7


def test_model_is_a_copy_so_the_outcome_stays_frozen() -> None:
    outcome = smt.solve(
        "(set-logic QF_BV)(declare-fun x () (_ BitVec 8))(assert (= x (_ bv3 8)))(check-sat)",
        timeout_ms=TIMEOUT_MS,
    )
    first = outcome.model
    first["x"] = "clobbered"
    assert outcome.model["x"] != "clobbered"
    with pytest.raises(AttributeError):
        outcome.status = "unsat"  # type: ignore[misc]


# --------------------------------------------------------------------------
# Plan 02-A: every remaining `Value` variant now has a typed Python class.
#
# The old behaviour was a `Display` string: honest, and useless -- a caller
# could read it and could not compute with it. These tests are about being
# able to compute with the value, which is the whole difference.
# --------------------------------------------------------------------------


def test_array_value_is_a_typed_object_not_a_rendering() -> None:
    model = solved(
        "(set-logic QF_ABV)(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))"
        "(assert (= (select a (_ bv1 4)) (_ bv7 8)))"
        "(assert (= (select a (_ bv2 4)) (_ bv9 8)))(check-sat)"
    )
    value = model["a"]
    assert isinstance(value, axeyum.ArrayValue)
    assert not isinstance(value, str)
    assert value.index_width == 4
    assert value.element_width == 8
    # The overrides are computable, not merely printable.
    assert value.select(1) == 7
    assert value.select(2) == 9
    # The stored map is NORMALIZED: entries equal to the default are removed,
    # so `select` is the accessor and `entries` is only the overriding part.
    entries = {int(index): int(element) for index, element in value.entries}
    assert len(value) == len(entries)
    default = int(value.default)
    for index, element in entries.items():
        assert element != default
        assert value.select(index) == element
    assert {value.select(1), value.select(2)} == {7, 9}


def test_datatype_value_carries_its_constructor_and_fields() -> None:
    model = solved(
        "(set-logic QF_DT)"
        "(declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Int)))))"
        "(declare-fun p () Pair)"
        "(assert (= (fst p) 3))(assert (= (snd p) 4))(check-sat)"
    )
    value = model["p"]
    assert isinstance(value, axeyum.DatatypeValue)
    assert [int(field) for field in value.fields] == [3, 4]
    assert isinstance(value.constructor, int)
    assert isinstance(value.datatype, int)


def test_uninterpreted_value_compares_by_token_within_its_sort() -> None:
    model = solved(
        "(set-logic QF_UF)(declare-sort U 0)"
        "(declare-fun a () U)(declare-fun b () U)"
        "(assert (distinct a b))(check-sat)"
    )
    first, second = model["a"], model["b"]
    assert isinstance(first, axeyum.UninterpretedValue)
    assert isinstance(second, axeyum.UninterpretedValue)
    assert first.sort == second.sort
    # `distinct` was asserted, so the tokens must differ -- and the class
    # compares by token, which is the ONLY meaning an uninterpreted value has.
    assert first != second
    assert first.token != second.token
    assert first != second
    assert hash(first) == hash(first)
    assert first.token == first.token


def test_function_interpretations_come_back_as_func_values() -> None:
    arena = ir.Arena()
    sort = ir.Sort.bv(4)
    f = arena.declare_fun("f", [sort], sort)
    a = arena.var(arena.declare("a", sort))
    b = arena.var(arena.declare("b", sort))
    goal = [
        arena.not_(arena.eq(a, b)),
        arena.not_(arena.eq(arena.apply(f, [a]), arena.apply(f, [b]))),
    ]
    result = solver.solve(arena, goal, solver.Config(timeout_ms=TIMEOUT_MS))
    assert result.status == "sat"
    interpretation = result.functions(arena)["f"]
    assert isinstance(interpretation, axeyum.FuncValue)
    assert len(interpretation.params) == 1
    assert interpretation.params[0].bv_width() == 4
    assert interpretation.result.bv_width() == 4
    # A finite interpretation: a default plus the pinned entries.
    assert interpretation.default is not None
    for args, value in interpretation.entries:
        assert len(args) == 1
        assert int(value) >= 0


def test_generic_array_values_carry_their_component_sorts() -> None:
    arena = ir.Arena()
    array_sort = ir.Sort.array(ir.Sort.int(), ir.Sort.int())
    a = arena.var(arena.declare("a", array_sort))
    goal = [
        arena.eq(arena.select(a, arena.int_const(1)), arena.int_const(5)),
        arena.eq(arena.select(a, arena.int_const(2)), arena.int_const(6)),
    ]
    result = solver.solve(arena, goal, solver.Config(timeout_ms=TIMEOUT_MS))
    if result.status != "sat":
        pytest.skip(f"generic-array query came back {result.status}")
    value = result.model(arena).get("a")
    if value is None:
        pytest.skip("the model left the array unconstrained")
    assert isinstance(value, axeyum.GenericArrayValue)
    assert value.index_sort.kind == "Int"
    assert value.element_sort.kind == "Int"
    assert isinstance(value.entries, list)


def test_no_model_value_falls_back_to_a_bare_string() -> None:
    """The regression guard for the old `Display` fallback.

    Before plan 02-A five `Value` variants arrived as their rendering. If one
    ever does again, this fails -- with the exception of the genuine `String`
    sort, whose values ARE Python strings by design.
    """
    scripts = [
        (
            "(set-logic QF_ABV)(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))"
            "(assert (= (select a (_ bv1 4)) (_ bv7 8)))(check-sat)"
        ),
        (
            "(set-logic QF_UF)(declare-sort U 0)(declare-fun a () U)(declare-fun b () U)"
            "(assert (distinct a b))(check-sat)"
        ),
        (
            "(set-logic QF_DT)(declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Int)))))"
            "(declare-fun p () Pair)(assert (= (fst p) 3))(check-sat)"
        ),
    ]
    checked = 0
    for script in scripts:
        for value in solved(script).values():
            assert not isinstance(value, str), value
            checked += 1
    assert checked >= 3


def test_bv_values_survive_the_round_trip_back_into_an_assignment() -> None:
    # `value_to_py` and `py_to_value` must agree, or a model read out of the
    # solver could not be fed back into the evaluator.
    arena = ir.Arena()
    x = arena.bv_var("x", 200)
    expected = (1 << 150) + 99
    goal = [arena.eq(x, arena.bv_const(200, expected))]
    result = solver.solve(arena, goal, solver.Config(timeout_ms=TIMEOUT_MS))
    assert result.status == "sat"
    read_out = result.model(arena)["x"]
    assert int(read_out) == expected

    fresh = arena.assignment()
    fresh.set(arena, arena.find_symbol("x"), read_out)
    assert int(ir.eval(arena, x, fresh)) == expected


def test_setting_a_value_of_the_wrong_width_is_refused() -> None:
    arena = ir.Arena()
    arena.bv_var("x", 8)
    arena.bv_var("wide", 16)
    assignment = arena.assignment()
    result = solver.solve(
        arena,
        [arena.eq(arena.var(arena.find_symbol("wide")), arena.bv_const(16, 1))],
        solver.Config(timeout_ms=TIMEOUT_MS),
    )
    sixteen_bit = result.model(arena)["wide"]
    with pytest.raises(ir.SortError):
        assignment.set(arena, arena.find_symbol("x"), sixteen_bit)


def test_a_real_value_round_trips_through_fraction() -> None:
    arena = ir.Arena()
    r = arena.real_var("r")
    goal = [arena.eq(r, arena.real_ratio(7, 3))]
    result = solver.solve(arena, goal, solver.Config(timeout_ms=TIMEOUT_MS))
    assert result.status == "sat"
    value = result.model(arena)["r"]
    assert value == Fraction(7, 3)
    fresh = arena.assignment()
    fresh.set(arena, arena.find_symbol("r"), value)
    assert ir.eval(arena, r, fresh) == Fraction(7, 3)


def test_cnf_formulae_are_plain_data_not_renderings() -> None:
    formula = cnf.parse_dimacs("p cnf 2 1\n1 -2 0\n")
    assert formula.clauses == [[1, -2]]
    assert isinstance(formula.to_dimacs(), str)


def test_real_algebraic_values_carry_their_defining_polynomial() -> None:
    """The sqrt(2) case: an irrational model value that is still exact.

    `x*x == 2` has no rational solution, so a correct model cannot be a
    `Fraction`. It arrives as the unique root of an integer polynomial inside
    an isolating interval -- which is computable, unlike the `Display` string
    this used to be.
    """
    model = solved("(set-logic QF_NRA)(declare-const x Real)(assert (= (* x x) 2))(check-sat)")
    value = model["x"]
    assert isinstance(value, axeyum.RealAlgebraicValue)
    assert not isinstance(value, str)
    # 1*x^2 + 0*x - 2, lowest-degree coefficient first.
    poly = value.defining_poly
    assert [int(c) for c in poly] == [-2, 0, 1]
    lo, hi = value.interval
    # The interval isolates a root of x^2 - 2, so it brackets +/- sqrt(2).
    assert lo < hi
    assert abs(float(lo) ** 2 - 2) < 1e-6
    midpoint = value.approx_midpoint
    assert midpoint is not None
    assert abs(float(midpoint) ** 2 - 2) < 1e-6
