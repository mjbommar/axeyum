"""Round-trips for every IR value variant this slice converts.

Each case drives a real solve, so the assertion is about what the *solver*
produces, not about a hand-built value the binding never sees.
"""

from __future__ import annotations

from fractions import Fraction

import pytest

import axeyum
from axeyum import smt

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


def test_unmapped_variants_render_rather_than_lie() -> None:
    # TODO(plan 02): arrays (and datatypes, uninterpreted carriers, real
    # algebraic numbers) need structured Python types. Until then they arrive as
    # their `Display` rendering -- readable, and impossible to mistake for a
    # number.
    model = solved(
        "(set-logic QF_ABV)(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))"
        "(assert (= (select a (_ bv1 4)) (_ bv7 8)))(check-sat)"
    )
    assert isinstance(model["a"], str)
    assert model["a"].startswith("(array ")


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
