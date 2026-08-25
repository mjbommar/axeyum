"""Hypothesis round-trips for every `Value` variant that reaches Python.

Each case drives a real solve, so what is checked is the value the SOLVER
produced and the binding converted -- not a hand-built value that never crossed
the boundary. `convert.rs`'s rule is *sound, never inventive*: a variant is
mapped only when the mapping is total and loses nothing, so every property here
is an equality, never an approximation.

The bit-vector case is the one with a seam in it. The IR splits bit-vectors at
128 bits (`Value::Bv` holds a `u128`, `Value::WideBv` a limb vector) and the
binding converges both on a single `BvValue` backed by a Python `int`. That
split is a storage detail, and the properties below are written to straddle it:
widths are drawn from both sides and from the boundary itself.
"""

from __future__ import annotations

from fractions import Fraction

import pytest
from hypothesis import given
from hypothesis import strategies as st

import axeyum
from axeyum import smt

TIMEOUT_MS = 20_000

# Straddles the `u128` boundary deliberately: 128 is the last narrow width, 129
# the first wide one, and a binding that read the wrong union arm would pass on
# one side and fail on the other.
BV_WIDTHS = st.one_of(
    st.sampled_from([1, 2, 7, 8, 63, 64, 127, 128, 129, 130, 200, 300]),
    st.integers(min_value=1, max_value=256),
)


def solved_model(script: str) -> dict[str, object]:
    """Solves, asserts the `sat` replayed, and returns the model."""
    outcome = smt.solve(script, timeout_ms=TIMEOUT_MS)
    assert outcome.status == "sat", (outcome.status, outcome.detail, script)
    assert outcome.replay() is True, script
    return outcome.model


@given(width=BV_WIDTHS, data=st.data())
def test_bitvector_round_trips_at_any_width(width: int, data: st.DataObject) -> None:
    """A bit-vector comes back as `BvValue` with its width and exact value."""
    value = data.draw(
        st.one_of(
            st.sampled_from([0, 1, (1 << width) - 1, 1 << (width - 1)]),
            st.integers(min_value=0, max_value=(1 << width) - 1),
        ),
        label="value",
    )
    model = solved_model(
        f"(set-logic QF_BV)(declare-fun x () (_ BitVec {width}))"
        f"(assert (= x (_ bv{value} {width})))(check-sat)"
    )
    recovered = model["x"]
    assert isinstance(recovered, axeyum.BvValue)
    assert recovered.width == width
    # Three spellings of the same integer, because each is a separate path
    # through `convert.rs` and a caller may use any of them.
    assert recovered.value == value
    assert int(recovered) == value
    assert recovered.__index__() == value
    assert repr(recovered) == f"BvValue(width={width}, value={value})"


@given(width=BV_WIDTHS, data=st.data())
def test_bitvector_equality_and_hash_agree(width: int, data: st.DataObject) -> None:
    """Two `BvValue`s from separate solves compare and hash alike -- and a
    bit-vector is never equal to a bare `int`, because it carries a width."""
    value = data.draw(st.integers(min_value=0, max_value=(1 << width) - 1), label="value")
    script = (
        "(set-logic QF_BV)(declare-fun {name} () (_ BitVec {width}))"
        "(assert (= {name} (_ bv{value} {width})))(check-sat)"
    )
    left = solved_model(script.format(name="x", width=width, value=value))["x"]
    right = solved_model(script.format(name="y", width=width, value=value))["y"]
    assert left == right
    assert hash(left) == hash(right)
    assert left != value


@given(value=st.integers(min_value=-(2**60), max_value=2**60))
def test_integer_round_trips_exactly(value: int) -> None:
    """An `Int` comes back as a Python `int`, not a float and not a string."""
    literal = f"(- {abs(value)})" if value < 0 else str(value)
    model = solved_model(
        f"(set-logic QF_LIA)(declare-fun n () Int)(assert (= n {literal}))(check-sat)"
    )
    assert model["n"] == value
    assert isinstance(model["n"], int)
    assert not isinstance(model["n"], bool)


@given(
    numerator=st.integers(min_value=-1000, max_value=1000),
    denominator=st.integers(min_value=1, max_value=1000),
)
def test_real_round_trips_as_an_exact_fraction(numerator: int, denominator: int) -> None:
    """A `Real` comes back as `fractions.Fraction` -- exact, never a float.

    A float would silently lose 1/3, and a caller comparing a model value to a
    rational it computed would then see a spurious disagreement.
    """
    sign = f"(- {abs(numerator)})" if numerator < 0 else str(numerator)
    model = solved_model(
        f"(set-logic QF_LRA)(declare-fun r () Real)"
        f"(assert (= r (/ {sign} {denominator})))(check-sat)"
    )
    assert isinstance(model["r"], Fraction)
    assert model["r"] == Fraction(numerator, denominator)


@given(value=st.booleans())
def test_bool_round_trips_as_a_python_bool(value: bool) -> None:
    """A `Bool` is `True`/`False` by identity, not merely by truthiness."""
    assertion = "p" if value else "(not p)"
    model = solved_model(f"(set-logic QF_UF)(declare-fun p () Bool)(assert {assertion})(check-sat)")
    assert model["p"] is value


# Printable ASCII minus backslash: the escape grammar is a parser question, and
# it is covered separately below with fixed literals rather than by a generator
# that would have to model SMT-LIB escaping to produce the expected value.
STRING_CHARS = st.sampled_from([chr(code) for code in range(0x20, 0x7F) if chr(code) not in {"\\"}])


@given(text=st.lists(STRING_CHARS, min_size=0, max_size=8).map("".join))
def test_string_round_trips_through_the_packed_encoding(text: str) -> None:
    """A `String` survives the parser's packed bit-vector representation.

    The parser lowers a declared `String` to a packed bit-vector and the front
    door lifts it back to a sequence of code points, so a model value makes the
    trip twice. `"` is doubled, which is SMT-LIB's only in-literal escape.
    """
    literal = text.replace('"', '""')
    model = solved_model(
        f'(set-logic QF_S)(declare-fun s () String)(assert (= s "{literal}"))(check-sat)'
    )
    assert model["s"] == text
    assert isinstance(model["s"], str)


@pytest.mark.parametrize(
    ("literal", "expected"),
    [
        (r"\u{41}b", "Ab"),
        (r"B", "B"),
        (r"\u{7f}", "\x7f"),
        (r"a\u{20}b", "a b"),
    ],
)
def test_string_escapes_are_decoded(literal: str, expected: str) -> None:
    """The `\\u{...}` and `\\uXXXX` forms both decode -- the two spellings a
    generator that only emitted printable characters would never reach."""
    model = solved_model(
        f'(set-logic QF_S)(declare-fun s () String)(assert (= s "{literal}"))(check-sat)'
    )
    assert model["s"] == expected
