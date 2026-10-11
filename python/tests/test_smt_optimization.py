"""Typed optimization values and feasibility replay remain separate from gold."""
import pytest
from axeyum import AxeyumError, smt

BOUNDS = """(set-logic QF_LIA)
(declare-const x Int)(declare-const y Int)
(assert (and (>= x 0) (<= x 10) (>= y 0) (<= y 3)))"""


def test_maximize_minimize_models_and_copies():
    for direction, expected in [("maximize", 10), ("minimize", 0)]:
        result = smt.optimize(f"{BOUNDS}({direction} x)(check-sat)")
        assert result.mode == "lex" and result.complete and len(result) == 1
        row = result[0]
        assert row.status == "optimal" and row.value == expected
        assert row.sort == "Int" and row.bit_width is None
        assert row.direction == direction and row.model_available
        assert row.model["x"] == expected and row.replay() is True
        assert not row.gold_eligible
        model = row.model
        model["x"] = 999
        assert row.model["x"] == expected and row.replay() is True
        with pytest.raises(IndexError):
            result[1]


def test_box_and_lex_have_distinct_per_objective_witnesses():
    query = f"{BOUNDS}(assert (<= (+ x y) 10))(maximize x)(maximize y)(check-sat)"
    for mode, expected in [("lex", [10, 0]), ("box", [10, 3])]:
        result = smt.optimize(query, mode=mode)
        assert result.mode == mode and result.complete
        assert [row.value for row in result.objectives] == expected
        assert all(row.replay() is True and not row.gold_eligible for row in result.objectives)
        assert result[1].model["y"] == expected[1]


def test_scoped_reset_and_late_objectives_match_the_query_snapshot():
    query = f"{BOUNDS}(maximize x)(push 1)(minimize x)(pop 1)(check-sat)(minimize y)"
    result = smt.optimize(query)
    assert len(result) == 1 and result[0].value == 10 and result[0].replay() is True
    query = f"{BOUNDS}(maximize x)(reset-assertions)(assert (and (>= x 0) (<= x 4)))(minimize x)(check-sat)"
    result = smt.optimize(query)
    assert len(result) == 1 and result[0].direction == "minimize" and result[0].value == 0


def test_unknown_infeasible_and_unbounded_are_values():
    query = f"{BOUNDS}(maximize x)(check-sat)"
    row = smt.optimize(query, timeout_ms=0)[0]
    assert row.status == "unknown" and row.value is None and row.detail
    assert row.model == {} and not row.model_available and row.replay() is None
    row = smt.optimize(f"{BOUNDS}(assert (< x 0))(maximize x)(check-sat)")[0]
    assert row.status == "infeasible" and row.replay() is None
    row = smt.optimize("(declare-const x Int)(maximize x)(check-sat)")[0]
    assert row.status == "unbounded" and row.value is None and row.replay() is None


def test_unsigned_bv_and_unsupported_modes_are_explicit():
    query = "(set-logic QF_BV)(declare-const x (_ BitVec 8))(assert (bvult x (_ bv200 8)))(maximize x)(check-sat)"
    row = smt.optimize(query)[0]
    assert row.status == "optimal" and row.value == 199
    assert row.sort == "BitVec" and row.bit_width == 8 and row.replay() is True
    with pytest.raises(ValueError, match="lex or box"):
        smt.optimize(query, mode="pareto")
    for query in ["(declare-const r Real)(maximize r)(check-sat)",
                  f"{BOUNDS}(maximize x)(set-option :opt.priority box)(check-sat)"]:
        with pytest.raises(AxeyumError, match="unsupported|conflicts|optimization"):
            smt.optimize(query)


def test_generic_satisfiability_route_still_declines_objectives():
    with pytest.raises(AxeyumError, match="optimization"):
        smt.solve(f"{BOUNDS}(maximize x)(check-sat)")
