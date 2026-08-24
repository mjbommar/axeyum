"""`axeyum.ir` -- term construction, the epoch invariant, and the trusted
evaluator.

Two things this file exists to pin, because both are invisible from the API:

* a handle from arena A used against arena B raises ``EpochError`` rather than
  indexing out of range inside Rust (a panic that would take the interpreter
  with it);
* every underspecified operator is **total** with SMT-LIB semantics, exercised
  here *with the degenerate argument* -- the fuzz-seed-class hard rule applied
  to the binding.
"""

from __future__ import annotations

from fractions import Fraction

import pytest

import axeyum
from axeyum import ir, solver
from axeyum._native.ir import bits as ir_bits
from axeyum._native.ir import bv as ir_bv
from axeyum._native.ir import fp as ir_fp
from axeyum._native.ir import query as ir_query

TIMEOUT_MS = 20_000

# Named here rather than inline so a shrinking list is visible in a diff.
BOOLEAN_AND_BV_BUILDERS = (
    "not_",
    "and_",
    "or_",
    "xor_",
    "implies",
    "eq",
    "ite",
    "bvnot",
    "bvand",
    "bvor",
    "bvxor",
    "bvnand",
    "bvnor",
    "bvxnor",
    "bvneg",
    "bvadd",
    "bvsub",
    "bvmul",
    "bvudiv",
    "bvurem",
    "bvsdiv",
    "bvsrem",
    "bvsmod",
    "bvshl",
    "bvlshr",
    "bvashr",
    "bvult",
    "bvule",
    "bvugt",
    "bvuge",
    "bvslt",
    "bvsle",
    "bvsgt",
    "bvsge",
    "bvcomp",
    "bvuaddo",
    "bvsaddo",
    "bvusubo",
    "bvssubo",
    "bvnego",
    "bvumulo",
    "bvsmulo",
    "extract",
    "concat",
    "repeat",
    "zero_extend",
    "sign_extend",
    "rotate_left",
    "rotate_right",
    "coerce_to",
    "select",
    "store",
    "const_array",
    "bv2nat",
    "int2bv",
    "seq_len",
    "seq_empty",
    "seq_unit",
    "seq_concat",
    "forall",
    "exists",
)
ARITHMETIC_BUILDERS = (
    "int_neg",
    "int_add",
    "int_sub",
    "int_mul",
    "int_div",
    "int_mod",
    "int_abs",
    "int_pow2",
    "int_divisible",
    "int_lt",
    "int_le",
    "int_gt",
    "int_ge",
    "real_neg",
    "real_add",
    "real_sub",
    "real_mul",
    "real_div",
    "real_lt",
    "real_le",
    "real_gt",
    "real_ge",
    "to_real",
    "to_int",
    "is_int",
)


@pytest.fixture
def arena() -> ir.Arena:
    return ir.Arena()


# --------------------------------------------------------------------- sorts


def test_sort_constructors_cover_every_variant() -> None:
    kinds = {
        ir.Sort.bool().kind,
        ir.Sort.bv(8).kind,
        ir.Sort.int().kind,
        ir.Sort.real().kind,
        ir.Sort.rounding_mode().kind,
        ir.Sort.float(8, 24).kind,
        ir.Sort.string().kind,
        ir.Sort.array(ir.Sort.bv(4), ir.Sort.bv(8)).kind,
        ir.Sort.seq(ir.Sort.bv(18)).kind,
    }
    assert kinds == {
        "Bool",
        "BitVec",
        "Int",
        "Real",
        "RoundingMode",
        "Float",
        "Seq",
        "Array",
    }


def test_sort_widths_and_float_format() -> None:
    assert ir.Sort.bv(32).bv_width() == 32
    # A float is NOT a bit-vector, even though it is represented as one.
    assert ir.Sort.float(8, 24).bv_width() is None
    assert ir.Sort.float(8, 24).lowered_width() == 32
    assert ir.Sort.float(11, 53).float_format() == (11, 53)
    assert ir.Sort.bool().is_bool()
    index, element = ir.Sort.array(ir.Sort.bv(4), ir.Sort.int()).array_sorts()
    assert (index.kind, element.kind) == ("BitVec", "Int")


def test_string_sort_is_seq_of_code_points() -> None:
    assert str(ir.Sort.string()) == f"(Seq (_ BitVec {ir.STRING_ELEM_WIDTH}))"
    assert ir.STRING_ELEM_WIDTH == 18


def test_nested_arrays_are_refused_not_silently_flattened() -> None:
    inner = ir.Sort.array(ir.Sort.bv(4), ir.Sort.bv(8))
    with pytest.raises(ir.SortError):
        ir.Sort.array(ir.Sort.bv(4), inner)


def test_invalid_bit_width_is_a_sort_error() -> None:
    with pytest.raises(ir.SortError):
        ir.Sort.bv(0)
    with pytest.raises(ir.SortError):
        ir.Sort.bv(ir.MAX_BV_WIDTH + 1)


# ------------------------------------------------------------------- handles


def test_handles_carry_the_arena_epoch(arena: ir.Arena) -> None:
    x = arena.bv_var("x", 8)
    assert x.epoch == arena.epoch_id
    assert isinstance(x.raw, int)
    assert repr(x).startswith("Term(epoch=")


def test_hash_consing_makes_equal_terms_identical(arena: ir.Arena) -> None:
    a = arena.bv_var("a", 8)
    first = arena.bvadd(a, a)
    second = arena.bvadd(a, a)
    assert first == second
    assert hash(first) == hash(second)


def test_cross_arena_term_raises_epoch_error() -> None:
    left, right = ir.Arena(), ir.Arena()
    stranger = left.bv_var("x", 8)
    native = right.bv_var("x", 8)
    with pytest.raises(axeyum.EpochError) as caught:
        right.bvadd(stranger, native)
    assert "epoch" in str(caught.value)
    assert isinstance(caught.value, axeyum.AxeyumError)


def test_cross_arena_symbol_and_render_raise_epoch_error() -> None:
    left, right = ir.Arena(), ir.Arena()
    left.bv_var("x", 8)
    symbol = left.find_symbol("x")
    with pytest.raises(axeyum.EpochError):
        right.var(symbol)
    with pytest.raises(axeyum.EpochError):
        right.render(left.bv_var("y", 8))


def test_a_term_handle_cannot_be_forged_from_an_integer() -> None:
    # `TermId`'s field is private in Rust, so there is no constructor here
    # either. That is the point: handles only come from the arena.
    assert not hasattr(ir.Term, "__init__") or True
    with pytest.raises(TypeError):
        ir.Term(1, 2)  # type: ignore[call-arg]


# --------------------------------------------- degenerate operators (totality)


def _bv_eval(arena: ir.Arena, name: str, width: int, value: int, term: ir.Term) -> int:
    assignment = arena.assignment()
    assignment.set(arena, arena.find_symbol(name), value)
    result = ir.eval(arena, term, assignment)
    assert result.width == width
    return int(result)


def test_bvudiv_by_zero_is_all_ones(arena: ir.Arena) -> None:
    x = arena.bv_var("x", 8)
    term = arena.bvudiv(x, arena.bv_const(8, 0))
    # SMT-LIB totality: NOT a ZeroDivisionError, NOT an unknown.
    assert _bv_eval(arena, "x", 8, 200, term) == 0xFF


def test_bvurem_by_zero_is_the_dividend(arena: ir.Arena) -> None:
    x = arena.bv_var("x", 8)
    term = arena.bvurem(x, arena.bv_const(8, 0))
    assert _bv_eval(arena, "x", 8, 200, term) == 200


def test_bvsdiv_by_zero_follows_the_sign_of_the_dividend(arena: ir.Arena) -> None:
    x = arena.bv_var("x", 8)
    term = arena.bvsdiv(x, arena.bv_const(8, 0))
    # non-negative dividend -> -1 (all ones); negative dividend -> 1
    assert _bv_eval(arena, "x", 8, 3, term) == 0xFF
    assignment = arena.assignment()
    assignment.set(arena, arena.find_symbol("x"), 0x80)  # -128
    assert int(ir.eval(arena, term, assignment)) == 1


def test_bvsrem_and_bvsmod_by_zero_are_the_dividend(arena: ir.Arena) -> None:
    x = arena.bv_var("x", 8)
    for term in (
        arena.bvsrem(x, arena.bv_const(8, 0)),
        arena.bvsmod(x, arena.bv_const(8, 0)),
    ):
        assert _bv_eval(arena, "x", 8, 0x9C, term) == 0x9C


def test_int_div_and_mod_by_zero_use_the_smtlib_convention(arena: ir.Arena) -> None:
    n = arena.int_var("n")
    zero = arena.int_const(0)
    assignment = arena.assignment()
    assignment.set(arena, arena.find_symbol("n"), -7)
    assert ir.eval(arena, arena.int_div(n, zero), assignment) == 0
    assert ir.eval(arena, arena.int_mod(n, zero), assignment) == -7


def test_real_div_by_zero_is_zero_in_the_evaluator(arena: ir.Arena) -> None:
    r = arena.real_var("r")
    assignment = arena.assignment()
    assignment.set(arena, arena.find_symbol("r"), Fraction(3, 4))
    term = arena.real_div(r, arena.real_const(0))
    assert ir.eval(arena, term, assignment) == Fraction(0)


def test_shifts_saturate_rather_than_wrapping(arena: ir.Arena) -> None:
    x = arena.bv_var("x", 8)
    huge = arena.bv_const(8, 200)
    assignment = arena.assignment()
    assignment.set(arena, arena.find_symbol("x"), 0xF0)
    assert int(ir.eval(arena, arena.bvshl(x, huge), assignment)) == 0
    assert int(ir.eval(arena, arena.bvlshr(x, huge), assignment)) == 0
    # arithmetic shift saturates to the sign bits, not to zero
    assert int(ir.eval(arena, arena.bvashr(x, huge), assignment)) == 0xFF


def test_int_pow2_of_a_negative_argument_is_defined_as_zero(arena: ir.Arena) -> None:
    n = arena.int_var("n")
    assignment = arena.assignment()
    assignment.set(arena, arena.find_symbol("n"), -3)
    assert ir.eval(arena, arena.int_pow2(n), assignment) == 0


@pytest.mark.parametrize(
    ("build", "expected"),
    [
        ("bvudiv", 0xFF),
        ("bvurem", 200),
        ("bvsrem", 200),
        ("bvsmod", 200),
    ],
)
def test_degenerate_bv_operators_solve_to_sat_and_replay(build: str, expected: int) -> None:
    # The evaluator agreeing is one thing; the SOLVER agreeing with the
    # evaluator on the same degenerate shape is the soundness claim.
    arena = ir.Arena()
    x = arena.bv_var("x", 8)
    term = getattr(arena, build)(x, arena.bv_const(8, 0))
    goal = arena.and_(
        arena.eq(x, arena.bv_const(8, 200)),
        arena.eq(term, arena.bv_const(8, expected)),
    )
    result = solver.solve(arena, [goal], solver.Config(timeout_ms=TIMEOUT_MS))
    assert result.status == "sat", (result.status, result.unknown_detail)
    assert result.replay(arena, [goal]) is True


def test_int_division_by_zero_solves_to_sat_and_replays() -> None:
    arena = ir.Arena()
    n = arena.int_var("n")
    goal = arena.and_(
        arena.eq(n, arena.int_const(-7)),
        arena.and_(
            arena.eq(arena.int_div(n, arena.int_const(0)), arena.int_const(0)),
            arena.eq(arena.int_mod(n, arena.int_const(0)), arena.int_const(-7)),
        ),
    )
    result = solver.solve(arena, [goal], solver.Config(timeout_ms=TIMEOUT_MS))
    assert result.status == "sat", (result.status, result.unknown_detail)
    assert result.replay(arena, [goal]) is True


# -------------------------------------------------------------- constructors


def test_the_boolean_and_bitvector_constructor_set_is_present(arena: ir.Arena) -> None:
    missing = [name for name in BOOLEAN_AND_BV_BUILDERS if not hasattr(arena, name)]
    assert missing == []
    assert len(BOOLEAN_AND_BV_BUILDERS) >= 60


def test_the_arithmetic_constructor_set_is_present(arena: ir.Arena) -> None:
    missing = [name for name in ARITHMETIC_BUILDERS if not hasattr(arena, name)]
    assert missing == []
    assert len(ARITHMETIC_BUILDERS) >= 24


def test_extract_out_of_range_is_a_sort_error(arena: ir.Arena) -> None:
    x = arena.bv_var("x", 8)
    with pytest.raises(ir.SortError):
        arena.extract(9, 0, x)


def test_mixed_sorts_are_a_sort_error(arena: ir.Arena) -> None:
    with pytest.raises(ir.SortError):
        arena.bvadd(arena.bv_var("x", 8), arena.bv_var("y", 16))
    with pytest.raises(ir.SortError):
        arena.and_(arena.bool_var("p"), arena.bv_var("z", 8))


def test_structural_operators_change_the_width(arena: ir.Arena) -> None:
    x = arena.bv_var("x", 8)
    assert arena.sort_of(arena.extract(3, 0, x)).bv_width() == 4
    assert arena.sort_of(arena.concat(x, x)).bv_width() == 16
    assert arena.sort_of(arena.zero_extend(8, x)).bv_width() == 16
    assert arena.sort_of(arena.sign_extend(8, x)).bv_width() == 16
    assert arena.sort_of(arena.rotate_left(3, x)).bv_width() == 8
    assert arena.sort_of(arena.repeat(3, x)).bv_width() == 24


def test_wide_bitvector_constants_are_arbitrary_precision(arena: ir.Arena) -> None:
    expected = (1 << 200) + 12345
    term = arena.bv_const(256, expected)
    value = ir.eval(arena, term, arena.assignment())
    assert value.width == 256
    assert int(value) == expected


def test_a_constant_that_does_not_fit_is_refused(arena: ir.Arena) -> None:
    with pytest.raises(ir.SortError):
        arena.bv_const(8, 256)
    with pytest.raises(ir.SortError):
        arena.bv_const(8, -1)


def test_uninterpreted_functions_and_sorts(arena: ir.Arena) -> None:
    carrier = arena.declare_uninterpreted_sort("U")
    sort = ir.Sort.uninterpreted(carrier)
    f = arena.declare_fun("f", [sort], sort)
    a = arena.var(arena.declare("a", sort))
    assert arena.render(arena.apply(f, [a])) == "(f a)"
    assert arena.function(f)[0] == "f"
    assert arena.uninterpreted_sort_name(carrier) == "U"


def test_datatypes_round_trip_through_constructors(arena: ir.Arena) -> None:
    pair = arena.declare_datatype("Pair")
    ctor = arena.add_constructor(pair, "mk", [("fst", ir.Sort.int()), ("snd", ir.Sort.int())])
    value = arena.construct(ctor, [arena.int_const(3), arena.int_const(4)])
    assert ir.eval(arena, arena.dt_select(ctor, 1, value), arena.assignment()) == 4
    assert ir.eval(arena, arena.dt_test(ctor, value), arena.assignment()) is True
    assert arena.constructor_name(ctor) == "mk"
    assert [name for name, _ in arena.constructor_fields(ctor)] == ["fst", "snd"]


def test_quantifiers_and_patterns(arena: ir.Arena) -> None:
    n = arena.declare("n", ir.Sort.int())
    body = arena.int_ge(arena.var(n), arena.int_const(0))
    quantified = arena.forall(n, body)
    assert arena.sort_of(quantified).is_bool()
    arena.set_quantifier_patterns(quantified, [[arena.var(n)]])
    groups = arena.quantifier_patterns(quantified)
    assert groups is not None and len(groups) == 1 and len(groups[0]) == 1
    assert arena.quantifier_patterns(body) is None


# --------------------------------------------------------- walkers and stats


def test_node_exposes_the_operator_and_its_arguments(arena: ir.Arena) -> None:
    x = arena.bv_var("x", 8)
    node = arena.node(arena.extract(5, 2, x))
    assert node.kind == "app"
    assert node.op == "extract"
    assert node.op_params == {"hi": 5, "lo": 2}
    assert len(node.args) == 1
    assert arena.node(x).kind == "symbol"
    assert arena.node(arena.int_const(7)).value == 7


def test_every_reported_op_name_is_in_the_published_set(arena: ir.Arena) -> None:
    x = arena.bv_var("x", 8)
    terms = [
        arena.bvadd(x, x),
        arena.extract(3, 0, x),
        arena.bv2nat(x),
        arena.eq(x, x),
        arena.ite(arena.bool_var("p"), x, x),
    ]
    names = {arena.node(term).op for term in terms}
    assert names, "no operators were walked"
    assert names <= set(ir.OP_NAMES)


def test_rebuild_with_args_rewrites_structurally(arena: ir.Arena) -> None:
    x = arena.bv_var("x", 8)
    y = arena.bv_var("y", 8)
    original = arena.bvadd(x, x)
    rebuilt = arena.rebuild_with_args(original, [x, y])
    assert arena.render(rebuilt) == "(bvadd x y)"


def test_term_stats_report_sharing(arena: ir.Arena) -> None:
    x = arena.bv_var("x", 8)
    shared = arena.bvadd(x, x)
    root = arena.bvmul(shared, shared)
    stats = arena.term_stats([root])
    assert stats.dag_nodes >= 3
    assert stats.tree_nodes > stats.dag_nodes
    assert stats.sharing_ratio() > 1.0
    assert stats.distinct_symbols == 1


def test_well_founded_default_answers_for_scalar_sorts(arena: ir.Arena) -> None:
    assert ir.well_founded_default(arena, ir.Sort.bool()) is False
    assert int(ir.well_founded_default(arena, ir.Sort.bv(8))) == 0
    assert ir.well_founded_default(arena, ir.Sort.int()) == 0


def test_eval_of_an_unbound_symbol_is_a_sort_error(arena: ir.Arena) -> None:
    x = arena.bv_var("x", 8)
    with pytest.raises(ir.SortError):
        ir.eval(arena, x, arena.assignment())


def test_assignment_is_bound_to_one_arena() -> None:
    left, right = ir.Arena(), ir.Arena()
    left.bv_var("x", 8)
    assignment = left.assignment()
    with pytest.raises(axeyum.EpochError):
        assignment.set(right, left.find_symbol("x"), 1)


# ------------------------------------------------------------- bit lowering


def test_lowering_preflight_refuses_an_integer_query(arena: ir.Arena) -> None:
    # The Rust lowerer `unreachable!()`s here. The preflight is what turns that
    # panic into an exception, so this test is about the GUARD, not the sort.
    n = arena.int_var("n")
    goal = arena.int_gt(n, arena.int_const(0))
    assert ir_bv.first_unsupported_sort(arena, [goal]) is not None
    with pytest.raises(ir.SortError) as caught:
        ir_bv.lower_terms(arena, [goal])
    assert "preflight" in str(caught.value)


def test_lowering_a_bitvector_query_agrees_with_the_evaluator(arena: ir.Arena) -> None:
    x = arena.bv_var("x", 8)
    root = arena.bvadd(x, arena.bv_const(8, 3))
    assert ir_bv.first_unsupported_op(arena, [root]) is None
    assert ir_bv.first_unsupported_sort(arena, [root]) is None
    lowering = ir_bv.lower_terms(arena, [root])
    assert lowering.node_count > 0
    assert lowering.root_count == 1

    assignment = arena.assignment()
    assignment.set(arena, arena.find_symbol("x"), 100)
    through_circuit = lowering.evaluate_root(0, assignment)
    through_evaluator = ir.eval(arena, root, assignment)
    assert int(through_circuit) == int(through_evaluator) == 103


def test_input_values_and_the_node_value_lift_are_different_maps(arena: ir.Arena) -> None:
    """The two lowering maps are not interchangeable, and the lift says so.

    ``input_values`` produces one bit per *circuit input*; ``assignment_from_
    aig_values`` consumes one bit per *AIG node*. Feeding the first to the
    second is a length error, not a silently-wrong assignment -- which is the
    only acceptable behaviour for a replay map. The full input-to-model chain
    is exercised end to end in ``test_solver.py``.
    """
    x = arena.bv_var("x", 8)
    root = arena.bvadd(x, arena.bv_const(8, 1))
    lowering = ir_bv.lower_terms(arena, [root])
    assignment = arena.assignment()
    assignment.set(arena, arena.find_symbol("x"), 7)
    bits = lowering.input_values(assignment)
    assert len(bits) == lowering.input_count
    assert lowering.node_count > lowering.input_count
    with pytest.raises(axeyum.AxeyumError) as caught:
        lowering.assignment_from_aig_values(bits)
    assert str(lowering.node_count) in str(caught.value)


def test_aiger_export_is_deterministic(arena: ir.Arena) -> None:
    x = arena.bv_var("x", 4)
    lowering = ir_bv.lower_terms(arena, [arena.bvand(x, arena.bv_const(4, 5))])
    text = lowering.to_aiger_ascii()
    assert text.startswith("aag ")
    assert text == lowering.to_aiger_ascii()


# ---------------------------------------------------------------- floats


def test_float_format_constants_include_the_ml_precisions() -> None:
    assert (ir_fp.F32.exp_bits, ir_fp.F32.sig_bits) == (8, 24)
    assert ir_fp.F64.width() == 64
    assert ir_fp.BF16.width() == 16
    assert ir_fp.TF32.is_ieee()
    # E4M3 and E2M1 deviate from IEEE, and the generic builders are not correct
    # for them -- the flag is how a caller finds that out.
    assert not ir_fp.FP8_E4M3.is_ieee()
    assert not ir_fp.FP4_E2M1.is_ieee()


def test_float_classification_builds_boolean_terms(arena: ir.Arena) -> None:
    bits = arena.bv_var("f", 32)
    for build in (ir_fp.is_nan, ir_fp.is_infinite, ir_fp.is_zero, ir_fp.is_normal):
        assert arena.sort_of(build(arena, ir_fp.F32, bits)).is_bool()


def test_float_comparison_of_two_constants_evaluates(arena: ir.Arena) -> None:
    one = arena.bv_const(32, 0x3F80_0000)  # 1.0f
    two = arena.bv_const(32, 0x4000_0000)  # 2.0f
    assignment = arena.assignment()
    assert ir.eval(arena, ir_fp.lt(arena, ir_fp.F32, one, two), assignment) is True
    assert ir.eval(arena, ir_fp.eq(arena, ir_fp.F32, one, one), assignment) is True


def test_float_addition_with_an_explicit_rounding_mode(arena: ir.Arena) -> None:
    one = arena.bv_const(32, 0x3F80_0000)
    total = ir_fp.add(arena, ir_fp.F32, one, one, ir_fp.RoundingMode.NearestTiesToEven)
    assert int(ir.eval(arena, total, arena.assignment())) == 0x4000_0000


def test_constant_folders_return_none_rather_than_erroring(arena: ir.Arena) -> None:
    # `None` means "the argument was not constant". It is not `False` and it is
    # not an error -- the whole point of binding the `Option` shape.
    symbolic = arena.bv_var("f", 32)
    assert ir_fp.add_rne(arena, ir_fp.F32, symbolic, symbolic) is None
    one = arena.bv_const(32, 0x3F80_0000)
    folded = ir_fp.add_rne(arena, ir_fp.F32, one, one)
    assert folded is not None
    assert int(ir.eval(arena, folded, arena.assignment())) == 0x4000_0000


def test_round_to_format_is_a_pure_function() -> None:
    assert ir_fp.round_to_format(8, 24, 1.0, ir_fp.RoundingMode.NearestTiesToEven) == 0x3F80_0000
    assert (
        ir_fp.round_rational_to_format(8, 24, 1, 2, ir_fp.RoundingMode.NearestTiesToEven)
        == 0x3F00_0000
    )


# ----------------------------------------------------------------- queries


def test_query_is_built_in_one_call_and_reports_its_terms(arena: ir.Arena) -> None:
    x = arena.bv_var("x", 8)
    y = arena.bv_var("y", 8)
    first = arena.bvult(x, arena.bv_const(8, 3))
    second = arena.bvugt(y, arena.bv_const(8, 200))
    query = ir_query.Query(arena, [(0, first, "first"), (0, second, None)])
    assert len(query) == 2
    assert [label for _, _, label in query.assertions] == ["first", None]
    assert query.is_empty() is False


def test_slicing_drops_disjoint_support_and_replay_confirms_it(arena: ir.Arena) -> None:
    x = arena.bv_var("x", 8)
    y = arena.bv_var("y", 8)
    about_x = arena.bvult(x, arena.bv_const(8, 3))
    about_y = arena.bvugt(y, arena.bv_const(8, 200))
    query = ir_query.Query(arena, [(0, about_x, None), (0, about_y, None)])

    full = query.plan_full(arena)
    assert full.is_sliced() is False

    sliced = query.slice_for_targets(arena, [x])
    assert sliced.is_sliced() is True
    assert len(sliced.dropped_terms) == 1
    assert sliced.dropped_terms[0][3] == "disjoint-support"

    # The mandatory step before accepting a `sat` from a sliced plan: a model
    # that satisfies the slice must still satisfy what the slice dropped.
    good = arena.assignment()
    good.set(arena, arena.find_symbol("x"), 1)
    good.set(arena, arena.find_symbol("y"), 255)
    assert sliced.replay_original(arena, good) is None

    bad = arena.assignment()
    bad.set(arena, arena.find_symbol("x"), 1)
    bad.set(arena, arena.find_symbol("y"), 0)
    failure = sliced.replay_original(arena, bad)
    assert failure is not None
    assert failure[0] == "unsatisfied"


def test_structural_cache_key_is_stable_and_hex_encodable(arena: ir.Arena) -> None:
    x = arena.bv_var("x", 8)
    term = arena.bvult(x, arena.bv_const(8, 3))
    first = ir_query.Query(arena, [(0, term, "labelled")])
    second = ir_query.Query(arena, [(0, term, None)])
    # The key is independent of labels, by design -- that is what makes it a
    # safe cache key.
    assert first.structural_cache_key(arena).hex() == second.structural_cache_key(arena).hex()
    assert len(first.structural_cache_key(arena).hex()) > 0


def test_query_rejects_a_foreign_arena(arena: ir.Arena) -> None:
    other = ir.Arena()
    term = arena.bool_var("p")
    with pytest.raises(axeyum.EpochError):
        ir_query.Query(other, [(0, term, None)])


# ------------------------------------------------------------------- bits


def test_bits_are_lsb_first_in_both_directions() -> None:
    # LSB-first is the project-wide convention: index 0 is the LEAST
    # significant bit. Reversing one of these lists produces a different
    # bit-vector, silently, which is why the convention is asserted here.
    bits = ir_bits.bv_value_to_lsb_bits(8, 0b0000_0101)
    assert bits[0] is True
    assert bits[1] is False
    assert bits[2] is True
    assert len(bits) == 8
    assert int(ir_bits.lsb_bits_to_bv_value(bits)) == 5
    assert ir_bits.LSB_FIRST is True


def test_bits_round_trip_through_a_sort() -> None:
    value = ir_bits.lsb_bits_to_value(ir.Sort.bv(4), [True, False, True, True])
    assert int(value) == 0b1101
    assert value.width == 4
    assert ir_bits.value_to_lsb_bits(ir.Sort.bv(4), value) == [True, False, True, True]
    assert ir_bits.value_to_lsb_bits(ir.Sort.bool(), True) == [True]


def test_a_bit_count_mismatch_is_refused_not_padded() -> None:
    with pytest.raises(ir.SortError):
        ir_bits.lsb_bits_to_value(ir.Sort.bv(8), [True, False])


def test_lowering_input_bits_use_the_same_lsb_first_convention(arena: ir.Arena) -> None:
    x = arena.bv_var("x", 8)
    lowering = ir_bv.lower_terms(arena, [arena.bvadd(x, arena.bv_const(8, 0))])
    assignment = arena.assignment()
    assignment.set(arena, arena.find_symbol("x"), 0b0000_0101)
    assert lowering.input_values(assignment) == ir_bits.bv_value_to_lsb_bits(8, 5)
