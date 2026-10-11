from datetime import date, datetime
import pytest
from axeyum.rules import Context, Date, Duration


def test_leap_day_arithmetic_and_lifted_model_replay():
    context = Context()
    application = context.date_var('application')
    deadline = context.date_var('deadline')
    constraints = [application == context.date(date(2024, 2, 28)), deadline == application + context.days(2)]
    result = context.solve(constraints)
    assert result.is_sat()
    assert result.replay(context.arena, context.lower(constraints))
    assert context.lift_model(result, constraints) == {'application': date(2024, 2, 28), 'deadline': date(2024, 3, 1)}
    assert context.source_sorts == {'application': 'Date', 'deadline': 'Date'}
    delta = deadline - application
    assert isinstance(delta, Duration)
    assert context.solve([*constraints, context.arena.eq(delta.term, context.days(2).term)]).is_sat()
    assert context.solve([*constraints, context.arena.eq(delta.term, context.days(3).term)]).is_unsat()


@pytest.mark.parametrize('start,days,end', [(date(1999, 12, 31), 1, date(2000, 1, 1)), (date(1900, 2, 28), 1, date(1900, 3, 1)), (date(2000, 2, 28), 1, date(2000, 2, 29)), (date(2024, 3, 1), -1, date(2024, 2, 29))])
def test_calendar_boundaries(start, days, end):
    ctx = Context()
    shifted = ctx.date(start) + ctx.days(days)
    assert isinstance(shifted, Date)
    assert ctx.solve([shifted == ctx.date(end)]).is_sat()
    assert ctx.solve([shifted != ctx.date(end)]).is_unsat()


def test_date_range_is_enforced_for_arithmetic_results():
    for value, days in [(date.min, -1), (date.max, 1)]:
        ctx = Context()
        ctx.date(value) + ctx.days(days)
        assert ctx.solve().is_unsat()


def test_sort_context_and_python_type_errors():
    ctx, other = Context(), Context()
    value = ctx.date_var('d')
    with pytest.raises(ValueError):
        ctx.duration_var('d')
    for bad in [1, True, datetime(2024, 1, 1), '2024-01-01']:
        with pytest.raises(TypeError):
            ctx.date(bad)
    with pytest.raises(TypeError):
        ctx.days(True)
    for bad in [1, ctx.days(1), other.date(date.min)]:
        with pytest.raises(TypeError):
            value == bad
    with pytest.raises(TypeError):
        value + 1
    with pytest.raises(TypeError):
        bool(value)
    with pytest.raises(ValueError):
        date(2023, 2, 29)


def test_model_lifting_requires_correct_source_query():
    ctx = Context()
    day = ctx.date_var('day')
    assertions = [day == ctx.date(date(2024, 1, 1))]
    result = ctx.solve(assertions)
    with pytest.raises(ValueError, match='replay'):
        ctx.lift_model(result, [day == ctx.date(date(2024, 1, 2))])
