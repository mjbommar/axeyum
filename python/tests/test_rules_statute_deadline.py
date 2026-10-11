from datetime import date, timedelta
import pytest
from axeyum.rules import HolidayCalendar, minnesota_deadline

FLAGS = dict(rule_applies=True, successive_weeks=False, calendar_months=False)


def test_weekend_and_synthetic_holiday_endpoints():
    calendar = HolidayCalendar(date(2026, 7, 1), date(2026, 7, 31), frozenset({date(2026, 7, 6)}), 'synthetic test calendar')
    result = minnesota_deadline(date(2026, 7, 3), 1, calendar, **FLAGS)
    assert result.status == 'computed' and result.value == date(2026, 7, 7)
    assert result.nominal == date(2026, 7, 4)
    assert result.skipped == (date(2026, 7, 4), date(2026, 7, 5), date(2026, 7, 6))
    assert result.calendar_source == calendar.source


@pytest.mark.parametrize('start,days,end', [(date(2024, 2, 28), 1, date(2024, 2, 29)), (date(2025, 12, 31), 1, date(2026, 1, 1)), (date(2026, 7, 2), 1, date(2026, 7, 3))])
def test_first_last_day_and_calendar_boundaries(start, days, end):
    calendar = HolidayCalendar(date(2024, 1, 1), date(2026, 12, 31), frozenset(), 'synthetic empty calendar')
    assert minnesota_deadline(start, days, calendar, **FLAGS).value == end


def test_independent_ordinal_reference_over_stated_domain():
    calendar = HolidayCalendar(date(2024, 1, 1), date(2024, 3, 31), frozenset({date(2024, 1, 15), date(2024, 2, 19)}), 'synthetic calendar')
    # Enumerate the reference population before calling the producer; weekday
    # calculation uses ordinal arithmetic instead of datetime.weekday().
    admitted = [n for n in range(calendar.first.toordinal(), calendar.last.toordinal()+1) if (n-1)%7 < 5 and date.fromordinal(n) not in calendar.holidays]
    cases = [(date(2024, 1, 1)+timedelta(days=offset), days) for offset in range(31) for days in (1, 2, 7, 30)]
    assert len(cases) == 124
    for start, days in cases:
        expected = date.fromordinal(min(n for n in admitted if n >= start.toordinal()+days))
        result = minnesota_deadline(start, days, calendar, **FLAGS)
        assert result.status == 'computed' and result.value == expected


def test_exclusions_missing_facts_and_resource_declines_have_no_deadline():
    calendar = HolidayCalendar(date(2026, 7, 1), date(2026, 7, 5), frozenset(), 'synthetic')
    assert minnesota_deadline(date(2026, 7, 3), 1, calendar).status == 'missing-inputs'
    for flags in [dict(FLAGS, rule_applies=False), dict(FLAGS, successive_weeks=True), dict(FLAGS, calendar_months=True)]:
        result = minnesota_deadline(date(2026, 7, 3), 1, calendar, **flags)
        assert result.status == 'outside-fragment' and result.value is None
    for result in [minnesota_deadline(date(2026, 7, 3), 1, calendar, **FLAGS), minnesota_deadline(date(2026, 7, 3), 1, calendar, max_roll=0, **FLAGS), minnesota_deadline(date.max, 1, calendar, **FLAGS), minnesota_deadline(date(2026, 7, 3), 36601, calendar, **FLAGS)]:
        assert result.status in ('missing-calendar', 'resource-limited')
        assert result.value is None


def test_malformed_inputs_and_calendar_authority_reject():
    calendar = HolidayCalendar(date(2026, 1, 1), date(2026, 12, 31), frozenset(), 'synthetic')
    for days in (0, -1, True):
        with pytest.raises(ValueError):
            minnesota_deadline(date(2026, 1, 1), days, calendar, **FLAGS)
    with pytest.raises(ValueError):
        HolidayCalendar(date(2026, 1, 1), date(2026, 12, 31), frozenset(), '')
    with pytest.raises(ValueError):
        HolidayCalendar(date(2026, 1, 1), date(2026, 12, 31), frozenset({date(2027, 1, 1)}), 'synthetic')


def test_native_deadline_obligations_and_wrong_claims():
    from axeyum.rules import verify_minnesota_deadline
    calendar = HolidayCalendar(date(2026, 7, 1), date(2026, 7, 31), frozenset({date(2026, 7, 6)}), 'synthetic test calendar')
    verified = verify_minnesota_deadline(date(2026, 7, 3), 1, calendar, date(2026, 7, 7), max_roll=7, **FLAGS)
    assert verified.status in ('checked-native', 'validated')
    assert [(item.name, item.verdict) for item in verified.obligations] == [('feasibility', 'sat'), ('minimality', 'unsat'), ('uniqueness', 'unsat')]
    assert verified.obligations[0].check_status == 'verified'
    for wrong in (date(2026, 7, 6), date(2026, 7, 8)):
        assert verify_minnesota_deadline(date(2026, 7, 3), 1, calendar, wrong, max_roll=7, **FLAGS).status == 'rejected'


def test_native_deadline_declines_incomplete_calendar():
    from axeyum.rules import verify_minnesota_deadline
    calendar = HolidayCalendar(date(2026, 7, 1), date(2026, 7, 5), frozenset(), 'synthetic')
    result = verify_minnesota_deadline(date(2026, 7, 3), 1, calendar, date(2026, 7, 6), max_roll=7, **FLAGS)
    assert result.status == 'inconclusive' and result.obligations == ()


def test_native_obligations_across_independent_reference_domain():
    from axeyum.rules import verify_minnesota_deadline
    calendar = HolidayCalendar(date(2024, 1, 1), date(2024, 3, 31), frozenset({date(2024, 1, 15), date(2024, 2, 19)}), 'synthetic calendar')
    admitted = [n for n in range(calendar.first.toordinal(), calendar.last.toordinal()+1) if (n-1)%7 < 5 and date.fromordinal(n) not in calendar.holidays]
    cases = [(date(2024, 1, 1)+timedelta(days=offset), days) for offset in range(31) for days in (1, 2, 7, 30)]
    assert len(cases) == 124
    for start, days in cases:
        expected = date.fromordinal(min(n for n in admitted if n >= start.toordinal()+days))
        report = verify_minnesota_deadline(start, days, calendar, expected, max_roll=7, **FLAGS)
        assert report.status in ('checked-native', 'validated')
        assert [item.verdict for item in report.obligations] == ['sat', 'unsat', 'unsat']
        assert report.obligations[0].check_status == 'verified'


def test_deadline_certificate_replay_source_binding_and_tampering():
    import json
    from axeyum.rules import deadline_certificate, check_deadline_certificate
    calendar = HolidayCalendar(date(2026, 7, 1), date(2026, 7, 31), frozenset({date(2026, 7, 6)}), 'synthetic test calendar')
    text = deadline_certificate(date(2026, 7, 3), 1, calendar, date(2026, 7, 7), max_roll=7, **FLAGS)
    assert text is not None
    artifact = json.loads(text)
    report = check_deadline_certificate(text, expected_subject=artifact['subject'])
    assert report.status == 'checked' and report.checked_candidates == 8
    assert deadline_certificate(date(2026, 7, 3), 1, calendar, date(2026, 7, 8), max_roll=7, **FLAGS) is None
    mutations = []
    for key, value in [('claim', '2026-07-08'), ('candidates', artifact['candidates'][:-1])]:
        mutations.append({**artifact, key: value})
    for key, value in [('weekday', 0), ('holiday', True), ('date', '2026-07-05')]:
        rows = [dict(row) for row in artifact['candidates']]
        rows[0][key] = value
        mutations.append({**artifact, 'candidates': rows})
    for mutated in mutations:
        assert check_deadline_certificate(json.dumps(mutated)).status == 'rejected'
    wrong_subject = {**artifact['subject'], 'days': 2}
    assert check_deadline_certificate(text, expected_subject=wrong_subject).status == 'rejected'
    assert check_deadline_certificate(text, expected_subject={**artifact['subject'], 'days': True}).status == 'rejected'
    assert check_deadline_certificate(text.replace('\"version\":1', '\"version\":1,\"version\":1')).status == 'rejected'
    assert check_deadline_certificate(chr(0xd800)).status == 'rejected'
    assert check_deadline_certificate(json.dumps({**artifact, 'version': 2})).status == 'unsupported'
    assert check_deadline_certificate('x' * 262145).status == 'resource-limited'
