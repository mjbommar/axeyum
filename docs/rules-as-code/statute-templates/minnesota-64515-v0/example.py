"""Synthetic-calendar demonstration; caller applicability assumptions are explicit."""
from datetime import date
from axeyum.rules import HolidayCalendar, minnesota_deadline, verify_minnesota_deadline

calendar = HolidayCalendar(date(2026, 7, 1), date(2026, 7, 31), frozenset(), 'synthetic demonstration; not a legal holiday authority')
result = minnesota_deadline(date(2026, 7, 3), 1, calendar, rule_applies=True, successive_weeks=False, calendar_months=False)
assert result.status == 'computed'
assert result.value == date(2026, 7, 6)
print(result)

verification = verify_minnesota_deadline(date(2026, 7, 3), 1, calendar, result.value, rule_applies=True, successive_weeks=False, calendar_months=False, max_roll=7)
assert verification.status in ('validated', 'checked-native')
print(verification.status)
for obligation in verification.obligations:
    print(obligation.name, obligation.verdict, obligation.check_status)
