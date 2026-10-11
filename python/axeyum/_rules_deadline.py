"""Bounded day-period template for Minnesota §645.15; applicability is input."""
from dataclasses import dataclass
from datetime import date, timedelta


@dataclass(frozen=True)
class HolidayCalendar:
    """Caller-sourced complete holiday classification within inclusive coverage."""
    first: date
    last: date
    holidays: frozenset
    source: str

    def __post_init__(self):
        if type(self.first) is not date or type(self.last) is not date or self.first > self.last:
            raise ValueError('calendar coverage requires ordered Gregorian dates')
        if type(self.holidays) is not frozenset or len(self.holidays) > 4096:
            raise ValueError('holidays must be a frozenset of at most 4096 dates')
        if any(type(day) is not date or not self.first <= day <= self.last for day in self.holidays):
            raise ValueError('holiday dates must lie inside calendar coverage')
        if not isinstance(self.source, str) or not self.source.strip():
            raise ValueError('holiday calendar requires a source identity')


@dataclass(frozen=True)
class Deadline:
    status: str
    value: date | None
    nominal: date | None
    skipped: tuple
    detail: str
    calendar_source: str | None


def minnesota_deadline(start, days, calendar, *, rule_applies=None, successive_weeks=None, calendar_months=None, max_roll=32):
    """Compute a positive day period only under explicit §645.15 assumptions.

    The holiday set is assumed complete within its coverage. This function does
    not establish legal applicability, effective dates or a verified holiday
    calendar. Declines carry no deadline value. See ADR-3400.
    """
    if type(start) is not date or type(days) is not int or days <= 0:
        raise ValueError('start must be a date and days a positive integer')
    if not isinstance(calendar, HolidayCalendar):
        raise TypeError('a sourced HolidayCalendar is required')
    if type(max_roll) is not int or not 0 <= max_roll <= 366:
        raise ValueError('max_roll must be an integer from 0 through 366')
    flags = (rule_applies, successive_weeks, calendar_months)
    if any(value is not None and type(value) is not bool for value in flags):
        raise TypeError('applicability flags must be bool or None')
    def result(status, nominal=None, skipped=(), value=None, detail=''):
        return Deadline(status, value, nominal, tuple(skipped), detail, calendar.source)
    if any(value is None for value in flags):
        return result('missing-inputs', detail='rule applicability and both cross-reference exclusions are required')
    if not rule_applies or successive_weeks or calendar_months:
        return result('outside-fragment', detail='requires applicable positive day period, excluding §§645.13 and 645.14')
    if days > 36600:
        return result('resource-limited', detail='day-period limit is 36600')
    try:
        nominal = start + timedelta(days=days)
    except OverflowError:
        return result('resource-limited', detail='nominal date exceeds Gregorian range')
    skipped = []
    candidate = nominal
    for offset in range(max_roll + 1):
        if not calendar.first <= candidate <= calendar.last:
            return result('missing-calendar', nominal, skipped, detail='candidate lies outside complete holiday coverage')
        if candidate.weekday() < 5 and candidate not in calendar.holidays:
            return result('computed', nominal, skipped, candidate)
        skipped.append(candidate)
        if offset == max_roll:
            break
        try:
            candidate += timedelta(days=1)
        except OverflowError:
            return result('resource-limited', nominal, skipped, detail='rollover exceeds Gregorian range')
    return result('resource-limited', nominal, skipped, detail='no admissible endpoint within rollover budget')


@dataclass(frozen=True)
class DeadlineObligation:
    name: str
    verdict: str
    check_status: str
    reason: str | None
    script: str
    evidence: object


@dataclass(frozen=True)
class DeadlineVerification:
    """Checked evidence and bare solver validation are deliberately distinct."""
    status: str
    obligations: tuple
    detail: str


def verify_minnesota_deadline(start, days, calendar, claimed, *, rule_applies=None, successive_weeks=None, calendar_months=None, max_roll=32, config=None):
    """Independently lower feasibility, minimality and uniqueness obligations.

    Weekdays are calculated in the native ground IR with ordinal modulo seven,
    independently of the producer's datetime.weekday path. Holiday completeness
    and legal applicability remain explicit input assumptions.
    """
    from .rules import Context
    from . import solver
    if type(start) is not date or type(claimed) is not date or type(days) is not int or days <= 0:
        raise ValueError('verification requires Gregorian start/claim and positive integer days')
    if not isinstance(calendar, HolidayCalendar):
        raise TypeError('verification requires a sourced HolidayCalendar')
    if type(max_roll) is not int or not 0 <= max_roll <= 366:
        raise ValueError('max_roll must be an integer from 0 through 366')
    flags = (rule_applies, successive_weeks, calendar_months)
    if any(value is not None and type(value) is not bool for value in flags):
        raise TypeError('applicability flags must be bool or None')
    if any(value is None for value in flags):
        return DeadlineVerification('inconclusive', (), 'missing applicability inputs')
    if not rule_applies or successive_weeks or calendar_months:
        return DeadlineVerification('inconclusive', (), 'outside modeled applicability')
    nominal = start.toordinal() + days
    last = min(nominal + max_roll, date.max.toordinal())
    if days > 36600 or nominal > date.max.toordinal():
        return DeadlineVerification('inconclusive', (), 'date/work limit')
    # Require complete facts over the whole obligation window; proving that no
    # earlier endpoint exists cannot assume an absent calendar fact is false.
    if not calendar.first.toordinal() <= nominal <= last <= calendar.last.toordinal():
        return DeadlineVerification('inconclusive', (), 'incomplete calendar coverage')
    ctx = Context()
    a = ctx.arena
    endpoint = ctx.date_var('deadline').term
    admitted = a.bool_const(False)
    minimum = a.bool_const(True)
    for ordinal in range(nominal, last + 1):
        constant = a.int_const(ordinal)
        weekday = a.int_mod(a.int_sub(constant, a.int_const(1)), a.int_const(7))
        allowed = a.and_(a.int_lt(weekday, a.int_const(5)), a.bool_const(date.fromordinal(ordinal) not in calendar.holidays))
        admitted = a.or_(admitted, a.and_(a.eq(endpoint, constant), allowed))
        minimum = a.and_(minimum, a.or_(a.not_(allowed), a.int_le(endpoint, constant)))
    claim = a.int_const(claimed.toordinal())
    subjects = (
        ('feasibility', [admitted, a.eq(endpoint, claim)], 'sat'),
        ('minimality', [admitted, a.int_lt(endpoint, claim)], 'unsat'),
        ('uniqueness', [admitted, minimum, a.not_(a.eq(endpoint, claim))], 'unsat'),
    )
    obligations = []
    for name, terms, expected in subjects:
        complete = ctx.lower(terms)
        evidence = solver.produce_evidence(a, complete, config)
        check = evidence.check_outcome(a, complete)
        obligations.append(DeadlineObligation(name, evidence.verdict, check.status, check.reason, a.write_script(complete), evidence))
        if check.is_failed() or (evidence.verdict != 'unknown' and evidence.verdict != expected):
            return DeadlineVerification('rejected', tuple(obligations), f'{name} contradicted the claim or failed replay')
    if any(item.verdict == 'unknown' for item in obligations):
        return DeadlineVerification('inconclusive', tuple(obligations), 'solver declined an obligation')
    if all(item.check_status == 'verified' and all(certified for _, certified in item.evidence.trusted_steps) for item in obligations):
        return DeadlineVerification('checked-native', tuple(obligations), 'conditional on calendar/applicability and native lowering')
    return DeadlineVerification('validated', tuple(obligations), 'one or more UNSAT obligations lack checked certificates')


@dataclass(frozen=True)
class DeadlineCertificateCheck:
    status: str
    detail: str
    checked_candidates: int = 0


def _subject(start, days, calendar, rule_applies, successive_weeks, calendar_months, max_roll):
    return dict(start=start.isoformat(), days=days, calendar_first=calendar.first.isoformat(), calendar_last=calendar.last.isoformat(), holidays=sorted(day.isoformat() for day in calendar.holidays), calendar_source=calendar.source, rule_applies=rule_applies, successive_weeks=successive_weeks, calendar_months=calendar_months, max_roll=max_roll)


def deadline_certificate(start, days, calendar, claimed, *, rule_applies=None, successive_weeks=None, calendar_months=None, max_roll=32):
    """Serialize a complete bounded candidate witness; not kernel admission."""
    import json
    if type(claimed) is not date:
        raise TypeError('claimed deadline must be a date')
    result = minnesota_deadline(start, days, calendar, rule_applies=rule_applies, successive_weeks=successive_weeks, calendar_months=calendar_months, max_roll=max_roll)
    if result.status != 'computed' or result.value != claimed:
        return None
    first = start.toordinal() + days
    last = min(first + max_roll, date.max.toordinal())
    if not calendar.first.toordinal() <= first <= last <= calendar.last.toordinal():
        return None
    rows = []
    for ordinal in range(first, last + 1):
        candidate = date.fromordinal(ordinal)
        rows.append(dict(date=candidate.isoformat(), weekday=candidate.weekday(), holiday=candidate in calendar.holidays))
    artifact = dict(version=1, subject=_subject(start, days, calendar, rule_applies, successive_weeks, calendar_months, max_roll), claim=claimed.isoformat(), candidates=rows)
    text = json.dumps(artifact, sort_keys=True, separators=(',', ':'), ensure_ascii=True)
    if len(text.encode()) > 262144:
        return None
    checked = check_deadline_certificate(text, expected_subject=artifact['subject'])
    return text if checked.status == 'checked' else None


def check_deadline_certificate(text, *, expected_subject=None):
    """Replay finite least-endpoint evidence using native ground arithmetic.

    A self-contained artifact establishes only its declared conditional subject.
    Pass expected_subject to bind it to an external query. Calendar completeness,
    source authority and legal applicability remain explicit assumptions.
    """
    import json
    from . import ir
    if not isinstance(text, str):
        raise TypeError('certificate must be text')
    if len(text) > 262144:
        return DeadlineCertificateCheck('resource-limited', 'certificate exceeds 256 KiB')
    try:
        encoded_size = len(text.encode())
    except UnicodeEncodeError:
        return DeadlineCertificateCheck('rejected', 'invalid Unicode encoding')
    if encoded_size > 262144:
        return DeadlineCertificateCheck('resource-limited', 'certificate exceeds 256 KiB')
    try:
        def unique_object(pairs):
            result = {}
            for key, value in pairs:
                if key in result:
                    raise ValueError('duplicate certificate field')
                result[key] = value
            return result
        artifact = json.loads(text, object_pairs_hook=unique_object)
        if type(artifact) is not dict or set(artifact) != {'version', 'subject', 'claim', 'candidates'}:
            raise ValueError('malformed certificate envelope')
        if type(artifact['version']) is not int:
            raise ValueError('version must be an integer')
        if artifact['version'] != 1:
            return DeadlineCertificateCheck('unsupported', 'unknown certificate version')
        subject = artifact['subject']
        keys = {'start', 'days', 'calendar_first', 'calendar_last', 'holidays', 'calendar_source', 'rule_applies', 'successive_weeks', 'calendar_months', 'max_roll'}
        if type(subject) is not dict or set(subject) != keys:
            raise ValueError('malformed conditional subject')
        if expected_subject is not None:
            if type(expected_subject) is not dict or json.dumps(subject, sort_keys=True) != json.dumps(expected_subject, sort_keys=True):
                raise ValueError('source subject does not match the expected query')
        def exact_date(value):
            if type(value) is not str:
                raise ValueError('date must be canonical text')
            parsed = date.fromisoformat(value)
            if parsed.isoformat() != value:
                raise ValueError('date must use canonical ISO syntax')
            return parsed
        start = exact_date(subject['start'])
        days, roll = subject['days'], subject['max_roll']
        if type(days) is not int or not 1 <= days <= 36600 or type(roll) is not int or not 0 <= roll <= 366:
            raise ValueError('invalid day/rollover limits')
        flags = [subject[name] for name in ('rule_applies', 'successive_weeks', 'calendar_months')]
        if any(type(flag) is not bool for flag in flags) or flags != [True, False, False]:
            raise ValueError('unsupported applicability assumptions')
        holiday_text = subject['holidays']
        if type(holiday_text) is not list or len(holiday_text) > 4096:
            raise ValueError('malformed holiday population')
        holiday_dates = [exact_date(value) for value in holiday_text]
        if holiday_text != sorted(set(holiday_text)):
            raise ValueError('holiday population must be ordered and unique')
        calendar = HolidayCalendar(exact_date(subject['calendar_first']), exact_date(subject['calendar_last']), frozenset(holiday_dates), subject['calendar_source'])
        first = start.toordinal() + days
        last = min(first + roll, date.max.toordinal())
        if not calendar.first.toordinal() <= first <= last <= calendar.last.toordinal():
            raise ValueError('incomplete calendar coverage')
        claimed = exact_date(artifact['claim']).toordinal()
        if not first <= claimed <= last:
            raise ValueError('claim outside the candidate window')
        rows = artifact['candidates']
        if type(rows) is not list or len(rows) != last - first + 1:
            raise ValueError('incomplete candidate population')
        arena = ir.Arena()
        assignment = arena.assignment()
        count = 0
        for ordinal, row in zip(range(first, last + 1), rows):
            if type(row) is not dict or set(row) != {'date', 'weekday', 'holiday'}:
                raise ValueError('malformed candidate witness')
            candidate = exact_date(row['date'])
            if candidate.toordinal() != ordinal:
                raise ValueError('candidate order/location mismatch')
            weekday = ir.eval(arena, arena.int_mod(arena.int_sub(arena.int_const(ordinal), arena.int_const(1)), arena.int_const(7)), assignment)
            holiday = candidate in calendar.holidays
            if type(row['weekday']) is not int or row['weekday'] != weekday or type(row['holiday']) is not bool or row['holiday'] != holiday:
                raise ValueError('candidate arithmetic/calendar witness mismatch')
            allowed = weekday < 5 and not holiday
            if (ordinal < claimed and allowed) or (ordinal == claimed and not allowed):
                raise ValueError('claim is not the first admitted endpoint')
            count += 1
        return DeadlineCertificateCheck('checked', 'finite least endpoint under declared calendar/applicability assumptions; no kernel admission', count)
    except (ValueError, TypeError, KeyError, OverflowError, RecursionError) as error:
        return DeadlineCertificateCheck('rejected', str(error))
