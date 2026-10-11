"""Typed Gregorian dates lowered to existing integer terms (ADR-3200)."""
from datetime import date as _date
from dataclasses import dataclass
from . import ir, solver


@dataclass(frozen=True, eq=False)
class Duration:
    """A symbolic signed number of days; distinct from a calendar date."""
    context: 'Context'
    term: ir.Term


@dataclass(frozen=True, eq=False)
class Date:
    """Symbolic Gregorian date in years 1–9999, with retained source sort."""
    context: 'Context'
    term: ir.Term

    def _other(self, other):
        if not isinstance(other, Date) or other.context is not self.context:
            raise TypeError('Date comparison requires dates from the same context')
        return other.term

    def __bool__(self):
        raise TypeError('a symbolic Date has no Python truth value')

    def __eq__(self, other):
        return self.context.arena.eq(self.term, self._other(other))

    def __ne__(self, other):
        return self.context.arena.not_(self == other)

    def __lt__(self, other):
        return self.context.arena.int_lt(self.term, self._other(other))

    def __le__(self, other):
        return self.context.arena.int_le(self.term, self._other(other))

    def __gt__(self, other):
        return self.context.arena.int_gt(self.term, self._other(other))

    def __ge__(self, other):
        return self.context.arena.int_ge(self.term, self._other(other))

    def __add__(self, days):
        if not isinstance(days, Duration) or days.context is not self.context:
            raise TypeError('Date addition requires a Duration from the same context')
        return self.context._date(self.context.arena.int_add(self.term, days.term))

    def __sub__(self, other):
        if isinstance(other, Date):
            return Duration(self.context, self.context.arena.int_sub(self.term, self._other(other)))
        if not isinstance(other, Duration) or other.context is not self.context:
            raise TypeError('Date subtraction requires Date or Duration from the same context')
        return self.context._date(self.context.arena.int_sub(self.term, other.term))


class Context:
    """Owns lowering metadata and range obligations for a typed date query."""
    def __init__(self):
        self.arena = ir.Arena()
        self._constraints = []
        self._sorts = {}

    @property
    def constraints(self):
        return tuple(self._constraints)

    @property
    def source_sorts(self):
        return dict(self._sorts)

    def _date(self, term):
        self._constraints.extend((self.arena.int_ge(term, self.arena.int_const(1)), self.arena.int_le(term, self.arena.int_const(_date.max.toordinal()))))
        return Date(self, term)

    def _name(self, name, sort):
        if not isinstance(name, str) or not name or name in self._sorts:
            raise ValueError('declaration name must be nonempty and unique')
        self._sorts[name] = sort

    def date_var(self, name: str) -> Date:
        self._name(name, 'Date')
        return self._date(self.arena.int_var(name))

    def duration_var(self, name: str) -> Duration:
        self._name(name, 'Duration')
        return Duration(self, self.arena.int_var(name))

    def date(self, value: _date) -> Date:
        if type(value) is not _date:
            raise TypeError('expected datetime.date, excluding datetime/timezone values')
        return self._date(self.arena.int_const(value.toordinal()))

    def days(self, value: int) -> Duration:
        if type(value) is not int:
            raise TypeError('duration must be an integer number of days')
        return Duration(self, self.arena.int_const(value))

    def lower(self, assertions):
        """Complete query for native solve/replay, including all Date ranges."""
        return [*self._constraints, *assertions]

    def solve(self, assertions=(), config=None):
        return solver.solve(self.arena, self.lower(assertions), config)

    def lift_model(self, result, assertions=()):
        """Retain omitted values; convert named Date ordinals after SAT replay."""
        if not result.is_sat():
            raise ValueError('model lifting requires a SAT result')
        if not result.replay(self.arena, self.lower(assertions)):
            raise ValueError('model does not replay against the complete Date query')
        model = result.model(self.arena)
        for name, sort in self._sorts.items():
            if name in model and sort == 'Date':
                ordinal = model[name]
                if type(ordinal) is not int:
                    raise ValueError('Date model value must be an integer ordinal')
                model[name] = _date.fromordinal(ordinal)
        return model


@dataclass(frozen=True)
class Evaluation:
    """Native verdict and replayed outputs, or explicit missing inputs."""
    status: str
    outputs: dict
    missing: tuple
    source_citations: tuple
    result: object = None


class Pack:
    """Load existing pack metadata and expose its native obligation fixtures."""
    def __init__(self, directory):
        import json
        from pathlib import Path
        self.directory = Path(directory).resolve()
        def read(name):
            path = self.directory / name
            if path.stat().st_size > 1_048_576:
                raise ValueError('pack document exceeds 1 MiB')
            return json.loads(path.read_text())
        self.metadata = read('metadata.json')
        self.expected = read('expected.json')
        if self.metadata.get('schema_version') != 1 or self.expected.get('schema_version') != 1:
            raise ValueError('unsupported pack schema version')
        if self.expected.get('pack_id') != self.metadata.get('id'):
            raise ValueError('pack metadata and expected identity differ')

    def check_obligations(self, *, timeout_ms=10000):
        """Return native outcomes; UNSAT alone is not a proof-check claim."""
        from . import smt
        results = {}
        paths = sorted((self.directory / 'smt2').glob('*.smt2'))
        if not paths:
            raise ValueError('pack has no SMT obligation fixtures')
        for path in paths:
            if path.stat().st_size > 1_048_576:
                raise ValueError('obligation exceeds 1 MiB')
            results[path.name] = smt.solve(path.read_text(), timeout_ms=timeout_ms, prove_unsat=True)
        return results

    def evaluate(self, facts, *, config=None, as_of=None):
        """Evaluate supported packs with typed facts and SAT replay."""
        pack_id = self.metadata['id']
        if pack_id in ('authorization_policy_v0', 'category_equivalence_v0', 'grant_allocation_v0', 'workflow_reachability_v0'):
            return self._evaluate_finite(facts, config, as_of)
        if pack_id not in ('benefit_eligibility_v0', 'tax_benefit_arithmetic_v0', 'procurement_scoring_v0'):
            raise NotImplementedError('this pack has obligation loading but no typed evaluator yet')
        inputs = {row['name']: row['sort'] for row in self.metadata['inputs']}
        contracts = {
            'benefit_eligibility_v0': {'age', 'income', 'resident', 'veteran', 'sanctioned', 'application_date'},
            'tax_benefit_arithmetic_v0': {'income', 'household_size', 'application_date'},
            'procurement_scoring_v0': {'bid_amount', 'quality_score', 'small_business', 'debarred', 'received_date'},
        }
        if set(inputs) != contracts[pack_id]:
            raise ValueError('benefit pack inputs do not match the supported contract')
        if set(facts) - set(inputs):
            raise ValueError('unknown input facts')
        for name, value in facts.items():
            sort = inputs[name]
            expected = {'Int': int, 'Bool': bool, 'Date': _date}.get(sort)
            if expected is None or type(value) is not expected:
                raise TypeError(f'{name} requires {sort}')
        citations = tuple(dict(row) for row in self.metadata['source_citations'])
        missing = tuple(sorted(set(inputs) - set(facts)))
        if missing:
            return Evaluation('missing-inputs', {}, missing, citations)
        interval = self.metadata['effective_interval']
        application = facts.get('application_date', facts.get('received_date'))
        if ((interval.get('from') and application < _date.fromisoformat(interval['from']))
                or (interval.get('to') and application >= _date.fromisoformat(interval['to']))):
            return Evaluation('outside-effective-interval', {}, (), citations)
        ctx = Context()
        arena = ctx.arena
        terms, assertions = {}, []
        for name, sort in inputs.items():
            if sort == 'Date':
                terms[name] = ctx.date_var(name).term
                value = ctx.date(facts[name]).term
            else:
                ctx._name(name, sort)
                terms[name] = arena.int_var(name) if sort == 'Int' else arena.bool_var(name)
                value = arena.int_const(facts[name]) if sort == 'Int' else arena.bool_const(facts[name])
            assertions.append(arena.eq(terms[name], value))
        params = self.expected['parameters']
        if pack_id != 'benefit_eligibility_v0':
            return self._evaluate_arithmetic(ctx, terms, assertions, params, citations, config)
        cutoff = ctx.date(_date.fromisoformat(params['change_date'])).term
        threshold = arena.ite(arena.int_lt(terms['application_date'], cutoff), arena.int_const(params['standard_threshold_before']), arena.int_const(params['standard_threshold_after']))
        income_allowed = arena.or_(arena.int_le(terms['income'], threshold), arena.and_(terms['veteran'], arena.int_le(terms['income'], arena.int_add(threshold, arena.int_const(params['veteran_bonus'])))))
        predicate = arena.and_(arena.and_(terms['resident'], arena.int_ge(terms['age'], arena.int_const(18))), arena.and_(arena.not_(terms['sanctioned']), income_allowed))
        eligible, ineligible = arena.bool_var('eligible'), arena.bool_var('ineligible')
        assertions.extend((arena.eq(eligible, predicate), arena.eq(ineligible, arena.not_(eligible))))
        result = ctx.solve(assertions, config)
        if result.is_sat():
            model = ctx.lift_model(result, assertions)
            if 'eligible' not in model or 'ineligible' not in model:
                raise ValueError('solver omitted required rule outputs')
            return Evaluation('sat-replayed', {key: model[key] for key in ('eligible', 'ineligible')}, (), citations, result)
        return Evaluation(result.status, {}, (), citations, result)

    def _evaluate_arithmetic(self, ctx, terms, assertions, params, citations, config):
        arena = ctx.arena
        integer = arena.int_const
        if self.metadata['id'] == 'tax_benefit_arithmetic_v0':
            if params['max_household_size'] < 1:
                raise ValueError('invalid household-size domain')
            assertions.extend((arena.int_ge(terms['income'], integer(0)), arena.int_ge(terms['household_size'], integer(1)), arena.int_le(terms['household_size'], integer(params['max_household_size']))))
            cutoff = ctx.date(_date.fromisoformat(params['change_date'])).term
            phase = arena.ite(arena.int_lt(terms['application_date'], cutoff), integer(params['phase_start_before']), integer(params['phase_start_after']))
            base = arena.int_add(integer(params['base_credit']), arena.int_mul(integer(params['household_adjustment']), arena.int_sub(terms['household_size'], integer(1))))
            capped = arena.ite(arena.int_le(base, integer(params['credit_cap'])), base, integer(params['credit_cap']))
            excess = arena.int_sub(terms['income'], phase)
            positive_excess = arena.ite(arena.int_ge(excess, integer(0)), excess, integer(0))
            raw = arena.int_sub(capped, arena.int_mul(integer(params['phaseout_rate']), positive_excess))
            expression = arena.ite(arena.int_ge(raw, integer(0)), raw, integer(0))
            name = 'benefit'
            output = arena.int_var(name)
        else:
            assertions.extend((arena.int_ge(terms['quality_score'], integer(params['min_quality_score'])), arena.int_le(terms['quality_score'], integer(params['max_quality_score']))))
            adjusted = arena.int_add(terms['quality_score'], arena.ite(terms['small_business'], integer(params['small_business_bonus']), integer(0)))
            deadline = ctx.date(_date.fromisoformat(params['deadline'])).term
            expression = arena.and_(arena.and_(arena.not_(terms['debarred']), arena.int_le(terms['received_date'], deadline)), arena.and_(arena.int_le(terms['bid_amount'], integer(params['max_bid'])), arena.int_ge(adjusted, integer(params['award_threshold']))))
            name = 'award'
            output = arena.bool_var(name)
        assertions.append(arena.eq(output, expression))
        result = ctx.solve(assertions, config)
        if result.is_sat():
            model = ctx.lift_model(result, assertions)
            if name not in model:
                raise ValueError('solver omitted required rule output')
            return Evaluation('sat-replayed', {name: model[name]}, (), citations, result)
        return Evaluation(result.status, {}, (), citations, result)

    def _evaluate_finite(self, facts, config, as_of):
        from fractions import Fraction
        inputs = {row['name']: row['sort'] for row in self.metadata['inputs']}
        if set(facts) - set(inputs):
            raise ValueError('unknown input facts')
        enum_maps = {}
        for name, sort in inputs.items():
            if sort.startswith('Enum(') and sort.endswith(')'):
                labels = sort[5:-1].split(',')
                if not labels or len(set(labels)) != len(labels):
                    raise ValueError('invalid enum declaration')
                enum_maps[name] = labels
        for name, value in facts.items():
            sort = inputs[name]
            if name in enum_maps:
                if type(value) is not str or value not in enum_maps[name]:
                    raise TypeError(f'{name} requires an admitted enum label')
            elif sort == 'Real':
                if type(value) not in (int, Fraction):
                    raise TypeError(f'{name} requires an exact Fraction or integer')
            elif {'Int': int, 'Bool': bool}.get(sort) is not type(value):
                raise TypeError(f'{name} requires {sort}')
        if as_of is not None and type(as_of) is not _date:
            raise TypeError('as_of requires datetime.date')
        missing = sorted(set(inputs) - set(facts))
        if as_of is None:
            missing.append('as_of')
        citations = tuple(dict(row) for row in self.metadata['source_citations'])
        if missing:
            return Evaluation('missing-inputs', {}, tuple(sorted(missing)), citations)
        interval = self.metadata['effective_interval']
        if ((interval.get('from') and as_of < _date.fromisoformat(interval['from']))
                or (interval.get('to') and as_of >= _date.fromisoformat(interval['to']))):
            return Evaluation('outside-effective-interval', {}, (), citations)
        ctx = Context()
        a = ctx.arena
        terms, assertions = {}, []
        def real(value):
            fraction = Fraction(value)
            if max(abs(fraction.numerator).bit_length(), fraction.denominator.bit_length()) > 127:
                raise ValueError('rule Real components exceed the current 127-bit binding limit')
            return a.real_div(a.real_const(fraction.numerator), a.real_const(fraction.denominator))
        for name, sort in inputs.items():
            ctx._name(name, sort)
            if name in enum_maps:
                terms[name] = a.int_var(name)
                value = a.int_const(enum_maps[name].index(facts[name]))
                assertions.extend((a.int_ge(terms[name], a.int_const(0)), a.int_lt(terms[name], a.int_const(len(enum_maps[name])))))
            elif sort == 'Real':
                terms[name], value = a.real_var(name), real(facts[name])
            elif sort == 'Bool':
                terms[name], value = a.bool_var(name), a.bool_const(facts[name])
            else:
                terms[name], value = a.int_var(name), a.int_const(facts[name])
            assertions.append(a.eq(terms[name], value))
        def label(name, value):
            return a.eq(terms[name], a.int_const(enum_maps[name].index(value)))
        def conjunction(values):
            result = a.bool_const(True)
            for value in values:
                result = a.and_(result, value)
            return result
        params = self.expected['parameters']
        identity = self.metadata['id']
        output_maps = {}
        if identity == 'authorization_policy_v0':
            permits = a.or_(a.and_(label('role', 'admin'), a.or_(label('action', 'read'), label('action', 'export'))), a.and_(label('role', 'analyst'), a.or_(label('action', 'read'), a.and_(label('action', 'export'), a.int_ge(terms['policy_version'], a.int_const(2))))))
            expressions = {'allow': conjunction((a.eq(terms['user_tenant'], terms['resource_tenant']), a.not_(terms['explicit_deny']), permits))}
        elif identity == 'category_equivalence_v0':
            # The shipped model has one local equivalence pair. Decline a changed
            # family rather than assuming an unimplemented transitive closure.
            if len(params['equivalence_pairs']) != 1:
                raise ValueError('category evaluator requires one equivalence pair')
            left, right = params['equivalence_pairs'][0]
            expressions = {'priority_review': a.and_(a.or_(label('applicant_category', left), label('applicant_category', right)), label('program', params['priority_program']))}
        elif identity == 'grant_allocation_v0':
            shelter, clinic, admin = (terms[name] for name in ('shelter_share', 'clinic_share', 'admin_share'))
            expressions = {'compliant': conjunction((a.eq(a.real_add(a.real_add(shelter, clinic), admin), real(params['total_share'])), a.real_ge(shelter, real(params['shelter_minimum'])), a.real_ge(clinic, real(params['clinic_minimum'])), a.real_le(admin, real(params['admin_cap'])), a.real_ge(shelter, real(0)), a.real_ge(clinic, real(0)), a.real_ge(admin, real(0))))}
        else:
            states = enum_maps['current_state']
            review = a.and_(label('current_state', params['initial_state']), label('action', 'request_review'))
            approve = conjunction((label('current_state', params['review_state']), label('action', 'approve'), terms['supervisor_review']))
            reject = a.and_(label('current_state', params['review_state']), label('action', 'reject'))
            next_state = a.ite(review, a.int_const(states.index(params['review_state'])), a.ite(approve, a.int_const(states.index(params['approved_state'])), a.ite(reject, a.int_const(states.index(params['rejected_state'])), terms['current_state'])))
            expressions = {'transition_allowed': a.or_(review, a.or_(approve, reject)), 'next_state': next_state}
            output_maps['next_state'] = states
        for name, expression in expressions.items():
            output = a.int_var(name) if name in output_maps else a.bool_var(name)
            assertions.append(a.eq(output, expression))
        result = ctx.solve(assertions, config)
        if not result.is_sat():
            return Evaluation(result.status, {}, (), citations, result)
        model = ctx.lift_model(result, assertions)
        if any(name not in model for name in expressions):
            raise ValueError('solver omitted required rule output')
        outputs = {name: model[name] for name in expressions}
        for name, labels in output_maps.items():
            ordinal = outputs[name]
            if type(ordinal) is not int or not 0 <= ordinal < len(labels):
                raise ValueError('invalid enum model value')
            outputs[name] = labels[ordinal]
        return Evaluation('sat-replayed', outputs, (), citations, result)


from ._rules_deadline import Deadline, HolidayCalendar, minnesota_deadline
from ._rules_deadline import DeadlineObligation, DeadlineVerification, verify_minnesota_deadline
from ._rules_deadline import DeadlineCertificateCheck, check_deadline_certificate, deadline_certificate
