from datetime import date
from pathlib import Path
import json
import pytest
from axeyum.rules import Pack

ROOT = Path(__file__).resolve().parents[2] / 'docs/rules-as-code/examples'


def test_load_existing_authoritative_pack_population():
    metadata = sorted(ROOT.glob('*/metadata.json'))
    assert len(metadata) == 7
    for path in metadata:
        pack = Pack(path.parent)
        assert pack.metadata['id'] == json.loads(path.read_text())['id']
        assert pack.expected['pack_id'] == pack.metadata['id']


def test_benefit_witnesses_match_replayed_typed_evaluation():
    pack = Pack(ROOT / 'benefit-eligibility-v0')
    assert pack.expected['witnesses']
    for row in pack.expected['witnesses']:
        facts = dict(row['facts'])
        facts['application_date'] = date.fromisoformat(facts['application_date'])
        outcome = pack.evaluate(facts)
        assert outcome.status == 'sat-replayed'
        assert outcome.outputs == {'eligible': row['expected_eligible'], 'ineligible': not row['expected_eligible']}
        assert outcome.source_citations == tuple(pack.metadata['source_citations'])


def test_missing_and_malformed_inputs_are_not_false_facts():
    pack = Pack(ROOT / 'benefit-eligibility-v0')
    result = pack.evaluate({'resident': True})
    assert result.status == 'missing-inputs'
    assert result.outputs == {} and 'sanctioned' in result.missing
    assert result.result is None
    with pytest.raises(TypeError):
        pack.evaluate({'age': True})
    with pytest.raises(ValueError):
        pack.evaluate({'invented': False})


def test_existing_native_obligations_retain_verdicts():
    results = Pack(ROOT / 'benefit-eligibility-v0').check_obligations()
    fixtures = list((ROOT / 'benefit-eligibility-v0/smt2').glob('*.smt2'))
    assert len(results) == len(fixtures) == 4
    assert all(result.status == 'unsat' for result in results.values())


def test_effective_start_boundary_has_explicit_applicability():
    pack = Pack(ROOT / 'benefit-eligibility-v0')
    facts = dict(pack.expected['witnesses'][0]['facts'])
    facts['application_date'] = date(2025, 12, 31)
    assert pack.evaluate(facts).status == 'outside-effective-interval'
    facts['application_date'] = date(2026, 1, 1)
    assert pack.evaluate(facts).status == 'sat-replayed'


@pytest.mark.parametrize('directory,output,expected_key', [('tax-benefit-arithmetic-v0', 'benefit', 'expected_benefit'), ('procurement-scoring-v0', 'award', 'expected_award')])
def test_temporal_arithmetic_pack_witnesses(directory, output, expected_key):
    pack = Pack(ROOT / directory)
    assert pack.expected['witnesses']
    for row in pack.expected['witnesses']:
        facts = dict(row['facts'])
        for declaration in pack.metadata['inputs']:
            if declaration['sort'] == 'Date':
                name = declaration['name']
                facts[name] = date.fromisoformat(facts[name])
        result = pack.evaluate(facts)
        assert result.status == 'sat-replayed'
        assert result.outputs == {output: row[expected_key]}


def test_arithmetic_domain_failure_has_no_outputs():
    pack = Pack(ROOT / 'tax-benefit-arithmetic-v0')
    result = pack.evaluate({'income': 0, 'household_size': 0, 'application_date': date(2026, 7, 1)})
    assert result.status == 'unsat'
    assert result.outputs == {}


@pytest.mark.parametrize('directory,family_id,output,expected_key,count', [('tax-benefit-arithmetic-v0', 'bounded_benefits', 'benefit', 'expected_benefit', 66), ('procurement-scoring-v0', 'bounded_awards', 'award', 'expected_award', 144)])
def test_complete_generated_arithmetic_populations(directory, family_id, output, expected_key, count):
    pack = Pack(ROOT / directory)
    generated = json.loads((ROOT.parent / 'generated/queries' / f'{directory}.json').read_text())
    family = next(row for row in generated['query_families'] if row['id'] == family_id)
    assert len(family['rows']) == family['row_count'] == count
    for row in family['rows']:
        facts = dict(row['facts'])
        for declaration in pack.metadata['inputs']:
            if declaration['sort'] == 'Date':
                name = declaration['name']
                facts[name] = date.fromisoformat(facts[name])
        result = pack.evaluate(facts)
        assert result.status == 'sat-replayed'
        assert result.outputs == {output: row[expected_key]}


@pytest.mark.parametrize('directory,family_id,outputs,count', [('authorization-policy-v0', 'bounded_requests', {'allow': 'expected_allow'}, 96), ('category-equivalence-v0', 'bounded_category_rows', {'priority_review': 'expected_priority_review'}, 6), ('grant-allocation-v0', 'bounded_allocations', {'compliant': 'expected_compliant'}, 125), ('workflow-reachability-v0', 'bounded_transition_rows', {'transition_allowed': 'expected_allowed', 'next_state': 'expected_next_state'}, 24)])
def test_enum_and_real_generated_populations(directory, family_id, outputs, count):
    from fractions import Fraction
    pack = Pack(ROOT / directory)
    generated = json.loads((ROOT.parent / 'generated/queries' / f'{directory}.json').read_text())
    family = next(row for row in generated['query_families'] if row['id'] == family_id)
    assert len(family['rows']) == family['row_count'] == count
    for row in family['rows']:
        facts = dict(row['facts'])
        for declaration in pack.metadata['inputs']:
            if declaration['sort'] == 'Real':
                facts[declaration['name']] = Fraction(facts[declaration['name']])
        result = pack.evaluate(facts, as_of=date(2026, 7, 1))
        assert result.status == 'sat-replayed'
        assert result.outputs == {key: row[expected] for key, expected in outputs.items()}


def test_enum_rational_types_and_applicability_are_explicit():
    from fractions import Fraction
    authorization = Pack(ROOT / 'authorization-policy-v0')
    facts = dict(authorization.expected['witnesses'][0]['facts'])
    assert authorization.evaluate(facts).missing == ('as_of',)
    assert authorization.evaluate(facts, as_of=date(2025, 12, 31)).status == 'outside-effective-interval'
    facts['role'] = 'invented'
    with pytest.raises(TypeError, match='enum'):
        authorization.evaluate(facts, as_of=date(2026, 7, 1))
    allocation = Pack(ROOT / 'grant-allocation-v0')
    shares = {'shelter_share': Fraction(1, 2), 'clinic_share': Fraction(1, 4), 'admin_share': Fraction(1, 4)}
    assert allocation.evaluate(shares, as_of=date(2026, 7, 1)).outputs == {'compliant': True}
    with pytest.raises(TypeError, match='exact'):
        allocation.evaluate({**shares, 'shelter_share': 0.5}, as_of=date(2026, 7, 1))
    with pytest.raises(ValueError, match='127-bit'):
        allocation.evaluate({**shares, 'shelter_share': Fraction(1, 1 << 128)}, as_of=date(2026, 7, 1))


def test_lifted_enum_rejects_negative_model_ordinal(monkeypatch):
    from axeyum.rules import Context
    original = Context.lift_model
    def tampered(self, result, assertions=()):
        model = original(self, result, assertions)
        if 'next_state' in model:
            model['next_state'] = -1
        return model
    monkeypatch.setattr(Context, 'lift_model', tampered)
    pack = Pack(ROOT / 'workflow-reachability-v0')
    with pytest.raises(ValueError, match='enum model'):
        pack.evaluate({'current_state': 'submitted', 'action': 'request_review', 'supervisor_review': False}, as_of=date(2026, 7, 1))
