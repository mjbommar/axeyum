"""`axeyum.knowledge.operations`: generality is measured, never labelled.

The defect this module is written against: a registry where every entry names
one fact is a dispatch table, and a dispatch table cannot fail to produce. So
the tests assert that ``n_targets`` tracks ``applicability.fact_ids`` and
nothing else, and that the driver allowlist is the validator's own object rather
than a copy of it.
"""

from __future__ import annotations

import json
import subprocess
import sys

import pytest

from axeyum.knowledge import operations
from axeyum.knowledge._paths import repo_root

ROOT = repo_root()
VALIDATOR = ROOT / "scripts" / "validate-autogenesis-operations.py"


def test_the_canonical_validator_accepts_the_registry() -> None:
    completed = subprocess.run(
        [sys.executable, str(VALIDATOR)],
        capture_output=True,
        text=True,
        timeout=300,
        check=False,
        cwd=str(ROOT),
    )
    assert completed.returncode == 0, completed.stderr
    line = [
        ln for ln in completed.stdout.splitlines() if ln.startswith("AUTOGENESIS_OPERATIONS_OK")
    ]
    assert line, completed.stdout
    reported = int(line[0].split("operations=", 1)[1].split("|", 1)[0])
    assert reported > 0
    assert len(operations.load(ROOT)) == reported


def test_execution_drivers_come_from_the_validator_not_a_copy() -> None:
    drivers = operations.execution_drivers(ROOT)
    assert len(drivers) > 0
    source = VALIDATOR.read_text(encoding="utf-8")
    for driver in drivers:
        assert f'"{driver}"' in source, "the allowlist was copied, not read"


def test_every_driver_in_use_is_allowlisted() -> None:
    registry = operations.load(ROOT)
    assert len(registry.drivers_in_use()) > 0
    assert registry.unknown_drivers() == frozenset()


def test_n_targets_is_derived_only_from_fact_ids() -> None:
    registry = operations.load(ROOT)
    assert len(registry) > 0
    for op in registry:
        assert op.n_targets == len(op.applicability.fact_ids)
        assert op.is_multi_target == (len(op.applicability.fact_ids) > 1)


def test_a_relabelled_operation_does_not_become_general() -> None:
    """Rename an operation to say `multi-target` and nothing must change."""
    registry = operations.load(ROOT)
    single = next(op for op in registry if op.n_targets == 1)
    relabelled = operations.Operation.from_raw(
        {
            **single.raw,
            "id": single.id + "-multi-target-general-reusable",
        }
    )
    assert relabelled.n_targets == 1
    assert not relabelled.is_multi_target


def test_the_generality_measurement_is_visible() -> None:
    registry = operations.load(ROOT)
    multi = registry.multi_target()
    # This is the number the programme is trying to raise; it must be readable
    # and it must be small enough that nobody mistakes the registry for a
    # producer population.
    assert len(multi) < len(registry)
    assert all(op.n_targets > 1 for op in multi)


def test_scopes_are_the_validators_scopes() -> None:
    registry = operations.load(ROOT)
    assert set(registry.by_scope()) <= operations.SCOPES
    # Reaching into the private loader is the contract under test.
    module = operations._validator_module(str(ROOT))
    assert operations.SCOPES == frozenset(module.SCOPES)


def test_admission_contracts_are_read_from_the_validator() -> None:
    contracts = operations.admission_contracts(ROOT)
    assert len(contracts) > 0
    registry = operations.load(ROOT)
    for op in registry:
        if op.is_authoritative:
            assert op.admission.contract in contracts


def test_sealed_capsule_contracts_are_pinned_per_fact() -> None:
    contracts = operations.sealed_capsule_contracts(ROOT)
    assert len(contracts) > 0
    for fact_id, contract in contracts.items():
        assert fact_id.startswith("F:")
        assert len(contract["capsule_sha256"]) == 64
        assert len(contract["receipt_sha256"]) == 64


def test_covering_is_empty_only_after_reading_the_registry() -> None:
    registry = operations.load(ROOT)
    assert registry.covering("F:definitely-not-registered") == ()
    assert len(registry.covered_fact_ids()) > 0


def test_get_raises_for_an_unknown_operation() -> None:
    with pytest.raises(KeyError):
        operations.get("no-such-operation-v1", ROOT)


def test_registry_json_round_trips_the_ids() -> None:
    document = json.loads((ROOT / operations.REGISTRY_PATH).read_text(encoding="utf-8"))
    assert [op.id for op in operations.load(ROOT)] == [row["id"] for row in document["operations"]]
