"""`axeyum.knowledge.nursery`: partition questions answered by partition.

Two things are checked here that prose alone did not keep true:

* :func:`held_out_ids` returns exactly what
  ``check-autogenesis-holdout-isolation.py`` protects -- compared against the
  gate's own printed count, in a subprocess.
* a fixture referencing a held-out id fails :func:`is_safe_to_reference`, so the
  filter demonstrably fires rather than merely existing.

The trap the third test encodes: "dependency-ready" and "train + development"
are both 138 and are **different sets**.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from axeyum.knowledge import facts, frontier, nursery
from axeyum.knowledge._paths import repo_root

ROOT = repo_root()
GATE = ROOT / "scripts" / nursery.GATE


@pytest.fixture(scope="module")
def gate_line() -> str:
    completed = subprocess.run(
        [sys.executable, str(GATE)],
        capture_output=True,
        text=True,
        timeout=600,
        check=False,
        cwd=str(ROOT),
    )
    assert completed.returncode == 0, completed.stderr
    lines = [ln for ln in completed.stdout.splitlines() if ln.startswith("AUTOGENESIS_HOLDOUT")]
    assert lines, completed.stdout
    return lines[0]


def _field(line: str, key: str) -> str:
    for part in line.split("|"):
        if part.startswith(f"{key}="):
            return part.split("=", 1)[1]
    raise AssertionError(f"{key} not in {line!r}")


def test_held_out_ids_equal_the_gates_population(gate_line: str) -> None:
    reported = int(_field(gate_line, "held_out"))
    assert reported > 0, "an empty held-out population would pass every gate vacuously"
    assert len(nursery.held_out_ids(ROOT)) == reported


def test_the_gate_actually_scanned_files(gate_line: str) -> None:
    assert int(_field(gate_line, "files_scanned")) > 0
    assert _field(gate_line, "verdict") == "PASS"


def test_held_out_ids_are_derived_from_the_partition_field() -> None:
    manifest = json.loads((ROOT / nursery.NURSERY_PATH).read_text(encoding="utf-8"))
    expected = {
        row["fact_id"] for row in manifest["entries"] if row.get("partition") == nursery.HELD_OUT
    }
    assert nursery.held_out_ids(ROOT) == frozenset(expected)


def test_a_held_out_reference_is_refused() -> None:
    held = sorted(nursery.held_out_ids(ROOT))
    assert held
    for fact_id in held:
        assert not nursery.is_safe_to_reference(fact_id, ROOT)


def test_a_train_fact_is_safe_to_reference() -> None:
    loaded = nursery.load(ROOT)
    train = loaded.partition("train")
    assert train
    assert all(loaded.is_safe_to_reference(row.fact_id) for row in train)


def test_filter_safe_removes_exactly_the_held_out_ids() -> None:
    loaded = nursery.load(ROOT)
    held = sorted(loaded.held_out_ids())
    train = [row.fact_id for row in loaded.partition("train")][:5]
    mixed = held[:3] + train
    filtered = loaded.filter_safe(mixed)
    assert set(filtered) == set(train)
    assert len(filtered) < len(mixed)


def test_partition_of_raises_for_a_fact_outside_the_population() -> None:
    with pytest.raises(KeyError):
        nursery.partition_of("F:not-preregistered-anywhere", ROOT)


def test_outside_the_population_is_safe_but_distinguishable() -> None:
    loaded = nursery.load(ROOT)
    assert loaded.is_safe_to_reference("F:not-preregistered-anywhere")
    assert not loaded.contains("F:not-preregistered-anywhere")


def test_an_unknown_partition_raises_rather_than_reading_as_empty() -> None:
    with pytest.raises(KeyError):
        nursery.load(ROOT).partition("holdout")


def test_dependency_ready_is_not_train_plus_development() -> None:
    """Both are 138 today and they are different sets."""
    loaded = nursery.load(ROOT)
    train_dev = {row.fact_id for row in loaded.partition("train") + loaded.partition("development")}
    ready = {row.fact_id for row in frontier.load(ROOT).dependency_ready()}
    ready_in_population = {fid for fid in ready if loaded.contains(fid)}
    assert ready_in_population != train_dev, "a count-based answer would have passed here"
    # And the ready set genuinely reaches into held-out.
    ready_partitions = {loaded.partition_of(fid) for fid in ready_in_population}
    assert nursery.HELD_OUT in ready_partitions


def test_families_are_the_partition_unit() -> None:
    loaded = nursery.load(ROOT)
    families = loaded.families()
    assert len(families) > 0
    for name, rows in families.items():
        partitions = {row.partition for row in rows}
        assert len(partitions) == 1, f"family {name} straddles {sorted(partitions)}"


def test_family_lookup_raises_for_an_unknown_family() -> None:
    with pytest.raises(KeyError):
        nursery.load(ROOT).family("no-such-family")


def test_no_held_out_fact_is_settled_in_the_ledger() -> None:
    ledger = facts.load(ROOT)
    for fact_id in nursery.held_out_ids(ROOT):
        try:
            fact = ledger.get(fact_id)
        except KeyError:
            continue
        assert fact.epistemic_status not in nursery.SETTLED


def test_amendments_are_readable_and_irreversible() -> None:
    rows = nursery.amendments(ROOT)
    assert len(rows) > 0
    for row in rows:
        assert row.irreversible is True
        assert row.breach, "an amendment must record what was spent"
        assert row.authority


def test_a_manifest_without_entries_fails_closed(tmp_path: Path) -> None:
    root = tmp_path / "fake"
    (root / "artifacts" / "ontology").mkdir(parents=True)
    (root / "artifacts" / "autogenesis").mkdir(parents=True)
    (root / "artifacts" / "ontology" / "fact.schema.json").write_text("{}", encoding="utf-8")
    (root / nursery.NURSERY_PATH).write_text(json.dumps({"kind": "x"}), encoding="utf-8")
    with pytest.raises(nursery.NurseryError):
        nursery.load(root, refresh=True)


def test_an_empty_held_out_population_is_an_error_not_a_pass(tmp_path: Path) -> None:
    root = tmp_path / "fake2"
    (root / "artifacts" / "ontology").mkdir(parents=True)
    (root / "artifacts" / "autogenesis").mkdir(parents=True)
    (root / "artifacts" / "ontology" / "fact.schema.json").write_text("{}", encoding="utf-8")
    (root / nursery.NURSERY_PATH).write_text(
        json.dumps({"kind": "x", "entries": [{"fact_id": "F:a", "partition": "train"}]}),
        encoding="utf-8",
    )
    loaded = nursery.load(root, refresh=True)
    with pytest.raises(nursery.NurseryError):
        loaded.held_out_ids()


def test_split_key_is_family_and_shape() -> None:
    loaded = nursery.load(ROOT)
    row = loaded.entries[0]
    assert row.split_key == f"{row.family}:{row.proof_shape}"
    assert len(loaded.split_keys()) >= len(loaded.families())
