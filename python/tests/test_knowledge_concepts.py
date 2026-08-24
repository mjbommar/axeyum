"""`axeyum.knowledge.concepts`: the generated foundational-concept table."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from axeyum.knowledge import concepts
from axeyum.knowledge._paths import repo_root

ROOT = repo_root()
VALIDATOR = ROOT / "scripts" / concepts.VALIDATOR


def test_the_canonical_validator_accepts_the_table() -> None:
    completed = subprocess.run(
        [sys.executable, str(VALIDATOR)],
        capture_output=True,
        text=True,
        timeout=300,
        check=False,
        cwd=str(ROOT),
    )
    assert completed.returncode == 0, completed.stderr
    line = [ln for ln in completed.stdout.splitlines() if "foundational concept rows" in ln]
    assert line, completed.stdout
    reported = int(line[0].split("validated ", 1)[1].split(" ", 1)[0])
    assert reported > 0
    assert len(concepts.load(ROOT)) == reported


def test_the_table_declares_what_generated_it() -> None:
    table = concepts.load(ROOT)
    assert len(table.generated_from) > 0
    assert (ROOT / "scripts" / concepts.GENERATOR).is_file()


def test_rows_have_stable_ids() -> None:
    table = concepts.load(ROOT)
    ids = [row.id for row in table]
    assert len(ids) == len(set(ids)) > 0


def test_get_raises_for_an_absent_concept() -> None:
    with pytest.raises(KeyError):
        concepts.get("no-such-concept", ROOT)


def test_layers_and_domains_partition_every_row() -> None:
    table = concepts.load(ROOT)
    assert sum(len(v) for v in table.by_layer().values()) == len(table)
    assert sum(len(v) for v in table.by_domain().values()) == len(table)


def test_validated_example_packs_exist_on_disk() -> None:
    table = concepts.load(ROOT)
    validated = [
        pack for row in table for pack in row.example_packs if pack.is_validated and pack.path
    ]
    assert validated, "no validated example packs -- the disk check would be vacuous"
    assert table.missing_validated_packs() == {}


def test_a_validated_pack_pointing_nowhere_is_reported(tmp_path: Path) -> None:
    """The negative control: the disk check must be able to fail."""
    row = concepts.Concept.from_raw(
        {
            "id": "fixture",
            "example_packs": [{"id": "p", "status": "validated", "path": "no/such/pack"}],
        }
    )
    assert row.missing_validated_packs(tmp_path) == ("no/such/pack",)


def test_fragment_lookup_is_empty_only_after_reading() -> None:
    table = concepts.load(ROOT)
    assert table.with_fragment("QF_NOT_REAL") == ()
    assert len(table) > 0


def test_the_json_row_order_is_preserved() -> None:
    document = json.loads((ROOT / concepts.CONCEPTS_PATH).read_text(encoding="utf-8"))
    assert [row.id for row in concepts.load(ROOT)] == [row["id"] for row in document["rows"]]


def test_a_missing_table_raises(tmp_path: Path) -> None:
    root = tmp_path / "fake"
    (root / "artifacts" / "ontology").mkdir(parents=True)
    (root / "artifacts" / "ontology" / "fact.schema.json").write_text("{}", encoding="utf-8")
    with pytest.raises(FileNotFoundError):
        concepts.load(root, refresh=True)
