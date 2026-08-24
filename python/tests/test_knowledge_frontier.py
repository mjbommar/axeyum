"""`axeyum.knowledge.frontier` wraps `scripts/fact-frontier.py`.

The property that must not regress: **a refusal is a value**. The current run
selects nothing, and an accessor that raised, or that read an empty
``admissible_fact_ids`` as an error, would break the dispatcher it exists to
serve.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from axeyum.knowledge import facts, frontier
from axeyum.knowledge._paths import repo_root

ROOT = repo_root()
SCRIPT = ROOT / "scripts" / "fact-frontier.py"


@pytest.fixture(scope="module")
def script_document() -> dict:
    completed = subprocess.run(
        [sys.executable, str(SCRIPT), "--json"],
        capture_output=True,
        text=True,
        timeout=300,
        check=False,
        cwd=str(ROOT),
    )
    assert completed.returncode == 0, completed.stderr
    document = json.loads(completed.stdout)
    assert len(document["entries"]) > 0, "a frontier with no entries is an inert measurement"
    return document


def test_the_typed_frontier_is_the_script_output(script_document: dict) -> None:
    loaded = frontier.load(ROOT, refresh=True)
    assert loaded.document == script_document
    assert len(loaded) == len(script_document["entries"]) > 0
    assert loaded.kind == "axeyum-fact-frontier"


def test_frontier_sha256_is_carried(script_document: dict) -> None:
    assert frontier.frontier_sha256(ROOT) == script_document["frontier_sha256"]
    assert len(frontier.frontier_sha256(ROOT)) == 64


def test_refusal_is_a_value_not_an_exception(script_document: dict) -> None:
    selection = frontier.selection(ROOT)
    assert selection.outcome == script_document["selection"]["outcome"]
    if selection.outcome == frontier.REFUSED_NO_ADMISSIBLE_CANDIDATE:
        assert selection.refused
        assert selection.admissible_fact_ids == ()
        assert selection.selected_fact_id is None
        # The refusal must still say WHY, per ready fact.
        assert len(selection.rationale) > 0
        assert all(row.rejected_by for row in selection.rationale)


def test_rationale_lookup_raises_for_a_fact_with_no_row() -> None:
    selection = frontier.selection(ROOT)
    with pytest.raises(KeyError):
        selection.rejected_by("F:not-on-this-frontier")


def test_capabilities_expose_the_decidable_fragments(script_document: dict) -> None:
    capabilities = frontier.capabilities(ROOT)
    assert set(capabilities.decidable_fragments) == set(
        script_document["capabilities"]["decidable_fragments"]
    )
    assert len(capabilities.decidable_fragments) > 0
    demonstrated = set(capabilities.decidable_fragments) - set(capabilities.undemonstrated())
    assert demonstrated, "no fragment carries a demonstration -- the field is inert"
    for fragment in demonstrated:
        assert capabilities.demonstration(fragment).startswith("F:")
    # A declared fragment with no demonstrating fact is a visible answer, not a
    # silent None: the two states must stay distinguishable.
    for fragment in capabilities.undemonstrated():
        with pytest.raises(KeyError):
            capabilities.demonstration(fragment)


def test_capability_demonstration_raises_for_an_unknown_fragment() -> None:
    with pytest.raises(KeyError):
        frontier.capabilities(ROOT).demonstration("QF_NOT_A_FRAGMENT")


def test_verify_shells_to_the_script_and_agrees() -> None:
    result = frontier.load(ROOT).verify()
    assert result.returncode == 0, result.stderr
    assert result.ok
    assert result.sha256 == frontier.frontier_sha256(ROOT)


def test_verify_rejects_a_tampered_frontier(tmp_path: Path) -> None:
    """The checker must be shown to fail, or it is not a checker."""
    loaded = frontier.load(ROOT)
    tampered = dict(loaded.document)
    tampered["selection"] = dict(tampered["selection"])
    tampered["selection"]["outcome"] = "selected"
    path = tmp_path / "tampered.json"
    path.write_text(json.dumps(tampered, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    result = loaded.verify(path)
    assert result.returncode != 0
    assert not result.ok
    assert "FACT_FRONTIER_ERROR" in result.stderr


def test_entry_lookup_raises_for_an_absent_fact() -> None:
    with pytest.raises(KeyError):
        frontier.load(ROOT).entry("F:not-a-fact")


def test_entries_reference_real_facts() -> None:
    ledger = facts.load(ROOT)
    known = ledger.ids
    rows = frontier.entries(ROOT)
    assert len(rows) > 0
    assert all(row.fact_id in known for row in rows)


def test_ledger_block_agrees_with_the_fact_ledger() -> None:
    loaded = frontier.load(ROOT)
    assert loaded.ledger["fact_count"] == len(facts.load(ROOT))


def test_dependency_ready_is_a_set_not_a_count() -> None:
    """`dependency_ready` and any partition are different questions."""
    ready = frontier.load(ROOT).dependency_ready()
    assert len(ready) > 0
    assert all(row.dependency_ready for row in ready)
    assert all(row.missing_dependencies == () for row in ready)


def test_bands_partition_every_entry() -> None:
    loaded = frontier.load(ROOT)
    grouped = loaded.by_band()
    assert sum(len(v) for v in grouped.values()) == len(loaded) > 0


def test_a_broken_root_raises_rather_than_returning_an_empty_frontier(tmp_path: Path) -> None:
    root = tmp_path / "fake"
    (root / "artifacts" / "ontology").mkdir(parents=True)
    (root / "artifacts" / "ontology" / "fact.schema.json").write_text("{}", encoding="utf-8")
    with pytest.raises(FileNotFoundError):
        frontier.load(root, refresh=True)
