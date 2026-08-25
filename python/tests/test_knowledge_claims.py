"""`axeyum.knowledge.claims`: a claim's `formal` is a recipe, not a proposition."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

from axeyum.knowledge import claims, facts
from axeyum.knowledge._paths import repo_root

ROOT = repo_root()
VALIDATOR = ROOT / "scripts" / claims.VALIDATOR


def test_the_canonical_validator_accepts_the_ledger() -> None:
    completed = subprocess.run(
        [sys.executable, str(VALIDATOR)],
        capture_output=True,
        text=True,
        timeout=300,
        check=False,
        cwd=str(ROOT),
    )
    assert completed.returncode == 0, completed.stderr
    tail = [ln for ln in completed.stdout.splitlines() if ln.endswith("errors")]
    assert tail, completed.stdout
    reported = int(tail[-1].split(" claims", 1)[0])
    assert reported > 0
    assert len(claims.load(ROOT)) == reported


def test_the_layout_is_nested_not_flat() -> None:
    """`artifacts/claims/*.json` finds nothing; the reader must walk the tree."""
    directory = ROOT / claims.CLAIMS_DIR
    assert list(directory.glob("*.json")) == []
    assert len(list(directory.glob("*/*/claim.json"))) > 0
    assert len(claims.load(ROOT)) == len(list(directory.glob("*/*/claim.json")))


def test_families_come_from_the_directory_layout() -> None:
    ledger = claims.load(ROOT)
    grouped = ledger.families()
    assert len(grouped) > 1
    assert sum(len(v) for v in grouped.values()) == len(ledger)
    for family, rows in grouped.items():
        assert all(row.path.parent.parent.name == family for row in rows)


def test_formal_is_a_generator_recipe() -> None:
    ledger = claims.load(ROOT)
    assert len(ledger) > 0
    recipes = [row for row in ledger if row.generator]
    assert recipes, "no claim named a generator -- the recipe distinction is inert"
    for row in recipes:
        assert row.formal.get("language") == "cnf-family"
        assert row.cnf_family
        assert row.parameters


def test_every_claim_carries_the_required_keys() -> None:
    ledger = claims.load(ROOT)
    assert len(ledger) > 0
    for row in ledger:
        assert row.missing_required == frozenset(), f"{row.id} is missing {row.missing_required}"


def test_concept_refs_are_citations_that_nothing_resolves() -> None:
    """ADR-0553: a `concept_ref` names a graph and an id, and stops there.

    Until 2026-08-24 each ref also carried `resolved`, asserting the id had been
    found in a sibling checkout at the commit `provenance.graph_pin` named. Both
    are gone from the schema and from all 104 claims, so the typed layer must not
    offer a `resolved` attribute either -- an accessor for a field the data never
    carries would read `None` on every ref and be indistinguishable from an
    honest "not resolved".
    """
    refs = claims.load(ROOT).concept_refs()
    assert len(refs) > 0
    assert not hasattr(refs[0], "resolved")
    assert "resolved" not in claims.ConceptRef.__slots__
    for ref in refs:
        # Still the value every committed claim carries. It is now a free-text
        # label rather than a schema enum, and it points at nothing: the pin it
        # used to be read against is gone.
        assert ref.graph == "math-education"
        assert ref.ref and (ref.ref.startswith("C:") or ref.ref.startswith("TQ:"))


def test_claim_ref_evidence_on_facts_resolves_to_a_claim() -> None:
    ledger = claims.load(ROOT)
    checked = 0
    for fact in facts.load(ROOT):
        for evidence in fact.evidence:
            if evidence.kind == "claim-ref" and evidence.artifact:
                assert (ROOT / evidence.artifact).is_file()
                assert ledger.referenced_by(evidence.artifact)
                checked += 1
    assert checked > 0, "no claim-ref evidence was examined -- the check is vacuous"


def test_get_raises_for_an_absent_claim() -> None:
    with pytest.raises(KeyError):
        claims.get("no-such-claim", ROOT)


def test_a_missing_directory_raises(tmp_path: Path) -> None:
    root = tmp_path / "fake"
    (root / "artifacts" / "ontology").mkdir(parents=True)
    (root / "artifacts" / "ontology" / "fact.schema.json").write_text("{}", encoding="utf-8")
    with pytest.raises(FileNotFoundError) as excinfo:
        claims.load(root, refresh=True)
    assert "claims" in str(excinfo.value)


def test_an_empty_claims_tree_is_empty_not_missing(tmp_path: Path) -> None:
    root = tmp_path / "empty"
    (root / "artifacts" / "ontology").mkdir(parents=True)
    (root / "artifacts" / "claims").mkdir(parents=True)
    (root / "artifacts" / "ontology" / "fact.schema.json").write_text("{}", encoding="utf-8")
    ledger = claims.load(root, refresh=True)
    assert len(ledger) == 0
    assert ledger.directory.is_dir()


def test_status_spread_is_readable() -> None:
    grouped = claims.load(ROOT).by_status()
    assert sum(len(v) for v in grouped.values()) == len(claims.load(ROOT))
    assert "computed" in grouped
