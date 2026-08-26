"""The public lemma API preserves exact identities and search-only authority."""

from __future__ import annotations

import json

import pytest

from axeyum.knowledge import lemmas
from axeyum.knowledge._paths import repo_root

ROOT = repo_root()


def test_index_matches_generated_census() -> None:
    index = lemmas.load(ROOT, refresh=True)
    document = json.loads((ROOT / lemmas.INDEX_PATH).read_text(encoding="utf-8"))
    assert len(index) == document["census"]["kernel_theorems"]
    assert len(index) > 0
    assert len(index.unresolved) == document["census"]["unresolved_prefixed_kernel_evidence"]


def test_exact_lookup_and_neighborhood_are_bidirectional() -> None:
    index = lemmas.load(ROOT)
    subject = next(lemma for lemma in index if lemma.dependencies and lemma.dependents)
    assert index.get(subject.id) is subject
    assert all(
        subject.id in dependency.dependents for dependency in index.prerequisites(subject.id)
    )
    assert all(subject.id in consumer.dependencies for consumer in index.consumers(subject.id))


def test_fact_lookup_uses_only_exact_generated_links() -> None:
    index = lemmas.load(ROOT)
    linked = next(lemma for lemma in index if lemma.fact_ids)
    for fact_id in linked.fact_ids:
        assert linked in index.for_fact(fact_id)
    assert index.for_fact("F:definitely-not-linked") == ()


def test_unknown_declaration_fails_closed() -> None:
    with pytest.raises(KeyError, match="no kernel lemma"):
        lemmas.get("Definitely.notATheorem", ROOT)


def test_rows_never_claim_applicability_or_proof_authority() -> None:
    index = lemmas.load(ROOT)
    assert all(lemma.search_authority.startswith("candidate-only") for lemma in index)
    forbidden = {"applicable", "proved", "admitted", "authorized"}
    assert all(forbidden.isdisjoint(lemma.raw) for lemma in index)
