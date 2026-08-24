"""`axeyum.knowledge.overlay`: every link carries its assurance."""

from __future__ import annotations

import json
import subprocess
import sys

import pytest

from axeyum.knowledge import facts, operations, overlay
from axeyum.knowledge._paths import repo_root

ROOT = repo_root()
VALIDATOR = ROOT / "scripts" / overlay.VALIDATOR


def test_the_canonical_validator_accepts_the_overlay() -> None:
    completed = subprocess.run(
        [sys.executable, str(VALIDATOR)],
        capture_output=True,
        text=True,
        timeout=300,
        check=False,
        cwd=str(ROOT),
    )
    assert completed.returncode == 0, completed.stderr
    line = [ln for ln in completed.stdout.splitlines() if ln.startswith("AUTOGENESIS_KNOWLEDGE_OK")]
    assert line, completed.stdout
    fields = dict(part.split("=", 1) for part in line[0].split("|")[1:])
    loaded = overlay.load(ROOT)
    assert int(fields["links"]) > 0
    assert len(loaded.links) == int(fields["links"])
    assert len(loaded.entities) == int(fields["entities"])
    assert len(loaded.relation_types) == int(fields["relations"])
    assert len(loaded.sources) == int(fields["sources"])


def test_constants_match_the_validators() -> None:
    module_source = VALIDATOR.read_text(encoding="utf-8")
    for kind in overlay.ENTITY_KINDS:
        assert f'"{kind}"' in module_source
    for level in overlay.ASSURANCE:
        assert f'"{level}"' in module_source
    assert set(overlay.ASSURANCE_ORDER) == set(overlay.ASSURANCE)


def test_every_link_carries_an_assurance() -> None:
    loaded = overlay.load(ROOT)
    assert len(loaded.links) > 0
    for link in loaded.links:
        assert link.assurance in overlay.ASSURANCE
        assert link.assurance_rank < len(overlay.ASSURANCE_ORDER)


def test_an_unknown_assurance_ranks_last_not_first() -> None:
    loaded = overlay.load(ROOT)
    forged = overlay.Link.from_raw({**loaded.links[0].raw, "assurance": "totally-certain"})
    assert forged.assurance_rank == len(overlay.ASSURANCE_ORDER)
    assert forged.assurance_rank > loaded.links[0].assurance_rank


def test_relation_domain_and_range_are_declared() -> None:
    loaded = overlay.load(ROOT)
    assert len(loaded.relation_types) > 0
    for link in loaded.links:
        relation = loaded.relation_type(link.relation)
        assert link.source.kind in relation.source_kinds
        assert link.target.kind in relation.target_kinds


def test_external_endpoints_carry_a_source_revision() -> None:
    loaded = overlay.load(ROOT)
    external = loaded.external_links()
    assert len(external) > 0
    pinned = loaded.pinned_revision()
    for link in external:
        for endpoint in (link.source, link.target):
            if endpoint.is_external:
                assert endpoint.source_revision == pinned


def test_local_endpoints_resolve() -> None:
    loaded = overlay.load(ROOT)
    ledger = facts.load(ROOT)
    registry = operations.load(ROOT)
    checked = 0
    for link in loaded.links:
        for endpoint in (link.source, link.target):
            if endpoint.namespace == "axeyum-fact":
                ledger.get(endpoint.id)
                checked += 1
            elif endpoint.namespace == "axeyum-operation":
                registry.get(endpoint.id)
                checked += 1
    assert checked > 0, "no local endpoints were checked -- the assertion is vacuous"


def test_query_filters_compose() -> None:
    loaded = overlay.load(ROOT)
    counts = loaded.relation_counts()
    assert counts
    relation, expected = next(iter(counts.items()))
    assert len(loaded.query(relation=relation)) == expected
    assert len(loaded.query()) == len(loaded.links)
    endpoint = loaded.links[0].source.id
    touching = loaded.query(endpoint_id=endpoint)
    assert touching
    assert all(row.touches(endpoint) for row in touching)


def test_query_for_nothing_is_empty_not_an_error() -> None:
    loaded = overlay.load(ROOT)
    assert loaded.query(relation="no-such-relation") == ()
    assert len(loaded.links) > 0, "the empty answer must come from a document we read"


def test_entity_lookup_raises_for_an_absent_entity() -> None:
    with pytest.raises(KeyError):
        overlay.load(ROOT).entity("K:no-such-capability")


def test_capability_entities_carry_their_budgets() -> None:
    loaded = overlay.load(ROOT)
    capabilities = [row for row in loaded.entities if row.kind == "capability"]
    assert capabilities
    for row in capabilities:
        assert row.kind in overlay.ENTITY_KINDS
        assert row.attributes, f"{row.id} declares a capability with no attributes"


def test_top_keys_are_exactly_the_schemas() -> None:
    document = json.loads((ROOT / overlay.OVERLAY_PATH).read_text(encoding="utf-8"))
    assert set(document) == set(overlay.TOP_KEYS)


def test_pinned_revision_raises_for_an_unpinned_source() -> None:
    loaded = overlay.load(ROOT)
    with pytest.raises(KeyError):
        loaded.pinned_revision("axeyum")
