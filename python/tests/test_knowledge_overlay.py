"""`axeyum.knowledge.overlay`: every link carries its assurance."""

from __future__ import annotations

import json
import subprocess
import sys
from dataclasses import replace

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


def test_the_overlay_declares_no_external_source() -> None:
    """ADR-0553: every endpoint resolves inside this checkout.

    This replaces `test_external_endpoints_carry_a_source_revision`, which
    asserted that external endpoints EXIST and pinned each one's revision to the
    sibling `math-education` checkout. That subject is gone, so the test is
    inverted rather than relaxed: the assertions below fail the moment an
    external source, an `external-pinned` namespace, or a `source_revision` on
    any endpoint comes back.

    It is deliberately not a tautology -- `assert loaded.external_links() == ()`
    alone would also pass against an overlay with no links at all -- so each
    check is paired with a positive control that the collection it filters was
    read and is non-empty.
    """
    loaded = overlay.load(ROOT)

    assert len(loaded.sources) > 0, "no sources were read -- the assertion is vacuous"
    for source in loaded.sources:
        assert not source.is_pinned, f"source {source.id!r} is pinned to a foreign revision"
        assert source.kind != "external-repository", f"source {source.id!r} is external"
        assert source.revision is None, f"source {source.id!r} carries a revision"

    assert len(loaded.namespaces) > 0, "no namespaces were read -- the assertion is vacuous"
    for namespace in loaded.namespaces:
        assert namespace.resolution != "external-pinned", (
            f"namespace {namespace.id!r} resolves against a pinned foreign checkout"
        )

    assert len(loaded.links) > 0, "no links were read -- the assertion is vacuous"
    for link in loaded.links:
        for endpoint in (link.source, link.target):
            assert endpoint.source_revision is None, (
                f"endpoint {endpoint.id!r} of link {link.id!r} carries a source_revision"
            )
            assert not endpoint.is_external
    assert loaded.external_links() == ()


def test_the_external_detector_still_fires_on_a_forged_endpoint() -> None:
    """The check above is only worth its assertions if the detector works.

    `external_links()` returning `()` for the committed artifact and returning
    `()` because nothing can ever be external are different states, and only one
    of them is a measurement. A forged endpoint tells them apart.
    """
    loaded = overlay.load(ROOT)
    raw = loaded.links[0].raw
    forged = overlay.Link.from_raw(
        {**raw, "source": {**raw["source"], "source_revision": "deadbee"}}
    )
    assert forged.source.is_external
    assert replace(loaded, links=(forged,)).external_links() == (forged,)


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
