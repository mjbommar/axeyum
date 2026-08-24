"""`axeyum.knowledge.autogenesis`: classify by shape, confirm by `kind`.

707 distinct `kind` values across 958 documents means the vocabulary is not a
closed set. The filename-suffix router is the first cut and `kind` is the
authoritative confirmation; where they disagree the index says so instead of
picking one silently.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from axeyum.knowledge import autogenesis
from axeyum.knowledge._paths import repo_root

ROOT = repo_root()


def test_every_artifact_json_is_indexed() -> None:
    on_disk = sorted((ROOT / autogenesis.ARTIFACTS_DIR).glob("*.json"))
    index = autogenesis.load(ROOT)
    assert len(on_disk) > 0
    assert len(index) == len(on_disk)
    assert [row.path for row in index] == on_disk


def test_every_document_is_readable_json() -> None:
    index = autogenesis.load(ROOT)
    assert index.unreadable() == ()
    assert len(index) > 0


def test_the_kind_vocabulary_is_open() -> None:
    """If this ever collapses to a small set, the shape router is unnecessary."""
    index = autogenesis.load(ROOT)
    assert len(index.kinds()) > 100


def test_shapes_partition_the_index() -> None:
    index = autogenesis.load(ROOT)
    grouped = index.by_shape()
    assert sum(len(v) for v in grouped.values()) == len(index)
    assert set(grouped) <= {*autogenesis.SHAPES, autogenesis.OTHER}
    assert len(grouped.get("plan", ())) > 0
    assert len(grouped.get("result", ())) > 0


def test_shape_counts_match_the_filenames() -> None:
    index = autogenesis.load(ROOT)
    directory = ROOT / autogenesis.ARTIFACTS_DIR
    for shape in ("plan", "result", "decline", "admission", "adapter", "policy", "capsule"):
        by_glob = len(list(directory.glob(f"*-{shape}.json"))) + len(
            list(directory.glob(f"*-{shape}-v*.json"))
        )
        assert len(index.shape(shape)) == by_glob, shape


def test_unknown_shape_raises_rather_than_reading_as_empty() -> None:
    with pytest.raises(KeyError):
        autogenesis.load(ROOT).shape("plans")


def test_kind_confirms_the_filename_router_for_most_documents() -> None:
    index = autogenesis.load(ROOT)
    unconfirmed = index.unconfirmed()
    # The router is a sound first cut, not a proof: disagreements are surfaced
    # rather than resolved, and must stay a small minority.
    assert len(unconfirmed) < len(index) * 0.05
    for row in unconfirmed:
        assert row.shape != row.kind_shape


def test_classify_strips_versions_and_falls_back_to_other() -> None:
    assert autogenesis.classify("foo-bar-plan-v12") == "plan"
    assert autogenesis.classify("foo-bar-result") == "result"
    assert autogenesis.classify("axeyum-autogenesis-census-v1") == autogenesis.OTHER


def test_pairs_match_plans_to_results() -> None:
    index = autogenesis.load(ROOT)
    pairs = index.pairs()
    assert len(pairs) > 0
    for pair in pairs:
        assert pair.plan.shape == "plan"
        assert pair.result.shape == "result"
        assert pair.plan.pair_key == pair.result.pair_key == pair.key
    assert len({pair.key for pair in pairs}) == len(pairs)


def test_unpaired_plans_are_named_not_hidden() -> None:
    index = autogenesis.load(ROOT)
    unpaired = index.unpaired_plans()
    paired = {pair.plan.name for pair in index.pairs()}
    assert len(index.shape("plan")) == len(paired) + len(unpaired)
    assert all(row.name not in paired for row in unpaired)


def test_get_raises_for_an_absent_artifact() -> None:
    with pytest.raises(KeyError):
        autogenesis.load(ROOT).get("no-such-artifact.json")


def test_documents_carry_their_kind() -> None:
    index = autogenesis.load(ROOT)
    without = [row for row in index if row.kind is None]
    assert without == [], f"{len(without)} artifacts carry no kind"


def test_a_missing_directory_raises(tmp_path: Path) -> None:
    root = tmp_path / "fake"
    (root / "artifacts" / "ontology").mkdir(parents=True)
    (root / "artifacts" / "ontology" / "fact.schema.json").write_text("{}", encoding="utf-8")
    with pytest.raises(FileNotFoundError):
        autogenesis.load(root, refresh=True)


def test_an_unreadable_document_is_recorded_not_skipped(tmp_path: Path) -> None:
    root = tmp_path / "broken"
    (root / "artifacts" / "ontology").mkdir(parents=True)
    (root / "artifacts" / "autogenesis").mkdir(parents=True)
    (root / "artifacts" / "ontology" / "fact.schema.json").write_text("{}", encoding="utf-8")
    (root / "artifacts" / "autogenesis" / "good-plan-v1.json").write_text(
        json.dumps({"kind": "fixture-plan-v1"}), encoding="utf-8"
    )
    (root / "artifacts" / "autogenesis" / "bad-result-v1.json").write_text(
        "{not json", encoding="utf-8"
    )
    index = autogenesis.load(root, refresh=True)
    assert len(index) == 2
    assert [row.name for row in index.unreadable()] == ["bad-result-v1.json"]
    assert index.get("good-plan-v1.json").shape_confirmed
