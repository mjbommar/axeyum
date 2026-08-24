"""`axeyum.knowledge.generated`: the dashboards and the scripts behind them."""

from __future__ import annotations

from pathlib import Path

import pytest

from axeyum.knowledge import generated
from axeyum.knowledge._paths import repo_root

ROOT = repo_root()


def test_every_markdown_dashboard_is_indexed() -> None:
    on_disk = sorted((ROOT / generated.GENERATED_DIR).glob("*.md"))
    index = generated.load(ROOT)
    assert len(on_disk) > 0
    assert len(index) == len(on_disk)


def test_most_dashboards_name_their_generator() -> None:
    index = generated.load(ROOT)
    with_generator = index.with_generator()
    assert len(with_generator) > len(index) // 2
    for doc in with_generator:
        assert (ROOT / doc.generator).is_file(), f"{doc.name} names a generator that is gone"


def test_a_dashboard_without_a_named_generator_is_a_value() -> None:
    index = generated.load(ROOT)
    silent = index.without_generator()
    # This must be reported, never inferred away: the header was read and did
    # not say, which is different from not having looked.
    assert len(silent) + len(index.with_generator()) == len(index)
    for doc in silent:
        assert doc.generator is None
        assert doc.header, "an empty header would make the negative result unproven"


def test_the_flywheel_dashboards_resolve_to_their_generators() -> None:
    index = generated.load(ROOT)
    expected = {
        "theorem-production-ledger": "scripts/gen-theorem-production-ledger.py",
        "production-provenance-ledger": "scripts/gen-production-provenance-ledger.py",
        "proof-gap-matrix": "scripts/gen-proof-gap-matrix.py",
        "autogenesis-knowledge-coverage": "scripts/gen-autogenesis-knowledge-coverage.py",
    }
    for stem, script in expected.items():
        assert index.get(stem).generator == script


def test_json_twins_are_detected_where_they_exist() -> None:
    index = generated.load(ROOT)
    twinned = [doc for doc in index if doc.has_json_twin]
    assert twinned
    for doc in twinned:
        assert doc.json_twin is not None and doc.json_twin.is_file()
    untwinned = [doc for doc in index if not doc.has_json_twin]
    assert untwinned, "if everything had a twin, has_json_twin would be inert"


def test_titles_are_read_from_the_headings() -> None:
    index = generated.load(ROOT)
    titled = [doc for doc in index if doc.title]
    assert len(titled) == len(index)


def test_get_raises_for_an_absent_dashboard() -> None:
    with pytest.raises(KeyError):
        generated.get("no-such-dashboard", ROOT)


def test_by_generator_groups_every_document() -> None:
    index = generated.load(ROOT)
    grouped = index.by_generator()
    assert sum(len(v) for v in grouped.values()) == len(index)


def test_a_missing_directory_raises(tmp_path: Path) -> None:
    root = tmp_path / "fake"
    (root / "artifacts" / "ontology").mkdir(parents=True)
    (root / "artifacts" / "ontology" / "fact.schema.json").write_text("{}", encoding="utf-8")
    with pytest.raises(FileNotFoundError):
        generated.load(root, refresh=True)


def test_an_empty_directory_is_empty_not_missing(tmp_path: Path) -> None:
    root = tmp_path / "empty"
    (root / "artifacts" / "ontology").mkdir(parents=True)
    (root / generated.GENERATED_DIR).mkdir(parents=True)
    (root / "artifacts" / "ontology" / "fact.schema.json").write_text("{}", encoding="utf-8")
    index = generated.load(root, refresh=True)
    assert len(index) == 0
    assert index.directory.is_dir()
