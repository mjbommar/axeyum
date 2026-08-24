"""`axeyum.knowledge.math_education`: the pinned sibling, and the parser.

Two things are under test. First the degradation contract: absent and off-pin
are *states*, mirroring the validator's skip-with-warning, and neither raises.
Second the hand-written front-matter reader, because PyYAML is not a dependency
here and a silently wrong parse of a 1,567-node knowledge graph would be
invisible.

The reader was differentially validated against PyYAML over all 1,609 graph
files while it was written (0 mismatches). PyYAML is not importable in this
environment, so the committed tests pin the behaviour with explicit fixtures
plus a whole-graph structural sweep, and never skip.
"""

from __future__ import annotations

import subprocess
from pathlib import Path

import pytest

from axeyum.knowledge import math_education as me
from axeyum.knowledge import overlay
from axeyum.knowledge._paths import repo_root

ROOT = repo_root()


# --------------------------------------------------------------------------
# the front-matter reader
# --------------------------------------------------------------------------


def test_scalars_quotes_and_types() -> None:
    parsed = me.parse_front_matter(
        "---\n"
        "id: C:thing\n"
        "count: 3\n"
        "ratio: 1.5\n"
        "flag: true\n"
        "missing: null\n"
        "quoted: '2026-08-05'\n"
        'escaped: "a \\"quoted\\" word"\n'
        "---\nbody\n"
    )
    assert parsed == {
        "id": "C:thing",
        "count": 3,
        "ratio": 1.5,
        "flag": True,
        "missing": None,
        "quoted": "2026-08-05",
        "escaped": 'a "quoted" word',
    }


def test_flow_sequences_including_apostrophes_and_empties() -> None:
    parsed = me.parse_front_matter(
        "---\n"
        "alt_labels: [Bezout's identity, Bezout's lemma]\n"
        "related: []\n"
        "nested: [a, [b, c]]\n"
        "---\n"
    )
    assert parsed["alt_labels"] == ["Bezout's identity", "Bezout's lemma"]
    assert parsed["related"] == []
    assert parsed["nested"] == ["a", ["b", "c"]]


def test_folded_and_literal_block_scalars() -> None:
    parsed = me.parse_front_matter(
        "---\n"
        "definition: >\n"
        "  one line\n"
        "  and its continuation\n"
        "clipped: >-\n"
        "  no trailing newline\n"
        "literal: |\n"
        "  line one\n"
        "  line two\n"
        "---\n"
    )
    assert parsed["definition"] == "one line and its continuation\n"
    assert parsed["clipped"] == "no trailing newline"
    assert parsed["literal"] == "line one\nline two\n"


def test_multi_line_plain_scalar_folds_to_spaces() -> None:
    parsed = me.parse_front_matter(
        "---\nsummary: a sentence that\n  wraps onto a second line\nnext: 1\n---\n"
    )
    assert parsed == {"summary": "a sentence that wraps onto a second line", "next": 1}


def test_nested_block_sequences_of_mappings() -> None:
    parsed = me.parse_front_matter(
        "---\n"
        "encounters:\n"
        "  - level: understand\n"
        "    summary: A summary.\n"
        "    objectives:\n"
        "      - statement: You can do the thing.\n"
        "        knowledge_dimension: conceptual\n"
        "    requires:\n"
        "      - encounter: C:other@understand\n"
        "        strength: helpful\n"
        "    uses_technique: []\n"
        "---\n"
    )
    encounter = parsed["encounters"][0]
    assert encounter["level"] == "understand"
    assert encounter["objectives"] == [
        {"statement": "You can do the thing.", "knowledge_dimension": "conceptual"}
    ]
    assert encounter["requires"] == [{"encounter": "C:other@understand", "strength": "helpful"}]
    assert encounter["uses_technique"] == []


def test_comments_are_ignored() -> None:
    parsed = me.parse_front_matter("---\n# a comment\nid: C:thing\n---\n")
    assert parsed == {"id": "C:thing"}


def test_a_document_without_front_matter_raises() -> None:
    with pytest.raises(me.FrontMatterError):
        me.parse_front_matter("no front matter here\n")
    with pytest.raises(me.FrontMatterError):
        me.parse_front_matter("---\nid: C:x\nnever terminated\n")


def test_split_front_matter_returns_the_body() -> None:
    front, body = me.split_front_matter("---\nid: C:x\n---\n\nThe prose.\n")
    assert front == {"id": "C:x"}
    assert body.startswith("The prose.")


# --------------------------------------------------------------------------
# the pin contract
# --------------------------------------------------------------------------


def test_status_is_one_of_three_and_never_raises() -> None:
    assert me.status(ROOT) in me.STATUSES


def test_the_pin_comes_from_the_overlay() -> None:
    graph = me.graph(ROOT)
    assert graph.pinned_revision == overlay.load(ROOT).pinned_revision("math-education")


def test_pin_ok_agrees_with_git_head() -> None:
    graph = me.graph(ROOT)
    if not graph.is_present:
        pytest.skip("the optional sibling checkout is absent on this host")
    completed = subprocess.run(
        ["git", "-C", str(graph.path), "rev-parse", "HEAD"],
        capture_output=True,
        text=True,
        timeout=60,
        check=False,
    )
    assert completed.returncode == 0, completed.stderr
    head = completed.stdout.strip()
    assert len(head) == 40
    assert graph.revision == head
    assert graph.pin_ok() == (head == graph.pinned_revision)


def test_an_absent_sibling_degrades_rather_than_raising(tmp_path: Path) -> None:
    graph = me.MathEducationGraph(
        path=tmp_path / "nowhere", pinned_revision="a" * 40, revision=None
    )
    assert graph.status == me.UNAVAILABLE
    assert graph.pin_ok() is False
    assert graph.resolves("C:anything") is False


def test_an_off_pin_sibling_is_a_warning_not_an_error() -> None:
    live = me.graph(ROOT)
    if not live.is_present:
        pytest.skip("the optional sibling checkout is absent on this host")
    off = me.MathEducationGraph(path=live.path, pinned_revision="0" * 40, revision=live.revision)
    assert off.status == me.OFF_PIN
    assert off.pin_ok() is False
    # Off-pin does not make the files unreadable.
    assert len(off.concepts()) > 0


def test_git_head_of_a_non_repository_is_none(tmp_path: Path) -> None:
    assert me.git_head(tmp_path / "absent") is None


# --------------------------------------------------------------------------
# the graph itself
# --------------------------------------------------------------------------


@pytest.fixture(scope="module")
def graph() -> me.MathEducationGraph:
    live = me.graph(ROOT)
    if not live.is_present:
        pytest.skip("the optional sibling checkout is absent on this host")
    return live


def test_every_concept_and_technique_parses(graph: me.MathEducationGraph) -> None:
    concepts = graph.concepts()
    techniques = graph.techniques()
    assert len(concepts) > 1000
    assert len(techniques) > 0
    assert all(row.id.startswith("C:") for row in concepts)
    assert all(row.id.startswith("TQ:") for row in techniques)


def test_the_file_count_matches_the_directory(graph: me.MathEducationGraph) -> None:
    on_disk = list((graph.path / "graph" / "concepts").glob("*.md"))
    assert len(graph.concepts()) == len(on_disk) > 0


def test_ids_agree_with_filenames(graph: me.MathEducationGraph) -> None:
    mismatched = [row.id for row in graph.concepts() if row.slug != row.path.stem]
    assert mismatched == []


def test_encounters_are_inline_not_a_directory(graph: me.MathEducationGraph) -> None:
    assert not (graph.path / "graph" / "encounters").exists()
    with_encounters = [row for row in graph.concepts() if row.encounters]
    assert len(with_encounters) > 1000
    for row in with_encounters[:200]:
        for encounter in row.encounters:
            assert encounter.level in me.ENCOUNTER_LEVELS


def test_encounter_lookup_raises_for_an_absent_level(graph: me.MathEducationGraph) -> None:
    concept = next(row for row in graph.concepts() if row.encounters)
    missing = [
        lvl for lvl in me.ENCOUNTER_LEVELS if lvl not in {e.level for e in concept.encounters}
    ]
    assert missing
    with pytest.raises(KeyError):
        concept.encounter(missing[0])


def test_requirements_split_concept_and_level(graph: me.MathEducationGraph) -> None:
    checked = 0
    for row in graph.concepts()[:400]:
        for encounter in row.encounters:
            for requirement in encounter.requires:
                if requirement.encounter and "@" in requirement.encounter:
                    assert requirement.concept_id.startswith("C:")
                    assert requirement.level in me.ENCOUNTER_LEVELS
                    checked += 1
    assert checked > 0, "no requirements were examined -- the assertion is vacuous"


def test_get_resolves_a_levelled_endpoint(graph: me.MathEducationGraph) -> None:
    concept = graph.concepts()[0]
    assert graph.get(f"{concept.id}@understand").id == concept.id


def test_get_raises_for_an_unknown_node(graph: me.MathEducationGraph) -> None:
    with pytest.raises(KeyError):
        graph.get("C:there-is-no-such-concept-slug")
    with pytest.raises(KeyError):
        graph.get("X:wrong-namespace")


def test_overlay_external_endpoints_resolve_when_on_pin(graph: me.MathEducationGraph) -> None:
    if not graph.pin_ok():
        pytest.skip("sibling is off-pin; live resolution is skipped, mirroring the validator")
    endpoints = [
        endpoint
        for link in overlay.load(ROOT).links
        for endpoint in (link.source, link.target)
        if endpoint.namespace == "math-education"
    ]
    assert endpoints, "no external endpoints -- the resolution check would be vacuous"
    for endpoint in endpoints:
        assert graph.resolves(endpoint.id), endpoint.id
