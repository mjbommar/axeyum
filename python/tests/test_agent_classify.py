"""The `Classify` node, and the agreement that keeps two implementations honest.

The classification exists twice on purpose and must never differ:

* `axeyum.agent.classify` runs inside the graph, where the typed objects are;
* `scripts/gen-obstruction-graph.py` re-derives it from committed bytes, because
  `just check` is standard-library only and nothing under `scripts/` may import
  the `[agent]` extra.

Duplication that nobody compares is drift waiting to happen, so the central test
here runs BOTH over all sixteen committed episodes and requires the same cluster
key for each. If that ever fails, the obstruction graph and the loop that
produced it have stopped describing the same world.

The rest asserts the properties the taxonomy rests on: that the enum this module
maps is the schema's enum and not a copy that drifted, that a proof is never
classified as an obstruction, and -- the one that matters most -- that
`no-general-route` and `gate-refused` land in the SAME cluster, because the A2
and A4 harnesses recorded the identical situation under two different names.
"""

from __future__ import annotations

import importlib.util
import json
import pathlib
import re

import pytest

ROOT = pathlib.Path(__file__).resolve().parents[2]
EPISODES = ROOT / "artifacts/episodes"
EPISODE_DIR = re.compile(r"^[0-9]{4}-[0-9]{2}-[0-9]{2}(?:-[a-z0-9]+)?$")
SCHEMA_V2 = ROOT / "artifacts/ontology/agent-episode-v2.schema.json"

classify_api = pytest.importorskip("axeyum.agent.classify")


def load_generator():
    path = ROOT / "scripts" / "gen-obstruction-graph.py"
    spec = importlib.util.spec_from_file_location("gen_obstruction_graph", path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def committed_episodes() -> list[tuple[pathlib.Path, dict, list[dict]]]:
    rows = []
    for directory in sorted(EPISODES.iterdir()):
        if not (directory.is_dir() and EPISODE_DIR.match(directory.name)):
            continue
        for path in sorted(directory.glob("episode-*.json")):
            document = json.loads(path.read_text(encoding="utf-8"))
            proposals = [
                json.loads((ROOT / row["path"]).read_text(encoding="utf-8"))
                for row in document["proposals"]
            ]
            rows.append((path, document, proposals))
    return rows


def test_there_are_episodes_to_classify() -> None:
    """A positive control. An empty population would make every test below vacuous."""
    assert len(committed_episodes()) >= 16


def test_the_two_implementations_agree_on_every_committed_episode() -> None:
    """The stdlib generator and the in-graph classifier produce the same cluster.

    This is the whole reason the duplication is acceptable. It is checked over
    the real episodes rather than a fixture because a fixture would only prove
    the two agree about a case somebody thought of.
    """
    generator = load_generator()
    checked = 0
    for path, document, proposals in committed_episodes():
        theirs = classify_api.classify_episode(document, proposals)
        if document["outcome"]["verdict"] == "proved":
            assert theirs is None, f"{path.name}: a proof was classified as an obstruction"
            continue
        first, _known, detail = generator.classify_episode(document, proposals)
        assert theirs is not None
        assert theirs.first_blocker.kind == first["kind"], path.name
        assert theirs.first_blocker.detail == first["detail"], path.name
        assert theirs.cluster_key == f"{first['kind']}|{detail}", path.name
        assert theirs.obstruction_id == generator.cluster_id(theirs.cluster_key), path.name
        checked += 1
    assert checked >= 14, f"only {checked} declines compared"


def test_every_committed_episode_clusters_into_the_committed_graph() -> None:
    """Each declined episode's cluster id is an obstruction the graph declares."""
    graph = json.loads(
        (ROOT / "artifacts/autogenesis/obstruction-graph-v1.json").read_text(encoding="utf-8")
    )
    known = {entity["id"] for entity in graph["entities"]}
    for path, document, proposals in committed_episodes():
        result = classify_api.classify_episode(document, proposals)
        if result is None:
            continue
        assert result.obstruction_id in known, f"{path.name} -> {result.obstruction_id}"


def test_the_decline_class_map_covers_the_v2_schema_enum() -> None:
    """The map is keyed on the schema's enum, not on a copy that drifted."""
    schema = json.loads(SCHEMA_V2.read_text(encoding="utf-8"))
    enum = schema["$defs"]["declineClass"]["enum"]
    assert set(enum) == set(classify_api.DECLINE_CLASS_BLOCKERS)


def test_no_general_route_and_gate_refused_are_one_cluster() -> None:
    """A2 and A4 recorded the SAME situation under two decline classes.

    A4 added a gate that refuses a `NoGeneralRoute` plan, so the same model
    behaviour that A2 recorded as `no-general-route` A4 records as
    `gate-refused`. Keying on the decline class alone would split one
    obstruction in two and attribute the split to the mathematics.
    """
    proposals = [{"route": "none", "tactic_ids": ["T:refl-closure"]}]
    a2 = classify_api.classify(decline_class="no-general-route", proposals=proposals)
    a4 = classify_api.classify(decline_class="gate-refused", proposals=proposals)
    assert a2 is not None and a4 is not None
    assert a2.obstruction_id == a4.obstruction_id
    assert a2.cluster_key == "no-general-route|T:refl-closure"
    # The complete known set still distinguishes them: A4 saw one blocker more.
    assert len(a4.known_blockers) == len(a2.known_blockers) + 1
    assert a4.known_blockers[-1].kind == classify_api.GATE_REFUSED


def test_a_proposal_object_and_its_serialized_form_classify_alike() -> None:
    """A live run holds typed objects; a replay holds the same rows from JSON."""
    models = pytest.importorskip("axeyum.agent.models")
    models.set_vocabulary_root(ROOT)
    try:
        typed = models.NoGeneralRoute(
            fact_id="F:ml430-nat-modeq-trans-ef9d1c46",
            tactic_ids=["T:modeq-equivalence-combinators"],
            producer_id="close_terminal",
            why="a definitional equivalence relation property",
            expected_decline_class="NotEquivalenceRelationGoal",
            obstruction="the sibling properties each need their own kernel theorem",
        )
    finally:
        models.set_vocabulary_root(None)
    serialized = json.loads(typed.model_dump_json())
    from_object = classify_api.classify(decline_class="gate-refused", proposals=[typed])
    from_json = classify_api.classify(decline_class="gate-refused", proposals=[serialized])
    assert from_object == from_json


def test_a_retrieval_miss_is_the_missing_export_not_a_producer_failure() -> None:
    """Measured: 3 of 98 eligible facts have an importable export (plan 03, A4)."""
    result = classify_api.classify(decline_class="retrieval-miss", proposals=[])
    assert result is not None
    assert result.first_blocker.kind == classify_api.EXPORT_MISSING
    assert result.first_blocker.detail == classify_api.EXPORT_DETAIL


def test_budget_exhaustion_keeps_its_phase() -> None:
    before = classify_api.classify(decline_class="budget-exhausted-before-plan", proposals=[])
    during = classify_api.classify(decline_class="budget-exhausted-during-plan", proposals=[])
    assert before is not None and during is not None
    assert before.first_blocker.detail == "before-plan"
    assert during.first_blocker.detail == "during-plan"
    assert before.obstruction_id != during.obstruction_id


def test_a_proof_is_not_an_obstruction() -> None:
    assert classify_api.classify(decline_class=None, proposals=[], verdict="proved") is None


def test_the_graph_declares_the_classify_node_on_the_decline_path() -> None:
    graph_api = pytest.importorskip("axeyum.agent.graph")
    rendered = graph_api.build_graph().render()
    assert "Classify" in rendered


def test_classify_runs_without_a_model() -> None:
    """The node reads state and calls nothing. No model, no network, no tool.

    Asserted by construction rather than by mocking: `Classify.run` is driven
    here with a state whose `model` is None, so any model call would raise.
    """
    import asyncio

    graph_api = pytest.importorskip("axeyum.agent.graph")

    class FakeContext:
        def __init__(self, state):
            self.state = state

    class FakeState:
        def __init__(self) -> None:
            self.decline_class = "gate-refused"
            self.proposals = [{"route": "none", "tactic_ids": ["T:refl-closure"]}]
            self.verdict = "declined"
            self.classification = None
            self.model = None

    state = FakeState()
    node = graph_api.Classify()
    result = asyncio.run(node.run(FakeContext(state)))
    assert isinstance(result, graph_api.WriteEpisode)
    assert state.classification is not None
    assert state.classification.cluster_key == "no-general-route|T:refl-closure"
