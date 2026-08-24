"""The four-node loop, end to end, offline.

The point of these assertions is what the graph did NOT do. A2 dispatches
nothing, so the episode it writes must record zero ledger writes, zero search
invocations, zero target-theorem submissions, and a verdict that does not claim
a proof -- and there must be no C-tier tool in the toolset that could have made
any of those nonzero.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

pytest.importorskip("pydantic_ai", reason="the [agent] extra is not installed")

from _agent_offline import offline_state, run_offline_episode

from axeyum.agent import graph as graph_api
from axeyum.agent import tools
from axeyum.agent.episode import EpisodeWriteError
from axeyum.agent.models import NoGeneralRoute, StrategyProposal
from axeyum.knowledge import nursery as nursery_api
from axeyum.knowledge._paths import resolve_root


def _resolve(root: Path, path: str) -> Path:
    """Episode paths are root-relative in the tree and absolute in a tmp dir."""
    candidate = Path(path)
    return candidate if candidate.is_absolute() else root / candidate


@pytest.fixture(scope="module")
def root():
    return resolve_root(None)


@pytest.fixture(scope="module")
def episode(root, tmp_path_factory):
    path = run_offline_episode(root, tmp_path_factory.mktemp("graph"))
    return path, json.loads(path.read_text())


def test_the_graph_has_exactly_the_four_nodes_this_slice_declares() -> None:
    rendered = graph_api.build_graph().render()
    for node in ("Select", "Gather", "Plan", "WriteEpisode"):
        assert node in rendered
    for absent in ("Dispatch", "Check", "StageTransaction", "Gate"):
        assert absent not in rendered, f"{absent} is an A4 node and must not exist yet"


def test_an_offline_run_writes_a_complete_episode(episode) -> None:
    path, document = episode
    assert path.is_file()
    assert document["kind"] == "axeyum-agent-episode"
    assert document["schema_version"] == 1
    assert document["policy"]["model_id"] == "test:offline"


def test_the_episode_records_no_authority(episode) -> None:
    _, document = episode
    outcome = document["outcome"]
    assert outcome["ledger_writes"] == 0
    assert outcome["search_invocations"] == 0
    assert outcome["target_theorem_submissions"] == 0
    assert outcome["verdict"] in ("declined", "budget-exhausted")
    assert outcome["axiom_footprint"] == []
    assert document["observed"] == {
        "facts_unlocked": [],
        "operations_widened": [],
        "overlay_links_proposed": [],
    }


def test_every_recorded_tool_call_is_a_read(episode) -> None:
    _, document = episode
    calls = document["transcript"]["tool_calls"]
    assert calls, "a run that called nothing is not a clean decline"
    assert {c["assurance"] for c in calls} == {"read"}
    assert [c["ordinal"] for c in calls] == list(range(len(calls)))
    assert all(c["tool"] in tools.TOOL_TIERS for c in calls)


def test_the_selection_is_pinned_to_a_committed_frontier(episode, root) -> None:
    _, document = episode
    selection = document["selection"]
    frontier_file = json.loads(_resolve(root, selection["frontier_path"]).read_text())
    assert frontier_file["frontier_sha256"] == selection["frontier_sha256"]
    assert selection["partition"] in ("train", "development")
    assert selection["fact_sha256"]


def test_the_episode_names_no_held_out_fact(episode, root) -> None:
    _, document = episode
    held = nursery_api.load(root).held_out_ids()
    text = json.dumps(document)
    assert held
    assert [f for f in held if f in text] == []


def test_the_proposal_is_written_beside_the_episode_and_hashed(episode, root) -> None:
    _, document = episode
    assert len(document["proposals"]) == 1
    row = document["proposals"][0]
    assert row["assurance"] == "proposed"
    assert row["kind"] == "strategy"
    payload = _resolve(root, row["path"]).read_bytes()
    assert hashlib.sha256(payload).hexdigest() == row["sha256"]


def test_the_proposal_parses_back_as_one_of_the_two_variants(episode, root) -> None:
    _, document = episode
    row = document["proposals"][0]
    payload = json.loads(_resolve(root, row["path"]).read_text())
    parsed = (
        StrategyProposal(**payload) if payload["route"] == "general" else NoGeneralRoute(**payload)
    )
    assert parsed.assurance == "proposed"


def test_select_refuses_a_fact_outside_the_eligible_population(root, tmp_path) -> None:
    blind = min(nursery_api.load(root).held_out_ids())
    state = offline_state(root, tmp_path)
    state.fact_id = blind
    with pytest.raises(EpisodeWriteError, match="not in the eligible population"):
        graph_api.run_episode(state)


def test_a_second_run_of_the_same_fact_writes_the_same_episode_path(root, tmp_path) -> None:
    """The episode id is a function of the fact, so a re-run replaces its own
    record instead of accumulating near-duplicates nobody can diff."""
    first = run_offline_episode(root, tmp_path)
    second = run_offline_episode(root, tmp_path)
    assert first == second


def test_the_instructions_name_every_tactic_in_the_catalog(root) -> None:
    from axeyum.agent.models import known_tactics

    text = graph_api.instructions_text(root)
    for tactic in known_tactics():
        assert tactic in text, f"{tactic} is in the catalog but not in the instructions"


def test_a_cut_short_run_does_not_duplicate_its_history() -> None:
    """`capture_run_messages` yields the run's FULL list, history included.

    Concatenating `history + captured` duplicated the whole Gather run in both
    budget-exhausted episodes (22 messages where 12 happened), which made them
    unreplayable: the graph asked for more responses than the run had made.
    """
    history = ["h0", "h1"]
    captured = ["h0", "h1", "p0", "p1"]
    assert graph_api.partial_messages(history, captured) == captured
    assert graph_api.partial_messages(history, []) == history
    assert graph_api.partial_messages([], captured) == captured


def test_the_offline_transcript_has_no_repeated_prompt(episode, root) -> None:
    """A cheap structural check for the same defect on a real transcript: the
    Gather prompt is issued once, so it must appear once."""
    from pydantic_ai.messages import ModelMessagesTypeAdapter

    _, document = episode
    payload = _resolve(root, document["transcript"]["messages_path"]).read_bytes()
    messages = list(ModelMessagesTypeAdapter.validate_json(payload))
    prompts = [
        part.content
        for message in messages
        for part in message.parts
        if getattr(part, "part_kind", "") == "user-prompt"
    ]
    assert len(prompts) == len(set(prompts)), "a prompt appears twice; the history was duplicated"
