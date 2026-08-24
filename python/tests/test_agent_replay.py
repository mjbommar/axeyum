"""Replay: the deterministic nodes must re-derive, and the check must be able to fail.

`models.ALLOW_MODEL_REQUESTS = False` is what makes a replay a replay rather
than a second, cheaper run that happens to agree.
"""

from __future__ import annotations

import json

import pytest

pytest.importorskip("pydantic_ai", reason="the [agent] extra is not installed")

from _agent_offline import run_offline_episode
from pydantic_ai import models

from axeyum.agent import cli as cli_api
from axeyum.agent import episode as episode_api
from axeyum.agent.replay import ReplayError, replay
from axeyum.knowledge._paths import resolve_root


@pytest.fixture(scope="module")
def root():
    return resolve_root(None)


@pytest.fixture(scope="module")
def episode(root, tmp_path_factory):
    return run_offline_episode(root, tmp_path_factory.mktemp("replay"))


def test_replay_reproduces_the_outcome_and_the_selection(root, episode) -> None:
    result = replay(episode, root=root)
    assert result.ok, result.diverged
    assert result.diverged == ()
    assert result.consumed_responses == result.recorded_responses


def test_replay_reports_the_tool_calls_it_re_derived(root, episode) -> None:
    result = replay(episode, root=root)
    assert result.tool_calls_match
    assert "tool_calls=match" in result.line()


def test_replay_leaves_the_model_request_guard_as_it_found_it(root, episode) -> None:
    before = models.ALLOW_MODEL_REQUESTS
    replay(episode, root=root)
    assert models.ALLOW_MODEL_REQUESTS is before


def test_replay_detects_a_forged_outcome(root, episode, tmp_path) -> None:
    """The control. A replay that cannot report divergence is not a check."""
    document = json.loads(episode.read_text())
    document["outcome"]["decline_class"] = "a-class-nobody-derived"
    forged = tmp_path / "forged-outcome.json"
    forged.write_text(episode_api.canonical(document))
    result = replay(forged, root=root)
    assert not result.ok
    assert "outcome" in result.diverged
    assert "status=DIVERGED" in result.line()


def test_replay_detects_a_forged_selection(root, episode, tmp_path) -> None:
    document = json.loads(episode.read_text())
    document["selection"]["eligibility_reason"] = "because I said so"
    forged = tmp_path / "forged-selection.json"
    forged.write_text(episode_api.canonical(document))
    result = replay(forged, root=root)
    assert not result.ok
    assert "selection" in result.diverged


def test_replay_refuses_a_document_that_is_not_an_episode(root, tmp_path) -> None:
    path = tmp_path / "not-an-episode.json"
    path.write_text('{"kind": "something-else"}\n')
    with pytest.raises(ReplayError, match="not an episode"):
        replay(path, root=root)


def test_replay_refuses_an_episode_whose_transcript_is_gone(root, episode, tmp_path) -> None:
    document = json.loads(episode.read_text())
    document["transcript"]["messages_path"] = "artifacts/episodes/nowhere.json.snapshot"
    orphan = tmp_path / "orphan.json"
    orphan.write_text(episode_api.canonical(document))
    with pytest.raises(ReplayError, match="not on disk"):
        replay(orphan, root=root)


def test_the_cli_exit_status_depends_on_the_comparison(root, episode, tmp_path) -> None:
    assert cli_api.main(["--root", str(root), "replay", "--from-transcript", str(episode)]) == 0
    document = json.loads(episode.read_text())
    document["outcome"]["verdict"] = "budget-exhausted"
    forged = tmp_path / "forged-verdict.json"
    forged.write_text(episode_api.canonical(document))
    assert cli_api.main(["--root", str(root), "replay", "--from-transcript", str(forged)]) == 1


def test_the_cli_reports_an_unreadable_episode_distinctly(root, tmp_path) -> None:
    missing = tmp_path / "nope.json"
    assert cli_api.main(["--root", str(root), "replay", "--from-transcript", str(missing)]) == 2
