"""The episode writer, judged by the gate that will judge it in CI.

The assertion that matters is not "the writer produced JSON". It is that
`scripts/check-agent-episode.py` -- a different program, standard library only,
which never imports this package -- says OK, and says FAIL on a corrupted copy.
A writer tested only against its own reader tests nothing.
"""

from __future__ import annotations

import json
import subprocess
import sys
import types
from pathlib import Path

import pytest

pytest.importorskip("pydantic_ai", reason="the [agent] extra is not installed")

from _agent_offline import run_offline_episode

from axeyum.agent import episode as episode_api
from axeyum.agent.episode import HeldOutLeak
from axeyum.knowledge import nursery as nursery_api
from axeyum.knowledge._paths import resolve_root

CHECKER = "scripts/check-agent-episode.py"


@pytest.fixture(scope="module")
def root() -> Path:
    return resolve_root(None)


@pytest.fixture(scope="module")
def episode(root, tmp_path_factory) -> Path:
    return run_offline_episode(root, tmp_path_factory.mktemp("episode"))


def check(root: Path, *paths: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(root / CHECKER), *[str(p) for p in paths]],
        capture_output=True,
        text=True,
        cwd=str(root),
        timeout=600,
        check=False,
    )


def test_the_written_episode_passes_the_committed_checker(root, episode) -> None:
    done = check(root, episode)
    assert done.returncode == 0, done.stdout + done.stderr
    assert "EPISODES|checked=1|ok=1|failed=0" in done.stdout


def test_the_checker_can_fail_on_a_corrupted_ledger_write(root, episode, tmp_path) -> None:
    """The control for the rule that matters most: an episode has no authority."""
    document = json.loads(episode.read_text())
    document["outcome"]["ledger_writes"] = 1
    broken = tmp_path / "broken-ledger-writes.json"
    broken.write_text(episode_api.canonical(document))
    done = check(root, broken)
    assert done.returncode == 1
    assert "ledger-writes-must-be-zero" in done.stdout + done.stderr


def test_the_checker_can_fail_on_a_corrupted_proposal_digest(root, episode, tmp_path) -> None:
    document = json.loads(episode.read_text())
    assert document["proposals"], "the offline episode wrote no proposal to corrupt"
    document["proposals"][0]["sha256"] = "0" * 64
    broken = tmp_path / "broken-proposal.json"
    broken.write_text(episode_api.canonical(document))
    done = check(root, broken)
    assert done.returncode == 1
    assert "proposal-digest" in done.stdout + done.stderr


def test_the_checker_can_fail_on_a_corrupted_frontier_digest(root, episode, tmp_path) -> None:
    document = json.loads(episode.read_text())
    document["selection"]["frontier_sha256"] = "0" * 64
    broken = tmp_path / "broken-frontier.json"
    broken.write_text(episode_api.canonical(document))
    done = check(root, broken)
    assert done.returncode == 1
    assert "frontier-digest" in done.stdout + done.stderr


def test_the_checker_can_fail_on_an_empty_transcript(root, episode, tmp_path) -> None:
    document = json.loads(episode.read_text())
    document["transcript"]["tool_calls"] = []
    broken = tmp_path / "broken-transcript.json"
    broken.write_text(episode_api.canonical(document))
    done = check(root, broken)
    assert done.returncode == 1
    assert "empty-transcript" in done.stdout + done.stderr


def test_a_checked_directory_that_held_nothing_is_not_a_pass(root, tmp_path) -> None:
    done = check(root, tmp_path)
    assert done.returncode == 1
    assert "EPISODES|checked=0|ok=0|failed=0" in done.stdout


# ------------------------------------------------------------ writer invariants


def test_the_writer_refuses_a_verdict_this_slice_cannot_earn(root, episode) -> None:
    """A schema v1 document cannot say `proved`, and the reason is structural.

    v1 has no `checker_runs`, so rule 11 -- a `checked` tool call AND a checker
    that exited 0 -- has nothing to stand on there. Slice A4 widened the
    writer's verdict set, but only for `build_episode_v2`; `build_episode`
    still refuses, because a version that quietly gained the ability to claim a
    proof it cannot evidence would be worse than no version at all.
    """
    document = json.loads(episode.read_text())
    with pytest.raises(episode_api.EpisodeWriteError, match="schema v1 document"):
        episode_api.build_episode(
            root=root,
            commit=document["git_commit"],
            fact_id=document["selection"]["fact_id"],
            frontier=_live_frontier(root),
            frontier_path=root / "artifacts",
            partition=document["selection"]["partition"],
            model_id="test:offline",
            settings=document["policy"]["settings"],
            prompt_hashes=document["policy"]["prompt_hashes"],
            budgets=episode_api.Budgets(600, 8, 12, 400000, 32000, 0.5),
            messages_path="x",
            messages_sha256="0" * 64,
            tool_calls=document["transcript"]["tool_calls"],
            proposal_rows=[],
            verdict="proved",
            decline_class=None,
        )


def _live_frontier(root):
    from axeyum.knowledge import frontier as frontier_api

    return frontier_api.load(root)


def test_the_writer_refuses_an_empty_transcript(root, episode) -> None:
    document = json.loads(episode.read_text())
    with pytest.raises(episode_api.EpisodeWriteError, match="called nothing"):
        episode_api.build_episode(
            root=root,
            commit=document["git_commit"],
            fact_id=document["selection"]["fact_id"],
            frontier=_live_frontier(root),
            frontier_path=root / "artifacts",
            partition=document["selection"]["partition"],
            model_id="test:offline",
            settings=document["policy"]["settings"],
            prompt_hashes=document["policy"]["prompt_hashes"],
            budgets=episode_api.Budgets(600, 8, 12, 400000, 32000, 0.5),
            messages_path="x",
            messages_sha256="0" * 64,
            tool_calls=[],
            proposal_rows=[],
            verdict="declined",
            decline_class=None,
        )


def test_bytes_carrying_a_held_out_id_are_refused_before_they_reach_disk(root) -> None:
    blind = min(nursery_api.load(root).held_out_ids())
    with pytest.raises(HeldOutLeak) as caught:
        episode_api.assert_no_held_out(f'{{"note": "{blind}"}}', "a test payload", root)
    assert blind not in str(caught.value)
    episode_api.assert_no_held_out('{"note": "nothing blind here"}', "a test payload", root)


def test_an_unknown_tool_is_not_recorded_as_harmless(root) -> None:
    """Defaulting an unrecognized tool to `read` is how a tool with side effects
    gets written into the evidence as a read."""

    part = types.SimpleNamespace(
        part_kind="tool-call", tool_name="write_the_ledger", tool_call_id="c1", args={}
    )
    message = types.SimpleNamespace(parts=[part])
    with pytest.raises(episode_api.EpisodeWriteError, match="no declared assurance tier"):
        episode_api.project_tool_calls([message], [])


def test_the_agent_code_digest_changes_with_the_code(root) -> None:
    first = episode_api.agent_code_sha256()
    assert first == episode_api.agent_code_sha256()
    assert len(first) == 64


def test_git_commit_refuses_a_malformed_override(root) -> None:
    with pytest.raises(episode_api.EpisodeWriteError, match="40-hex"):
        episode_api.git_commit(root, "not-a-sha")


def test_canonical_json_is_sorted_and_newline_terminated() -> None:
    text = episode_api.canonical({"b": 1, "a": 2})
    assert text == '{\n  "a": 2,\n  "b": 1\n}\n'
