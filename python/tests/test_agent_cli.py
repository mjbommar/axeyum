"""The command line: what it refuses, and that an offline run is labelled as one."""

from __future__ import annotations

import json

import pytest

pytest.importorskip("pydantic_ai", reason="the [agent] extra is not installed")

from axeyum.agent import cli as cli_api
from axeyum.agent.tools import eligible_fact_ids
from axeyum.knowledge import nursery as nursery_api
from axeyum.knowledge._paths import resolve_root


@pytest.fixture(scope="module")
def root():
    return resolve_root(None)


def test_pick_facts_takes_the_next_n_eligible(root) -> None:
    assert cli_api.pick_facts(root, [], 4) == list(eligible_fact_ids(root)[:4])


def test_pick_facts_refuses_a_held_out_fact(root) -> None:
    blind = min(nursery_api.load(root).held_out_ids())
    with pytest.raises(SystemExit) as caught:
        cli_api.pick_facts(root, [blind], 0)
    assert blind not in str(caught.value)


def test_pick_facts_refuses_an_empty_request(root) -> None:
    with pytest.raises(SystemExit):
        cli_api.pick_facts(root, [], 0)


def test_an_offline_run_labels_itself_as_offline(root, tmp_path, capsys) -> None:
    fact_id = eligible_fact_ids(root)[0]
    status = cli_api.main(
        [
            "--root",
            str(root),
            "run",
            "--fact",
            fact_id,
            "--offline",
            "--out",
            str(tmp_path),
            "--git-commit",
            "0" * 40,
        ]
    )
    assert status == 0
    printed = capsys.readouterr().out
    assert "AGENT_EPISODES|requested=1|written=1|failed=0" in printed
    written = list(tmp_path.glob("episode-*.json"))
    assert len(written) == 1
    document = json.loads(written[0].read_text())
    assert document["policy"]["model_id"] == "test:offline", (
        "an episode that hid which model produced it would poison every "
        "downstream measurement conditioned on the model"
    )


def test_the_parser_defaults_to_a_provider_prefixed_model() -> None:
    args = cli_api.build_parser().parse_args(["run", "--next", "--n", "1"])
    assert ":" in args.model, "v2 rejects a bare model name; the default must carry a provider"


def _an_unreachable_eligible_fact(root) -> str:
    """An eligible fact with no frozen export -- a producer could only ever
    report retrieval-miss for it."""
    from axeyum.agent.tools import ExportUnavailable, resolve_export

    for fid in eligible_fact_ids(root):
        try:
            resolve_export(root, fid)
        except ExportUnavailable:
            return fid
    pytest.skip("every eligible fact has a frozen export; nothing to skip")


def test_skip_unreachable_skips_facts_with_no_export_without_spending_a_model(
    root, tmp_path, capsys
) -> None:
    unreachable = _an_unreachable_eligible_fact(root)
    status = cli_api.main(
        [
            "--root", str(root), "run",
            "--fact", unreachable,
            "--offline", "--skip-unreachable",
            "--out", str(tmp_path),
            "--git-commit", "0" * 40,
        ]
    )
    assert status == 0
    out = capsys.readouterr()
    # No episode written, no model spend -- the skip is on stderr, the summary counts it.
    assert not list(tmp_path.glob("episode-*.json"))
    assert f"AGENT_SKIP|fact={unreachable}|reason=no-frozen-export" in out.err
    assert "AGENT_EPISODES|requested=1|written=0|failed=0|skipped_unreachable=1" in out.out


def test_skip_unreachable_still_runs_a_reachable_fact(root, tmp_path, capsys) -> None:
    from axeyum.agent.tools import ExportUnavailable, resolve_export

    reachable = None
    for fid in eligible_fact_ids(root):
        try:
            resolve_export(root, fid)
            reachable = fid
            break
        except ExportUnavailable:
            continue
    if reachable is None:
        pytest.skip("no eligible fact has a frozen export")
    status = cli_api.main(
        [
            "--root", str(root), "run",
            "--fact", reachable,
            "--offline", "--skip-unreachable",
            "--out", str(tmp_path),
            "--git-commit", "0" * 40,
        ]
    )
    assert status == 0
    out = capsys.readouterr()
    assert len(list(tmp_path.glob("episode-*.json"))) == 1
    assert "skipped_unreachable=0" in out.out
