"""The deferred round trip, offline: ask, pause, decide, resume, re-check.

No provider is reached and no `/nas3` export is read. The producer is stubbed
through `tools.run_producer`, so what is exercised is the part that is ours: the
model can only ASK to dispatch, the run really does end at the approval, a
deterministic supervisor really does decide it, the tool's result is re-derived
by a second check, and the episode that comes out cannot say `proved` unless
both halves of rule 11 hold.

The sharpest assertion in the file is the negative one: with the supervisor
denying, the stub producer is never entered at all. A gate that let the work
happen and discarded the result afterwards would look identical from the
episode, and would not be a gate.
"""

from __future__ import annotations

import json
import time
from decimal import Decimal
from pathlib import Path

import pytest

pytest.importorskip("pydantic_ai", reason="the [agent] extra is not installed")

from _agent_offline import TEST_COMMIT, temporarily_open_fact
from pydantic_ai import ModelSettings
from pydantic_ai.usage import RunUsage, UsageLimits

from axeyum.agent import graph as graph_api
from axeyum.agent import tools
from axeyum.agent.cli import OFFLINE_MODEL_ID, offline_dispatch_model, offline_models
from axeyum.agent.episode import Budgets, EpisodeWriteError
from axeyum.agent.graph import EpisodeState, run_episode
from axeyum.agent.tools import AgentDeps
from axeyum.knowledge._paths import resolve_root

TARGET = (
    "F:ml430-nat-modeq-symm-0a3d4d18"  # open + train/dev + exportable (refl was proved on main)
)

STUB = {
    "goal_sha256": "a" * 64,
    "proof_sha256": "b" * 64,
    "binders_used": 2,
    "inductions_used": None,
    "admitted_declarations": 193,
    "axiom_footprint": (),
    "theorem_dependencies": (),
}


@pytest.fixture(scope="module")
def root() -> Path:
    with temporarily_open_fact(TARGET):
        yield resolve_root(None)


def a4_state(root: Path, out_dir: Path, fact_id: str = TARGET) -> EpisodeState:
    gather, plan = offline_models(root, fact_id)
    return EpisodeState(
        root=root,
        out_dir=out_dir,
        commit=TEST_COMMIT,
        model=gather,
        plan_model=plan,
        dispatch_model=offline_dispatch_model(fact_id, "modeq_family"),
        schema_version=2,
        model_id=OFFLINE_MODEL_ID,
        budgets=Budgets(600, 10, 16, 400000, 32000, 1.0),
        limits=UsageLimits(
            cost_limit=Decimal("1.00"),
            request_limit=10,
            tool_calls_limit=16,
            input_tokens_limit=400000,
            output_tokens_limit=32000,
        ),
        settings=ModelSettings(temperature=0.0, max_tokens=8192),
        fact_id=fact_id,
        deps=AgentDeps(root=root),
        usage=RunUsage(),
        deadline=time.monotonic() + 600,
    )


@pytest.fixture(scope="module")
def approved(root, tmp_path_factory, module_stub):
    del module_stub
    out = tmp_path_factory.mktemp("a4-approved")
    path = run_episode(a4_state(root, out))
    return path, json.loads(path.read_text())


@pytest.fixture(scope="module")
def module_stub():
    """Stub the producer for this module. Nothing here reads a pinned export."""
    original = tools.run_producer
    original_resolve = tools.resolve_export
    source = Path(__file__)
    digest = __import__("hashlib").sha256(source.read_bytes()).hexdigest()

    def resolve(root: Path, fact_id: str):
        if fact_id != TARGET:
            return original_resolve(root, fact_id)
        return tools.ExportResolution(
            fact_id=fact_id,
            path=source,
            sha256=digest,
            target_definition="Axeyum.Autogenesis.Statement.NatModEqFamily.natModEqSymm",
            source="portable-test-fixture",
        )

    tools.run_producer = lambda tool, export: dict(STUB)
    tools.resolve_export = resolve
    yield
    tools.run_producer = original
    tools.resolve_export = original_resolve


# ----------------------------------------------------------- the happy round trip


def test_the_round_trip_produces_a_v2_episode(approved) -> None:
    _path, document = approved
    assert document["schema_version"] == 2
    assert document["kind"] == "axeyum-agent-episode"
    assert document["episode_id"].startswith("E:a4-")


def test_the_dispatched_call_is_recorded_as_checked(approved) -> None:
    _path, document = approved
    checked = [c for c in document["transcript"]["tool_calls"] if c["assurance"] == "checked"]
    assert len(checked) == 1
    assert checked[0]["tool"] == "modeq_family"


def test_the_episode_records_a_passing_independent_checker_run(approved) -> None:
    _path, document = approved
    runs = document["outcome"]["checker_runs"]
    assert runs, "a v2 episode that dispatched must record what re-checked it"
    assert runs[0]["exit_status"] == 0
    assert runs[0]["assurance"] == "checked"
    assert "python -m axeyum.agent check" in runs[0]["command"]


def test_the_verdict_is_proved_and_the_footprint_is_empty(approved) -> None:
    _path, document = approved
    assert document["outcome"]["verdict"] == "proved"
    assert document["outcome"]["axiom_footprint"] == []
    assert document["outcome"]["decline_class"] is None


def test_the_episode_still_records_no_admission_authority(approved) -> None:
    _path, document = approved
    assert document["outcome"]["ledger_writes"] == 0
    assert document["outcome"]["target_theorem_submissions"] == 0


def test_the_selection_carries_the_ledger_digest_v1_could_not_hold(approved) -> None:
    _path, document = approved
    ledger = document["selection"]["ledger_sha256"]
    assert len(ledger) == 64
    assert ledger in document["selection"]["eligibility_reason"]


def test_the_transaction_proposal_run_is_recorded_whatever_it_returned(approved) -> None:
    """A nonzero status here is the useful case and must not be hidden."""
    _path, document = approved
    prepare = [
        r for r in document["outcome"]["checker_runs"] if "prepare-autogenesis" in r["command"]
    ]
    assert len(prepare) == 1
    assert "apply-autogenesis" not in json.dumps(document)


def test_the_committed_checker_accepts_the_written_v2_episode(approved, root) -> None:
    import subprocess
    import sys

    path, _document = approved
    done = subprocess.run(
        [sys.executable, str(root / "scripts/check-agent-episode.py"), str(path)],
        capture_output=True,
        text=True,
        cwd=str(root),
        timeout=300,
        check=False,
    )
    assert done.returncode == 0, done.stdout + done.stderr
    assert "EPISODES|checked=1|ok=1|failed=0" in done.stdout


# ------------------------------------------------------------------- the denial


def test_a_denied_dispatch_never_enters_the_producer(root, tmp_path, monkeypatch) -> None:
    """The decisive negative: denial must prevent the work, not discard its result."""
    entered: list[str] = []

    def spy(tool, export):
        entered.append(tool)
        return dict(STUB)

    monkeypatch.setattr(tools, "run_producer", spy)
    monkeypatch.setattr(graph_api, "supervisor_decision", lambda s, c: (False, "denied by policy"))
    state = a4_state(root, tmp_path)
    path = run_episode(state)
    document = json.loads(path.read_text())
    assert entered == [], "the producer ran despite a denial"
    assert document["outcome"]["verdict"] == "declined"
    assert document["outcome"]["decline_class"] == "supervisor-denied"


def test_the_denial_reason_reaches_the_model(root, tmp_path, monkeypatch) -> None:
    """A denial the model cannot see is a denial it will make again."""
    monkeypatch.setattr(tools, "run_producer", lambda tool, export: dict(STUB))
    monkeypatch.setattr(
        graph_api, "supervisor_decision", lambda s, c: (False, "denied: a distinctive reason")
    )
    state = a4_state(root, tmp_path)
    run_episode(state)
    transcript = (tmp_path / TARGET.split(":", 1)[1] / "messages.json.snapshot").read_text()
    assert "a distinctive reason" in transcript


def test_a_gate_refusal_stops_before_the_model_is_shown_a_tier_c_tool(
    root, tmp_path, monkeypatch
) -> None:
    monkeypatch.setattr(tools, "run_producer", lambda tool, export: dict(STUB))
    monkeypatch.setattr(graph_api, "gate_decision", lambda s: (False, "refused for the test", ""))
    state = a4_state(root, tmp_path)
    document = json.loads(run_episode(state).read_text())
    assert document["outcome"]["verdict"] == "declined"
    assert document["outcome"]["decline_class"] == "gate-refused"
    assert document["outcome"]["checker_runs"] == []
    assert all(c["assurance"] == "read" for c in document["transcript"]["tool_calls"])


# --------------------------------------------------------------- the re-check


def test_a_tampered_proof_term_makes_the_check_fail_and_the_verdict_declined(
    root, tmp_path, monkeypatch
) -> None:
    """The producer says one term, the second kernel derives another."""
    calls = {"n": 0}

    def drifting(tool, export):
        calls["n"] += 1
        measured = dict(STUB)
        if calls["n"] > 1:
            measured["proof_sha256"] = "f" * 64
        return measured

    monkeypatch.setattr(tools, "run_producer", drifting)
    document = json.loads(run_episode(a4_state(root, tmp_path)).read_text())
    assert document["outcome"]["verdict"] == "declined"
    assert document["outcome"]["checker_runs"][0]["exit_status"] == 1
    assert document["outcome"]["decline_class"] == "operational-failure"


def test_a_nonempty_axiom_footprint_is_not_proved(root, tmp_path, monkeypatch) -> None:
    """Admission succeeding is not the claim; an empty MEASURED footprint is."""
    measured = dict(STUB)
    measured["axiom_footprint"] = ("Classical.choice",)
    monkeypatch.setattr(tools, "run_producer", lambda tool, export: dict(measured))
    document = json.loads(run_episode(a4_state(root, tmp_path)).read_text())
    assert document["outcome"]["verdict"] == "declined"
    assert document["outcome"]["decline_class"] == "missing-certificate"
    assert document["outcome"]["axiom_footprint"] == ["Classical.choice"]


def test_a_producer_decline_lands_in_the_taxonomy_not_as_an_error(
    root, tmp_path, monkeypatch
) -> None:
    monkeypatch.setattr(
        tools,
        "run_producer",
        lambda tool, export: (_ for _ in ()).throw(RuntimeError("boom")),
    )
    document = json.loads(run_episode(a4_state(root, tmp_path)).read_text())
    assert document["outcome"]["verdict"] == "declined"
    assert document["outcome"]["decline_class"] == "operational-failure"


def test_an_unresolvable_export_is_recorded_as_a_retrieval_miss(root, tmp_path) -> None:
    """A fact with no frozen export: the gate passes, the supervisor approves,
    and the TOOL is what refuses -- with `retrieval-miss`, which is an AG4.1
    class and not `operational-failure`. Getting that distinction wrong was a
    measured defect: the outcome list was appended to only on the accepted
    branch, so the supervisor could not tell a decline from a tool that never
    ran, and an honest retrieval miss was written as a broken harness."""
    fact_id = next(
        (
            candidate
            for candidate in tools.eligible_fact_ids(root)
            if _export_is_unavailable(root, candidate)
        ),
        None,
    )
    assert fact_id is not None, "the retrieval-miss control needs one eligible fact with no export"
    state = a4_state(root, tmp_path, fact_id=fact_id)
    document = json.loads(run_episode(state).read_text())
    assert document["outcome"]["verdict"] == "declined"
    assert document["outcome"]["decline_class"] == "retrieval-miss"
    assert document["outcome"]["checker_runs"] == []


def _export_is_unavailable(root: Path, fact_id: str) -> bool:
    try:
        tools.resolve_export(root, fact_id)
    except tools.ExportUnavailable:
        return True
    return False


# ----------------------------------------------------------------- the replay


def test_a_v2_episode_replays_with_model_requests_disabled(approved, root, module_stub) -> None:
    del module_stub
    from axeyum.agent.replay import replay

    path, _document = approved
    result = replay(path, root=root)
    assert result.ok, result.diverged
    assert result.consumed_responses == result.recorded_responses


# ------------------------------------------------------------ the writer's rule


def test_the_writer_refuses_proved_without_a_checked_call(approved, root) -> None:
    from axeyum.agent import episode as episode_api
    from axeyum.knowledge import frontier as frontier_api

    _path, document = approved
    reads = [c for c in document["transcript"]["tool_calls"] if c["assurance"] == "read"]
    with pytest.raises(EpisodeWriteError, match="assurance='checked'"):
        episode_api.build_episode_v2(
            root=root,
            commit=document["git_commit"],
            fact_id=document["selection"]["fact_id"],
            frontier=frontier_api.load(root),
            frontier_path=root / "artifacts",
            partition=document["selection"]["partition"],
            model_id="test:offline",
            settings=document["policy"]["settings"],
            prompt_hashes=document["policy"]["prompt_hashes"],
            budgets=Budgets(600, 10, 16, 400000, 32000, 1.0),
            messages_path="x",
            messages_sha256="0" * 64,
            tool_calls=reads,
            proposal_rows=[],
            verdict="proved",
            decline_class=None,
            checker_runs=document["outcome"]["checker_runs"],
        )


def test_the_writer_refuses_proved_without_a_passing_checker_run(approved, root) -> None:
    from axeyum.agent import episode as episode_api
    from axeyum.knowledge import frontier as frontier_api

    _path, document = approved
    failing = [dict(r, exit_status=1) for r in document["outcome"]["checker_runs"]]
    with pytest.raises(EpisodeWriteError, match="no checker run exited 0"):
        episode_api.build_episode_v2(
            root=root,
            commit=document["git_commit"],
            fact_id=document["selection"]["fact_id"],
            frontier=frontier_api.load(root),
            frontier_path=root / "artifacts",
            partition=document["selection"]["partition"],
            model_id="test:offline",
            settings=document["policy"]["settings"],
            prompt_hashes=document["policy"]["prompt_hashes"],
            budgets=Budgets(600, 10, 16, 400000, 32000, 1.0),
            messages_path="x",
            messages_sha256="0" * 64,
            tool_calls=document["transcript"]["tool_calls"],
            proposal_rows=[],
            verdict="proved",
            decline_class=None,
            checker_runs=failing,
        )
