"""The two deterministic decision points: `Gate` and `Supervise`.

Both are pure functions of the state, which is the property under test as much
as any individual refusal. `gate_decision` and `supervisor_decision` take no
model, build no agent and reach no provider; a version of either that consulted
one would be the same actor deciding twice, and the loop's whole claim is that
the thing which authorizes is not the thing which proposes.

Every case below asserts the REASON, not just the boolean. A gate that refuses
for the wrong reason is a gate that will approve for the wrong reason.
"""

from __future__ import annotations

import time
from pathlib import Path
from types import SimpleNamespace

import pytest

pytest.importorskip("pydantic_ai", reason="the [agent] extra is not installed")

from _agent_offline import temporarily_open_fact

from axeyum.agent import graph as graph_api
from axeyum.agent import models as models_api
from axeyum.agent import tools
from axeyum.agent.models import NoGeneralRoute, StrategyProposal
from axeyum.knowledge import nursery as nursery_api
from axeyum.knowledge._paths import resolve_root

TARGET = "F:ml430-nat-modeq-symm-0a3d4d18"  # open + train/dev + exportable
SIBLINGS = [
    "F:ml430-nat-modeq-trans-ef9d1c46",
    "F:ml430-nat-modeq-comm-24b71e7a",
    "F:ml430-nat-modeq-one-516d46e8",
]
SETTLED = "F:ml430-int-modeq-trans-6d7863e0"


@pytest.fixture(scope="module")
def root() -> Path:
    with temporarily_open_fact(TARGET):
        yield resolve_root(None)


def state(root: Path, proposal=None, *, wall: float = 600.0, fact_id: str = TARGET):
    deps = tools.AgentDeps(root=root, deadline=time.monotonic() + wall)
    return SimpleNamespace(
        root=root,
        fact_id=fact_id,
        deps=deps,
        proposals=[proposal] if proposal is not None else [],
        gate_passed=False,
        producer_tool="",
    )


def strategy(**overrides) -> StrategyProposal:
    payload = {
        "fact_id": TARGET,
        "tactic_ids": ["T:modeq-equivalence-combinators"],
        "producer_id": "close_terminal",
        "why": "a definitional equivalence relation closed by primitive combinators",
        "expected_decline_class": "NotDefinitionalEquivalence",
        "sibling_fact_ids": list(SIBLINGS),
    }
    payload.update(overrides)
    return StrategyProposal(**payload)


def call(tool_name: str = "modeq_family", fact_id: str = TARGET, call_id: str = "c0"):
    return SimpleNamespace(tool_name=tool_name, args={"fact_id": fact_id}, tool_call_id=call_id)


# ------------------------------------------------------------------- the gate


def test_the_gate_passes_a_well_formed_plan_and_says_why(root: Path) -> None:
    passed, reason, tool = graph_api.gate_decision(state(root, strategy()))
    assert passed is True
    assert tool == "modeq_family"
    assert "siblings all train or development" in reason


def test_the_gate_refuses_when_no_plan_was_emitted(root: Path) -> None:
    passed, reason, _tool = graph_api.gate_decision(state(root))
    assert passed is False
    assert "nothing to gate" in reason


def test_the_gate_refuses_a_no_general_route_plan(root: Path) -> None:
    """Dispatching one anyway would discard the model's own finding."""
    proposal = NoGeneralRoute(
        fact_id=TARGET,
        tactic_ids=["T:refl-closure"],
        producer_id="close_terminal",
        why="a reflexivity goal with no sibling of the same shape",
        expected_decline_class="NotEqualityGoal",
        obstruction="nothing else eligible has the pure reflexivity structure",
    )
    passed, reason, _ = graph_api.gate_decision(state(root, proposal))
    assert passed is False
    assert "NoGeneralRoute" in reason


def test_the_gate_refuses_a_producer_no_tool_in_this_loop_executes(root: Path) -> None:
    """Naming a registered operation is not the same as having a route that runs it.

    The producer id used here is drawn from the live vocabulary rather than
    written down, so this cannot pass by naming something that stopped
    resolving: it must be a value the proposal schema ACCEPTS and the gate still
    refuses.
    """
    unrouted = sorted(models_api.known_producers() - set(tools.PRODUCER_TOOLS))
    assert unrouted, "every known producer routes to a tool; this control is vacuous"
    passed, reason, tool = graph_api.gate_decision(state(root, strategy(producer_id=unrouted[0])))
    assert passed is False
    assert "no" in reason and "tier-C tool" in reason
    assert tool == ""


def test_the_gate_refuses_a_plan_that_targets_another_fact(root: Path) -> None:
    other = SIBLINGS[0]
    proposal = strategy(fact_id=other, sibling_fact_ids=[TARGET, SIBLINGS[1], SIBLINGS[2]])
    passed, reason, _ = graph_api.gate_decision(state(root, proposal))
    assert passed is False
    assert "other than the selected one" in reason


def test_the_gate_refuses_a_sibling_the_nursery_does_not_preregister(
    root: Path, monkeypatch
) -> None:
    """Refusing rather than assuming: no partition can be checked for it."""
    pen = nursery_api.load(root)
    monkeypatch.setattr(
        nursery_api,
        "load",
        lambda _root: SimpleNamespace(
            contains=lambda f: f != SIBLINGS[1],
            partition_of=pen.partition_of,
        ),
    )
    passed, reason, _ = graph_api.gate_decision(state(root, strategy()))
    assert passed is False
    assert "not preregistered" in reason


def test_the_gate_refuses_a_sibling_outside_train_and_development(root: Path, monkeypatch) -> None:
    """A generality claim over a blind row spends that row's whole family."""
    pen = nursery_api.load(root)
    monkeypatch.setattr(
        nursery_api,
        "load",
        lambda _root: SimpleNamespace(
            contains=lambda f: True,
            partition_of=lambda f: "held-out" if f == SIBLINGS[2] else pen.partition_of(f),
        ),
    )
    passed, reason, _ = graph_api.gate_decision(state(root, strategy()))
    assert passed is False
    assert "train and development" in reason


def test_the_gate_refuses_when_less_budget_remains_than_one_producer_call(root: Path) -> None:
    passed, reason, _ = graph_api.gate_decision(state(root, strategy(), wall=5.0))
    assert passed is False
    assert "cannot be bounded" in reason


def test_the_gate_refuses_a_target_another_lane_already_settled(root: Path) -> None:
    proposal = strategy(fact_id=SETTLED)
    passed, reason, _ = graph_api.gate_decision(state(root, proposal, fact_id=SETTLED))
    assert passed is False
    assert "already settled" in reason


def test_fact_is_settled_reads_the_ledger_not_a_cached_value(root: Path) -> None:
    assert graph_api.fact_is_settled(root, SETTLED) is True
    assert graph_api.fact_is_settled(root, TARGET) is False
    assert graph_api.fact_is_settled(root, "F:no-such-fact-00000000") is False


# ------------------------------------------------------------- the supervisor


def test_the_supervisor_approves_an_eligible_call(root: Path) -> None:
    st = state(root, strategy())
    st.gate_passed, st.producer_tool = True, "modeq_family"
    approved, reason = graph_api.supervisor_decision(st, call())
    assert approved is True
    assert "ledger still open" in reason


def test_the_supervisor_denies_when_the_gate_did_not_pass(root: Path) -> None:
    st = state(root, strategy())
    st.gate_passed, st.producer_tool = False, "modeq_family"
    approved, reason = graph_api.supervisor_decision(st, call())
    assert approved is False
    assert "gate did not pass" in reason


def test_the_supervisor_denies_a_tool_other_than_the_one_the_gate_routed_to(root: Path) -> None:
    """An approval is for one route, not for the tier."""
    st = state(root, strategy())
    st.gate_passed, st.producer_tool = True, "modeq_family"
    approved, reason = graph_api.supervisor_decision(st, call(tool_name="bounded_induction"))
    assert approved is False
    assert "one route" in reason


def test_the_supervisor_denies_a_call_that_targets_another_fact(root: Path) -> None:
    st = state(root, strategy())
    st.gate_passed, st.producer_tool = True, "modeq_family"
    approved, reason = graph_api.supervisor_decision(st, call(fact_id=SIBLINGS[0]))
    assert approved is False
    assert "other than the selected one" in reason


def test_the_supervisor_denies_a_settled_fact(root: Path) -> None:
    st = state(root, strategy(fact_id=SETTLED), fact_id=SETTLED)
    st.gate_passed, st.producer_tool = True, "modeq_family"
    approved, reason = graph_api.supervisor_decision(st, call(fact_id=SETTLED))
    assert approved is False
    assert "already settles" in reason


def test_the_supervisor_reads_string_encoded_arguments(root: Path) -> None:
    """Some providers send tool arguments as a JSON string, not as an object."""
    st = state(root, strategy())
    st.gate_passed, st.producer_tool = True, "modeq_family"
    raw = SimpleNamespace(
        tool_name="modeq_family", args=f'{{"fact_id": "{TARGET}"}}', tool_call_id="c1"
    )
    approved, _ = graph_api.supervisor_decision(st, raw)
    assert approved is True


def test_the_supervisor_denies_unparseable_arguments(root: Path) -> None:
    st = state(root, strategy())
    st.gate_passed, st.producer_tool = True, "modeq_family"
    raw = SimpleNamespace(tool_name="modeq_family", args="{not json", tool_call_id="c2")
    approved, reason = graph_api.supervisor_decision(st, raw)
    assert approved is False
    assert "other than the selected one" in reason
