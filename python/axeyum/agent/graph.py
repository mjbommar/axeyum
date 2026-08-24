"""The frontier loop: Select -> Gather -> Plan -> Gate -> Dispatch -> Supervise
-> Check -> StageTransaction -> WriteEpisode.

Slice A2 dispatched nothing and that absence was the increment; A4 dispatches,
and the shape of *how* is the increment. Four of the nine nodes involve a model
and five do not, and the five are the ones that could do damage:

* `Select`, `Gate`, `Supervise`, `Check` and `WriteEpisode` run **no model**.
  The choice of what to work on, whether a plan may be dispatched, whether an
  approval is granted, whether the proof re-derives, and what is written down
  are all decided by code a referee can read.
* `Gather`, `Plan` and `Dispatch` are the model. `Dispatch` is the only one that
  can see a tier-C tool, and every tier-C tool is `requires_approval=True`, so
  the model calling one does not run it -- the run ENDS with a
  `DeferredToolRequests` output and waits. The model can ask. It cannot
  dispatch, and there is no argument it can pass that changes that.

`Supervise` deserves the sharpest statement of all: it is a deterministic
policy with no model in it, and it must stay that way. An LLM deciding whether
an LLM's plan may run is not a gate, it is the same actor twice.

What this loop still cannot do is admit a theorem. `StageTransaction` shells out
to `prepare-autogenesis-fact-transaction.py`, which is read-only and writes a
*proposal*; `apply-autogenesis-fact-transaction.py`, the repository's one ledger
writer, is not reachable from this package at all. `outcome.ledger_writes` is
pinned to 0 by the schema, by the checker, and by the writer.

`pydantic_graph.persistence` is **removed in v2**, and this design wants that.
A framework checkpoint is not a referee-auditable artifact: not content
addressed, not diffable, and not checkable by a standard-library gate that never
installs the framework. The episode is the persistence, and
`scripts/check-agent-episode.py` is what reads it.

Everything the deterministic nodes compute -- the eligible set, the frontier
digest, the partition, the gate decision, the supervisor's verdict, the
independent re-check, the tool-call projection -- must come out bit-identical on
replay, and :mod:`axeyum.agent.replay` fails when it does not. The model nodes'
output is recorded, never trusted.

A v1 episode replays through the A2 path: `Plan` returns straight to
`WriteEpisode` when `EpisodeState.schema_version` is 1. That is not a
compatibility shim, it is what makes the ten committed A2 episodes still
replayable against a graph that has grown five nodes -- a replay that ran the
new nodes would ask the recorded transcript for responses it never made.

Budget exhaustion is a **verdict**, not an error: a run that hits its cost,
request or wall limit writes an episode saying so, because "the loop stopped
because it ran out of money" and "the loop crashed" are different findings and
a harness that reports them the same way is hiding one of them.
"""

from __future__ import annotations

import asyncio
import json
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from pydantic_ai import (
    Agent,
    DeferredToolRequests,
    ModelSettings,
    ToolDenied,
    UsageLimitExceeded,
    capture_run_messages,
)
from pydantic_ai.usage import RunUsage, UsageLimits
from pydantic_graph import BaseNode, End, GraphBuilder, GraphRunContext

from ..knowledge import facts as facts_api
from ..knowledge import frontier as frontier_api
from ..knowledge import nursery as nursery_api
from ..knowledge._paths import read_json, resolve_root
from . import classify as classify_api
from . import episode as episode_api
from . import web as web_api
from .episode import Budgets, EpisodeWriteError
from .models import (
    ELIGIBLE_PARTITIONS,
    TACTIC_CATALOG,
    CheckVerified,
    NoGeneralRoute,
    ProducerAccepted,
    StrategyProposal,
)
from .models import Plan as PlanOutput
from .tools import (
    PRODUCER_TOOLS,
    PRODUCER_WALL_SECONDS,
    AgentDeps,
    build_toolset,
    eligible_fact_ids,
    independent_check,
)

#: How the episode's `decline_class` names why this run stopped.
#:
#: `DECLINE_NO_DISPATCH` is the A2 value and is written only into schema v1
#: documents; it is not in the v2 enum, because in A4 "nothing was dispatched"
#: is never the true reason -- the gate refused, or the supervisor denied, or
#: the producer declined, and saying which is the entire point of the taxonomy.
DECLINE_NO_DISPATCH = "no-dispatch-authority-in-slice-a2"
DECLINE_NO_GENERAL_ROUTE = "no-general-route"
DECLINE_BUDGET = "budget-exhausted-before-plan"
DECLINE_GATE = "gate-refused"
DECLINE_SUPERVISOR = "supervisor-denied"
DECLINE_OPERATIONAL = "operational-failure"

#: The reproduction command an independent re-check is recorded under. It is a
#: real command with a real exit status -- `python -m axeyum.agent check` exits
#: 0 only when a second kernel re-derives exactly this proof term -- because a
#: `checker_command` nobody can run is the decoration this repository audited 40
#: checker runs to find.
CHECK_COMMAND = (
    "python -m axeyum.agent check --fact {fact_id} --producer {tool} --expect-proof-sha256 {sha}"
)

#: The read-only transaction-proposal writer. `apply-autogenesis-fact-transaction.py`
#: is NOT here and is not reachable from this package; it is the ledger writer
#: and it stays a human-approved step.
PREPARE_TRANSACTION = "scripts/prepare-autogenesis-fact-transaction.py"


def partial_messages(history: list[Any], captured: list[Any]) -> list[Any]:
    """The transcript of a run that was cut short by a budget.

    `capture_run_messages` yields the run's FULL message list -- INCLUDING the
    `message_history` it was handed. Concatenating `history + captured`
    therefore duplicates everything that came before, and it did: measured
    2026-08-24, both budget-exhausted episodes carried the entire Gather run
    twice (22 messages where 12 happened), which made them unreplayable because
    the graph then asked for more responses than the run had made.

    An empty capture is a real case -- the limit can bite before the first
    response -- and there the history is all there is.
    """
    return list(captured) if captured else list(history)


def instructions_text(root: Path) -> str:
    """The standing instructions, rendered from the vocabulary that constrains them.

    The tactic ids are read out of the catalog rather than transcribed, so a
    catalog change is a prompt change is a new `prompt_hashes.instructions` --
    which is the honest outcome, because a plan written against a different
    vocabulary is a plan from a different agent.
    """
    catalog = read_json(root / TACTIC_CATALOG)
    lines = [
        f"  {row['id']}  ({row.get('kind', '?')})  {row.get('title', '')}"
        for row in catalog.get("tactics", [])
        if isinstance(row, dict) and "id" in row
    ]
    return (
        "You are the proposer in Axeyum's autonomous frontier loop.\n"
        "\n"
        "Axeyum is a Rust automated-reasoning stack with a Lean kernel. Its fact\n"
        "ledger records open mathematical propositions; a producer proposes a proof\n"
        "plan and a FRESH kernel process decides whether it worked. You are the\n"
        "proposer and nothing else.\n"
        "\n"
        "WHAT YOU CAN DO. You have six read-only tools. After you emit a plan, a\n"
        "DETERMINISTIC gate -- code, not a model -- decides whether that plan may be\n"
        "dispatched; if it passes you are then given one producer tool and asked to\n"
        "call it. That tool requires approval: calling it does not run it. It ends\n"
        "your turn, and a deterministic supervisor outside this agent decides. You\n"
        "cannot admit a declaration or write to the ledger by any route at all.\n"
        "\n"
        "Nothing you emit is evidence. Every proposal you make is recorded with\n"
        "assurance='proposed'; a producer result is recorded and then RE-DERIVED in a\n"
        "second, independent kernel before it counts. Do not claim a fact is proved,\n"
        "and do not describe your plan, or a producer's accepted result, as verified.\n"
        "\n"
        "THE BLIND POPULATION. Some facts are held out for evaluation. The tools\n"
        "filter them out before you see them, so work only with ids the tools\n"
        "returned to you. Never invent or guess a fact id.\n"
        "\n"
        "THE VOCABULARY. A plan names tactics from this catalog, by id:\n"
        + "\n".join(lines)
        + "\n\n"
        "and a producer_id that is either a registered operation id (see\n"
        "operation_registry) or a producer symbol the catalog names\n"
        "(close_terminal, try_induction, try_congr_rewrite, try_residual_lemma,\n"
        "try_absurd_elimination, try_case_split_elimination, try_split_congruence,\n"
        "try_absorbing_argument).\n"
        "\n"
        "THE GENERALITY RULE. An operation that reaches exactly one theorem is a\n"
        "dispatch-table entry, not a producer: 24 of 26 registered operations were\n"
        "measured to name exactly one fact, and that is the defect this loop\n"
        "exists to fix. So a StrategyProposal must name at least THREE other\n"
        "eligible facts the same tactics and producer would reach, chosen from ids\n"
        "the tools showed you. If you cannot honestly name three, emit\n"
        "NoGeneralRoute instead and say what is specific to this goal. Emitting\n"
        "NoGeneralRoute is a RESULT, not a failure -- it is the datapoint the\n"
        "obstruction graph is built from. Inventing siblings to satisfy the rule\n"
        "destroys exactly the measurement this loop is for.\n"
    )


GATHER_PROMPT = (
    "Target fact: {fact_id}\n"
    "\n"
    "Investigate it with the read tools, then summarize in at most 200 words.\n"
    "Suggested moves, in order, but use your judgement and stop when you have\n"
    "enough:\n"
    "  1. fact_get on the target -- read its formal statement and fragment.\n"
    "  2. fact_neighbourhood -- what it rests on and what it would free.\n"
    "  3. kernel_theorems on the prelude its fragment names -- the premises you\n"
    "     would actually have. Use a glob; an empty result for a glob means the\n"
    "     lookup FAILED, not that the prelude is empty.\n"
    "  4. frontier_select -- other eligible facts of the same shape.\n"
    "  5. operation_registry -- whether anything already targets it.\n"
    "\n"
    "Report: the goal's structural shape, which premises exist, and which other\n"
    "eligible facts share the shape. Do not propose a plan yet."
)

PLAN_PROMPT = (
    "Now emit your plan for {fact_id} as a structured result.\n"
    "\n"
    "Choose StrategyProposal only if you can name at least three OTHER eligible\n"
    "fact ids -- ids the tools actually returned -- that these same tactics and\n"
    "this same producer would reach. Otherwise choose NoGeneralRoute and state\n"
    "the obstruction. Do not invent fact ids or tactic ids; both are checked\n"
    "against the ledger and the catalog and an unknown id is rejected."
)


DISPATCH_PROMPT = (
    "Your plan for {fact_id} named producer {producer_id}, which this loop routes\n"
    "to the tool `{tool}`. Call that tool now, exactly once, with fact_id\n"
    "{fact_id} and nothing else.\n"
    "\n"
    "Calling it ENDS your turn. The tool requires approval: a deterministic\n"
    "supervisor outside this agent decides whether it runs, and no argument you\n"
    "pass changes that. If the call is denied you will be told why; report the\n"
    "denial and stop. If it runs, report the result verbatim and stop -- do not\n"
    "characterize a `declined` result as a failure of the fact, and do not\n"
    "describe an `accepted` result as proved. A second, independent kernel\n"
    "decides that, after you."
)


@dataclass
class EpisodeState:
    """Everything one episode needs, and everything it accumulates.

    This is the graph's state rather than its dependencies because a replay has
    to re-derive it: the deterministic nodes read and write exactly these
    fields, and the `selection` and `outcome` blocks of the episode are
    functions of them alone.
    """

    root: Path
    out_dir: Path
    commit: str
    model: Any
    model_id: str
    budgets: Budgets
    limits: UsageLimits
    settings: ModelSettings
    fact_id: str
    deps: AgentDeps
    #: An optional second model for the `Plan` node only. It exists for the
    #: offline stand-in: `TestModel` primed with `custom_output_args` raises on
    #: a run whose `output_type` is `str`, because there is no output tool to
    #: put the args in. Live runs and replays leave this `None` and use one
    #: model throughout, which is what makes a replay a replay.
    plan_model: Any = None
    #: An optional third model for the `Dispatch` node only, for the same reason
    #: `plan_model` exists: the offline stand-in has to emit one specific tool
    #: call with one specific argument, and `TestModel` invents its arguments
    #: from the schema. Live runs and replays leave this `None` and use one
    #: model throughout, which is what makes a replay a replay.
    dispatch_model: Any = None
    #: Which episode schema this run writes, and therefore which loop it runs.
    #: `1` is the A2 four-node path and exists so the ten committed A2 episodes
    #: still replay against a graph that has grown five nodes; `2` is A4.
    schema_version: int = episode_api.SCHEMA_VERSION_V2
    usage: RunUsage = field(default_factory=RunUsage)
    deadline: float = 0.0
    frontier: frontier_api.Frontier | None = None
    frontier_path: Path | None = None
    partition: str = ""
    messages: list[Any] = field(default_factory=list)
    gather_summary: str = ""
    proposals: list[StrategyProposal | NoGeneralRoute] = field(default_factory=list)
    verdict: str = "declined"
    decline_class: str | None = DECLINE_NO_DISPATCH
    episode_path: Path | None = None
    #: What the deterministic gate decided, and why. Recorded whichever way it
    #: went: "the gate passed" is as much a finding as "the gate refused", and a
    #: state that only carried refusals would make the pass unauditable.
    gate_passed: bool = False
    gate_reason: str = ""
    #: The tier-C tool the plan's `producer_id` routes to, empty when none does.
    producer_tool: str = ""
    #: Whether this episode ASKED for the A6 retrieval tools. Default off, and
    #: off is not the same as refused: `web_reason` records which it was, so an
    #: episode that never asked and one whose family the guard closed are
    #: distinguishable afterwards.
    allow_web: bool = False
    #: What `web.family_guard` decided in `Gather`, in its own words. Never
    #: contains a fact id.
    web_reason: str = "web retrieval was not requested for this episode"
    #: Whether the `Gather` toolset actually carried `web_fetch`/`python_exec`.
    web_enabled: bool = False
    #: The pending approval request the deferred tool call ended the run with.
    deferred: Any = None
    #: What the supervisor decided per tool call id: `(approved, reason)`.
    supervisor_decisions: dict[str, tuple[bool, str]] = field(default_factory=dict)
    #: The typed tier-C outcome, once a tool actually ran.
    producer_outcome: Any = None
    #: What the SECOND kernel said. Never the producer's own word.
    check_outcome: Any = None
    #: What `Classify` made of a decline: the typed obstruction cluster this run
    #: belongs to. It is NOT written into the episode -- schema v2 already has
    #: every field the classification is a function of, and slice A5 deliberately
    #: added none -- so this exists for the CLI, for logging, and as the in-graph
    #: half of the pair `python/tests/test_agent_classify.py` holds to agreement
    #: with `scripts/gen-obstruction-graph.py`.
    classification: Any = None
    checker_runs: list[dict[str, Any]] = field(default_factory=list)
    axiom_footprint: list[str] = field(default_factory=list)
    transaction_path: Path | None = None
    observed: dict[str, Any] = field(
        default_factory=lambda: {
            "facts_unlocked": [],
            "operations_widened": [],
            "overlay_links_proposed": [],
        }
    )

    def out_of_time(self) -> bool:
        return self.deadline > 0 and time.monotonic() > self.deadline

    def prompt_hashes(self) -> dict[str, str]:
        return {
            "instructions": episode_api.sha256_text(instructions_text(self.root)),
            "gather": episode_api.sha256_text(GATHER_PROMPT),
            "plan": episode_api.sha256_text(PLAN_PROMPT),
            "dispatch": episode_api.sha256_text(DISPATCH_PROMPT),
        }


def build_agent(
    state: EpisodeState,
    *,
    for_plan: bool = False,
    include_tier_c: bool = False,
    with_web: bool = False,
) -> Agent[AgentDeps, str]:
    """One agent, standing instructions, and only the tools the caller asked for.

    `retries=3` is what turns a validation failure into feedback: an unknown
    tactic id comes back to the model as the validator's own message, so the
    vocabulary is taught by the schema rather than by the prompt.

    `include_tier_c` defaults to False, and the default is the guard: `Gather`
    and `Plan` call this with no argument, so the model that looks and the model
    that plans cannot see a tool that dispatches. Only `Dispatch` and
    `Supervise` pass True, and there every tier-C tool is
    `requires_approval=True`.

    `with_web` defaults to False for the same reason and answers a different
    question: not "may it dispatch" but "may it retrieve". Only `Gather` passes
    True, only when `state.allow_web` was asked for AND `web.family_guard`
    allows it for this episode's target. A run that never asks is byte-identical
    to one from before slice A6, which is what keeps the committed episodes
    replayable.
    """
    model = state.model
    if for_plan and state.plan_model is not None:
        model = state.plan_model
    elif include_tier_c and state.dispatch_model is not None:
        model = state.dispatch_model
    return Agent(
        model,
        deps_type=AgentDeps,
        toolsets=[build_toolset(include_tier_c=include_tier_c, with_web=with_web)],
        instructions=instructions_text(state.root),
        model_settings=state.settings,
        retries=3,
    )


def web_decision(state: EpisodeState) -> web_api.FamilyDecision:
    """May this episode see the A6 retrieval tools? Two conditions, both required.

    `allow_web` is the REQUEST and `web.family_guard` is the POLICY, and they are
    kept apart because the two "no"s are different findings: an episode that
    never asked and an episode whose nursery family the guard closed both run
    without `web_fetch`, and only one of them is the guard doing its job.

    A module-level function rather than a block inside `Gather.run` so it can be
    exercised without a model. A guard that can only be observed by running a
    whole episode is a guard whose branches get tested on the paths that happen
    to be reachable today -- and today no eligible fact sits in a family with a
    held-out member, so the disabling branch would never run.
    """
    if not state.allow_web:
        return web_api.Disabled("web retrieval was not requested for this episode")
    return web_api.family_guard(state.fact_id, state.root)


# ------------------------------------------------------------------- the nodes


@dataclass
class Select(BaseNode[EpisodeState, None, Path]):
    """Deterministic. Pin the frontier, check eligibility, commit the snapshot.

    No model runs here and none may: the choice of what to work on is where a
    blind row would be spent, so it is made by the partition filter and recorded
    with the digest of the frontier it was made from.
    """

    async def run(self, ctx: GraphRunContext[EpisodeState, None]) -> Gather:
        state = ctx.state
        eligible = eligible_fact_ids(state.root)
        if state.fact_id not in eligible:
            raise EpisodeWriteError(
                "the requested fact is not in the eligible population "
                f"({len(eligible)} facts: open, dependency-ready, train or development)"
            )
        state.partition = episode_api.fact_partition(state.root, state.fact_id)
        state.frontier = frontier_api.load(state.root)
        state.frontier_path, _ = episode_api.save_frontier(state.frontier, state.out_dir)
        state.deps.selected_fact_id = state.fact_id
        state.deps.deadline = state.deadline
        # Pinned here rather than in `Gather`, because `web_fetch` refuses
        # without it: a snapshot outside the episode directory is a digest
        # `check-agent-episode.py` rule 4 cannot resolve.
        state.deps.episode_dir = state.out_dir
        return Gather()


@dataclass
class Gather(BaseNode[EpisodeState, None, Path]):
    """The model, with read tools only. Its job is to look, not to decide."""

    async def run(self, ctx: GraphRunContext[EpisodeState, None]) -> Plan | WriteEpisode:
        state = ctx.state
        if state.out_of_time():
            state.verdict, state.decline_class = "budget-exhausted", DECLINE_BUDGET
            return WriteEpisode()
        # The A6 guard, evaluated once per episode and recorded either way.
        decision = web_decision(state)
        state.web_enabled = bool(decision.allowed)
        state.web_reason = decision.reason
        agent = build_agent(state, with_web=state.web_enabled)
        try:
            with capture_run_messages() as captured:
                result = await agent.run(
                    GATHER_PROMPT.format(fact_id=state.fact_id),
                    deps=state.deps,
                    usage=state.usage,
                    usage_limits=state.limits,
                )
        except UsageLimitExceeded:
            state.messages = partial_messages([], list(captured))
            state.verdict, state.decline_class = "budget-exhausted", DECLINE_BUDGET
            return WriteEpisode()
        state.gather_summary = str(result.output)
        state.messages = list(result.all_messages())
        return Plan()


@dataclass
class Plan(BaseNode[EpisodeState, None, Path]):
    """The model again, this time constrained to the proposal schema.

    `output_type` is the discriminated union, so the model's only two ways to
    finish are "here is a route and three siblings it reaches" and "there is no
    general route and here is why". Prose is not one of them.
    """

    async def run(self, ctx: GraphRunContext[EpisodeState, None]) -> Gate | WriteEpisode:
        state = ctx.state
        if state.out_of_time():
            state.verdict, state.decline_class = "budget-exhausted", DECLINE_BUDGET
            return WriteEpisode()
        agent = build_agent(state, for_plan=True)
        history = list(state.messages)
        try:
            with capture_run_messages() as captured:
                result = await agent.run(
                    PLAN_PROMPT.format(fact_id=state.fact_id),
                    output_type=PlanOutput,
                    message_history=history,
                    deps=state.deps,
                    usage=state.usage,
                    usage_limits=state.limits,
                )
        except UsageLimitExceeded:
            state.messages = partial_messages(history, list(captured))
            state.verdict = "budget-exhausted"
            state.decline_class = "budget-exhausted-during-plan"
            return WriteEpisode()
        proposal = result.output
        state.proposals = [proposal]
        state.messages = list(result.all_messages())
        state.verdict = "declined"
        state.decline_class = (
            DECLINE_NO_GENERAL_ROUTE
            if isinstance(proposal, NoGeneralRoute)
            else DECLINE_NO_DISPATCH
        )
        if state.schema_version < episode_api.SCHEMA_VERSION_V2:
            # The A2 four-node path, kept alive so the ten committed v1 episodes
            # still replay. Running the A4 nodes against a v1 transcript would
            # ask it for responses it never made.
            return WriteEpisode()
        return Gate()


@dataclass
class Gate(BaseNode[EpisodeState, None, Path]):
    """Deterministic. May this plan be dispatched at all? No model runs here.

    Four refusals, and each one exists because the alternative is a measured
    failure mode rather than a hypothetical:

    * **The plan must name a route this loop can execute.** `producer_id` is
      already checked against the vocabulary by the proposal schema, but naming
      a registered operation is not the same as naming something with a tool
      behind it. A `NoGeneralRoute` never reaches here at all.
    * **Every sibling must be train or development.** The plan's siblings are
      the claim that the route generalizes, and a claim over a blind row spends
      that row: one capsule registered against one held-out fact cost 19 of 76
      held-out propositions on 2026-08-21. The tools filter what the model can
      SEE; this filters what it may act on, and the two guards are not
      redundant.
    * **Budget must remain.** A producer call is budgeted at
      `PRODUCER_WALL_SECONDS`; starting one with less than that left is starting
      work that cannot be bounded.
    * **The target must still be open.** Between selection and dispatch another
      lane can settle the fact, and re-proving a settled fact is not what this
      loop is measuring.

    A refusal is a `declined` verdict with `decline_class = "gate-refused"` and a
    stated reason, never an exception: "the gate refused" is a datapoint and an
    exception would put it in the harness's error path.
    """

    async def run(self, ctx: GraphRunContext[EpisodeState, None]) -> Dispatch | Classify:
        state = ctx.state
        passed, reason, tool = gate_decision(state)
        state.gate_passed, state.gate_reason, state.producer_tool = passed, reason, tool
        if not passed:
            state.verdict, state.decline_class = "declined", DECLINE_GATE
            return Classify()
        return Dispatch()


def gate_decision(state: EpisodeState) -> tuple[bool, str, str]:
    """`(passed, reason, tool)`. Pure, so it is testable without running a graph.

    The reason is returned on the passing branch too. A gate that explains only
    its refusals cannot be audited on the runs that mattered.
    """
    if not state.proposals:
        return (False, "the plan node emitted no proposal, so there is nothing to gate", "")
    proposal = state.proposals[0]
    if isinstance(proposal, NoGeneralRoute):
        return (
            False,
            (
                "the plan is NoGeneralRoute; the model declined to claim a route that "
                "generalizes, and dispatching one anyway would discard its own finding"
            ),
            "",
        )
    tool = PRODUCER_TOOLS.get(proposal.producer_id, "")
    if not tool:
        return (
            False,
            (
                f"producer_id {proposal.producer_id!r} resolves in the vocabulary but no "
                f"tier-C tool in this loop executes it; naming an operation is not the "
                f"same as having a route that runs it"
            ),
            "",
        )
    if proposal.fact_id != state.fact_id:
        return (
            False,
            (
                "the plan targets a fact other than the selected one; the selection is "
                "where eligibility was decided and a plan may not move it"
            ),
            tool,
        )
    pen = nursery_api.load(state.root)
    for sibling in proposal.sibling_fact_ids:
        if not pen.contains(sibling):
            return (
                False,
                (
                    "a sibling is not preregistered in the nursery, so no partition can "
                    "be checked for it; refusing rather than assuming"
                ),
                tool,
            )
        if pen.partition_of(sibling) not in ELIGIBLE_PARTITIONS:
            return (
                False,
                (
                    "a sibling is outside the train and development partitions; a "
                    "generality claim over a blind row spends that row's whole family"
                ),
                tool,
            )
    remaining = state.deps.seconds_remaining()
    if remaining is not None and remaining < PRODUCER_WALL_SECONDS:
        return (
            False,
            (
                f"{remaining:.0f}s of wall budget remain against a "
                f"{PRODUCER_WALL_SECONDS}s producer budget; refusing to start work that "
                f"cannot be bounded"
            ),
            tool,
        )
    if fact_is_settled(state.root, state.fact_id):
        return (
            False,
            (
                "the target is already settled in the ledger; another lane closed it "
                "between selection and dispatch and re-proving it measures nothing"
            ),
            tool,
        )
    return (
        True,
        (
            f"plan names {proposal.producer_id} -> {tool}; "
            f"{len(proposal.sibling_fact_ids)} siblings all train or development; "
            f"target still open; budget remains"
        ),
        tool,
    )


def fact_is_settled(root: Path, fact_id: str) -> bool:
    """Whether the ledger already calls this fact established.

    Read from the ledger every time rather than cached on the state: the whole
    point of the check is that another lane may have moved it since selection.
    """
    try:
        fact = facts_api.load(root).get(fact_id)
    except KeyError:
        return False
    return bool(fact.is_settled)


@dataclass
class Dispatch(BaseNode[EpisodeState, None, Path]):
    """The model, now able to SEE a tier-C tool. It still cannot run one.

    The tool is declared `requires_approval=True`, so the model calling it does
    not execute it: pydantic-ai ends the run with a `DeferredToolRequests`
    output carrying the pending call. That is the pause point, and it is a typed
    object rather than a framework checkpoint -- which is why it can be recorded
    in an episode and re-derived on replay.

    An output that is not a `DeferredToolRequests` means the model talked
    instead of calling, and that is `operational-failure`: the loop asked for a
    dispatch and did not get one.
    """

    async def run(self, ctx: GraphRunContext[EpisodeState, None]) -> Supervise | Classify:
        state = ctx.state
        if state.out_of_time():
            state.verdict, state.decline_class = "budget-exhausted", DECLINE_BUDGET
            return Classify()
        proposal = state.proposals[0]
        agent = build_agent(state, include_tier_c=True)
        history = list(state.messages)
        try:
            with capture_run_messages() as captured:
                result = await agent.run(
                    DISPATCH_PROMPT.format(
                        fact_id=state.fact_id,
                        producer_id=proposal.producer_id,
                        tool=state.producer_tool,
                    ),
                    output_type=[str, DeferredToolRequests],
                    message_history=history,
                    deps=state.deps,
                    usage=state.usage,
                    usage_limits=state.limits,
                )
        except UsageLimitExceeded:
            state.messages = partial_messages(history, list(captured))
            state.verdict = "budget-exhausted"
            state.decline_class = "budget-exhausted-during-plan"
            return Classify()
        state.messages = list(result.all_messages())
        output = result.output
        if not isinstance(output, DeferredToolRequests) or not output.approvals:
            state.verdict, state.decline_class = "declined", DECLINE_OPERATIONAL
            state.gate_reason = (
                f"{state.gate_reason}; but the model did not call the tool: the run "
                f"finished with {type(output).__name__} instead of an approval request"
            )
            return Classify()
        state.deferred = output
        return Supervise()


@dataclass
class Supervise(BaseNode[EpisodeState, None, Path]):
    """Deterministic policy. NO MODEL. This is the trusted process the tier exists for.

    An LLM deciding whether an LLM's plan may run is not a gate, it is the same
    actor twice, so this node holds no model and takes none: the decision is a
    function of the gate's verdict, the ledger, and the arguments the call
    actually carries.

    A denial is `ToolDenied(reason)` handed back through `DeferredToolResults`,
    so the model is *told* why -- a denial the model cannot see is a denial it
    will make again -- and the reason is recorded on the episode.
    """

    async def run(self, ctx: GraphRunContext[EpisodeState, None]) -> Check | Classify:
        state = ctx.state
        requests = state.deferred
        approvals: dict[str, Any] = {}
        for call in requests.approvals:
            approved, reason = supervisor_decision(state, call)
            state.supervisor_decisions[str(call.tool_call_id)] = (approved, reason)
            approvals[call.tool_call_id] = True if approved else ToolDenied(reason)
        results = requests.build_results(approvals=approvals)
        agent = build_agent(state, include_tier_c=True)
        history = list(state.messages)
        try:
            with capture_run_messages() as captured:
                result = await agent.run(
                    output_type=[str, DeferredToolRequests],
                    message_history=history,
                    deferred_tool_results=results,
                    deps=state.deps,
                    usage=state.usage,
                    usage_limits=state.limits,
                )
        except UsageLimitExceeded:
            state.messages = partial_messages(history, list(captured))
            state.verdict = "budget-exhausted"
            state.decline_class = "budget-exhausted-during-plan"
            return Classify()
        state.messages = list(result.all_messages())
        if not any(approved for approved, _ in state.supervisor_decisions.values()):
            state.verdict, state.decline_class = "declined", DECLINE_SUPERVISOR
            return Classify()
        outcomes = list(state.deps.producer_outcomes)
        if not outcomes:
            state.verdict, state.decline_class = "declined", DECLINE_OPERATIONAL
            return Classify()
        state.producer_outcome = outcomes[-1]
        return Check()


def supervisor_decision(state: EpisodeState, call: Any) -> tuple[bool, str]:
    """`(approved, reason)` for one pending tier-C call. Pure and model-free.

    Approve only when every one of these holds, and say which failed otherwise:
    the gate passed, the tool is the one the gate routed to, the call targets the
    selected fact, and the ledger still calls that fact open.
    """
    if not state.gate_passed:
        return (False, "the deterministic gate did not pass this plan")
    tool_name = str(getattr(call, "tool_name", ""))
    if tool_name != state.producer_tool:
        return (
            False,
            (
                f"the gate authorized {state.producer_tool!r} and this call is "
                f"{tool_name!r}; an approval is for one route, not for the tier"
            ),
        )
    args = getattr(call, "args", None)
    if isinstance(args, str):
        try:
            args = json.loads(args)
        except json.JSONDecodeError:
            args = None
    target = (args or {}).get("fact_id") if isinstance(args, dict) else None
    if target != state.fact_id:
        return (
            False,
            (
                "the call targets a fact other than the selected one; the selection is "
                "where eligibility and partition were decided"
            ),
        )
    if fact_is_settled(state.root, state.fact_id):
        return (False, "the ledger already settles this fact; re-proving it measures nothing")
    return (True, "gate passed, tool and target match the selection, ledger still open")


@dataclass
class Check(BaseNode[EpisodeState, None, Path]):
    """Independent re-check in a SECOND kernel. The producer's word is not evidence.

    A term cannot be carried between kernels -- an `ExprId` is an index into the
    kernel that interned it -- and that constraint is what makes this honest:
    the only way to re-check is to re-import the same frozen export into a fresh
    kernel, re-run the producer, re-render and re-hash. Two kernels agreeing is
    a different claim from one kernel consulted twice.

    `verdict = "proved"` requires the re-check to agree AND the measured axiom
    footprint to be empty. Not "admission succeeded" -- the footprint is read
    off the admitted name, because the Rust `axiom_footprint` answers an absent
    name with an empty vector and the Python binding raises instead, which is
    the whole reason an empty list here means anything.
    """

    async def run(self, ctx: GraphRunContext[EpisodeState, None]) -> StageTransaction | Classify:
        state = ctx.state
        outcome = state.producer_outcome
        if not isinstance(outcome, ProducerAccepted):
            state.verdict = "declined"
            state.decline_class = getattr(outcome, "decline_class", DECLINE_OPERATIONAL)
            return Classify()
        verdict = independent_check(state.root, state.fact_id, outcome.tool, outcome.proof_sha256)
        state.check_outcome = verdict
        record = verdict.model_dump(mode="json")
        state.checker_runs.append(
            {
                "command": CHECK_COMMAND.format(
                    fact_id=state.fact_id, tool=outcome.tool, sha=outcome.proof_sha256
                ),
                "exit_status": 0 if isinstance(verdict, CheckVerified) else 1,
                "output_sha256": episode_api.sha256_text(episode_api.canonical(record)),
                "assurance": "checked",
            }
        )
        if not isinstance(verdict, CheckVerified):
            state.verdict, state.decline_class = "declined", DECLINE_OPERATIONAL
            return Classify()
        state.axiom_footprint = list(verdict.axiom_footprint)
        if verdict.axiom_footprint:
            state.verdict, state.decline_class = "declined", "missing-certificate"
            return Classify()
        state.verdict, state.decline_class = "proved", None
        return StageTransaction()


def run_prepare(command: list[str], root: Path) -> tuple[int, str]:
    """Run the read-only proposal writer, bounded. `(exit status, combined output)`.

    A timeout is reported as a nonzero status with the reason in the output, not
    as a skip: a subprocess that never returns is a gate that never fails.
    """
    try:
        done = subprocess.run(
            command,
            capture_output=True,
            text=True,
            timeout=120,
            cwd=str(root),
            check=False,
        )
    except subprocess.TimeoutExpired:
        return (124, "prepare-autogenesis-fact-transaction.py did not finish in 120s")
    except (OSError, subprocess.SubprocessError) as error:
        return (2, f"{type(error).__name__}: {error}")
    return (done.returncode, (done.stdout or "") + (done.stderr or ""))


@dataclass
class StageTransaction(BaseNode[EpisodeState, None, Path]):
    """Write a transaction PROPOSAL, and never apply one.

    `prepare-autogenesis-fact-transaction.py` is read-only with respect to the
    ledger: it derives a proposal and writes it to `--output`.
    `apply-autogenesis-fact-transaction.py` is the repository's one ledger
    writer and is not invoked, imported, or named anywhere in this package.

    The proposal run's exit status is recorded whatever it is. A nonzero status
    is the honest and useful case: it says the fact is not covered by a
    registered authoritative operation, which is exactly the prerequisite the
    human ledger-writing step has to satisfy. An episode that hid that would be
    reporting a smaller world than it saw.
    """

    async def run(self, ctx: GraphRunContext[EpisodeState, None]) -> WriteEpisode:
        state = ctx.state
        episode_dir = state.out_dir / state.fact_id.split(":", 1)[1]
        episode_dir.mkdir(parents=True, exist_ok=True)
        target = episode_dir / f"transaction.proposal{episode_api.SNAPSHOT_SUFFIX}"
        if target.exists():
            target.unlink()
        fact_path = (
            state.root / "artifacts" / "facts" / (state.fact_id.replace("F:", "F-") + ".json")
        )
        command = [
            sys.executable,
            str(state.root / PREPARE_TRANSACTION),
            "--fact",
            str(fact_path),
            "--output",
            str(target),
        ]
        status, output = await asyncio.to_thread(run_prepare, command, state.root)
        state.checker_runs.append(
            {
                # The output path is written as a placeholder, not as the
                # absolute path this run used. A replay writes into a scratch
                # directory, so an absolute path here would make `outcome`
                # diverge on every replay for a reason that carries no meaning.
                # The fact path, which is what the run actually depended on, is
                # recorded exactly.
                "command": (
                    f"python3 {PREPARE_TRANSACTION} --fact "
                    f"{episode_api.repo_relative(fact_path, state.root)} "
                    f"--output <episode-dir>/transaction.proposal.json.snapshot"
                ),
                "exit_status": status,
                "output_sha256": episode_api.sha256_text(output),
                "assurance": "checked",
            }
        )
        if status == 0 and target.is_file():
            state.transaction_path = target
        state.observed = {
            "facts_unlocked": [],
            "operations_widened": [],
            "overlay_links_proposed": [],
        }
        return WriteEpisode()


@dataclass
class Classify(BaseNode[EpisodeState, None, Path]):
    """Deterministic. Which typed obstruction does this decline belong to? NO MODEL.

    Every post-plan decline arrives here -- a gate refusal, a supervisor denial,
    a producer that declined, a re-check that disagreed, a budget that ran out
    mid-dispatch -- and leaves with a cluster key. `Select` and `Plan` still exit
    straight to `WriteEpisode` when a run is cut short before it has a plan: there
    is no typed proposal to read, `decline_class` already carries the whole
    finding, and routing the v1 path through a node the A2 episodes never ran
    would change what a v1 replay re-derives.

    **No model runs here, and the plan drew this node in italics.** The reasons
    are in :mod:`axeyum.agent.classify`; the short form is that the inputs are
    already typed values -- a discriminated `NoGeneralRoute`, a pinned
    `decline_class` enum, a producer's own Rust `DeclineReason` variant -- so
    there is no free text left for a classifier to read, and a model call here
    would put the obstruction graph's cluster keys outside the replay guarantee
    that every deterministic node re-derives bit-identically.

    **This node writes nothing into the episode.** Schema v2 already carries
    every field the classification is a function of, so
    `scripts/gen-obstruction-graph.py` re-derives the identical cluster from the
    committed bytes with the standard library alone. That is the property that
    lets a stdlib gate own the obstruction graph while the classifier lives in
    an optional extra, and `python/tests/test_agent_classify.py` holds the two
    implementations to agreement on every committed episode.
    """

    async def run(self, ctx: GraphRunContext[EpisodeState, None]) -> WriteEpisode:
        state = ctx.state
        state.classification = classify_api.classify(
            decline_class=state.decline_class,
            proposals=state.proposals,
            verdict=state.verdict,
        )
        return WriteEpisode()


@dataclass
class WriteEpisode(BaseNode[EpisodeState, None, Path]):
    """Deterministic. Serialize the run into the one artifact it may produce."""

    async def run(self, ctx: GraphRunContext[EpisodeState, None]) -> End[Path]:
        state = ctx.state
        if state.frontier is None or state.frontier_path is None:
            raise EpisodeWriteError("WriteEpisode reached without a pinned frontier")
        episode_dir = state.out_dir / state.fact_id.split(":", 1)[1]
        messages_path, messages_sha = episode_api.write_transcript(
            state.messages, episode_dir, state.root
        )
        proposal_rows = episode_api.write_proposals(
            state.proposals, episode_dir / "proposals", state.root
        )
        builder = (
            episode_api.build_episode_v2
            if state.schema_version >= episode_api.SCHEMA_VERSION_V2
            else episode_api.build_episode
        )
        extra: dict[str, Any] = (
            {
                "checker_runs": state.checker_runs,
                "axiom_footprint": state.axiom_footprint,
                "observed": state.observed,
            }
            if state.schema_version >= episode_api.SCHEMA_VERSION_V2
            else {}
        )
        document = builder(
            root=state.root,
            commit=state.commit,
            fact_id=state.fact_id,
            frontier=state.frontier,
            frontier_path=state.frontier_path,
            partition=state.partition,
            model_id=state.model_id,
            settings={
                # `top_p` falls back to 1.0 -- the provider default, and the
                # value in effect -- rather than to null, because the schema
                # requires a number and because Anthropic rejects a request
                # carrying BOTH `temperature` and `top_p` (HTTP 400, measured
                # 2026-08-24). What is recorded is the sampling policy that
                # applied, not merely the fields we transmitted.
                "temperature": float(state.settings.get("temperature", 0.0)),
                "top_p": float(state.settings.get("top_p", 1.0)),
                "max_tokens": int(state.settings.get("max_tokens", 8192)),
                "seed": state.settings.get("seed"),
            },
            prompt_hashes=state.prompt_hashes(),
            budgets=state.budgets,
            messages_path=messages_path,
            messages_sha256=messages_sha,
            tool_calls=episode_api.project_tool_calls(state.messages, state.deps.calls),
            proposal_rows=proposal_rows,
            verdict=state.verdict,
            decline_class=state.decline_class,
            # Empty on every episode that did not retrieve, which is all of them
            # by default. The rows are projected from the fetch log rather than
            # rebuilt from the snapshot directory, so a file nobody fetched
            # cannot become a row and a fetch that happened cannot become absent.
            web_snapshots=web_api.web_snapshot_rows(state.deps.web_documents, state.root),
            **extra,
        )
        state.episode_path = episode_api.write_episode(document, state.out_dir, state.root)
        return End(state.episode_path)


def build_graph():
    """The ten-node loop. Every node can short-circuit to a terminal path.

    That every path ends at `WriteEpisode` is the design: a run that was gated,
    denied, declined or cut short still produces the artifact, because "the gate
    refused" and "the loop crashed" are different findings and a harness that
    wrote nothing for the first would be reporting the second. Since slice A5
    every POST-PLAN decline reaches `WriteEpisode` through `Classify`, so the
    typed obstruction is derived while the state that produced it is still in
    hand rather than reconstructed from the artifact afterwards.
    """
    builder: GraphBuilder[EpisodeState, None, Select, Path] = GraphBuilder(
        name="axeyum-frontier-loop",
        state_type=EpisodeState,
        input_type=Select,
        output_type=Path,
    )
    builder.add(builder.edge_from(builder.start_node).to(Select))
    builder.add(
        builder.node(Select),
        builder.node(Gather),
        builder.node(Plan),
        builder.node(Gate),
        builder.node(Dispatch),
        builder.node(Supervise),
        builder.node(Check),
        builder.node(StageTransaction),
        builder.node(Classify),
        builder.node(WriteEpisode),
    )
    return builder.build()


def run_episode(state: EpisodeState) -> Path:
    """Run one episode to completion and return the path of the artifact written."""
    state.root = resolve_root(state.root)
    return build_graph().run_sync(state=state, inputs=Select())


__all__ = [
    "CHECK_COMMAND",
    "DECLINE_BUDGET",
    "DECLINE_GATE",
    "DECLINE_NO_DISPATCH",
    "DECLINE_NO_GENERAL_ROUTE",
    "DECLINE_OPERATIONAL",
    "DECLINE_SUPERVISOR",
    "DISPATCH_PROMPT",
    "GATHER_PROMPT",
    "PLAN_PROMPT",
    "PREPARE_TRANSACTION",
    "Check",
    "Classify",
    "Dispatch",
    "EpisodeState",
    "Gate",
    "Gather",
    "Plan",
    "Select",
    "StageTransaction",
    "Supervise",
    "WriteEpisode",
    "build_agent",
    "build_graph",
    "fact_is_settled",
    "gate_decision",
    "instructions_text",
    "partial_messages",
    "run_episode",
    "run_prepare",
    "supervisor_decision",
    "web_decision",
]
