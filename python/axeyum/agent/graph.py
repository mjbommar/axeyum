"""The four-node frontier loop: Select -> Gather -> Plan -> WriteEpisode.

Slice A2 dispatches **nothing**. There is no `Gate`, no `Dispatch`, no `Check`
and no `StageTransaction` in this module, and that is not an omission -- it is
the increment. The two model-driven nodes see only tier-R tools, so the loop is
not merely unauthorized to admit a theorem, it has no tool that could. What it
produces is an episode: a record of what a model looked at and what it proposed,
which slice A4 can put behind an approval gate once the record itself is
trustworthy.

`pydantic_graph.persistence` is **removed in v2**, and this design wants that.
A framework checkpoint is not a referee-auditable artifact: not content
addressed, not diffable, and not checkable by a standard-library gate that never
installs the framework. The episode is the persistence, and
`scripts/check-agent-episode.py` is what reads it.

Two nodes are deterministic and two are not, deliberately:

* `Select` and `WriteEpisode` involve no model. Everything they compute --
  the eligible set, the frontier digest, the partition, the tool-call
  projection, the verdict -- must come out bit-identical on replay, and
  :mod:`axeyum.agent.replay` fails when it does not.
* `Gather` and `Plan` are the model. Their output is recorded, never trusted.

Budget exhaustion is a **verdict**, not an error: a run that hits its cost,
request or wall limit writes an episode saying so, because "the loop stopped
because it ran out of money" and "the loop crashed" are different findings and
a harness that reports them the same way is hiding one of them.
"""

from __future__ import annotations

import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from pydantic_ai import (
    Agent,
    ModelSettings,
    UsageLimitExceeded,
    capture_run_messages,
)
from pydantic_ai.usage import RunUsage, UsageLimits
from pydantic_graph import BaseNode, End, GraphBuilder, GraphRunContext

from ..knowledge import frontier as frontier_api
from ..knowledge._paths import read_json, resolve_root
from . import episode as episode_api
from .episode import Budgets, EpisodeWriteError
from .models import TACTIC_CATALOG, NoGeneralRoute, StrategyProposal
from .models import Plan as PlanOutput
from .tools import AgentDeps, build_toolset, eligible_fact_ids

#: How the episode's `decline_class` names why this run stopped. A2 has exactly
#: three honest reasons and none of them is "the proof failed": nothing was
#: dispatched, so nothing could fail.
DECLINE_NO_DISPATCH = "no-dispatch-authority-in-slice-a2"
DECLINE_NO_GENERAL_ROUTE = "no-general-route"
DECLINE_BUDGET = "budget-exhausted-before-plan"


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
        "WHAT YOU CAN DO. You have six read-only tools and no others. You cannot\n"
        "run a producer, invoke a checker, admit a declaration, or write to the\n"
        "ledger. Nothing you emit is evidence: every proposal you make is recorded\n"
        "with assurance='proposed' and a human or a trusted process decides later.\n"
        "Do not claim a fact is proved, and do not describe your plan as verified.\n"
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

    def out_of_time(self) -> bool:
        return self.deadline > 0 and time.monotonic() > self.deadline

    def prompt_hashes(self) -> dict[str, str]:
        return {
            "instructions": episode_api.sha256_text(instructions_text(self.root)),
            "gather": episode_api.sha256_text(GATHER_PROMPT),
            "plan": episode_api.sha256_text(PLAN_PROMPT),
        }


def build_agent(state: EpisodeState, *, for_plan: bool = False) -> Agent[AgentDeps, str]:
    """One agent, tier-R toolset, standing instructions.

    `retries=3` is what turns a validation failure into feedback: an unknown
    tactic id comes back to the model as the validator's own message, so the
    vocabulary is taught by the schema rather than by the prompt.
    """
    model = state.plan_model if (for_plan and state.plan_model is not None) else state.model
    return Agent(
        model,
        deps_type=AgentDeps,
        toolsets=[build_toolset()],
        instructions=instructions_text(state.root),
        model_settings=state.settings,
        retries=3,
    )


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
        return Gather()


@dataclass
class Gather(BaseNode[EpisodeState, None, Path]):
    """The model, with read tools only. Its job is to look, not to decide."""

    async def run(self, ctx: GraphRunContext[EpisodeState, None]) -> Plan | WriteEpisode:
        state = ctx.state
        if state.out_of_time():
            state.verdict, state.decline_class = "budget-exhausted", DECLINE_BUDGET
            return WriteEpisode()
        agent = build_agent(state)
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

    async def run(self, ctx: GraphRunContext[EpisodeState, None]) -> WriteEpisode:
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
        document = episode_api.build_episode(
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
        )
        state.episode_path = episode_api.write_episode(document, state.out_dir, state.root)
        return End(state.episode_path)


def build_graph():
    """`Select -> Gather -> Plan -> WriteEpisode`, with `Gather` able to short-circuit."""
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
        builder.node(WriteEpisode),
    )
    return builder.build()


def run_episode(state: EpisodeState) -> Path:
    """Run one episode to completion and return the path of the artifact written."""
    state.root = resolve_root(state.root)
    return build_graph().run_sync(state=state, inputs=Select())


__all__ = [
    "DECLINE_BUDGET",
    "DECLINE_NO_DISPATCH",
    "DECLINE_NO_GENERAL_ROUTE",
    "GATHER_PROMPT",
    "PLAN_PROMPT",
    "EpisodeState",
    "Gather",
    "Plan",
    "Select",
    "WriteEpisode",
    "build_agent",
    "build_graph",
    "instructions_text",
    "partial_messages",
    "run_episode",
]
