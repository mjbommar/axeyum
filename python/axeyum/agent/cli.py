"""`python -m axeyum.agent` -- run episodes, replay one, or re-check one.

Four commands, and the split between them is the trust boundary:

    python -m axeyum.agent run     --next --n 10 --model anthropic:claude-sonnet-4-5
    python -m axeyum.agent run     --fact F:... --offline
    python -m axeyum.agent replay  --from-transcript artifacts/episodes/.../episode-....json
    python -m axeyum.agent check   --fact F:... --producer modeq_family \
                                   --expect-proof-sha256 <64 hex>

`run` produces episodes. Since slice A4 it can dispatch, but only through a
deferred tool a deterministic supervisor approves, and it still cannot admit a
fact or write the ledger: `apply-autogenesis-fact-transaction.py` is not
reachable from this package. `replay` produces no artifact; its output is an
exit status that depends on whether the deterministic nodes re-derived.

`check` is the command an episode's `outcome.checker_runs[0].command` names, and
it exists so that field is a thing a referee can run rather than a string. It
builds a SECOND kernel from the same frozen export, re-runs the producer,
re-renders the proof term and compares the digest against the one it was given.
It exits 0 only when they match; a mismatch, a missing export and an absent
producer route are three distinct nonzero findings, never one.

`--offline` swaps the provider for `TestModel`, which is what the test suite
and a machine with no API key use. An offline episode says so in its own
`policy.model_id` (`test:offline`), because an episode that hid which model
produced it would be worse than no episode: every downstream measurement --
cost per decline, route quality, obstruction clusters -- is conditioned on it.
"""

from __future__ import annotations

import argparse
import os
import sys
import time
from decimal import Decimal
from pathlib import Path
from typing import Any

from pydantic_ai import ModelSettings
from pydantic_ai.usage import RunUsage, UsageLimits

from ..knowledge._paths import resolve_root
from . import episode as episode_api
from . import mobility as mobility_api
from .episode import Budgets
from .graph import EpisodeState, run_episode
from .models import set_vocabulary_root
from .replay import ReplayError, replay
from .tools import PRODUCER_TOOLS, AgentDeps, eligible_fact_ids, independent_check

#: The offline stand-in's model id. It is a real id shape (provider-prefixed, as
#: v2 requires) that resolves to no provider, so it cannot be mistaken for a run
#: that cost money.
OFFLINE_MODEL_ID = "test:offline"

#: Tools `TestModel` is allowed to call offline. Every one of them answers a
#: call with defaulted or nonsense arguments without refusing, so an offline run
#: exercises the real tool bodies instead of a chain of retries. `fact_get`,
#: `fact_neighbourhood` and `kernel_theorems` are excluded for the opposite
#: reason: they REFUSE an unknown id or prelude, which is correct behaviour and
#: makes them useless to a model that invents its arguments.
OFFLINE_TOOLS = ["frontier_select", "operation_registry", "overlay_query"]


def offline_dispatch_model(fact_id: str, tool: str) -> Any:
    """A model that calls exactly one tier-C tool with exactly one argument.

    `TestModel` cannot do this: it invents arguments from the JSON schema, so a
    `fact_id: str` comes back as `"a"` and the supervisor correctly denies the
    call for targeting a fact other than the selected one. That is a real
    outcome and a useless demonstration, so the offline dispatch is a
    `FunctionModel` that emits the call the loop is actually asking for -- and
    the approval gate in front of it is untouched, which is the whole point:
    even a model that asks perfectly still cannot run the tool.
    """
    from pydantic_ai.messages import ModelResponse, TextPart, ToolCallPart
    from pydantic_ai.models.function import AgentInfo, FunctionModel

    state = {"called": False}

    def respond(messages: list[Any], info: AgentInfo) -> ModelResponse:
        if state["called"]:
            return ModelResponse(parts=[TextPart(content="offline stand-in: tool call resolved")])
        state["called"] = True
        return ModelResponse(
            parts=[
                ToolCallPart(
                    tool_name=tool,
                    args={"fact_id": fact_id},
                    tool_call_id=f"offline-{tool}-0",
                )
            ]
        )

    return FunctionModel(respond, model_name="offline-dispatch")


def offline_models(root: Path, fact_id: str) -> tuple[Any, Any]:
    """`(gather model, plan model)` -- `TestModel`, primed to resolve in the vocabulary.

    The plan is constructed here rather than generated from the schema because a
    schema-generated `tactic_ids` is `["a"]`, which the validator correctly
    rejects -- an offline run would then measure the retry loop rather than the
    graph. What it must never do is look like a model's judgement: the episode
    records `test:offline`, and nothing downstream should read an offline plan
    as a proposal anyone made.
    """
    from pydantic_ai.models.test import TestModel

    siblings = [f for f in eligible_fact_ids(root) if f != fact_id][:3]
    if len(siblings) < 3:
        raise SystemExit(
            "fewer than three other eligible facts exist; an offline StrategyProposal "
            "cannot be built without inventing siblings, and inventing them is the "
            "one thing this schema exists to prevent"
        )
    gather = TestModel(call_tools=OFFLINE_TOOLS)
    plan = TestModel(
        call_tools=[],
        custom_output_args={
            "route": "general",
            "fact_id": fact_id,
            "tactic_ids": ["T:refl-closure"],
            "producer_id": "close_terminal",
            "why": "offline stand-in: no model judged this goal; TestModel supplied the plan",
            "expected_decline_class": "TerminalNotDefEqNoRewrite",
            "sibling_fact_ids": siblings,
            "assurance": "proposed",
        },
    )
    return gather, plan


def pick_facts(root: Path, requested: list[str], take_next: int) -> list[str]:
    """The facts to run, refusing anything outside the eligible population."""
    eligible = eligible_fact_ids(root)
    if requested:
        unknown = [f for f in requested if f not in eligible]
        if unknown:
            raise SystemExit(
                f"{len(unknown)} requested fact(s) are not eligible (open, dependency-ready, "
                f"train or development); the population has {len(eligible)} members"
            )
        return requested
    if take_next <= 0:
        raise SystemExit("pass --fact or --next --n N")
    return list(eligible[:take_next])


def run_command(args: argparse.Namespace) -> int:
    root = resolve_root(args.root)
    set_vocabulary_root(root)
    out_dir = Path(args.out)
    if not out_dir.is_absolute():
        out_dir = root / out_dir
    commit = episode_api.git_commit(root, args.git_commit or os.environ.get("AXEYUM_GIT_COMMIT"))
    facts = pick_facts(root, args.fact, args.n if args.next else 0)

    budgets = Budgets(
        wall_seconds=args.wall_seconds,
        request_limit=args.request_limit,
        tool_calls_limit=args.tool_calls_limit,
        input_tokens_limit=args.input_tokens_limit,
        output_tokens_limit=args.output_tokens_limit,
        cost_limit_usd=args.budget_usd,
    )
    # `temperature` ONLY. Measured 2026-08-24 against claude-sonnet-4-5: sending
    # both knobs is HTTP 400, "`temperature` and `top_p` cannot both be specified
    # for this model". The episode still records `top_p` -- the schema requires a
    # number -- as the provider default 1.0, which is the value in effect when
    # nucleus sampling is not requested. See the note in `graph.WriteEpisode`.
    settings = ModelSettings(temperature=0.0, max_tokens=args.max_tokens)

    failures = 0
    for fact_id in facts:
        model, plan_model = offline_models(root, fact_id) if args.offline else (args.model, None)
        dispatch_model = (
            offline_dispatch_model(fact_id, PRODUCER_TOOLS["close_terminal"])
            if args.offline
            else None
        )
        model_id = OFFLINE_MODEL_ID if args.offline else args.model
        usage = RunUsage()
        state = EpisodeState(
            root=root,
            out_dir=out_dir,
            commit=commit,
            model=model,
            plan_model=plan_model,
            dispatch_model=dispatch_model,
            model_id=model_id,
            schema_version=args.schema_version,
            budgets=budgets,
            limits=UsageLimits(
                cost_limit=Decimal(str(args.budget_usd)),
                request_limit=args.request_limit,
                tool_calls_limit=args.tool_calls_limit,
                input_tokens_limit=args.input_tokens_limit,
                output_tokens_limit=args.output_tokens_limit,
            ),
            settings=settings,
            fact_id=fact_id,
            deps=AgentDeps(root=root),
            usage=usage,
            deadline=time.monotonic() + args.wall_seconds,
        )
        try:
            path = run_episode(state)
        except Exception as error:  # noqa: BLE001 - reported per fact, never swallowed
            failures += 1
            print(
                f"AGENT_EPISODE|fact={fact_id}|status=ERROR|{type(error).__name__}: {error}",
                file=sys.stderr,
            )
            continue
        route = state.proposals[0].route if state.proposals else "none-emitted"
        # `RunUsage.cost` is an ATTRIBUTE the run fills in, not a method. Calling
        # it raises `TypeError: 'NoneType' object is not callable` when pricing
        # was unavailable -- which a bare `except` then reports as "cost 0", the
        # same output an unpriced run gives. Read it, and say plainly when the
        # cost limit could not be enforced: pydantic-ai emits
        # `CostNotFoundWarning` in that case and a budget that cannot fire is
        # decoration, so it must not pass silently.
        cost = getattr(usage, "cost", None)
        print(
            f"AGENT_EPISODE|path={episode_api.repo_relative(path, root)}|fact={fact_id}"
            f"|verdict={state.verdict}|decline_class={state.decline_class}|route={route}"
            f"|requests={usage.requests}|tool_calls={usage.tool_calls}"
            f"|input_tokens={usage.input_tokens}|output_tokens={usage.output_tokens}"
            f"|cost_usd={'unpriced' if cost is None else f'{float(cost):.6f}'}"
            f"|cost_limit_enforced={'false' if cost is None else 'true'}"
        )
    print(
        f"AGENT_EPISODES|requested={len(facts)}|written={len(facts) - failures}|failed={failures}"
    )
    if not facts:
        print(
            "axeyum.agent run: no facts were run; a run that ran nothing is not a pass",
            file=sys.stderr,
        )
        return 1
    return 1 if failures else 0


def replay_command(args: argparse.Namespace) -> int:
    root = resolve_root(args.root)
    set_vocabulary_root(root)
    try:
        result = replay(args.from_transcript, root=root)
    except ReplayError as error:
        print(f"EPISODE_REPLAY|path={args.from_transcript}|status=ERROR|{error}", file=sys.stderr)
        return 2
    print(result.line())
    return 0 if result.ok else 1


def check_command(args: argparse.Namespace) -> int:
    """Re-derive a proof in a fresh kernel and compare. Exit status IS the finding.

    Nothing here reads the episode that named it. The command carries the fact,
    the producer and the expected digest, so this re-derives from the frozen
    export and the committed resolution records alone -- a checker that read its
    expected answer out of the artifact it is checking would agree with it by
    construction.
    """
    root = resolve_root(args.root)
    if args.producer not in set(PRODUCER_TOOLS.values()):
        print(
            f"EPISODE_CHECK|fact={args.fact}|status=ERROR|no such producer route: "
            f"{args.producer!r}; this loop runs {sorted(set(PRODUCER_TOOLS.values()))}",
            file=sys.stderr,
        )
        return 2
    outcome = independent_check(root, args.fact, args.producer, args.expect_proof_sha256)
    verified = outcome.status == "verified"
    footprint = ",".join(getattr(outcome, "axiom_footprint", ()) or ())
    print(
        f"EPISODE_CHECK|fact={args.fact}|producer={args.producer}"
        f"|status={'VERIFIED' if verified else 'FAILED'}"
        f"|proof_sha256={getattr(outcome, 'proof_sha256', '')}"
        f"|expected={args.expect_proof_sha256}"
        f"|axiom_footprint={footprint or 'empty'}"
        f"|axiom_free={'true' if verified and not footprint else 'false'}"
    )
    if not verified:
        print(f"  {outcome.reason}", file=sys.stderr)
        return 1
    if footprint:
        print(
            "  the re-derived declaration is NOT axiom-free; an admitted theorem "
            "resting on assumptions is a different claim",
            file=sys.stderr,
        )
        return 1
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="python -m axeyum.agent",
        description="Run or replay one turn of the agentic frontier loop.",
    )
    parser.add_argument("--root", default=None, help="repository root (default: auto-discover)")
    sub = parser.add_subparsers(dest="command", required=True)

    run = sub.add_parser("run", help="run episodes over eligible facts")
    run.add_argument("--fact", action="append", default=[], help="fact id (repeatable)")
    run.add_argument("--next", action="store_true", help="take the next --n eligible facts")
    run.add_argument("--n", type=int, default=1, help="how many facts --next takes")
    run.add_argument(
        "--model",
        default="anthropic:claude-sonnet-4-5",
        help="provider-prefixed model id; v2 rejects a bare name",
    )
    run.add_argument(
        "--offline",
        action="store_true",
        help="use TestModel; the episode records model_id test:offline",
    )
    run.add_argument(
        "--out",
        default="artifacts/episodes",
        help="directory the episodes and their snapshots are written to",
    )
    run.add_argument(
        "--git-commit",
        default=None,
        help="40-hex commit; required where there is no .git (a lane snapshot)",
    )
    run.add_argument("--budget-usd", type=float, default=0.50)
    run.add_argument("--wall-seconds", type=int, default=600)
    run.add_argument("--request-limit", type=int, default=8)
    run.add_argument("--tool-calls-limit", type=int, default=12)
    run.add_argument("--input-tokens-limit", type=int, default=400000)
    run.add_argument("--output-tokens-limit", type=int, default=32000)
    run.add_argument("--max-tokens", type=int, default=8192)
    run.add_argument(
        "--schema-version",
        type=int,
        default=2,
        choices=(1, 2),
        help="2 runs the full A4 loop; 1 runs the A2 four-node path and writes a v1 episode",
    )
    run.set_defaults(handler=run_command)

    replay_parser = sub.add_parser("replay", help="re-run an episode from its own transcript")
    replay_parser.add_argument("--from-transcript", required=True, help="path to an episode JSON")
    replay_parser.set_defaults(handler=replay_command)

    check_parser = sub.add_parser(
        "check", help="re-derive a proof in a second kernel and compare its digest"
    )
    check_parser.add_argument("--fact", required=True, help="the fact whose goal to re-close")
    check_parser.add_argument("--producer", required=True, help="bounded_induction or modeq_family")
    check_parser.add_argument(
        "--expect-proof-sha256",
        required=True,
        help="the sha256 of render_lean(proof) this must reproduce",
    )
    check_parser.set_defaults(handler=check_command)

    # A7: the mobility census. It runs no producer and calls no model, so it
    # lives beside `run`/`replay`/`check` rather than inside them: what it
    # measures is the vocabulary's structural reach, which is a property of the
    # catalog and the ledger and not of any episode.
    mobility_api.add_parser(sub)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    return int(args.handler(args))


__all__ = [
    "OFFLINE_MODEL_ID",
    "OFFLINE_TOOLS",
    "build_parser",
    "check_command",
    "main",
    "offline_dispatch_model",
    "offline_models",
    "pick_facts",
    "replay_command",
    "run_command",
]
