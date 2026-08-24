"""Replay an episode against its own transcript, and fail when the loop drifts.

**Replayable, not reproducible.** `ModelSettings.seed` exists and the provider
documentation itself hedges that even `temperature=0.0` is not deterministic, so
promising a bit-identical model response would be a promise we cannot keep. What
IS promised is narrower and checkable: with the recorded responses replayed in
order, every *deterministic* node must re-derive the same thing. Divergence is a
finding, not a warning.

The guard that makes this real is `models.ALLOW_MODEL_REQUESTS = False`. It is a
library-level kill switch, so a replay that accidentally reached a provider
raises instead of quietly costing money and producing a different episode.

What is compared, and why the exit status depends on it:

* `selection` -- the frontier digest, the fact, its digest, the partition and
  the eligibility reason. These come from `Select`, which runs no model. If they
  move, either the ledger moved under the episode or the filter changed; both
  are things a referee needs told.
* `outcome` -- verdict, decline class, and the three receipt counters including
  `ledger_writes`. If a replay of a `declined` episode produces anything else,
  the episode was not a record of what happened.

`selection.frontier_path` is compared by BASENAME. The replay writes into a
scratch directory, so the absolute path necessarily differs; the digest, which
is the part that carries meaning, is compared in full.

Tool-call digests are reported but do NOT gate the exit status: the tools read a
live ledger, so a fact added by another lane legitimately changes a result hash
without anything about the episode being wrong. The line is printed either way,
because an unreported difference is the one nobody investigates.
"""

from __future__ import annotations

import json
import tempfile
from collections.abc import Iterator
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from pydantic_ai import ModelSettings, models
from pydantic_ai.messages import ModelMessagesTypeAdapter, ModelResponse
from pydantic_ai.models.function import AgentInfo, FunctionModel
from pydantic_ai.usage import UsageLimits

from ..knowledge._paths import resolve_root
from .episode import Budgets, EpisodeWriteError
from .graph import EpisodeState, run_episode
from .tools import AgentDeps

#: Blocks in the episode whose re-derivation gates the exit status.
DETERMINISTIC_BLOCKS = ("selection", "outcome")


class ReplayError(RuntimeError):
    """The replay could not be performed. Distinct from a replay that diverged.

    Fail-closed: neither is reported as success, but they are different findings
    and collapsing them would let "the transcript was missing" read as "the loop
    is deterministic".
    """


class TranscriptExhausted(ReplayError):
    """The replayed graph asked for more model responses than were recorded."""


@dataclass(frozen=True)
class ReplayResult:
    """What the replay found. `ok` is derived, never asserted."""

    episode_path: Path
    replayed_path: Path
    diverged: tuple[str, ...]
    tool_calls_match: bool
    recorded_responses: int
    consumed_responses: int

    @property
    def ok(self) -> bool:
        return not self.diverged

    def line(self) -> str:
        return (
            f"EPISODE_REPLAY|path={self.episode_path}"
            f"|status={'OK' if self.ok else 'DIVERGED'}"
            f"|blocks={','.join(self.diverged) if self.diverged else ''}"
            f"|tool_calls={'match' if self.tool_calls_match else 'differ'}"
            f"|responses={self.consumed_responses}/{self.recorded_responses}"
        )


def recorded_responses(messages: list[Any]) -> list[ModelResponse]:
    """Every model response in the transcript, in order."""
    return [m for m in messages if isinstance(m, ModelResponse)]


def transcript_model(responses: list[ModelResponse]) -> FunctionModel:
    """A model that returns the recorded responses in order and nothing else.

    Running past the end raises :class:`TranscriptExhausted` rather than
    inventing a response: a replay that quietly generated new content would
    compare a different run against the episode and call the match meaningful.
    """
    stream: Iterator[ModelResponse] = iter(responses)
    consumed: list[int] = [0]

    def respond(messages: list[Any], info: AgentInfo) -> ModelResponse:
        try:
            response = next(stream)
        except StopIteration:
            raise TranscriptExhausted(
                f"the graph requested response {consumed[0] + 1} but the transcript "
                f"records {len(responses)}; the loop asked for more than it did"
            ) from None
        consumed[0] += 1
        return response

    model = FunctionModel(respond, model_name="replay")
    model._axeyum_consumed = consumed
    return model


def _comparable_selection(selection: dict[str, Any]) -> dict[str, Any]:
    out = dict(selection)
    path = out.get("frontier_path")
    if isinstance(path, str):
        out["frontier_path"] = Path(path).name
    return out


def compare(original: dict[str, Any], replayed: dict[str, Any]) -> tuple[str, ...]:
    """Blocks that did not re-derive. Empty means every deterministic node agreed."""
    diverged: list[str] = []
    for block in DETERMINISTIC_BLOCKS:
        left, right = original.get(block), replayed.get(block)
        if block == "selection":
            left = _comparable_selection(left or {})
            right = _comparable_selection(right or {})
        if left != right:
            diverged.append(block)
    return tuple(diverged)


def _tool_call_shape(document: dict[str, Any]) -> list[tuple[Any, ...]]:
    calls = (document.get("transcript") or {}).get("tool_calls") or []
    return [
        (
            c.get("ordinal"),
            c.get("tool"),
            c.get("args_sha256"),
            c.get("result_sha256"),
            c.get("assurance"),
            c.get("exit_status"),
        )
        for c in calls
    ]


def replay(
    episode_path: Path | str,
    root: Path | str | None = None,
    out_dir: Path | str | None = None,
) -> ReplayResult:
    """Re-run the graph from a recorded transcript and compare the deterministic blocks."""
    resolved_root = resolve_root(root)
    episode_path = Path(episode_path)
    try:
        document = json.loads(episode_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ReplayError(f"{episode_path} is unreadable: {error}") from error
    if document.get("kind") != "axeyum-agent-episode":
        raise ReplayError(f"{episode_path} is not an episode: kind={document.get('kind')!r}")

    transcript = document.get("transcript") or {}
    messages_path = resolved_root / str(transcript.get("messages_path", ""))
    if not messages_path.is_file():
        raise ReplayError(
            f"the transcript {transcript.get('messages_path')!r} is not on disk; "
            f"an episode without its messages cannot be replayed"
        )
    messages = list(ModelMessagesTypeAdapter.validate_json(messages_path.read_bytes()))
    responses = recorded_responses(messages)
    if not responses:
        raise ReplayError("the transcript records no model responses; nothing to replay")

    selection = document.get("selection") or {}
    policy = document.get("policy") or {}
    budgets_doc = document.get("budgets") or {}
    fact_id = selection.get("fact_id")
    if not isinstance(fact_id, str):
        raise ReplayError("the episode names no fact to re-select")

    model = transcript_model(responses)
    settings_doc = policy.get("settings") or {}
    settings = ModelSettings(
        temperature=float(settings_doc.get("temperature", 0.0)),
        top_p=float(settings_doc.get("top_p", 1.0)),
        max_tokens=int(settings_doc.get("max_tokens", 8192)),
    )
    budgets = Budgets(
        wall_seconds=int(budgets_doc.get("wall_seconds", 600)),
        request_limit=int(budgets_doc.get("request_limit", 8)),
        tool_calls_limit=int(budgets_doc.get("tool_calls_limit", 12)),
        input_tokens_limit=int(budgets_doc.get("input_tokens_limit", 400000)),
        output_tokens_limit=int(budgets_doc.get("output_tokens_limit", 32000)),
        cost_limit_usd=float(budgets_doc.get("cost_limit_usd", 0.0)),
    )

    previous = models.ALLOW_MODEL_REQUESTS
    models.ALLOW_MODEL_REQUESTS = False
    temporary: tempfile.TemporaryDirectory[str] | None = None
    try:
        if out_dir is None:
            temporary = tempfile.TemporaryDirectory(prefix="axeyum-replay-")
            target = Path(temporary.name)
        else:
            target = Path(out_dir)
        state = EpisodeState(
            root=resolved_root,
            out_dir=target,
            commit=str(document.get("git_commit", "")),
            model=model,
            model_id=str(policy.get("model_id", "test:replay")),
            budgets=budgets,
            # The RECORDED request and tool-call limits, exactly. Relaxing them
            # made every budget-exhausted episode unreplayable: the loop ran past
            # the point it originally stopped and asked for a response the
            # transcript does not have. Both counters are provider-independent,
            # so replaying them is meaningful.
            #
            # The token and cost limits are deliberately NOT replayed. A
            # `FunctionModel` reports different token counts and no cost at all,
            # so re-imposing them would compare the run against a budget it never
            # had -- firing early, or silently not at all.
            limits=UsageLimits(
                request_limit=budgets.request_limit,
                tool_calls_limit=budgets.tool_calls_limit,
            ),
            settings=settings,
            fact_id=fact_id,
            deps=AgentDeps(root=resolved_root),
            deadline=0.0,
        )
        try:
            replayed_path = run_episode(state)
        except EpisodeWriteError as error:
            raise ReplayError(f"the replayed run could not write an episode: {error}") from error
        replayed = json.loads(replayed_path.read_text(encoding="utf-8"))
        result = ReplayResult(
            episode_path=episode_path,
            replayed_path=replayed_path,
            diverged=compare(document, replayed),
            tool_calls_match=_tool_call_shape(document) == _tool_call_shape(replayed),
            recorded_responses=len(responses),
            consumed_responses=model._axeyum_consumed[0],
        )
        if temporary is not None:
            # Read everything needed before the scratch directory disappears.
            temporary.cleanup()
            temporary = None
        return result
    finally:
        models.ALLOW_MODEL_REQUESTS = previous
        if temporary is not None:
            temporary.cleanup()


__all__ = [
    "DETERMINISTIC_BLOCKS",
    "ReplayError",
    "ReplayResult",
    "TranscriptExhausted",
    "compare",
    "recorded_responses",
    "replay",
    "transcript_model",
]
