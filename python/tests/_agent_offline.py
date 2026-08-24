"""One offline episode, shared by the agent test modules.

Offline means `TestModel`: no provider is reached, `policy.model_id` is
`test:offline`, and the plan is supplied by the harness rather than judged by a
model. What is exercised is everything else -- the real tools against the real
ledger, the real graph, the real writer, and the real checker.
"""

from __future__ import annotations

import time
from decimal import Decimal
from pathlib import Path

from pydantic_ai import ModelSettings
from pydantic_ai.usage import RunUsage, UsageLimits

from axeyum.agent.cli import OFFLINE_MODEL_ID, offline_dispatch_model, offline_models
from axeyum.agent.episode import Budgets
from axeyum.agent.graph import EpisodeState, run_episode
from axeyum.agent.tools import AgentDeps, eligible_fact_ids

#: A syntactically valid commit that is not in any history, so the ancestor rule
#: warns (the default) instead of silently matching something real.
TEST_COMMIT = "0" * 40


def offline_state(
    root: Path,
    out_dir: Path,
    fact_id: str | None = None,
    *,
    schema_version: int = 1,
    dispatch_tool: str | None = None,
) -> EpisodeState:
    """One offline episode's state.

    `schema_version` defaults to **1**, the A2 four-node path, because that is
    what the A2 tests assert about and a helper that silently moved them onto
    the A4 loop would change what they measure without changing what they say.
    A4 tests pass `schema_version=2` explicitly.
    """
    fact_id = fact_id or eligible_fact_ids(root)[0]
    gather, plan = offline_models(root, fact_id)
    dispatch = (
        offline_dispatch_model(fact_id, dispatch_tool)
        if dispatch_tool and schema_version >= 2
        else None
    )
    return EpisodeState(
        root=root,
        out_dir=out_dir,
        commit=TEST_COMMIT,
        model=gather,
        plan_model=plan,
        dispatch_model=dispatch,
        schema_version=schema_version,
        model_id=OFFLINE_MODEL_ID,
        budgets=Budgets(600, 8, 12, 400000, 32000, 0.5),
        limits=UsageLimits(
            cost_limit=Decimal("0.50"),
            request_limit=8,
            tool_calls_limit=12,
            input_tokens_limit=400000,
            output_tokens_limit=32000,
        ),
        settings=ModelSettings(temperature=0.0, max_tokens=8192),
        fact_id=fact_id,
        deps=AgentDeps(root=root),
        usage=RunUsage(),
        deadline=time.monotonic() + 600,
    )


def run_offline_episode(root: Path, out_dir: Path, fact_id: str | None = None) -> Path:
    return run_episode(offline_state(root, out_dir, fact_id))


def run_offline_a4_episode(
    root: Path,
    out_dir: Path,
    fact_id: str,
    dispatch_tool: str = "modeq_family",
) -> Path:
    """The full A4 loop offline: gate, deferred dispatch, supervisor, re-check."""
    return run_episode(
        offline_state(root, out_dir, fact_id, schema_version=2, dispatch_tool=dispatch_tool)
    )
