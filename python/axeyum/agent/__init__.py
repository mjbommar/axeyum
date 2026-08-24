"""The agentic frontier loop (`docs/python-2026-08/03-agentic-layer.md`, slice A2).

An optional extra -- ``pip install axeyum[agent]`` -- and deliberately optional.
Every gate in ``just check`` runs on the standard library, so nothing under
``scripts/`` may import this package; the two worlds meet as JSON on disk, in
the episode artifact, checked by a stdlib-only
``scripts/check-agent-episode.py``.

What this slice ships:

* six **tier-R** tools over :mod:`axeyum.knowledge` and :mod:`axeyum.kernel`,
  with the held-out filter inside the tool rather than in a prompt;
* typed **tier-P** proposals that cannot be constructed with any assurance other
  than ``proposed``, must resolve their tactics and producer in the committed
  vocabulary, and must either name three sibling facts the route reaches or say
  explicitly that there is no general route;
* a four-node graph, ``Select -> Gather -> Plan -> WriteEpisode``, that
  **dispatches nothing** -- there is no C-tier tool here, so the loop is not
  merely unauthorized to admit a theorem, it has no tool that could;
* an **episode** per run, and a replay that fails when a deterministic node
  does not re-derive.

Importing this package requires the extra. The error, if it is missing, names
the extra rather than the transitive dependency that failed.
"""

from __future__ import annotations

try:
    import pydantic_ai as _pydantic_ai  # noqa: F401
except ModuleNotFoundError as _error:  # pragma: no cover - exercised by a fresh env
    raise ModuleNotFoundError(
        "axeyum.agent needs the optional [agent] extra: "
        "`uv sync --extra agent` or `pip install 'axeyum[agent]'`"
    ) from _error

from . import episode, graph, models, replay, tools
from .episode import Budgets, EpisodeWriteError, HeldOutLeak
from .graph import EpisodeState, build_graph, run_episode
from .models import NoGeneralRoute, Plan, StrategyProposal
from .replay import ReplayError, ReplayResult
from .tools import TOOL_TIERS, AgentDeps, build_toolset, eligible_fact_ids

__all__ = [
    "TOOL_TIERS",
    "AgentDeps",
    "Budgets",
    "EpisodeState",
    "EpisodeWriteError",
    "HeldOutLeak",
    "NoGeneralRoute",
    "Plan",
    "ReplayError",
    "ReplayResult",
    "StrategyProposal",
    "build_graph",
    "build_toolset",
    "eligible_fact_ids",
    "episode",
    "graph",
    "models",
    "replay",
    "run_episode",
    "tools",
]
