"""The six tier-R tools: everything the loop is allowed to look at, and nothing else.

Tier R is *read*. No tool here writes a ledger, registers an operation, admits a
declaration, or invokes a checker; the only bytes an R tool causes to be written
are the episode's own record of the call. Tier P (proposals) and tier C
(checking, deferred behind approval) are slices A2+1 and A4 -- they are absent
from this module, so a model running against it is not merely unauthorized to
dispatch, it cannot see a tool that would.

**The held-out filter lives here, not in a prompt.** ``frontier_select`` joins
the nursery partition and drops every ``held-out`` and ``longitudinal`` row
*before returning*, and every other tool runs its outgoing fact ids through the
same filter -- because ``would_unlock``, ``depends_on`` and
``applicability.fact_ids`` are three more paths by which a blind id could reach
a transcript. One capsule registered against one held-out row spent 19 of 76
blind propositions on 2026-08-21; the population is a shared resource with no
owner, and a guard that a prompt can forget is not a guard.

A refusal here never echoes the offending id (see
:func:`axeyum.agent.models.assert_referenceable`): an id in an error message is
an id in the transcript, which is the breach itself.
"""

from __future__ import annotations

import hashlib
import json
import time
from collections.abc import Callable
from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path
from typing import Any, Literal

from pydantic_ai import FunctionToolset, ModelRetry, RunContext

from ..knowledge import facts as facts_api
from ..knowledge import frontier as frontier_api
from ..knowledge import nursery as nursery_api
from ..knowledge import operations as operations_api
from ..knowledge import overlay as overlay_api
from ..knowledge._paths import resolve_root
from .models import (
    ELIGIBLE_PARTITIONS,
    EvidenceView,
    FactView,
    FrontierPage,
    FrontierRow,
    Neighbourhood,
    NeighbourRow,
    OperationRegistryView,
    OperationRow,
    OverlayLinkRow,
    OverlayPage,
    TheoremPage,
    TheoremRow,
    glob_match,
)

#: Assurance tier per tool name, as the episode's ``tool_calls[].assurance``
#: records it. This is the ONLY source for that field: a tool absent from this
#: map is projected as an error rather than defaulted to ``read``, because
#: defaulting is how a tool with side effects comes to be recorded as harmless.
TOOL_TIERS: dict[str, Literal["read", "proposed", "checked"]] = {
    "frontier_select": "read",
    "fact_get": "read",
    "fact_neighbourhood": "read",
    "kernel_theorems": "read",
    "operation_registry": "read",
    "overlay_query": "read",
}

#: The prefix pydantic-ai gives the tools it synthesizes for structured output.
#: A single `output_type` produces `final_result`; a UNION produces one tool per
#: member, named `final_result_StrategyProposal` and `final_result_NoGeneralRoute`
#: -- which is why this is a prefix test and not a fixed set. They are not tools
#: in the tier sense (the model is filling in its own answer, not reading the
#: world) and the transcript projection skips them.
OUTPUT_TOOL_PREFIX = "final_result"


def is_output_tool(name: str) -> bool:
    """Whether a tool name is one pydantic-ai synthesized for structured output.

    Deliberately narrow: exactly `final_result`, or `final_result_` followed by
    an output-type name. A tool called `final_results_cache` is NOT one of these
    and must still declare a tier -- a loose prefix match here would let a real
    tool be recorded as if it had no side effects.
    """
    return name == OUTPUT_TOOL_PREFIX or name.startswith(OUTPUT_TOOL_PREFIX + "_")


#: Kernel preludes ``kernel_theorems`` will build, and the builder for each.
#: ``axreal`` is the AXIOMATIZED ordered field (30 declared axioms, none reached
#: by a shipped route); ``creal`` is the CONSTRUCTED reals, which measure 0.
#: They are different packages and one name is a substring of the other, so they
#: are keyed apart here rather than resolved by a prefix test.
PRELUDES: dict[str, str] = {
    "nat": "build_nat_prelude",
    "int": "build_int_prelude",
    "logic": "build_logic_prelude",
    "rat": "build_rat_prelude",
    "creal": "build_creal_prelude",
    "complex": "build_complex_prelude",
    "axreal": "build_arith_prelude",
}

#: How many rows a single R call may return. A page is a budget, not a summary:
#: the model sees whole typed rows or it sees a stated count of what it did not.
MAX_ROWS = 60


@dataclass
class ToolCallRecord:
    """What the harness measured about one tool call.

    The digests in the episode come from the serialized message list, not from
    here -- a parallel log that could disagree with the transcript is exactly
    the shape this repository keeps finding. What lives here is what the message
    list does not carry: how long the call took and whether it raised.
    """

    tool: str
    tool_call_id: str | None
    duration_ms: int
    exit_status: int


@dataclass
class AgentDeps:
    """Everything a tool needs, and the run's own call log."""

    root: Path
    selected_fact_id: str | None = None
    calls: list[ToolCallRecord] = field(default_factory=list)

    @classmethod
    def for_root(cls, root: Path | str | None = None) -> AgentDeps:
        return cls(root=resolve_root(root))


class ToolRefusal(ModelRetry):
    """A tool declined and the model may pick differently. Never echoes an id."""


def _record(ctx: RunContext[AgentDeps], tool: str, started: float, status: int) -> None:
    ctx.deps.calls.append(
        ToolCallRecord(
            tool=tool,
            tool_call_id=getattr(ctx, "tool_call_id", None),
            duration_ms=max(0, int((time.monotonic() - started) * 1000)),
            exit_status=status,
        )
    )


def _timed(tool: str, ctx: RunContext[AgentDeps], body: Callable[[], Any]) -> Any:
    started = time.monotonic()
    try:
        result = body()
    except Exception:
        _record(ctx, tool, started, 1)
        raise
    _record(ctx, tool, started, 0)
    return result


@lru_cache(maxsize=4)
def _held_out(root_key: str) -> frozenset[str]:
    return nursery_api.load(Path(root_key)).held_out_ids()


def _safe(root: Path, ids) -> tuple[tuple[str, ...], int]:
    """Drop held-out ids from a sequence and say how many were dropped.

    The count is returned rather than swallowed: "nothing was filtered" and
    "three rows were filtered" are different facts about the world, and a tool
    that reports the same output for both is hiding a measurement.
    """
    held = _held_out(str(root))
    kept = tuple(i for i in ids if i not in held)
    return kept, len(tuple(ids)) - len(kept)


# ------------------------------------------------------------------- the tools


def frontier_select(
    ctx: RunContext[AgentDeps],
    band: str = "",
    limit: int = 20,
) -> FrontierPage:
    """List open, dependency-ready facts this loop may work on.

    Held-out and longitudinal rows are removed before this returns, so every id
    you see here is safe to name. Facts the nursery does not preregister are
    also dropped: the episode can only record a train or development partition.

    Args:
        band: Restrict to one frontier band (research, backlog, blocked,
            established) or leave empty for all bands.
        limit: Maximum rows to return, 1 to 60.
    """

    def body() -> FrontierPage:
        root = ctx.deps.root
        live = frontier_api.load(root)
        pen = nursery_api.load(root)
        ready = [e for e in live.entries if e.dependency_ready and e.epistemic_status == "open"]
        held = longitudinal = unpartitioned = 0
        rows: list[FrontierRow] = []
        for entry in ready:
            if not pen.contains(entry.fact_id):
                unpartitioned += 1
                continue
            partition = pen.partition_of(entry.fact_id)
            if partition == nursery_api.HELD_OUT:
                held += 1
                continue
            if partition not in ELIGIBLE_PARTITIONS:
                longitudinal += 1
                continue
            if band and entry.band != band:
                continue
            unlocks, _ = _safe(root, entry.would_unlock)
            rows.append(
                FrontierRow(
                    fact_id=entry.fact_id,
                    partition=partition,  # type: ignore[arg-type]
                    band=entry.band,
                    fragment=entry.fragment,
                    route_class=entry.route_class,
                    epistemic_status=entry.epistemic_status,
                    external_status=entry.external_status,
                    registered_operation_ids=tuple(entry.registered_operation_ids),
                    would_unlock=unlocks,
                )
            )
        capped = max(1, min(int(limit), MAX_ROWS))
        return FrontierPage(
            eligible_total=len(rows),
            returned=min(capped, len(rows)),
            dropped_held_out=held,
            dropped_longitudinal=longitudinal,
            dropped_unpartitioned=unpartitioned,
            frontier_sha256=live.frontier_sha256,
            rows=tuple(rows[:capped]),
        )

    return _timed("frontier_select", ctx, body)


def fact_get(ctx: RunContext[AgentDeps], fact_id: str) -> FactView:
    """Read one fact from the ledger: its statement, status, route and evidence.

    Args:
        fact_id: The fact ledger id, as printed by frontier_select.
    """

    def body() -> FactView:
        root = ctx.deps.root
        if fact_id in _held_out(str(root)):
            raise ToolRefusal(
                "that fact is in the blind held-out population and is not available to this "
                "loop; choose a row that frontier_select returned"
            )
        try:
            fact = facts_api.load(root).get(fact_id)
        except KeyError:
            raise ToolRefusal(
                "no such fact in the ledger; call frontier_select and copy an id from it"
            ) from None
        pen = nursery_api.load(root)
        deps, _ = _safe(root, fact.depends_on)
        return FactView(
            fact_id=fact.id,
            title=fact.title,
            statement=fact.statement,
            formal_language=fact.formal.language,
            formal_statement=fact.formal.statement,
            fragment=fact.formal.fragment,
            epistemic_status=fact.epistemic_status,
            external_status=fact.external_status,
            proof_route=fact.proof_route,
            depends_on=deps,
            axiom_footprint=tuple(fact.axiom_footprint) if fact.axiom_footprint else None,
            evidence=tuple(
                EvidenceView(
                    kind=e.kind, check_status=e.check_status, checker_command=e.checker_command
                )
                for e in fact.evidence
            ),
            partition=pen.partition_of(fact_id) if pen.contains(fact_id) else None,
            notes=fact.notes,
        )

    return _timed("fact_get", ctx, body)


def fact_neighbourhood(ctx: RunContext[AgentDeps], fact_id: str) -> Neighbourhood:
    """What a fact rests on (depends_on) and what closing it would free (would_unlock).

    Args:
        fact_id: The fact ledger id to centre the neighbourhood on.
    """

    def body() -> Neighbourhood:
        root = ctx.deps.root
        if fact_id in _held_out(str(root)):
            raise ToolRefusal(
                "that fact is in the blind held-out population and is not available to this loop"
            )
        ledger = facts_api.load(root)
        try:
            fact = ledger.get(fact_id)
        except KeyError:
            raise ToolRefusal("no such fact in the ledger") from None

        def row(other_id: str) -> NeighbourRow:
            try:
                other = ledger.get(other_id)
            except KeyError:
                return NeighbourRow(fact_id=other_id, epistemic_status=None, settled=False)
            return NeighbourRow(
                fact_id=other_id,
                epistemic_status=other.epistemic_status,
                settled=other.is_settled,
            )

        depends, _ = _safe(root, fact.depends_on)
        unlocks, _ = _safe(root, [f.id for f in ledger if fact_id in f.depends_on])
        depends_rows = tuple(row(d) for d in depends)
        return Neighbourhood(
            fact_id=fact_id,
            depends_on=depends_rows,
            would_unlock=tuple(row(u) for u in unlocks),
            unmet_dependencies=tuple(r.fact_id for r in depends_rows if not r.settled),
        )

    return _timed("fact_neighbourhood", ctx, body)


@lru_cache(maxsize=len(PRELUDES))
def _kernel_for(prelude: str) -> Any:
    """One kernel per prelude, built once per process.

    Handles are lifetime-free indices into the kernel that interned them, so the
    cache is per prelude and never shared across them; nothing here hands a
    handle out.
    """
    from ..kernel import Kernel

    kernel = Kernel()
    getattr(kernel, PRELUDES[prelude])()
    return kernel


def kernel_theorems(
    ctx: RunContext[AgentDeps],
    prelude: str = "nat",
    name_glob: str = "",
) -> TheoremPage:
    """Search a kernel prelude's proved theorems by name -- the premise corpus.

    Every row is a theorem this kernel has admitted, with its canonical type.
    An empty result for a non-empty glob is a FAILED lookup, not a report that
    the prelude is empty: `total_theorems` tells you which one it was.

    Args:
        prelude: One of nat, int, logic, rat, creal, complex, axreal. `axreal`
            is the axiomatized ordered field; `creal` is the constructed reals.
        name_glob: A shell-style glob over the theorem name, e.g. "Nat.add_*".
            Empty means every theorem.
    """

    def body() -> TheoremPage:
        if prelude not in PRELUDES:
            raise ToolRefusal(f"unknown prelude {prelude!r}; this kernel builds {sorted(PRELUDES)}")
        kernel = _kernel_for(prelude)
        total = 0
        rows: list[TheoremRow] = []
        for name, declaration in kernel.declarations():
            if declaration.kind != "theorem":
                continue
            total += 1
            if not glob_match(name, name_glob):
                continue
            rendered = kernel.render_lean(declaration.ty)
            rows.append(TheoremRow(name=name, binders=rendered.count("->"), type=rendered))
        rows.sort(key=lambda r: r.name)
        return TheoremPage(
            prelude=prelude,
            name_glob=name_glob,
            matched=len(rows),
            total_theorems=total,
            rows=tuple(rows[:MAX_ROWS]),
        )

    return _timed("kernel_theorems", ctx, body)


def operation_registry(ctx: RunContext[AgentDeps], fact_id: str = "") -> OperationRegistryView:
    """The registered operations, each with how many facts it names.

    `n_targets == 1` means the entry is a dispatch table row, not a producer:
    it can never fail to "produce" because it was written for one theorem. Read
    `multi_target` against `total` before proposing a producer.

    Args:
        fact_id: Restrict to operations naming this fact, or leave empty for all.
    """

    def body() -> OperationRegistryView:
        root = ctx.deps.root
        registry = operations_api.load(root)
        selected = [op for op in registry if not fact_id or op.targets(fact_id)]
        rows: list[OperationRow] = []
        for op in selected:
            ids, _ = _safe(root, op.applicability.fact_ids)
            rows.append(
                OperationRow(
                    operation_id=op.id,
                    scope=op.scope,
                    n_targets=op.n_targets,
                    fact_ids=ids,
                    producer=op.producer.implementation or op.producer.operation,
                    checker=op.checker.implementation or op.checker.operation,
                    driver=op.executor.driver,
                )
            )
        rows.sort(key=lambda r: r.operation_id)
        return OperationRegistryView(
            total=len(registry),
            multi_target=sum(1 for op in registry if op.is_multi_target),
            single_target=sum(1 for op in registry if op.n_targets == 1),
            rows=tuple(rows[:MAX_ROWS]),
        )

    return _timed("operation_registry", ctx, body)


def overlay_query(
    ctx: RunContext[AgentDeps],
    relation: str = "",
    endpoint_id: str = "",
) -> OverlayPage:
    """Query the typed knowledge overlay: which concepts and techniques a thing links to.

    Every link carries its `assurance` unchanged. `heuristic` and `proposed`
    links are opinions; `formal-derived` and `independently-checked` are not.

    Args:
        relation: A relation type id, or empty for all relations.
        endpoint_id: Match links touching this endpoint id, or empty for all.
    """

    def body() -> OverlayPage:
        root = ctx.deps.root
        graph = overlay_api.load(root)
        held = _held_out(str(root))
        matched = graph.query(relation or None, endpoint_id or None)
        rows = [
            OverlayLinkRow(
                link_id=link.id,
                relation=link.relation,
                source=link.source.id,
                target=link.target.id,
                assurance=link.assurance,
                status=link.status,
                reason=link.reason,
            )
            for link in matched
            if link.source.id not in held and link.target.id not in held
        ]
        rows.sort(key=lambda r: r.link_id)
        return OverlayPage(
            relation=relation or None,
            endpoint_id=endpoint_id or None,
            matched=len(rows),
            total_links=len(graph.links),
            rows=tuple(rows[:MAX_ROWS]),
        )

    return _timed("overlay_query", ctx, body)


TIER_R_TOOLS: tuple[Callable[..., Any], ...] = (
    frontier_select,
    fact_get,
    fact_neighbourhood,
    kernel_theorems,
    operation_registry,
    overlay_query,
)


def build_toolset() -> FunctionToolset[AgentDeps]:
    """The tier-R toolset, and nothing else.

    ``sequential=True`` is not a performance choice: it makes the execution
    order of tool calls equal to their order in the message list, which is what
    lets the episode's ``tool_calls`` projection line durations up with the
    digests it takes from the transcript.

    ``require_parameter_descriptions=True`` makes an undocumented parameter a
    build-time failure rather than an underspecified schema the model has to
    guess at.
    """
    toolset: FunctionToolset[AgentDeps] = FunctionToolset(
        max_retries=2,
        sequential=True,
        require_parameter_descriptions=True,
    )
    for function in TIER_R_TOOLS:
        toolset.add_function(function)
    return toolset


def toolset_fingerprint() -> dict[str, Any]:
    """A canonical description of the tool surface the model was shown.

    Digested into ``policy.toolset_sha256``. It covers the name, the declared
    tier and the documented signature of every tool, so widening a tool -- or
    adding one -- changes the episode's policy digest and a replay against the
    old episode is visibly against a different agent.
    """
    import inspect

    return {
        name: {
            "assurance": TOOL_TIERS[name],
            "signature": str(inspect.signature(function)),
            "doc_sha256": hashlib.sha256(
                (inspect.getdoc(function) or "").encode("utf-8")
            ).hexdigest(),
        }
        for name, function in ((f.__name__, f) for f in TIER_R_TOOLS)
    }


def toolset_sha256() -> str:
    payload = json.dumps(toolset_fingerprint(), sort_keys=True, ensure_ascii=True)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def eligible_fact_ids(root: Path | str | None = None) -> tuple[str, ...]:
    """The eligible population, computed WITHOUT the agent, for cross-checking.

    ``frontier_select`` must agree with this. Two implementations of the same
    filter is normally a smell; here it is the point -- the tests assert the
    tool's output equals this independent computation, so a filter that silently
    stopped filtering would have to break both at once.
    """
    resolved = resolve_root(root)
    live = frontier_api.load(resolved)
    pen = nursery_api.load(resolved)
    return tuple(
        entry.fact_id
        for entry in live.entries
        if entry.dependency_ready
        and entry.epistemic_status == "open"
        and pen.contains(entry.fact_id)
        and pen.partition_of(entry.fact_id) in ELIGIBLE_PARTITIONS
    )


__all__ = [
    "MAX_ROWS",
    "OUTPUT_TOOL_PREFIX",
    "PRELUDES",
    "TIER_R_TOOLS",
    "TOOL_TIERS",
    "AgentDeps",
    "ToolCallRecord",
    "ToolRefusal",
    "build_toolset",
    "eligible_fact_ids",
    "fact_get",
    "fact_neighbourhood",
    "frontier_select",
    "is_output_tool",
    "kernel_theorems",
    "operation_registry",
    "overlay_query",
    "toolset_fingerprint",
    "toolset_sha256",
]
