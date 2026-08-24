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
from typing import Any, Literal, NamedTuple

from pydantic_ai import FunctionToolset, ModelRetry, RunContext

from ..knowledge import facts as facts_api
from ..knowledge import frontier as frontier_api
from ..knowledge import nursery as nursery_api
from ..knowledge import operations as operations_api
from ..knowledge import overlay as overlay_api
from ..knowledge._paths import resolve_root
from .models import (
    ELIGIBLE_PARTITIONS,
    CheckFailed,
    CheckVerified,
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
    ProducerAccepted,
    ProducerDeclined,
    ProducerError,
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
    # Tier C. `checked` is the only assurance that can put `proved` in an
    # episode, and these two tools are the only things that can produce it.
    # Both are declared `requires_approval=True` in `build_toolset`, so the run
    # ENDS when the model calls one and a trusted process decides.
    "bounded_induction": "checked",
    "modeq_family": "checked",
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
#:
#: Raised from 60 to 120 in slice A4, for a measured reason rather than a
#: comfort one. The eligible population is 98 facts, and the generality rule
#: asks the model to name three OTHER eligible facts "from ids the tools showed
#: you". With a 60-row cap, a fact whose siblings sit outside the first page
#: cannot satisfy that rule no matter what is true of the mathematics -- the
#: first live A4 episode emitted `NoGeneralRoute` for `Nat.ModEq` reflexivity
#: while naming only the two ModEq facts its page happened to contain, with
#: symmetry and transitivity eligible and unseen. That is a retrieval failure
#: recorded as a mathematical obstruction, which is exactly the measurement the
#: obstruction graph must not be poisoned by. The cap now exceeds the eligible
#: population, so "I could not name three" means what it says.
MAX_ROWS = 120


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
    #: Typed tier-C outcomes, in the order the tools produced them.
    #:
    #: The `Supervise` node reads the outcome from here rather than parsing it
    #: back out of a `ToolReturnPart`, because a projection of the transcript is
    #: what the EPISODE records and re-deriving the object from that projection
    #: would make the two agree by construction instead of by measurement.
    producer_outcomes: list[Any] = field(default_factory=list)
    #: `time.monotonic()` at which this episode's wall budget expires, or 0 for
    #: no deadline. It lives here rather than only on the graph state because a
    #: tier-C tool has to refuse work it cannot finish, and a budget the tool
    #: cannot see is a budget only the harness can enforce -- which is one node
    #: boundary too late when the work is a producer call.
    deadline: float = 0.0

    @classmethod
    def for_root(cls, root: Path | str | None = None) -> AgentDeps:
        return cls(root=resolve_root(root))

    def seconds_remaining(self) -> float | None:
        """Wall seconds left, or None when this run has no deadline."""
        if self.deadline <= 0:
            return None
        return self.deadline - time.monotonic()


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
    limit: int = 120,
) -> FrontierPage:
    """List open, dependency-ready facts this loop may work on.

    Held-out and longitudinal rows are removed before this returns, so every id
    you see here is safe to name. Facts the nursery does not preregister are
    also dropped: the episode can only record a train or development partition.

    Args:
        band: Restrict to one frontier band (research, backlog, blocked,
            established) or leave empty for all bands.
        limit: Maximum rows to return, 1 to 120. The eligible population is
            smaller than that, so a single call can show you all of it.
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


# ------------------------------------------------------- tier C: checking tools
#
# Tier C is the only tier that can put `proved` in an episode, and every tool
# here is declared `requires_approval=True`. That is not a policy note: the run
# literally ENDS with a `DeferredToolRequests` output when the model calls one,
# and cannot continue until a process outside the agent resumes it with
# `DeferredToolResults`. The model can ask; it cannot dispatch.
#
# What these tools do NOT do is decide. A producer searches and a KERNEL admits;
# the footprint is then measured on the admitted name rather than inferred from
# the fact that admission succeeded. And a decline is a returned value, never an
# exception: `Declined` carries the producer's own typed Rust enum variant, and
# a tool that raised would put a decline into the harness's error path where it
# reads as a crash instead of as the datapoint it is.

#: The frozen-export resolution index, relative to the repository root. It is
#: consulted ONLY for facts no committed statement-adapter manifest resolves;
#: see its own `why_this_file_exists`.
EXPORT_INDEX = Path("artifacts") / "autogenesis" / "agent-frozen-export-index-v1.json"

#: Which tier-C tool a `producer_id` names. The keys are values that already
#: resolve in `models.known_producers()` -- registered operation ids and the
#: producer operation ids those operations declare -- so a plan naming one of
#: them is a plan in the existing vocabulary, not a new one invented for the
#: gate. Anything else is refused by `Gate` rather than guessed at.
PRODUCER_TOOLS: dict[str, str] = {
    "authoritative-mathlib-bounded-induction-factorial-family-v1": "bounded_induction",
    "bounded-induction-reflexivity-v1": "bounded_induction",
    "try_induction": "bounded_induction",
    "try_congr_rewrite": "bounded_induction",
    "try_residual_lemma": "bounded_induction",
    "try_split_congruence": "bounded_induction",
    "try_absorbing_argument": "bounded_induction",
    "try_absurd_elimination": "bounded_induction",
    "try_case_split_elimination": "bounded_induction",
    "authoritative-mathlib-modeq-family-v1": "modeq_family",
    "modeq-family-eq-iff-combinators-v1": "modeq_family",
    "close_terminal": "modeq_family",
}

#: Wall-clock budget for one producer call, in seconds.
#:
#: It is MEASURED, not preemptive, and saying so matters. A producer is a Rust
#: call; nothing here can interrupt it once it starts. So the budget is spent
#: twice: refused BEFORE the call when the episode's own deadline leaves less
#: than this, and reported AFTER it as a `resource-exhaustion` error when the
#: call overran. A thread with a join timeout would bound the wait and leave the
#: work running, which is the shape CLAUDE.md records as a 125 GB test.
PRODUCER_WALL_SECONDS = 120

#: How a producer's typed `DeclineReason.kind` lands in the episode taxonomy.
#: The default is `missing-plan-rule`: the bounded search has no rule that
#: closes this goal. The raw variant is carried beside it on the outcome, never
#: replaced by this, because the mapping is a judgement and the variant is the
#: evidence for it.
DECLINE_KIND_CLASSES: dict[str, str] = {
    "BinderBudgetExhausted": "resource-exhaustion",
    "InductionBudgetExhausted": "resource-exhaustion",
    "NotEqualityGoal": "unsupported-semantics",
    "UnsupportedGoalShape": "unsupported-semantics",
}
DEFAULT_DECLINE_CLASS = "missing-plan-rule"


class ExportResolution(NamedTuple):
    """Where a fact's frozen, proof-free goal actually lives.

    `source` says which committed record answered, because "a manifest named it"
    and "the resolution index named it" are different provenances and an
    episode that recorded them the same way would be hiding one.
    """

    fact_id: str
    path: Path
    sha256: str
    target_definition: str
    source: str


class ExportUnavailable(RuntimeError):
    """No frozen export resolves for this fact, or the bytes are not what was pinned."""


def _adapter_records(root: Path) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for path in sorted((root / "artifacts" / "autogenesis").glob("*.json")):
        try:
            document = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            continue
        if isinstance(document, dict):
            out.append(document)
    return out


def resolve_export(root: Path, fact_id: str) -> ExportResolution:
    """The frozen NDJSON export for `fact_id`, with its bytes re-hashed.

    Two routes, in order. A committed statement-adapter manifest -- one carrying
    `source_fact_id` and `external_artifact` -- is authoritative and is tried
    first; this is how all nine facts of the two multi-target operations
    resolve, and the index is never consulted for them. Only then
    `agent-frozen-export-index-v1.json`, which exists for exports that were
    produced and never registered.

    Raises:
        ExportUnavailable: when nothing resolves, when the file is not on this
            host, or when its digest is not the one that was pinned. All three
            are refusals rather than a best effort: importing bytes nobody
            pinned would make every digest downstream meaningless.
    """
    candidates: list[tuple[str, str, str, int | None]] = []
    for document in _adapter_records(root):
        if document.get("source_fact_id") != fact_id:
            continue
        artifact = document.get("external_artifact")
        target = (document.get("adapter_source") or {}).get("target_definition")
        if isinstance(artifact, dict) and isinstance(target, str) and artifact.get("path"):
            candidates.append(
                (
                    str(artifact["path"]),
                    str(artifact.get("sha256", "")),
                    target,
                    artifact.get("bytes"),
                )
            )
    source = "statement-adapter-manifest"
    if not candidates:
        try:
            index = json.loads((root / EXPORT_INDEX).read_text(encoding="utf-8"))
        except (OSError, ValueError) as error:
            raise ExportUnavailable(
                f"no statement-adapter manifest resolves this fact and the export index "
                f"is unreadable: {error}"
            ) from error
        for entry in index.get("entries", []):
            if not isinstance(entry, dict) or entry.get("fact_id") != fact_id:
                continue
            artifact = entry.get("external_artifact") or {}
            candidates.append(
                (
                    str(artifact.get("path", "")),
                    str(artifact.get("sha256", "")),
                    str(entry.get("target_definition", "")),
                    artifact.get("bytes"),
                )
            )
        source = "agent-frozen-export-index-v1"
    if not candidates:
        raise ExportUnavailable(
            "no frozen statement export is registered for this fact; a producer has "
            "nothing to import and there is no goal to attack"
        )
    path_text, pinned, target, _bytes = candidates[0]
    path = Path(path_text)
    if not path.is_file():
        raise ExportUnavailable(
            f"the frozen export is not on this host: {path}. That is a retrieval miss, "
            f"not a mathematical obstruction"
        )
    measured = hashlib.sha256(path.read_bytes()).hexdigest()
    if pinned and measured != pinned:
        raise ExportUnavailable(
            f"{path} does not hash to what was pinned (pinned {pinned}, on disk {measured}); "
            f"refusing to import bytes nobody pinned"
        )
    if not target:
        raise ExportUnavailable(f"the record for this fact names no target definition ({source})")
    return ExportResolution(fact_id, path, measured, target, source)


def _sha256_of_render(kernel: Any, expression: Any) -> str:
    """The digest the operation drivers stamp on a rendered term.

    `sha256(render_lean(term))`, byte for byte the same computation as
    `scripts/execute-autogenesis-operation.py` and the family checkers, so a
    value produced here is comparable to a committed manifest rather than
    merely similar to one.
    """
    return hashlib.sha256(kernel.render_lean(expression).encode()).hexdigest()


def run_producer(tool: str, export: ExportResolution) -> dict[str, Any]:
    """Import the frozen goal, search, and let a KERNEL decide. One indirection.

    This is a module-level function and not an inline block because the two
    tests that must run on a host without `/nas3` replace it. Everything that
    touches the pinned exports is behind it; everything above it is resolution
    and policy, which is testable anywhere.

    Returns a plain dict rather than a model so the caller owns the mapping into
    the typed outcome, and raises `producers.Declined` unchanged so the caller
    can read `.reason.kind` rather than a message.
    """
    from .. import producers as producers_api
    from ..kernel import Declaration

    imported = producers_api.import_statement_ndjson(
        str(export.path), None, export.target_definition
    )
    kernel = imported.kernel()
    goal = imported.goal()
    report = imported.report()
    propose = (
        producers_api.propose_bounded_induction
        if tool == "bounded_induction"
        else producers_api.propose_modeq_family
    )
    candidate = propose(kernel, goal)
    name = kernel.name(f"Axeyum.Agent.{export.fact_id.split(':', 1)[1]}", must_exist=False)
    kernel.add_declaration(Declaration.theorem(name, [], goal, candidate.proof))
    return {
        "goal_sha256": _sha256_of_render(kernel, goal),
        "proof_sha256": _sha256_of_render(kernel, candidate.proof),
        "binders_used": int(candidate.binders_used),
        "inductions_used": getattr(candidate, "inductions_used", None),
        "admitted_declarations": int(report.admitted_declarations),
        "axiom_footprint": tuple(str(a) for a in kernel.axiom_footprint(name)),
        "theorem_dependencies": tuple(str(d) for d in kernel.theorem_dependencies(name)),
    }


def _tier_c(
    ctx: RunContext[AgentDeps],
    tool: str,
    fact_id: str,
) -> ProducerAccepted | ProducerDeclined | ProducerError:
    """The shared body of both tier-C tools. Never raises for a decline."""

    def body() -> ProducerAccepted | ProducerDeclined | ProducerError:
        from .. import producers as producers_api

        root = ctx.deps.root
        started = time.monotonic()

        def elapsed() -> int:
            return max(0, int((time.monotonic() - started) * 1000))

        if fact_id in _held_out(str(root)):
            return ProducerError(
                fact_id="F:redacted",
                tool=tool,
                error_kind="HeldOutTarget",
                detail=(
                    "that fact is in the blind held-out population; a producer must not be "
                    "pointed at it and the id is not repeated here"
                ),
                decline_class="operational-failure",
                duration_ms=elapsed(),
            )
        remaining = ctx.deps.seconds_remaining()
        if remaining is not None and remaining < PRODUCER_WALL_SECONDS:
            return ProducerError(
                fact_id=fact_id,
                tool=tool,
                error_kind="WallBudgetTooSmall",
                detail=(
                    f"{remaining:.0f}s of wall budget remain and one producer call is "
                    f"budgeted at {PRODUCER_WALL_SECONDS}s; refusing to start work that "
                    f"cannot be bounded"
                ),
                decline_class="resource-exhaustion",
                duration_ms=elapsed(),
            )
        try:
            export = resolve_export(root, fact_id)
        except ExportUnavailable as error:
            return ProducerError(
                fact_id=fact_id,
                tool=tool,
                error_kind="ExportUnavailable",
                detail=str(error),
                decline_class="retrieval-miss",
                duration_ms=elapsed(),
            )
        try:
            measured = run_producer(tool, export)
        except producers_api.Declined as declined:
            kind = str(declined.reason.kind)
            return ProducerDeclined(
                fact_id=fact_id,
                tool=tool,
                reason_kind=kind,
                detail=str(declined.reason.detail),
                decline_class=DECLINE_KIND_CLASSES.get(kind, DEFAULT_DECLINE_CLASS),
                duration_ms=elapsed(),
            )
        except Exception as error:  # noqa: BLE001 - reported as a typed value, never swallowed
            return ProducerError(
                fact_id=fact_id,
                tool=tool,
                error_kind=type(error).__name__,
                detail=str(error),
                decline_class="operational-failure",
                duration_ms=elapsed(),
            )
        spent = elapsed()
        if spent > PRODUCER_WALL_SECONDS * 1000:
            return ProducerError(
                fact_id=fact_id,
                tool=tool,
                error_kind="WallBudgetOverrun",
                detail=(
                    f"the call took {spent}ms against a {PRODUCER_WALL_SECONDS}s budget; "
                    f"the budget is measured, not preemptive, so the overrun is reported "
                    f"rather than prevented"
                ),
                decline_class="resource-exhaustion",
                duration_ms=spent,
            )
        accepted = ProducerAccepted(
            fact_id=fact_id,
            tool=tool,
            target_definition=export.target_definition,
            export_path=str(export.path),
            export_sha256=export.sha256,
            goal_sha256=measured["goal_sha256"],
            proof_sha256=measured["proof_sha256"],
            binders_used=measured["binders_used"],
            inductions_used=measured["inductions_used"],
            admitted_declarations=measured["admitted_declarations"],
            axiom_footprint=measured["axiom_footprint"],
            theorem_dependencies=measured["theorem_dependencies"],
            duration_ms=spent,
        )
        return accepted

    # EVERY outcome is recorded, not only the accepted one. Appending on the
    # accepted branch alone was a real defect measured 2026-08-24: an episode
    # whose producer honestly reported `retrieval-miss` was written as
    # `operational-failure`, because `Supervise` found the outcome list empty
    # and could not tell "the tool declined" from "the tool never ran". A
    # taxonomy that loses the reason on exactly the paths the taxonomy is for is
    # worse than no taxonomy.
    outcome = _timed(tool, ctx, body)
    ctx.deps.producer_outcomes.append(outcome)
    return outcome


def bounded_induction(
    ctx: RunContext[AgentDeps],
    fact_id: str,
) -> ProducerAccepted | ProducerDeclined | ProducerError:
    """Run the bounded structural-induction producer on a fact's frozen goal, and CHECK it.

    This dispatches. Calling it ends your turn: the run stops with an approval
    request and a process outside this agent decides whether it happens. You
    cannot admit anything, and neither can this tool -- it imports the fact's
    proof-free statement export, searches for a proof term under the pinned
    binder and induction budgets, and hands the term to a kernel, which is what
    accepts or rejects it. A refusal comes back as a typed `declined` result
    with the producer's own reason, not as an error.

    Args:
        fact_id: The fact to attack, as frontier_select returned it.
    """
    return _tier_c(ctx, "bounded_induction", fact_id)


def modeq_family(
    ctx: RunContext[AgentDeps],
    fact_id: str,
) -> ProducerAccepted | ProducerDeclined | ProducerError:
    """Run the ModEq Eq/Iff combinator producer on a fact's frozen goal, and CHECK it.

    This dispatches, under the same approval gate as bounded_induction. It suits
    a goal that is a definitional equivalence relation -- reflexivity, symmetry,
    transitivity, commutativity of a transparent `a % n = b % n` style relation
    -- where the move is primitive Eq/Iff combinators rather than an induction.
    The kernel decides; a refusal is a typed `declined` result.

    Args:
        fact_id: The fact to attack, as frontier_select returned it.
    """
    return _tier_c(ctx, "modeq_family", fact_id)


def independent_check(
    root: Path,
    fact_id: str,
    tool: str,
    expected_proof_sha256: str,
) -> CheckVerified | CheckFailed:
    """Re-derive the proof in a SECOND kernel and compare. The re-validator.

    The producer's kernel is not reused and cannot be: an `ExprId` is an index
    into the kernel that interned it, so a term cannot be carried across. That
    constraint is the feature -- this re-imports the same frozen export into a
    fresh kernel, re-runs the producer, re-renders, and only then compares the
    digest against what the tool reported. A producer that returned a different
    term, or a recorded digest that was tampered with, comes back `failed`.

    The footprint is measured on the newly admitted name in the new kernel, so a
    passing result is two independent kernels agreeing rather than one kernel
    consulted twice.
    """
    try:
        export = resolve_export(root, fact_id)
    except ExportUnavailable as error:
        return CheckFailed(fact_id=fact_id, reason=f"export unavailable to the checker: {error}")
    try:
        measured = run_producer(tool, export)
    except Exception as error:  # noqa: BLE001 - a checker that raised is a checker that skipped
        return CheckFailed(
            fact_id=fact_id,
            reason=f"the independent re-run did not produce a candidate: {type(error).__name__}: {error}",
        )
    if measured["proof_sha256"] != expected_proof_sha256:
        return CheckFailed(
            fact_id=fact_id,
            reason="the independently re-derived proof term is not the one that was reported",
            expected=expected_proof_sha256,
            actual=measured["proof_sha256"],
        )
    return CheckVerified(
        fact_id=fact_id,
        goal_sha256=measured["goal_sha256"],
        proof_sha256=measured["proof_sha256"],
        axiom_footprint=measured["axiom_footprint"],
        theorem_dependencies=measured["theorem_dependencies"],
        admitted_declarations=measured["admitted_declarations"],
    )


TIER_C_TOOLS: tuple[Callable[..., Any], ...] = (bounded_induction, modeq_family)


TIER_R_TOOLS: tuple[Callable[..., Any], ...] = (
    frontier_select,
    fact_get,
    fact_neighbourhood,
    kernel_theorems,
    operation_registry,
    overlay_query,
)


def build_toolset(*, include_tier_c: bool = False) -> FunctionToolset[AgentDeps]:
    """The tier-R toolset, plus the two tier-C tools when a node asks for them.

    `include_tier_c` defaults to False and that default is load-bearing: the
    `Gather` and `Plan` nodes build the toolset with no argument, so the model
    doing the looking and the model writing the plan cannot see a tool that
    dispatches. Only `Dispatch` passes True, and every tool it adds is declared
    `requires_approval=True`, so seeing one is still not being able to run one.

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
    if include_tier_c:
        for function in TIER_C_TOOLS:
            # `requires_approval=True` is what makes this a deferred tool: the
            # model calling it does not run it, it ends the run with a
            # `DeferredToolRequests` output and waits for `DeferredToolResults`.
            toolset.add_function(function, requires_approval=True)
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
        for name, function in ((f.__name__, f) for f in TIER_R_TOOLS + TIER_C_TOOLS)
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
    "DECLINE_KIND_CLASSES",
    "DEFAULT_DECLINE_CLASS",
    "EXPORT_INDEX",
    "MAX_ROWS",
    "OUTPUT_TOOL_PREFIX",
    "PRELUDES",
    "PRODUCER_TOOLS",
    "PRODUCER_WALL_SECONDS",
    "TIER_C_TOOLS",
    "TIER_R_TOOLS",
    "TOOL_TIERS",
    "AgentDeps",
    "ExportResolution",
    "ExportUnavailable",
    "ToolCallRecord",
    "ToolRefusal",
    "bounded_induction",
    "build_toolset",
    "eligible_fact_ids",
    "fact_get",
    "fact_neighbourhood",
    "frontier_select",
    "independent_check",
    "is_output_tool",
    "kernel_theorems",
    "modeq_family",
    "operation_registry",
    "overlay_query",
    "resolve_export",
    "run_producer",
    "toolset_fingerprint",
    "toolset_sha256",
]
