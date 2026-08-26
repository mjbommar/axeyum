"""The eight tier-R tools, and the held-out filter that lives inside them.

The central assertion is not "no held-out id appeared". That is what a broken
filter and a working one both report when the population is empty or the query
is wrong. Every isolation test here is paired with a POSITIVE control -- a
count of rows the filter actually removed -- so a filter that silently stopped
filtering fails a test rather than passing a vacuous one.
"""

from __future__ import annotations

import types

import pytest

pytest.importorskip("pydantic_ai", reason="the [agent] extra is not installed")

from axeyum.agent import tools
from axeyum.agent.models import ELIGIBLE_PARTITIONS
from axeyum.agent.tools import AgentDeps
from axeyum.knowledge import frontier as frontier_api
from axeyum.knowledge import nursery as nursery_api
from axeyum.knowledge._paths import resolve_root


@pytest.fixture(scope="module")
def root():
    return resolve_root(None)


@pytest.fixture(scope="module")
def ctx(root):
    """A minimal RunContext stand-in: the tools read `deps` and `tool_call_id`."""
    return types.SimpleNamespace(deps=AgentDeps(root=root), tool_call_id=None)


def independent_eligible(root) -> tuple[str, ...]:
    """The eligible population, recomputed here from `axeyum.knowledge` alone.

    Deliberately a second implementation: `frontier_select` must agree with it,
    so a filter that stopped filtering would have to break in both places at
    once, in the same direction, to stay green.
    """
    live = frontier_api.load(root)
    pen = nursery_api.load(root)
    return tuple(
        entry.fact_id
        for entry in live.entries
        if entry.dependency_ready
        and entry.epistemic_status == "open"
        and pen.contains(entry.fact_id)
        and pen.partition_of(entry.fact_id) in ELIGIBLE_PARTITIONS
    )


# --------------------------------------------------------------- frontier_select


def test_frontier_select_matches_an_independent_computation(ctx, root) -> None:
    page = tools.frontier_select(ctx, limit=tools.MAX_ROWS)
    expected = independent_eligible(root)
    assert page.eligible_total == len(expected)
    assert tools.eligible_fact_ids(root) == expected


def test_frontier_select_returns_no_held_out_id(ctx, root) -> None:
    held = nursery_api.load(root).held_out_ids()
    page = tools.frontier_select(ctx, limit=tools.MAX_ROWS)
    assert held, "the held-out population is empty; this test would pass vacuously"
    assert [row.fact_id for row in page.rows if row.fact_id in held] == []


def test_frontier_select_actually_dropped_held_out_rows(ctx) -> None:
    """The positive control. Without it, an empty intersection proves nothing."""
    page = tools.frontier_select(ctx, limit=tools.MAX_ROWS)
    assert page.dropped_held_out > 0, (
        "no dependency-ready row was dropped as held-out; either the population "
        "changed or the filter is no longer filtering, and the isolation test "
        "above cannot tell those apart"
    )


def test_frontier_select_drops_longitudinal_and_unpartitioned(ctx, root) -> None:
    page = tools.frontier_select(ctx, limit=tools.MAX_ROWS)
    pen = nursery_api.load(root)
    partitions = {p for p in pen.by_partition() if p not in ELIGIBLE_PARTITIONS}
    assert "held-out" in partitions
    assert all(row.partition in ELIGIBLE_PARTITIONS for row in page.rows)
    assert page.dropped_longitudinal + page.dropped_unpartitioned >= 0


def test_frontier_select_respects_its_limit(ctx) -> None:
    page = tools.frontier_select(ctx, limit=3)
    assert len(page.rows) == 3
    assert page.returned == 3
    assert page.eligible_total > 3


def test_frontier_select_band_filter_narrows(ctx) -> None:
    everything = tools.frontier_select(ctx, limit=tools.MAX_ROWS)
    nonsense = tools.frontier_select(ctx, band="not-a-band", limit=tools.MAX_ROWS)
    assert nonsense.eligible_total == 0
    assert everything.eligible_total > 0


# ------------------------------------------------------------ fact_get / graph


def test_fact_get_reads_an_eligible_fact(ctx, root) -> None:
    fact_id = tools.eligible_fact_ids(root)[0]
    view = tools.fact_get(ctx, fact_id)
    assert view.fact_id == fact_id
    assert view.epistemic_status == "open"
    assert view.partition in ELIGIBLE_PARTITIONS


def test_fact_get_refuses_a_held_out_fact_without_echoing_it(ctx, root) -> None:
    blind = min(nursery_api.load(root).held_out_ids())
    with pytest.raises(tools.ToolRefusal) as caught:
        tools.fact_get(ctx, blind)
    assert blind not in str(caught.value), (
        "the refusal repeated the held-out id; an id in an error message is an "
        "id in the transcript, which is the breach itself"
    )


def test_fact_get_refuses_an_unknown_fact(ctx) -> None:
    with pytest.raises(tools.ToolRefusal):
        tools.fact_get(ctx, "F:not-a-real-fact-00000000")


def test_fact_neighbourhood_filters_held_out_neighbours(ctx, root) -> None:
    held = nursery_api.load(root).held_out_ids()
    fact_id = tools.eligible_fact_ids(root)[0]
    hood = tools.fact_neighbourhood(ctx, fact_id)
    named = {r.fact_id for r in hood.depends_on} | {r.fact_id for r in hood.would_unlock}
    assert named.isdisjoint(held)


def test_fact_neighbourhood_refuses_a_held_out_centre(ctx, root) -> None:
    blind = min(nursery_api.load(root).held_out_ids())
    with pytest.raises(tools.ToolRefusal):
        tools.fact_neighbourhood(ctx, blind)


# ------------------------------------------------------------- kernel_theorems


def test_kernel_theorems_returns_rows_for_nat(ctx) -> None:
    page = tools.kernel_theorems(ctx, prelude="nat")
    assert page.total_theorems > 0
    assert page.rows
    assert all(row.type for row in page.rows)


def test_kernel_theorems_glob_narrows_without_hiding_the_total(ctx) -> None:
    """An empty result for a glob is a FAILED lookup, and `total_theorems` is
    what lets a caller tell that from an empty prelude."""
    page = tools.kernel_theorems(ctx, prelude="nat", name_glob="*definitely-not-a-theorem*")
    assert page.matched == 0
    assert page.total_theorems > 0


def test_kernel_theorems_refuses_an_unknown_prelude(ctx) -> None:
    with pytest.raises(tools.ToolRefusal):
        tools.kernel_theorems(ctx, prelude="axreal-but-misspelled")


def test_every_declared_prelude_builds(ctx) -> None:
    for prelude in tools.PRELUDES:
        assert tools.kernel_theorems(ctx, prelude=prelude).total_theorems >= 0


# --------------------------------------- lemma / operation_registry / overlay


def test_lemma_neighbourhood_exposes_candidate_dependencies(ctx) -> None:
    page = tools.lemma_neighbourhood(ctx, name_glob="Nat.add_*")
    assert page.total_lemmas > 0
    assert page.matched > 0
    assert all(row.declaration_id.startswith("Nat.add_") for row in page.rows)
    assert all(row.canonical_type for row in page.rows)
    assert all(row.axiom_footprint_size == 0 for row in page.rows)


def test_lemma_neighbourhood_requires_one_query_axis(ctx) -> None:
    with pytest.raises(tools.ToolRefusal):
        tools.lemma_neighbourhood(ctx)
    with pytest.raises(tools.ToolRefusal):
        tools.lemma_neighbourhood(ctx, name_glob="Nat.*", fact_id="F:any")


def test_lemma_neighbourhood_filters_by_canonical_type(ctx) -> None:
    page = tools.lemma_neighbourhood(ctx, canonical_type_contains="AxNat.fib")
    assert page.matched > 0
    assert page.canonical_type_contains == "AxNat.fib"
    assert all("AxNat.fib" in row.canonical_type for row in page.rows)


def test_lemma_candidates_joins_fact_dependencies_to_exact_kernel_links(ctx) -> None:
    page = tools.lemma_candidates(ctx, "F:ml430-nat-fib-mono-cc6afe09")
    assert page.declared_dependency_count == 1
    assert page.linked_dependency_count == 1
    assert page.matched == 1
    assert page.unresolved_dependency_fact_ids == ()
    assert page.rows[0].source_dependency_fact_id == ("F:ml430-nat-fib-le-fib-succ-d1ef4a3d")
    assert page.rows[0].declaration_id == "Nat.fib_le_succ"
    assert "AxNat.fib" in page.rows[0].canonical_type
    assert page.rows[0].axiom_footprint_size == 0


def test_lemma_candidates_reports_unlinked_dependencies_without_guessing(ctx) -> None:
    page = tools.lemma_candidates(ctx, "F:ml430-nat-modeq-dvd-iff-8f130450")
    assert page.declared_dependency_count > 0
    assert page.linked_dependency_count < page.declared_dependency_count
    assert page.unresolved_dependency_fact_ids


def test_operation_registry_exposes_generality(ctx) -> None:
    view = tools.operation_registry(ctx)
    assert view.total > 0
    assert view.single_target + view.multi_target == view.total
    assert all(row.n_targets == len(row.fact_ids) or row.n_targets >= 1 for row in view.rows)


def test_overlay_query_filters_by_relation(ctx) -> None:
    everything = tools.overlay_query(ctx)
    assert everything.total_links > 0
    relation = everything.rows[0].relation
    narrowed = tools.overlay_query(ctx, relation=relation)
    assert 0 < narrowed.matched <= everything.matched
    assert all(row.relation == relation for row in narrowed.rows)


# ----------------------------------------------------------------- the toolset


def test_every_tool_declares_a_tier() -> None:
    # `TIER_R_GUARDED_TOOLS` joined the union in slice A6. It is a THIRD tuple
    # rather than six-plus-two in `TIER_R_TOOLS` because the two axes are
    # different: those tools are tier R by assurance and guarded by
    # availability, and only `build_toolset(with_web=True)` offers them.
    declared = {
        f.__name__ for f in tools.TIER_R_TOOLS + tools.TIER_R_GUARDED_TOOLS + tools.TIER_C_TOOLS
    }
    assert declared == set(tools.TOOL_TIERS)
    assert {tools.TOOL_TIERS[f.__name__] for f in tools.TIER_R_TOOLS} == {"read"}
    assert {tools.TOOL_TIERS[f.__name__] for f in tools.TIER_R_GUARDED_TOOLS} == {"read"}
    assert {tools.TOOL_TIERS[f.__name__] for f in tools.TIER_C_TOOLS} == {"checked"}


def test_the_toolset_exposes_exactly_the_eight_read_tools() -> None:
    assert len(tools.TIER_R_TOOLS) == 8
    tools.build_toolset()  # constructs, so every parameter carries a description


def test_output_tool_names_are_recognized_narrowly() -> None:
    assert tools.is_output_tool("final_result")
    assert tools.is_output_tool("final_result_StrategyProposal")
    assert tools.is_output_tool("final_result_NoGeneralRoute")
    assert not tools.is_output_tool("final_results_cache")
    assert not tools.is_output_tool("frontier_select")


def test_the_toolset_digest_is_stable_and_covers_every_tool() -> None:
    digest = tools.toolset_sha256()
    assert digest == tools.toolset_sha256()
    assert set(tools.toolset_fingerprint()) == set(tools.TOOL_TIERS)


def test_calls_are_recorded_with_a_duration_and_a_status(root) -> None:
    deps = AgentDeps(root=root)
    ctx = types.SimpleNamespace(deps=deps, tool_call_id="call-1")
    tools.frontier_select(ctx, limit=1)
    assert len(deps.calls) == 1
    assert deps.calls[0].tool == "frontier_select"
    assert deps.calls[0].exit_status == 0
    assert deps.calls[0].duration_ms >= 0


def test_a_refusal_is_recorded_with_a_nonzero_status(root) -> None:
    deps = AgentDeps(root=root)
    ctx = types.SimpleNamespace(deps=deps, tool_call_id="call-1")
    with pytest.raises(tools.ToolRefusal):
        tools.fact_get(ctx, "F:not-a-real-fact-00000000")
    assert deps.calls[0].exit_status == 1
