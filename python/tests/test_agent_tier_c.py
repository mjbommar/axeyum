"""The two tier-C tools: what they resolve, what they refuse, and what they measure.

Tier C is the only tier that can put `proved` in an episode, so the interesting
assertions here are the refusals. Every one of them is a *returned typed value*
rather than an exception, and that is the property under test: a decline has no
candidate to return and `None` would erase the reason, but a decline delivered
as an exception lands in the harness's error path where it reads as a crash
instead of as the datapoint it is.

Everything that touches `/nas3` goes through one indirection, `run_producer`,
which these tests replace. That is deliberate: resolution, budget policy, the
held-out guard and the decline mapping are testable on any host, and only the
two tests that reproduce a committed digest need the pinned exports.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from types import SimpleNamespace

import pytest

pytest.importorskip("pydantic_ai", reason="the [agent] extra is not installed")

from axeyum.agent import tools
from axeyum.agent.models import ProducerAccepted, ProducerDeclined, ProducerError
from axeyum.knowledge._paths import resolve_root

#: A fact with a committed statement-adapter manifest (route 1) and one with an
#: entry only in the resolution index (route 2). Keeping both is the point: the
#: index must never shadow a manifest.
MANIFEST_FACT = "F:ml430-nat-descfactorial-one-d4856d4a"
INDEX_FACT = "F:ml430-nat-modeq-comm-24b71e7a"

#: Reproduced from `python/tests/test_producers.py`, which reproduces them from
#: the committed manifests. A digest asserted in two places that both derive it
#: from the same run is not two measurements; these come from the manifests.
FROZEN_MODEQ_TRANS_PROOF_SHA = "c5e4388868b7e82a46843080112d61a09e2115a4a7a2e36d8e5960a973391b82"

STUB = {
    "goal_sha256": "a" * 64,
    "proof_sha256": "b" * 64,
    "binders_used": 2,
    "inductions_used": None,
    "admitted_declarations": 193,
    "axiom_footprint": (),
    "theorem_dependencies": (),
}


@pytest.fixture(scope="module")
def root() -> Path:
    return resolve_root(None)


@pytest.fixture(autouse=True)
def portable_registered_exports(tmp_path: Path, monkeypatch) -> None:
    """Keep policy tests independent of fleet-only frozen-export storage."""
    if _FROZEN.is_file():
        return
    source = tmp_path / "portable.ndjson"
    source.write_text('{"kind":"portable-test-export"}\n')
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    original = tools.resolve_export

    def resolve(root: Path, fact_id: str):
        if fact_id not in {MANIFEST_FACT, INDEX_FACT}:
            return original(root, fact_id)
        return tools.ExportResolution(
            fact_id=fact_id,
            path=source,
            sha256=digest,
            target_definition=(
                "Axeyum.Autogenesis.Statement.natDescFactorialOne"
                if fact_id == MANIFEST_FACT
                else "Axeyum.Autogenesis.Statement.NatModEqFamily.natModEqComm"
            ),
            source=(
                "statement-adapter-manifest"
                if fact_id == MANIFEST_FACT
                else "agent-frozen-export-index-v1"
            ),
        )

    monkeypatch.setattr(tools, "resolve_export", resolve)


def context(root: Path, deadline: float = 0.0) -> SimpleNamespace:
    deps = tools.AgentDeps(root=root, deadline=deadline)
    return SimpleNamespace(deps=deps, tool_call_id="t0")


# --------------------------------------------------------------- declaration


def test_both_tier_c_tools_declare_the_checked_assurance() -> None:
    assert tools.TOOL_TIERS["bounded_induction"] == "checked"
    assert tools.TOOL_TIERS["modeq_family"] == "checked"


def test_the_default_toolset_does_not_expose_a_tool_that_dispatches() -> None:
    """`Gather` and `Plan` build the toolset with no argument."""
    default = tools.build_toolset()
    names = set(default.tools)
    assert "modeq_family" not in names
    assert "bounded_induction" not in names
    assert "frontier_select" in names


def test_the_dispatch_toolset_declares_every_tier_c_tool_as_requiring_approval() -> None:
    """Seeing the tool is not being able to run it, and that is a library-level fact."""
    toolset = tools.build_toolset(include_tier_c=True)
    for name in ("bounded_induction", "modeq_family"):
        assert name in toolset.tools
        assert toolset.tools[name].requires_approval is True, (
            f"{name} must be deferred; without requires_approval the model dispatches"
        )


def test_the_toolset_fingerprint_covers_the_tier_c_tools() -> None:
    """A widened tool surface must change `policy.toolset_sha256`."""
    fingerprint = tools.toolset_fingerprint()
    assert set(fingerprint) == set(tools.TOOL_TIERS)
    assert fingerprint["modeq_family"]["assurance"] == "checked"


def test_every_registered_producer_id_routes_to_a_tool_that_exists() -> None:
    names = {f.__name__ for f in tools.TIER_C_TOOLS}
    assert set(tools.PRODUCER_TOOLS.values()) <= names


# ------------------------------------------------------------------ resolution


def test_a_committed_manifest_resolves_before_the_index(root: Path) -> None:
    resolution = tools.resolve_export(root, MANIFEST_FACT)
    assert resolution.source == "statement-adapter-manifest"
    assert resolution.target_definition.endswith("natDescFactorialOne")


def test_the_index_resolves_an_export_when_no_manifest_names(tmp_path: Path, monkeypatch) -> None:
    source = tmp_path / "source.ndjson"
    source.write_text('{"kind":"fixture"}\n')
    index = tmp_path / "index.json"
    index.write_text(
        json.dumps(
            {
                "entries": [
                    {
                        "fact_id": "F:ml430-index-only-0000cafe",
                        "target_definition": (
                            "Axeyum.Autogenesis.Statement.NatModEqFamily.natModEqComm"
                        ),
                        "external_artifact": {
                            "path": str(source),
                            "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                        },
                    }
                ]
            }
        )
    )
    monkeypatch.setattr(tools, "EXPORT_INDEX", index.relative_to(tmp_path))
    resolution = tools.resolve_export(tmp_path, "F:ml430-index-only-0000cafe")
    assert resolution.source == "agent-frozen-export-index-v1"
    assert resolution.target_definition.endswith("natModEqComm")


def test_a_fact_with_no_frozen_export_is_refused(root: Path) -> None:
    with pytest.raises(tools.ExportUnavailable, match="no frozen statement export"):
        tools.resolve_export(root, "F:ml430-int-fib-add-181b6a2c")


def test_the_resolved_export_is_rehashed_and_a_mismatch_is_refused(
    root: Path, tmp_path: Path, monkeypatch
) -> None:
    """A pinned digest that is not re-derived is a pin nobody checks."""
    decoy = tmp_path / "decoy.ndjson"
    decoy.write_text("not the pinned bytes\n")
    index = tmp_path / "index.json"
    index.write_text(
        json.dumps(
            {
                "entries": [
                    {
                        "fact_id": "F:ml430-decoy-0000dead",
                        "target_definition": "X.Y",
                        "external_artifact": {"path": str(decoy), "sha256": "0" * 64},
                    }
                ]
            }
        )
    )
    monkeypatch.setattr(tools, "EXPORT_INDEX", index.relative_to(tmp_path))
    with pytest.raises(tools.ExportUnavailable, match="does not hash to what was pinned"):
        tools.resolve_export(tmp_path, "F:ml430-decoy-0000dead")


def test_an_export_that_is_not_on_this_host_is_a_retrieval_miss_not_a_guess(
    tmp_path: Path, monkeypatch
) -> None:
    index = tmp_path / "index.json"
    index.write_text(
        json.dumps(
            {
                "entries": [
                    {
                        "fact_id": "F:ml430-absent-0000beef",
                        "target_definition": "X.Y",
                        "external_artifact": {
                            "path": str(tmp_path / "nowhere.ndjson"),
                            "sha256": "0" * 64,
                        },
                    }
                ]
            }
        )
    )
    monkeypatch.setattr(tools, "EXPORT_INDEX", index.relative_to(tmp_path))
    with pytest.raises(tools.ExportUnavailable, match="not on this host"):
        tools.resolve_export(tmp_path, "F:ml430-absent-0000beef")


def test_the_committed_index_pins_every_export_it_names(root: Path) -> None:
    """Each entry's digest is re-derived from the bytes on disk, or skipped loudly."""
    index = json.loads((root / tools.EXPORT_INDEX).read_text())
    checked = 0
    for entry in index["entries"]:
        path = Path(entry["external_artifact"]["path"])
        if not path.is_file():
            continue
        checked += 1
        assert hashlib.sha256(path.read_bytes()).hexdigest() == entry["external_artifact"]["sha256"]
    if checked == 0:
        pytest.skip(f"no pinned export on this host: {index['entries'][0]}")


# ------------------------------------------------------------------- refusals


def test_a_held_out_target_is_refused_without_repeating_the_id(root: Path, monkeypatch) -> None:
    """The refusal must not echo the id: an id in a message is an id in the transcript."""
    from axeyum.knowledge import nursery as nursery_api

    held = min(nursery_api.load(root).held_out_ids())
    monkeypatch.setattr(tools, "run_producer", lambda tool, export: STUB)
    outcome = tools.modeq_family(context(root), held)
    assert isinstance(outcome, ProducerError)
    assert outcome.error_kind == "HeldOutTarget"
    assert held not in json.dumps(outcome.model_dump(mode="json"))


def test_a_wall_budget_smaller_than_one_producer_call_refuses_before_starting(
    root: Path, monkeypatch
) -> None:
    import time

    monkeypatch.setattr(tools, "run_producer", lambda tool, export: STUB)
    outcome = tools.modeq_family(context(root, deadline=time.monotonic() + 5), INDEX_FACT)
    assert isinstance(outcome, ProducerError)
    assert outcome.error_kind == "WallBudgetTooSmall"
    assert outcome.decline_class == "resource-exhaustion"


def test_an_absent_export_comes_back_as_a_typed_retrieval_miss(root: Path) -> None:
    outcome = tools.modeq_family(context(root), "F:ml430-int-fib-add-181b6a2c")
    assert isinstance(outcome, ProducerError)
    assert outcome.error_kind == "ExportUnavailable"
    assert outcome.decline_class == "retrieval-miss"


def declined_with(kind: str, detail: str = "d"):
    """A `producers.Declined` carrying a typed reason, as the binding delivers one.

    Subclassed rather than constructed: the real exception's `.reason` comes
    from Rust, and a test that read a message string instead would pass against
    a binding that had stopped carrying the variant at all.
    """
    from axeyum import producers as producers_api

    class _Reason:
        pass

    reason = _Reason()
    reason.kind = kind
    reason.detail = detail

    class _Declined(producers_api.Declined):
        def __init__(self) -> None:
            super().__init__(kind)
            self.reason = reason

    return _Declined()


def test_a_producer_decline_is_a_returned_value_carrying_the_typed_variant(
    root: Path, monkeypatch
) -> None:
    def refuse(tool, export):
        raise declined_with("TerminalNotDefEqNoRewrite", "not definitionally equal")

    monkeypatch.setattr(tools, "run_producer", refuse)
    outcome = tools.modeq_family(context(root), INDEX_FACT)
    assert isinstance(outcome, ProducerDeclined)
    assert outcome.reason_kind == "TerminalNotDefEqNoRewrite"
    assert outcome.decline_class == tools.DEFAULT_DECLINE_CLASS


def test_a_budget_exhausted_decline_maps_to_resource_exhaustion(root: Path, monkeypatch) -> None:
    def refuse(tool, export):
        raise declined_with("BinderBudgetExhausted", "8 binders")

    monkeypatch.setattr(tools, "run_producer", refuse)
    outcome = tools.modeq_family(context(root), INDEX_FACT)
    assert outcome.decline_class == "resource-exhaustion"


def test_an_unexpected_exception_is_an_operational_failure_not_a_decline(
    root: Path, monkeypatch
) -> None:
    """ "The producer refused" and "the tool broke" are different findings."""

    def explode(tool, export):
        raise RuntimeError("the binding fell over")

    monkeypatch.setattr(tools, "run_producer", explode)
    outcome = tools.modeq_family(context(root), INDEX_FACT)
    assert isinstance(outcome, ProducerError)
    assert outcome.decline_class == "operational-failure"
    assert outcome.error_kind == "RuntimeError"


def test_an_overrun_call_is_reported_as_resource_exhaustion(root: Path, monkeypatch) -> None:
    """The wall budget is MEASURED, not preemptive, and the overrun is not hidden."""
    monkeypatch.setattr(tools, "PRODUCER_WALL_SECONDS", 0)
    monkeypatch.setattr(tools, "run_producer", lambda tool, export: STUB)
    outcome = tools.modeq_family(context(root), INDEX_FACT)
    assert isinstance(outcome, ProducerError)
    assert outcome.error_kind == "WallBudgetOverrun"


# ------------------------------------------------------------------ acceptance


def test_an_accepted_outcome_carries_the_measured_footprint(root: Path, monkeypatch) -> None:
    monkeypatch.setattr(tools, "run_producer", lambda tool, export: STUB)
    outcome = tools.modeq_family(context(root), INDEX_FACT)
    assert isinstance(outcome, ProducerAccepted)
    assert outcome.assurance == "checked"
    assert outcome.axiom_footprint == ()
    assert outcome.proof_sha256 == "b" * 64
    assert outcome.export_sha256 and outcome.export_path


def test_every_outcome_is_recorded_on_the_deps_not_only_the_accepted_one(
    root: Path, monkeypatch
) -> None:
    """The defect this pins: an honest `retrieval-miss` was written as
    `operational-failure` because only the accepted branch appended, so the
    supervisor could not tell "the tool declined" from "the tool never ran"."""
    ctx = context(root)
    outcome = tools.modeq_family(ctx, "F:ml430-int-fib-add-181b6a2c")
    assert ctx.deps.producer_outcomes == [outcome]


def test_a_tier_c_call_is_recorded_in_the_call_log(root: Path, monkeypatch) -> None:
    monkeypatch.setattr(tools, "run_producer", lambda tool, export: STUB)
    ctx = context(root)
    tools.modeq_family(ctx, INDEX_FACT)
    assert [c.tool for c in ctx.deps.calls] == ["modeq_family"]
    assert ctx.deps.calls[0].exit_status == 0


# --------------------------------------------------------- independent re-check


def test_the_re_check_fails_on_a_tampered_proof_digest(root: Path, monkeypatch) -> None:
    monkeypatch.setattr(tools, "run_producer", lambda tool, export: STUB)
    verdict = tools.independent_check(root, INDEX_FACT, "modeq_family", "c" * 64)
    assert verdict.status == "failed"
    assert verdict.expected == "c" * 64
    assert verdict.actual == "b" * 64


def test_the_re_check_agrees_when_the_digest_is_the_one_produced(root: Path, monkeypatch) -> None:
    monkeypatch.setattr(tools, "run_producer", lambda tool, export: STUB)
    verdict = tools.independent_check(root, INDEX_FACT, "modeq_family", "b" * 64)
    assert verdict.status == "verified"
    assert verdict.axiom_footprint == ()


def test_the_re_check_reports_an_unavailable_export_as_failed_not_as_verified(
    root: Path,
) -> None:
    verdict = tools.independent_check(
        root, "F:ml430-int-fib-add-181b6a2c", "modeq_family", "b" * 64
    )
    assert verdict.status == "failed"
    assert "export unavailable" in verdict.reason


def test_the_re_check_reports_a_broken_producer_as_failed(root: Path, monkeypatch) -> None:
    def explode(tool, export):
        raise RuntimeError("no")

    monkeypatch.setattr(tools, "run_producer", explode)
    verdict = tools.independent_check(root, INDEX_FACT, "modeq_family", "b" * 64)
    assert verdict.status == "failed"


# --------------------------------------------- against the pinned exports only

_FROZEN = Path(
    "/nas3/data/axeyum/autogenesis/sources/mathlib-v4.30.0-modeq-family-v1/int-modeq-trans.ndjson"
)


@pytest.mark.skipif(
    not _FROZEN.is_file(), reason=f"pinned Mathlib export not on this host: {_FROZEN}"
)
def test_the_tool_reproduces_a_committed_manifest_digest(root: Path) -> None:
    """`Int.ModEq` transitivity, through the tool, against
    `mathlib-modeq-family-trans-v1.json`. This is what makes the tool's
    `proof_sha256` comparable to a manifest rather than merely similar to one."""
    outcome = tools.modeq_family(context(root), "F:ml430-int-modeq-trans-6d7863e0")
    assert isinstance(outcome, ProducerAccepted)
    assert outcome.proof_sha256 == FROZEN_MODEQ_TRANS_PROOF_SHA
    assert outcome.axiom_footprint == ()
    assert outcome.theorem_dependencies == ()


@pytest.mark.skipif(
    not _FROZEN.is_file(), reason=f"pinned Mathlib export not on this host: {_FROZEN}"
)
def test_a_second_kernel_re_derives_the_same_term(root: Path) -> None:
    """Two kernels agreeing, not one kernel consulted twice."""
    verdict = tools.independent_check(
        root, "F:ml430-int-modeq-trans-6d7863e0", "modeq_family", FROZEN_MODEQ_TRANS_PROOF_SHA
    )
    assert verdict.status == "verified"
    assert verdict.axiom_footprint == ()
