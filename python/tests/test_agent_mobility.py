"""Controls for the mobility census evaluator (`axeyum.agent.mobility`).

Every predicate kind the tactic-catalog schema enumerates is exercised against a
goal built by hand with `axeyum.kernel` constructors -- positive, negative, and
where the predicate has one, unevaluable. Hand-built goals, not imported ones,
because the four facts with a frozen export on this host all have the same
shape: a suite that only used them would leave most of the vocabulary
unmeasured and would report that as coverage.

The rule the whole file exists to hold: **the three-valued result must never
collapse.** `unmatched` and `unevaluable` are different findings -- one says the
goal violates the precondition, the other says nothing looked -- and a census
that merged them would report 187 never-inspected facts as a capability gap.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

import pytest

from axeyum.agent import mobility as M
from axeyum.kernel import Declaration, Kernel

ROOT = Path(__file__).resolve().parents[2]
SCHEMA = ROOT / "artifacts/ontology/tactic-catalog.schema.json"
NURSERY = ROOT / "artifacts/autogenesis/nursery-v1.json"


# ---------------------------------------------------------------------------
# Hand-built goals
# ---------------------------------------------------------------------------


class Fixture:
    """A kernel with the Nat prelude and helpers for building small goals."""

    def __init__(self) -> None:
        self.k = Kernel()
        self.k.build_nat_prelude()
        self.nat = self.k.const_(self.k.name("Nat", must_exist=True), [])
        self.zero = self.k.const_(self.k.name("Nat.zero", must_exist=True), [])
        self.succ_name = self.k.name("Nat.succ", must_exist=True)
        self.eq_name = self.k.name("Eq", must_exist=True)
        self.iff_name = self.k.name("Iff", must_exist=True)
        self.le_name = self.k.name("Nat.le", must_exist=True)
        self.level_one = self.k.level_succ(self.k.level_zero())

    def n(self, text: str):
        return self.k.name(text, must_exist=False)

    def succ(self, expr):
        return self.k.app(self.k.const_(self.succ_name, []), expr)

    def eq(self, lhs, rhs):
        head = self.k.const_(self.eq_name, [self.level_one])
        return self.k.app(self.k.app(self.k.app(head, self.nat), lhs), rhs)

    def le(self, parameter, index):
        head = self.k.const_(self.le_name, [])
        return self.k.app(self.k.app(head, parameter), index)

    def iff(self, left, right):
        head = self.k.const_(self.iff_name, [])
        return self.k.app(self.k.app(head, left), right)

    def pi(self, name: str, domain, body):
        return self.k.pi(self.n(name), domain, body)

    def view(self, goal) -> M.GoalView:
        return M.GoalView(self.k, goal)

    def bvar(self, index: int):
        return self.k.bvar(index)


@pytest.fixture(scope="module")
def fx() -> Fixture:
    return Fixture()


@pytest.fixture(scope="module")
def refl_goal(fx: Fixture):
    """`forall (n : Nat), n = n`."""
    return fx.pi("n", fx.nat, fx.eq(fx.bvar(0), fx.bvar(0)))


@pytest.fixture(scope="module")
def succ_goal(fx: Fixture):
    """`forall (n : Nat), succ n = n` -- an equation whose sides differ."""
    return fx.pi("n", fx.nat, fx.eq(fx.succ(fx.bvar(0)), fx.bvar(0)))


@pytest.fixture(scope="module")
def order_goal(fx: Fixture):
    """`forall (n : Nat), Nat.le n n` -- a Prop that is not an equation."""
    return fx.pi("n", fx.nat, fx.le(fx.bvar(0), fx.bvar(0)))


@pytest.fixture(scope="module")
def iff_goal(fx: Fixture):
    """`forall (n : Nat), Nat.le n n <-> Nat.le n n`."""
    body = fx.iff(fx.le(fx.bvar(0), fx.bvar(0)), fx.le(fx.bvar(0), fx.bvar(0)))
    return fx.pi("n", fx.nat, body)


@pytest.fixture(scope="module")
def absurd_goal(fx: Fixture):
    """`forall (n : Nat), Nat.le (succ n) zero -> n = n`.

    A le-shaped hypothesis at index `zero` with a `succ` parameter -- the shape
    `T:absurd-elimination` names, discovered structurally.
    """
    inner = fx.pi("h", fx.le(fx.succ(fx.bvar(0)), fx.zero), fx.eq(fx.bvar(1), fx.bvar(1)))
    return fx.pi("n", fx.nat, inner)


@pytest.fixture(scope="module")
def hypothesis_goal(fx: Fixture):
    """`forall (a b : Nat), a = b -> succ b = succ b`."""
    body = fx.pi(
        "h", fx.eq(fx.bvar(1), fx.bvar(0)), fx.eq(fx.succ(fx.bvar(1)), fx.succ(fx.bvar(1)))
    )
    return fx.pi("a", fx.nat, fx.pi("b", fx.nat, body))


@pytest.fixture(scope="module")
def hypothesis_goal_no_occurrence(fx: Fixture):
    """`forall (a b : Nat), a = b -> succ a = succ a` -- the hypothesis rhs is absent."""
    body = fx.pi(
        "h", fx.eq(fx.bvar(1), fx.bvar(0)), fx.eq(fx.succ(fx.bvar(2)), fx.succ(fx.bvar(2)))
    )
    return fx.pi("a", fx.nat, fx.pi("b", fx.nat, body))


@pytest.fixture(scope="module")
def closed_goal(fx: Fixture):
    """`zero = zero` -- no leading binder at all."""
    return fx.eq(fx.zero, fx.zero)


@pytest.fixture(scope="module")
def data_goal(fx: Fixture):
    """`forall (n : Nat), Nat` -- a conclusion that is not a proposition."""
    return fx.pi("n", fx.nat, fx.nat)


@pytest.fixture(scope="module")
def unfolding_goal(fx: Fixture):
    """`forall (n : Nat), Selfy n`, where `Selfy n` delta-reduces to `n = n`."""
    name = fx.n("Axeyum.Test.Selfy")
    prop = fx.k.sort(fx.k.level_zero())
    ty = fx.k.pi(fx.n("n"), fx.nat, prop)
    value = fx.k.lam(fx.n("n"), fx.nat, fx.eq(fx.bvar(0), fx.bvar(0)))
    fx.k.add_declaration(Declaration.definition(name, [], ty, value))
    head = fx.k.const_(name, [])
    return fx.pi("n", fx.nat, fx.k.app(head, fx.bvar(0)))


def verdict(view: M.GoalView, kind: str, **args) -> M.Verdict:
    return M.evaluate_predicate(view, {"kind": kind, "args": args})


# ---------------------------------------------------------------------------
# The three-valued result itself
# ---------------------------------------------------------------------------


def test_verdict_outcomes_are_the_three_named_states() -> None:
    assert M.matched().outcome == M.MATCHED
    assert M.unmatched("r").outcome == M.UNMATCHED
    assert M.unevaluable("r").outcome == M.UNEVALUABLE
    assert len({M.MATCHED, M.UNMATCHED, M.UNEVALUABLE}) == 3


def test_unmatched_without_a_reason_is_refused() -> None:
    with pytest.raises(M.MobilityError):
        M.unmatched("")


def test_unevaluable_without_a_reason_is_refused() -> None:
    with pytest.raises(M.MobilityError):
        M.unevaluable("")


def test_unevaluable_is_not_unmatched(fx: Fixture, refl_goal) -> None:
    """The distinction the whole census rests on, asserted directly."""
    view = fx.view(refl_goal)
    gap = verdict(view, "residual-gap-shape", shape="single-argument-diff")
    miss = verdict(view, "goal-head", head="Iff")
    assert gap.is_unevaluable and not gap.is_unmatched
    assert miss.is_unmatched and not miss.is_unevaluable
    assert gap.outcome != miss.outcome


# ---------------------------------------------------------------------------
# The predicate vocabulary is complete
# ---------------------------------------------------------------------------


def test_every_schema_predicate_kind_is_implemented() -> None:
    """An unimplemented kind would be silently skipped, i.e. reported satisfied."""
    schema = json.loads(SCHEMA.read_text(encoding="utf-8"))
    declared = {
        branch["properties"]["kind"]["const"] for branch in schema["$defs"]["predicate"]["oneOf"]
    }
    assert declared == set(M.PREDICATES)


def test_an_unknown_predicate_kind_raises_rather_than_passing(fx: Fixture, refl_goal) -> None:
    with pytest.raises(M.MobilityError):
        M.evaluate_predicate(fx.view(refl_goal), {"kind": "invented-predicate", "args": {}})


# ---------------------------------------------------------------------------
# goal-head
# ---------------------------------------------------------------------------


def test_goal_head_eq_matches_an_equation(fx: Fixture, refl_goal) -> None:
    assert verdict(fx.view(refl_goal), "goal-head", head="Eq").is_matched


def test_goal_head_eq_does_not_match_an_order_goal(fx: Fixture, order_goal) -> None:
    result = verdict(fx.view(order_goal), "goal-head", head="Eq")
    assert result.is_unmatched and result.reason == "goal-head-is-not-eq-shaped"


def test_goal_head_iff_matches_an_iff_goal(fx: Fixture, iff_goal) -> None:
    assert verdict(fx.view(iff_goal), "goal-head", head="Iff").is_matched


def test_goal_head_any_prop_matches_any_proposition(fx: Fixture, order_goal) -> None:
    assert verdict(fx.view(order_goal), "goal-head", head="any-prop").is_matched


def test_goal_head_any_prop_rejects_a_data_conclusion(fx: Fixture, data_goal) -> None:
    result = verdict(fx.view(data_goal), "goal-head", head="any-prop")
    assert result.is_unmatched and result.reason == "conclusion-is-not-a-proposition"


# ---------------------------------------------------------------------------
# sides-definitionally-equal
# ---------------------------------------------------------------------------


def test_sides_definitionally_equal_true(fx: Fixture, refl_goal) -> None:
    assert verdict(fx.view(refl_goal), "sides-definitionally-equal", value=True).is_matched


def test_sides_definitionally_equal_false_on_differing_sides(fx: Fixture, succ_goal) -> None:
    view = fx.view(succ_goal)
    assert verdict(view, "sides-definitionally-equal", value=False).is_matched
    assert verdict(view, "sides-definitionally-equal", value=True).is_unmatched


def test_sides_predicate_on_a_non_equation_is_unmatched_not_unevaluable(
    fx: Fixture, order_goal
) -> None:
    """The goal WAS inspected; it simply has no sides. That is a finding."""
    result = verdict(fx.view(order_goal), "sides-definitionally-equal", value=True)
    assert result.is_unmatched
    assert result.reason == "goal-is-not-an-equation-so-it-has-no-sides"


# ---------------------------------------------------------------------------
# binder-shape
# ---------------------------------------------------------------------------


def test_binder_shape_zero_succ_is_discovered_structurally(fx: Fixture, refl_goal) -> None:
    """Nat is matched because of its constructors, and nothing here names it."""
    assert verdict(fx.view(refl_goal), "binder-shape", shape="zero-succ").is_matched
    assert len(fx.view(refl_goal).env.shapes.zero_succ) >= 1


def test_binder_shape_hypothesis_pi_needs_a_proposition_binder(
    fx: Fixture, refl_goal, hypothesis_goal
) -> None:
    assert verdict(fx.view(hypothesis_goal), "binder-shape", shape="hypothesis-pi").is_matched
    miss = verdict(fx.view(refl_goal), "binder-shape", shape="hypothesis-pi")
    assert miss.is_unmatched and miss.reason == "no-leading-hypothesis-binder"


def test_binder_shape_on_a_goal_with_no_binder(fx: Fixture, closed_goal) -> None:
    result = verdict(fx.view(closed_goal), "binder-shape", shape="zero-succ")
    assert result.is_unmatched and result.reason == "goal-has-no-leading-pi-binder"


def test_binder_shape_ordinary_pi(fx: Fixture, refl_goal) -> None:
    assert verdict(fx.view(refl_goal), "binder-shape", shape="ordinary-pi").is_matched


# ---------------------------------------------------------------------------
# hypothesis-family
# ---------------------------------------------------------------------------


def test_hypothesis_family_le_shaped_at_zero_index_succ_parameter(fx: Fixture, absurd_goal) -> None:
    result = verdict(
        fx.view(absurd_goal),
        "hypothesis-family",
        family="le-shaped",
        index="zero",
        parameter="succ",
    )
    assert result.is_matched


def test_hypothesis_family_rejects_the_wrong_index(fx: Fixture, absurd_goal) -> None:
    result = verdict(
        fx.view(absurd_goal),
        "hypothesis-family",
        family="le-shaped",
        index="succ",
        parameter="any",
    )
    assert result.is_unmatched
    assert result.reason == "hypothesis-le-shaped-index-or-parameter-mismatch"


def test_hypothesis_family_with_no_hypothesis_at_all(fx: Fixture, refl_goal) -> None:
    result = verdict(
        fx.view(refl_goal), "hypothesis-family", family="le-shaped", index="any", parameter="any"
    )
    assert result.is_unmatched and result.reason == "no-hypothesis-binder-to-classify"


def test_hypothesis_family_eq_shaped(fx: Fixture, hypothesis_goal) -> None:
    result = verdict(
        fx.view(hypothesis_goal),
        "hypothesis-family",
        family="eq-shaped",
        index="any",
        parameter="any",
    )
    assert result.is_matched


# ---------------------------------------------------------------------------
# hypothesis-state
# ---------------------------------------------------------------------------


def test_hypothesis_state_absent_on_a_goal_with_no_hypothesis(fx: Fixture, refl_goal) -> None:
    assert verdict(fx.view(refl_goal), "hypothesis-state", state="absent").is_matched


def test_hypothesis_state_available_when_an_equation_hypothesis_agrees(
    fx: Fixture, hypothesis_goal
) -> None:
    view = fx.view(hypothesis_goal)
    assert verdict(view, "hypothesis-state", state="available").is_matched
    assert verdict(view, "hypothesis-state", state="absent").is_unmatched


def test_hypothesis_state_available_is_unmatched_without_one(fx: Fixture, refl_goal) -> None:
    result = verdict(fx.view(refl_goal), "hypothesis-state", state="available")
    assert result.is_unmatched and result.reason == "no-equation-shaped-hypothesis"


def test_hypothesis_state_stuck_is_the_negation_of_agreement(fx: Fixture, hypothesis_goal) -> None:
    result = verdict(fx.view(hypothesis_goal), "hypothesis-state", state="stuck")
    assert result.is_unmatched and result.reason == "hypothesis-agrees-so-it-is-not-stuck"


# ---------------------------------------------------------------------------
# occurrence-embeds
# ---------------------------------------------------------------------------


def test_occurrence_embeds_finds_a_hypothesis_side_in_the_goal(
    fx: Fixture, hypothesis_goal
) -> None:
    result = verdict(
        fx.view(hypothesis_goal),
        "occurrence-embeds",
        needle="hypothesis-rhs",
        haystack="goal-rhs-whnf",
        via="kabstract-occurrences",
    )
    assert result.is_matched


def test_occurrence_embeds_reports_absence(fx: Fixture, hypothesis_goal_no_occurrence) -> None:
    result = verdict(
        fx.view(hypothesis_goal_no_occurrence),
        "occurrence-embeds",
        needle="hypothesis-rhs",
        haystack="goal-rhs-whnf",
        via="kabstract-occurrences",
    )
    assert result.is_unmatched
    assert result.reason == "needle-does-not-occur-in-haystack-via-kabstract-occurrences"


def test_occurrence_embeds_app_spine_is_narrower_than_kabstract(
    fx: Fixture, hypothesis_goal
) -> None:
    view = fx.view(hypothesis_goal)
    assert verdict(
        view,
        "occurrence-embeds",
        needle="hypothesis-rhs",
        haystack="goal-rhs-whnf",
        via="app-spine",
    ).is_matched


def test_occurrence_embeds_mid_derivation_sites_are_unevaluable(
    fx: Fixture, hypothesis_goal
) -> None:
    result = verdict(
        fx.view(hypothesis_goal),
        "occurrence-embeds",
        needle="candidate-argument",
        haystack="expected-argument",
        via="kabstract-occurrences",
    )
    assert result.is_unevaluable and result.reason == M.MID_DERIVATION


# ---------------------------------------------------------------------------
# residual-gap-shape, spine-argument-matches, head-unfolds
# ---------------------------------------------------------------------------


def test_residual_gap_shape_is_always_unevaluable_at_the_initial_goal(
    fx: Fixture, refl_goal
) -> None:
    for shape in (
        "single-argument-diff",
        "multi-argument-diff-same-head",
        "collapsed-occurrence-site",
    ):
        result = verdict(fx.view(refl_goal), "residual-gap-shape", shape=shape)
        assert result.is_unevaluable and result.reason == M.MID_DERIVATION


def test_spine_argument_matches_finds_the_rhs_in_the_lhs_spine(fx: Fixture, succ_goal) -> None:
    result = verdict(
        fx.view(succ_goal), "spine-argument-matches", position="any-top-level", target="goal-rhs"
    )
    assert result.is_matched


def test_spine_argument_matches_reports_a_miss(fx: Fixture, refl_goal) -> None:
    result = verdict(
        fx.view(refl_goal), "spine-argument-matches", position="any-top-level", target="goal-rhs"
    )
    assert result.is_unmatched
    assert result.reason == "goal-lhs-has-no-top-level-arguments"


def test_head_unfolds_through_a_definition(fx: Fixture, unfolding_goal) -> None:
    result = verdict(fx.view(unfolding_goal), "head-unfolds", via="whnf-delta", to="Eq")
    assert result.is_matched


def test_head_unfolds_reports_a_head_that_does_not_reach_eq(fx: Fixture, order_goal) -> None:
    result = verdict(fx.view(order_goal), "head-unfolds", via="whnf-delta", to="Eq")
    assert result.is_unmatched and result.reason == "goal-does-not-unfold-to-an-eq-shaped-head"


# ---------------------------------------------------------------------------
# Tactic aggregation
# ---------------------------------------------------------------------------


def test_all_of_aggregation_prefers_unmatched_over_unevaluable(fx: Fixture, order_goal) -> None:
    tactic = {
        "id": "T:test",
        "precondition": {
            "description": "d",
            "structural": {
                "all_of": [
                    {"kind": "goal-head", "args": {"head": "Eq"}},
                    {"kind": "residual-gap-shape", "args": {"shape": "single-argument-diff"}},
                ]
            },
        },
    }
    outcome = M.evaluate_tactic(fx.view(order_goal), tactic)
    assert outcome.verdict.is_unmatched


def test_all_of_aggregation_is_unevaluable_when_nothing_is_violated(fx: Fixture, refl_goal) -> None:
    tactic = {
        "id": "T:test",
        "precondition": {
            "description": "d",
            "structural": {
                "all_of": [
                    {"kind": "goal-head", "args": {"head": "Eq"}},
                    {"kind": "residual-gap-shape", "args": {"shape": "single-argument-diff"}},
                ]
            },
        },
    }
    outcome = M.evaluate_tactic(fx.view(refl_goal), tactic)
    assert outcome.verdict.is_unevaluable and outcome.verdict.reason == M.MID_DERIVATION


def test_a_tactic_without_a_precondition_is_refused(fx: Fixture, refl_goal) -> None:
    with pytest.raises(M.MobilityError):
        M.evaluate_tactic(fx.view(refl_goal), {"id": "T:empty", "precondition": {}})


def test_the_committed_catalog_evaluates_end_to_end(fx: Fixture, refl_goal) -> None:
    """Every committed tactic answers with one of the three states, and none raises."""
    tactics, _ = M.load_catalog(ROOT)
    view = fx.view(refl_goal)
    outcomes = [M.evaluate_tactic(view, tactic) for tactic in tactics]
    assert len(outcomes) == len(tactics) >= 8
    assert {o.verdict.outcome for o in outcomes} <= {M.MATCHED, M.UNMATCHED, M.UNEVALUABLE}
    assert any(o.verdict.is_matched for o in outcomes)


# ---------------------------------------------------------------------------
# Goal shapes
# ---------------------------------------------------------------------------


def test_canonical_shape_erases_binder_names(fx: Fixture) -> None:
    left = fx.k.pi(fx.n("n"), fx.nat, fx.eq(fx.bvar(0), fx.bvar(0)))
    right = fx.k.pi(fx.n("hygienic._@._internal._hyg._0"), fx.nat, fx.eq(fx.bvar(0), fx.bvar(0)))
    assert M.shape_sha256(fx.k, left) == M.shape_sha256(fx.k, right)


def test_canonical_shape_separates_different_goals(fx: Fixture, refl_goal, succ_goal) -> None:
    assert M.shape_sha256(fx.k, refl_goal) != M.shape_sha256(fx.k, succ_goal)


# ---------------------------------------------------------------------------
# Held-out isolation
# ---------------------------------------------------------------------------


def held_out_sample() -> str:
    document = json.loads(NURSERY.read_text(encoding="utf-8"))
    ids = sorted(
        entry["fact_id"] for entry in document["entries"] if entry.get("partition") == "held-out"
    )
    assert ids, "the nursery declares no held-out rows; this control would be vacuous"
    return ids[0]


def test_assert_no_held_out_raises_on_a_leak() -> None:
    """The positive control: the guard must actually fire."""
    leaked = held_out_sample()
    with pytest.raises(M.MobilityError):
        M.assert_no_held_out({"facts": [{"fact_id": leaked}]}, {leaked})


def test_assert_no_held_out_passes_a_clean_document() -> None:
    leaked = held_out_sample()
    M.assert_no_held_out({"facts": [{"fact_id": "F:not-held-out"}]}, {leaked})


def test_the_committed_census_names_no_held_out_fact() -> None:
    census = json.loads((ROOT / M.CENSUS_PATH).read_text(encoding="utf-8"))
    document = json.loads(NURSERY.read_text(encoding="utf-8"))
    held_out = {
        entry["fact_id"] for entry in document["entries"] if entry.get("partition") == "held-out"
    }
    assert held_out
    text = json.dumps(census, sort_keys=True)
    assert not [fact_id for fact_id in held_out if fact_id in text]
    assert census["totals"]["held_out_excluded"] > 0


# ---------------------------------------------------------------------------
# Census plumbing
# ---------------------------------------------------------------------------


CENSUS_LINE = re.compile(
    r"^MOBILITY\|open=(\d+)\|evaluable=(\d+)\|unevaluable=(\d+)"
    r"\|unevaluable_no_export=(\d+)\|unevaluable_top=[^|]+\|tactics=(\d+)"
    r"\|matched_pairs=(\d+)\|zero_match_facts=(\d+)\|clusters=(\d+)\|held_out_excluded=(\d+)$"
)


def test_census_line_parses_and_the_numbers_add_up() -> None:
    census = json.loads((ROOT / M.CENSUS_PATH).read_text(encoding="utf-8"))
    match = CENSUS_LINE.match(M.census_line(census))
    assert match is not None
    open_facts, evaluable, unevaluable = (int(match.group(i)) for i in (1, 2, 3))
    assert evaluable + unevaluable == open_facts
    assert evaluable > 0


def test_build_clusters_ignores_unevaluable_rows() -> None:
    rows = [
        {"fact_id": "F:a", "evaluable": True, "mobility": 0, "unmatched": {"T:x": "r1"}},
        {"fact_id": "F:b", "evaluable": True, "mobility": 0, "unmatched": {"T:x": "r1"}},
        {"fact_id": "F:c", "evaluable": True, "mobility": 1, "unmatched": {"T:x": "r1"}},
        {"fact_id": "F:d", "evaluable": False, "mobility": 0, "unmatched": {}},
    ]
    clusters = M.build_clusters(rows)
    assert len(clusters) == 1
    assert clusters[0]["size"] == 2
    assert clusters[0]["fact_ids"] == ["F:a", "F:b"]


def test_load_goal_for_an_unknown_fact_is_unevaluable_not_unmatched() -> None:
    source = M.load_goal(ROOT, "F:no-such-fact-anywhere")
    assert not source.evaluable
    assert source.reason == "no-frozen-export"


def test_must_decline_population_is_derived_and_non_held_out() -> None:
    ids = M.must_decline_ids(ROOT)
    document = json.loads(NURSERY.read_text(encoding="utf-8"))
    partitions = {entry["fact_id"]: entry.get("partition") for entry in document["entries"]}
    # Derived from the nursery, not a literal: the must-decline population
    # grows as mutation fixtures are registered, so pin it to its source.
    nursery = json.loads((ROOT / "artifacts/autogenesis/nursery-v1.json").read_text())
    expected = {
        e["fact_id"]
        for e in nursery["entries"]
        if e.get("provenance_class") == "generated-mutation" and e["partition"] != "held-out"
    }
    assert set(ids) == expected
    assert all(partitions[fact_id] != "held-out" for fact_id in ids)


def test_open_facts_are_only_open_facts() -> None:
    facts = M.open_facts(ROOT)
    assert facts
    assert all(fact.is_open for fact in facts)


def test_reach_cross_check_reports_scope_and_never_forces_a_verdict() -> None:
    rows = M.reach_cross_check(ROOT)
    assert rows
    assert all(row["outcome"] in {M.MATCHED, M.UNMATCHED, M.UNEVALUABLE} for row in rows)
    for row in rows:
        if row["outcome"] == M.UNEVALUABLE:
            assert row["agrees"] is None
    evaluable = [row for row in rows if row["outcome"] != M.UNEVALUABLE]
    if evaluable:
        assert any(row["agrees"] is True for row in evaluable)
    else:
        assert all(row["agrees"] is None for row in rows)


def test_census_line_surfaces_the_dominant_unevaluable_reason() -> None:
    """The summary line must make an unevaluable count legible as reachability
    vs a tactic gap -- the whole point of the three-valued result."""
    census = {
        "totals": {
            "open_facts": 189,
            "evaluable": 3,
            "unevaluable": 186,
            "tactics": 9,
            "matched_pairs": 2,
            "zero_match_facts": 1,
            "clusters": 1,
            "held_out_excluded": 37,
        },
        "unevaluable_reasons": {
            "no-frozen-export": 184,
            "statement-import-failed:StatementImportError": 2,
        },
    }
    line = M.census_line(census)
    assert "unevaluable=186" in line
    assert "unevaluable_no_export=184" in line
    assert "unevaluable_top=no-frozen-export:184" in line


def test_census_line_tolerates_no_unevaluable_reasons() -> None:
    census = {
        "totals": {
            "open_facts": 3,
            "evaluable": 3,
            "unevaluable": 0,
            "tactics": 9,
            "matched_pairs": 2,
            "zero_match_facts": 0,
            "clusters": 1,
            "held_out_excluded": 0,
        },
        "unevaluable_reasons": {},
    }
    line = M.census_line(census)
    assert "unevaluable_no_export=0" in line
    assert "unevaluable_top=none:0" in line
