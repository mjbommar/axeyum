"""`axeyum.cas.certify` -- one producer/checker pair per route.

Every route is tested the same four ways, and the second is the load-bearing
one:

a. a fixture certifies and ``check()`` verifies **with every report count > 0**;
b. a **tampered** certificate is rejected -- the checker is shown to fail, because
   a checker that has never been observed to reject is indistinguishable from
   one that returns ``True``;
c. the crate's own committed JSON artifacts round-trip **byte-identically**;
d. a starved budget returns the **typed decline**, not an exception, and not a
   verdict about the theorem.
"""

from __future__ import annotations

import pathlib
import re
from fractions import Fraction

import pytest

from axeyum._native import cas
from axeyum._native.cas import certify
from axeyum._native.cas.certify import geometry, gf2, groebner, sos, sturm, telescoping

REPO = pathlib.Path(__file__).resolve().parents[2]
GEOMETRY_DIR = REPO / "artifacts/geometry-certificates"
TELESCOPING_DIR = REPO / "artifacts/cas-certificates"
SOS_DIR = REPO / "artifacts/sos-certificates"


def _fixture_names(directory: pathlib.Path) -> list[str]:
    names = sorted(path.name for path in directory.glob("*.json"))
    assert names, f"{directory} is empty; a suite over it would examine nothing"
    return names


GEOMETRY_FIXTURES = _fixture_names(GEOMETRY_DIR)
TELESCOPING_FIXTURES = _fixture_names(TELESCOPING_DIR)
SOS_FIXTURES = _fixture_names(SOS_DIR)


_NUMERATOR = re.compile(r'"(?:coefficient|weight)": \[(-?\d+), (\d+)\]')


def _tamper(text: str, after: str) -> str:
    """Bumps the first exact-rational numerator occurring after `after`.

    Every certificate format in this crate writes a rational as `[num, den]`, so
    one regex covers all three. The assertion that the text actually changed is
    part of the control: a tamper that silently edited nothing would make the
    "rejected" test pass for the wrong reason.
    """
    index = text.index(after)
    match = _NUMERATOR.search(text, index)
    assert match is not None, f"no rational to perturb after {after!r}"
    bumped = f'"coefficient": [{int(match.group(1)) + 1}, {match.group(2)}]'
    bumped = (
        match.group(0).split(":")[0]
        + ": ["
        + str(int(match.group(1)) + 1)
        + ", "
        + match.group(2)
        + "]"
    )
    tampered = text[: match.start()] + bumped + text[match.end() :]
    assert tampered != text, "the tamper changed nothing"
    return tampered


_CONCLUSION_POLY = re.compile(r'"poly": (\{"terms": \[.*?\]\})(, "cofactors")')


def _forge_geometry_conclusion(text: str) -> str:
    """Rewrites the first conclusion to claim the constant `1`.

    A bumped coefficient does not work uniformly: `varignon-midpoint-
    parallelogram` proves two conclusions whose polynomials are *identically
    zero* with empty cofactor lists, so there is no coefficient in them to
    perturb. Claiming `1` instead is a forgery every certificate must reject,
    because no cofactor combination of the generators reproduces a nonzero
    constant.
    """
    index = text.index('"conclusions"')
    match = _CONCLUSION_POLY.search(text, index)
    assert match is not None, "no conclusion polynomial to forge"
    forged = '"poly": {"terms": [{"monomial": [], "coefficient": [1, 1]}]}' + match.group(2)
    tampered = text[: match.start()] + forged + text[match.end() :]
    assert tampered != text, "the forgery changed nothing"
    return tampered


# ==========================================================================
# module shape
# ==========================================================================


@pytest.mark.parametrize("name", ["geometry", "gf2", "groebner", "sos", "sturm", "telescoping"])
def test_route_is_importable_by_name(name: str) -> None:
    module = __import__(f"axeyum._native.cas.certify.{name}", fromlist=["_"])
    assert module is getattr(certify, name)


# ==========================================================================
# groebner -- cofactor-tracked ideal membership
# ==========================================================================


def _poly(name: str) -> cas.MvPoly:
    return cas.MvPoly.var(name)


def _circle_system() -> tuple[list[cas.MvPoly], cas.MvPoly]:
    """`x**2 - 1` and `y - x` generate an ideal containing `y**2 - 1`."""
    x, y, one = _poly("x"), _poly("y"), cas.MvPoly.constant(1)
    return [x.mul(x).sub(one), y.sub(x)], y.mul(y).sub(one)


def test_groebner_limits_quote_the_fast_defaults() -> None:
    fast = groebner.Limits.fast()
    assert (fast.reduction_steps, fast.pair_iterations) == (20_000, 4_000)
    assert (fast.basis_size, fast.poly_terms, fast.order) == (64, 512, "lex")
    assert groebner.Limits().reduction_steps == fast.reduction_steps


def test_groebner_limits_reject_an_unknown_order() -> None:
    with pytest.raises(ValueError):
        groebner.Limits(order="grlex")


def test_groebner_reduces_and_the_identity_re_expands() -> None:
    generators, target = _circle_system()
    outcome = groebner.reduce_with_cofactors(generators, target)
    assert outcome.kind == "Reduced"
    assert outcome.in_ideal() is True
    assert len(outcome.cofactors) == len(generators)
    assert outcome.remainder.is_zero()
    assert outcome.check(generators, target) is True


def test_groebner_check_rejects_a_tampered_cofactor() -> None:
    generators, target = _circle_system()
    outcome = groebner.reduce_with_cofactors(generators, target)
    cofactors = list(outcome.cofactors)
    cofactors[0] = cofactors[0].add(cas.MvPoly.constant(1))
    assert groebner.check_identity(cofactors, outcome.remainder, generators, target) is False
    # ...and the untampered list still passes, so the checker is not simply
    # rejecting everything.
    assert (
        groebner.check_identity(list(outcome.cofactors), outcome.remainder, generators, target)
        is True
    )


def test_groebner_check_rejects_a_tampered_remainder() -> None:
    generators, target = _circle_system()
    outcome = groebner.reduce_with_cofactors(generators, target)
    bad = outcome.remainder.add(cas.MvPoly.constant(1))
    assert groebner.check_identity(outcome.cofactors, bad, generators, target) is False


def test_groebner_check_rejects_an_arity_mismatch() -> None:
    generators, target = _circle_system()
    outcome = groebner.reduce_with_cofactors(generators, target)
    assert (
        groebner.check_identity(outcome.cofactors[:1], outcome.remainder, generators, target)
        is False
    )


def test_groebner_check_rejects_a_short_cofactor_list_that_still_sums_right() -> None:
    """The arity guard, tested where arithmetic alone cannot catch it.

    A short cofactor list zips against a prefix of the generators, so the sum can
    still equal the target -- here `1 * (x - 1)` reproduces `x - 1` while the
    second generator goes unmentioned. Without the length check the identity
    "holds" and a certificate that never spoke about `y - 1` is accepted. This is
    the case that kills the guard; the mismatch test above passes for arithmetic
    reasons and survives its deletion.
    """
    x, y, one = _poly("x"), _poly("y"), cas.MvPoly.constant(1)
    generators = [x.sub(one), y.sub(one)]
    target = x.sub(one)
    assert groebner.check_identity([one], cas.MvPoly.zero(), generators, target) is False
    # Positive control: naming BOTH generators, with a zero cofactor for the
    # unused one, is the same arithmetic and is accepted.
    assert (
        groebner.check_identity([one, cas.MvPoly.zero()], cas.MvPoly.zero(), generators, target)
        is True
    )


def test_groebner_check_rejects_a_long_cofactor_list() -> None:
    """The same guard from the other side.

    Extra cofactors are truncated by `zip`, so a list claiming more generators
    than exist must be refused on shape rather than on arithmetic.
    """
    x, one = _poly("x"), cas.MvPoly.constant(1)
    generators = [x.sub(one)]
    target = x.sub(one)
    assert (
        groebner.check_identity(
            [one, cas.MvPoly.constant(5)], cas.MvPoly.zero(), generators, target
        )
        is False
    )


def test_groebner_non_member_leaves_a_nonzero_remainder() -> None:
    x, one = _poly("x"), cas.MvPoly.constant(1)
    generators = [x.mul(x).sub(one)]
    target = x.add(cas.MvPoly.constant(2))
    outcome = groebner.reduce_with_cofactors(generators, target)
    assert outcome.kind == "Reduced"
    assert outcome.in_ideal() is False
    assert not outcome.remainder.is_zero()
    # The identity still holds -- membership is what fails, not the arithmetic.
    assert outcome.check(generators, target) is True


def test_groebner_starved_budget_declines_with_a_ceiling_reason() -> None:
    x, y = _poly("x"), _poly("y")
    generators = [
        x.pow(4).sub(y.pow(3)),
        y.pow(4).sub(x.pow(3)),
        x.mul(y).sub(cas.MvPoly.constant(1)),
    ]
    tiny = groebner.Limits(reduction_steps=1, pair_iterations=1, basis_size=1, poly_terms=1)
    outcome = groebner.reduce_with_cofactors(generators, x.pow(9), tiny)
    assert outcome.kind == "Declined"
    assert outcome.reason.is_ceiling() is True
    assert outcome.reason.name in {
        "ReductionSteps",
        "PairIterations",
        "BasisSize",
        "PolyTerms",
    }


def test_groebner_decline_claims_nothing_about_membership() -> None:
    x = _poly("x")
    tiny = groebner.Limits(basis_size=1)
    outcome = groebner.reduce_with_cofactors([x.pow(4), x.pow(3), x.pow(2)], x.pow(9), tiny)
    if outcome.kind == "Declined":
        assert outcome.in_ideal() is None  # NOT False
        assert outcome.cofactors is None
        assert outcome.remainder is None
        assert outcome.check([x.pow(4)], x) is False


def test_groebner_unit_ideal_cofactors() -> None:
    x = _poly("x")
    generators = [x, x.add(cas.MvPoly.constant(1))]
    outcome = groebner.unit_ideal_cofactors(generators)
    assert outcome.kind in {"Reduced", "Declined"}
    if outcome.kind == "Reduced":
        assert outcome.check(generators, cas.MvPoly.constant(1)) is True


def test_groebner_reduce_many_reports_stats() -> None:
    generators, target = _circle_system()
    outcomes, stats = groebner.reduce_many_with_cofactors(generators, [target, target])
    assert len(outcomes) == 2
    assert all(outcome.in_ideal() for outcome in outcomes)
    assert stats.pairs_queued >= stats.pairs_processed
    assert stats.max_basis_len >= len(generators)


# ==========================================================================
# geometry
# ==========================================================================

# `rhombus-diagonals-perpendicular` is deliberately absent: it takes ~98 s to
# certify on this machine, and the fixture round-trip below covers it anyway.
FAST_GEOMETRY = [
    "varignon-midpoint-parallelogram",
    "thales-right-angle-in-semicircle",
    "orthocentre-altitudes-concurrent",
    "medians-concurrent",
    "centroid-divides-medians",
    "parallelogram-diagonals-bisect",
    "euler-line",
    "pappus-hexagon",
    "simson-line",
]

# The counts a report must show as nonzero. `degenerate_witnesses_checked` and
# `conditions_used` are nonzero only for a theorem that HAS a non-degeneracy
# condition, so the five-count test below picks one that does.
FIVE_COUNT_PROBLEM = "centroid-divides-medians"


def _problem(problem_id: str) -> geometry.GeometryProblem:
    for problem in geometry.corpus():
        if problem.id == problem_id:
            return problem
    raise AssertionError(f"{problem_id} is not in the corpus")


def test_geometry_corpus_is_not_empty() -> None:
    corpus = geometry.corpus()
    assert len(corpus) >= 10
    assert all(problem.hypotheses or problem.conclusions for problem in corpus)


def test_geometry_frontier_is_readable() -> None:
    # Empty today; the accessor must still exist and answer.
    assert isinstance(geometry.frontier(), list)


def test_geometry_limits_default_to_degrevlex() -> None:
    limits = geometry.geometry_limits()
    assert limits.order == "degrevlex"
    assert limits.reduction_steps > 0


@pytest.mark.parametrize("problem_id", FAST_GEOMETRY)
def test_geometry_corpus_problem_certifies_and_verifies(problem_id: str) -> None:
    outcome = geometry.certify_any_route(_problem(problem_id))
    assert outcome.kind == "Certified", outcome
    verdict = outcome.certificate.check()
    assert verdict.kind == "Verified", verdict.reason
    report = verdict.report
    assert report.conclusions_checked > 0
    assert report.generic_witnesses_checked > 0
    assert report.numeric_points_checked > 0


def test_geometry_report_shows_all_five_counts_nonzero() -> None:
    outcome = geometry.certify_any_route(_problem(FIVE_COUNT_PROBLEM))
    report = outcome.certificate.check().report
    assert report.conclusions_checked > 0
    assert report.degenerate_witnesses_checked > 0
    assert report.generic_witnesses_checked > 0
    assert report.numeric_points_checked > 0
    assert len(report.conditions_used) > 0


def test_geometry_check_options_default_and_scale_the_numeric_replay() -> None:
    options = geometry.CheckOptions()
    assert (options.numeric_points, options.half_range) == (24, 6)
    outcome = geometry.certify_any_route(_problem("thales-right-angle-in-semicircle"))
    report = outcome.certificate.check(geometry.CheckOptions(numeric_points=5)).report
    assert report.numeric_points_checked == 5


@pytest.mark.parametrize("name", GEOMETRY_FIXTURES)
def test_geometry_fixture_round_trips_byte_identically(name: str) -> None:
    text = (GEOMETRY_DIR / name).read_text()
    certificate = geometry.GeometryCertificate.from_json(text)
    assert certificate.to_json() == text


@pytest.mark.parametrize("name", GEOMETRY_FIXTURES)
def test_geometry_fixture_verifies(name: str) -> None:
    certificate = geometry.GeometryCertificate.from_json((GEOMETRY_DIR / name).read_text())
    verdict = certificate.check()
    assert verdict.is_verified(), verdict.reason
    assert verdict.report.conclusions_checked > 0


@pytest.mark.parametrize("name", GEOMETRY_FIXTURES)
def test_geometry_tampered_coefficient_is_rejected(name: str) -> None:
    text = (GEOMETRY_DIR / name).read_text()
    tampered = _forge_geometry_conclusion(text)
    verdict = geometry.GeometryCertificate.from_json(tampered).check()
    assert verdict.kind == "Rejected"
    assert verdict.reason
    assert verdict.report is None


def test_geometry_malformed_json_raises_cas_error() -> None:
    with pytest.raises(cas.CasError):
        geometry.GeometryCertificate.from_json("{}")


def test_geometry_starved_budget_declines_with_a_typed_reason() -> None:
    tiny = groebner.Limits(
        reduction_steps=1,
        pair_iterations=1,
        basis_size=1,
        poly_terms=1,
        order="degrevlex",
    )
    outcome = geometry.certify(_problem("simson-line"), tiny)
    assert outcome.kind == "Declined"
    decline = outcome.decline
    assert decline.name == "Reduction"
    assert decline.reduction_reason is not None
    assert decline.is_refuted_by_own_witness() is False
    assert outcome.certificate is None


def test_geometry_false_statement_is_not_in_the_saturated_ideal() -> None:
    a, b, c = geometry.Pt.free("a"), geometry.Pt.free("b"), geometry.Pt.free("c")
    claim = geometry.collinear(a, b, c)
    problem = geometry.GeometryProblem(
        id="three-free-points-are-collinear",
        title="a deliberately false statement",
        statement="Three unconstrained points are collinear. They are not.",
        hypotheses=[],
        conclusions=[geometry.Constraint("collinear", "abc collinear", claim)],
    )
    outcome = geometry.certify_any_route(problem)
    assert outcome.kind in {"NotInSaturatedIdeal", "Declined"}
    if outcome.kind == "NotInSaturatedIdeal":
        assert outcome.conclusion_id == "collinear"
        assert not outcome.remainder.is_zero()
        assert outcome.certificate is None


def test_geometry_point_dsl() -> None:
    a = geometry.Pt.free("a")
    b = geometry.Pt.fixed(Fraction(1), Fraction(0))
    assert geometry.dist_sq(a, b) is not None
    assert geometry.det(a, b) is not None
    assert geometry.dot(a, b) is not None
    assert geometry.midpoint(a, b) is not None
    assert geometry.centroid(a, b, geometry.Pt.free("c")) is not None
    assert len(geometry.same_point(a, b)) == 2
    assert a.sub(b) is not None
    assert a.add(b) is not None
    assert a.scale(Fraction(1, 2)) is not None


def test_geometry_predicates_over_four_points() -> None:
    points = [geometry.Pt.free(name) for name in "abcd"]
    assert geometry.parallel(*points) is not None
    assert geometry.perpendicular(*points) is not None
    assert geometry.equidistant(*points) is not None
    assert geometry.concyclic(*points) is not None
    assert geometry.collinear(*points[:3]) is not None


def test_geometry_constants() -> None:
    assert geometry.INVERSE_PREFIX == "Zinv"
    assert geometry.FORMAT == "axeyum-geometry-certificate"
    assert geometry.VERSION == 1


def test_geometry_certificate_exposes_its_cofactors() -> None:
    outcome = geometry.certify_any_route(_problem("thales-right-angle-in-semicircle"))
    certificate = outcome.certificate
    assert certificate.generators
    conclusions = certificate.conclusion_cofactors
    assert conclusions
    for _, cofactors in conclusions:
        assert len(cofactors) == len(certificate.generators)


# ==========================================================================
# telescoping
# ==========================================================================


def _binomial_row_sum() -> telescoping.HyperTerm:
    """The summand of `sum_k C(n, k) = 2**n`."""
    n = telescoping.LinearForm([("n", 1)])
    k = telescoping.LinearForm([("k", 1)])
    return telescoping.HyperTerm(telescoping.binomial_factors(n, k, 1))


def _binomial_options() -> telescoping.CheckOptions:
    return telescoping.CheckOptions.over("n", [3, 4, 5, 6, 7], (-2, 12)).with_("k", [0, 1, 2, 3])


def test_telescoping_limits_quote_the_classical_defaults() -> None:
    classical = telescoping.Limits.classical()
    assert classical.max_order == 2
    assert classical.max_certificate_degree == 8
    assert classical.max_unknowns == 400
    assert classical.max_poly_terms == 4_000
    assert classical.max_dispersion == 32
    assert classical.max_parameter_degree == 6
    assert telescoping.Limits().max_order == classical.max_order


def test_telescoping_finds_and_verifies_with_nonzero_counts() -> None:
    outcome = telescoping.zeilberger(_binomial_row_sum(), "n", "k")
    assert outcome.kind == "Found"
    certificate = outcome.certificate
    assert certificate.order() >= 1
    verdict = certificate.check(_binomial_options())
    assert verdict.kind == "Verified", verdict.reasons
    report = verdict.report
    assert report.ratio_samples > 0
    assert report.pointwise_samples > 0
    assert report.recurrence_samples > 0


def test_telescoping_certificate_parts_are_reachable() -> None:
    certificate = telescoping.zeilberger(_binomial_row_sum(), "n", "k").certificate
    assert certificate.shift_var == "n"
    assert certificate.sum_var == "k"
    assert len(certificate.recurrence) == certificate.order() + 1
    assert certificate.certificate_numerator is not None
    assert not certificate.certificate_denominator.is_zero()
    assert len(certificate.term.factors) == 3


def test_telescoping_starved_budget_declines() -> None:
    starved = telescoping.Limits(
        max_order=1,
        max_certificate_degree=0,
        max_unknowns=1,
        max_poly_terms=1,
        max_dispersion=1,
        max_parameter_degree=0,
    )
    outcome = telescoping.zeilberger(_binomial_row_sum(), "n", "k", starved)
    assert outcome.kind == "Declined"
    assert outcome.certificate is None


@pytest.mark.parametrize("name", TELESCOPING_FIXTURES)
def test_telescoping_fixture_round_trips_byte_identically(name: str) -> None:
    text = (TELESCOPING_DIR / name).read_text()
    document = telescoping.CertificateDocument.from_json(text)
    assert document.to_json() == text


@pytest.mark.parametrize("name", TELESCOPING_FIXTURES)
def test_telescoping_fixture_verifies_with_nonzero_counts(name: str) -> None:
    document = telescoping.CertificateDocument.from_json((TELESCOPING_DIR / name).read_text())
    verdict = document.certificate.check(document.options)
    assert verdict.is_verified(), verdict.reasons
    report = verdict.report
    assert report.ratio_samples > 0
    assert report.recurrence_samples > 0


@pytest.mark.parametrize("name", TELESCOPING_FIXTURES)
def test_telescoping_tampered_certificate_is_rejected(name: str) -> None:
    text = (TELESCOPING_DIR / name).read_text()
    tampered = _tamper(text, '"certificate_numerator"')
    document = telescoping.CertificateDocument.from_json(tampered)
    verdict = document.certificate.check(document.options)
    assert verdict.kind == "Rejected"
    assert verdict.reasons
    assert verdict.report is None


def test_telescoping_closed_form_check() -> None:
    document = telescoping.CertificateDocument.from_json(
        (TELESCOPING_DIR / "binomial-row-sum-two-power.json").read_text()
    )
    closed_form = document.closed_form
    assert closed_form is not None
    report = document.certificate.check_closed_form(closed_form, 0, document.options)
    assert report.base == 0
    assert report.base_cases > 0
    assert report.leading_zeros == []


def test_telescoping_closed_form_rejects_a_wrong_claim() -> None:
    document = telescoping.CertificateDocument.from_json(
        (TELESCOPING_DIR / "binomial-row-sum-two-power.json").read_text()
    )
    wrong = telescoping.HyperTerm([telescoping.Factor.power(3, telescoping.LinearForm([("n", 1)]))])
    with pytest.raises(cas.CasError):
        document.certificate.check_closed_form(wrong, 0, document.options)


def test_telescoping_term_dsl() -> None:
    form = telescoping.LinearForm([("n", 1), ("k", -1)], 2)
    assert form.coefficient("n") == 1
    assert form.coefficient("k") == -1
    assert form.constant == 2
    assert form.variables() == ["k", "n"]
    assert form.to_poly() is not None
    assert telescoping.factorial_factor(form, 1).kind == "Gamma"
    assert telescoping.Factor.poly(cas.MvPoly.var("k"), 2).kind == "Poly"
    assert telescoping.Factor.power(Fraction(1, 2), form).kind == "Power"
    assert len(telescoping.binomial_factors(form, form, 1)) == 3


def test_telescoping_check_options_builder() -> None:
    options = telescoping.CheckOptions.over("n", [1, 2, 3], (0, 5)).with_("k", [0, 1])
    assert options.window == (0, 5)
    assert set(options.samples) == {"n", "k"}
    assert options.min_ratio_samples >= 0


def test_telescoping_constants() -> None:
    assert telescoping.FORMAT == "axeyum-telescoping-certificate"
    assert telescoping.VERSION == 1


# ==========================================================================
# sos
# ==========================================================================


def test_sos_corpus_is_not_empty() -> None:
    artifacts = sos.corpus()
    assert len(artifacts) >= 3
    assert {artifact.kind for artifact in artifacts} == {
        "lyapunov",
        "barrier",
        "psd-not-sos",
    }


@pytest.mark.parametrize("artifact_id", [a.id for a in sos.corpus()])
def test_sos_corpus_artifact_checks_with_a_nonempty_report(artifact_id: str) -> None:
    artifact = sos.by_id(artifact_id)
    report = sos.check(artifact)
    assert len(report) > 0
    assert not report.is_empty()
    assert all(obligation.name and obligation.detail for obligation in report.obligations)


def test_sos_lyapunov_reports_a_certified_rate() -> None:
    report = sos.check(sos.by_id("damped-rotation-lyapunov"))
    assert report.rate is not None
    assert report.rate > 0


def test_sos_by_id_of_an_unknown_artifact_is_none() -> None:
    assert sos.by_id("no-such-artifact") is None


@pytest.mark.parametrize("name", SOS_FIXTURES)
def test_sos_fixture_round_trips_byte_identically(name: str) -> None:
    text = (SOS_DIR / name).read_text()
    assert sos.SosArtifact.from_json(text).to_json() == text


@pytest.mark.parametrize("name", SOS_FIXTURES)
def test_sos_tampered_certificate_is_rejected(name: str) -> None:
    text = (SOS_DIR / name).read_text()
    tampered = _tamper(text, '"certificate"')
    artifact = sos.SosArtifact.from_json(tampered)
    with pytest.raises(cas.CasError, match="rejected"):
        sos.check(artifact)


def test_sos_empty_obligation_list_is_refused() -> None:
    """The guard exists; it cannot be reached through the public surface.

    `sos.check` raises when the report is empty, because a checker that
    discharged nothing established nothing. No public constructor can build such
    an artifact: `SosArtifact` is reachable only from `corpus()` and
    `from_json`, and every per-kind checker pushes at least one obligation
    before it can return `Ok`. So this test pins the *observable* half -- that
    every artifact the surface can produce has a nonempty report, and that the
    unguarded call agrees with the guarded one -- and records why the raising
    branch has no fixture.
    """
    for artifact in sos.corpus():
        guarded = sos.check(artifact)
        unguarded = sos.check_unguarded(artifact)
        assert len(unguarded) == len(guarded) > 0
        assert not unguarded.is_empty()


def test_sos_sum_expands() -> None:
    x = cas.MvPoly.var("x")
    total = sos.SosSum([(Fraction(2), x)])
    assert len(total) == 1
    assert not total.is_empty()
    expanded = total.expand()
    assert expanded.evaluate({"x": Fraction(3)}) == Fraction(18)


def test_sos_sum_rejects_a_negative_weight() -> None:
    with pytest.raises(ValueError):
        sos.SosSum([(Fraction(-1), cas.MvPoly.var("x"))])


def test_sos_sum_of_variable_squares() -> None:
    norm = sos.sum_of_variable_squares(["x", "y"])
    assert norm.evaluate({"x": Fraction(3), "y": Fraction(4)}) == Fraction(25)


def test_sos_is_psd_accepts_a_positive_definite_matrix() -> None:
    result = sos.is_psd([[Fraction(2), Fraction(0)], [Fraction(0), Fraction(3)]])
    assert result.kind == "Yes"
    assert result.is_psd()
    assert len(result.pivots) == 2
    assert result.zero_pivots == 0


def test_sos_is_psd_rejects_an_indefinite_matrix() -> None:
    result = sos.is_psd([[Fraction(-1), Fraction(0)], [Fraction(0), Fraction(1)]])
    assert result.kind == "No"
    assert result.reason
    assert not result.is_psd()


def test_sos_psd_not_sos_dual_is_inspectable() -> None:
    dual = sos.psd_not_sos_dual(sos.by_id("motzkin-psd-not-sos"))
    assert dual is not None and len(dual) > 0
    assert sos.psd_not_sos_dual(sos.by_id("damped-rotation-lyapunov")) is None


def test_sos_malformed_json_raises_cas_error() -> None:
    with pytest.raises(cas.CasError):
        sos.SosArtifact.from_json("{}")


def test_sos_replay_points_constant() -> None:
    assert sos.REPLAY_POINTS == 16


# ==========================================================================
# gf2
# ==========================================================================

IRREDUCIBLE_DEGREE_8 = [8, 4, 3, 1, 0]


def _irreducible() -> gf2.Gf2Poly:
    return gf2.Gf2Poly.from_exponents(IRREDUCIBLE_DEGREE_8)


def test_gf2_limits_quote_the_defaults() -> None:
    limits = gf2.Gf2Limits()
    assert limits.max_input_degree == 4_096
    assert limits.max_intermediate_degree == 8_192
    assert limits.max_frobenius_steps == 4_096
    assert limits.max_word_ops == 50_000_000
    independent = gf2.IndependentCheckLimits()
    assert independent.max_degree == 4_096
    assert independent.max_coefficient_ops == 500_000_000


def test_gf2_poly_shape() -> None:
    poly = _irreducible()
    assert poly.degree() == 8
    assert poly.exponents() == sorted(IRREDUCIBLE_DEGREE_8)
    assert poly.coefficient(8) is True
    assert poly.coefficient(7) is False
    assert not poly.is_zero()
    assert poly.is_half_degree_shaped()
    assert gf2.Gf2Poly.zero().degree() is None
    assert gf2.Gf2Poly.one().degree() == 0
    assert gf2.Gf2Poly.x().degree() == 1
    assert gf2.Gf2Poly.from_words(poly.words()) == poly


def test_gf2_reducible_polynomial_is_a_decided_none() -> None:
    # x**2 + 1 = (x + 1)**2 over GF(2).
    assert gf2.certify_irreducible(gf2.Gf2Poly.from_exponents([2, 0])) is None


def test_gf2_irreducible_polynomial_passes_both_checkers() -> None:
    certificate = gf2.certify_irreducible(_irreducible())
    assert certificate is not None
    assert certificate.frobenius_steps == 8
    assert certificate.bezout_prime_divisors == [2]
    primary = certificate.check_primary()
    independent = certificate.check_independent()
    assert primary.accepted and primary.checker == "packed"
    assert independent.accepted and independent.checker == "independent"
    assert primary.frobenius_steps > 0
    assert primary.bezout_obligations > 0
    both = certificate.check_both()
    assert both.accepted is True


def test_gf2_tampered_certificate_fails_both_checkers() -> None:
    certificate = gf2.certify_irreducible(_irreducible())
    chain = certificate.frobenius
    tampered = gf2.IrreducibilityCertificate(
        certificate.polynomial,
        [gf2.FrobeniusReduction(chain[0].quotient, gf2.Gf2Poly.one())] + chain[1:],
        certificate.bezout,
    )
    primary = tampered.check_primary()
    independent = tampered.check_independent()
    assert primary.accepted is False and primary.reason
    assert independent.accepted is False and independent.reason
    assert tampered.check_both().accepted is False


def test_gf2_tampered_bezout_fails_both_checkers() -> None:
    certificate = gf2.certify_irreducible(_irreducible())
    identity = certificate.bezout[0]
    tampered = gf2.IrreducibilityCertificate(
        certificate.polynomial,
        certificate.frobenius,
        [
            gf2.RabinBezout(
                identity.prime_divisor,
                gf2.Gf2Poly.one(),
                identity.frobenius_coefficient,
            )
        ],
    )
    assert tampered.check_primary().accepted is False
    assert tampered.check_independent().accepted is False


def test_gf2_checker_budget_refusal_is_an_exception_not_a_rejection() -> None:
    """A tripped ceiling is not a statement about the certificate.

    The two are kept apart deliberately: `InvalidCertificate` comes back as
    `accepted == False` with a reason, and every other `Gf2Error` is raised.
    Reporting a starved checker as "the certificate is wrong" is the more
    dangerous of the two confusions, so it gets its own control.
    """
    certificate = gf2.certify_irreducible(_irreducible())
    with pytest.raises(cas.Gf2Error):
        certificate.check_primary(gf2.Gf2Limits(max_input_degree=4))
    with pytest.raises(cas.Gf2Error):
        certificate.check_independent(gf2.IndependentCheckLimits(max_degree=4))
    with pytest.raises(cas.Gf2Error):
        certificate.check_both(gf2.Gf2Limits(max_input_degree=4))


def test_gf2_budget_refusal_is_an_exception_not_a_verdict() -> None:
    with pytest.raises(cas.Gf2Error):
        gf2.certify_irreducible(_irreducible(), gf2.Gf2Limits(max_input_degree=4))


def test_gf2_constant_polynomial_is_a_shape_error() -> None:
    with pytest.raises(cas.Gf2Error):
        gf2.certify_irreducible(gf2.Gf2Poly.one())


def test_gf2_zero_polynomial_is_a_shape_error() -> None:
    with pytest.raises(cas.Gf2Error):
        gf2.certify_irreducible(gf2.Gf2Poly.zero())


def test_gf2_artifact_round_trips_and_validates() -> None:
    certificate = gf2.certify_irreducible(_irreducible())
    artifact = gf2.HalfDegreeArtifact("half-degree-8", "axeyum-py/test", certificate)
    artifact.validate()
    text = artifact.to_canonical_json()
    parsed = gf2.HalfDegreeArtifact.from_canonical_json(text)
    assert parsed == artifact
    assert parsed.to_canonical_json() == text
    assert parsed.id == "half-degree-8"
    assert parsed.producer == "axeyum-py/test"


def test_gf2_artifact_ingest_is_fail_closed_on_a_tampered_certificate() -> None:
    certificate = gf2.certify_irreducible(_irreducible())
    chain = certificate.frobenius
    tampered = gf2.IrreducibilityCertificate(
        certificate.polynomial,
        [gf2.FrobeniusReduction(chain[0].quotient, gf2.Gf2Poly.one())] + chain[1:],
        certificate.bezout,
    )
    artifact = gf2.HalfDegreeArtifact("half-degree-8", "axeyum-py/test", tampered)
    with pytest.raises(cas.Gf2Error):
        artifact.validate()
    with pytest.raises(cas.Gf2Error):
        artifact.to_canonical_json()


def test_gf2_artifact_rejects_malformed_json() -> None:
    with pytest.raises(cas.Gf2Error):
        gf2.HalfDegreeArtifact.from_canonical_json("{}")


def test_gf2_artifact_constants() -> None:
    assert gf2.FORMAT == "axeyum-gf2-half-degree-irreducible"
    assert gf2.VERSION == 1
    assert "monic irreducible" in gf2.STATEMENT


def test_gf2_artifact_limits_defaults() -> None:
    limits = gf2.ArtifactLimits()
    assert limits.max_bytes == 32 * 1024 * 1024
    assert limits.max_id_bytes == 256
    assert limits.max_producer_bytes == 256


def test_gf2_no_shard_or_filesystem_surface_in_v1() -> None:
    # The shard functions touch the filesystem and are deliberately not bound.
    assert not hasattr(gf2, "check_shard_directory")
    assert not hasattr(gf2, "sha256_hex")


# ==========================================================================
# sturm / interval
# ==========================================================================


def _sqrt_two() -> list[Fraction]:
    """`x**2 - 2`, dense, lowest degree first."""
    return [Fraction(-2), Fraction(0), Fraction(1)]


def test_sturm_counts_real_roots_exactly() -> None:
    assert sturm.count_real_roots_in(_sqrt_two(), Fraction(-3), Fraction(3)) == 2
    assert sturm.count_real_roots_in(_sqrt_two(), Fraction(0), Fraction(3)) == 1
    assert sturm.count_real_roots_in(_sqrt_two(), Fraction(2), Fraction(3)) == 0


def test_sturm_isolates_real_roots() -> None:
    intervals = sturm.isolate_real_roots(_sqrt_two())
    assert len(intervals) == 2
    for lower, upper in intervals:
        assert lower < upper


def test_sturm_approximates_real_roots() -> None:
    roots = sturm.approximate_real_roots(_sqrt_two(), Fraction(1, 10_000))
    assert len(roots) == 2
    assert abs(float(roots[1]) - 2**0.5) < 1e-4


def test_interval_basic_accessors() -> None:
    interval = sturm.Interval(Fraction(-1), Fraction(3))
    assert interval.lower == Fraction(-1)
    assert interval.upper == Fraction(3)
    assert interval.width() == Fraction(4)
    assert interval.midpoint() == Fraction(1)
    assert interval.contains(Fraction(0))
    assert not interval.contains(Fraction(9))


def test_interval_rejects_a_reversed_pair() -> None:
    assert sturm.Interval(Fraction(3), Fraction(1)) is None


def test_interval_arithmetic() -> None:
    a = sturm.Interval(Fraction(1), Fraction(2))
    b = sturm.Interval(Fraction(3), Fraction(4))
    assert a.add(b).lower == Fraction(4)
    assert a.sub(b).upper == Fraction(-1)
    assert a.mul(b).upper == Fraction(8)
    assert a.neg().lower == Fraction(-2)
    assert a.pow(2).upper == Fraction(4)
    assert a.abs().lower == Fraction(1)
    assert a.hull(b).upper == Fraction(4)
    assert a.intersection(b) is None
    assert a.contains_interval(sturm.Interval(Fraction(3, 2), Fraction(3, 2)))


def test_interval_div_declines_when_the_divisor_straddles_zero() -> None:
    """The soundness guard: no finite interval encloses `1 / [-1, 1]`."""
    numerator = sturm.Interval(Fraction(1), Fraction(2))
    straddling = sturm.Interval(Fraction(-1), Fraction(1))
    assert numerator.div(straddling) is None
    # ...and a divisor bounded away from zero still divides.
    positive = sturm.Interval(Fraction(1), Fraction(2))
    assert numerator.div(positive) is not None


def test_interval_degenerate() -> None:
    point = sturm.Interval.degenerate(Fraction(5, 2))
    assert point.lower == point.upper == Fraction(5, 2)
    assert point.width() == 0


def test_evaluate_polynomial_over_an_interval_encloses_the_range() -> None:
    enclosure = sturm.evaluate_polynomial_over(
        _sqrt_two(), sturm.Interval(Fraction(1), Fraction(2))
    )
    assert enclosure is not None
    assert enclosure.lower <= Fraction(-1)  # value at x = 1
    assert enclosure.upper >= Fraction(2)  # value at x = 2


def test_set_interval_is_a_distinct_type() -> None:
    closed = sturm.SetInterval.closed(Fraction(0), Fraction(1))
    assert closed.contains(Fraction(1))
    assert not sturm.SetInterval.open(Fraction(0), Fraction(1)).contains(Fraction(1))
    assert not sturm.SetInterval.universe().is_empty()
    assert not isinstance(closed, sturm.Interval)


def test_the_three_interval_types_are_all_reachable_and_distinct() -> None:
    # `interval_arith::Interval`, `sets::Interval` and `lib::RealInterval` are
    # three different Rust types; the inventory flags the name collision.
    assert sturm.Interval is not sturm.SetInterval
    assert cas.RealInterval is not sturm.Interval
