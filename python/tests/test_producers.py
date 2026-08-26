"""``axeyum.producers`` (tier P) -- the untrusted bounded producers.

What these tests are for, in order of what they would catch:

**A producer whose reach silently changed.** Every accept/decline below is a
*measured* verdict of the promoted library modules, not a doc claim, and each
decline asserts the exact typed ``DeclineReason.kind``. A refactor that turned an
accept into a decline, or one ``DeclineReason`` variant into another, fails here.

**A candidate admitted on the producer's word.** No test accepts a candidate as
proved. Every accepted proof is put through ``Kernel.add_declaration`` -- the
kernel, not the producer, is what decides -- and then measured for an *empty*
``axiom_footprint`` and zero cited theorems. A producer that returned a wrong
term would be rejected by the kernel and fail the test.

**A budget that drifted.** ``MAX_BINDERS == 8`` is part of five settled facts'
reproduction contract; ``check-autogenesis-bounded-induction-family.py`` refuses
a mismatch even when every ``proof_sha256`` agrees. It is asserted here as a
literal, and asserted to be unreachable as a keyword argument.

**A handle used against the wrong kernel.** ``ExprId`` is an index, not a term:
mixing kernels is not a Rust type error, it silently denotes something else.

The seven frozen ``natural-factorial`` goals the module doc names
(``descFactorial n 1 = n``, ``ascFactorial n 0 = 1``, ...) live in the *Mathlib*
namespace and are reachable only through the pinned exports under ``/nas3``.
This project's own ``build_nat_prelude`` has neither ``descFactorial`` nor
``ascFactorial``, so the host-independent tests below use the in-tree goals the
module doc *also* names -- ``Nat.sub_self`` above all, which the doc singles out
as the shape needing ``try_split_congruence`` -- plus the ``0 <= n`` /
``1 <= n`` order pair from the promoted module's own ``order_terminal_tests``.
The two ``/nas3`` tests reproduce the committed ``proof_sha256`` of a genuine
frozen goal for each producer and are skipped, loudly, when the export is not on
this host.
"""

from __future__ import annotations

import hashlib
import pathlib

import pytest

from axeyum import AxeyumError
from axeyum import producers as P
from axeyum.kernel import BinderInfo, Declaration, EpochError, ExprId, Kernel

# --- frozen external goals, one per producer ------------------------------
#
# Path, target and expected digests are copied from the committed manifests
# `artifacts/autogenesis/mathlib-bounded-induction-family-descfactorial-one-v1.json`
# and `artifacts/autogenesis/mathlib-modeq-family-trans-v1.json`.

FROZEN_BOUNDED_INDUCTION = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/sources/"
    "mathlib-v4.30.0-bounded-induction-family-v1/descfactorial-one.ndjson"
)
FROZEN_BOUNDED_INDUCTION_TARGET = (
    "Axeyum.Autogenesis.Statement.BoundedInductionFamily.natDescFactorialOne"
)
FROZEN_BOUNDED_INDUCTION_GOAL_SHA = (
    "29d67ba637045e918b70290a218dfe43db046a97bfc0cadb981d706ed37b56e4"
)
FROZEN_BOUNDED_INDUCTION_PROOF_SHA = (
    "b05d1fa37636341ef3251512dcb9d9797d565ce9cad427517771386a68f082a9"
)
FROZEN_BOUNDED_INDUCTION_CONTENT_SHA = (
    "a8adc68c502ee2679ce4aef7eedee7f996b015ed7b76b2fee59a586ff5e4263e"
)

FROZEN_MODEQ = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/sources/mathlib-v4.30.0-modeq-family-v1/int-modeq-trans.ndjson"
)
FROZEN_MODEQ_TARGET = "Axeyum.Autogenesis.Statement.IntModEqFamily.intModEqTrans"
FROZEN_MODEQ_PROOF_SHA = "c5e4388868b7e82a46843080112d61a09e2115a4a7a2e36d8e5960a973391b82"

# Measured reach of `producers::bounded_induction` against this project's own
# `build_nat_prelude`. Each row is (theorem name, binders, inductions).
ACCEPTED_GOALS = [
    ("Nat.sub_self", 1, 1),
    ("Nat.zero_add", 1, 1),
    ("Nat.add_zero", 1, 1),
    ("Nat.mul_one", 1, 1),
    ("Nat.one_mul", 1, 1),
    ("Nat.zero_le", 1, 1),
]

# Goals the bounded search does NOT close, with the exact typed reason.
DECLINED_GOALS = [
    ("Nat.add_comm", "TerminalNotDefEqNoRewrite"),
    ("Nat.succ_le_succ", "TerminalNotDefEqNoRewrite"),
]


def sha256(text: str) -> str:
    """The digest the operation drivers stamp on a rendered term."""
    return hashlib.sha256(text.encode()).hexdigest()


@pytest.fixture
def nat_kernel() -> Kernel:
    """A kernel with the computational ``Nat`` prelude admitted."""
    kernel = Kernel()
    kernel.build_nat_prelude()
    return kernel


def goal_of(kernel: Kernel, theorem: str) -> ExprId:
    """The *statement* of an already-declared theorem, as a producer goal."""
    declaration = kernel.get_declaration(theorem)
    assert declaration is not None, f"{theorem} is not in this prelude"
    return declaration.ty


# ---------------------------------------------------------------------------
# Pinned budgets
# ---------------------------------------------------------------------------


def test_max_binders_is_the_pinned_eight() -> None:
    """Five settled facts pin ``max_binders: 8``; the family checker refuses a
    mismatch even when every ``proof_sha256`` is byte-identical."""
    assert P.MAX_BINDERS == 8


def test_the_other_budgets_are_exported_as_constants() -> None:
    assert P.MAX_INDUCTIONS == 2
    assert P.MODEQ_MAX_BINDERS == 8
    assert P.APPLICATION_MAX_BINDERS == 8
    assert P.APPLICATION_MAX_DEPTH == 8
    assert P.APPLICATION_MAX_TERMS == 128


def test_bounded_application_composes_retrieved_fibonacci_lemmas(
    nat_kernel: Kernel,
) -> None:
    goal = goal_of(nat_kernel, "Nat.fib_mono")
    declarations = [
        nat_kernel.name("Nat.monotone_of_le_succ", must_exist=True),
        nat_kernel.name("Nat.fib", must_exist=True),
        nat_kernel.name("Nat.fib_le_succ", must_exist=True),
    ]
    candidate = P.propose_bounded_application(nat_kernel, goal, declarations)
    name = nat_kernel.name("Axeyum.Test.BoundedApplicationFibMono", must_exist=False)
    nat_kernel.add_declaration(Declaration.theorem(name, [], goal, candidate.proof))
    assert nat_kernel.axiom_footprint(name) == []
    assert nat_kernel.theorem_dependencies(name) == [
        "Nat.fib_le_succ",
        "Nat.monotone_of_le_succ",
    ]
    assert candidate.binders_used == 3
    assert 0 < candidate.application_depth <= P.APPLICATION_MAX_DEPTH
    assert candidate.terms_considered <= P.APPLICATION_MAX_TERMS


def test_candidate_capsule_imports_exact_lemmas_without_target_proof() -> None:
    source = Kernel()
    source.build_nat_prelude()
    goal = goal_of(source, "Nat.fib_mono")
    target_text = "Axeyum.Autogenesis.Statement.Native.fibMono"
    target = source.name(target_text, must_exist=False)
    source.add_declaration(Declaration.definition(target, [], source.sort_zero(), goal))
    candidate_names = [
        "Nat.monotone_of_le_succ",
        "Nat.fib",
        "Nat.fib_le_succ",
    ]
    roots = [target, *(source.name(name, must_exist=True) for name in candidate_names)]
    capsule = source.render_lean4export_ndjson_roots("4.30.0", roots).encode()
    assert b'"Nat.fib_mono"' not in capsule

    imported = P.import_candidate_statement_ndjson(capsule, None, target_text, candidate_names)
    kernel = imported.kernel()
    declarations = [kernel.name(name, must_exist=True) for name in candidate_names]
    candidate = P.propose_bounded_application(kernel, imported.goal(), declarations)
    admitted = kernel.name("Axeyum.Test.ImportedBoundedApplicationFibMono", must_exist=False)
    kernel.add_declaration(Declaration.theorem(admitted, [], imported.goal(), candidate.proof))
    assert kernel.axiom_footprint(admitted) == []
    assert kernel.theorem_dependencies(admitted) == [
        "Nat.fib_le_succ",
        "Nat.monotone_of_le_succ",
    ]

    with pytest.raises(P.StatementImportError, match="trusted declaration"):
        P.import_candidate_statement_ndjson(capsule, None, target_text, [])
    with pytest.raises(P.StatementImportError, match="contains target"):
        P.import_candidate_statement_ndjson(capsule, None, target_text, [target_text])


def test_bounded_application_declines_without_adjacent_step(
    nat_kernel: Kernel,
) -> None:
    goal = goal_of(nat_kernel, "Nat.fib_mono")
    declarations = [
        nat_kernel.name("Nat.monotone_of_le_succ", must_exist=True),
        nat_kernel.name("Nat.fib", must_exist=True),
    ]
    with pytest.raises(P.Declined) as raised:
        P.propose_bounded_application(nat_kernel, goal, declarations)
    assert raised.value.reason.producer == "bounded-application"
    assert raised.value.reason.kind == "NoTypedApplication"


def test_budgets_are_not_reachable_as_keyword_arguments(nat_kernel: Kernel) -> None:
    """A budget passed per call is a budget that can drift per call."""
    goal = goal_of(nat_kernel, "Nat.add_zero")
    with pytest.raises(TypeError):
        P.propose_bounded_induction(nat_kernel, goal, max_binders=12)


def test_wire_format_constants_are_exported() -> None:
    assert P.FORMAT_VERSION == "3.1.0"
    assert P.IDENTITY_VERSION == "axeyum-lean-declaration-identity-v1"


# ---------------------------------------------------------------------------
# Import limits
# ---------------------------------------------------------------------------


def test_import_limits_defaults_are_the_rust_defaults() -> None:
    limits = P.ImportLimits()
    assert limits.max_line_bytes == 16 * 1024 * 1024
    assert limits.max_records == 2_000_000


def test_import_limits_overrides_and_equality() -> None:
    tight = P.ImportLimits(max_line_bytes=4096, max_records=10)
    assert (tight.max_line_bytes, tight.max_records) == (4096, 10)
    assert tight == P.ImportLimits(4096, 10)
    assert tight != P.ImportLimits()
    assert "4096" in repr(tight)


# ---------------------------------------------------------------------------
# Bounded induction: what it closes
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(("theorem", "binders", "inductions"), ACCEPTED_GOALS)
def test_accepted_goal_reproduces_the_measured_search_shape(
    nat_kernel: Kernel, theorem: str, binders: int, inductions: int
) -> None:
    candidate = P.propose_bounded_induction(nat_kernel, goal_of(nat_kernel, theorem))
    assert candidate.binders_used == binders
    assert candidate.inductions_used == inductions
    assert candidate.binders_used <= P.MAX_BINDERS
    assert candidate.inductions_used <= P.MAX_INDUCTIONS


@pytest.mark.parametrize(("theorem", "binders", "inductions"), ACCEPTED_GOALS)
def test_accepted_candidate_is_admitted_and_axiom_free(
    nat_kernel: Kernel, theorem: str, binders: int, inductions: int
) -> None:
    """The kernel decides, not the producer -- and then the footprint is
    *measured*, never inferred from the fact that admission succeeded."""
    del binders, inductions
    goal = goal_of(nat_kernel, theorem)
    candidate = P.propose_bounded_induction(nat_kernel, goal)
    name = nat_kernel.name(f"Axeyum.Test.{theorem.replace('.', '_')}", must_exist=False)
    nat_kernel.add_declaration(Declaration.theorem(name, [], goal, candidate.proof))
    assert nat_kernel.axiom_footprint(name) == []
    assert nat_kernel.theorem_dependencies(name) == []
    assert nat_kernel.is_axiom_free(name)


def test_reflexivity_alone_would_not_have_closed_these(nat_kernel: Kernel) -> None:
    """Every accepted goal above needed a genuine induction: ``inductions_used``
    is nonzero for all of them, so none is a reflexivity result in disguise."""
    used = set()
    for theorem, _, _ in ACCEPTED_GOALS:
        kernel = Kernel()
        kernel.build_nat_prelude()
        used.add(P.propose_bounded_induction(kernel, goal_of(kernel, theorem)).inductions_used)
    assert used == {1}


# ---------------------------------------------------------------------------
# Bounded induction: what it declines, and with which typed reason
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(("theorem", "kind"), DECLINED_GOALS)
def test_declined_goal_reports_its_typed_reason(
    nat_kernel: Kernel, theorem: str, kind: str
) -> None:
    with pytest.raises(P.Declined) as raised:
        P.propose_bounded_induction(nat_kernel, goal_of(nat_kernel, theorem))
    assert raised.value.reason.kind == kind
    assert raised.value.reason.producer == "bounded-induction"


def test_non_equality_goal_declines_with_not_equality_goal(nat_kernel: Kernel) -> None:
    """``Nat`` is a type, not an equation: nothing this producer builds applies."""
    goal = nat_kernel.const_(nat_kernel.name("Nat", must_exist=True), [])
    with pytest.raises(P.Declined) as raised:
        P.propose_bounded_induction(nat_kernel, goal)
    assert raised.value.reason.kind == "NotEqualityGoal"
    assert raised.value.reason.detail is None


def test_nine_binders_exceeds_the_pinned_budget(nat_kernel: Kernel) -> None:
    """One binder past ``MAX_BINDERS``, over an otherwise trivial ``x = x``."""
    kernel = nat_kernel
    nat = kernel.const_(kernel.name("Nat", must_exist=True), [])
    level = kernel.level_succ(kernel.level_zero())
    equality = kernel.const_(kernel.name("Eq", must_exist=True), [level])
    bound = kernel.bvar(0)
    goal = kernel.app(kernel.app(kernel.app(equality, nat), bound), bound)
    for index in range(P.MAX_BINDERS + 1):
        binder = kernel.name_str(kernel.anon(), f"x{index}")
        goal = kernel.pi(binder, nat, goal, BinderInfo.Default)
    with pytest.raises(P.Declined) as raised:
        P.propose_bounded_induction(kernel, goal)
    assert raised.value.reason.kind == "BinderBudgetExceeded"
    assert str(P.MAX_BINDERS) in raised.value.reason.message


def test_decline_reason_is_typed_data_not_a_parsed_string(nat_kernel: Kernel) -> None:
    with pytest.raises(P.Declined) as raised:
        P.propose_bounded_induction(nat_kernel, goal_of(nat_kernel, "Nat.add_comm"))
    reason = raised.value.reason
    assert isinstance(reason, P.DeclineReason)
    assert reason.kind == "TerminalNotDefEqNoRewrite"
    assert reason.detail is None
    assert reason.message and reason.message != reason.kind
    assert reason == reason  # noqa: PLR0124 - the pyclass __eq__ is the subject
    assert "TerminalNotDefEqNoRewrite" in repr(reason)


def test_declined_is_catchable_as_the_one_root_exception(nat_kernel: Kernel) -> None:
    with pytest.raises(AxeyumError):
        P.propose_bounded_induction(nat_kernel, goal_of(nat_kernel, "Nat.add_comm"))


# ---------------------------------------------------------------------------
# Handle provenance
# ---------------------------------------------------------------------------


def test_bounded_induction_refuses_a_goal_from_another_kernel(nat_kernel: Kernel) -> None:
    """The two kernels agree on every index; only the epoch says they are not
    the same term."""
    other = Kernel()
    other.build_nat_prelude()
    foreign = goal_of(other, "Nat.add_zero")
    with pytest.raises(EpochError):
        P.propose_bounded_induction(nat_kernel, foreign)


def test_modeq_family_refuses_a_goal_from_another_kernel(nat_kernel: Kernel) -> None:
    other = Kernel()
    other.build_nat_prelude()
    with pytest.raises(EpochError):
        P.propose_modeq_family(nat_kernel, goal_of(other, "Nat.add_zero"))


def test_audit_circularity_refuses_a_name_from_another_kernel(nat_kernel: Kernel) -> None:
    other = Kernel()
    other.build_nat_prelude()
    mine = nat_kernel.name("Nat.add_zero", must_exist=True)
    theirs = other.name("Nat.add_zero", must_exist=True)
    with pytest.raises(EpochError):
        P.audit_circularity(nat_kernel, mine, theirs)


def test_a_fork_takes_a_new_epoch_and_refuses_the_parents_goal(nat_kernel: Kernel) -> None:
    goal = goal_of(nat_kernel, "Nat.add_zero")
    forked = nat_kernel.fork()
    with pytest.raises(EpochError):
        P.propose_bounded_induction(forked, goal)


# ---------------------------------------------------------------------------
# The `ModEq` producer
# ---------------------------------------------------------------------------


def test_modeq_family_declines_a_nat_induction_goal(nat_kernel: Kernel) -> None:
    """``Nat.sub_self`` needs an induction; this producer has none, so it
    declines with its own vocabulary rather than borrowing the other's."""
    with pytest.raises(P.Declined) as raised:
        P.propose_modeq_family(nat_kernel, goal_of(nat_kernel, "Nat.sub_self"))
    assert raised.value.reason.producer == "modeq-family"
    assert raised.value.reason.kind in {
        "TerminalNotClosed",
        "RequiredDeclarationUnavailable",
        "UnsupportedRecursorShape",
        "UnsupportedIffShape",
        "BinderBudgetExceeded",
    }


def test_modeq_family_closes_a_reflexivity_goal(nat_kernel: Kernel) -> None:
    """``∀ n, n = n`` is inside the Eq-combinator schema, and the kernel agrees."""
    kernel = nat_kernel
    nat = kernel.const_(kernel.name("Nat", must_exist=True), [])
    level = kernel.level_succ(kernel.level_zero())
    equality = kernel.const_(kernel.name("Eq", must_exist=True), [level])
    bound = kernel.bvar(0)
    body = kernel.app(kernel.app(kernel.app(equality, nat), bound), bound)
    goal = kernel.pi(kernel.name_str(kernel.anon(), "n"), nat, body, BinderInfo.Default)
    candidate = P.propose_modeq_family(kernel, goal)
    assert candidate.binders_used == 1
    name = kernel.name("Axeyum.Test.ModEqRefl", must_exist=False)
    kernel.add_declaration(Declaration.theorem(name, [], goal, candidate.proof))
    assert kernel.axiom_footprint(name) == []


# ---------------------------------------------------------------------------
# Circularity audit
# ---------------------------------------------------------------------------


def test_audit_circularity_detects_direct_self_citation() -> None:
    """The adversarial fixture: ``candidate : Prop := target``, literally citing
    its own target. An audit that cannot fail is worse than no audit."""
    kernel = Kernel()
    root = kernel.anon()
    target = kernel.name_str(root, "CircularityFixtureTarget")
    candidate = kernel.name_str(root, "CircularityFixtureCandidate")
    prop = kernel.sort_zero()
    kernel.add_declaration(Declaration.axiom(target, [], prop))
    kernel.add_declaration(
        Declaration.definition(candidate, [], prop, kernel.const_(target, []), "regular", 0)
    )
    audit = P.audit_circularity(kernel, candidate, target)
    assert audit.target_dependency is True
    assert audit.axiom_footprint == 1
    assert audit.passes() is False


def test_audit_circularity_passes_a_genuinely_independent_candidate(
    nat_kernel: Kernel,
) -> None:
    goal = goal_of(nat_kernel, "Nat.sub_self")
    proposed = P.propose_bounded_induction(nat_kernel, goal)
    name = nat_kernel.name("Axeyum.Test.Independent", must_exist=False)
    nat_kernel.add_declaration(Declaration.theorem(name, [], goal, proposed.proof))
    # The target is the already-proved SIBLING theorem the candidate must not
    # borrow -- `Nat.sub_self` itself, not the definition `Nat.sub` the goal is
    # necessarily about. Citing the definition is the point; citing the theorem
    # would be the circularity.
    target = nat_kernel.name("Nat.sub_self", must_exist=True)
    audit = P.audit_circularity(nat_kernel, name, target)
    assert (audit.axiom_footprint, audit.theorem_dependencies) == (0, 0)
    assert audit.target_dependency is False
    assert audit.passes() is True
    assert "True" in repr(audit)


# ---------------------------------------------------------------------------
# Statement import
# ---------------------------------------------------------------------------


def _render_statement_export(kernel: Kernel) -> tuple[str, str]:
    """A one-declaration ``lean4export`` stream carrying ``Demo.goal : Prop``.

    The goal is ``∀ n, Nat.sub n n = Nat.zero`` -- the ``Nat.sub_self``
    statement, built directly rather than borrowed from the prelude's theorem,
    so the exported closure contains no proof of it.
    """
    nat = kernel.const_(kernel.name("Nat", must_exist=True), [])
    level = kernel.level_succ(kernel.level_zero())
    equality = kernel.const_(kernel.name("Eq", must_exist=True), [level])
    subtract = kernel.const_(kernel.name("Nat.sub", must_exist=True), [])
    zero = kernel.const_(kernel.name("Nat.zero", must_exist=True), [])
    bound = kernel.bvar(0)
    difference = kernel.app(kernel.app(subtract, bound), bound)
    body = kernel.app(kernel.app(kernel.app(equality, nat), difference), zero)
    statement = kernel.pi(kernel.name_str(kernel.anon(), "n"), nat, body, BinderInfo.Default)
    name = kernel.name("Demo.goal", must_exist=False)
    kernel.add_declaration(
        Declaration.definition(name, [], kernel.sort_zero(), statement, "regular", 0)
    )
    return kernel.render_lean(statement), kernel.render_lean4export_ndjson_roots("4.30.0", [name])


def test_import_statement_ndjson_round_trips_the_goal(nat_kernel: Kernel) -> None:
    rendered, export = _render_statement_export(nat_kernel)
    imported = P.import_statement_ndjson(export.encode(), None, "Demo.goal")
    assert imported.kernel().render_lean(imported.goal()) == rendered


def test_import_statement_ndjson_accepts_a_path_and_bytes(
    nat_kernel: Kernel, tmp_path: pathlib.Path
) -> None:
    rendered, export = _render_statement_export(nat_kernel)
    path = tmp_path / "demo.ndjson"
    path.write_text(export)
    from_bytes = P.import_statement_ndjson(export.encode(), None, "Demo.goal")
    from_path = P.import_statement_ndjson(str(path), P.ImportLimits(), "Demo.goal")
    from_pathlike = P.import_statement_ndjson(path, None, "Demo.goal")
    renders = {
        each.kernel().render_lean(each.goal()) for each in (from_bytes, from_path, from_pathlike)
    }
    assert renders == {rendered}


def test_statement_import_hands_back_the_same_kernel_object(nat_kernel: Kernel) -> None:
    """A fresh copy per call would invalidate every handle already handed out."""
    _, export = _render_statement_export(nat_kernel)
    imported = P.import_statement_ndjson(export.encode(), None, "Demo.goal")
    assert imported.kernel() is imported.kernel()
    assert imported.kernel().epoch == imported.goal().epoch
    assert imported.kernel().epoch == imported.target_name().epoch
    assert imported.kernel().epoch != nat_kernel.epoch


def test_statement_import_report_is_a_measurement(nat_kernel: Kernel) -> None:
    _, export = _render_statement_export(nat_kernel)
    report = P.import_statement_ndjson(export.encode(), None, "Demo.goal").report()
    assert report.format_version == P.FORMAT_VERSION
    assert report.lean_version == "4.30.0"
    assert report.identity_version == P.IDENTITY_VERSION
    assert report.axioms == []
    assert report.substituted_theorems == []
    assert report.admitted_declarations == len(report.declaration_identities)
    identities = {row.name: row for row in report.declaration_identities}
    assert identities["Demo.goal"].kind == "definition"
    assert len(identities["Demo.goal"].content_sha256) == 64
    assert all(len(dep.content_sha256) == 64 for dep in identities["Demo.goal"].dependencies)


def test_statement_import_produces_a_kernel_that_cannot_prove_the_goal(
    nat_kernel: Kernel,
) -> None:
    """Proof isolation is the whole point: the import carries the goal's
    definitional dependencies and no theorem at all."""
    _, export = _render_statement_export(nat_kernel)
    imported = P.import_statement_ndjson(export.encode(), None, "Demo.goal")
    report = imported.report()
    assert all(row.kind != "theorem" for row in report.declaration_identities)
    kernel = imported.kernel()
    candidate = P.propose_bounded_induction(kernel, imported.goal())
    name = kernel.name("Axeyum.Test.Imported", must_exist=False)
    kernel.add_declaration(Declaration.theorem(name, [], imported.goal(), candidate.proof))
    assert kernel.axiom_footprint(name) == []
    assert P.audit_circularity(kernel, name, imported.target_name()).passes() is True


def test_statement_import_rejects_a_proof_bearing_stream(nat_kernel: Kernel) -> None:
    export = nat_kernel.render_lean4export_ndjson_roots(
        "4.30.0", [nat_kernel.name("Nat.add_zero", must_exist=True)]
    )
    with pytest.raises(P.StatementImportError) as raised:
        P.import_statement_ndjson(export.encode(), None, "Nat.add_zero")
    assert raised.value.variant == "TrustedDeclaration"


def test_statement_import_rejects_a_source_that_is_neither_path_nor_bytes() -> None:
    with pytest.raises(TypeError):
        P.import_statement_ndjson(123, None, "Demo.goal")


def test_statement_import_propagates_a_missing_file(tmp_path: pathlib.Path) -> None:
    with pytest.raises(OSError):
        P.import_statement_ndjson(str(tmp_path / "absent.ndjson"), None, "Demo.goal")


def test_tight_limits_refuse_an_oversized_record(nat_kernel: Kernel) -> None:
    _, export = _render_statement_export(nat_kernel)
    with pytest.raises(P.StatementImportError):
        P.import_statement_ndjson(export.encode(), P.ImportLimits(max_line_bytes=8), "Demo.goal")


# ---------------------------------------------------------------------------
# The frozen external goals
# ---------------------------------------------------------------------------


@pytest.mark.skipif(
    not FROZEN_BOUNDED_INDUCTION.is_file(),
    reason=f"pinned Mathlib export not on this host: {FROZEN_BOUNDED_INDUCTION}",
)
def test_frozen_factorial_goal_reproduces_the_committed_digests() -> None:
    """``descFactorial n 1 = n`` -- one of the seven frozen ``natural-factorial``
    goals -- through the binding, compared against
    ``mathlib-bounded-induction-family-descfactorial-one-v1.json``."""
    imported = P.import_statement_ndjson(
        str(FROZEN_BOUNDED_INDUCTION), None, FROZEN_BOUNDED_INDUCTION_TARGET
    )
    kernel = imported.kernel()
    assert sha256(kernel.render_lean(imported.goal())) == FROZEN_BOUNDED_INDUCTION_GOAL_SHA
    candidate = P.propose_bounded_induction(kernel, imported.goal())
    assert sha256(kernel.render_lean(candidate.proof)) == FROZEN_BOUNDED_INDUCTION_PROOF_SHA
    assert (candidate.binders_used, candidate.inductions_used) == (1, 1)
    report = imported.report()
    assert report.admitted_declarations == 59
    target = next(
        row for row in report.declaration_identities if row.name == FROZEN_BOUNDED_INDUCTION_TARGET
    )
    assert target.content_sha256 == FROZEN_BOUNDED_INDUCTION_CONTENT_SHA
    name = kernel.name("Axeyum.Test.FrozenFactorial", must_exist=False)
    kernel.add_declaration(Declaration.theorem(name, [], imported.goal(), candidate.proof))
    assert kernel.axiom_footprint(name) == []


@pytest.mark.skipif(
    not FROZEN_MODEQ.is_file(),
    reason=f"pinned Mathlib export not on this host: {FROZEN_MODEQ}",
)
def test_frozen_modeq_goal_reproduces_the_committed_digest() -> None:
    """``Int.ModEq`` transitivity, compared against
    ``mathlib-modeq-family-trans-v1.json``."""
    imported = P.import_statement_ndjson(str(FROZEN_MODEQ), None, FROZEN_MODEQ_TARGET)
    kernel = imported.kernel()
    candidate = P.propose_modeq_family(kernel, imported.goal())
    assert sha256(kernel.render_lean(candidate.proof)) == FROZEN_MODEQ_PROOF_SHA
    assert candidate.binders_used == 6
    name = kernel.name("Axeyum.Test.FrozenModEq", must_exist=False)
    kernel.add_declaration(Declaration.theorem(name, [], imported.goal(), candidate.proof))
    audit = P.audit_circularity(kernel, name, imported.target_name())
    assert (audit.axiom_footprint, audit.theorem_dependencies) == (0, 0)
    assert audit.passes() is True


# ---------------------------------------------------------------------------
# Surface
# ---------------------------------------------------------------------------


def test_every_exported_name_resolves() -> None:
    missing = [name for name in P.__all__ if not hasattr(P, name)]
    assert missing == []


def test_the_exceptions_share_one_root() -> None:
    assert issubclass(P.Declined, AxeyumError)
    assert issubclass(P.StatementImportError, AxeyumError)
