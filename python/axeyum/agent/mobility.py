"""The mobility census: every tactic precondition against every open fact.

Slice A7 of [`docs/python-2026-08/03-agentic-layer.md`]. A4 measured that the
model emits `NoGeneralRoute` far more often than the producers actually decline,
and could not say whether that gap was the model's judgement or the repository's
capability. A census answers it without a model in the loop: evaluate each
tactic's **structural precondition** against each open fact's kernel goal, and
publish what matched, what did not, and -- the part that matters -- what was
never looked at.

Three rules are load-bearing here.

**Three-valued, never a bare bool.** :class:`Verdict` is `matched`,
`unmatched(reason)` or `unevaluable(reason)`. "No tactic matched this fact"
and "this fact has no kernel goal, so nothing was evaluated" are the two
answers a two-valued census would merge, and merging them is exactly the
CLAUDE.md trap: an empty result from a tool that was never pointed at your
subject is indistinguishable from a strong negative result. 187 of 191 open
facts have no frozen export; a boolean census would have reported them as
zero-match and made the capability backlog a fiction.

**No goal is invented.** A fact's goal comes from a frozen, digest-pinned
statement export resolved by :func:`axeyum.agent.tools.resolve_export`, imported
through `import_statement_ndjson` into a real kernel. When no export resolves,
every kernel predicate answers `unevaluable("no-frozen-export")`. Parsing the
ledger's `formal.statement` Lean text into a term would manufacture a goal
nobody pinned and put a fabricated verdict into the backlog.

**Structure, never names.** `tactic-catalog.schema.json` says it outright: a
tactic that dispatches on a declaration name is a dispatch table entry, not a
producer. So `zero-succ`, `le-shaped`, `eq-shaped` and `iff-shaped` families are
discovered here the way `producers/bounded_induction.rs` discovers them -- by
constructor arity and conclusion shape read out of the environment. Nothing in
:class:`Environment` mentions `Nat`, `Nat.le`, `Eq` or `Iff`.

What the census evaluates is the **initial** goal of a fact, opened into its Pi
telescope. Two predicate families in the schema (`residual-gap-shape`, and the
`candidate-argument`/`expected-argument` sites of `occurrence-embeds`) describe
a state that exists only *after* a congruence wrap has run, so at the initial
goal they answer `unevaluable`, never `unmatched`. That is not a gap in the
evaluator; it is the honest reading of a mid-derivation predicate at time zero,
and it is why the two tactics that depend on them report `unevaluable` rather
than a zero that would understate their reach.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from ..knowledge._paths import read_json, require_file, resolve_root

#: Where the committed census lives.
CENSUS_PATH = Path("artifacts") / "autogenesis" / "mobility-census-v1.json"

#: The generated dashboard the capability backlog is read from.
DASHBOARD_PATH = Path("docs") / "plan" / "generated" / "mobility-census.md"

#: The tactic vocabulary this census evaluates. Never written by this module.
CATALOG_PATH = Path("artifacts") / "autogenesis" / "tactic-catalog-v1.json"

#: The frozen-export resolution index, pinned into the census so a later reader
#: can tell a changed answer from a changed input.
EXPORT_INDEX_PATH = Path("artifacts") / "autogenesis" / "agent-frozen-export-index-v1.json"

#: The nursery, whose partitions decide which ids may be written.
NURSERY_PATH = Path("artifacts") / "autogenesis" / "nursery-v1.json"

SCHEMA_VERSION = 1
KIND = "axeyum-mobility-census"

#: Guard on the structural recursion in :func:`canonical_shape`. A kernel term
#: is a DAG and a goal is small; this bounds a pathological import rather than
#: shaping any answer.
MAX_SHAPE_DEPTH = 4096

#: How many leading Pi binders of a goal are opened into the telescope. The
#: producers' own budget is `MAX_BINDERS = 8`; this is deliberately larger so
#: the census never reports "unmatched" for a goal the producer would merely
#: refuse on budget -- a budget decline and a shape decline are different
#: findings and the catalog records them separately.
MAX_TELESCOPE = 64

MATCHED = "matched"
UNMATCHED = "unmatched"
UNEVALUABLE = "unevaluable"


class MobilityError(RuntimeError):
    """The census could not be built from the inputs it was given."""


# --------------------------------------------------------------------------
# The three-valued verdict
# --------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class Verdict:
    """One predicate's (or one tactic's) answer about one goal.

    `outcome` is one of :data:`MATCHED`, :data:`UNMATCHED`, :data:`UNEVALUABLE`.
    `reason` is a stable kebab-case code, empty only for :data:`MATCHED`; it is
    what the zero-match clusters are keyed on, so it must never carry a fact id,
    a path, or anything else that varies between subjects.
    """

    outcome: str
    reason: str = ""

    @property
    def is_matched(self) -> bool:
        return self.outcome == MATCHED

    @property
    def is_unmatched(self) -> bool:
        return self.outcome == UNMATCHED

    @property
    def is_unevaluable(self) -> bool:
        return self.outcome == UNEVALUABLE


def matched() -> Verdict:
    return Verdict(MATCHED)


def unmatched(reason: str) -> Verdict:
    if not reason:
        raise MobilityError("an unmatched verdict without a reason is a bare bool")
    return Verdict(UNMATCHED, reason)


def unevaluable(reason: str) -> Verdict:
    if not reason:
        raise MobilityError("an unevaluable verdict without a reason is a bare bool")
    return Verdict(UNEVALUABLE, reason)


# --------------------------------------------------------------------------
# A structural view of one kernel's environment
# --------------------------------------------------------------------------


@dataclass(slots=True)
class FamilyShapes:
    """Which structural families a kernel's inductives belong to."""

    zero_succ: dict[Any, tuple[Any, Any]] = field(default_factory=dict)
    le_shaped: dict[Any, dict[str, Any]] = field(default_factory=dict)
    eq_shaped: set[Any] = field(default_factory=set)
    iff_shaped: set[Any] = field(default_factory=set)


class Environment:
    """Cached structural facts about one kernel, discovered never by name.

    Mirrors `detect_nat_shape` / `detect_le_shape` in
    `crates/axeyum-lean-import/src/producers/bounded_induction.rs`: a family is
    zero/succ-shaped because it has two constructors, one nullary and one whose
    single field is the family itself, and a recursor eliminating it -- not
    because it is called `Nat`.
    """

    def __init__(self, kernel: Any) -> None:
        self.kernel = kernel
        self._fresh = 1_000_000
        self.decls: dict[Any, Any] = {}
        self.text: dict[Any, str] = {}
        self._ctors: dict[Any, list[Any]] = {}
        self._recursor_families: set[Any] = set()
        for name, declaration in kernel.declarations():
            self.decls[declaration.name] = declaration
            self.text[declaration.name] = name
        for declaration in list(self.decls.values()):
            if declaration.kind == "constructor":
                family = self._conclusion_head_name(declaration.ty)
                if family is not None:
                    self._ctors.setdefault(family, []).append(declaration)
            elif declaration.kind == "recursor":
                self._recursor_families.update(self._binder_domain_heads(declaration.ty))
        self.shapes = FamilyShapes()
        self._classify()

    # -- small structural helpers -----------------------------------------

    def fresh_fvar(self) -> Any:
        self._fresh += 1
        return self.kernel.fvar(self._fresh)

    def node(self, expr: Any) -> Any:
        return self.kernel.expr_node(expr)

    def peel_raw(self, ty: Any) -> tuple[list[Any], Any]:
        """Leading Pi domains and the conclusion, WITHOUT instantiating.

        Loose bound variables survive in both halves. That is fine for every
        question asked of it here (a conclusion's head constant and a domain's
        head constant do not depend on the binder), and it keeps the walk
        allocation-free.
        """
        domains: list[Any] = []
        current = ty
        for _ in range(MAX_TELESCOPE):
            node = self.node(current)
            if node.kind != "pi":
                break
            domains.append(node.ty)
            current = node.body
        return domains, current

    def app_spine(self, expr: Any) -> tuple[Any, list[Any]]:
        """`(head, args)` of a left-nested application."""
        args: list[Any] = []
        current = expr
        for _ in range(MAX_SHAPE_DEPTH):
            node = self.node(current)
            if node.kind != "app":
                break
            args.append(node.arg)
            current = node.fun
        args.reverse()
        return current, args

    def head_const(self, expr: Any) -> Any | None:
        head, _ = self.app_spine(expr)
        node = self.node(head)
        return node.name if node.kind == "const" else None

    def _conclusion_head_name(self, ty: Any) -> Any | None:
        _, conclusion = self.peel_raw(ty)
        return self.head_const(conclusion)

    def _binder_domain_heads(self, ty: Any) -> set[Any]:
        domains, _ = self.peel_raw(ty)
        out: set[Any] = set()
        for domain in domains:
            name = self.head_const(domain)
            if name is not None:
                out.add(name)
        return out

    def is_prop_valued(self, family: Any) -> bool:
        """Whether a declaration's type ends in `Sort 0`."""
        declaration = self.decls.get(family)
        if declaration is None:
            return False
        _, conclusion = self.peel_raw(declaration.ty)
        node = self.node(conclusion)
        if node.kind != "sort":
            return False
        return bool(self.kernel.level_is_zero(node.level))

    def expression_is_prop(self, ty: Any) -> bool:
        """Whether a *term* denotes a proposition, decided structurally.

        `Kernel.infer` cannot be used: the telescope is opened with free
        variables and an fvar has no type in this kernel (`UnboundFVar`), so
        inference raises on exactly the terms this predicate is asked about. The
        structural reading -- a Pi is a Prop when its conclusion is, an
        application is a Prop when its head declaration is Prop-valued -- agrees
        with inference on every well-typed goal and never raises.
        """
        current = ty
        for _ in range(MAX_TELESCOPE):
            node = self.node(current)
            if node.kind != "pi":
                break
            current = node.body
        head = self.head_const(current)
        if head is None:
            return False
        return self.is_prop_valued(head)

    # -- family classification --------------------------------------------

    def _classify(self) -> None:
        for family, declaration in self.decls.items():
            if declaration.kind != "inductive":
                continue
            ctors = self._ctors.get(family, [])
            zero_succ = self._as_zero_succ(family, declaration, ctors)
            if zero_succ is not None:
                self.shapes.zero_succ[family] = zero_succ
            le_shape = self._as_le_shaped(family, declaration, ctors)
            if le_shape is not None:
                self.shapes.le_shaped[family] = le_shape
            if self._as_eq_shaped(family, declaration, ctors):
                self.shapes.eq_shaped.add(family)
            if self._as_iff_shaped(family, declaration, ctors):
                self.shapes.iff_shaped.add(family)

    def _as_zero_succ(
        self, family: Any, declaration: Any, ctors: list[Any]
    ) -> tuple[Any, Any] | None:
        domains, conclusion = self.peel_raw(declaration.ty)
        if domains or self.node(conclusion).kind != "sort":
            return None
        if len(ctors) != 2 or family not in self._recursor_families:
            return None
        first, second = ctors[0], ctors[1]
        for zero, succ in ((first, second), (second, first)):
            if self._ctor_is_nullary(zero, family) and self._ctor_is_unary_recursive(succ, family):
                return (zero.name, succ.name)
        return None

    def _ctor_is_nullary(self, ctor: Any, family: Any) -> bool:
        domains, conclusion = self.peel_raw(ctor.ty)
        return not domains and self.head_const(conclusion) == family

    def _ctor_is_unary_recursive(self, ctor: Any, family: Any) -> bool:
        domains, conclusion = self.peel_raw(ctor.ty)
        if len(domains) != 1:
            return False
        return self.head_const(domains[0]) == family and self.head_const(conclusion) == family

    def _as_le_shaped(
        self, family: Any, declaration: Any, ctors: list[Any]
    ) -> dict[str, Any] | None:
        domains, conclusion = self.peel_raw(declaration.ty)
        if len(domains) != 2 or not self._is_prop_sort(conclusion):
            return None
        if len(ctors) != 2 or family not in self._recursor_families:
            return None
        for refl, step in ((ctors[0], ctors[1]), (ctors[1], ctors[0])):
            shape = self._try_le_pair(family, refl, step)
            if shape is not None:
                return shape
        return None

    def _is_prop_sort(self, expr: Any) -> bool:
        node = self.node(expr)
        return node.kind == "sort" and bool(self.kernel.level_is_zero(node.level))

    def _try_le_pair(self, family: Any, refl: Any, step: Any) -> dict[str, Any] | None:
        kernel = self.kernel
        # refl : (p : P) -> family p p
        refl_domains, refl_conclusion = self.peel_raw(refl.ty)
        if len(refl_domains) != 1:
            return None
        p = self.fresh_fvar()
        refl_body = kernel.instantiate(refl_conclusion, [p])
        head, args = self.app_spine(refl_body)
        if self.node(head).kind != "const" or self.node(head).name != family or len(args) != 2:
            return None
        if not (kernel.def_eq(args[0], p) and kernel.def_eq(args[1], p)):
            return None
        # step : (p : P) (m : Q) (_ : family p m) -> family p (succ m)
        step_domains, step_conclusion = self.peel_raw(step.ty)
        if len(step_domains) != 3:
            return None
        p2, m, h = self.fresh_fvar(), self.fresh_fvar(), self.fresh_fvar()
        index_ty = kernel.instantiate(step_domains[1], [p2])
        hypothesis = kernel.instantiate(step_domains[2], [p2, m])
        conclusion = kernel.instantiate(step_conclusion, [p2, m, h])
        h_head, h_args = self.app_spine(hypothesis)
        if self.node(h_head).kind != "const" or self.node(h_head).name != family:
            return None
        if len(h_args) != 2 or not (kernel.def_eq(h_args[0], p2) and kernel.def_eq(h_args[1], m)):
            return None
        c_head, c_args = self.app_spine(conclusion)
        if self.node(c_head).kind != "const" or self.node(c_head).name != family:
            return None
        if len(c_args) != 2 or not kernel.def_eq(c_args[0], p2):
            return None
        index_family = self.head_const(kernel.whnf(index_ty))
        if index_family is None or index_family not in self.shapes.zero_succ:
            return None
        zero_ctor, succ_ctor = self.shapes.zero_succ[index_family]
        succ_m = kernel.app(kernel.const_(succ_ctor, []), m)
        if not kernel.def_eq(c_args[1], succ_m):
            return None
        return {
            "index_family": index_family,
            "zero_ctor": zero_ctor,
            "succ_ctor": succ_ctor,
            "refl_ctor": refl.name,
            "step_ctor": step.name,
        }

    def _as_eq_shaped(self, family: Any, declaration: Any, ctors: list[Any]) -> bool:
        domains, conclusion = self.peel_raw(declaration.ty)
        if len(domains) < 2 or not self._is_prop_sort(conclusion) or len(ctors) != 1:
            return False
        ctor = ctors[0]
        ctor_domains, ctor_conclusion = self.peel_raw(ctor.ty)
        if not ctor_domains:
            return False
        fvars = [self.fresh_fvar() for _ in ctor_domains]
        body = self.kernel.instantiate(ctor_conclusion, fvars)
        head, args = self.app_spine(body)
        if self.node(head).kind != "const" or self.node(head).name != family or len(args) < 2:
            return False
        return bool(self.kernel.def_eq(args[-1], args[-2]))

    def _as_iff_shaped(self, family: Any, declaration: Any, ctors: list[Any]) -> bool:
        domains, conclusion = self.peel_raw(declaration.ty)
        if len(domains) != 2 or not self._is_prop_sort(conclusion) or len(ctors) != 1:
            return False
        if not all(self._is_prop_sort(domain) for domain in domains):
            return False
        ctor_domains, _ = self.peel_raw(ctors[0].ty)
        # (a : Prop) (b : Prop) (mp : a -> b) (mpr : b -> a)
        return len(ctor_domains) == 4


# --------------------------------------------------------------------------
# One goal, opened
# --------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class Binder:
    """One opened leading Pi binder of the goal."""

    domain: Any
    fvar: Any
    is_hypothesis: bool


class GoalView:
    """A kernel goal with its Pi telescope opened and its hypotheses named.

    The **hypothesis set** is the leading Pi binders whose domain denotes a
    proposition; the **conclusion** is what is left. A census over an initial
    goal has no other notion of "a hypothesis retained along the derivation",
    and saying so is better than pretending the derivation already ran.
    """

    def __init__(self, kernel: Any, goal: Any, environment: Environment | None = None) -> None:
        self.kernel = kernel
        self.goal = goal
        self.env = environment if environment is not None else Environment(kernel)
        self.binders: list[Binder] = []
        current = goal
        for _ in range(MAX_TELESCOPE):
            node = kernel.expr_node(current)
            if node.kind != "pi":
                break
            fvar = self.env.fresh_fvar()
            self.binders.append(Binder(node.ty, fvar, self.env.expression_is_prop(node.ty)))
            current = kernel.instantiate(node.body, [fvar])
        self.conclusion = current

    # -- derived views -----------------------------------------------------

    @property
    def hypotheses(self) -> list[Binder]:
        return [b for b in self.binders if b.is_hypothesis]

    @property
    def data_binders(self) -> list[Binder]:
        return [b for b in self.binders if not b.is_hypothesis]

    def whnf_conclusion(self) -> Any:
        return self.kernel.whnf(self.conclusion)

    def as_equation(self, expr: Any) -> tuple[Any, Any] | None:
        """`(lhs, rhs)` when `expr` is an application of an Eq-shaped family."""
        head, args = self.env.app_spine(expr)
        node = self.kernel.expr_node(head)
        if node.kind != "const" or node.name not in self.env.shapes.eq_shaped:
            return None
        if len(args) < 2:
            return None
        return (args[-2], args[-1])

    def carrier(self, expr: Any) -> Any | None:
        """The Eq-shaped family's carrier argument, when there is one."""
        head, args = self.env.app_spine(expr)
        node = self.kernel.expr_node(head)
        if node.kind != "const" or node.name not in self.env.shapes.eq_shaped:
            return None
        return args[0] if len(args) >= 3 else None

    def goal_equation(self) -> tuple[Any, Any] | None:
        direct = self.as_equation(self.conclusion)
        if direct is not None:
            return direct
        return self.as_equation(self.whnf_conclusion())

    def hypothesis_equations(self) -> list[tuple[Binder, tuple[Any, Any], Any]]:
        """Every hypothesis whose type is (or unfolds to) an equation."""
        out: list[tuple[Binder, tuple[Any, Any], Any]] = []
        for binder in self.hypotheses:
            for candidate in (binder.domain, self.kernel.whnf(binder.domain)):
                sides = self.as_equation(candidate)
                if sides is not None:
                    out.append((binder, sides, candidate))
                    break
        return out


# --------------------------------------------------------------------------
# Occurrence search
# --------------------------------------------------------------------------


def subterms(kernel: Any, expr: Any, limit: int = MAX_SHAPE_DEPTH) -> set[Any]:
    """Every subterm reachable through App / binder types and bodies / Proj / Let.

    This is the census's reading of the catalog's `kabstract-occurrences`: the
    same reachability `Expr.kabstract` walks. `app-spine` is the narrower
    alternative and is handled by the caller.
    """
    seen: set[Any] = set()
    stack = [expr]
    while stack and len(seen) < limit:
        current = stack.pop()
        if current in seen:
            continue
        seen.add(current)
        node = kernel.expr_node(current)
        for child in (node.fun, node.arg, node.ty, node.body, node.value, node.structure):
            if child is not None:
                stack.append(child)
    return seen


# --------------------------------------------------------------------------
# The predicate vocabulary
# --------------------------------------------------------------------------

#: Reason codes for a predicate that describes a state which exists only after a
#: move has run. They are `unevaluable`, never `unmatched`.
MID_DERIVATION = "requires-mid-derivation-state"


def _predicate_goal_head(view: GoalView, args: dict[str, Any]) -> Verdict:
    head = args["head"]
    if head == "any-prop":
        if view.env.expression_is_prop(view.conclusion):
            return matched()
        return unmatched("conclusion-is-not-a-proposition")
    conclusion = view.conclusion
    family = view.env.head_const(conclusion)
    if family is None:
        return unmatched("conclusion-has-no-constant-head")
    shapes = view.env.shapes
    if head == "Eq":
        if family in shapes.eq_shaped:
            return matched()
        return unmatched("goal-head-is-not-eq-shaped")
    if head == "Iff":
        if family in shapes.iff_shaped:
            return matched()
        return unmatched("goal-head-is-not-iff-shaped")
    return unevaluable(f"unknown-goal-head-class:{head}")


def _predicate_sides_definitionally_equal(view: GoalView, args: dict[str, Any]) -> Verdict:
    want = bool(args["value"])
    sides = view.goal_equation()
    if sides is None:
        return unmatched("goal-is-not-an-equation-so-it-has-no-sides")
    same = bool(view.kernel.def_eq(sides[0], sides[1]))
    if same == want:
        return matched()
    return unmatched("sides-definitionally-equal" if same else "sides-not-definitionally-equal")


def _predicate_binder_shape(view: GoalView, args: dict[str, Any]) -> Verdict:
    shape = args["shape"]
    if not view.binders:
        return unmatched("goal-has-no-leading-pi-binder")
    if shape == "hypothesis-pi":
        if view.hypotheses:
            return matched()
        return unmatched("no-leading-hypothesis-binder")
    if shape == "ordinary-pi":
        if view.data_binders:
            return matched()
        return unmatched("no-leading-data-binder")
    if shape == "zero-succ":
        zero_succ = view.env.shapes.zero_succ
        for binder in view.data_binders:
            family = view.env.head_const(view.kernel.whnf(binder.domain))
            if family is not None and family in zero_succ:
                return matched()
        return unmatched("no-zero-succ-shaped-binder")
    return unevaluable(f"unknown-binder-shape:{shape}")


def _index_class(view: GoalView, expr: Any, zero_ctor: Any, succ_ctor: Any) -> str:
    kernel = view.kernel
    if kernel.def_eq(expr, kernel.const_(zero_ctor, [])):
        return "zero"
    head, spine_args = view.env.app_spine(kernel.whnf(expr))
    node = kernel.expr_node(head)
    if node.kind == "const" and node.name == succ_ctor and len(spine_args) == 1:
        return "succ"
    return "other"


def _predicate_hypothesis_family(view: GoalView, args: dict[str, Any]) -> Verdict:
    family_class = args["family"]
    want_index = args.get("index", "any")
    want_parameter = args.get("parameter", "any")
    shapes = view.env.shapes
    if not view.hypotheses:
        return unmatched("no-hypothesis-binder-to-classify")
    saw_family = False
    for binder in view.hypotheses:
        domain = view.kernel.whnf(binder.domain)
        head, spine_args = view.env.app_spine(domain)
        node = view.kernel.expr_node(head)
        if node.kind != "const":
            continue
        if family_class == "le-shaped":
            shape = shapes.le_shaped.get(node.name)
            if shape is None or len(spine_args) != 2:
                continue
            saw_family = True
            parameter, index = spine_args[0], spine_args[1]
            zero_ctor, succ_ctor = shape["zero_ctor"], shape["succ_ctor"]
        elif family_class == "eq-shaped":
            if node.name not in shapes.eq_shaped or len(spine_args) < 2:
                continue
            saw_family = True
            parameter, index = spine_args[-2], spine_args[-1]
            zero_succ = _sole_zero_succ(view)
            if zero_succ is None:
                if want_index == "any" and want_parameter == "any":
                    return matched()
                return unevaluable("no-zero-succ-family-to-classify-an-index-against")
            zero_ctor, succ_ctor = zero_succ
        else:
            return unevaluable(f"unknown-hypothesis-family:{family_class}")
        index_ok = (
            want_index == "any" or _index_class(view, index, zero_ctor, succ_ctor) == want_index
        )
        parameter_ok = (
            want_parameter == "any"
            or _index_class(view, parameter, zero_ctor, succ_ctor) == want_parameter
        )
        if index_ok and parameter_ok:
            return matched()
    if saw_family:
        return unmatched(f"hypothesis-{family_class}-index-or-parameter-mismatch")
    return unmatched(f"no-{family_class}-hypothesis")


def _sole_zero_succ(view: GoalView) -> tuple[Any, Any] | None:
    zero_succ = view.env.shapes.zero_succ
    if len(zero_succ) == 1:
        return next(iter(zero_succ.values()))
    return None


def _predicate_hypothesis_state(view: GoalView, args: dict[str, Any]) -> Verdict:
    state = args["state"]
    goal_sides = view.goal_equation()
    equations = view.hypothesis_equations()
    if state == "absent":
        if not equations:
            return matched()
        return unmatched("an-equation-shaped-hypothesis-is-present")
    if state in {"available", "stuck"}:
        if not equations:
            return unmatched("no-equation-shaped-hypothesis")
        if goal_sides is None:
            return unmatched("goal-is-not-an-equation-so-no-hypothesis-can-agree-with-it")
        goal_carrier = view.carrier(view.conclusion) or view.carrier(view.whnf_conclusion())
        agrees = False
        undecided = False
        for _binder, _sides, typed in equations:
            hypothesis_carrier = view.carrier(typed)
            if goal_carrier is None or hypothesis_carrier is None:
                undecided = True
                continue
            if view.kernel.def_eq(goal_carrier, hypothesis_carrier):
                agrees = True
        if not agrees and undecided:
            return unevaluable("equation-carrier-is-not-readable-on-both-sides")
        if state == "available":
            return matched() if agrees else unmatched("hypothesis-domain-does-not-agree-with-goal")
        return matched() if not agrees else unmatched("hypothesis-agrees-so-it-is-not-stuck")
    return unevaluable(f"unknown-hypothesis-state:{state}")


def _needle_expression(view: GoalView, needle: str) -> tuple[Any | None, str]:
    equations = view.hypothesis_equations()
    if needle in {"hypothesis-lhs", "hypothesis-rhs"}:
        if not equations:
            return None, "no-equation-shaped-hypothesis-to-take-a-side-from"
        _binder, sides, _typed = equations[0]
        return (sides[0] if needle == "hypothesis-lhs" else sides[1]), ""
    if needle == "candidate-argument":
        return None, MID_DERIVATION
    return None, f"unknown-needle:{needle}"


def _haystack_expression(view: GoalView, haystack: str) -> tuple[Any | None, str]:
    sides = view.goal_equation()
    if haystack in {"goal-lhs-whnf", "goal-rhs-whnf"}:
        if sides is None:
            return None, "goal-is-not-an-equation-so-it-has-no-sides"
        side = sides[0] if haystack == "goal-lhs-whnf" else sides[1]
        return view.kernel.whnf(side), ""
    if haystack == "expected-argument":
        return None, MID_DERIVATION
    return None, f"unknown-haystack:{haystack}"


def _predicate_occurrence_embeds(view: GoalView, args: dict[str, Any]) -> Verdict:
    needle, needle_reason = _needle_expression(view, args["needle"])
    haystack, haystack_reason = _haystack_expression(view, args["haystack"])
    for reason in (needle_reason, haystack_reason):
        if reason == MID_DERIVATION:
            return unevaluable(MID_DERIVATION)
    if needle_reason.startswith("unknown-") or haystack_reason.startswith("unknown-"):
        return unevaluable(needle_reason or haystack_reason)
    if needle is None:
        return unmatched(needle_reason)
    if haystack is None:
        return unmatched(haystack_reason)
    via = args["via"]
    if via == "kabstract-occurrences":
        found = needle in subterms(view.kernel, haystack)
    elif via == "app-spine":
        _head, spine_args = view.env.app_spine(haystack)
        found = any(view.kernel.def_eq(arg, needle) for arg in spine_args)
    else:
        return unevaluable(f"unknown-occurrence-search:{via}")
    if found:
        return matched()
    return unmatched(f"needle-does-not-occur-in-haystack-via-{via}")


def _predicate_residual_gap_shape(view: GoalView, args: dict[str, Any]) -> Verdict:
    shape = args["shape"]
    if shape not in {
        "single-argument-diff",
        "multi-argument-diff-same-head",
        "collapsed-occurrence-site",
    }:
        return unevaluable(f"unknown-residual-gap-shape:{shape}")
    return unevaluable(MID_DERIVATION)


def _predicate_spine_argument_matches(view: GoalView, args: dict[str, Any]) -> Verdict:
    if args["position"] != "any-top-level":
        return unevaluable(f"unknown-spine-position:{args['position']}")
    if args["target"] != "goal-rhs":
        return unevaluable(f"unknown-spine-target:{args['target']}")
    sides = view.goal_equation()
    if sides is None:
        return unmatched("goal-is-not-an-equation-so-it-has-no-sides")
    _head, spine_args = view.env.app_spine(sides[0])
    if not spine_args:
        return unmatched("goal-lhs-has-no-top-level-arguments")
    if any(view.kernel.def_eq(arg, sides[1]) for arg in spine_args):
        return matched()
    return unmatched("no-top-level-argument-equals-the-goal-rhs")


def _predicate_head_unfolds(view: GoalView, args: dict[str, Any]) -> Verdict:
    if args["via"] != "whnf-delta":
        return unevaluable(f"unknown-unfolding:{args['via']}")
    target = args["to"]
    unfolded = view.whnf_conclusion()
    family = view.env.head_const(unfolded)
    if family is None:
        return unmatched("whnf-of-the-goal-has-no-constant-head")
    shapes = view.env.shapes
    if target == "Eq":
        if family in shapes.eq_shaped:
            return matched()
        return unmatched("goal-does-not-unfold-to-an-eq-shaped-head")
    if target == "Iff":
        if family in shapes.iff_shaped:
            return matched()
        return unmatched("goal-does-not-unfold-to-an-iff-shaped-head")
    return unevaluable(f"unknown-unfolding-target:{target}")


#: Every predicate `kind` the catalog schema enumerates. A catalog carrying a
#: kind absent from here is a hard error rather than a silent skip: a census
#: that quietly ignored a predicate would report a tactic as matched on a
#: precondition it never evaluated.
PREDICATES = {
    "goal-head": _predicate_goal_head,
    "sides-definitionally-equal": _predicate_sides_definitionally_equal,
    "binder-shape": _predicate_binder_shape,
    "hypothesis-family": _predicate_hypothesis_family,
    "hypothesis-state": _predicate_hypothesis_state,
    "occurrence-embeds": _predicate_occurrence_embeds,
    "residual-gap-shape": _predicate_residual_gap_shape,
    "spine-argument-matches": _predicate_spine_argument_matches,
    "head-unfolds": _predicate_head_unfolds,
}


def evaluate_predicate(view: GoalView, predicate: dict[str, Any]) -> Verdict:
    """One typed structural predicate against one opened goal."""
    kind = predicate.get("kind")
    handler = PREDICATES.get(str(kind))
    if handler is None:
        raise MobilityError(
            f"the catalog carries predicate kind {kind!r}, which this evaluator does not "
            f"implement; a census that skipped it would report an unevaluated precondition "
            f"as satisfied"
        )
    args = predicate.get("args") or {}
    return handler(view, dict(args))


@dataclass(frozen=True, slots=True)
class TacticVerdict:
    """A tactic's precondition against one goal, with the reason it failed."""

    tactic_id: str
    verdict: Verdict
    predicate_reasons: tuple[str, ...]


def evaluate_tactic(view: GoalView, tactic: dict[str, Any]) -> TacticVerdict:
    """`all_of` over the tactic's predicates, three-valued.

    An `unmatched` predicate wins over an `unevaluable` one: knowing that a
    precondition is structurally violated is a stronger answer than knowing that
    a different conjunct could not be inspected, and the census would rather
    place a fact in a named cluster than in the unevaluable bucket.
    """
    predicates = ((tactic.get("precondition") or {}).get("structural") or {}).get("all_of") or []
    if not predicates:
        raise MobilityError(f"{tactic.get('id')} has no structural precondition to evaluate")
    reasons: list[str] = []
    unevaluables: list[str] = []
    for predicate in predicates:
        verdict = evaluate_predicate(view, predicate)
        if verdict.is_unmatched:
            reasons.append(verdict.reason)
        elif verdict.is_unevaluable:
            unevaluables.append(verdict.reason)
    tactic_id = str(tactic.get("id"))
    if reasons:
        return TacticVerdict(tactic_id, unmatched(reasons[0]), tuple(sorted(set(reasons))))
    if unevaluables:
        return TacticVerdict(
            tactic_id, unevaluable(unevaluables[0]), tuple(sorted(set(unevaluables)))
        )
    return TacticVerdict(tactic_id, matched(), ())


# --------------------------------------------------------------------------
# Goal shapes
# --------------------------------------------------------------------------


def canonical_shape(kernel: Any, expr: Any) -> str:
    """A rendering of `expr` with every binder NAME erased.

    Two goals have the same shape exactly when this string agrees. Binder names
    are erased because an imported Mathlib statement carries hygienic names
    (`a._@._internal._hyg._0`) that differ between exports of the same shape --
    counting those as distinct shapes would inflate every tactic's reach.
    """
    parts: list[str] = []
    stack: list[Any] = [expr]
    depth = 0
    while stack:
        depth += 1
        if depth > MAX_SHAPE_DEPTH:
            raise MobilityError("goal is deeper than the canonical-shape budget")
        current = stack.pop()
        if isinstance(current, str):
            parts.append(current)
            continue
        node = kernel.expr_node(current)
        kind = node.kind
        if kind == "bvar":
            parts.append(f"b{node.index}")
        elif kind == "fvar":
            parts.append(f"f{node.fvar_id}")
        elif kind == "sort":
            parts.append(f"s[{kernel.render_lean(kernel.sort(node.level))}]")
        elif kind == "const":
            levels = ",".join(
                kernel.render_lean(kernel.sort(level)) for level in (node.levels or [])
            )
            parts.append(f"c[{kernel.display_name(node.name)}|{levels}]")
        elif kind == "app":
            parts.append("(")
            stack.extend([")", node.arg, " ", node.fun])
        elif kind in {"lam", "pi"}:
            parts.append("L(" if kind == "lam" else "P(")
            stack.extend([")", node.body, "->", node.ty])
        elif kind == "let":
            parts.append("T(")
            stack.extend([")", node.body, ";", node.value, ":", node.ty])
        elif kind == "proj":
            parts.append(f"j[{kernel.display_name(node.name)}.{node.field_index}](")
            stack.extend([")", node.structure])
        else:
            lit = node.lit
            parts.append(f"l[{getattr(lit, 'kind', '?')}:{getattr(lit, 'value', '?')}]")
    return "".join(parts)


def shape_sha256(kernel: Any, expr: Any) -> str:
    return hashlib.sha256(canonical_shape(kernel, expr).encode("utf-8")).hexdigest()


# --------------------------------------------------------------------------
# Goal sourcing
# --------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class GoalSource:
    """Where a fact's kernel goal came from, or why there is none."""

    fact_id: str
    view: GoalView | None
    source: str
    reason: str

    @property
    def evaluable(self) -> bool:
        return self.view is not None


def load_goal(root: Path, fact_id: str) -> GoalSource:
    """Resolve, verify and import the frozen statement export for one fact.

    There is exactly one route and it is digest-pinned. A fact with no export is
    `unevaluable("no-frozen-export")`: not looked at, and recorded as such.
    """
    from .. import producers as producers_api
    from . import tools as tools_api

    try:
        export = tools_api.resolve_export(root, fact_id)
    except tools_api.ExportUnavailable as error:
        text = str(error)
        if "not on this host" in text:
            return GoalSource(fact_id, None, "none", "frozen-export-not-on-this-host")
        if "does not hash" in text:
            return GoalSource(fact_id, None, "none", "frozen-export-digest-mismatch")
        return GoalSource(fact_id, None, "none", "no-frozen-export")
    try:
        imported = producers_api.import_statement_ndjson(
            str(export.path), None, export.target_definition
        )
    except Exception as error:  # noqa: BLE001 - an import failure is a datapoint
        return GoalSource(
            fact_id, None, export.source, f"statement-import-failed:{type(error).__name__}"
        )
    kernel = imported.kernel()
    goal = imported.goal()
    return GoalSource(fact_id, GoalView(kernel, goal), export.source, "")


# --------------------------------------------------------------------------
# The census
# --------------------------------------------------------------------------


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode("utf-8")).hexdigest()


def file_sha256(path: Path) -> str:
    return hashlib.sha256(require_file(path).read_bytes()).hexdigest()


def ledger_sha256(root: Path) -> str:
    """The same digest `scripts/fact-frontier.py` stamps in its `ledger` block.

    Recomputed rather than read out of a frontier document so the census pins the
    ledger it actually evaluated, and so it is comparable to a committed episode.
    """
    facts: dict[str, Any] = {}
    for path in sorted((root / "artifacts" / "facts").glob("*.json")):
        document = json.loads(path.read_text(encoding="utf-8"))
        facts[document["id"]] = document
    return digest(
        [{"fact_id": fact_id, "fact_sha256": digest(facts[fact_id])} for fact_id in sorted(facts)]
    )


def git_commit(root: Path, override: str | None = None) -> str:
    if override:
        return override
    try:
        completed = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=str(root),
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        completed = None
    if completed is not None and completed.returncode == 0:
        return completed.stdout.strip()
    lane_ref = root / ".lane-ref"
    if lane_ref.is_file():
        text = lane_ref.read_text(encoding="utf-8").strip()
        if len(text) == 40:
            return text
    raise MobilityError(
        f"{root} is not a git checkout and carries no 40-hex .lane-ref; pass --git-commit "
        f"so the census pins the tree it measured"
    )


def load_catalog(root: Path) -> tuple[list[dict[str, Any]], str]:
    path = root / CATALOG_PATH
    document = read_json(path)
    tactics = document.get("tactics")
    if not isinstance(tactics, list) or not tactics:
        raise MobilityError(f"{path} carries no tactics; a census over nothing is not a census")
    return sorted(tactics, key=lambda t: str(t["id"])), file_sha256(path)


def open_facts(root: Path) -> list[Any]:
    from ..knowledge import facts as facts_api

    ledger = facts_api.load(root)
    return sorted((fact for fact in ledger if fact.is_open), key=lambda f: f.id)


def build_census(
    root: Path,
    *,
    commit: str | None = None,
    fact_ids: list[str] | None = None,
) -> dict[str, Any]:
    """Evaluate every tactic precondition against every open fact.

    Held-out ids are counted and never written. That is not belt-and-braces: the
    nursery's partitions are a shared blind population and a single leaked id
    spends its whole split key (CLAUDE.md, "19 of 76 held-out propositions for
    one theorem"). :func:`assert_no_held_out` re-checks the serialized document.
    """
    from ..knowledge import nursery as nursery_api

    tactics, catalog_digest = load_catalog(root)
    nursery = nursery_api.load(root)
    held_out = set(nursery.held_out_ids())
    facts = open_facts(root)
    if fact_ids is not None:
        wanted = set(fact_ids)
        facts = [fact for fact in facts if fact.id in wanted]

    rows: list[dict[str, Any]] = []
    held_out_rows = 0
    held_out_evaluable = 0
    partition_counts: dict[str, dict[str, int]] = {}
    tactic_matches: dict[str, list[str]] = {tactic["id"]: [] for tactic in tactics}
    tactic_shapes: dict[str, set[str]] = {tactic["id"]: set() for tactic in tactics}
    unevaluable_reasons: dict[str, int] = {}
    export_sources: dict[str, int] = {}
    matched_pairs = 0
    unmatched_pairs = 0
    unevaluable_pairs = 0

    for fact in facts:
        partition = nursery.partition_of(fact.id) if nursery.contains(fact.id) else "not-in-nursery"
        bucket = partition_counts.setdefault(
            partition, {"open": 0, "evaluable": 0, "unevaluable": 0, "zero_match": 0}
        )
        bucket["open"] += 1
        source = load_goal(root, fact.id)
        is_held_out = fact.id in held_out or partition == "held-out"
        if is_held_out:
            held_out_rows += 1
        if not source.evaluable:
            bucket["unevaluable"] += 1
            unevaluable_reasons[source.reason] = unevaluable_reasons.get(source.reason, 0) + 1
            unevaluable_pairs += len(tactics)
            if not is_held_out:
                rows.append(
                    {
                        "fact_id": fact.id,
                        "partition": partition,
                        "evaluable": False,
                        "goal_source": source.source,
                        "unevaluable_reason": source.reason,
                        "mobility": 0,
                        "matched": [],
                        "unmatched": {},
                        "unevaluable": {tactic["id"]: source.reason for tactic in tactics},
                    }
                )
            continue
        bucket["evaluable"] += 1
        if is_held_out:
            held_out_evaluable += 1
        export_sources[source.source] = export_sources.get(source.source, 0) + 1
        view = source.view
        assert view is not None
        shape = shape_sha256(view.kernel, view.goal)
        matched_ids: list[str] = []
        unmatched_map: dict[str, str] = {}
        unevaluable_map: dict[str, str] = {}
        for tactic in tactics:
            outcome = evaluate_tactic(view, tactic)
            if outcome.verdict.is_matched:
                matched_ids.append(outcome.tactic_id)
                matched_pairs += 1
                tactic_matches[outcome.tactic_id].append(fact.id)
                tactic_shapes[outcome.tactic_id].add(shape)
            elif outcome.verdict.is_unmatched:
                unmatched_map[outcome.tactic_id] = outcome.verdict.reason
                unmatched_pairs += 1
            else:
                unevaluable_map[outcome.tactic_id] = outcome.verdict.reason
                unevaluable_pairs += 1
        if not matched_ids:
            bucket["zero_match"] += 1
        if is_held_out:
            continue
        rows.append(
            {
                "fact_id": fact.id,
                "partition": partition,
                "evaluable": True,
                "goal_source": source.source,
                "goal_shape_sha256": shape,
                "mobility": len(matched_ids),
                "matched": sorted(matched_ids),
                "unmatched": dict(sorted(unmatched_map.items())),
                "unevaluable": dict(sorted(unevaluable_map.items())),
            }
        )

    clusters = build_clusters(rows)
    zero_match_total = sum(bucket["zero_match"] for bucket in partition_counts.values())
    evaluable_total = sum(bucket["evaluable"] for bucket in partition_counts.values())
    unevaluable_total = sum(bucket["unevaluable"] for bucket in partition_counts.values())

    census = {
        "schema_version": SCHEMA_VERSION,
        "kind": KIND,
        "generated_by": "python -m axeyum.agent mobility",
        "git_commit": git_commit(root, commit),
        "catalog_path": CATALOG_PATH.as_posix(),
        "catalog_sha256": catalog_digest,
        "ledger_sha256": ledger_sha256(root),
        "export_index_path": EXPORT_INDEX_PATH.as_posix(),
        "export_index_sha256": file_sha256(root / EXPORT_INDEX_PATH),
        "nursery_sha256": file_sha256(root / NURSERY_PATH),
        "holdout_policy": (
            "Held-out fact ids are never written to this file. Held-out rows are counted in "
            "`totals.held_out_excluded` and in `partitions['held-out']` and appear nowhere else; "
            "the writer re-scans the serialized document for every held-out id before it lands."
        ),
        "semantics": {
            "goal_source": (
                "A frozen, digest-pinned statement export resolved through "
                "agent.tools.resolve_export and imported with import_statement_ndjson. No goal is "
                "parsed from ledger text."
            ),
            "evaluation_point": (
                "The fact's INITIAL goal, opened into its Pi telescope. Hypotheses are the leading "
                "Pi binders whose domain denotes a proposition."
            ),
            "mid_derivation": (
                "residual-gap-shape, and the candidate-argument/expected-argument sites of "
                "occurrence-embeds, describe a state that exists only after a move has run; at the "
                f"initial goal they answer unevaluable('{MID_DERIVATION}')."
            ),
            "aggregation": "all_of; an unmatched predicate wins over an unevaluable one.",
            "shape": (
                "sha256 of a canonical rendering of the goal with every binder NAME erased "
                "(mobility.canonical_shape)."
            ),
        },
        "totals": {
            "open_facts": len(facts),
            "evaluable": evaluable_total,
            "unevaluable": unevaluable_total,
            "tactics": len(tactics),
            "pairs": len(facts) * len(tactics),
            "matched_pairs": matched_pairs,
            "unmatched_pairs": unmatched_pairs,
            "unevaluable_pairs": unevaluable_pairs,
            "zero_match_facts": zero_match_total,
            "clusters": len(clusters),
            "held_out_excluded": held_out_rows,
            "held_out_evaluable": held_out_evaluable,
            "written_fact_rows": len(rows),
        },
        "partitions": {name: dict(counts) for name, counts in sorted(partition_counts.items())},
        "export_coverage": {
            "open_facts_with_export": evaluable_total,
            "by_source": dict(sorted(export_sources.items())),
        },
        "unevaluable_reasons": dict(sorted(unevaluable_reasons.items())),
        "tactics": [
            {
                "id": str(tactic["id"]),
                "title": str(tactic["title"]),
                "kind": str(tactic["kind"]),
                "status": str(tactic["status"]),
                "matched_facts": len(tactic_matches[tactic["id"]]),
                "distinct_goal_shapes_matched": len(tactic_shapes[tactic["id"]]),
                "catalog_reach_accepted": len(tactic["reach"]["accepted_goals"]),
                "catalog_reach_declined": len(tactic["reach"]["declined_goals"]),
                "matched_fact_ids": sorted(
                    fid for fid in tactic_matches[tactic["id"]] if fid not in held_out
                ),
            }
            for tactic in tactics
        ],
        "facts": rows,
        "zero_match_clusters": clusters,
        "must_decline_sampling": must_decline_summary(root),
    }
    assert_no_held_out(census, held_out)
    return census


def build_clusters(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Zero-match facts grouped by the tuple of reasons that rejected them.

    Only **evaluable** facts can be zero-match: an unevaluable fact was never
    looked at, and putting it in a capability cluster would name a capability
    that would not have helped.
    """
    buckets: dict[tuple[str, ...], list[str]] = {}
    for row in rows:
        if not row["evaluable"] or row["mobility"] > 0:
            continue
        key = tuple(sorted(set(row["unmatched"].values())))
        buckets.setdefault(key, []).append(row["fact_id"])
    # Annotated because the rows are heterogeneous JSON: without it the value
    # type infers as `list[str] | int` and `-cluster["size"]` below is a unary
    # minus on a union the checker cannot accept.
    clusters: list[dict[str, Any]] = [
        {"reasons": list(key), "size": len(ids), "fact_ids": sorted(ids)}
        for key, ids in buckets.items()
    ]
    clusters.sort(key=lambda c: (-c["size"], c["reasons"]))
    return clusters


def assert_no_held_out(census: dict[str, Any], held_out: set[str]) -> None:
    """Fail loudly if any held-out id reached the serialized document.

    A positive control lives beside this in the tests: the same scan over a
    document that DOES carry a held-out id must raise, or the guard is
    decoration.
    """
    text = canonical_json(census)
    leaked = sorted(fact_id for fact_id in held_out if fact_id in text)
    if leaked:
        raise MobilityError(
            f"the census carries held-out fact id(s) {leaked}; refusing to write. A held-out id "
            f"in a published artifact spends its whole split key"
        )


def census_line(census: dict[str, Any]) -> str:
    totals = census["totals"]
    return (
        f"MOBILITY|open={totals['open_facts']}|evaluable={totals['evaluable']}"
        f"|unevaluable={totals['unevaluable']}|tactics={totals['tactics']}"
        f"|matched_pairs={totals['matched_pairs']}|zero_match_facts={totals['zero_match_facts']}"
        f"|clusters={totals['clusters']}|held_out_excluded={totals['held_out_excluded']}"
    )


# --------------------------------------------------------------------------
# The reach cross-check
# --------------------------------------------------------------------------


def fact_statement(root: Path, fact_id: str) -> str | None:
    """`formal.statement` for one fact, or `None` when the ledger has no such row."""
    path = root / "artifacts" / "facts" / (fact_id.replace("F:", "F-") + ".json")
    if not path.is_file():
        return None
    document = json.loads(path.read_text(encoding="utf-8"))
    statement = (document.get("formal") or {}).get("statement")
    return str(statement) if isinstance(statement, str) else None


def reach_scope(root: Path, fact_id: str, goal_text: str) -> str:
    """Whether a reach row cites the fact's WHOLE statement or a sub-goal of it.

    Decided by comparing the catalog's `goal` string to the ledger's
    `formal.statement`, not by pattern-matching prose. It matters because the
    census evaluates a precondition at the INITIAL goal, while a reach row may
    record that a tactic fired on the `succ` case reached after an induction --
    two different questions, and only the first kind of row is a claim this
    census can contradict.
    """
    statement = fact_statement(root, fact_id)
    if statement is None:
        return "unknown-statement"
    return "initial-goal" if statement == goal_text else "sub-goal"


def reach_cross_check(root: Path) -> list[dict[str, Any]]:
    """Every `reach.accepted_goals` row whose fact resolves to a frozen export.

    A row the evaluator calls `unmatched` is a disagreement: either the
    evaluator is wrong, or the catalog claims a reach it does not have. Neither
    is fixed here -- the catalog is another lane's file and an evaluator that
    edited its own oracle would be worthless.

    `agrees` is `None`, never `False`, when the tactic verdict is `unevaluable`:
    a precondition nobody could inspect is not a precondition that failed.
    """
    tactics, _ = load_catalog(root)
    cache: dict[str, GoalSource] = {}
    out: list[dict[str, Any]] = []
    for tactic in tactics:
        for accepted in tactic["reach"]["accepted_goals"]:
            fact_id = accepted.get("fact_id")
            if not fact_id:
                out.append(
                    {
                        "tactic_id": str(tactic["id"]),
                        "fact_id": None,
                        "goal": accepted["goal"],
                        "goal_scope": "no-fact-id",
                        "outcome": UNEVALUABLE,
                        "reason": "reach-row-cites-no-fact-id",
                        "agrees": None,
                    }
                )
                continue
            if fact_id not in cache:
                cache[fact_id] = load_goal(root, fact_id)
            source = cache[fact_id]
            scope = reach_scope(root, fact_id, str(accepted["goal"]))
            if not source.evaluable:
                out.append(
                    {
                        "tactic_id": str(tactic["id"]),
                        "fact_id": fact_id,
                        "goal": accepted["goal"],
                        "goal_scope": scope,
                        "outcome": UNEVALUABLE,
                        "reason": source.reason,
                        "agrees": None,
                    }
                )
                continue
            view = source.view
            assert view is not None
            outcome = evaluate_tactic(view, tactic)
            out.append(
                {
                    "tactic_id": str(tactic["id"]),
                    "fact_id": fact_id,
                    "goal": accepted["goal"],
                    "goal_scope": scope,
                    "outcome": outcome.verdict.outcome,
                    "reason": outcome.verdict.reason,
                    "agrees": None
                    if outcome.verdict.is_unevaluable
                    else outcome.verdict.is_matched,
                }
            )
    return out


# --------------------------------------------------------------------------
# Must-decline sampling
# --------------------------------------------------------------------------


def must_decline_ids(root: Path) -> list[str]:
    """The nine non-held-out `generated-mutation` rows, derived from the nursery.

    Derived, never copied: `scripts/check-autogenesis-must-decline-population.py`
    computes the same set the same way, and a hand-copied list would be the
    second source of truth this repository keeps getting bitten by.
    """
    document = read_json(root / NURSERY_PATH)
    entries = document.get("entries")
    if not isinstance(entries, list):
        raise MobilityError(f"{NURSERY_PATH} has no entries")
    ids = sorted(
        entry["fact_id"]
        for entry in entries
        if isinstance(entry, dict)
        and entry.get("provenance_class") == "generated-mutation"
        and entry.get("partition") != "held-out"
        and isinstance(entry.get("fact_id"), str)
    )
    if not ids:
        raise MobilityError(
            "the must-decline population is empty; sampling from it would pass vacuously"
        )
    return ids


def must_decline_table(root: Path) -> list[dict[str, Any]]:
    """Every tactic against every must-decline goal.

    A `matched` here is flagged `SUSPECT`: the statement is FALSE by a recorded,
    recomputed counterexample, so a precondition that admits it is either too
    loose or is matching something other than what it claims to. The census
    cannot prove a producer would admit it -- only that nothing structural
    stopped it from trying.
    """
    tactics, _ = load_catalog(root)
    out: list[dict[str, Any]] = []
    for fact_id in must_decline_ids(root):
        source = load_goal(root, fact_id)
        if not source.evaluable:
            out.append(
                {
                    "fact_id": fact_id,
                    "evaluable": False,
                    "reason": source.reason,
                    "suspect": [],
                    "matched": [],
                }
            )
            continue
        view = source.view
        assert view is not None
        matched_ids = [
            str(tactic["id"])
            for tactic in tactics
            if evaluate_tactic(view, tactic).verdict.is_matched
        ]
        out.append(
            {
                "fact_id": fact_id,
                "evaluable": True,
                "reason": "",
                "goal": view.kernel.render_lean(view.goal),
                "matched": matched_ids,
                "suspect": matched_ids,
            }
        )
    return out


# --------------------------------------------------------------------------
# The generated dashboard
# --------------------------------------------------------------------------


def must_decline_summary(root: Path) -> dict[str, Any]:
    """The nine must-decline rows, summarized for the committed census.

    A `suspect` is a tactic whose precondition is satisfied by a statement with a
    RECOMPUTED counterexample (`check-autogenesis-must-decline-population.py`).
    `evaluated` is reported beside it on purpose: `suspects == 0` over
    `evaluated == 0` is "not looked at", and a reader who saw only the zero
    would read it as a clean bill of health.
    """
    table = must_decline_table(root)
    evaluated = [row for row in table if row["evaluable"]]
    return {
        "rows": len(table),
        "evaluated": len(evaluated),
        "unevaluable": len(table) - len(evaluated),
        "suspects": sorted({tactic for row in table for tactic in row["suspect"]}),
        "suspect_facts": sorted(row["fact_id"] for row in table if row["suspect"]),
        "unevaluable_reasons": dict(
            sorted(
                {
                    row["reason"]: sum(1 for r in table if r["reason"] == row["reason"])
                    for row in table
                    if not row["evaluable"]
                }.items()
            )
        ),
    }


def render_dashboard(census: dict[str, Any], reach: list[dict[str, Any]]) -> str:
    totals = census["totals"]
    lines: list[str] = []
    lines.append("# Mobility census - the capability backlog")
    lines.append("")
    lines.append(
        "Generated by `python -m axeyum.agent mobility`. Do not edit. Validated by "
        "`scripts/check-mobility-census.py`; the census itself is "
        f"[`{CENSUS_PATH.as_posix()}`](../../../{CENSUS_PATH.as_posix()})."
    )
    lines.append("")
    lines.append("```")
    lines.append(census_line(census))
    lines.append("```")
    lines.append("")
    lines.append("## What was evaluated, and what was not")
    lines.append("")
    lines.append(
        f"**{totals['evaluable']} of {totals['open_facts']} open facts were evaluated at all.** "
        f"The other {totals['unevaluable']} have no frozen, digest-pinned statement export on "
        "this host, so there is no kernel goal to run a precondition against. Those facts are "
        "`unevaluable`, **not** zero-match: nothing looked at them, and a capability that "
        "removed every structural obstruction would not move one of them."
    )
    lines.append("")
    lines.append("| bucket | facts |")
    lines.append("|---|---|")
    lines.append(f"| open | {totals['open_facts']} |")
    lines.append(f"| evaluable (frozen export imported) | {totals['evaluable']} |")
    lines.append(f"| unevaluable (never looked at) | {totals['unevaluable']} |")
    lines.append(f"| zero-match among evaluable | {totals['zero_match_facts']} |")
    lines.append(f"| held-out, counted and never named | {totals['held_out_excluded']} |")
    lines.append("")
    lines.append("Why a fact was never looked at:")
    lines.append("")
    lines.append("| reason | facts |")
    lines.append("|---|---|")
    for reason, count in sorted(
        census["unevaluable_reasons"].items(), key=lambda kv: (-kv[1], kv[0])
    ):
        lines.append(f"| `{reason}` | {count} |")
    lines.append("")
    lines.append("| partition | open | evaluable | unevaluable | zero-match |")
    lines.append("|---|---|---|---|---|")
    for name, counts in census["partitions"].items():
        lines.append(
            f"| {name} | {counts['open']} | {counts['evaluable']} | "
            f"{counts['unevaluable']} | {counts['zero_match']} |"
        )
    lines.append("")
    lines.append("## Capability backlog: zero-match clusters, ranked")
    lines.append("")
    if not census["zero_match_clusters"]:
        lines.append(
            "No evaluable open fact matched zero tactics. That is a statement about the "
            f"{totals['evaluable']} facts a goal could be built for, and about nothing else."
        )
    else:
        lines.append("| rank | size | the reasons every tactic gave | facts |")
        lines.append("|---|---|---|---|")
        for rank, cluster in enumerate(census["zero_match_clusters"], start=1):
            reasons = "<br>".join(f"`{reason}`" for reason in cluster["reasons"])
            facts = "<br>".join(f"`{fid}`" for fid in cluster["fact_ids"][:8])
            if len(cluster["fact_ids"]) > 8:
                facts += f"<br>... and {len(cluster['fact_ids']) - 8} more"
            lines.append(f"| {rank} | {cluster['size']} | {reasons} | {facts} |")
    lines.append("")
    lines.append("## Per-tactic reach: measured here vs claimed in the catalog")
    lines.append("")
    lines.append(
        "`matched (open)` counts open facts whose initial goal satisfies the precondition. "
        "`shapes` is `distinct_goal_shapes_matched` -- distinct goals, never targets, which is "
        "the counting rule A3 fixed. `catalog accepted` is what "
        f"[`{CATALOG_PATH.as_posix()}`](../../../{CATALOG_PATH.as_posix()}) records as MEASURED "
        "reach, over a different population (mostly already-proved facts), so the two columns "
        "are not expected to agree; the cross-check below is what compares them properly."
    )
    lines.append("")
    lines.append(
        "| tactic | kind | matched (open) | shapes | catalog accepted | catalog declined |"
    )
    lines.append("|---|---|---|---|---|---|")
    for row in census["tactics"]:
        lines.append(
            f"| `{row['id']}` | {row['kind']} | {row['matched_facts']} | "
            f"{row['distinct_goal_shapes_matched']} | {row['catalog_reach_accepted']} | "
            f"{row['catalog_reach_declined']} |"
        )
    lines.append("")
    lines.append("## Reach cross-check")
    lines.append("")
    lines.append(
        "Every `reach.accepted_goals` row the catalog cites by fact id, re-evaluated. A row the "
        "evaluator calls `unmatched` is a disagreement and is listed here rather than repaired: "
        "either this evaluator is wrong or the catalog claims a reach it does not have, and both "
        "are findings for a human."
    )
    lines.append("")
    evaluated = [row for row in reach if row["agrees"] is not None]
    disagreements = [row for row in evaluated if not row["agrees"]]
    initial = [row for row in disagreements if row["goal_scope"] == "initial-goal"]
    sub_goal = [row for row in disagreements if row["goal_scope"] == "sub-goal"]
    lines.append(
        f"{len(evaluated)} of {len(reach)} accepted-goal rows were evaluable; "
        f"**{len(disagreements)} disagree** -- {len(initial)} on a row citing the fact's whole "
        f"statement, {len(sub_goal)} on a row citing a sub-goal reached after a move this census "
        "does not perform. `goal_scope` is decided by comparing the catalog's own `goal` text to "
        "the ledger's `formal.statement`, not by reading the prose."
    )
    lines.append("")
    if disagreements:
        lines.append("| scope | tactic | fact | catalog goal | evaluator said |")
        lines.append("|---|---|---|---|---|")
        for row in initial + sub_goal:
            goal = str(row["goal"]).replace("|", "\\|")
            lines.append(
                f"| {row['goal_scope']} | `{row['tactic_id']}` | `{row['fact_id']}` | {goal} | "
                f"`{row['outcome']}` / `{row['reason']}` |"
            )
        lines.append("")
    lines.append("## Must-decline sampling")
    lines.append("")
    sampling = census["must_decline_sampling"]
    lines.append(
        "The nine non-held-out `generated-mutation` rows are FALSE by a recomputed "
        "counterexample (`scripts/check-autogenesis-must-decline-population.py`). A tactic whose "
        "precondition is satisfied by one of them is flagged `SUSPECT`."
    )
    lines.append("")
    lines.append("| rows | evaluated | unevaluable | suspects |")
    lines.append("|---|---|---|---|")
    lines.append(
        f"| {sampling['rows']} | {sampling['evaluated']} | {sampling['unevaluable']} | "
        f"{len(sampling['suspects'])} |"
    )
    lines.append("")
    if sampling["evaluated"] == 0:
        lines.append(
            "**`suspects = 0` here means nothing was looked at, not that nothing was found.** No "
            "must-decline row has a frozen statement export, so the sampling rule has no subject "
            "on this host and `python -m axeyum.agent mobility --must-decline` exits **2** rather "
            "than 0. Producing exports for these nine is the cheapest way to make the negative "
            "control real."
        )
        lines.append("")
    elif sampling["suspects"]:
        lines.append("| suspect tactic |")
        lines.append("|---|")
        for tactic_id in sampling["suspects"]:
            lines.append(f"| `{tactic_id}` |")
        lines.append("")
    lines.append("## Pins")
    lines.append("")
    lines.append("| input | sha256 |")
    lines.append("|---|---|")
    lines.append(f"| `{CATALOG_PATH.as_posix()}` | `{census['catalog_sha256']}` |")
    lines.append(f"| `artifacts/facts/` (ledger digest) | `{census['ledger_sha256']}` |")
    lines.append(f"| `{EXPORT_INDEX_PATH.as_posix()}` | `{census['export_index_sha256']}` |")
    lines.append(f"| `{NURSERY_PATH.as_posix()}` | `{census['nursery_sha256']}` |")
    lines.append(f"| git commit | `{census['git_commit']}` |")
    lines.append("")
    return "\n".join(lines) + "\n"


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------


def write_json(path: Path, document: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def mobility_command(args: argparse.Namespace) -> int:
    root = resolve_root(args.root)
    if args.must_decline:
        table = must_decline_table(root)
        suspects = 0
        print("MUST-DECLINE SAMPLING")
        print(f"{'fact_id':<44} {'evaluable':<10} {'matched tactics / reason'}")
        for row in table:
            if row["evaluable"]:
                flag = "SUSPECT " + ",".join(row["suspect"]) if row["suspect"] else "clean"
                suspects += 1 if row["suspect"] else 0
                print(f"{row['fact_id']:<44} {'yes':<10} {flag}")
            else:
                print(f"{row['fact_id']:<44} {'no':<10} unevaluable: {row['reason']}")
        evaluable = sum(1 for row in table if row["evaluable"])
        print(
            f"MUST_DECLINE|rows={len(table)}|evaluable={evaluable}"
            f"|unevaluable={len(table) - evaluable}|suspect={suspects}"
        )
        if suspects:
            print(
                "MUST_DECLINE_ERROR|a tactic precondition admits a statement with a recomputed "
                "counterexample",
                file=sys.stderr,
            )
            return 1
        if evaluable == 0:
            # `suspect=0` over zero evaluated rows is the checker-that-cannot-fail
            # shape this repository refuses: nothing was looked at, so nothing
            # could have been found. A distinct status says so.
            print(
                "MUST_DECLINE_NOT_EXERCISED|no must-decline row has a frozen statement export on "
                "this host, so the sampling rule evaluated nothing; suspect=0 is 'not looked at', "
                "not 'clean'",
                file=sys.stderr,
            )
            return 2
        return 0

    if args.reach_check:
        rows = reach_cross_check(root)
        evaluated = [row for row in rows if row["agrees"] is not None]
        disagreements = [row for row in evaluated if not row["agrees"]]
        for row in rows:
            state = (
                "AGREES" if row["agrees"] else ("DISAGREES" if row["agrees"] is False else "n/a")
            )
            print(
                f"{state:<10} {row['goal_scope']:<18} {row['tactic_id']:<38} "
                f"{row['fact_id']} {row['reason']}"
            )
        initial = [r for r in disagreements if r["goal_scope"] == "initial-goal"]
        print(
            f"REACH|rows={len(rows)}|evaluable={len(evaluated)}"
            f"|disagreements={len(disagreements)}|initial_goal_disagreements={len(initial)}"
        )
        return 0

    census = build_census(root, commit=args.git_commit, fact_ids=args.fact or None)
    reach = reach_cross_check(root) if not args.skip_reach else []
    line = census_line(census)
    if args.write:
        write_json(root / CENSUS_PATH, census)
        (root / DASHBOARD_PATH).parent.mkdir(parents=True, exist_ok=True)
        (root / DASHBOARD_PATH).write_text(render_dashboard(census, reach), encoding="utf-8")
        print(f"wrote {CENSUS_PATH.as_posix()} and {DASHBOARD_PATH.as_posix()}")
    else:
        print(json.dumps(census["totals"], indent=2, sort_keys=True))
    print(line)
    if census["totals"]["evaluable"] == 0:
        print(
            "MOBILITY_ERROR|a census that evaluated nothing is not a census: no open fact "
            "resolved to a frozen statement export on this host",
            file=sys.stderr,
        )
        return 1
    return 0


def add_parser(sub: Any) -> Any:
    parser = sub.add_parser(
        "mobility",
        help="run every tactic precondition against every open fact (no producer runs)",
    )
    parser.add_argument("--write", action="store_true", help="write the census and the dashboard")
    parser.add_argument(
        "--fact", action="append", default=[], help="restrict to a fact (repeatable)"
    )
    parser.add_argument("--git-commit", default=None, help="40-hex commit for a non-git snapshot")
    parser.add_argument(
        "--must-decline",
        action="store_true",
        help="evaluate the nine must-decline rows; exits 1 when any tactic matches one",
    )
    parser.add_argument(
        "--reach-check",
        action="store_true",
        help="re-evaluate the catalog's accepted_goals rows and report disagreements",
    )
    parser.add_argument("--skip-reach", action="store_true", help="omit the cross-check section")
    parser.set_defaults(handler=mobility_command)
    return parser


__all__ = [
    "CATALOG_PATH",
    "CENSUS_PATH",
    "DASHBOARD_PATH",
    "EXPORT_INDEX_PATH",
    "MATCHED",
    "MID_DERIVATION",
    "PREDICATES",
    "UNEVALUABLE",
    "UNMATCHED",
    "Environment",
    "GoalSource",
    "GoalView",
    "MobilityError",
    "TacticVerdict",
    "Verdict",
    "add_parser",
    "assert_no_held_out",
    "build_census",
    "build_clusters",
    "canonical_shape",
    "census_line",
    "evaluate_predicate",
    "evaluate_tactic",
    "fact_statement",
    "ledger_sha256",
    "load_catalog",
    "load_goal",
    "matched",
    "mobility_command",
    "must_decline_ids",
    "must_decline_summary",
    "must_decline_table",
    "open_facts",
    "reach_cross_check",
    "reach_scope",
    "render_dashboard",
    "shape_sha256",
    "subterms",
    "unevaluable",
    "unmatched",
]
