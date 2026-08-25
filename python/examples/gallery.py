"""A gallery of the Axeyum Python layer -- one short demo per submodule, run with real output.

    uv run python python/examples/gallery.py

Every block prints what it computes; nothing is mocked. Where a result is a
certificate, the demo shows the CHECK, not just the answer -- that is the
project's identity (untrusted fast search, trusted small checking) carried
across the language boundary.
"""

from __future__ import annotations

from fractions import Fraction

import axeyum
from axeyum import cas, ir, kernel, knowledge, m, smt, solver


def section(title: str) -> None:
    print(f"\n== {title}")


section("smt -- the SMT-LIB front door; unknown is a value; every sat replays")
o = smt.solve(
    "(set-logic QF_BV)(declare-fun x () (_ BitVec 8))(declare-fun y () (_ BitVec 8))"
    "(assert (= (bvmul x y) (_ bv143 8)))(assert (bvugt x (_ bv1 8)))(assert (bvugt y (_ bv1 8)))(check-sat)",
    timeout_ms=5000,
)
print(f"status={o.status} model={o.model} replay={o.replay()}")
u = smt.solve(
    "(set-logic QF_BV)(declare-fun x () (_ BitVec 8))(assert (bvult x (_ bv1 8)))(assert (bvugt x (_ bv0 8)))(check-sat)"
)
print(
    f"status={u.status} replay_available={u.replay_available} reason={u.replay_unavailable_reason!r}"
)
hard = "(set-logic QF_BV)(declare-fun a () (_ BitVec 64))(declare-fun b () (_ BitVec 64))(assert (= (bvmul a b) (_ bv3369738766071892021 64)))(assert (bvugt a (_ bv1 64)))(assert (bvugt b (_ bv1 64)))(check-sat)"
k = smt.solve(hard, timeout_ms=1)
print(f"1 ms budget on a factoring instance: status={k.status}  (a value, not an exception)")

section("ir + solver -- build terms without SMT-LIB text; SMT-LIB totality is kept")
a = ir.Arena()
x = a.bv_var("x", 8)
zero = a.bv_const(8, 0)
all_ones = a.bv_const(8, 255)
t = a.eq(a.bvudiv(x, zero), all_ones)  # bvudiv by zero is all-ones, per SMT-LIB
r = solver.solve(a, [t], solver.Config(timeout_ms=5000))
print(f"bvudiv(x, 0) == 0xff is {r.status}  (total operator, no ZeroDivisionError)")
ev = solver.produce_evidence(a, [t], solver.Config(timeout_ms=5000))
print(
    f"evidence verdict={ev.verdict} kind={ev.evidence_kind} check_outcome={ev.check_outcome(a, [t])}"
)

section("cas -- exact algebra with certificates")
X = cas.Expr.var("x")
p = X * X + cas.Expr.int(5) * X + cas.Expr.int(6)
print("factor  :", m.show(cas.factor(p, "x")))
integ = cas.integrate(p, "x")
print("integral:", m.show(integ.antiderivative), "| certificate:", integ.certificate.certainty())
print("equal   :", cas.equal((X + 2) * (X + 3), p))
print("mixed   :", m.show(X + 1), "|", m.show(Fraction(1, 2) * X))

section("m -- Mathematica-shaped verbs from strings")
print("Solve   :", m.show(m.Solve("2x + 3 = 7")), m.show(m.Solve("x^2 - 2")))
print("System  :", m.Solve(["x + y = 3", "x - y = 1"], ["x", "y"]))
print("Sum     :", m.show(m.Sum("k^2", ("k", 1, "n"))))
print("Reduce  :", [m.interval(i) for i in m.Reduce("x^2 >= 4")])
print("Limit   :", m.Limit("sin(x)/x", 0), "| Series:", m.show(m.Series("exp(x)", order=3)))
print(
    "Equal   :",
    m.Equal("(x+2)(x+3)", "x^2 + 5x + 6"),
    "| NRoots(x^2-2):",
    [float(r) for r in m.NRoots("x^2 - 2")],
)

section("cas.certify -- untrusted producer, trusted checker, tamper rejected")
from axeyum.cas.certify import geometry

problem = geometry.corpus()[0]
outcome = geometry.certify_any_route(problem, geometry.geometry_limits())
print(f"{problem.id}: {type(outcome).__name__}")
if hasattr(outcome, "certificate"):
    verdict = outcome.certificate.check(geometry.CheckOptions())
    print("check   :", type(verdict).__name__, getattr(verdict, "report", ""))

section("kernel -- preludes, footprints, admission")
K = kernel.Kernel()
K.build_nat_prelude()
names = K.declaration_names()
print(
    f"nat prelude: {len(names)} declarations | Nat.add_comm axiom-free: {K.is_axiom_free('Nat.add_comm')}"
)
print("footprint of Nat.add_comm:", K.axiom_footprint("Nat.add_comm"))
try:
    K.axiom_footprint("Nat.does_not_exist")
except KeyError as e:
    print("absent name is KeyError, never an empty (axiom-free-looking) list:", e)

section("knowledge -- the artifacts, read-only, partition-safe")
facts = knowledge.facts.load()
fr = knowledge.frontier.load()
nur = knowledge.nursery.load()
print(
    f"facts={len(facts)} frontier_entries={len(fr.entries)} selection={fr.selection.outcome} held_out={len(nur.held_out_ids())}"
)
print(
    "safe to reference F:ml430-nat-modeq-refl-d870c8f5:",
    nur.is_safe_to_reference("F:ml430-nat-modeq-refl-d870c8f5"),
)

section("version")
print("axeyum", axeyum.__version__)
