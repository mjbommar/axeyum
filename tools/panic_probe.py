"""Measure the panic surface of `axeyum._native` that a Python caller can reach.

A Rust `panic!` inside a `#[pyfunction]` does not become a Python exception: PyO3
turns it into `pyo3_runtime.PanicException`, which derives from `BaseException`.
It therefore escapes `except Exception`, and its message is a Rust internal
("builder guaranteed BitVec operand"). That is neither typed nor safe, so the
first thing to know is *how many* such calls exist -- measured, not asserted.

# What this does

1. Walks every submodule of `axeyum._native` and enumerates the public callable
   surface: module-level functions, classes (as constructors), bound methods,
   and property getters.
2. For each callable, builds a deterministic battery of argument vectors from an
   adversarial pool -- wrong sorts, cross-arena handles, empty lists, zero and
   over-wide bit-vector widths, division by zero, out-of-range extracts,
   negative ints where a `u32` is expected, huge ints, non-polynomial input to
   polynomial-only functions, foreign `TermId`s, degenerate arrays.
3. Runs them in a **subprocess**, so an abort or a segfault is observed rather
   than ending the measurement. The worker writes one JSONL record before each
   call and one after; if it dies, the parent attributes the crash to the case
   that had started and no record closed, then resumes at the next case.
4. Classifies every outcome: `ok`, `exception` (a normal typed `Exception`),
   `panic` (`pyo3_runtime.PanicException`), `base` (any other `BaseException`),
   or `crash` (the worker died -- segfault, abort, or the case timed out).

# Why the count is the deliverable

`panics == 0` is a property a test can assert and a regression can break. A
count printed by a tool that was never pointed at the subject is worth nothing,
so the summary line carries `callables` and `probed` beside it: a probe that
found no panics because it made no calls is visibly different from one that made
fifteen thousand.

# The failure this probe cannot see

It only reaches what its argument pool can construct. A callable whose receiver
could not be built is counted in `callables` and reported as `unreachable` in the
table -- never silently dropped, because an unprobed callable and a clean one
would otherwise be the same number.

Usage:
    python3 tools/panic_probe.py                 # measure and print
    python3 tools/panic_probe.py --write         # regenerate the report
    python3 tools/panic_probe.py --check         # fail if the report is stale
"""

from __future__ import annotations

import argparse
import inspect
import json
import os
import pathlib
import re
import subprocess
import sys
import time
import types

REPORT = pathlib.Path("docs/plan/generated/panic-probe.md")

# A worker gets this long before the parent calls it hung and resumes past the
# case in flight. Generous: a solver call under a cold cache is seconds, and a
# false "crash" would be a fabricated finding in the direction that looks worse.
WORKER_TIMEOUT_S = 240.0
# Address-space ceiling for a worker. A probe that asks for a 2**70-bit vector
# must fail as a MemoryError inside its own process, never by inviting the
# host OOM killer to pick a victim (CLAUDE.md: a kernel OOM has killed a live
# agent session on this fleet).
WORKER_ADDRESS_SPACE_BYTES = 4 * 1024**3
# Per-callable cap, so one function with nine parameters cannot dominate the run.
MAX_VECTORS_PER_CALLABLE = 24

# Callables that must NOT run while the case plan is being built.
#
# Receiver discovery calls methods to find out what they return. That happens in
# the parent AND in every worker, before any case runs, so a call that kills the
# process there costs the entire measurement rather than producing one row.
# `build_cpoint_prelude` overflows the 8 MB main-thread stack and takes CPython
# down with SIGSEGV -- measured 2026-08-25, and it is one of the findings, so it
# is probed as an ordinary case below instead of being discovered here.
PLAN_TIME_EXCLUDED = frozenset({"build_cpoint_prelude"})

# --------------------------------------------------------------- the arg pool

# Values that are wrong for almost every parameter. Used to fill uniform vectors
# and as the fallback candidates for a parameter whose name says nothing.
GENERIC = [
    ("none", lambda s: None),
    ("zero", lambda s: 0),
    ("negative", lambda s: -1),
    ("huge", lambda s: 1 << 70),
    ("neg-huge", lambda s: -(1 << 70)),
    ("empty-str", lambda s: ""),
    ("text", lambda s: "ÿ(not a term"),
    ("empty-list", lambda s: []),
    ("list-of-none", lambda s: [None]),
    ("true", lambda s: True),
    ("float", lambda s: 0.5),
    ("object", lambda s: object()),
]


# Parameter-name keyed candidates. The key is matched against the parameter name
# by exact hit first, then by substring, so `hi`/`lo`/`index` and `assertions`/
# `roots`/`terms` each get the arguments that actually reach the Rust path.
def keyed_candidates(name: str, s: dict) -> list:
    """Adversarial candidates for a parameter called `name`, most specific first."""
    n = name.lower()
    out: list = []

    def add(label, value):
        out.append((label, value))

    if n in {"arena"}:
        add("foreign-arena", s.get("arena2"))
        add("not-an-arena", 0)
    if n in {"width", "bits", "exp", "sig", "size", "n", "degree", "exponent"}:
        for w in (0, 1, 65, 129, 70000, -1, 1 << 70):
            add(f"width={w}", w)
    if n in {"hi", "lo", "index", "position", "start", "end", "offset", "row", "col"}:
        for i in (-1, 0, 1 << 31, 1 << 70):
            add(f"idx={i}", i)
    if n in {"den", "denominator", "divisor", "modulus"}:
        for d in (0, -1, 1 << 70):
            add(f"den={d}", d)
    if n in {"num", "numerator", "value", "constant"}:
        for v in (0, -1, 1 << 70, -(1 << 70)):
            add(f"num={v}", v)
    if n in {"name", "symbol_name", "logic", "text", "script", "source"}:
        for label, v in (
            ("empty", ""),
            ("nul", "\x00"),
            ("astral", "\U0001f600"),
            ("bad-smtlib", "(assert (bvadd"),
            ("unknown-logic", "(set-logic NOPE)(check-sat)"),
            ("string-escape", '(set-logic QF_S)(assert (= "\\u{110000}" ""))(check-sat)'),
        ):
            add(f"str:{label}", v)
    if n in {"term", "root", "goal", "a", "b", "c", "x", "y", "subject"}:
        for label in ("term_foreign", "term_int", "term_real", "term_array", "term_bool"):
            if s.get(label) is not None:
                add(label, s[label])
    if n in {"roots", "assertions", "terms", "assumptions", "hypotheses", "targets", "generators"}:
        for label in (
            "terms_empty",
            "terms_foreign",
            "terms_int",
            "terms_real",
            "terms_array",
            "terms_mixed",
        ):
            if s.get(label) is not None:
                add(label, s[label])
    if n in {"assignment"}:
        add("foreign-assignment", s.get("assignment_foreign"))
    if n in {"sort", "index_sort", "element_sort", "result_sort"}:
        for label in ("sort_int", "sort_real", "sort_array", "sort_string", "sort_uninterpreted"):
            if s.get(label) is not None:
                add(label, s[label])
    if n in {"expr", "polynomial", "poly", "p", "q", "lhs", "rhs"}:
        for label in ("expr_nonpoly", "expr_div_zero", "expr_deep", "mvpoly_zero"):
            if s.get(label) is not None:
                add(label, s[label])
    if n in {"values", "candidates", "patterns", "entries", "pairs", "rows", "columns"}:
        add("empty", [])
        add("mismatched", [True])
        add("mismatched-2", [[], [], []])
    return out


def best_guess(name: str, param, s: dict):
    """A plausibly VALID value for `name`, so one-at-a-time mutation starts from
    something that reaches the Rust path rather than bouncing off `TypeError`."""
    n = name.lower()
    table = {
        "arena": "arena",
        "assignment": "assignment",
        "config": "config",
        "sort": "sort_bv8",
        "index_sort": "sort_bv8",
        "element_sort": "sort_bv8",
        "term": "term_bv",
        "root": "term_bv",
        "goal": "term_bool",
        "subject": "term_bool",
        "a": "term_bv",
        "b": "term_bv",
        "x": "term_bv",
        "y": "term_bv",
        "assertions": "terms_bool",
        "roots": "terms_bv",
        "terms": "terms_bv",
        "assumptions": "terms_bool",
        "hypotheses": "terms_bool",
        "symbol": "symbol_bv",
        "expr": "expr_ok",
        "poly": "mvpoly_ok",
        "polynomial": "mvpoly_ok",
        "p": "mvpoly_ok",
        "q": "mvpoly_ok",
        "script": "script_text",
        "name": "name_text",
        "width": "eight",
        "hi": "seven",
        "lo": "zero",
        "index": "zero",
        "num": "one",
        "den": "one",
        "n": "one",
    }
    key = table.get(n)
    if key is not None and s.get(key) is not None:
        return s[key]
    if param.default is not inspect.Parameter.empty:
        return param.default
    return None


# ------------------------------------------------------------- the specimens


def build_specimens(native) -> dict:
    """Live objects the argument pool draws on. Every entry is best-effort: a
    specimen that cannot be built is `None` and its candidates are skipped, so a
    binding change cannot make this file fail to import."""
    s: dict = {}

    def attempt(key, thunk):
        try:
            s[key] = thunk()
        except BaseException:  # noqa: BLE001 - a broken specimen must not stop the probe
            s[key] = None

    ir = native.ir
    s["zero"], s["one"], s["seven"], s["eight"] = 0, 1, 7, 8
    s["name_text"] = "p"
    s["script_text"] = "(set-logic QF_BV)(declare-const x (_ BitVec 8))(assert (= x x))(check-sat)"

    attempt("arena", ir.Arena)
    attempt("arena2", ir.Arena)
    attempt("sort_bool", ir.Sort.bool)
    attempt("sort_bv8", lambda: ir.Sort.bv(8))
    attempt("sort_bv1", lambda: ir.Sort.bv(1))
    attempt("sort_int", ir.Sort.int)
    attempt("sort_real", ir.Sort.real)
    attempt("sort_string", ir.Sort.string)
    attempt("sort_array", lambda: ir.Sort.array(ir.Sort.bv(8), ir.Sort.bv(8)))

    a = s.get("arena")
    if a is not None:
        attempt("term_bv", lambda: a.bv_var("bv", 8))
        attempt("term_bv1", lambda: a.bv_var("bv1", 1))
        attempt("term_bool", lambda: a.bool_var("p"))
        attempt("term_int", lambda: a.int_var("i"))
        attempt("term_real", lambda: a.real_var("r"))
        attempt("term_array", lambda: a.array_var("arr", ir.Sort.bv(8), ir.Sort.bv(8)))
        attempt("symbol_bv", lambda: a.declare("sym", ir.Sort.bv(8)))
        attempt("symbol_int", lambda: a.declare("symi", ir.Sort.int))
        attempt("assignment", a.assignment)
        attempt("sort_uninterpreted", lambda: a.declare_uninterpreted_sort("U"))
    b = s.get("arena2")
    if b is not None:
        attempt("term_foreign", lambda: b.bv_var("foreign", 8))
        attempt("assignment_foreign", b.assignment)

    for src, dst in (
        ("term_bv", "terms_bv"),
        ("term_bool", "terms_bool"),
        ("term_int", "terms_int"),
        ("term_real", "terms_real"),
        ("term_array", "terms_array"),
        ("term_foreign", "terms_foreign"),
    ):
        s[dst] = [s[src]] if s.get(src) is not None else None
    s["terms_empty"] = []
    s["terms_mixed"] = [t for t in (s.get("term_bool"), s.get("term_int")) if t is not None] or None

    attempt("config", native.solver.Config)

    cas = native.cas
    attempt("expr_ok", lambda: cas.Expr.var("x") + cas.Expr.int(1))
    attempt("expr_nonpoly", lambda: cas.Expr.var("x").sin())
    attempt("expr_div_zero", lambda: cas.Expr.var("x") / cas.Expr.zero())
    attempt("expr_deep", lambda: cas.Expr.var("x").pow(2).ln().exp())
    attempt("mvpoly_ok", lambda: cas.MvPoly.var("x"))
    attempt("mvpoly_zero", cas.MvPoly.zero)
    attempt("rational_ok", lambda: cas.Rational(1, 2))
    attempt("monomial_ok", cas.Monomial.one)

    kernel = native.kernel
    attempt("kernel", kernel.Kernel)
    attempt("kernel2", kernel.Kernel)
    if s.get("kernel") is not None:
        attempt("kernel_name", lambda: s["kernel"].lean_name(["Nat"]))
        attempt("kernel_expr", lambda: s["kernel"].const_(s["kernel"].lean_name(["Nat"]), []))
    if s.get("kernel2") is not None:
        attempt("kernel2_name", lambda: s["kernel2"].lean_name(["Nat"]))
        attempt("kernel2_expr", lambda: s["kernel2"].const_(s["kernel2"].lean_name(["Nat"]), []))

    attempt("script_parsed", lambda: native.smt.parse(s["script_text"]))
    attempt("outcome", lambda: native.smt.solve(s["script_text"]))
    if s.get("arena") is not None and s.get("terms_bv") is not None:
        attempt("lowering", lambda: ir.bv.lower_terms(s["arena"], s["terms_bv"]))
    return s


# Receivers for methods, by class name.
#
# Three sources, in order: the specimen bag, a harvest of what a curated list of
# producer calls RETURNS (this is what reaches `CheckResult`, `Declaration`,
# `TermNode`, `CofactorOutcome` and the other result types that have no `#[new]`),
# and finally a direct construction attempt for classes that do have one.
#
# A class with no receiver is not silently dropped -- its methods are reported as
# `unreachable`, because an unprobed callable and a clean one must not be the
# same number.
def build_receivers(native, s: dict) -> dict:
    """`class name -> a live instance`, best effort."""
    out: dict = {}

    def put(name, value):
        if value is not None and name not in out:
            out[name] = value

    # Match by CLASS NAME against the walked surface, not by `__module__`: a
    # `#[pyclass]` without an explicit `module = ...` reports `builtins`, and a
    # `__module__` test silently dropped `ExprNode`, `Declaration` and
    # `SolveStats` -- the result types with no constructor, which are exactly
    # the ones a harvest exists to reach.
    known = {obj.__name__ for _p, kind, obj, _o in walk_surface(native) if kind == "class"}

    def harvest(value, depth=0):
        """Register `value` and, up to `depth` 3, whatever it contains."""
        if value is None or depth > 3:
            return
        if type(value).__name__ in known:
            put(type(value).__name__, value)
        if isinstance(value, (list, tuple, set)):
            for item in list(value)[:6]:
                harvest(item, depth + 1)
        elif isinstance(value, dict):
            for item in list(value.values())[:6]:
                harvest(item, depth + 1)

    for key, name in (
        ("arena", "Arena"),
        ("assignment", "Assignment"),
        ("sort_bv8", "Sort"),
        ("term_bv", "Term"),
        ("symbol_bv", "Symbol"),
        ("config", "Config"),
        ("script_parsed", "Script"),
        ("outcome", "Outcome"),
        ("lowering", "BitLowering"),
        ("expr_ok", "Expr"),
        ("mvpoly_ok", "MvPoly"),
        ("rational_ok", "Rational"),
        ("monomial_ok", "Monomial"),
    ):
        put(name, s.get(key))

    for thunk in _producers(native, s):
        try:
            harvest(thunk())
        except BaseException:  # noqa: BLE001, S112 - a producer that declines is data, not a stop
            continue

    # Anything still missing that has a constructor: build it from the same
    # best-guess baseline the sweep uses.
    for path, kind, obj, _owner in walk_surface(native):
        if kind != "class" or obj.__name__ in out:
            continue
        sig = _signature(obj)
        if sig is None:
            continue
        args = [best_guess(param.name, param, s) for param in _positional(sig)]
        try:
            put(obj.__name__, obj(*args))
        except BaseException:  # noqa: BLE001, S112
            continue

    # Closure rounds. Most result types have no constructor and are reachable
    # only as the RETURN of a method on something already held -- `ExprNode`
    # from `Kernel.expr_node`, `SolveStats` from `CheckResult.stats`,
    # `QueryPlan` from `Query.plan`. Two rounds is enough to reach depth two and
    # keeps the plan build near a second.
    for _round in range(2):
        for receiver in list(out.values()):
            for member in sorted(dir(type(receiver))):
                if member.startswith("_") or member in PLAN_TIME_EXCLUDED:
                    continue
                try:
                    attribute = getattr(receiver, member)
                except BaseException:  # noqa: BLE001, S112
                    continue
                if not callable(attribute):
                    harvest(attribute)
                    continue
                sig = _signature(attribute)
                if sig is None:
                    continue
                params = _positional(sig)
                if len(params) > 3:
                    continue
                try:
                    harvest(attribute(*[best_guess(p.name, p, s) for p in params]))
                except BaseException:  # noqa: BLE001, S112
                    continue
    return out


def _producers(native, s: dict):
    """Calls whose RETURN VALUES are the receivers for the result types.

    Curated rather than exhaustive on purpose: this list runs while the case
    plan is being built, in both the parent and every worker, so a call here
    that crashed would take the whole measurement with it instead of being
    recorded as one bad case. Everything here is a route the committed test
    suite already exercises."""
    ir, smt, solver, cas, kernel = (
        native.ir,
        native.smt,
        native.solver,
        native.cas,
        native.kernel,
    )
    arena, terms_bool, terms_bv = s.get("arena"), s.get("terms_bool"), s.get("terms_bv")
    return [
        lambda: kernel.Kernel(),
        lambda: kernel.Kernel().build_nat_prelude(),
        lambda: _kernel_pieces(kernel),
        lambda: solver.solve(arena, terms_bool, solver.Config()),
        lambda: solver.check_auto_explained(arena, terms_bool, solver.Config()),
        lambda: solver.produce_evidence(arena, terms_bool, solver.Config()),
        lambda: solver.unsat_core(arena, terms_bool, solver.Config()),
        lambda: solver.capabilities(),
        lambda: solver.capability_rows(),
        lambda: solver.support_matrix_rows(),
        lambda: solver.trust_ledger_rows(),
        lambda: solver.recommended_portfolio(arena, terms_bool),
        lambda: solver.Incremental(arena),
        lambda: solver.SatBvBackend(),
        lambda: solver.SatBvBackend().capabilities(),
        lambda: ir.query.Query(arena, terms_bool),
        lambda: arena.term_stats(terms_bv),
        lambda: arena.node(s.get("term_bv")),
        lambda: arena.sort_of(s.get("term_bv")),
        lambda: ir.bv.lower_terms(arena, terms_bv),
        lambda: solver.cnf.tseitin_encode(s.get("lowering")),
        lambda: solver.cnf.parse_dimacs("p cnf 1 1\n1 0\n"),
        lambda: solver.proofs.export_qf_bv_unsat_proof(arena, terms_bool, solver.Config()),
        lambda: smt.solve(s.get("script_text")),
        lambda: smt.parse(s.get("script_text")),
        lambda: smt.session(s.get("script_text")),
        lambda: cas.equal(s.get("expr_ok"), s.get("expr_ok")),
        lambda: cas.normalize(s.get("expr_ok")),
        lambda: cas.Rational(1, 2),
        lambda: cas.Monomial.from_powers([("x", 2)]),
        lambda: cas.certify.groebner.Limits(),
        lambda: cas.certify.groebner.reduce_with_cofactors(
            [s.get("mvpoly_ok")], s.get("mvpoly_ok"), cas.certify.groebner.Limits()
        ),
        lambda: cas.certify.geometry.Pt("a"),
        lambda: cas.certify.gf2.Gf2Limits(),
        lambda: cas.certify.geometry.corpus(),
        lambda: cas.certify.geometry.centroid(
            cas.certify.geometry.Pt("a"), cas.certify.geometry.Pt("b")
        ),
        lambda: cas.certify.sturm.__dict__,
        lambda: cas.Matrix.identity(2),
        lambda: cas.Matrix.zero(2, 2),
        lambda: cas.RealInterval.point(s.get("rational_ok")),
        lambda: cas.Assumptions(),
        lambda: ir.query.Query(arena, terms_bool).plan(),
        lambda: ir.fp.F32,
        lambda: ir.fp.pack_params(arena, ir.fp.F32),
        lambda: smt.solve(s.get("script_text")).stats,
        lambda: solver.solve(arena, terms_bool, solver.Config()).stats,
        lambda: solver.proofs.export_qf_bv_unsat_proof(
            arena, [arena.bool_const(False)], solver.Config()
        ),
        lambda: _import_report(native),
        lambda: native.producers.__dict__,
    ]


def _import_report(native):
    """Whatever the `producers` module can build without touching the network."""
    out = []
    for name in sorted(dir(native.producers)):
        if name.startswith("_"):
            continue
        member = getattr(native.producers, name)
        if callable(member) and not isinstance(member, type):
            try:
                out.append(member())
            except BaseException:  # noqa: BLE001, S112
                continue
    return out


def _kernel_pieces(kernel_module):
    """Kernel-owned handles: expressions, names, levels, declarations.

    Each piece is attempted separately: one missing accessor must not cost the
    other seventy-odd `Kernel` methods their receiver."""
    k = kernel_module.Kernel()
    pieces = [k]
    for thunk in (
        lambda: k.build_nat_prelude(),
        lambda: k.build_logic_prelude(),
        lambda: k.declaration_names(),
        lambda: k.get_declaration(k.declaration_names()[0]),
        lambda: k.expr_node(k.const_(k.lean_name(["Nat"]), [])),
        lambda: k.lean_name(["Nat"]),
        lambda: k.const_(k.lean_name(["Nat"]), []),
        lambda: k.bvar(0),
        lambda: k.declarations(),
        lambda: k.axiom_footprint(k.declaration_names()[0]),
        lambda: k.fork(),
    ):
        try:
            pieces.append(thunk())
        except BaseException:  # noqa: BLE001, S112
            continue
    return pieces


# ------------------------------------------------------- the targeted battery


def targeted_cases(native, s: dict):
    """Hand-written adversarial scenarios the generic sweep cannot express.

    The generic sweep mutates one argument at a time from a name-guessed
    baseline; it cannot build a *second* arena's term, a datatype whose
    constructor index is out of range, or a scope-parent list of the wrong
    length. Every entry here names a specific Rust panic site the inventory
    (`docs/python-2026-08/inventories/smt-solver.md` section 15,
    `inventories/cas.md` section 0.6) says a Python caller can reach.

    Each entry is `(target, label, thunk)`. A thunk that cannot even build its
    inputs raises an ordinary exception and is recorded as such -- which is the
    honest outcome, not a skip.
    """
    ir, smt, solver, cas = native.ir, native.smt, native.solver, native.cas
    out = []

    def case(target, label):
        def wrap(fn):
            out.append((target, f"targeted:{label}", fn))
            return fn

        return wrap

    # --- the bv lowerer's `unreachable!()` on a sort it cannot represent -----
    for label, key in (
        ("int", "terms_int"),
        ("real", "terms_real"),
        ("array", "terms_array"),
    ):
        case("ir.bv.lower_terms", f"sort-{label}")(
            lambda k=key: ir.bv.lower_terms(s["arena"], s[k])
        )
        case("solver.solve", f"sort-{label}")(
            lambda k=key: solver.solve(s["arena"], s[k], solver.Config())
        )
        for mode in ("eager", "lazy", "hybrid"):
            case("solver.solve", f"sort-{label}-mode-{mode}")(
                lambda k=key, m=mode: solver.solve(
                    s["arena"], s[k], solver.Config(bit_lowering_mode=m)
                )
            )
        case("solver.Incremental.assert_", f"sort-{label}")(
            lambda k=key: _incremental_assert(solver, s["arena"], s[k])
        )
        case("solver.produce_evidence", f"sort-{label}")(
            lambda k=key: solver.produce_evidence(s["arena"], s[k], solver.Config())
        )
        case("solver.unsat_core", f"sort-{label}")(
            lambda k=key: solver.unsat_core(s["arena"], s[k], solver.Config())
        )
        case("ir.query.Query", f"sort-{label}")(lambda k=key: ir.query.Query(s["arena"], s[k]))

    def _uninterpreted_term():
        arena = ir.Arena()
        sort = arena.declare_uninterpreted_sort("U")
        symbol = arena.declare("u", sort)
        return arena, [arena.var(symbol)]

    case("ir.bv.lower_terms", "sort-uninterpreted")(
        lambda: ir.bv.lower_terms(*_uninterpreted_term())
    )
    case("solver.solve", "sort-uninterpreted")(
        lambda: solver.solve(*_uninterpreted_term(), solver.Config())
    )

    def _seq_term():
        arena = ir.Arena()
        symbol = arena.declare("s", ir.Sort.string())
        return arena, [arena.seq_len(arena.var(symbol))]

    case("ir.bv.lower_terms", "sort-seq")(lambda: ir.bv.lower_terms(*_seq_term()))

    # --- `write_script` on a foreign `TermId` -------------------------------
    case("smt.write_script", "foreign-term")(
        lambda: smt.write_script(s["arena"], s["terms_foreign"])
    )
    case("ir.Arena.write_script", "foreign-term")(
        lambda: s["arena"].write_script(s["terms_foreign"])
    )
    case("smt.write_script", "empty")(lambda: smt.write_script(s["arena"], []))

    # --- cross-arena handles everywhere they are accepted -------------------
    for target, thunk in (
        ("ir.eval", lambda: ir.eval(s["arena"], s["term_foreign"], s["assignment"])),
        ("ir.eval", lambda: ir.eval(s["arena"], s["term_bv"], s["assignment_foreign"])),
        ("ir.Arena.render", lambda: s["arena"].render(s["term_foreign"])),
        ("ir.Arena.sort_of", lambda: s["arena"].sort_of(s["term_foreign"])),
        ("ir.Arena.node", lambda: s["arena"].node(s["term_foreign"])),
        ("solver.solve", lambda: solver.solve(s["arena"], s["terms_foreign"], None)),
        ("ir.bv.lower_terms", lambda: ir.bv.lower_terms(s["arena"], s["terms_foreign"])),
    ):
        case(target, "cross-arena")(thunk)

    # --- degenerate widths, out-of-range extracts, u32 range guards ----------
    for width in (0, 1, 65, 129, 70000, 1 << 40):
        case("ir.Arena.bv_var", f"width={width}")(lambda w=width: ir.Arena().bv_var("x", w))
        case("ir.Sort.bv", f"width={width}")(lambda w=width: ir.Sort.bv(w))
        case("ir.Arena.bv_const", f"width={width}")(
            lambda w=width: ir.Arena().bv_const(w, (1 << 200) - 1)
        )
    for hi, lo in ((0, 1), (8, 0), (7, 8), (1 << 40, 0), (0, 1 << 40)):
        case("ir.Arena.extract", f"hi={hi},lo={lo}")(
            lambda h=hi, l=lo: s["arena"].extract(h, l, s["term_bv"])
        )
    for count in (0, 1 << 31, 1 << 40):
        case("ir.Arena.repeat", f"count={count}")(
            lambda c=count: s["arena"].repeat(c, s["term_bv"])
        )
        case("ir.Arena.zero_extend", f"count={count}")(
            lambda c=count: s["arena"].zero_extend(c, s["term_bv"])
        )
        case("ir.Arena.rotate_left", f"count={count}")(
            lambda c=count: s["arena"].rotate_left(c, s["term_bv"])
        )

    # --- partial / underspecified operators, then the trusted evaluator -----
    def _div_by_zero(builder, zero_builder):
        arena = ir.Arena()
        term = getattr(arena, builder)(*zero_builder(arena))
        return ir.eval(arena, term, arena.assignment())

    case("ir.eval", "bvudiv-by-zero")(
        lambda: _div_by_zero("bvudiv", lambda a: (a.bv_const(8, 1), a.bv_const(8, 0)))
    )
    case("ir.eval", "bvurem-by-zero")(
        lambda: _div_by_zero("bvurem", lambda a: (a.bv_const(8, 1), a.bv_const(8, 0)))
    )
    case("ir.eval", "bvsdiv-by-zero")(
        lambda: _div_by_zero("bvsdiv", lambda a: (a.bv_const(8, 1), a.bv_const(8, 0)))
    )
    case("ir.eval", "bvsmod-by-zero")(
        lambda: _div_by_zero("bvsmod", lambda a: (a.bv_const(8, 1), a.bv_const(8, 0)))
    )
    case("ir.eval", "int-div-by-zero")(
        lambda: _div_by_zero("int_div", lambda a: (a.int_const(1), a.int_const(0)))
    )
    case("ir.eval", "int-mod-by-zero")(
        lambda: _div_by_zero("int_mod", lambda a: (a.int_const(1), a.int_const(0)))
    )
    case("ir.eval", "real-div-by-zero")(
        lambda: _div_by_zero("real_div", lambda a: (a.real_const(1), a.real_const(0)))
    )
    case("ir.eval", "int-overflow")(
        lambda: _div_by_zero(
            "int_mul", lambda a: (a.int_const((1 << 126) - 1), a.int_const((1 << 126) - 1))
        )
    )

    # --- an assignment whose value has the wrong shape for the sort ---------
    def _mislift(sort_maker, value):
        arena = ir.Arena()
        symbol = arena.declare("v", sort_maker())
        assignment = arena.assignment()
        assignment.set(arena, symbol, value)
        return ir.eval(arena, arena.var(symbol), assignment)

    for label, sort_maker, value in (
        ("bool<-int", ir.Sort.bool, 3),
        ("int<-bool", ir.Sort.int, True),
        ("bv8<-str", lambda: ir.Sort.bv(8), "x"),
        ("bv8<-negative", lambda: ir.Sort.bv(8), -1),
        ("bv8<-overwide", lambda: ir.Sort.bv(8), 1 << 200),
        ("real<-str", ir.Sort.real, "1/2"),
        ("string<-int", ir.Sort.string, 5),
        ("array<-int", lambda: ir.Sort.array(ir.Sort.bv(8), ir.Sort.bv(8)), 0),
    ):
        case("ir.Assignment.set", f"mislift-{label}")(lambda m=sort_maker, v=value: _mislift(m, v))

    # --- quantifier patterns: the e-graph length assert ---------------------
    def _patterns(groups):
        arena = ir.Arena()
        symbol = arena.declare("q", ir.Sort.int())
        body = arena.int_ge(arena.var(symbol), arena.int_const(0))
        quantifier = arena.forall([symbol], body)
        arena.set_quantifier_patterns(quantifier, groups)
        return arena.quantifier_patterns(quantifier)

    for label, groups in (
        ("empty", []),
        ("empty-group", [[]]),
        ("nested-empty", [[], []]),
        ("foreign-term", None),
    ):
        if label == "foreign-term":
            case("ir.Arena.set_quantifier_patterns", "foreign-term")(
                lambda: _patterns([[s["term_foreign"]]])
            )
        else:
            case("ir.Arena.set_quantifier_patterns", label)(lambda g=groups: _patterns(g))

    # --- datatypes: constructor and field indices out of range --------------
    def _datatype(constructor_index, args):
        arena = ir.Arena()
        datatype = arena.declare_datatype("D")
        constructor = arena.add_constructor(datatype, "mk", [("f", ir.Sort.bv(8))])
        target = constructor if constructor_index is None else constructor_index
        return arena.construct(target, args)

    case("ir.Arena.construct", "no-args")(lambda: _datatype(None, []))
    case("ir.Arena.construct", "too-many-args")(lambda: _datatype(None, [None, None, None]))
    case("ir.Arena.construct", "bad-constructor")(lambda: _datatype(1 << 40, []))

    # --- the SMT-LIB front door on scripts that stress the parse routes -----
    for label, text in (
        ("empty", ""),
        ("truncated", "(assert"),
        ("no-check-sat", "(set-logic QF_BV)"),
        ("multi-check-sat", "(set-logic QF_BV)(check-sat)(check-sat)"),
        ("word-fallback", '(set-logic QF_S)(declare-const s String)(assert (= s "a"))(check-sat)'),
        (
            "astral-literal",
            '(set-logic QF_S)(declare-const s String)(assert (= s "\\u{1F600}"))(check-sat)',
        ),
        (
            "escape-literal",
            '(set-logic QF_S)(declare-const s String)(assert (= s "\\u0041"))(check-sat)',
        ),
        (
            "bad-escape",
            '(set-logic QF_S)(declare-const s String)(assert (= s "\\u{110000}"))(check-sat)',
        ),
        ("quantified", "(set-logic LIA)(assert (forall ((x Int)) (>= x 0)))(check-sat)"),
        ("zero-width-bv", "(set-logic QF_BV)(declare-const x (_ BitVec 0))(check-sat)"),
        ("huge-width-bv", "(set-logic QF_BV)(declare-const x (_ BitVec 70000))(check-sat)"),
        (
            "div-by-zero",
            "(set-logic QF_LIA)(declare-const x Int)(assert (= (div x 0) 1))(check-sat)",
        ),
        (
            "get-value-no-model",
            (
                "(set-logic QF_BV)(declare-const x (_ BitVec 8))"
                "(assert false)(check-sat)(get-value (x))"
            ),
        ),
    ):
        case("smt.solve", label)(lambda t=text: smt.solve(t))
        case("smt.parse", label)(lambda t=text: smt.parse(t))
        case("smt.solve+replay", label)(lambda t=text: _solve_then_replay(smt, t))

    # --- every route that reaches `Rational::checked_new` -------------------
    #
    # `checked_new` is documented as the overflow-graceful counterpart of `new`,
    # and it KEEPS `new`'s `assert!(den != 0)`. So every binding call site that
    # passes a caller-supplied denominator is a panic site, and the name of the
    # function is what hides it. The generic sweep found only the first of these
    # -- the others need a tuple, a duck-typed object, or a rounding mode, none
    # of which a name-keyed pool produces.
    class _ZeroDenominator:
        """Not a `Fraction`, but `py_to_value` accepts anything with the pair."""

        numerator = 1
        denominator = 0

    case("ir.Arena.real_ratio", "den=0")(lambda: ir.Arena().real_ratio(1, 0))
    case("ir.Assignment.set_real_div_zero", "numerator-den=0")(
        lambda: ir.Arena().assignment().set_real_div_zero((1, 0), (1, 1))
    )
    case("ir.Assignment.set_real_div_zero", "quotient-den=0")(
        lambda: ir.Arena().assignment().set_real_div_zero((1, 1), (1, 0))
    )

    def _real_symbol_bound_to(value):
        arena = ir.Arena()
        symbol = arena.declare("r", ir.Sort.real())
        assignment = arena.assignment()
        assignment.set(arena, symbol, value)
        return ir.eval(arena, arena.var(symbol), assignment)

    case("ir.Assignment.set", "real-den=0")(lambda: _real_symbol_bound_to(_ZeroDenominator()))

    def _fp_from_real(num, den):
        arena = ir.Arena()
        return ir.fp.from_real(arena, ir.fp.F32, ir.fp.RoundingMode.NearestTiesToEven, num, den)

    case("ir.fp.from_real", "den=0")(lambda: _fp_from_real(1, 0))
    case("ir.fp.from_real", "den=1")(lambda: _fp_from_real(1, 1))

    # --- allocation requests the Rust allocator ABORTS on --------------------
    for rows, cols in ((70000, 70000), (1 << 30, 1 << 30), (0, 0)):
        case("cas.Matrix.identity", f"n={rows}")(lambda r=rows: cas.Matrix.identity(r))
        case("cas.Matrix.zeros", f"{rows}x{cols}")(lambda r=rows, c=cols: cas.Matrix.zeros(r, c))

    # --- the CAS rational and polynomial guards -----------------------------
    for den in (0, -1):
        case("cas.Expr.rat", f"den={den}")(lambda d=den: cas.Expr.rat(1, d))
        case("cas.Rational", f"den={den}")(lambda d=den: cas.Rational(1, d))
    case("cas.Rational", "i128-overflow")(lambda: cas.Rational((1 << 200), 3))
    case("cas.normalize", "non-polynomial")(lambda: cas.normalize(s["expr_nonpoly"]))
    case("cas.normalize", "division-by-zero-expr")(lambda: cas.normalize(s["expr_div_zero"]))
    case("cas.MvPoly.pow", "huge-exponent")(lambda: s["mvpoly_ok"].pow(1 << 40))
    case("cas.MvPoly.from_terms", "empty")(lambda: cas.MvPoly.from_terms([]))
    case("cas.MvPoly.from_terms", "mismatched")(lambda: cas.MvPoly.from_terms([(None, None)]))
    case("cas.Expr.pow", "huge-exponent")(lambda: s["expr_ok"].pow(1 << 40))

    # --- the CNF / proof surface -------------------------------------------
    case("solver.cnf.parse_dimacs", "empty")(lambda: solver.cnf.parse_dimacs(""))
    case("solver.cnf.parse_dimacs", "bad-header")(lambda: solver.cnf.parse_dimacs("p cnf -1 -1\n"))
    case("solver.cnf.parse_dimacs", "huge-header")(
        lambda: solver.cnf.parse_dimacs("p cnf 4294967296 1\n1 0\n")
    )
    case("solver.cnf.check_drat", "empty")(lambda: solver.cnf.check_drat("", ""))

    # --- the dispatcher route that reaches the bv lowerer's `unreachable!()` -
    #
    # `(= s1 s2)` over two String symbols: the SAME sort that `(= (str.len s) 1)`
    # dispatches to arithmetic without trouble. Found by the Hypothesis property
    # in `python/tests/test_prop_ir.py`, not by this battery, which is the case
    # for keeping both.
    def _string_equality():
        arena = ir.Arena()
        left = arena.var(arena.declare("s0", ir.Sort.string()))
        right = arena.var(arena.declare("s1", ir.Sort.string()))
        return arena, [arena.eq(left, right)]

    for route in ("solve", "check_auto_explained", "unsat_core", "solve_with_portfolio"):
        case(f"solver.{route}", "string-equality")(
            lambda r=route: _dispatch_route(solver, r, *_string_equality())
        )

    def _string_length_equality():
        arena = ir.Arena()
        symbol = arena.var(arena.declare("s", ir.Sort.string()))
        return arena, [arena.eq(arena.seq_len(symbol), arena.int_const(1))]

    for route in ("solve", "check_auto_explained", "unsat_core"):
        case(f"solver.{route}", "string-length-equality")(
            lambda r=route: _dispatch_route(solver, r, *_string_length_equality())
        )

    # --- cross-kernel handles ----------------------------------------------
    kernel = native.kernel
    for target, thunk in (
        ("kernel.Kernel.expr_node", lambda: s["kernel"].expr_node(s["kernel2_expr"])),
        ("kernel.Kernel.infer", lambda: s["kernel"].infer(s["kernel2_expr"])),
        ("kernel.Kernel.display_name", lambda: s["kernel"].display_name(s["kernel2_name"])),
        ("kernel.Kernel.app", lambda: s["kernel"].app(s["kernel2_expr"], s["kernel_expr"])),
        ("kernel.Kernel.def_eq", lambda: s["kernel"].def_eq(s["kernel2_expr"], s["kernel_expr"])),
        ("kernel.Kernel.instantiate", lambda: s["kernel"].instantiate(s["kernel2_expr"], [])),
        ("kernel.Kernel.bvar", lambda: s["kernel"].bvar(1 << 40)),
        ("kernel.Kernel.infer", lambda: s["kernel"].infer(s["kernel"].bvar(0))),
        ("kernel.Kernel.lean_name", lambda: kernel.Kernel().lean_name([])),
        ("kernel.Kernel.lean_name", lambda: kernel.Kernel().lean_name(["\x00"])),
        ("kernel.Kernel.get_declaration", lambda: s["kernel"].get_declaration("no.such.decl")),
    ):
        case(target, "cross-kernel")(thunk)

    # --- calls that overflow the Rust stack and kill the process ------------
    #
    # These are not `PanicException`: the process dies, so `except` of any kind
    # is powerless. The probe records them as `crash` because that is what a
    # caller sees.
    case("kernel.Kernel.build_cpoint_prelude", "default-stack")(
        lambda: kernel.Kernel().build_cpoint_prelude()
    )

    def _deep_term(depth):
        arena = ir.Arena()
        term = arena.bv_const(8, 1)
        for _ in range(depth):
            term = arena.bvnot(term)
        return arena, term

    for depth in (1000, 50000):

        def _render_deep(d):
            arena, term = _deep_term(d)
            return arena.render(term)

        def _write_script_deep(d):
            arena, term = _deep_term(d)
            return arena.write_script([term])

        def _eval_deep(d):
            arena, term = _deep_term(d)
            return ir.eval(arena, term, arena.assignment())

        case("ir.Arena.render", f"depth={depth}")(lambda d=depth: _render_deep(d))
        case("ir.Arena.write_script", f"depth={depth}")(lambda d=depth: _write_script_deep(d))
        case("ir.eval", f"depth={depth}")(lambda d=depth: _eval_deep(d))
        case("smt.parse", f"depth={depth}")(
            lambda d=depth: smt.parse(
                "(set-logic QF_BV)(declare-const x (_ BitVec 8))(assert (= x "
                + "(bvnot " * d
                + "x"
                + ")" * d
                + "))(check-sat)"
            )
        )

    def _deep_expr(depth):
        expr = cas.Expr.var("x")
        for _ in range(depth):
            expr = expr + cas.Expr.int(1)
        return expr

    for depth in (1000, 50000):
        case("cas.Expr.__add__", f"depth={depth}")(lambda d=depth: str(_deep_expr(d)))
        case("cas.normalize", f"depth={depth}")(lambda d=depth: cas.normalize(_deep_expr(d)))

    # --- an incremental session driven out of balance -----------------------
    def _pop_too_far():
        session = solver.Incremental(s["arena"])
        session.pop()
        return session.scope_depth

    case("solver.Incremental.pop", "underflow")(_pop_too_far)
    return out


def _dispatch_route(solver_module, route, arena, terms):
    """One named `solver` entry point over `terms`, with a small budget."""
    config = solver_module.Config(timeout_ms=200)
    if route == "solve_with_portfolio":
        return solver_module.solve_with_portfolio(arena, terms, ["auto"], config)
    return getattr(solver_module, route)(arena, terms, config)


def _incremental_assert(solver_module, arena, terms):
    session = solver_module.Incremental(arena)
    for term in terms:
        session.assert_(term)
    return session.check()


def _solve_then_replay(smt_module, text):
    outcome = smt_module.solve(text)
    return outcome.replay()


# ------------------------------------------------------------- the case plan


class Case:
    __slots__ = ("call", "index", "target", "vector")

    def __init__(self, index, target, vector, call):
        self.index, self.target, self.vector, self.call = index, target, vector, call


def _signature(obj):
    try:
        return inspect.signature(obj)
    except (TypeError, ValueError):
        return None


def _positional(sig):
    kinds = (inspect.Parameter.POSITIONAL_ONLY, inspect.Parameter.POSITIONAL_OR_KEYWORD)
    return [p for p in sig.parameters.values() if p.kind in kinds and p.name != "self"]


def _vectors(params, s: dict):
    """Deterministic `(label, args)` battery for a parameter list.

    One-at-a-time mutation from a best-guess baseline, then uniform vectors of a
    single wrong value. Mutation from a baseline is what gets an adversarial
    argument PAST the front-door type check and into the Rust call.
    """
    baseline = [best_guess(p.name, p, s) for p in params]
    out = [("baseline", list(baseline))]
    for i, p in enumerate(params):
        cands = keyed_candidates(p.name, s) or []
        cands = cands + [(label, make(s)) for label, make in GENERIC[:6]]
        for label, value in cands:
            args = list(baseline)
            args[i] = value
            out.append((f"{p.name}:={label}", args))
    for label, make in GENERIC:
        out.append((f"all:={label}", [make(s) for _ in params]))
    if params and all(p.default is not inspect.Parameter.empty for p in params):
        out.append(("no-args", []))
    # Stable de-duplication by label; the cap keeps a wide signature bounded.
    seen, deduped = set(), []
    for label, args in out:
        if label in seen:
            continue
        seen.add(label)
        deduped.append((label, args))
    return deduped[:MAX_VECTORS_PER_CALLABLE]


def walk_surface(native):
    """`(path, kind, obj, owner)` for every public callable, in a stable order."""
    found, seen = [], set()

    def walk(module, prefix):
        if id(module) in seen:
            return
        seen.add(id(module))
        for name in sorted(dir(module)):
            if name.startswith("_"):
                continue
            obj = getattr(module, name)
            path = prefix + name
            if isinstance(obj, types.ModuleType):
                walk(obj, path + ".")
            elif isinstance(obj, type):
                found.append((path, "class", obj, None))
                for member in sorted(dir(obj)):
                    if member.startswith("_"):
                        continue
                    attribute = inspect.getattr_static(obj, member, None)
                    kind = (
                        "getter" if isinstance(attribute, types.GetSetDescriptorType) else "method"
                    )
                    found.append((f"{path}.{member}", kind, member, obj))
            elif callable(obj):
                found.append((path, "function", obj, None))

    walk(native, "")
    return found


def build_cases(native):
    """The full deterministic case list. Parent and worker call this and must
    agree index-for-index, which is what lets the parent resume past a crash."""
    s = build_specimens(native)
    receivers = build_receivers(native, s)
    cases: list[Case] = []
    unreachable: list[str] = []

    def emit(target, vector, call):
        cases.append(Case(len(cases), target, vector, call))

    # Targeted first: these are the scenarios the inventory names, and putting
    # them at low indices means a crash late in the generic sweep cannot cost
    # the measurement that actually answers the question.
    for target, label, thunk in targeted_cases(native, s):
        emit(target, label, thunk)

    for path, kind, obj, owner in walk_surface(native):
        if kind == "class":
            sig = _signature(obj)
            if sig is None:
                unreachable.append(f"{path} (class has no constructor signature)")
                continue
            for label, args in _vectors(_positional(sig), s):
                emit(path, label, (lambda f=obj, a=args: f(*a)))
            continue

        if kind in {"method", "getter"}:
            receiver = receivers.get(owner.__name__)
            if receiver is None:
                unreachable.append(f"{path} (no receiver for {owner.__name__})")
                continue
            try:
                bound = getattr(receiver, obj)
            except BaseException:  # noqa: BLE001 - an unreadable attribute is data
                unreachable.append(f"{path} (attribute access failed)")
                continue
            if kind == "getter":
                emit(path, "getter", (lambda r=receiver, n=obj: getattr(r, n)))
                continue
            sig = _signature(bound)
            if sig is None:
                emit(path, "no-args", (lambda f=bound: f()))
                continue
            for label, args in _vectors(_positional(sig), s):
                emit(path, label, (lambda f=bound, a=args: f(*a)))
            continue

        sig = _signature(obj)
        if sig is None:
            emit(path, "no-args", (lambda f=obj: f()))
            continue
        for label, args in _vectors(_positional(sig), s):
            emit(path, label, (lambda f=obj, a=args: f(*a)))

    return cases, unreachable


# ------------------------------------------------------------------ the worker


def run_worker(start: int, out_path: str) -> int:
    import resource

    resource.setrlimit(resource.RLIMIT_AS, (WORKER_ADDRESS_SPACE_BYTES, WORKER_ADDRESS_SPACE_BYTES))
    import axeyum._native as native

    cases, _ = build_cases(native)
    with open(out_path, "a", encoding="utf-8") as handle:

        def record(payload):
            # `flush()` and NOT `os.fsync()`. The parent must see the record
            # even when the worker segfaults, and a flushed write is already in
            # the page cache, which outlives the process. `fsync` would add
            # machine-crash durability nothing here needs, and measured at
            # ~0.6 s per call on this box it dominated the whole run.
            handle.write(json.dumps(payload, sort_keys=True) + "\n")
            handle.flush()

        for case in cases[start:]:
            record(
                {"i": case.index, "phase": "start", "target": case.target, "vector": case.vector}
            )
            began = time.monotonic()
            try:
                case.call()
                outcome, exc, message = "ok", "", ""
            except Exception as error:  # noqa: BLE001 - classifying is the point
                outcome, exc, message = "exception", _type_name(error), str(error)
            except BaseException as error:
                if _is_panic(error):
                    outcome = "panic"
                elif isinstance(error, (KeyboardInterrupt, SystemExit)):
                    raise
                else:
                    outcome = "base"
                exc, message = _type_name(error), str(error)
            record(
                {
                    "i": case.index,
                    "phase": "done",
                    "target": case.target,
                    "vector": case.vector,
                    "outcome": outcome,
                    "exc": exc,
                    "message": message[:400],
                    "ms": round((time.monotonic() - began) * 1000.0),
                }
            )
    return 0


def _is_panic(error) -> bool:
    """Whether `error` is `pyo3_runtime.PanicException`.

    NOT by importing `pyo3_runtime` and testing `isinstance`. That module is
    not in `sys.modules` until PyO3 has raised a panic at least once, so a type
    resolved at worker start is `None` and EVERY panic is then misfiled as some
    other `BaseException` -- measured 2026-08-25, the first run reported
    `panic 0 / base 3` for three calls that were `PanicException` all along.
    The headline total was right and the census was wrong, which is the worse
    of the two failure modes because the census is what a reader believes.

    Testing the type's own module and name needs no import and cannot go stale.
    """
    cls = type(error)
    return getattr(cls, "__module__", "") == "pyo3_runtime" and cls.__name__ == "PanicException"


def _type_name(error) -> str:
    cls = type(error)
    module = getattr(cls, "__module__", "")
    return f"{module}.{cls.__name__}" if module and module != "builtins" else cls.__name__


# ------------------------------------------------------------------ the parent


def run_probe(verbose: bool = False):
    import axeyum._native as native

    cases, unreachable = build_cases(native)
    total = len(cases)
    scratch = pathlib.Path(os.environ.get("TMPDIR", "/tmp"))
    agent = os.environ.get("AXEYUM_AGENT", "local")
    out_path = scratch / f"panic-probe-{agent}-{os.getpid()}.jsonl"
    err_path = scratch / f"panic-probe-{agent}-{os.getpid()}.stderr"
    if out_path.exists():
        out_path.unlink()

    results: dict[int, dict] = {}
    crashes: list[dict] = []
    start = 0
    while start < total:
        with open(err_path, "ab") as errors:
            proc = subprocess.run(
                [
                    sys.executable,
                    os.path.abspath(__file__),
                    "--worker",
                    "--start",
                    str(start),
                    "--out",
                    str(out_path),
                ],
                stdout=subprocess.DEVNULL,
                stderr=errors,
                timeout=None if WORKER_TIMEOUT_S <= 0 else WORKER_TIMEOUT_S * 4,
                check=False,
            )
        open_case, results = _read_results(out_path, results)
        if proc.returncode == 0 and open_case is None:
            break
        if open_case is None:
            # Died without opening a case: nothing left to attribute, stop.
            break
        crashes.append(dict(open_case, outcome="crash", exc=f"worker exit {proc.returncode}"))
        results[open_case["i"]] = crashes[-1]
        start = open_case["i"] + 1
        if verbose:
            print(
                f"  worker died on case {open_case['i']} ({open_case['target']}); resuming",
                file=sys.stderr,
            )

    _read_results(out_path, results)
    return cases, results, unreachable, crashes


def _read_results(path: pathlib.Path, results: dict):
    """Fold the worker's JSONL into `results`; return the case left open, if any."""
    open_case = None
    if not path.exists():
        return open_case, results
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        try:
            record = json.loads(line)
        except json.JSONDecodeError:
            continue  # a torn last line means the worker died mid-write
        if record.get("phase") == "start":
            open_case = record
        elif record.get("phase") == "done":
            results[record["i"]] = record
            open_case = None
    if open_case is not None and open_case["i"] in results:
        open_case = None
    return open_case, results


NOISE = [
    (re.compile(r"0x[0-9a-f]+"), "0xADDR"),
    (re.compile(r"epoch \d+"), "epoch N"),
    (re.compile(r"#\d+"), "#N"),
    (re.compile(r"/[^\s`'\"]+/axeyum[^\s`'\"]*"), "<path>"),
]


def normalize(text: str) -> str:
    for pattern, replacement in NOISE:
        text = pattern.sub(replacement, text)
    return text.strip().replace("\n", " ")[:200]


def summarize(cases, results, unreachable, crashes):
    counts = {"ok": 0, "exception": 0, "panic": 0, "base": 0, "crash": 0, "missing": 0}
    panics: dict[tuple, int] = {}
    for case in cases:
        record = results.get(case.index)
        if record is None:
            counts["missing"] += 1
            continue
        outcome = record.get("outcome", "missing")
        counts[outcome] = counts.get(outcome, 0) + 1
        if outcome in {"panic", "base", "crash"}:
            key = (
                outcome,
                case.target,
                normalize(record.get("message", "") or record.get("exc", "")),
            )
            panics[key] = panics.get(key, 0) + 1
    segfaults = counts["crash"]
    return counts, panics, segfaults


def render(cases, results, unreachable, crashes) -> str:
    counts, panics, segfaults = summarize(cases, results, unreachable, crashes)
    probed = sum(v for k, v in counts.items() if k != "missing")
    callables = len({c.target for c in cases}) + len(unreachable)
    headline = (
        f"PANIC_PROBE|callables={callables}|probed={probed}"
        f"|panics={counts['panic'] + counts['base']}|segfaults={segfaults}"
    )
    lines = [
        "# Generated panic-surface probe",
        "",
        "> Generated by `tools/panic_probe.py`. Do not hand-edit.",
        "> Regenerate with `uv run python tools/panic_probe.py --write`;",
        "> `--check` fails when this file is stale.",
        "",
        "A `panic!` inside a `#[pyfunction]` reaches Python as",
        "`pyo3_runtime.PanicException`, which derives from `BaseException` -- it",
        "escapes `except Exception` and carries a Rust internal as its message.",
        "This is the measured count of calls that do that.",
        "",
        f"    {headline}",
        "",
        "## Outcome census",
        "",
        "| outcome | calls | meaning |",
        "|---|---:|---|",
        f"| `ok` | {counts['ok']} | returned a value |",
        f"| `exception` | {counts['exception']} | raised an `Exception` subclass (the contract) |",
        f"| `panic` | {counts['panic']} | `pyo3_runtime.PanicException` -- a `BaseException` |",
        f"| `base` | {counts['base']} | some other non-`Exception` `BaseException` |",
        f"| `crash` | {counts['crash']} | the worker died (abort, segfault, or hung) |",
        "",
        (
            f"Distinct callables probed: **{len({c.target for c in cases})}**; "
            f"callables with no reachable receiver: **{len(unreachable)}**."
        ),
        "",
    ]
    if panics:
        lines += [
            "## Calls that did NOT raise an `Exception`",
            "",
            "| outcome | callable | normalized message | calls |",
            "|---|---|---|---:|",
        ]
        for (outcome, target, message), count in sorted(panics.items()):
            lines.append(f"| `{outcome}` | `{target}` | `{message}` | {count} |")
        lines.append("")
    else:
        lines += [
            "## Calls that did NOT raise an `Exception`",
            "",
            "None. Every probed call either returned a value or raised an",
            "`Exception` subclass, so `except Exception` is sufficient.",
            "",
        ]
    if unreachable:
        lines += [
            "## Callables the probe could not reach",
            "",
            "Listed rather than dropped: an unprobed callable and a clean one",
            "would otherwise be the same number.",
            "",
        ]
        lines += [f"- `{item}`" for item in sorted(unreachable)]
        lines.append("")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worker", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--start", type=int, default=0, help=argparse.SUPPRESS)
    parser.add_argument("--out", default="", help=argparse.SUPPRESS)
    parser.add_argument("--write", action="store_true", help="regenerate the report")
    parser.add_argument("--check", action="store_true", help="fail when the report is stale")
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()

    if args.worker:
        return run_worker(args.start, args.out)

    cases, results, unreachable, crashes = run_probe(verbose=args.verbose)
    report = render(cases, results, unreachable, crashes)
    headline = next(
        line.strip() for line in report.splitlines() if line.strip().startswith("PANIC_PROBE|")
    )
    print(headline)
    print()
    print("\n".join(report.splitlines()[report.splitlines().index("## Outcome census") :]))

    if args.write:
        REPORT.parent.mkdir(parents=True, exist_ok=True)
        REPORT.write_text(report, encoding="utf-8")
        print(f"wrote {REPORT}")
        return 0
    if args.check:
        if not REPORT.exists():
            print(f"MISSING: {REPORT}; run --write", file=sys.stderr)
            return 1
        if REPORT.read_text(encoding="utf-8") != report:
            print(f"STALE: {REPORT} does not match a fresh probe; run --write", file=sys.stderr)
            return 1
        print(f"OK: {REPORT} matches a fresh probe")
        return 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
