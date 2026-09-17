"""Lift a scalar, loop-free C function from cindergraph's AST into QF_BV queries.

Cindergraph parses the C and hands back a typed AST (``binary_expr``,
``cast_expr``, ``cond_expr``, ``if_stmt`` …) with source spans, the declared
type of every binding, and a CFG whose back edges name the loops. This module
walks that AST with C's own integer semantics — integer promotion, the usual
arithmetic conversions, wraparound on unsigned types, ``bvsdiv``/``bvudiv``
by signedness — and emits, per reachable sink, one SMT-LIB query whose ``sat``
is a concrete input that reaches the sink with its safety obligation violated.

What it deliberately does NOT do: pointers are opaque (only their annotated
capacity is modelled), there are no loops (a function with a back edge is
refused by name), and every C construct outside the subset raises
:class:`Refused` with the line and the reason. A refusal is a result; a silent
approximation would make "no witness" a measurement of the accepted subset.

Sinks, and the obligation each one must satisfy on every path that reaches it:

=====================  ==========================================================
``memcpy``/``memmove``/``memset``/``strncpy``  ``offset >= 0`` and ``offset + n <= capacity(dst)``, in 128-bit
``buf[i]``             ``i >= 0`` (signed index) and ``i < capacity(buf)``
``a / b``, ``a % b``   ``b != 0``; signed: not (``a == MIN`` and ``b == -1``)
``a << b``, ``a >> b`` ``0 <= b < width(a)``; signed ``<<``: ``a >= 0``
signed ``+ - *``       the mathematical result is representable (no UB overflow)
implicit narrowing     the stored value equals the source value (informational)
``if`` condition       both edges feasible; an infeasible edge is a dead branch
=====================  ==========================================================

Capacities are declared with a structured comment on the line before the
function: ``// axeyum: capacity(dst) = dst_len``. A local array
``T buf[N]`` declares its own.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field

try:  # cindergraph is an optional, git-installed dependency of this example.
    import cindergraph as _cg
except ImportError:  # pragma: no cover - exercised by the driver's refusal path
    _cg = None


class Refused(Exception):
    """A construct outside the lifted subset, with the line and the reason."""

    def __init__(self, line: int, why: str) -> None:
        super().__init__(f"line {line}: {why}")
        self.line = line
        self.why = why


# --------------------------------------------------------------------------
# C integer types
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class CType:
    width: int
    signed: bool

    @property
    def smt(self) -> str:
        return f"(_ BitVec {self.width})"

    def __str__(self) -> str:
        return f"{'i' if self.signed else 'u'}{self.width}"


INT = CType(32, True)
UINT = CType(32, False)
LONG = CType(64, True)
ULONG = CType(64, False)
SIZE_T = ULONG
BOOL = "bool"  # the sort of a C condition before it becomes an int

_TYPE_TABLE: dict[str, CType] = {
    "char": CType(8, True),
    "signed char": CType(8, True),
    "unsigned char": CType(8, False),
    "short": CType(16, True),
    "short int": CType(16, True),
    "unsigned short": CType(16, False),
    "unsigned short int": CType(16, False),
    "int": INT,
    "signed": INT,
    "signed int": INT,
    "unsigned": UINT,
    "unsigned int": UINT,
    "long": LONG,
    "long int": LONG,
    "long long": LONG,
    "long long int": LONG,
    "unsigned long": ULONG,
    "unsigned long int": ULONG,
    "unsigned long long": ULONG,
    "unsigned long long int": ULONG,
    "size_t": SIZE_T,
    "ssize_t": LONG,
    "ptrdiff_t": LONG,
    "intptr_t": LONG,
    "uintptr_t": ULONG,
    "int8_t": CType(8, True),
    "uint8_t": CType(8, False),
    "int16_t": CType(16, True),
    "uint16_t": CType(16, False),
    "int32_t": INT,
    "uint32_t": UINT,
    "int64_t": LONG,
    "uint64_t": ULONG,
    "_Bool": CType(8, False),
    "bool": CType(8, False),
}


def parse_ctype(text: str, line: int) -> CType:
    """The declared scalar type named by ``text`` (``const`` and ``volatile`` dropped)."""
    words = [
        w
        for w in text.replace("*", " * ").split()
        if w not in ("const", "volatile", "static", "register")
    ]
    if "*" in words:
        raise Refused(
            line, f"pointer type {text.strip()!r} is opaque here; only its capacity is modelled"
        )
    key = " ".join(words)
    if key not in _TYPE_TABLE:
        raise Refused(line, f"type {text.strip()!r} is not in the scalar subset")
    return _TYPE_TABLE[key]


def promote(t: CType) -> CType:
    """C integer promotion: anything narrower than ``int`` becomes ``int``."""
    return INT if t.width < 32 else t


def usual_arithmetic(a: CType, b: CType) -> CType:
    """The usual arithmetic conversions (C17 §6.3.1.8) after promotion."""
    a, b = promote(a), promote(b)
    if a.signed == b.signed:
        return a if a.width >= b.width else b
    unsigned, signed = (a, b) if not a.signed else (b, a)
    if unsigned.width >= signed.width:
        return unsigned
    return signed  # the wider signed type represents every value of the narrower unsigned one


# --------------------------------------------------------------------------
# Terms
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Term:
    """An SMT-LIB term with its C type, or a Bool condition (``ctype is None``)."""

    smt: str
    ctype: CType | None

    @property
    def is_bool(self) -> bool:
        return self.ctype is None


def bv_literal(value: int, t: CType) -> str:
    return f"(_ bv{value % (1 << t.width)} {t.width})"


def convert(term: Term, to: CType) -> Term:
    """Convert a value to another integer type with C's semantics (modular)."""
    if term.is_bool:
        return Term(f"(ite {term.smt} {bv_literal(1, to)} {bv_literal(0, to)})", to)
    src = term.ctype
    assert src is not None
    if src.width == to.width:
        return Term(term.smt, to)
    if src.width < to.width:
        ext = "sign_extend" if src.signed else "zero_extend"
        return Term(f"((_ {ext} {to.width - src.width}) {term.smt})", to)
    return Term(f"((_ extract {to.width - 1} 0) {term.smt})", to)


def as_bool(term: Term) -> Term:
    if term.is_bool:
        return term
    assert term.ctype is not None
    return Term(f"(not (= {term.smt} {bv_literal(0, term.ctype)}))", None)


def extend_to(term: Term, width: int) -> str:
    """The value as a ``width``-bit term keeping its sign (for wide obligations)."""
    t = term.ctype
    assert t is not None and width >= t.width
    if width == t.width:
        return term.smt
    ext = "sign_extend" if t.signed else "zero_extend"
    return f"((_ {ext} {width - t.width}) {term.smt})"


# --------------------------------------------------------------------------
# Sinks and paths
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Obligation:
    kind: str  # buffer / index / divide / shift / signed-overflow / narrowing / dead-branch
    line: int
    text: str  # the C source of the construct
    holds: str  # a Bool SMT-LIB term that must be true for the construct to be safe
    path_len: int  # how many path conditions precede the construct
    note: str = ""


@dataclass
class PathState:
    env: dict[str, Term] = field(default_factory=dict)
    conds: list[str] = field(default_factory=list)
    defs: list[tuple[str, CType, str]] = field(default_factory=list)
    obligations: list[Obligation] = field(default_factory=list)
    returned: bool = False
    counter: dict[str, int] = field(default_factory=dict)

    def fork(self) -> PathState:
        return PathState(
            dict(self.env),
            list(self.conds),
            list(self.defs),
            list(self.obligations),
            self.returned,
            dict(self.counter),
        )


@dataclass
class Query:
    function: str
    obligation: Obligation
    smtlib: str
    params: list[tuple[str, CType]]  # scalar parameters, in declaration order
    capacities: dict[str, str]  # pointer parameter -> capacity symbol


@dataclass
class Lifted:
    function: str
    line: int
    params: list[str]
    scalar_params: list[tuple[str, CType]]
    pointer_params: list[str]
    capacities: dict[str, str]
    paths: int
    queries: list[Query]


# --------------------------------------------------------------------------
# The AST walk
# --------------------------------------------------------------------------

_SINK_CALLS = {"memcpy", "memmove", "memset", "strncpy"}
STOPPING = {"buffer", "buffer-read", "index-negative", "index-high", "divide"}
_CAP_RE = re.compile(r"//\s*axeyum:\s*capacity\((\w+)\)\s*=\s*(\w+)")
_ARRAY_RE = re.compile(r"^\s*(\w+)\s*\[\s*(\d+)\s*\]\s*$")
_INT_LIT_RE = re.compile(r"^(0[xX][0-9a-fA-F]+|0[0-7]*|[1-9][0-9]*)([uUlL]*)$")


class _Ast:
    def __init__(self, src: str, doc: dict) -> None:
        self.src = src
        self.raw = src.encode("utf-8")  # cindergraph spans are BYTE offsets
        self.nodes = {n["id"]: n for n in doc["nodes"]}
        kids: dict[int, list[int]] = {}
        for e in doc["edges"]:
            kids.setdefault(e["source"], []).append(e["target"])
        self.kids = {k: sorted(v, key=lambda i: self.span(i)[0]) for k, v in kids.items()}

    def span(self, i: int) -> tuple[int, int]:
        s, e = self.nodes[i]["span"].split(":")
        return int(s), int(e)

    def slice(self, start: int, end: int) -> str:
        return self.raw[start:end].decode("utf-8", errors="replace")

    def text(self, i: int) -> str:
        s, e = self.span(i)
        return self.slice(s, e)

    def tag(self, i: int) -> str:
        return self.nodes[i]["tag"]

    def label(self, i: int) -> str:
        return self.nodes[i]["label"].split("\n", 1)[-1]

    def line(self, i: int) -> int:
        return self.raw.count(b"\n", 0, self.span(i)[0]) + 1

    def children(self, i: int) -> list[int]:
        return self.kids.get(i, [])

    def gap(self, a: int, b: int) -> str:
        """The source text between two sibling nodes: where the operator lives."""
        return self.slice(self.span(a)[1], self.span(b)[0]).strip()


class Lifter:
    def __init__(self, src: str, ast: _Ast, root: int) -> None:
        self.src = src
        self.ast = ast
        self.root = root
        self.types: dict[str, CType] = {}
        self.pointers: set[str] = set()
        self.capacities: dict[str, str] = {}
        self.consts: list[tuple[str, CType]] = []
        self.name = ""
        self.params: list[str] = []

    # -- declarations ------------------------------------------------------

    def declare_params(self) -> None:
        a = self.ast
        decl = next(c for c in a.children(self.root) if a.tag(c) == "declarator")
        self.name = a.label(next(c for c in a.children(decl) if a.tag(c) == "decl_name"))
        plist = next((c for c in a.children(decl) if a.tag(c) == "param_list"), None)
        for p in a.children(plist) if plist is not None else []:
            text = a.label(p).strip()
            if text == "void":
                continue
            m = re.match(r"^(.*?)\s*(\**)\s*(\w+)$", text)
            if not m:
                raise Refused(
                    a.line(p), f"parameter {text!r} is not a scalar or pointer declaration"
                )
            tname, stars, pname = m.group(1), m.group(2), m.group(3)
            self.params.append(pname)
            if stars or "*" in tname:
                self.pointers.add(pname)
            else:
                t = parse_ctype(tname, a.line(p))
                self.types[pname] = t
                self.consts.append((pname, t))

    def read_capacity_annotations(self) -> None:
        start = self.ast.span(self.root)[0]
        head = self.ast.slice(0, start)
        # Annotations sit on the lines immediately above the function.
        tail = "\n".join(head.rstrip().splitlines()[-4:])
        for m in _CAP_RE.finditer(tail):
            ptr, cap = m.group(1), m.group(2)
            if ptr not in self.pointers:
                raise Refused(
                    self.ast.line(self.root),
                    f"capacity annotation names {ptr!r}, not a pointer parameter",
                )
            if cap.isdigit():
                self.capacities[ptr] = bv_literal(int(cap), SIZE_T)
            elif cap in self.types:
                self.capacities[ptr] = cap
            else:
                raise Refused(
                    self.ast.line(self.root),
                    f"capacity {cap!r} for {ptr!r} is not a scalar parameter",
                )

    # -- expressions -------------------------------------------------------

    def literal(self, i: int) -> Term:
        text = self.ast.label(i).strip()
        line = self.ast.line(i)
        if text.startswith("'"):
            body = text[1:-1]
            if body.startswith("\\"):
                raise Refused(line, f"escaped character literal {text!r}")
            return Term(bv_literal(ord(body), INT), INT)
        m = _INT_LIT_RE.match(text)
        if not m:
            raise Refused(line, f"literal {text!r} is not an integer literal")
        digits, suffix = m.group(1), m.group(2).lower()
        value = (
            int(digits, 16)
            if digits[:2].lower() == "0x"
            else int(digits, 8)
            if digits.startswith("0") and len(digits) > 1
            else int(digits)
        )
        unsigned = "u" in suffix
        long_ = "l" in suffix
        if not long_ and not unsigned:
            t = (
                INT
                if value < 1 << 31
                else LONG
                if digits[:2].lower() != "0x" or value >= 1 << 32
                else UINT
            )
        elif unsigned and not long_:
            t = UINT if value < 1 << 32 else ULONG
        elif long_ and not unsigned:
            t = LONG
        else:
            t = ULONG
        return Term(bv_literal(value, t), t)

    def name_ref(self, i: int, state: PathState) -> Term:
        name = self.ast.label(i).strip()
        if name in state.env:
            return state.env[name]
        if name in self.pointers:
            raise Refused(self.ast.line(i), f"pointer {name!r} used as a value")
        raise Refused(self.ast.line(i), f"unknown name {name!r}")

    def sizeof(self, i: int, state: PathState) -> Term:
        a = self.ast
        child = a.children(i)[0]
        inner = (
            a.children(child)[0] if a.tag(child) == "paren_expr" and a.children(child) else child
        )
        text = a.text(inner).strip()
        if a.tag(inner) == "name_ref" and text in state.env:
            t = state.env[text].ctype
            assert t is not None
            return Term(bv_literal(t.width // 8, SIZE_T), SIZE_T)
        return Term(bv_literal(parse_ctype(text, a.line(i)).width // 8, SIZE_T), SIZE_T)

    def unary(self, i: int, state: PathState) -> Term:
        a = self.ast
        child = a.children(i)[0]
        op = a.slice(a.span(i)[0], a.span(child)[0]).strip()
        if op == "sizeof":
            return self.sizeof(i, state)
        if op in ("&", "*"):
            raise Refused(
                a.line(i), f"unary {op!r} on {a.text(i).strip()!r}: pointers are opaque here"
            )
        x = self.expr(child, state)
        if op == "!":
            return Term(f"(not {as_bool(x).smt})", None)
        if x.is_bool:
            x = convert(x, INT)
        assert x.ctype is not None
        t = promote(x.ctype)
        x = convert(x, t)
        if op == "-":
            if t.signed:
                # `bvnego` (SMT-LIB 2.6) is exactly "a is the signed minimum",
                # the one value whose negation does not fit back in `t.width`
                # bits -- no double-width arithmetic needed.
                self.obligation(state, "signed-overflow", i, f"(not (bvnego {x.smt}))")
            return Term(f"(bvneg {x.smt})", t)
        if op == "~":
            return Term(f"(bvnot {x.smt})", t)
        if op == "+":
            return x
        raise Refused(a.line(i), f"unary operator {op!r}")

    def binary(self, i: int, state: PathState) -> Term:
        a = self.ast
        kids = a.children(i)
        acc = self.expr(kids[0], state)
        for left, right in zip(kids, kids[1:]):
            op = a.gap(left, right)
            acc = self.apply(op, acc, self.expr(right, state), i, state)
        return acc

    def apply(self, op: str, x: Term, y: Term, node: int, state: PathState) -> Term:
        line = self.ast.line(node)
        if op == "&&":
            return Term(f"(and {as_bool(x).smt} {as_bool(y).smt})", None)
        if op == "||":
            return Term(f"(or {as_bool(x).smt} {as_bool(y).smt})", None)
        if x.is_bool:
            x = convert(x, INT)
        if y.is_bool:
            y = convert(y, INT)
        assert x.ctype is not None and y.ctype is not None
        if op in ("<<", ">>"):
            t = promote(x.ctype)
            amt_t = promote(y.ctype)
            xv, amt = convert(x, t), convert(y, amt_t)
            holds = f"(bvult {extend_to(amt, 64)} {bv_literal(t.width, ULONG)})"
            if amt_t.signed:
                holds = f"(and (bvsge {amt.smt} {bv_literal(0, amt_t)}) {holds})"
            if op == "<<" and t.signed:
                holds = f"(and (bvsge {xv.smt} {bv_literal(0, t)}) {holds})"
            self.obligation(state, "shift", node, holds)
            amt_same = convert(amt, t)
            if op == "<<":
                return Term(f"(bvshl {xv.smt} {amt_same.smt})", t)
            return Term(f"({'bvashr' if t.signed else 'bvlshr'} {xv.smt} {amt_same.smt})", t)
        t = usual_arithmetic(x.ctype, y.ctype)
        xv, yv = convert(x, t), convert(y, t)
        if op in ("<", "<=", ">", ">=", "==", "!="):
            table = {
                "<": "bvslt" if t.signed else "bvult",
                "<=": "bvsle" if t.signed else "bvule",
                ">": "bvsgt" if t.signed else "bvugt",
                ">=": "bvsge" if t.signed else "bvuge",
            }
            if op == "==":
                return Term(f"(= {xv.smt} {yv.smt})", None)
            if op == "!=":
                return Term(f"(not (= {xv.smt} {yv.smt}))", None)
            return Term(f"({table[op]} {xv.smt} {yv.smt})", None)
        if op in ("+", "-", "*"):
            bvop = {"+": "bvadd", "-": "bvsub", "*": "bvmul"}[op]
            if t.signed:
                # SMT-LIB 2.6's overflow-detection predicates (`bvsaddo` /
                # `bvssubo` / `bvsmulo`) state the obligation directly, at
                # the operand width -- no double-width sign-extended
                # shadow computation needed.
                overflow_op = {"+": "bvsaddo", "-": "bvssubo", "*": "bvsmulo"}[op]
                self.obligation(
                    state,
                    "signed-overflow",
                    node,
                    f"(not ({overflow_op} {xv.smt} {yv.smt}))",
                    note=f"{t} arithmetic",
                )
            return Term(f"({bvop} {xv.smt} {yv.smt})", t)
        if op in ("/", "%"):
            holds = f"(not (= {yv.smt} {bv_literal(0, t)}))"
            if t.signed:
                holds = f"(and {holds} (not (and (= {xv.smt} {bv_literal(1 << (t.width - 1), t)}) (= {yv.smt} {bv_literal(-1, t)}))))"
            self.obligation(state, "divide", node, holds)
            if op == "/":
                return Term(f"({'bvsdiv' if t.signed else 'bvudiv'} {xv.smt} {yv.smt})", t)
            return Term(f"({'bvsrem' if t.signed else 'bvurem'} {xv.smt} {yv.smt})", t)
        if op in ("&", "|", "^"):
            return Term(
                f"({ {'&': 'bvand', '|': 'bvor', '^': 'bvxor'}[op] } {xv.smt} {yv.smt})".replace(
                    "( ", "("
                ).replace(" )", ")"),
                t,
            )
        raise Refused(line, f"binary operator {op!r}")

    def expr(self, i: int, state: PathState) -> Term:
        a = self.ast
        tag = a.tag(i)
        if tag == "literal":
            return self.literal(i)
        if tag == "name_ref":
            return self.name_ref(i, state)
        if tag == "paren_expr":
            return self.expr(a.children(i)[0], state)
        if tag == "unary_expr":
            return self.unary(i, state)
        if tag == "binary_expr":
            return self.binary(i, state)
        if tag == "cast_expr":
            tn, operand = a.children(i)
            target = parse_ctype(a.label(tn).strip().strip("()"), a.line(i))
            x = self.expr(operand, state)
            return convert(x, target)
        if tag == "cond_expr":
            c, x, y = (self.expr(k, state) for k in a.children(i))
            if x.is_bool or y.is_bool:
                x, y = convert(x, INT), convert(y, INT)
            assert x.ctype is not None and y.ctype is not None
            t = usual_arithmetic(x.ctype, y.ctype)
            return Term(f"(ite {as_bool(c).smt} {convert(x, t).smt} {convert(y, t).smt})", t)
        if tag == "postfix_expr":
            return self.postfix(i, state)
        if tag == "assign_expr":
            return self.assign(i, state)
        raise Refused(a.line(i), f"expression form {tag!r}: {a.text(i).strip()[:40]!r}")

    def postfix(self, i: int, state: PathState) -> Term:
        a = self.ast
        base, suffix = a.children(i)[0], a.children(i)[1]
        stag = a.tag(suffix)
        if stag == "index_suffix":
            name = a.label(base).strip()
            if name not in self.capacities:
                raise Refused(a.line(i), f"subscript on {name!r} without a known capacity")
            idx = self.expr(a.children(suffix)[0], state)
            if idx.is_bool:
                idx = convert(idx, INT)
            assert idx.ctype is not None
            it = promote(idx.ctype)
            iv = convert(idx, it)
            elem = self.types.get(f"{name}[]", CType(8, False))
            # Capacities are in bytes; the index is in elements.
            cap_elems = f"(bvudiv {self.capacities[name]} {bv_literal(elem.width // 8, SIZE_T)})"
            high = f"(bvult {extend_to(iv, 128)} ((_ zero_extend 64) {cap_elems}))"
            if it.signed:
                nonneg = f"(bvsge {iv.smt} {bv_literal(0, it)})"
                self.obligation(
                    state, "index-negative", i, nonneg, note=f"index into {name} is negative"
                )
                high = (
                    f"(or (not {nonneg}) {high})"  # the too-large half, given a non-negative index
                )
            self.obligation(
                state,
                "index-high",
                i,
                high,
                note=f"index into {name} is past its {cap_elems if False else 'capacity'}",
            )
            return self.element_symbol(name, elem, state)
        if stag == "call_args":
            return self.call(i, base, suffix, state)
        if stag == "inc_dec_suffix":
            raise Refused(a.line(i), f"{a.text(i).strip()!r}: ++/-- only as a statement")
        raise Refused(a.line(i), f"postfix form {stag!r}")

    def element_symbol(self, name: str, elem: CType, state: PathState) -> Term:
        # An element read is an unconstrained value of the element type; the
        # index obligation is what the sink checks.
        sym = f"{name}_elem_{self.fresh(state, name)}"
        self.consts.append((sym, elem))
        return Term(sym, elem)

    def call(self, i: int, base: int, args_node: int, state: PathState) -> Term:
        a = self.ast
        fname = a.label(base).strip()
        args = a.children(args_node)
        if fname not in _SINK_CALLS:
            raise Refused(
                a.line(i), f"call to {fname!r} is not modelled (only {sorted(_SINK_CALLS)})"
            )
        if fname == "memset":
            dst, _value, n = args
            srcp = None
        else:
            dst, srcp, n = args
        length = self.expr(n, state)
        if length.is_bool:
            length = convert(length, INT)
        assert length.ctype is not None
        n64 = convert(length, SIZE_T)  # the argument is converted to size_t
        for ptr_node, kind, verb in ((dst, "buffer", "writes"), (srcp, "buffer-read", "reads")):
            if ptr_node is None:
                continue
            base_name, offset = self.pointer_arith(ptr_node, state)
            cap = self.capacities.get(base_name)
            if cap is None:
                raise Refused(a.line(i), f"{fname} on {base_name!r} without a capacity annotation")
            off128 = extend_to(offset, 128)
            holds = f"(bvule (bvadd {off128} ((_ zero_extend 64) {n64.smt})) ((_ zero_extend 64) {cap}))"
            if offset.ctype is not None and offset.ctype.signed:
                holds = f"(and (bvsge {offset.smt} {bv_literal(0, offset.ctype)}) {holds})"
            self.obligation(
                state,
                kind,
                i,
                holds,
                note=f"{fname} {verb} {a.text(n).strip()} bytes at {a.text(ptr_node).strip()}",
            )
        return Term(bv_literal(0, INT), INT)

    def pointer_arith(self, node: int, state: PathState) -> tuple[str, Term]:
        """``p`` or ``p + off`` → (pointer name, byte offset term)."""
        a = self.ast
        if a.tag(node) == "name_ref":
            name = a.label(node).strip()
            if name not in self.pointers:
                raise Refused(a.line(node), f"{name!r} is not a pointer parameter")
            return name, Term(bv_literal(0, SIZE_T), SIZE_T)
        if a.tag(node) == "binary_expr":
            kids = a.children(node)
            if len(kids) == 2 and a.gap(kids[0], kids[1]) == "+" and a.tag(kids[0]) == "name_ref":
                name = a.label(kids[0]).strip()
                if name in self.pointers:
                    off = self.expr(kids[1], state)
                    if off.is_bool:
                        off = convert(off, INT)
                    assert off.ctype is not None
                    return name, convert(off, promote(off.ctype))
        raise Refused(
            a.line(node),
            f"destination {a.text(node).strip()!r} is not `p` or `p + offset` on a pointer parameter",
        )

    def assign(self, i: int, state: PathState) -> Term:
        a = self.ast
        lhs, rhs = a.children(i)
        op = a.gap(lhs, rhs)
        if a.tag(lhs) == "postfix_expr":
            # buf[i] = v : the index obligation is the finding; the store itself is not modelled.
            self.postfix(lhs, state)
            value = self.expr(rhs, state)
            return value
        if a.tag(lhs) != "name_ref":
            raise Refused(a.line(i), f"assignment target {a.text(lhs).strip()!r}")
        name = a.label(lhs).strip()
        if name not in state.env:
            raise Refused(a.line(i), f"assignment to unknown {name!r}")
        target = state.env[name].ctype
        assert target is not None
        value = self.expr(rhs, state)
        if op != "=":
            value = self.apply(op[:-1], state.env[name], value, i, state)
        return self.store(name, target, value, i, state)

    def store(self, name: str, target: CType, value: Term, node: int, state: PathState) -> Term:
        if value.is_bool:
            value = convert(value, INT)
        assert value.ctype is not None
        if value.ctype != target and (
            value.ctype.width > target.width or value.ctype.signed != target.signed
        ):
            back = convert(convert(value, target), value.ctype)
            self.obligation(
                state,
                "narrowing",
                node,
                f"(= {back.smt} {value.smt})",
                note=f"{value.ctype} stored into {target} {name}",
            )
        stored = convert(value, target)
        sym = f"{name}_{self.fresh(state, name)}"
        state.defs.append((sym, target, stored.smt))
        state.env[name] = Term(sym, target)
        return state.env[name]

    def fresh(self, state: PathState, name: str) -> int:
        state.counter[name] = state.counter.get(name, 0) + 1
        return state.counter[name]

    def obligation(
        self, state: PathState, kind: str, node: int, holds: str, note: str = ""
    ) -> None:
        state.obligations.append(
            Obligation(
                kind,
                self.ast.line(node),
                self.ast.text(node).strip(),
                holds,
                len(state.conds),
                note,
            )
        )

    # -- statements ----------------------------------------------------------

    def stmt(self, i: int, state: PathState) -> list[PathState]:
        a = self.ast
        tag = a.tag(i)
        if state.returned:
            return [state]
        if tag == "compound_stmt":
            return self.block(a.children(i), state)
        if tag == "decl":
            return [self.decl(i, state)]
        if tag == "expr_stmt":
            e = a.children(i)[0]
            if a.tag(e) == "postfix_expr" and a.tag(a.children(e)[1]) == "inc_dec_suffix":
                name = a.label(a.children(e)[0]).strip()
                one = Term(bv_literal(1, INT), INT)
                op = "+" if a.text(a.children(e)[1]).strip() == "++" else "-"
                self.store(
                    name,
                    state.env[name].ctype,
                    self.apply(op, state.env[name], one, e, state),
                    e,
                    state,
                )  # type: ignore[arg-type]
            else:
                self.expr(e, state)
            return [state]
        if tag == "return_stmt":
            for c in a.children(i):
                self.expr(c, state)
            state.returned = True
            return [state]
        if tag == "if_stmt":
            kids = a.children(i)
            cond = as_bool(self.expr(kids[0], state))
            then_state, else_state = state.fork(), state.fork()
            then_state.conds.append(cond.smt)
            else_state.conds.append(f"(not {cond.smt})")
            # A dead-branch obligation on each edge: "this edge is feasible".
            for st, edge in ((then_state, "true"), (else_state, "false")):
                st.obligations.append(
                    Obligation(
                        "dead-branch",
                        a.line(kids[0]),
                        a.text(kids[0]).strip(),
                        "false",
                        len(st.conds),
                        note=f"{edge} edge",
                    )
                )
            out = self.stmt(kids[1], then_state)
            out += self.stmt(kids[2], else_state) if len(kids) > 2 else [else_state]
            return out
        if tag in ("for_stmt", "while_stmt", "do_stmt"):
            raise Refused(a.line(i), f"{tag}: loops are refused (no unrolling in this lifter)")
        raise Refused(a.line(i), f"statement form {tag!r}")

    def block(self, stmts: list[int], state: PathState) -> list[PathState]:
        states = [state]
        for s in stmts:
            states = [t for st in states for t in self.stmt(s, st)]
        return states

    def decl(self, i: int, state: PathState) -> PathState:
        a = self.ast
        kids = a.children(i)
        spec = next(k for k in kids if a.tag(k) == "decl_specifiers")
        declarator = next(k for k in kids if a.tag(k) == "declarator")
        init = next((k for k in kids if a.tag(k) == "initializer"), None)
        dtext = a.text(declarator).strip()
        m = _ARRAY_RE.match(dtext)
        if m:
            name, count = m.group(1), int(m.group(2))
            elem = parse_ctype(a.label(spec), a.line(i))
            self.pointers.add(name)
            self.capacities[name] = bv_literal(count * (elem.width // 8), SIZE_T)
            self.types[f"{name}[]"] = elem
            if init is not None:
                raise Refused(a.line(i), f"array initializer for {name!r}")
            return state
        if "*" in dtext or "*" in a.label(spec):
            raise Refused(a.line(i), f"local pointer {dtext!r}")
        name = a.label(next(k for k in a.children(declarator) if a.tag(k) == "decl_name")).strip()
        t = parse_ctype(a.label(spec), a.line(i))
        if init is None:
            sym = f"{name}_uninit"
            self.consts.append((sym, t))
            state.env[name] = Term(sym, t)
            return state
        value = self.expr(a.children(init)[0], state)
        self.store(name, t, value, i, state)
        return state

    # -- queries -------------------------------------------------------------

    def run(self) -> Lifted:
        self.declare_params()
        self.read_capacity_annotations()
        state = PathState(env={p: Term(p, t) for p, t in self.consts})
        body = next(c for c in self.ast.children(self.root) if self.ast.tag(c) == "compound_stmt")
        finals = self.stmt(body, state)
        queries: list[Query] = []
        for st in finals:
            for ob in st.obligations:
                queries.append(self.query(st, ob))
        # Obligations are per path; the same construct reached on two paths
        # produces two queries, and the driver dedupes by (line, kind, verdict).
        scalar = [(p, self.types[p]) for p in self.params if p in self.types]
        return Lifted(
            self.name,
            self.ast.line(self.root),
            list(self.params),
            scalar,
            [p for p in self.params if p in self.pointers],
            dict(self.capacities),
            len(finals),
            queries,
        )

    def query(self, st: PathState, ob: Obligation) -> Query:
        lines = ["(set-logic QF_BV)", "(set-option :produce-models true)"]
        seen: set[str] = set()
        for name, t in self.consts:
            if name not in seen:
                seen.add(name)
                lines.append(f"(declare-const {name} {t.smt})")
        for sym, t, term in st.defs:
            lines.append(f"(define-fun {sym} () {t.smt} {term})")
        for cap in self.capacities.values():
            if not cap.startswith("(_ bv"):
                # Keep every capacity allocatable so the witness can be replayed.
                lines.append(f"(assert (bvule {cap} {bv_literal(65536, SIZE_T)}))")
        for c in st.conds[: ob.path_len]:
            lines.append(f"(assert {c})")
        # Execution must REACH this sink: every earlier obligation whose
        # violation stops the program (a memory fault, a division trap) is
        # assumed to hold. Ones the program survives — a narrowing store, a
        # signed overflow at -O0, a bad shift — are not, because the textbook
        # bugs are exactly the ones where that survived violation defeats a
        # later check.
        for earlier in st.obligations:
            if earlier is ob:
                break
            if earlier.kind in STOPPING and earlier.path_len <= ob.path_len:
                lines.append(f"(assert {earlier.holds})")
        lines.append(f"(assert (not {ob.holds}))")
        lines.append("(check-sat)")
        names = [n for n, _ in self.consts]
        lines.append(f"(get-value ({' '.join(names)}))")
        return Query(
            self.name,
            ob,
            "\n".join(lines) + "\n",
            [(p, self.types[p]) for p in self.params if p in self.types],
            dict(self.capacities),
        )


# --------------------------------------------------------------------------
# Entry point
# --------------------------------------------------------------------------


def lift_source(src: str) -> list[Lifted | tuple[str, Refused]]:
    """Every function in ``src``: a :class:`Lifted`, or ``(name, Refused)``."""
    if _cg is None:
        raise RuntimeError(
            "cindergraph is not installed: uv pip install 'cindergraph @ git+https://github.com/mjbommar/cindergraph.git@main'"
        )
    report = _cg.analyze(src)
    if report.diagnostics:
        raise RuntimeError(f"cindergraph diagnostics: {[str(d) for d in report.diagnostics]}")
    out: list[Lifted | tuple[str, Refused]] = []
    cfgs = {
        name: json.loads(doc) for name, doc in _cg.export_graphs(src, repr="cfg", format="json")
    }
    for name, doc in _cg.export_graphs(src, repr="ast", format="json"):
        ast = _Ast(src, json.loads(doc))
        root = next(i for i in ast.nodes if ast.tag(i) == "func_def")
        try:
            back = [e for e in cfgs[name]["edges"] if e.get("back") not in (None, "false", False)]
            if back:
                raise Refused(
                    ast.line(root),
                    f"{len(back)} loop back edge(s) in cindergraph's CFG; loops are refused",
                )
            out.append(Lifter(src, ast, root).run())
        except Refused as r:
            out.append((name, r))
    return out
