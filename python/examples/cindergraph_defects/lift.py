"""Lift a scalar C function from cindergraph's AST into QF_BV queries.

Cindergraph parses the C and hands back a typed AST (``binary_expr``,
``cast_expr``, ``cond_expr``, ``if_stmt``, ``for_stmt`` …) with source spans,
the declared type of every binding, and a CFG whose back edges name the loops.
This module walks that AST with C's own integer semantics — integer promotion,
the usual arithmetic conversions, wraparound on unsigned types,
``bvsdiv``/``bvudiv`` by signedness — and emits, per reachable sink, one
SMT-LIB query whose ``sat`` is a concrete input that reaches the sink with its
safety obligation violated.

Loops are unrolled to a stated bound ``K`` (``unroll=``): each iteration count
``0..K`` at which the loop exits normally is its own path with the loop
condition asserted false at the exit, ``break`` and ``return`` end a path, and
the state that would need a ``K+1``-th iteration is parked behind a
``loop-bound`` obligation whose ``sat`` means "some input runs this loop past
the bound" — the driver reports that as *bounded*, never as clean. ``continue``
and ``goto`` are refused by name.

What it deliberately does NOT do: pointers are opaque (only their annotated
capacity, their annotated string length, or their ``malloc`` size is modelled),
memory contents are unconstrained, and every C construct outside the subset
raises :class:`Refused` with the line and the reason. A refusal is a result; a
silent approximation would make "no witness" a measurement of the accepted
subset.

Sinks, and the obligation each one must satisfy on every path that reaches it:

=====================  ==========================================================
``memcpy``/``memmove``/``memset``/``strncpy``  ``offset >= 0`` and ``offset + n <= capacity(dst)``, in 128-bit
``strcpy(dst, s)``     ``offset + strlen(s) + 1 <= capacity(dst)``; ``strcat`` adds ``strlen(dst)``
``buf[i]``             ``i >= 0`` (signed index) and ``i < capacity(buf) / sizeof(*buf)``
``a / b``, ``a % b``   ``b != 0``; signed: not (``a == MIN`` and ``b == -1``)
``a << b``, ``a >> b`` ``0 <= b < width(a)``; signed ``<<``: ``a >= 0``
signed ``+ - *``       the mathematical result is representable (no UB overflow)
``malloc(a * b)``      the unsigned size arithmetic does not wrap (``bvumulo``/``bvuaddo``)
implicit narrowing     the stored value equals the source value (informational)
read of a local        an assignment dominates it on this path (``uninitialized``)
use after ``free``     never (``use-after-free``; a second ``free`` is the same kind)
``if`` condition       both edges feasible; an infeasible edge is a dead branch
loop condition         false within ``K`` iterations on every input (``loop-bound``)
=====================  ==========================================================

Annotations are structured comments on the lines above the function:
``// axeyum: capacity(dst) = dst_len`` (a scalar parameter or a literal, in
bytes) and ``// axeyum: strlen(s) = n`` (the length of the NUL-terminated string
``s`` points at; ``capacity(s)`` defaults to ``n + 1``). A local array
``T buf[N]`` declares its own capacity, and ``T *p = malloc(size)`` gives ``p``
the capacity ``size``. A file-level ``// axeyum: unroll = N`` overrides the
driver's unrolling bound for every function in that file.

cindergraph (from its 2026-09-17 export) resolves those same comments itself —
``// @cindergraph`` is its marker and ``// axeyum:`` an alias — and writes the
result on the nodes: ``facts="capacity=dst_len"`` on a ``param_decl``,
``facts="unroll=17"`` on the ``func_def`` the comment precedes. The lifter reads
the attribute when the export carries it and re-reads the comment when it does
not (an older cindergraph, a synthetic AST). Likewise every node's ``line`` is
read from the export before it is counted, and a loop's ``loop_kind`` picks its
form before the statement tag does.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from itertools import pairwise

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
    kind: str  # see the module docstring's table
    line: int
    text: str  # the C source of the construct
    holds: str  # a Bool SMT-LIB term that must be true for the construct to be safe
    path_len: int  # how many path conditions precede the construct
    defs_len: int  # how many definitions precede it (later ones are not its business)
    note: str = ""


@dataclass
class PathState:
    env: dict[str, Term] = field(default_factory=dict)
    conds: list[str] = field(default_factory=list)
    defs: list[tuple[str, CType, str]] = field(default_factory=list)
    obligations: list[Obligation] = field(default_factory=list)
    returned: bool = False
    counter: dict[str, int] = field(default_factory=dict)
    broke: bool = False  # a `break` ended this path's trip through the innermost loop
    uninit: set[str] = field(default_factory=set)  # locals no assignment has reached yet
    freed: set[str] = field(default_factory=set)  # pointers `free`d on this path

    def fork(self) -> PathState:
        return PathState(
            dict(self.env),
            list(self.conds),
            list(self.defs),
            list(self.obligations),
            self.returned,
            dict(self.counter),
            self.broke,
            set(self.uninit),
            set(self.freed),
        )


@dataclass
class Query:
    function: str
    obligation: Obligation
    smtlib: str
    params: list[tuple[str, CType]]  # scalar parameters, in declaration order
    capacities: dict[str, str]  # pointer parameter -> capacity symbol


@dataclass(frozen=True)
class LoopInfo:
    """What cindergraph says about one loop: its form and, when it can tell, its bound.

    ``kind`` is ``for``/``while``/``do_while``; ``bound_kind`` is ``constant``
    (``bound_value`` holds the literal), ``parameter`` (the bound is a parameter
    the body leaves alone), ``runtime`` or absent; ``induction`` and ``step``
    name the counter and its increment (``+1``). The lifter unrolls every loop
    the same way whatever this says — the metadata is carried so a ``bounded``
    verdict can say what kind of bound was not reached.
    """

    kind: str
    bound_kind: str | None = None
    induction: str | None = None
    step: str | None = None
    bound_value: str | None = None


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
    strlens: dict[str, str] = field(default_factory=dict)  # pointer parameter -> length term
    unrolled: int | None = None  # the bound every loop in this function was unrolled to
    loops: list[LoopInfo | None] = field(default_factory=list)  # per unrolled loop, source order


# --------------------------------------------------------------------------
# The AST walk
# --------------------------------------------------------------------------

_SINK_CALLS = {"memcpy", "memmove", "memset", "strncpy", "strcpy", "strcat"}
_OTHER_CALLS = {"strlen", "free"}
_ALLOC_CALLS = {"malloc", "calloc"}
STOPPING = {"buffer", "buffer-read", "index-negative", "index-high", "divide", "use-after-free"}
# Kinds that share a runtime oracle. The replay compiles with ONE sanitizer and
# no recovery, so an earlier violation of a kind in the sink's own group aborts
# the run before the sink: the witness must satisfy those earlier obligations
# or it cannot reach the sink under the oracle that would observe it.
ORACLE_GROUP = {
    "buffer": "address",
    "buffer-read": "address",
    "index-negative": "address",
    "index-high": "address",
    "use-after-free": "address",
    "divide": "undefined",
    "shift": "undefined",
    "signed-overflow": "undefined",
    "narrowing": "implicit-conversion",
    "alloc-size-wrap": "unsigned-overflow",
    "uninitialized": "memory",
}
_CAP_RE = re.compile(r"//\s*axeyum:\s*capacity\((\w+)\)\s*=\s*(\w+)")
_STRLEN_RE = re.compile(r"//\s*axeyum:\s*strlen\((\w+)\)\s*=\s*(\w+)")
_UNROLL_RE = re.compile(r"//\s*axeyum:\s*unroll\s*=\s*(\d+)")
_ARRAY_RE = re.compile(r"^\s*(\w+)\s*\[\s*(\d+)\s*\]\s*$")
_INT_LIT_RE = re.compile(r"^(0[xX][0-9a-fA-F]+|0[0-7]*|[1-9][0-9]*)([uUlL]*)$")
DEFAULT_UNROLL = 8
MAX_PATHS = 4096  # beyond this the unrolling is refused rather than left to run
MAX_CAPACITY = 65536  # bytes; every witness must be allocatable to be replayed
_LOOP_TAGS = {"for_stmt", "while_stmt", "do_while_stmt"}


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
        """The 1-based line a node starts on: the export's ``line``, else counted.

        cindergraph writes ``line`` and ``column`` on every node since its
        2026-09-17 export; measured identical to the newline count on all
        1,100 nodes of the sample set. The count stays as the fallback for an
        older export or a synthetic node.
        """
        line = self.attr(i, "line")
        if line is not None and line.isdigit():
            return int(line)
        return self.raw.count(b"\n", 0, self.span(i)[0]) + 1

    def attr(self, i: int, key: str) -> str | None:
        """A string attribute cindergraph put on node ``i``, or ``None``."""
        value = self.nodes[i].get(key)
        return value if isinstance(value, str) else None

    def facts(self, i: int) -> dict[str, str] | None:
        """The external facts cindergraph attached to node ``i``, or ``None`` when it carries none.

        The export writes ``facts="capacity=dst_len,strlen=n"`` on a
        ``param_decl`` and ``facts="unroll=17"`` on the ``func_def`` it resolved
        the ``// @cindergraph`` / ``// axeyum:`` comments against. ``None`` (no
        attribute) and ``{}`` are different: the former means an older export
        or a node the parser attached nothing to, and the lifter then falls
        back to reading the comment itself.
        """
        raw = self.attr(i, "facts")
        if raw is None:
            return None
        out: dict[str, str] = {}
        for item in raw.split(","):
            key, sep, value = item.partition("=")
            if sep and key.strip():
                out[key.strip()] = value.strip()
        return out

    def loop_info(self, i: int) -> LoopInfo | None:
        """cindergraph's loop metadata on a loop statement, or ``None`` on an older export."""
        kind = self.attr(i, "loop_kind")
        if kind is None:
            return None
        return LoopInfo(
            kind,
            self.attr(i, "bound_kind"),
            self.attr(i, "induction"),
            self.attr(i, "step"),
            self.attr(i, "bound_value"),
        )

    def children(self, i: int) -> list[int]:
        return self.kids.get(i, [])

    def gap(self, a: int, b: int) -> str:
        """The source text between two sibling nodes: where the operator lives."""
        return self.slice(self.span(a)[1], self.span(b)[0]).strip()

    def ops(self, i: int) -> list[str] | None:
        """The operator tokens cindergraph attached to node ``i``, if its export carries them.

        Newer cindergraph exports put ``op`` (and ``ops`` on a flat chain) on
        the node; older ones do not, and the operator is then recovered from the
        bytes between two sibling spans (:meth:`gap`). The attribute wins when
        present because it is the parser's own token rather than a re-read.
        """
        node = self.nodes[i]
        if isinstance(node.get("ops"), list) and node["ops"]:
            return [str(o) for o in node["ops"]]
        if isinstance(node.get("op"), str) and node["op"]:
            return [node["op"]]
        return None

    def binary_ops(self, i: int, kids: list[int]) -> list[str]:
        ops = self.ops(i)
        if ops is not None and len(ops) == len(kids) - 1:
            return ops
        if ops is not None and len(ops) == 1 and len(kids) > 2:
            return ops * (len(kids) - 1)
        return [self.gap(a, b) for a, b in pairwise(kids)]

    def prefix_op(self, i: int, child: int) -> str:
        ops = self.ops(i)
        if ops is not None:
            return ops[0]
        return self.slice(self.span(i)[0], self.span(child)[0]).strip()


class Lifter:
    def __init__(self, src: str, ast: _Ast, root: int, unroll: int = DEFAULT_UNROLL) -> None:
        self.src = src
        self.ast = ast
        self.root = root
        self.unroll = unroll
        self.types: dict[str, CType] = {}
        self.pointers: set[str] = set()
        self.capacities: dict[str, str] = {}
        self.strlens: dict[str, str] = {}
        self.addrs: dict[str, str] = {}  # pointer -> its address symbol, once used as a value
        self.consts: list[tuple[str, CType]] = []
        self.base_asserts: list[str] = []  # facts every query of this function carries
        self.name = ""
        self.params: list[str] = []
        self.loop_depth = 0
        self.loops: list[int] = []  # lines of the loops that were unrolled
        self.loop_infos: list[LoopInfo | None] = []  # cindergraph's metadata per unrolled loop
        self.parked: list[PathState] = []  # states that ran a loop past the bound
        self.alloc_depth = 0  # >0 while lifting a malloc/calloc size argument
        self.param_nodes: dict[str, int] = {}  # parameter name -> its param_decl node

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
            self.param_nodes[pname] = p
            if stars or "*" in tname:
                self.pointers.add(pname)
                base = tname.replace("*", " ").strip()
                try:
                    self.types[f"{pname}[]"] = parse_ctype(base, a.line(p))
                except Refused:
                    pass  # `void *`, a struct pointer: bytes for sinks, refused for indexing
            else:
                t = parse_ctype(tname, a.line(p))
                self.types[pname] = t
                self.consts.append((pname, t))

    def annotations(self) -> tuple[list[tuple[str, str]], list[tuple[str, str]]]:
        """``(capacities, strlens)`` as ``(pointer, value)`` pairs, from the export or the comment.

        cindergraph resolves the ``// axeyum:`` / ``// @cindergraph`` comments
        itself and writes the result on the ``param_decl`` nodes as
        ``facts="capacity=dst_len"``; when any parameter of this function
        carries that attribute, the export is the source and the comment is not
        re-read. An export without the attribute (an older cindergraph) falls
        back to the comment on the lines immediately above the function.
        """
        exported = {p: self.ast.facts(node) for p, node in self.param_nodes.items()}
        if any(f is not None for f in exported.values()):
            caps = [(p, f["capacity"]) for p, f in exported.items() if f and "capacity" in f]
            lens = [(p, f["strlen"]) for p, f in exported.items() if f and "strlen" in f]
            return caps, lens
        start = self.ast.span(self.root)[0]
        head = self.ast.slice(0, start)
        tail = "\n".join(head.rstrip().splitlines()[-6:])
        return (
            [(m.group(1), m.group(2)) for m in _CAP_RE.finditer(tail)],
            [(m.group(1), m.group(2)) for m in _STRLEN_RE.finditer(tail)],
        )

    def read_annotations(self) -> None:
        line = self.ast.line(self.root)
        caps, lens = self.annotations()
        for ptr, cap in caps:
            if ptr not in self.pointers:
                raise Refused(line, f"capacity annotation names {ptr!r}, not a pointer parameter")
            self.capacities[ptr] = self.annotation_term(cap, ptr, "capacity", line)
        for ptr, n in lens:
            if ptr not in self.pointers:
                raise Refused(line, f"strlen annotation names {ptr!r}, not a pointer parameter")
            length = self.annotation_term(n, ptr, "strlen", line)
            self.strlens[ptr] = length
            if ptr in self.capacities:
                # The NUL fits: strlen(s) < capacity(s).
                self.base_asserts.append(f"(bvult {length} {self.capacities[ptr]})")
            else:
                cap = f"{ptr}_cap"
                self.consts.append((cap, SIZE_T))
                self.base_asserts.append(f"(= {cap} (bvadd {length} {bv_literal(1, SIZE_T)}))")
                self.capacities[ptr] = cap

    def annotation_term(self, value: str, ptr: str, what: str, line: int) -> str:
        if value.isdigit():
            return bv_literal(int(value), SIZE_T)
        if value in self.types:
            t = self.types[value]
            if t != SIZE_T:
                raise Refused(line, f"{what} {value!r} for {ptr!r} must be a size_t parameter")
            return value
        raise Refused(line, f"{what} {value!r} for {ptr!r} is not a scalar parameter or literal")

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

    def read(self, name: str, node: int, state: PathState) -> Term:
        """A read of local or parameter ``name``; an uninitialised local is a finding."""
        if name in state.uninit:
            self.obligation(
                state,
                "uninitialized",
                node,
                "false",
                note=f"{name} is read before any assignment on this path",
            )
        return state.env[name]

    def name_ref(self, i: int, state: PathState) -> Term:
        name = self.ast.label(i).strip()
        if name in state.env:
            return self.read(name, i, state)
        if name == "NULL":
            return Term(bv_literal(0, ULONG), ULONG)
        if name in self.pointers:
            # A pointer used as a value (`if (!p)`, `p == NULL`): its address is
            # an unconstrained 64-bit symbol, so both outcomes of a null test are
            # feasible and neither branch is reported dead.
            if name not in self.addrs:
                self.addrs[name] = f"{name}_addr"
                self.consts.append((self.addrs[name], ULONG))
            return Term(self.addrs[name], ULONG)
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
        if a.tag(inner) == "name_ref" and self.capacities.get(text, "").startswith("(_ bv"):
            return Term(self.capacities[text], SIZE_T)  # sizeof a local array: its bytes
        return Term(bv_literal(parse_ctype(text, a.line(i)).width // 8, SIZE_T), SIZE_T)

    def unary(self, i: int, state: PathState) -> Term:
        a = self.ast
        child = a.children(i)[0]
        op = a.prefix_op(i, child)
        if op == "sizeof":
            return self.sizeof(i, state)
        if op in ("&", "*"):
            raise Refused(
                a.line(i), f"unary {op!r} on {a.text(i).strip()!r}: pointers are opaque here"
            )
        if op in ("++", "--"):
            return self.inc_dec(child, op, i, state, prefix=True)
        x = self.expr(child, state)
        if op == "!":
            return Term(f"(not {as_bool(x).smt})", None)
        if x.is_bool:
            x = convert(x, INT)
        assert x.ctype is not None
        t = promote(x.ctype)
        x = convert(x, t)
        if op == "-":
            if t.signed and not x.smt.startswith("(_ bv"):
                # A literal never overflows on negation (2147483648 is already `long`).
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

    def inc_dec(self, target: int, op: str, node: int, state: PathState, prefix: bool) -> Term:
        """``++x`` / ``x++`` / ``--x`` / ``x--``: the store, and the value C gives the expression."""
        a = self.ast
        if a.tag(target) != "name_ref":
            raise Refused(a.line(node), f"{op} on {a.text(target).strip()!r}: only a scalar local")
        name = a.label(target).strip()
        if name not in state.env:
            raise Refused(a.line(node), f"{op} on unknown {name!r}")
        old = self.read(name, target, state)
        assert old.ctype is not None
        one = Term(bv_literal(1, INT), INT)
        new = self.store(name, old.ctype, self.apply(op[0], old, one, node, state), node, state)
        return new if prefix else old

    def binary(self, i: int, state: PathState) -> Term:
        a = self.ast
        kids = a.children(i)
        acc = self.expr(kids[0], state)
        for op, right in zip(a.binary_ops(i, kids), kids[1:]):
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
            elif self.alloc_depth > 0 and op in ("+", "*"):
                # Unsigned wrap is defined, but inside an allocation size it is
                # the bug: the block is smaller than the count says.
                overflow_op = {"+": "bvuaddo", "*": "bvumulo"}[op]
                self.obligation(
                    state,
                    "alloc-size-wrap",
                    node,
                    f"(not ({overflow_op} {xv.smt} {yv.smt}))",
                    note=f"{t} allocation size wraps",
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
            bvop = {"&": "bvand", "|": "bvor", "^": "bvxor"}[op]
            return Term(f"({bvop} {xv.smt} {yv.smt})", t)
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
            if name in state.freed:
                self.obligation(state, "use-after-free", i, "false", note=f"{name} was freed")
            idx = self.expr(a.children(suffix)[0], state)
            if idx.is_bool:
                idx = convert(idx, INT)
            assert idx.ctype is not None
            it = promote(idx.ctype)
            iv = convert(idx, it)
            elem = self.types.get(f"{name}[]")
            if elem is None:
                raise Refused(a.line(i), f"subscript on {name!r}: its element type is not scalar")
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
                state, "index-high", i, high, note=f"index into {name} is past its capacity"
            )
            return self.element_symbol(name, elem, state)
        if stag == "call_args":
            return self.call(i, base, suffix, state)
        if stag == "inc_dec_suffix":
            return self.inc_dec(base, a.text(suffix).strip(), i, state, prefix=False)
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
        if fname == "strlen":
            (s,) = args
            name = a.label(s).strip() if a.tag(s) == "name_ref" else ""
            if name not in self.strlens:
                raise Refused(
                    a.line(i),
                    f"strlen on {a.text(s).strip()!r} without a `// axeyum: strlen(...)` annotation",
                )
            if name in state.freed:
                self.obligation(state, "use-after-free", i, "false", note=f"{name} was freed")
            return Term(self.strlens[name], SIZE_T)
        if fname == "free":
            (p,) = args
            name = a.label(p).strip() if a.tag(p) == "name_ref" else ""
            if name not in self.pointers:
                raise Refused(a.line(i), f"free of {a.text(p).strip()!r}: not a pointer")
            if name in state.freed:
                self.obligation(state, "use-after-free", i, "false", note=f"{name} freed twice")
            state.freed.add(name)
            return Term(bv_literal(0, INT), INT)
        if fname not in _SINK_CALLS:
            raise Refused(
                a.line(i),
                f"call to {fname!r} is not modelled (only {sorted(_SINK_CALLS | _OTHER_CALLS)})",
            )
        if fname == "memset":
            dst, _value, n = args
            srcp = None
            length = self.expr(n, state)
        elif fname in ("strcpy", "strcat"):
            dst, srcp = args
            n = None
            src_name = a.label(srcp).strip() if a.tag(srcp) == "name_ref" else ""
            if src_name not in self.strlens:
                raise Refused(
                    a.line(i),
                    f"{fname} from {a.text(srcp).strip()!r} without a `// axeyum: strlen(...)` annotation",
                )
            # strcpy writes strlen(s) + 1 bytes (the NUL); strcat writes them after dst's own string.
            length = Term(f"(bvadd {self.strlens[src_name]} {bv_literal(1, SIZE_T)})", SIZE_T)
        else:
            dst, srcp, n = args
            length = self.expr(n, state)
        if length.is_bool:
            length = convert(length, INT)
        assert length.ctype is not None
        n64 = convert(length, SIZE_T)  # the argument is converted to size_t
        n_text = a.text(n).strip() if n is not None else f"strlen({a.text(srcp).strip()}) + 1"
        for ptr_node, kind, verb in ((dst, "buffer", "writes"), (srcp, "buffer-read", "reads")):
            if ptr_node is None:
                continue
            base_name, offset, scale = self.pointer_arith(ptr_node, state)
            cap = self.capacities.get(base_name)
            if cap is None:
                raise Refused(a.line(i), f"{fname} on {base_name!r} without a capacity annotation")
            if base_name in state.freed:
                self.obligation(state, "use-after-free", i, "false", note=f"{base_name} was freed")
            off128 = extend_to(offset, 128)
            if scale != 1:
                # Pointer arithmetic counts elements; capacities are bytes. The
                # scaling happens in the 128-bit obligation, so it cannot wrap.
                off128 = f"(bvmul {off128} {bv_literal(scale, CType(128, False))})"
            if fname == "strcat" and kind == "buffer":
                if base_name not in self.strlens:
                    raise Refused(
                        a.line(i),
                        f"strcat onto {base_name!r} without a `// axeyum: strlen(...)` annotation",
                    )
                off128 = f"(bvadd {off128} ((_ zero_extend 64) {self.strlens[base_name]}))"
            holds = f"(bvule (bvadd {off128} ((_ zero_extend 64) {n64.smt})) ((_ zero_extend 64) {cap}))"
            if offset.ctype is not None and offset.ctype.signed:
                holds = f"(and (bvsge {offset.smt} {bv_literal(0, offset.ctype)}) {holds})"
            self.obligation(
                state,
                kind,
                i,
                holds,
                note=f"{fname} {verb} {n_text} bytes at {a.text(ptr_node).strip()}",
            )
        return Term(bv_literal(0, INT), INT)

    def pointer_arith(self, node: int, state: PathState) -> tuple[str, Term, int]:
        """``p`` or ``p + off`` → (pointer name, element offset term, bytes per element)."""
        a = self.ast
        if a.tag(node) == "name_ref":
            name = a.label(node).strip()
            if name not in self.pointers:
                raise Refused(a.line(node), f"{name!r} is not a pointer parameter")
            return name, Term(bv_literal(0, SIZE_T), SIZE_T), 1
        if a.tag(node) == "binary_expr":
            kids = a.children(node)
            if (
                len(kids) == 2
                and a.binary_ops(node, kids) == ["+"]
                and a.tag(kids[0]) == "name_ref"
            ):
                name = a.label(kids[0]).strip()
                if name in self.pointers:
                    off = self.expr(kids[1], state)
                    if off.is_bool:
                        off = convert(off, INT)
                    assert off.ctype is not None
                    elem = self.types.get(f"{name}[]", CType(8, False))
                    return name, convert(off, promote(off.ctype)), elem.width // 8
        raise Refused(
            a.line(node),
            f"destination {a.text(node).strip()!r} is not `p` or `p + offset` on a pointer parameter",
        )

    def assign(self, i: int, state: PathState) -> Term:
        a = self.ast
        lhs, rhs = a.children(i)
        op = a.binary_ops(i, [lhs, rhs])[0]
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
            value = self.apply(op[:-1], self.read(name, lhs, state), value, i, state)
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
        state.uninit.discard(name)
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
                len(state.defs),
                note,
            )
        )

    # -- statements ----------------------------------------------------------

    def stmt(self, i: int, state: PathState) -> list[PathState]:
        a = self.ast
        tag = a.tag(i)
        if state.returned or state.broke:
            return [state]
        if tag == "compound_stmt":
            return self.block(a.children(i), state)
        if tag == "decl":
            return [self.decl(i, state)]
        if tag == "expr_stmt":
            if a.children(i):
                self.expr(a.children(i)[0], state)
            return [state]
        if tag == "return_stmt":
            for c in a.children(i):
                self.expr(c, state)
            state.returned = True
            return [state]
        if tag == "break_stmt":
            if self.loop_depth == 0:
                raise Refused(a.line(i), "break outside a loop (switch is not modelled)")
            state.broke = True
            return [state]
        if tag == "continue_stmt":
            raise Refused(a.line(i), "continue: not supported by the unroller")
        if tag in ("goto_stmt", "labeled_stmt", "label_stmt"):
            raise Refused(a.line(i), f"{tag}: goto is refused")
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
                        len(st.defs),
                        note=f"{edge} edge",
                    )
                )
            out = self.stmt(kids[1], then_state)
            out += self.stmt(kids[2], else_state) if len(kids) > 2 else [else_state]
            return out
        if tag in _LOOP_TAGS:
            return self.loop(i, state)
        raise Refused(a.line(i), f"statement form {tag!r}")

    def block(self, stmts: list[int], state: PathState) -> list[PathState]:
        states = [state]
        for s in stmts:
            states = [t for st in states for t in self.stmt(s, st)]
        return states

    def loop(self, i: int, state: PathState) -> list[PathState]:
        """Unroll ``for``/``while``/``do`` to ``self.unroll`` iterations.

        Every exit is its own path: after ``k`` iterations with the condition
        asserted false (a normal exit), or through ``break``/``return`` inside
        the body. A state that would need iteration ``K + 1`` is parked with a
        ``loop-bound`` obligation: the query "path conditions and the condition
        is still true" is ``sat`` exactly when some input runs the loop past the
        bound, which the driver reports rather than calling the function clean.
        """
        a = self.ast
        info = a.loop_info(i)
        # The loop's form: cindergraph's `loop_kind` when the export carries
        # it (`for`/`while`/`do_while`), else the statement tag it mirrors.
        tag = f"{info.kind}_stmt" if info is not None else a.tag(i)
        if tag not in _LOOP_TAGS:
            raise Refused(a.line(i), f"loop form {tag!r}")
        kids = a.children(i)
        init = cond = step = body = None
        if tag == "for_stmt":
            for k in kids:
                kt = a.tag(k)
                if kt == "for_init":
                    init = a.children(k)[0] if a.children(k) else None
                elif kt == "for_cond":
                    cond = a.children(k)[0] if a.children(k) else None
                elif kt == "for_step":
                    step = a.children(k)[0] if a.children(k) else None
                else:
                    body = k
        elif tag == "while_stmt":
            cond, body = kids
        else:  # do_while_stmt: the body runs before the first test
            body, cond = kids
        assert body is not None
        if init is not None and a.tag(init) == "decl":
            state = self.decl(init, state)
        elif init is not None:
            self.expr(init, state)
        self.loops.append(a.line(i))
        self.loop_infos.append(info)
        self.loop_depth += 1
        bound = self.unroll
        out: list[PathState] = []
        live = [state]

        def test(st: PathState) -> PathState | None:
            """Fork ``st`` on the loop condition; the exit goes to ``out``, the entry is returned."""
            if cond is None:
                return st  # `for (;;)`: only break/return leave
            c = as_bool(self.expr(cond, st))
            exit_st, enter_st = st.fork(), st.fork()
            exit_st.conds.append(f"(not {c.smt})")
            enter_st.conds.append(c.smt)
            out.append(exit_st)
            return enter_st

        for _ in range(bound):
            nxt: list[PathState] = []
            for st in live:
                entering = st if tag == "do_while_stmt" else test(st)
                if entering is None:
                    continue
                for bst in self.stmt(body, entering):
                    if bst.returned:
                        out.append(bst)
                    elif bst.broke:
                        bst.broke = False
                        out.append(bst)
                    else:
                        if step is not None:
                            self.expr(step, bst)
                        again = test(bst) if tag == "do_while_stmt" else bst
                        if again is not None:
                            nxt.append(again)
            live = nxt
            if len(live) + len(out) > MAX_PATHS:
                raise Refused(a.line(i), f"more than {MAX_PATHS} paths after unrolling to {bound}")
        # Whoever is still looping after `bound` iterations: would it iterate again?
        for st in live:
            entering = st if tag == "do_while_stmt" else test(st)
            if entering is None:
                continue
            entering.obligations.append(
                Obligation(
                    "loop-bound",
                    a.line(i),
                    a.text(cond).strip() if cond is not None else a.text(i).strip()[:40],
                    "false",
                    len(entering.conds),
                    len(entering.defs),
                    note=f"still true after {bound} iterations",
                )
            )
            self.parked.append(entering)
        self.loop_depth -= 1
        return out

    def decl(self, i: int, state: PathState) -> PathState:
        """``T a = x, b = a, c;``: each declarator in order, its initializer after the previous."""
        a = self.ast
        kids = a.children(i)
        spec = next(k for k in kids if a.tag(k) == "decl_specifiers")
        declarators = [k for k in kids if a.tag(k) == "declarator"]
        for declarator in declarators:
            # The initializer, if any, is the sibling right after its declarator.
            following = kids[kids.index(declarator) + 1 :]
            init = following[0] if following and a.tag(following[0]) == "initializer" else None
            state = self.one_declarator(i, spec, declarator, init, state)
        return state

    def one_declarator(
        self, i: int, spec: int, declarator: int, init: int | None, state: PathState
    ) -> PathState:
        a = self.ast
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
        name = a.label(next(k for k in a.children(declarator) if a.tag(k) == "decl_name")).strip()
        if "*" in dtext or "*" in a.label(spec):
            return self.pointer_decl(i, name, spec, dtext, init, state)
        t = parse_ctype(a.label(spec), a.line(i))
        if init is None:
            sym = f"{name}_uninit"
            self.consts.append((sym, t))
            state.env[name] = Term(sym, t)
            state.uninit.add(name)
            return state
        value = self.expr(a.children(init)[0], state)
        self.store(name, t, value, i, state)
        return state

    def pointer_decl(
        self, i: int, name: str, spec: int, dtext: str, init: int | None, state: PathState
    ) -> PathState:
        """``T *p = malloc(size)`` / ``calloc(n, size)``: ``p`` gets the capacity ``size``."""
        a = self.ast
        line = a.line(i)
        if dtext.count("*") != 1:
            raise Refused(line, f"local pointer {dtext!r}: only one level of indirection")
        call = a.children(init)[0] if init is not None else None
        if (
            call is None
            or a.tag(call) != "postfix_expr"
            or a.tag(a.children(call)[1]) != "call_args"
            or a.label(a.children(call)[0]).strip() not in _ALLOC_CALLS
        ):
            raise Refused(line, f"local pointer {dtext!r}: only `T *p = malloc(...)` is modelled")
        fname = a.label(a.children(call)[0]).strip()
        args = a.children(a.children(call)[1])
        self.alloc_depth += 1
        try:
            sizes = [self.expr(arg, state) for arg in args]
        finally:
            self.alloc_depth -= 1
        sizes = [convert(convert(s, INT) if s.is_bool else s, SIZE_T) for s in sizes]
        if fname == "calloc":
            n, each = sizes
            self.obligation(
                state,
                "alloc-size-wrap",
                call,
                f"(not (bvumulo {n.smt} {each.smt}))",
                note="calloc count * size wraps in size_t",
            )
            size = Term(f"(bvmul {n.smt} {each.smt})", SIZE_T)
        else:
            (size,) = sizes
        elem_text = a.label(spec)
        try:
            self.types[f"{name}[]"] = parse_ctype(elem_text, line)
        except Refused:
            pass  # `void *p`: bytes for sinks, refused for indexing
        cap = f"{name}_cap_{self.fresh(state, name + '_cap')}"
        state.defs.append((cap, SIZE_T, size.smt))
        self.pointers.add(name)
        self.capacities[name] = cap
        self.addrs[name] = f"{name}_addr"
        if (self.addrs[name], ULONG) not in self.consts:
            self.consts.append((self.addrs[name], ULONG))
        state.freed.discard(name)
        return state

    # -- queries -------------------------------------------------------------

    def run(self) -> Lifted:
        self.declare_params()
        self.read_annotations()
        state = PathState(env={p: Term(p, t) for p, t in self.consts if p in self.types})
        body = next(c for c in self.ast.children(self.root) if self.ast.tag(c) == "compound_stmt")
        finals = self.stmt(body, state)
        queries: list[Query] = []
        seen: set[tuple[str, int, str, str]] = set()
        for st in finals + self.parked:
            for ob in st.obligations:
                q = self.query(st, ob)
                # The same construct reached on two paths that fork AFTER it
                # yields the same query; ask it once. The key carries the
                # obligation's identity too: a feasibility question (`holds`
                # is `false`) reads the same for a dead branch and for an
                # uninitialised read on the same path, and they are not one.
                key = (ob.kind, ob.line, ob.note, q.smtlib)
                if key not in seen:
                    seen.add(key)
                    queries.append(q)
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
            dict(self.strlens),
            self.unroll if self.loops else None,
            list(self.loop_infos),
        )

    def query(self, st: PathState, ob: Obligation) -> Query:
        lines = ["(set-logic QF_BV)", "(set-option :produce-models true)"]
        seen: set[str] = set()
        defined: set[str] = set()
        for name, t in self.consts:
            if name not in seen:
                seen.add(name)
                defined.add(name)
                lines.append(f"(declare-const {name} {t.smt})")
        for sym, t, term in st.defs[: ob.defs_len]:
            defined.add(sym)
            lines.append(f"(define-fun {sym} () {t.smt} {term})")
        for cap in self.capacities.values():
            if not cap.startswith("(_ bv") and cap in defined:
                # Keep every capacity allocatable AND observable so the witness
                # can be replayed: AddressSanitizer does not see a write into a
                # zero-byte region (measured: malloc(0) then p[0] = 1 reports
                # only the leak).
                lines.append(
                    f"(assert (and (bvuge {cap} {bv_literal(1, SIZE_T)}) (bvule {cap} {bv_literal(MAX_CAPACITY, SIZE_T)})))"
                )
        lines.extend(f"(assert {fact})" for fact in self.base_asserts)
        for c in st.conds[: ob.path_len]:
            lines.append(f"(assert {c})")
        # Execution must REACH this sink: every earlier obligation whose
        # violation stops the program (a memory fault, a division trap), or
        # that the sink's own sanitizer would abort on first (`32 - n` after
        # `x << n` on one line, both under -fsanitize=undefined), is assumed
        # to hold. Ones the program survives under that oracle — a narrowing
        # store or a signed overflow before a memcpy — are not, because the
        # textbook bugs are exactly the ones where that survived violation
        # defeats a later check.
        group = ORACLE_GROUP.get(ob.kind)
        for earlier in st.obligations:
            if earlier is ob:
                break
            if earlier.path_len > ob.path_len:
                continue
            if earlier.kind in STOPPING or (
                group is not None and ORACLE_GROUP.get(earlier.kind) == group
            ):
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


def file_unroll(src: str) -> int | None:
    """The file-level ``// axeyum: unroll = N`` override, if the source carries one."""
    m = _UNROLL_RE.search(src)
    return int(m.group(1)) if m else None


def function_unroll(ast: _Ast, root: int, default: int) -> int:
    """The unrolling bound for one function: cindergraph's ``unroll`` fact, else ``default``.

    cindergraph attaches ``// axeyum: unroll = N`` to the function the comment
    precedes and writes it as ``facts="unroll=N"`` on that ``func_def``. The
    lifter's own reading is file-wide (``default`` is :func:`file_unroll` or the
    driver's bound), so a function the parser attached nothing to — the second
    function in a file whose comment sits above the first — keeps the file's
    bound, and the two readings agree wherever both exist.
    """
    facts = ast.facts(root)
    value = facts.get("unroll") if facts else None
    return int(value) if value is not None and value.isdigit() else default


def lift_source(src: str, unroll: int = DEFAULT_UNROLL) -> list[Lifted | tuple[str, Refused]]:
    """Every function in ``src``: a :class:`Lifted`, or ``(name, Refused)``.

    Loops are unrolled to ``unroll`` iterations, unless the file says
    ``// axeyum: unroll = N``, in which case ``N`` wins for that file.

    A cindergraph diagnostic (it parses tolerantly and reports what it could
    not make sense of, with a byte span) refuses the function whose span holds
    it; functions elsewhere in the file are lifted. Diagnostics outside every
    exported function — a header comment the lexer disliked, a function it gave
    up on entirely and so never exported — are returned as one refusal named
    ``"<file>"`` so the file's coverage is visible.
    """
    if _cg is None:
        raise RuntimeError(
            "cindergraph is not installed: `uv sync --dev` installs the commit "
            "pyproject.toml pins in its dev group"
        )
    report = _cg.analyze(src)
    diags = [(int(d.start), int(d.end), str(d.message)) for d in report.diagnostics]
    bound = file_unroll(src)
    if bound is None:
        bound = unroll
    out: list[Lifted | tuple[str, Refused]] = []
    cfgs = {
        name: json.loads(doc) for name, doc in _cg.export_graphs(src, repr="cfg", format="json")
    }
    covered: set[int] = set()
    raw = src.encode("utf-8")
    for name, doc in _cg.export_graphs(src, repr="ast", format="json"):
        ast = _Ast(src, json.loads(doc))
        root = next(i for i in ast.nodes if ast.tag(i) == "func_def")
        start, end = ast.span(root)
        try:
            inside = [k for k, (ds, de, _) in enumerate(diags) if ds < end and de > start]
            covered.update(inside)
            if inside:
                ds, _, msg = diags[inside[0]]
                raise Refused(
                    raw.count(b"\n", 0, ds) + 1,
                    f"cindergraph diagnostic inside this function: {msg} "
                    f"({len(inside)} in the function)",
                )
            back = [e for e in cfgs[name]["edges"] if e.get("back") not in (None, "false", False)]
            lifter = Lifter(src, ast, root, unroll=function_unroll(ast, root, bound))
            lifted = lifter.run()
            if back and not lifter.loops:
                raise Refused(
                    ast.line(root),
                    f"{len(back)} loop back edge(s) in cindergraph's CFG but no for/while/do "
                    "statement: a goto-formed loop is refused",
                )
            out.append(lifted)
        except Refused as r:
            out.append((name, r))
    outside = [k for k in range(len(diags)) if k not in covered]
    if outside:
        ds, _, msg = diags[outside[0]]
        out.append(
            (
                "<file>",
                Refused(
                    raw.count(b"\n", 0, ds) + 1,
                    f"cindergraph diagnostic outside every exported function: {msg} "
                    f"({len(outside)} such; a function the parser gave up on is not exported)",
                ),
            )
        )
    return out
