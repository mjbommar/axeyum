#!/usr/bin/env python3
"""Shape features for QF_NRA corpus files (ADR-2110, lane NRA-TRACE).

One row per file: declared `:status`, the number of 0-ary declared symbols
("variables"), the maximum polynomial degree reachable in any assertion, and
whether real division / `to_int` / `ite` / a top-level disjunction appear.

Why a parser and not a grep
---------------------------

`grep -c '/'` counts the slash in a comment and in the path
`20161105-Sturm-MBO`; a degree read off `*` nesting by regex cannot see
`(^ x 4)` and cannot see that `(* 2 x)` is degree 1 while `(* x x)` is
degree 2.  Every number here comes from the s-expression, and a file this
reader cannot parse is NAMED on stderr and makes the command exit non-zero --
it is never silently a zero row (CLAUDE.md: a tool that omits rather than
refuses measures the accepted subset, not the set).

`max_degree` is an UPPER BOUND on the syntactic degree of the polynomial
atoms: a `let`-bound name inherits its definition's degree, `(^ t n)`
multiplies, and `(/ a b)` contributes `deg a + deg b` while setting the
`has_div` column.  It is not the degree after simplification, and the column
header says so.
"""

from __future__ import annotations

import sys
import threading
from pathlib import Path

NUMERIC = set("0123456789")

#: Some `LassoRanker` and `hycomp` assertions nest ~1,000 deep, so the reader
#: runs on a thread with its own large stack rather than under CPython's
#: default 1,000-frame limit.  The alternative -- reading a `RecursionError`
#: as "unparsed" -- would have silently dropped 63 of 83 files from the
#: population, which is exactly the omission this module refuses to make.
RECURSION_LIMIT = 200_000
THREAD_STACK_BYTES = 512 * 1024 * 1024


class ParseError(Exception):
    """The file is not an s-expression this reader can read."""


def tokenize(text: str) -> list[str]:
    out: list[str] = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == ";":
            while i < n and text[i] != "\n":
                i += 1
        elif c in " \t\r\n":
            i += 1
        elif c in "()":
            out.append(c)
            i += 1
        elif c == '"':
            j = i + 1
            while j < n:
                if text[j] == '"':
                    if j + 1 < n and text[j + 1] == '"':
                        j += 2
                        continue
                    break
                j += 1
            out.append(text[i : j + 1])
            i = j + 1
        elif c == "|":
            j = text.find("|", i + 1)
            if j < 0:
                raise ParseError("unterminated |symbol|")
            out.append(text[i : j + 1])
            i = j + 1
        else:
            j = i
            while j < n and text[j] not in " \t\r\n();":
                j += 1
            out.append(text[i:j])
            i = j
    return out


def parse(tokens: list[str]) -> list:
    pos = 0

    def rd():
        nonlocal pos
        if pos >= len(tokens):
            raise ParseError("unexpected end of input")
        t = tokens[pos]
        pos += 1
        if t == "(":
            items = []
            while pos < len(tokens) and tokens[pos] != ")":
                items.append(rd())
            if pos >= len(tokens):
                raise ParseError("unterminated (")
            pos += 1
            return items
        if t == ")":
            raise ParseError("unexpected )")
        return t

    forms = []
    while pos < len(tokens):
        forms.append(rd())
    return forms


def is_numeral(tok: str) -> bool:
    if not tok:
        return False
    body = tok[1:] if tok[0] in "+-" and len(tok) > 1 else tok
    return bool(body) and all(ch in NUMERIC or ch == "." for ch in body)


def is_constant(term) -> bool:
    """Whether `term` is a ground numeric constant.

    SMT-LIB has no negative numeral, so every negative coefficient is the
    APPLICATION `(- 471)`, and `meti-tarski` writes rational coefficients as
    `(/ (- 471) 100)`.  A first version of this reader tested only
    `isinstance(a, str) and is_numeral(a)` on the operands of `/`, so every
    such coefficient counted as symbolic real division: it reported 31 files
    with a symbolic denominator where 29 of them were `meti-tarski` constants
    and the real answer is 2.  The whole finding it fed -- "division
    elimination is the bucket" -- would have been an artefact of this
    function.
    """
    if isinstance(term, str):
        return is_numeral(term)
    if not term or isinstance(term[0], list):
        return False
    head = term[0]
    if head in ("-", "+", "*", "/") and len(term) >= 2:
        return all(is_constant(a) for a in term[1:])
    if head == "to_real" and len(term) == 2:
        return is_constant(term[1])
    return False


#: Operators whose result degree is the MAX of the argument degrees.
MAX_OPS = frozenset(
    {
        "+",
        "-",
        "=",
        "<",
        "<=",
        ">",
        ">=",
        "distinct",
        "and",
        "or",
        "not",
        "=>",
        "xor",
        "abs",
        "to_real",
    }
)


class Shape:
    """One file's measured shape."""

    def __init__(self) -> None:
        self.status = "unknown"
        self.n_vars = 0
        self.max_degree = 0
        self.n_assert = 0
        self.has_div = False
        self.has_div_const = False
        self.has_to_int = False
        self.has_ite = False
        self.has_top_or = False
        #: The largest absolute integer literal anywhere in an assertion.
        #: `nra_real_root::MAX_ABS_COEFF` is `1 << 40`, so a file whose
        #: coefficients run past that cannot reach the exact root-isolation
        #: decider at all, whatever its degree or variable count.
        self.max_abs_int = 0
        self.unparsed_ops: set[str] = set()


def degree(term, env: dict[str, int], sh: Shape) -> int:
    if isinstance(term, str):
        if is_numeral(term):
            body = term.lstrip("+-")
            if body.isdigit():
                sh.max_abs_int = max(sh.max_abs_int, int(body))
            return 0
        if term in ("true", "false"):
            return 0
        if term in env:
            return env[term]
        return 1  # a declared symbol
    if not term:
        return 0
    head = term[0]
    if isinstance(head, list):
        # `((_ ...) args)` or an annotated head; the max of the parts is still
        # an upper bound.
        return max((degree(a, env, sh) for a in term), default=0)
    if head == "let":
        inner = dict(env)
        for binding in term[1]:
            inner[binding[0]] = degree(binding[1], env, sh)
        return degree(term[2], inner, sh)
    if head in ("forall", "exists"):
        inner = dict(env)
        for binding in term[1]:
            inner[binding[0]] = 1
        return degree(term[2], inner, sh)
    if head == "!":
        return degree(term[1], env, sh)
    if head == "*":
        return sum(degree(a, env, sh) for a in term[1:])
    if head == "^":
        base = degree(term[1], env, sh)
        exp = term[2]
        if isinstance(exp, str) and is_numeral(exp) and "." not in exp:
            return base * int(exp)
        return base
    if head == "/":
        # A `(/ <numeral> <numeral>)` is a RATIONAL LITERAL, not real division.
        # Reading the two as one column was this reader's first wrong answer:
        # 40 of 83 files "had division" and on inspection 34 of them were
        # `meti-tarski` coefficient literals such as `(/ 9062500 7)`, with no
        # symbolic denominator anywhere. The columns are separate because the
        # engines treat them as nothing alike -- `nra::eliminate_real_div`
        # fires on the second and never on the first.
        # The column that matters is whether the DENOMINATOR is symbolic. A
        # constant denominator is a scaling: `nra::eliminate_real_div` has no
        # `y = 0` branch to introduce and the atom stays polynomial. Only a
        # non-constant denominator forces the `(y = 0) or (x = r*y)` case
        # split that multiplies both the cross-product count and the Boolean
        # skeleton.
        if all(is_constant(a) for a in term[2:]):
            sh.has_div_const = True
            num = degree(term[1], env, sh)
            for a in term[2:]:
                degree(a, env, sh)
            return num
        sh.has_div = True
        return sum(degree(a, env, sh) for a in term[1:])
    if head == "to_int":
        sh.has_to_int = True
        return degree(term[1], env, sh)
    if head == "ite":
        sh.has_ite = True
        return max((degree(a, env, sh) for a in term[1:]), default=0)
    if head in MAX_OPS:
        return max((degree(a, env, sh) for a in term[1:]), default=0)
    sh.unparsed_ops.add(head if isinstance(head, str) else "?")
    return max((degree(a, env, sh) for a in term[1:]), default=0)


def top_disjunction(term) -> bool:
    if isinstance(term, list) and term:
        if term[0] == "or":
            return True
        if term[0] == "let" and len(term) >= 3:
            return top_disjunction(term[2])
        if term[0] == "!" and len(term) >= 2:
            return top_disjunction(term[1])
    return False


def shape_of(path: Path) -> Shape:
    sh = Shape()
    forms = parse(tokenize(path.read_text(encoding="utf-8", errors="replace")))
    for form in forms:
        if not isinstance(form, list) or not form:
            continue
        head = form[0]
        if head == "set-info" and len(form) >= 3 and form[1] == ":status":
            sh.status = form[2] if isinstance(form[2], str) else "unknown"
        elif head == "declare-fun" and len(form) >= 4:
            if isinstance(form[2], list) and not form[2]:
                sh.n_vars += 1
        elif head == "declare-const":
            sh.n_vars += 1
        elif head == "assert" and len(form) >= 2:
            sh.n_assert += 1
            sh.max_degree = max(sh.max_degree, degree(form[1], {}, sh))
            if top_disjunction(form[1]):
                sh.has_top_or = True
    return sh


COLUMNS = (
    "file",
    "status",
    "n_vars",
    "max_degree",
    "n_assert",
    "has_div",
    "has_div_const",
    "max_abs_int_log2",
    "has_to_int",
    "has_ite",
    "has_top_or",
)


def main(argv: list[str]) -> int:
    if len(argv) < 3:
        print("usage: shape-features.py CORPUS_ROOT LIST_FILE", file=sys.stderr)
        return 2
    root = Path(argv[1])
    listing = Path(argv[2]).read_text().split()
    failed: list[str] = []
    print("\t".join(COLUMNS))
    for rel in listing:
        try:
            sh = shape_of(root / rel)
        except (ParseError, OSError) as exc:
            failed.append(f"{rel}: {exc}")
            continue
        print(
            "\t".join(
                str(x)
                for x in (
                    rel,
                    sh.status,
                    sh.n_vars,
                    sh.max_degree,
                    sh.n_assert,
                    int(sh.has_div),
                    int(sh.has_div_const),
                    sh.max_abs_int.bit_length(),
                    int(sh.has_to_int),
                    int(sh.has_ite),
                    int(sh.has_top_or),
                )
            )
        )
    for line in failed:
        print(f"shape-features: UNPARSED {line}", file=sys.stderr)
    # Exit status depends on the finding: an unparsed file is not a silent
    # omission from the population.
    return 1 if failed else 0


def _run(argv: list[str]) -> int:
    sys.setrecursionlimit(RECURSION_LIMIT)
    threading.stack_size(THREAD_STACK_BYTES)
    box: list[int] = []
    worker = threading.Thread(target=lambda: box.append(main(argv)))
    worker.start()
    worker.join()
    # An empty box means the worker died (a stack overflow kills the thread and
    # leaves the process alive); that is a failure, not a pass.
    return box[0] if box else 3


if __name__ == "__main__":
    sys.exit(_run(sys.argv))
