#!/usr/bin/env python3
"""Why does `datatype_expansion_is_exact` fail, on the files where it does?

ADR-1975's census attributes 124 of 316 winnable rows across the four datatype
divisions to three MBQI refusals, and all three of them rest on ONE predicate:
`datatype_expansion_is_exact` in `crates/axeyum-solver/src/datatype_native.rs`,
which is false exactly when some constructor field has sort `Datatype(_)` --
`field_sort_expands` admits `Bool`/`BitVec`/`Int`/`Real`/`Uninterpreted` and
datatype-free arrays, and nothing else.

A lane sizing a fix needs to know which of two very different shapes it faces:

  NESTED       a datatype whose fields mention OTHER datatypes, with no cycle.
               A recursive expansion TERMINATES, at a depth this script reports.
  RECURSIVE    a datatype that reaches itself. A recursive expansion does not
               terminate and needs a depth bound with its own soundness story.

It parses the `declare-datatypes` blocks out of the SMT-LIB text rather than
going through the solver, so a refusal cannot hide the answer from it, and
because the answer is a property of the BENCHMARK and not of our encoding.

Exit status depends on the finding: non-zero if any examined file could not be
parsed, because an unparsed file is indistinguishable from a file with no
datatypes and would silently shrink the denominator.

    usage: dt-exactness-field-shape.py <file-list> [<file-list> ...]

Each list holds paths relative to the corpus root, one per line (the key form
of `bench-results/*/census/*.winnable.tsv`), or absolute paths.
"""

import collections
import pathlib
import re
import sys

CORPUS = pathlib.Path(
    "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental"
)

# Sorts `field_sort_expands` admits, spelled as they appear in SMT-LIB text.
# `Array` is admitted only when it mentions no datatype, which this script
# handles by looking for a declared datatype name inside the array sort.
SCALAR = {"Bool", "Int", "Real", "RoundingMode"}


def tokenize(text: str) -> list[str]:
    return text.replace("(", " ( ").replace(")", " ) ").split()


def sexprs(tokens: list[str], start: int) -> tuple[list, int]:
    """Reads one s-expression beginning at `tokens[start]`."""
    if tokens[start] != "(":
        return tokens[start], start + 1
    out: list = []
    i = start + 1
    while i < len(tokens) and tokens[i] != ")":
        node, i = sexprs(tokens, i)
        out.append(node)
    return out, i + 1


def flatten(node) -> list[str]:
    if isinstance(node, str):
        return [node]
    return [a for n in node for a in flatten(n)]


def datatype_graph(path: pathlib.Path) -> tuple[dict[str, set[str]], bool]:
    """`{datatype: set of datatype names its fields mention}`, plus parsed-ok."""
    try:
        text = path.read_text(errors="replace")
    except OSError:
        return {}, False
    # Strip line comments; a `;` inside a |quoted| symbol would break this, and
    # these corpora do not use one -- asserted by the parse check below.
    text = re.sub(r";[^\n]*", "", text)
    tokens = tokenize(text)
    names: list[str] = []
    bodies: list = []
    i = 0
    while i < len(tokens):
        if tokens[i] == "(" and i + 1 < len(tokens) and tokens[i + 1] in (
            "declare-datatypes",
            "declare-datatype",
        ):
            form, i = sexprs(tokens, i)
            if form[0] == "declare-datatype":
                # (declare-datatype name (ctor ...))
                names.append(form[1])
                bodies.append(form[2] if len(form) > 2 else [])
            elif len(form) >= 3:
                # SMT-LIB 2.6: (declare-datatypes ((name arity) ...) (body ...))
                decls, bods = form[1], form[2]
                for d, b in zip(decls, bods):
                    names.append(d[0] if isinstance(d, list) else d)
                    bodies.append(b)
            elif len(form) == 2:
                # SMT-LIB 2.0 legacy, which is what the SPARK corpus emits:
                # (declare-datatypes () ((name ctor ...) ...)) reaches here only
                # when the parameter list was elided; the NAME lives inside each
                # body. Both spellings appear in these divisions, and reading
                # only the 2.6 form reported every SPARK file as `no-datatype`.
                for b in form[1]:
                    if isinstance(b, list) and b and isinstance(b[0], str):
                        names.append(b[0])
                        bodies.append(b[1:])
            continue
        i += 1
    declared = set(names)
    graph = {n: set() for n in names}
    for n, body in zip(names, bodies):
        for tok in flatten(body):
            if tok in declared:
                graph[n].add(tok)
    return graph, True


def classify(graph: dict[str, set[str]]) -> str:
    """`recursive` if any datatype reaches itself, else `nested` / `flat`."""
    if not graph:
        return "no-datatype"

    def reaches(start: str) -> set[str]:
        seen: set[str] = set()
        stack = list(graph.get(start, ()))
        while stack:
            n = stack.pop()
            if n in seen:
                continue
            seen.add(n)
            stack.extend(graph.get(n, ()))
        return seen

    if any(n in reaches(n) for n in graph):
        return "recursive"
    return "nested" if any(graph.values()) else "flat"


def depth(graph: dict[str, set[str]]) -> int:
    """Longest datatype-field chain; only meaningful when not recursive."""
    memo: dict[str, int] = {}

    def d(n: str) -> int:
        if n in memo:
            return memo[n]
        memo[n] = 0  # guards a cycle; `classify` has already reported one
        memo[n] = 1 + max((d(m) for m in graph.get(n, ())), default=-1)
        return memo[n]

    return max((d(n) for n in graph), default=0)


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print(__doc__, file=sys.stderr)
        return 2
    kinds: collections.Counter = collections.Counter()
    depths: collections.Counter = collections.Counter()
    unparsed: list[str] = []
    examined = 0
    for list_path in argv[1:]:
        for line in pathlib.Path(list_path).read_text().split("\n"):
            rel = line.strip()
            if not rel:
                continue
            path = pathlib.Path(rel) if rel.startswith("/") else CORPUS / rel
            graph, ok = datatype_graph(path)
            if not ok:
                unparsed.append(rel)
                continue
            examined += 1
            kind = classify(graph)
            kinds[kind] += 1
            if kind == "nested":
                depths[depth(graph)] += 1
    print(f"examined {examined} files from {len(argv) - 1} list(s)")
    for k, v in kinds.most_common():
        print(f"  {v:5d}  {k}")
    if depths:
        print("  nested field-chain depth (how deep a recursive expansion goes):")
        for k in sorted(depths):
            print(f"    depth {k}: {depths[k]}")
    if unparsed:
        print(f"UNPARSED {len(unparsed)} files, e.g. {unparsed[:3]}"
              " -- an unparsed file reads as 'no datatype' and would shrink the"
              " denominator silently")
        return 1
    if not examined:
        print("NOTHING EXAMINED -- an empty result from a tool never pointed at"
              " its subject is not a negative finding")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
