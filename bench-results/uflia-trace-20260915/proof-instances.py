#!/usr/bin/env python3
"""UFLIA-TRACE -- name the ground terms z3 substituted, from its own proof.

`(get-proof)` writes the refutation as one deeply `let`-bound s-expression whose
`(_ quant-inst t1 ... tn)` rules carry the SUBSTITUTED TERMS. Those terms are
what "the instance z3 needed" means concretely; every aggregate count of
instantiations is blind to which ones they were.

The terms arrive abbreviated -- `(+ ?x55 y)` -- so the `let` chain is expanded
before anything is reported. Reporting the abbreviations would name a z3
internal and not a term of the query.

Usage:
    proof-instances.py <proof-file> [--applications] [--json]

`--applications` prints only the uninterpreted APPLICATIONS inside the
substituted terms, deduplicated and sorted. Those are the terms a matcher must
have built to be able to fire: a bound variable can only be instantiated with a
term that exists, so an application in this list that is absent from our ground
set is a term-construction gap and not a ranking one.
"""

from __future__ import annotations

import json
import sys

# Operators that are interpreted in UFLIA, so an application of one of these is
# not a term an e-matcher has to have CONSTRUCTED: the arithmetic solver makes
# them. Only uninterpreted applications discriminate "we never built it".
INTERPRETED = {
    "+", "-", "*", "div", "mod", "abs", "<=", "<", ">=", ">", "=", "distinct",
    "and", "or", "not", "=>", "xor", "ite", "let", "true", "false",
    "select", "store", "forall", "exists", "!", "_",
}


def tokenize(text: str) -> list[str]:
    out: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c in "()":
            out.append(c)
            i += 1
        elif c.isspace():
            i += 1
        elif c == "|":
            j = text.index("|", i + 1)
            out.append(text[i : j + 1])
            i = j + 1
        elif c == ";":
            j = text.find("\n", i)
            i = n if j < 0 else j + 1
        else:
            j = i
            while j < n and not text[j].isspace() and text[j] not in "()|;":
                j += 1
            out.append(text[i:j])
            i = j
    return out


def parse(tokens: list[str], pos: int = 0):
    """Iterative s-expression parse. A z3 proof nests thousands of `let`s deep,
    so a recursive-descent parser dies on the interpreter's stack before it
    reaches the first `quant-inst` -- measured on this very population."""
    stack: list[list] = []
    cur: list = []
    while pos < len(tokens):
        t = tokens[pos]
        pos += 1
        if t == "(":
            stack.append(cur)
            cur = []
        elif t == ")":
            done = cur
            if not stack:
                return done, pos
            cur = stack.pop()
            cur.append(done)
        else:
            cur.append(t)
    return cur, pos


def render(node) -> str:
    if isinstance(node, str):
        return node
    return "(" + " ".join(render(x) for x in node) + ")"


def collect_lets(node, env: dict[str, object]) -> None:
    """Walks the proof iteratively, recording every `let` binding it meets.

    z3 emits a proof as a single chain of `(let ((@x N ...)) body)`, and a name
    is bound exactly once in the whole term, so one flat environment is correct
    and no scoping is lost.
    """
    stack = [node]
    while stack:
        cur = stack.pop()
        if isinstance(cur, str):
            continue
        if cur and cur[0] == "let" and len(cur) >= 3 and isinstance(cur[1], list):
            for binding in cur[1]:
                if isinstance(binding, list) and len(binding) == 2:
                    env[binding[0]] = binding[1]
            stack.extend(cur[2:])
            stack.extend(cur[1])
            continue
        stack.extend(x for x in cur if isinstance(x, list))


def expand(node, env: dict[str, object], depth: int = 0):
    """Substitutes `let` names until a fixpoint. `depth` bounds a cycle; z3's
    output is acyclic but a truncated proof is not, and an unbounded expander
    on a truncated file is how a lane reaches 63 GB."""
    if depth > 200:
        return node
    if isinstance(node, str):
        if node in env:
            return expand(env[node], env, depth + 1)
        return node
    return [expand(x, env, depth + 1) for x in node]


def find_quant_inst(node) -> list[list]:
    """Every `(_ quant-inst t1 ... tn)` head in the proof, in document order."""
    found: list[list] = []
    stack = [node]
    while stack:
        cur = stack.pop()
        if isinstance(cur, str):
            continue
        if len(cur) >= 2 and cur[0] == "_" and cur[1] == "quant-inst":
            found.append(cur[2:])
        stack.extend(x for x in cur if isinstance(x, list))
    return found


def applications(node, out: set[str]) -> None:
    stack = [node]
    while stack:
        cur = stack.pop()
        if isinstance(cur, str):
            continue
        if cur and isinstance(cur[0], str) and cur[0] not in INTERPRETED:
            out.add(render(cur))
        stack.extend(x for x in cur if isinstance(x, list))


def main() -> None:
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    flags = {a for a in sys.argv[1:] if a.startswith("--")}
    if not args:
        print(__doc__)
        sys.exit(2)

    text = open(args[0], encoding="utf-8", errors="replace").read()
    # The verdict line precedes the proof.
    start = text.find("(proof")
    if start < 0:
        start = text.find("((set-logic")
    if start < 0:
        print("NO-PROOF", file=sys.stderr)
        sys.exit(1)

    tree, _ = parse(tokenize(text[start:]))
    env: dict[str, object] = {}
    collect_lets(tree, env)

    heads = find_quant_inst(tree)
    terms = [[expand(t, env) for t in h] for h in heads]

    if "--applications" in flags:
        apps: set[str] = set()
        for tuple_ in terms:
            for t in tuple_:
                applications(t, apps)
        for a in sorted(apps):
            print(a)
        return

    if "--json" in flags:
        json.dump(
            {"instances": [[render(t) for t in tup] for tup in terms]},
            sys.stdout,
            indent=1,
        )
        print()
        return

    for i, tup in enumerate(terms):
        print(f"INSTANCE {i}\t" + "\t".join(render(t) for t in tup))


if __name__ == "__main__":
    main()
