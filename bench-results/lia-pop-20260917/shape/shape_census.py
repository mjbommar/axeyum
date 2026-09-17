#!/usr/bin/env python3
"""Census of the push / assert-negation / pop shape in SMT-LIB scripts.

For each file: walk the commands, keep a scope stack of asserted term texts
(whitespace-normalised), and flag the file when an `assert` T arrives while
`(not T)` is live in ANY enclosing scope, or `(not T)` arrives while T is live.
Prints one TSV row per file: path, logic, pushes, asserts, shadow_pairs.
"""
import re
import sys


def tokens(text):
    # strip comments
    text = re.sub(r";[^\n]*", "", text)
    return re.findall(r"\(|\)|\|[^|]*\||\"(?:[^\"]|\"\")*\"|[^\s()]+", text)


def commands(text):
    toks = tokens(text)
    depth = 0
    cur = []
    for t in toks:
        if t == "(":
            depth += 1
        cur.append(t)
        if t == ")":
            depth -= 1
        if depth == 0 and cur:
            yield cur
            cur = []


def render(toks):
    out = []
    for t in toks:
        if t == "(":
            out.append("(")
        elif t == ")":
            if out and out[-1] == " ":
                out.pop()
            out.append(")")
            out.append(" ")
        else:
            out.append(t)
            out.append(" ")
    return "".join(out).strip().replace("( ", "(")


def census(path):
    text = open(path, encoding="utf-8", errors="replace").read()
    logic = "?"
    scopes = [set()]
    pushes = asserts = shadow = 0
    for cmd in commands(text):
        if len(cmd) < 2:
            continue
        head = cmd[1]
        if head == "set-logic" and len(cmd) > 2:
            logic = cmd[2]
        elif head == "push":
            n = int(cmd[2]) if len(cmd) > 3 else 1
            for _ in range(n):
                scopes.append(set())
            pushes += n
        elif head == "pop":
            n = int(cmd[2]) if len(cmd) > 3 else 1
            for _ in range(n):
                if len(scopes) > 1:
                    scopes.pop()
        elif head == "assert":
            asserts += 1
            term = render(cmd[2:-1])
            if term.startswith("(not ") and term.endswith(")"):
                neg = term[5:-1]
            else:
                neg = f"(not {term})"
            if any(neg in s for s in scopes):
                shadow += 1
            scopes[-1].add(term)
    return logic, pushes, asserts, shadow


for p in sys.argv[1:]:
    try:
        logic, pushes, asserts, shadow = census(p)
    except Exception as e:  # noqa: BLE001
        print(f"{p}\tERROR\t{e}")
        continue
    print(f"{p}\t{logic}\t{pushes}\t{asserts}\t{shadow}")
