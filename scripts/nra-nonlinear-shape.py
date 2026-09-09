#!/usr/bin/env python3
"""How many variables each nonlinear ATOM of a QF_NRA benchmark actually couples.

Written 2026-09-09 to size one specific capability against the `QF_NRA` parity
losses. The `meti-tarski` family (49 of the 75) is a polynomial approximation of
a transcendental function: a HIGH-DEGREE atom in ONE variable, plus LINEAR atoms
that tie that variable to others. If that shape dominates, the missing procedure
is not a general CAD — it is "solve the univariate nonlinear atoms exactly into
an interval constraint, then hand the residual to LRA", which is complete on
exactly this fragment.

So the question is per ATOM, not per file: an atom's variable count is what a
decision procedure has to handle at once, while a file's variable count is the
union over atoms and says nothing about coupling.

    scripts/nra-nonlinear-shape.py <file>...
    scripts/nra-nonlinear-shape.py --list <file-list>

Reports, per file, the maximum number of distinct variables inside any single
nonlinear atom, and aggregates that over the population.

This is a SYNTACTIC reading of the s-expression, deliberately: it is a sizing
measurement for a design question, not an admission test, and nothing in the
solver consumes it. It does not normalize polynomials, so a product that cancels
still counts — which can only OVERSTATE the coupling, never understate it, so a
"mostly univariate" finding from it is a lower bound on how univariate the
population is.
"""

import collections
import sys

# The `meti-tarski` asserts are ONE right-nested `and` per file, so both the
# parser and the walkers recurse once per conjunct. The default 1000 is not
# enough for the larger chunks; raising it is the whole fix, and a file that
# still overflows is reported as SKIPPED rather than silently dropped.
sys.setrecursionlimit(100_000)


def tokenize(text):
    """S-expression tokens, with `;` comments and `|quoted|` symbols removed."""
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c == ";":
            while i < n and text[i] != "\n":
                i += 1
        elif c == "|":
            j = text.index("|", i + 1)
            out.append(text[i : j + 1])
            i = j + 1
        elif c in "()":
            out.append(c)
            i += 1
        elif c.isspace():
            i += 1
        else:
            j = i
            while j < n and not text[j].isspace() and text[j] not in "();|":
                j += 1
            out.append(text[i:j])
            i = j
    return out


def parse(tokens, pos=0):
    """One s-expression from `tokens[pos:]`, as nested lists."""
    if tokens[pos] != "(":
        return tokens[pos], pos + 1
    out, pos = [], pos + 1
    while tokens[pos] != ")":
        item, pos = parse(tokens, pos)
        out.append(item)
    return out, pos + 1


def top_level(text):
    tokens = tokenize(text)
    pos, forms = 0, []
    while pos < len(tokens):
        form, pos = parse(tokens, pos)
        forms.append(form)
    return forms


def vars_in(node, declared, acc):
    if isinstance(node, str):
        if node in declared:
            acc.add(node)
        return
    for child in node:
        vars_in(child, declared, acc)


def is_nonlinear(node, declared):
    """True if `node` contains a `*` whose operands both carry a variable, or a
    `/` whose divisor does — the two ways an atom leaves linear arithmetic."""
    if isinstance(node, str):
        return False
    if node and node[0] == "*":
        withvar = 0
        for arg in node[1:]:
            acc = set()
            vars_in(arg, declared, acc)
            if acc:
                withvar += 1
        if withvar >= 2:
            return True
    if node and node[0] == "/" and len(node) == 3:
        acc = set()
        vars_in(node[2], declared, acc)
        if acc:
            return True
    return any(is_nonlinear(c, declared) for c in node)


ATOM_HEADS = {"<", "<=", ">", ">=", "=", "distinct"}


def atoms(node, out):
    """Every comparison atom in the term, as a list."""
    if isinstance(node, str):
        return
    if node and isinstance(node[0], str) and node[0] in ATOM_HEADS:
        out.append(node)
        return
    for child in node:
        atoms(child, out)


def analyse(path):
    forms = top_level(open(path, encoding="utf-8", errors="replace").read())
    declared = {
        f[1]
        for f in forms
        if isinstance(f, list) and f and f[0] in ("declare-fun", "declare-const")
    }
    found = []
    for f in forms:
        if isinstance(f, list) and f and f[0] == "assert":
            atoms(f[1], found)
    widths = []
    for atom in found:
        if not is_nonlinear(atom, declared):
            continue
        acc = set()
        vars_in(atom, declared, acc)
        widths.append(len(acc))
    return len(declared), len(found), widths


def main(paths):
    hist = collections.Counter()
    rows = []
    for path in paths:
        try:
            nvars, natoms, widths = analyse(path)
        except (IndexError, ValueError, RecursionError) as exc:
            print(f"SKIPPED (unparsed) {path}: {exc}", file=sys.stderr)
            continue
        worst = max(widths) if widths else 0
        hist[worst] += 1
        rows.append((path.rsplit("/", 1)[-1], nvars, natoms, len(widths), worst))

    print(f"{len(rows)} files\n")
    print("== widest NONLINEAR atom, by variable count ==")
    total = sum(hist.values())
    for k in sorted(hist):
        label = "no nonlinear atom" if k == 0 else f"{k} variable(s)"
        print(f"  {label:22s} {hist[k]:3d} files  ({hist[k] / total:5.1%})")

    print("\n== per file ==")
    print(f"{'file':46s} {'decls':>6s} {'atoms':>6s} {'nl':>4s} {'widest':>7s}")
    for name, nvars, natoms, nnl, worst in sorted(rows, key=lambda r: (r[4], r[0])):
        print(f"{name[:46]:46s} {nvars:6d} {natoms:6d} {nnl:4d} {worst:7d}")


if __name__ == "__main__":
    args = sys.argv[1:]
    if args[:1] == ["--list"]:
        files = [
            line.strip()
            for line in open(args[1], encoding="utf-8")
            if line.strip()
        ]
    else:
        files = args
    main(files)
