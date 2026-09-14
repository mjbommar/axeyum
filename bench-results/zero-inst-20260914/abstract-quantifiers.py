#!/usr/bin/env python3
"""ZERO-INST -- replace every maximal quantified subformula by a fresh Boolean
constant, producing the file's QUANTIFIER-FREE BOOLEAN SKELETON.

    abstract-quantifiers.py <file> <out.smt2>

This is the standard CDCL(T) Boolean abstraction: each distinct quantified
subformula becomes one opaque propositional atom.  It is a WEAKENING -- the
skeleton has strictly more models than the original -- so

    skeleton UNSAT  ==>  original UNSAT

is valid, and that is the only direction claimed here.  The converse is not
claimed and is false in general.

Why this instrument exists rather than a cvc5 flag: a flag measures cvc5.
This measures the BENCHMARK, so the answer does not depend on any solver's
internals, and can be checked by any two independent solvers.

Prints, to stderr, the number of abstracted occurrences and distinct atoms.
A run that abstracts ZERO occurrences has measured nothing, and the caller
must treat that as a failed probe rather than as a skeleton.
"""
import re
import sys

HEAD = re.compile(r'\(\s*([A-Za-z0-9_.\-!|]+)')


def forms(text):
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c == ';':
            j = text.find('\n', i)
            i = n if j < 0 else j + 1
            continue
        if c.isspace():
            i += 1
            continue
        if c != '(':
            j = i
            while j < n and not text[j].isspace():
                j += 1
            i = j
            continue
        j = scan(text, i)
        out.append(text[i:j])
        i = j
    return out


def scan(text, i):
    """Return the index just past the s-expression starting at text[i]=='('."""
    n = len(text)
    depth, j = 0, i
    while j < n:
        ch = text[j]
        if ch == ';':
            k = text.find('\n', j)
            j = n if k < 0 else k + 1
            continue
        if ch == '"':
            j += 1
            while j < n:
                if text[j] == '"':
                    if j + 1 < n and text[j + 1] == '"':
                        j += 2
                        continue
                    j += 1
                    break
                j += 1
            continue
        if ch == '|':
            k = text.find('|', j + 1)
            j = n if k < 0 else k + 1
            continue
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
            if depth == 0:
                return j + 1
        j += 1
    return n


def head(f):
    m = HEAD.match(f)
    return m.group(1) if m else '?'


QSTART = re.compile(r'\(\s*(forall|exists)\s')


def abstract(text, atoms):
    """Replace every MAXIMAL (forall ...)/(exists ...) subterm by an atom.

    Maximal = outermost.  Scanning left to right and skipping past each
    match's full extent means a quantifier nested inside another is never
    visited, which is what makes the atoms opaque.
    """
    out = []
    i, n = 0, len(text)
    count = 0
    while i < n:
        m = QSTART.search(text, i)
        if not m:
            out.append(text[i:])
            break
        s = m.start()
        e = scan(text, s)
        body = text[s:e]
        name = atoms.get(body)
        if name is None:
            name = f'QABS_{len(atoms)}'
            atoms[body] = name
        out.append(text[i:s])
        out.append(name)
        count += 1
        i = e
    return ''.join(out), count


def main():
    path, out = sys.argv[1], sys.argv[2]
    fs = forms(open(path, encoding='utf-8', errors='replace').read())
    atoms = {}
    total = 0
    body = []
    prefix = []
    for f in fs:
        h = head(f)
        if h in ('check-sat', 'exit', 'set-info'):
            continue
        if h == 'assert':
            a, c = abstract(f, atoms)
            total += c
            body.append(a)
        else:
            prefix.append(f)
    decls = [f'(declare-fun {n} () Bool)' for n in atoms.values()]
    with open(out, 'w') as fh:
        fh.write('\n'.join(prefix + decls + body + ['(check-sat)']) + '\n')
    print(f'{out}\toccurrences_abstracted={total}\tdistinct_atoms={len(atoms)}',
          file=sys.stderr)
    if total == 0:
        sys.exit(3)


main()
