#!/usr/bin/env python3
"""DT-QUANT-TRACE -- split a real benchmark into its GROUND and QUANTIFIED
halves, keeping every declaration.

    degroundify.py <in.smt2> <out-ground.smt2> <out-quantified.smt2>

The toy reproducer in this directory is decided by `qf-bv` and
`q:bool-skeleton` long before the datatype rung runs, so it cannot test the
claim.  This takes a benchmark that DOES reach the refusal and removes exactly
one thing: the assertions carrying a quantifier.

Dropping assertions WEAKENS the query, so the ground half may legitimately turn
`unsat` into `sat`.  That is not what is being measured.  The question is
whether the ADR-0022 DATATYPE SENTENCE still appears with no quantifier
anywhere in the file -- if it does, the refusal is in the quantifier-free
closure and `auto.rs:2488`'s "mbqi declined" prefix names the wrong engine.

The quantified half is written too, and is the control in the other direction:
if it did NOT refuse, the refusal would be coming from the ground assertions
specifically rather than from the shared declarations.
"""

import sys

sys.path.insert(0, __file__.rsplit('/', 2)[0])
from dtshape import parse, tokenize, Sym  # noqa: E402


def has_quant(node):
    stack = [node]
    while stack:
        n = stack.pop()
        if isinstance(n, list):
            stack.extend(n)
        elif str(n) in ('forall', 'exists'):
            return True
    return False


def render(node, out):
    """Iterative writer -- these bodies nest hundreds deep and `repr` recursion
    dies on them."""
    stack = [node]
    while stack:
        n = stack.pop()
        if isinstance(n, str):
            out.append(n)
        elif isinstance(n, list):
            out.append('(')
            stack.append(')')
            for c in reversed(n):
                stack.append(c)
                stack.append(' ')
            if n:
                stack.pop()      # the leading separator
        else:
            out.append(str(n))


def text_of(node):
    out = []
    render(node, out)
    return ''.join(out)


def main():
    src, gout, qout = sys.argv[1], sys.argv[2], sys.argv[3]
    with open(src, errors='replace') as fh:
        forms = list(parse(tokenize(fh.read())))
    ground, quant, decls = [], [], []
    for f in forms:
        head = str(f[0]) if isinstance(f, list) and f and not isinstance(f[0], list) else ''
        if head == 'assert':
            (quant if has_quant(f) else ground).append(f)
        elif head in ('check-sat', 'exit', 'get-info', 'get-model',
                      'get-unsat-core', 'set-info'):
            continue
        else:
            decls.append(f)
    for path, keep in ((gout, ground), (qout, quant)):
        with open(path, 'w') as fh:
            for f in decls:
                fh.write(text_of(f) + '\n')
            for f in keep:
                fh.write(text_of(f) + '\n')
            fh.write('(check-sat)\n')
    print(f'decls={len(decls)} ground_asserts={len(ground)} '
          f'quantified_asserts={len(quant)}')
    # A split with nothing on one side cannot test anything; say so loudly and
    # non-zero rather than writing a file that looks like a result.
    if not ground or not quant:
        sys.stderr.write('DEGENERATE SPLIT: one half is empty\n')
        return 3
    return 0


if __name__ == '__main__':
    sys.exit(main())
