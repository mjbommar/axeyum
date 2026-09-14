#!/usr/bin/env python3
"""QF-WALL -- reduce a quantifier-free skeleton to a MINIMAL unsat subset.

    minimize.py <skel.smt2> <out-core.smt2> [--tlimit S]

Step 1  split every top-level `(assert (and a b c))` into separate asserts.
        A conjunction is equivalent to its conjuncts asserted separately, so
        this is an equivalence, not a weakening -- the split file is unsat iff
        the original is, and that is CHECKED before anything else happens.
Step 2  name each assert, ask z3 for an unsat core.
Step 3  greedily delete core members one at a time, keeping the deletion only
        when the remainder is still `unsat`.  The fixpoint is minimal wrt
        single deletion (not necessarily minimum cardinality).

Every step's verdict is re-checked, so a bug that drops the unsat produces a
FAILED-PRECONDITION rather than a small file with a wrong story attached.
"""
import subprocess
import sys

Z3 = 'z3'


def scan(text, i):
    n, depth, j = len(text), 0, i
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


def args_of(form):
    """Split `(head a1 a2 ...)` into head and the argument source strings."""
    inner = form[1:-1]
    i, n = 0, len(inner)
    while i < n and inner[i].isspace():
        i += 1
    j = i
    while j < n and not inner[j].isspace() and inner[j] != '(':
        j += 1
    head = inner[i:j]
    out, i = [], j
    while i < n:
        if inner[i].isspace():
            i += 1
            continue
        if inner[i] == '(':
            k = scan(inner, i)
            out.append(inner[i:k])
            i = k
        else:
            k = i
            while k < n and not inner[k].isspace() and inner[k] != ')':
                k += 1
            out.append(inner[i:k])
            i = k
    return head, out


def body_of_assert(form):
    head, a = args_of(form)
    assert head == 'assert', head
    return a[0] if len(a) == 1 else None


def flatten(body, depth=0):
    """Split a top-level `and` into conjuncts (an equivalence, not a weakening)."""
    b = body.strip()
    if depth > 6 or not b.startswith('('):
        return [b]
    head, a = args_of(b)
    if head == 'and' and len(a) > 1:
        out = []
        for x in a:
            out.extend(flatten(x, depth + 1))
        return out
    return [b]


def run(path, tlimit, core=False):
    cmd = [Z3, f'-T:{tlimit}', path]
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=tlimit * 4 + 30)
    txt = p.stdout
    v = 'unknown'
    for line in txt.splitlines():
        s = line.strip()
        if s in ('sat', 'unsat', 'unknown'):
            v = s
            break
    names = []
    if core:
        i = txt.find('(', txt.find(v) + len(v))
        if i >= 0:
            names = txt[i + 1:txt.find(')', i)].split()
    return v, names


def write(path, prefix, bodies, names=None, get_core=False):
    with open(path, 'w') as fh:
        if get_core:
            fh.write('(set-option :produce-unsat-cores true)\n')
        fh.write('\n'.join(prefix) + '\n')
        for k, b in enumerate(bodies):
            if names is not None:
                fh.write(f'(assert (! {b} :named {names[k]}))\n')
            else:
                fh.write(f'(assert {b})\n')
        fh.write('(check-sat)\n')
        if get_core:
            fh.write('(get-unsat-core)\n')


def main():
    src, out = sys.argv[1], sys.argv[2]
    tl = 60
    if '--tlimit' in sys.argv:
        tl = int(sys.argv[sys.argv.index('--tlimit') + 1])
    fs = forms(open(src, encoding='utf-8', errors='replace').read())
    prefix, bodies = [], []
    for f in fs:
        h = args_of(f)[0] if f.startswith('(') else '?'
        if h == 'assert':
            b = body_of_assert(f)
            if b is None:
                prefix.append(f)
            else:
                bodies.extend(flatten(b))
        elif h in ('check-sat', 'exit', 'get-unsat-core', 'set-option'):
            continue
        else:
            prefix.append(f)

    tmp = out + '.work.smt2'
    write(tmp, prefix, bodies)
    v, _ = run(tmp, tl)
    if v != 'unsat':
        print(f'FAILED-PRECONDITION\tsplit file is {v}\tconjuncts={len(bodies)}')
        sys.exit(4)
    n0 = len(bodies)

    names = [f'c{k}' for k in range(len(bodies))]
    write(tmp, prefix, bodies, names, get_core=True)
    v, core = run(tmp, tl, core=True)
    if v != 'unsat' or not core:
        print(f'CORE-FAILED\t{v}\tconjuncts={n0}')
        sys.exit(5)
    keep = [bodies[int(c[1:])] for c in core if c.startswith('c')]
    n1 = len(keep)

    # greedy single-deletion minimisation
    changed = True
    while changed and len(keep) > 1:
        changed = False
        for k in range(len(keep) - 1, -1, -1):
            cand = keep[:k] + keep[k + 1:]
            write(tmp, prefix, cand)
            vv, _ = run(tmp, max(5, tl // 4))
            if vv == 'unsat':
                keep = cand
                changed = True
    write(out, prefix, keep)
    v2, _ = run(out, tl)
    print(f'{src}\tconjuncts={n0}\tz3_core={n1}\tminimal={len(keep)}\trecheck={v2}')


main()
