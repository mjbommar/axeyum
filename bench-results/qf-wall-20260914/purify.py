#!/usr/bin/env python3
"""QF-WALL -- purify UF applications and array `select`s out of a ground query.

    purify.py <in.smt2> <out.smt2>

Every application `(f a1 .. an)` of a DECLARED function of arity >= 1, and
every `(select A i)`, is replaced by a FRESH CONSTANT of the same sort, shared
by structural identity after `let`-expansion.  Nullary constants are left
alone, so the arithmetic structure of the query is untouched; only the
non-arithmetic LEAVES change.

This is the standard purification step, minus congruence: two occurrences of
the same application share a constant (so reflexive congruence survives), but
`a = b  =>  f(a) = f(b)` does not.  Dropping congruence is a WEAKENING, so

    purified unsat  ==>  original unsat

and that is the only direction claimed.  If a query is unsat before
purification and SAT after, congruence was load-bearing and that is itself the
finding.

The point of the instrument: it produces a query in the SAME theory fragment
with the SAME Boolean structure, differing only in whether the arithmetic
atoms have non-arithmetic leaves.  Handing both to one solver isolates that
single axis.
"""
import sys

sys.setrecursionlimit(100000)


def tokenize(s):
    out, i, n = [], 0, len(s)
    while i < n:
        c = s[i]
        if c == ';':
            j = s.find('\n', i)
            i = n if j < 0 else j + 1
            continue
        if c.isspace():
            i += 1
            continue
        if c in '()':
            out.append(c)
            i += 1
            continue
        if c == '|':
            j = s.find('|', i + 1)
            j = n if j < 0 else j + 1
            out.append(s[i:j])
            i = j
            continue
        if c == '"':
            j = i + 1
            while j < n:
                if s[j] == '"':
                    if j + 1 < n and s[j + 1] == '"':
                        j += 2
                        continue
                    j += 1
                    break
                j += 1
            out.append(s[i:j])
            i = j
            continue
        j = i
        while j < n and not s[j].isspace() and s[j] not in '();|"':
            j += 1
        out.append(s[i:j])
        i = j
    return out


def read(toks, i):
    if toks[i] != '(':
        return toks[i], i + 1
    out, i = [], i + 1
    while toks[i] != ')':
        x, i = read(toks, i)
        out.append(x)
    return out, i + 1


def read_all(s):
    toks = tokenize(s)
    out, i = [], 0
    while i < len(toks):
        x, i = read(toks, i)
        out.append(x)
    return out


def dump(x):
    return x if isinstance(x, str) else '(' + ' '.join(dump(y) for y in x) + ')'


def expand_let(x, env):
    if isinstance(x, str):
        return env.get(x, x)
    if not x:
        return x
    if x[0] == 'let' and len(x) == 3:
        new = dict(env)
        for b in x[1]:
            new[b[0]] = expand_let(b[1], env)
        return expand_let(x[2], new)
    return [expand_let(y, env) for y in x]


def main():
    src, out = sys.argv[1], sys.argv[2]
    fs = read_all(open(src, encoding='utf-8', errors='replace').read())
    ret = {}        # declared fn name (arity >= 1) -> return sort
    elem = {}       # array-sorted constant -> element sort
    prefix, bodies = [], []
    for f in fs:
        if isinstance(f, list) and f and f[0] == 'declare-fun':
            name, args, rs = f[1], f[2], f[3]
            if isinstance(args, list) and len(args) >= 1:
                ret[name] = rs
            elif isinstance(rs, list) and rs and rs[0] == 'Array':
                elem[name] = rs[2]
        if isinstance(f, list) and f and f[0] == 'assert':
            bodies.append(f[1])
        elif isinstance(f, list) and f and f[0] in ('check-sat', 'exit', 'get-unsat-core'):
            continue
        else:
            prefix.append(f)

    fresh = {}   # structural key -> (name, sort)

    def go(x):
        if isinstance(x, str):
            return x
        if not x:
            return x
        h = x[0]
        if isinstance(h, str) and h in ret and len(x) >= 2:
            k = dump(x)
            if k not in fresh:
                fresh[k] = (f'PUR_{len(fresh)}', ret[h])
            return fresh[k][0]
        if h == 'let' and len(x) == 3:
            return ['let', [[b[0], go(b[1])] for b in x[1]], go(x[2])]
        if h == 'select' and len(x) == 3 and isinstance(x[1], str) and x[1] in elem:
            k = dump(x)
            if k not in fresh:
                fresh[k] = (f'PUR_{len(fresh)}', elem[x[1]])
            return fresh[k][0]
        if not isinstance(h, str):
            return [go(y) for y in x]
        return [h] + [go(y) for y in x[1:]]

    keep_let = '--keep-let' in sys.argv
    newb = [go(b if keep_let else expand_let(b, {})) for b in bodies]
    with open(out, 'w') as fh:
        for p in prefix:
            fh.write(dump(p) + '\n')
        for name, sort in fresh.values():
            fh.write(f'(declare-fun {name} () {dump(sort)})\n')
        for b in newb:
            fh.write(f'(assert {dump(b)})\n')
        fh.write('(check-sat)\n')
    print(f'{out}\tpurified_terms={len(fresh)}\tdeclared_fns={len(ret)}\tarrays={len(elem)}',
          file=sys.stderr)


main()
