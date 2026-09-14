#!/usr/bin/env python3
"""QF-WALL -- the SCOPE-CORRECT quantifier skeleton.

    scopeskel.py <in.smt2> <out.smt2>

`abstract-quantifiers.py`'s default map shares one atom between two
quantified subformulas with IDENTICAL TEXT. Its own docstring says that is not
unconditionally sound, because `let` can bind the same name to different values
in two scopes, so identical text can denote different formulas -- and sharing
then STRENGTHENS the skeleton and can manufacture a false `unsat`.

`--fresh-per-occurrence` is the sound extreme: no sharing at all. It is
strictly weaker than any correct sharing, so a `sat` from it does not by itself
refute a shared-map `unsat` -- it only shows the shared map did work the
no-sharing map cannot do.

This instrument is the one that decides between them. It expands every `let`
first, then shares an atom between two quantified subformulas exactly when they
are STRUCTURALLY IDENTICAL AFTER EXPANSION -- at which point no binder remains
that could give one text two meanings, so the sharing is sound. Its verdict is
therefore the admissible one:

    unsat  -> the shared-by-text map's `unsat` was justified after all
    sat    -> the shared-by-text map's `unsat` came from an unsound merge
"""
import sys

sys.setrecursionlimit(200000)


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
    toks, out, i = tokenize(s), [], 0
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
    if x[0] in ('forall', 'exists') and len(x) == 3:
        inner = dict(env)
        for b in x[1]:
            inner.pop(b[0] if isinstance(b, str) else b[0], None)
        return [x[0], x[1], expand_let(x[2], inner)]
    return [expand_let(y, env) for y in x]


def main():
    src, out = sys.argv[1], sys.argv[2]
    fs = read_all(open(src, encoding='utf-8', errors='replace').read())
    atoms, count = {}, [0]

    def go(x):
        if isinstance(x, str):
            return x
        if not x:
            return x
        if x[0] in ('forall', 'exists'):
            k = dump(x)
            if k not in atoms:
                atoms[k] = f'QABS_{len(atoms)}'
            count[0] += 1
            return atoms[k]
        return [go(y) for y in x]

    prefix, bodies = [], []
    for f in fs:
        if isinstance(f, list) and f and f[0] == 'assert':
            bodies.append(go(expand_let(f[1], {})))
        elif isinstance(f, list) and f and f[0] in ('check-sat', 'exit', 'set-info'):
            continue
        else:
            prefix.append(f)
    with open(out, 'w') as fh:
        for p in prefix:
            fh.write(dump(p) + '\n')
        for a in atoms.values():
            fh.write(f'(declare-fun {a} () Bool)\n')
        for b in bodies:
            fh.write(f'(assert {dump(b)})\n')
        fh.write('(check-sat)\n')
    print(f'{out}\toccurrences={count[0]}\tdistinct_atoms={len(atoms)}\tmap=structural-after-let-expansion',
          file=sys.stderr)
    if count[0] == 0:
        sys.exit(3)


main()
