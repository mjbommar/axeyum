#!/usr/bin/env python3
"""QF-WALL -- replace every THEORY ATOM by an opaque Boolean constant.

    propabstract.py <in.smt2> <out.smt2>

This is the strictly harder question than the quantifier skeleton.  The
quantifier skeleton still hands a solver real arithmetic, array and UF atoms.
This hands it NOTHING but propositional structure: `let` is expanded by
substitution, and every maximal non-Boolean-connective subformula becomes one
Bool constant, SHARED by structural identity after let-expansion.

If the result is still `unsat`, the refutation needs NO theory solver of any
kind -- it is propositional resolution over shared atoms, and any SAT solver
decides it.  That is a claim about the BENCHMARK, checkable by any solver.

Sharing by structure after let-expansion is sound here in a way that sharing by
raw TEXT is not: two occurrences that are structurally identical AFTER every
`let` has been substituted away denote the same term, because there is no
binder left that could give the same text two meanings.  (The files reduced
here are quantifier-free by construction, so no quantifier binder remains
either.)  Abstraction is otherwise a weakening, so `abstract unsat` entails
`concrete unsat`; the converse is not claimed.

Prints the atom count and, when the abstraction is unsat, that is the finding.
"""
import sys

sys.setrecursionlimit(200000)

CONNECTIVES = {'not', 'and', 'or', '=>', 'xor', 'true', 'false'}


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
    if isinstance(x, str):
        return x
    return '(' + ' '.join(dump(y) for y in x) + ')'


def expand_let(x, env):
    """Substitute every `let` binding away.  Bindings are sequential-scoped
    per SMT-LIB `let` semantics: all right-hand sides are evaluated in the
    OUTER env, then bound simultaneously."""
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
            inner.pop(b[0], None)
        return [x[0], x[1], expand_let(x[2], inner)]
    return [expand_let(y, env) for y in x]


def is_bool_eq(x):
    """`=`/`ite` are Boolean CONNECTIVES only when an operand is visibly Bool."""
    for a in x[1:]:
        if a in ('true', 'false'):
            return True
        if isinstance(a, list) and a and a[0] in CONNECTIVES:
            return True
    return False


def abstract(x, atoms):
    if isinstance(x, str):
        if x in ('true', 'false'):
            return x
        return atoms.setdefault(x, f'PABS_{len(atoms)}')
    if not x:
        return atoms.setdefault(dump(x), f'PABS_{len(atoms)}')
    h = x[0]
    if isinstance(h, str) and h in CONNECTIVES:
        return [h] + [abstract(y, atoms) for y in x[1:]]
    if isinstance(h, str) and h in ('=', 'ite', 'distinct') and is_bool_eq(x):
        return [h] + [abstract(y, atoms) for y in x[1:]]
    return atoms.setdefault(dump(x), f'PABS_{len(atoms)}')


def main():
    src, out = sys.argv[1], sys.argv[2]
    fs = read_all(open(src, encoding='utf-8', errors='replace').read())
    atoms = {}
    bodies = []
    for f in fs:
        if isinstance(f, list) and f and f[0] == 'assert':
            bodies.append(abstract(expand_let(f[1], {}), atoms))
    with open(out, 'w') as fh:
        fh.write('(set-logic QF_UF)\n')
        for a in sorted(atoms.values(), key=lambda s: int(s.split('_')[1])):
            fh.write(f'(declare-fun {a} () Bool)\n')
        for b in bodies:
            fh.write(f'(assert {dump(b)})\n')
        fh.write('(check-sat)\n')
    print(f'{out}\tasserts={len(bodies)}\tatoms={len(atoms)}', file=sys.stderr)


main()
