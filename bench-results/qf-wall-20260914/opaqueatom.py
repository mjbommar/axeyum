#!/usr/bin/env python3
"""QF-WALL -- simulate the proposed lever OUTSIDE the solver, before building it.

    opaqueatom.py <in.smt2> <out.smt2> [--report]

`ArithAbstractor::abstract_term` (crates/axeyum-solver/src/dpll_lia.rs) calls
`ensure_supported_atom` on every atom and, when that says the atom is outside
the linear fragment, returns `Err(Unsupported)` -- which refuses the WHOLE
QUERY.  The proposed lever is to allocate a fresh opaque Boolean proposition
for such an atom instead and carry on, which is a weakening (sound for `unsat`,
and `sat` must be downgraded to `unknown`, exactly as `check_with_lia_opaque_
apps` already does on the integer side).

This script produces the query that lever would hand the Boolean skeleton:

  * an atom whose leaves are numerals and NULLARY arithmetic symbols is LEFT
    ALONE -- the theory still sees it;
  * every other atom (a UF application, an array `select`, an equality over an
    uninterpreted sort, a non-linear product) becomes one fresh `Bool`, shared
    by structural identity after `let`-expansion.

It is deliberately CONSERVATIVE about what the linearizer accepts: `lra.rs`'s
`linearize` handles RealAdd/RealSub/RealNeg and RealMul with a constant factor,
and the integer mirror the same, so those and nothing else are kept.  Being
conservative can only UNDERSTATE what the lever buys.

Running the result through axeyum answers "would the lever convert this row?"
without writing the lever -- and if the answer is no, that is found for the
price of a script.
"""
import sys

sys.setrecursionlimit(200000)

CONNECTIVES = {'not', 'and', 'or', '=>', 'xor', 'ite', 'true', 'false', '!'}
CMP = {'<', '<=', '>', '>=', '='}
ARITH = {'+', '-', '*', '/'}


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
    return [expand_let(y, env) for y in x]


def numeral(s):
    t = s[1:] if s.startswith('-') else s
    return t.replace('.', '', 1).isdigit()


def main():
    src, out = sys.argv[1], sys.argv[2]
    fs = read_all(open(src, encoding='utf-8', errors='replace').read())
    arith_const = set()   # nullary symbols of sort Int/Real
    bool_const = set()
    prefix, bodies = [], []
    for f in fs:
        if isinstance(f, list) and f and f[0] == 'declare-fun' and isinstance(f[2], list) \
                and not f[2]:
            if f[3] in ('Int', 'Real'):
                arith_const.add(f[1])
            elif f[3] == 'Bool':
                bool_const.add(f[1])
        if isinstance(f, list) and f and f[0] == 'assert':
            bodies.append(f[1])
        elif isinstance(f, list) and f and f[0] in ('check-sat', 'exit', 'get-unsat-core'):
            continue
        else:
            prefix.append(f)

    def linearizable(t):
        """Exactly what `lra.rs::linearize` accepts, and nothing more."""
        if isinstance(t, str):
            return numeral(t) or t in arith_const
        if not t:
            return False
        h = t[0]
        if h == '-' and len(t) == 2:
            return linearizable(t[1])
        if h in ('+', '-') and len(t) >= 3:
            return all(linearizable(a) for a in t[1:])
        if h == '*' and len(t) == 3:
            a, b = t[1], t[2]
            ca, cb = isinstance(a, str) and numeral(a), isinstance(b, str) and numeral(b)
            return (ca and linearizable(b)) or (cb and linearizable(a))
        if h == '/' and len(t) == 3:
            return isinstance(t[2], str) and numeral(t[2]) and linearizable(t[1])
        return False

    atoms, kept, opaqued = {}, [0], [0]

    def go(x):
        if isinstance(x, str):
            if x in ('true', 'false') or x in bool_const:
                return x
            return atoms.setdefault(x, f'OATOM_{len(atoms)}')
        if not x:
            return atoms.setdefault(dump(x), f'OATOM_{len(atoms)}')
        h = x[0]
        if isinstance(h, str) and h in CONNECTIVES:
            if h == '!':
                return go(x[1])
            return [h] + [go(y) for y in x[1:]]
        if isinstance(h, str) and h in CMP and all(linearizable(a) for a in x[1:]):
            kept[0] += 1
            return x
        opaqued[0] += 1
        return atoms.setdefault(dump(x), f'OATOM_{len(atoms)}')

    newb = [go(expand_let(b, {})) for b in bodies]
    with open(out, 'w') as fh:
        for p in prefix:
            # Keep the source logic verbatim. Rewriting it to `ALL` made
            # cvc5 refuse these files outright: `ALL` carries transcendental
            # theory symbols (`exp`, `log`) that these benchmarks legally
            # DECLARE, and cvc5 rejects a declaration that shadows a theory
            # symbol in scope. The authority check then measured the rewrite
            # rather than the query.
            fh.write(dump(p) + '\n')
        for a in sorted(atoms.values(), key=lambda s: int(s.split('_')[1])):
            fh.write(f'(declare-fun {a} () Bool)\n')
        for b in newb:
            fh.write(f'(assert {dump(b)})\n')
        fh.write('(check-sat)\n')
    print(f'{out}\tatoms_kept={kept[0]}\tatoms_opaqued={opaqued[0]}\tfresh_bools={len(atoms)}',
          file=sys.stderr)


main()
