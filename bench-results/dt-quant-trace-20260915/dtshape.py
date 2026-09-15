#!/usr/bin/env python3
"""DT-QUANT-TRACE -- classify an SMT-LIB file by the DATATYPE CONSTRUCT that our
datatype rung refuses, and by the shape of its quantifier bodies.

    dtshape.py <file.smt2> [<file.smt2> ...]        one TSV row per file

Why a parser and not a grep.  The three refusal wordings in
`crates/axeyum-solver/src/datatype_native.rs` are decided by SORTS, not by
names: `register_datatype` (:1514) refuses a field sort that
`field_sort_expands` (:1549) rejects, and `datatype_expansion_is_exact` (:1576)
-- the precondition guarding :904 and :963 -- is "every field sort of every
constructor expands".  Neither predicate is visible in the text of a
`declare-datatypes` form without resolving sort names, so a name-matching
census would be measuring the SPARK naming convention rather than the refusal.

`let` is RESOLVED, NOT EXPANDED.  CLAUDE.md records a lane's `let`-expander
reaching 63.4 GB on this corpus and taking the host down; these files nest
`let` hundreds deep with shared bodies, so substitution is exponential.
Instead each `let` binding's value is walked in place and its construct set is
unioned into the binding NAME, and a name contributes only where it is
REFERENCED.  That is what substitution would have produced for a set-valued
census, at linear cost.  Both readings are emitted -- `reached` (let-resolved,
the brief's unit) and `all` (a plain tree walk, a superset) -- because a census
that reports one number where two readings exist cannot show its own blind spot.
"""

import os
import sys

# ---------------------------------------------------------------- s-expressions


class Sym(str):
    """A symbol, so a quoted `|a b|` is never confused with a 2-element list."""

    __slots__ = ()


def tokenize(text):
    out = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == ';':
            j = text.find('\n', i)
            i = n if j < 0 else j + 1
        elif c in ' \t\r\n':
            i += 1
        elif c in '()':
            out.append(c)
            i += 1
        elif c == '|':
            j = text.find('|', i + 1)
            if j < 0:
                raise ValueError('unterminated |quoted| symbol')
            out.append(Sym(text[i:j + 1]))
            i = j + 1
        elif c == '"':
            j = i + 1
            while j < n:
                if text[j] == '"':
                    if j + 1 < n and text[j + 1] == '"':
                        j += 2
                        continue
                    break
                j += 1
            out.append(Sym(text[i:j + 1]))
            i = j + 1
        else:
            j = i
            while j < n and text[j] not in ' \t\r\n()|;"':
                j += 1
            out.append(Sym(text[i:j]))
            i = j
    return out


def parse(tokens):
    """Iterate top-level forms.  Iterative, never recursive: these files nest
    `let` hundreds deep and a recursive parser dies on the recursion limit
    rather than on the input."""
    stack = []
    for t in tokens:
        if t == '(':
            stack.append([])
        elif t == ')':
            if not stack:
                raise ValueError('unbalanced )')
            done = stack.pop()
            if stack:
                stack[-1].append(done)
            else:
                yield done
        else:
            if stack:
                stack[-1].append(t)
            else:
                yield t


# ---------------------------------------------------------------- sorts

# A sort is normalised to a hashable tuple:
#   ('Bool',) ('Int',) ('Real',) ('BitVec', n) ('Array', dom, rng)
#   ('U', name)   -- declare-sort
#   ('D', name)   -- declare-datatypes
#   ('?', text)   -- anything unresolved; counted and reported, never assumed


def norm_sort(s, datatypes, usorts):
    if isinstance(s, list):
        if len(s) >= 3 and s[0] == '_' and s[1] == 'BitVec':
            return ('BitVec', int(s[2]))
        if s and s[0] == 'Array' and len(s) == 3:
            return ('Array',
                    norm_sort(s[1], datatypes, usorts),
                    norm_sort(s[2], datatypes, usorts))
        return ('?', sexp_head(s))
    if s in ('Bool', 'Int', 'Real'):
        return (str(s),)
    if s in datatypes:
        return ('D', str(s))
    if s in usorts:
        return ('U', str(s))
    return ('?', str(s))


def sexp_head(s):
    while isinstance(s, list) and s:
        s = s[0]
    return str(s) if not isinstance(s, list) else '()'


def sort_mentions_datatype(sort):
    if sort[0] == 'D':
        return True
    if sort[0] == 'Array':
        return sort_mentions_datatype(sort[1]) or sort_mentions_datatype(sort[2])
    return False


def field_sort_expands(sort):
    """`datatype_native.rs:1549` verbatim: Bool/BitVec/Int/Real/uninterpreted
    expand; an Array expands iff it mentions no datatype; everything else --
    `Sort::Datatype` included -- does not."""
    if sort[0] in ('Bool', 'Int', 'Real', 'BitVec', 'U'):
        return True
    if sort[0] == 'Array':
        return not sort_mentions_datatype(sort)
    return False


# ---------------------------------------------------------------- declarations


class Sig:
    """What the file declares, resolved."""

    def __init__(self):
        self.usorts = set()
        # dt name -> [(ctor, [(selector, raw sort)])], raw until every dt is known
        self.dt_raw = {}
        self.dt = {}          # dt name -> [(ctor, [(sel, sort)])]
        self.sel_of = {}      # selector name -> (dt name, field sort)
        self.ctor_of = {}     # constructor name -> dt name
        self.funs = {}        # declare-fun/const name -> (argsorts, ressort)
        self.defs = {}        # define-fun name -> (argsorts, ressort)
        self.unresolved = 0


def read_datatype_decl(form, sig):
    """`(declare-datatypes ((name arity)...) ((ctor...)...))`, the 2.6 form, and
    the legacy `(declare-datatypes () ((name ctor...)...))`."""
    if len(form) != 3:
        return
    decls, bodies = form[1], form[2]
    names = []
    if isinstance(decls, list) and decls:
        for d in decls:
            if isinstance(d, list) and d:
                names.append(str(d[0]))
        for nm, body in zip(names, bodies if isinstance(bodies, list) else []):
            sig.dt_raw[nm] = body
    elif isinstance(bodies, list):
        for body in bodies:                      # legacy: name is body[0]
            if isinstance(body, list) and body:
                sig.dt_raw[str(body[0])] = body[1:]


def resolve(sig):
    """Second pass: every datatype name is known, so field sorts resolve."""
    for nm, body in sig.dt_raw.items():
        ctors = []
        if not isinstance(body, list):
            continue
        for c in body:
            if isinstance(c, list) and c:
                cname = str(c[0])
                fields = []
                for f in c[1:]:
                    if isinstance(f, list) and len(f) >= 2:
                        fs = norm_sort(f[1], sig.dt_raw, sig.usorts)
                        fields.append((str(f[0]), fs))
                        sig.sel_of[str(f[0])] = (nm, fs)
                        if fs[0] == '?':
                            sig.unresolved += 1
                ctors.append((cname, fields))
            else:
                cname = str(c)
                ctors.append((cname, []))
            sig.ctor_of[ctors[-1][0]] = nm
        sig.dt[nm] = ctors


def exact(sig, dtname):
    """`datatype_native.rs:1576`."""
    return all(field_sort_expands(fs)
               for _, fields in sig.dt.get(dtname, [])
               for _, fs in fields)


def register_refuses(sig, dtname, seen=None):
    """`register_datatype` (`datatype_native.rs:1497`) walks INTO a
    `Sort::Datatype` field and refuses any other non-expanding field sort.  So
    W1 fires on `dtname` iff some datatype REACHABLE from it has such a field --
    which is not the same predicate as `exact`, and conflating the two would
    put every nested record in the W1 bucket."""
    if seen is None:
        seen = set()
    if dtname in seen:
        return None
    seen.add(dtname)
    for _, fields in sig.dt.get(dtname, []):
        for _, fs in fields:
            if fs[0] == 'D':
                got = register_refuses(sig, fs[1], seen)
                if got:
                    return got
            elif not field_sort_expands(fs):
                return (dtname, fs)
    return None


# ---------------------------------------------------------------- body census

CONSTRUCTS = (
    'q_dt_binder',        # a quantified variable of datatype sort
    'q_arraydt_binder',   # a quantified variable of an array-of-datatype sort
    'selector',           # a datatype selector application
    'tester',             # (_ is C) or SPARK's `is-C`
    'constructor',        # a constructor application
    'sel_over_dt_array',  # `select` whose array's element sort mentions a dt
    'uf_dt_arg',          # a declare-fun applied to a datatype-sorted argument
    'uf_dt_result',       # a declare-fun whose result sort is a datatype
    'uf_mentions_dt',     # result sort mentions a dt without being one
    'eq_dt',              # `=` over datatype-sorted operands
    'ite_dt',             # `ite` producing a datatype
)


def sort_of(sig, node, env):
    """Best-effort sort of a term.  `None` when unknown -- never guessed."""
    if not isinstance(node, list):
        s = str(node)
        if s in env:
            return env[s]
        if s in sig.funs and not sig.funs[s][0]:
            return sig.funs[s][1]
        if s in sig.defs and not sig.defs[s][0]:
            return sig.defs[s][1]
        if s in sig.ctor_of:
            return ('D', sig.ctor_of[s])
        return None
    if not node:
        return None
    h = node[0]
    if isinstance(h, list):
        return None
    hs = str(h)
    if hs in sig.sel_of:
        return sig.sel_of[hs][1]
    if hs in sig.ctor_of:
        return ('D', sig.ctor_of[hs])
    if hs in sig.funs:
        return sig.funs[hs][1]
    if hs in sig.defs:
        return sig.defs[hs][1]
    if hs == 'ite' and len(node) == 4:
        return sort_of(sig, node[2], env) or sort_of(sig, node[3], env)
    if hs == 'select' and len(node) == 3:
        a = sort_of(sig, node[1], env)
        return a[2] if a and a[0] == 'Array' else None
    if hs == 'store' and len(node) == 4:
        return sort_of(sig, node[1], env)
    return None


def census(sig, root, under_quantifier_only):
    """Walk `root` iteratively.  Returns (reached, allseen) construct->count.

    `reached` resolves `let`: a binding's constructs are attributed to its NAME
    and folded in only where the name is referenced.  `allseen` is the plain
    tree walk.  A fixpoint pass handles a binding referring to an earlier one.
    """
    reached = {k: 0 for k in CONSTRUCTS}
    allseen = {k: 0 for k in CONSTRUCTS}
    binder_sorts = []
    n_forall = 0
    n_exists = 0
    max_depth = 0

    # (node, env, qdepth, sink) -- sink is the dict this node's hits go to.
    letsets = {}          # let-binding name -> dict of construct counts
    work = [(root, {}, 0, None)]
    while work:
        node, env, qd, sink = work.pop()
        max_depth = max(max_depth, qd)

        def hit(kind, k=1):
            allseen[kind] += k
            if sink is not None:
                sink[kind] = sink.get(kind, 0) + k
            elif not under_quantifier_only or qd > 0:
                reached[kind] += k

        if not isinstance(node, list):
            s = str(node)
            if s in letsets:
                for kk, vv in letsets[s].items():
                    allseen[kk] += 0          # already counted in the tree walk
                    if sink is not None:
                        sink[kk] = sink.get(kk, 0) + vv
                    elif not under_quantifier_only or qd > 0:
                        reached[kk] += vv
            elif s in sig.funs and not sig.funs[s][0]:
                rs = sig.funs[s][1]
                if rs[0] == 'D':
                    hit('uf_dt_result')
                elif sort_mentions_datatype(rs):
                    hit('uf_mentions_dt')
            continue
        if not node:
            continue

        h = node[0]
        hs = None if isinstance(h, list) else str(h)

        if hs in ('forall', 'exists') and len(node) == 3:
            if hs == 'forall':
                n_forall += 1
            else:
                n_exists += 1
            env2 = dict(env)
            for b in node[1] if isinstance(node[1], list) else []:
                if isinstance(b, list) and len(b) >= 2:
                    bs = norm_sort(b[1], sig.dt_raw, sig.usorts)
                    env2[str(b[0])] = bs
                    binder_sorts.append(bs)
                    if bs[0] == 'D':
                        hit('q_dt_binder')
                    elif bs[0] == 'Array' and sort_mentions_datatype(bs):
                        hit('q_arraydt_binder')
            work.append((node[2], env2, qd + 1, sink))
            continue

        if hs == 'let' and len(node) == 3:
            env2 = dict(env)
            for b in node[1] if isinstance(node[1], list) else []:
                if isinstance(b, list) and len(b) >= 2:
                    sub = {}
                    # Walk the bound VALUE into its own sink, then register it.
                    inner = census_sub(sig, b[1], env2, letsets, allseen)
                    sub.update(inner[0])
                    letsets[str(b[0])] = sub
                    env2[str(b[0])] = inner[1]
            work.append((node[2], env2, qd, sink))
            continue

        if hs is not None:
            if hs in sig.sel_of:
                hit('selector')
            if hs in sig.ctor_of and len(node) > 1:
                hit('constructor')
            if hs in sig.funs:
                arg, res = sig.funs[hs]
                if res[0] == 'D':
                    hit('uf_dt_result')
                elif sort_mentions_datatype(res):
                    hit('uf_mentions_dt')
                if any(a[0] == 'D' for a in arg):
                    hit('uf_dt_arg')
            if hs == 'select' and len(node) == 3:
                asort = sort_of(sig, node[1], env)
                if asort and asort[0] == 'Array' and sort_mentions_datatype(asort[2]):
                    hit('sel_over_dt_array')
            if hs == '=' and len(node) == 3:
                for side in (node[1], node[2]):
                    s = sort_of(sig, side, env)
                    if s and s[0] == 'D':
                        hit('eq_dt')
                        break
            if hs == 'ite' and len(node) == 4:
                s = sort_of(sig, node[2], env) or sort_of(sig, node[3], env)
                if s and s[0] == 'D':
                    hit('ite_dt')
        elif isinstance(h, list) and len(h) >= 3 and str(h[0]) == '_' and str(h[1]) == 'is':
            hit('tester')

        for c in reversed(node[1:] if hs is not None else node):
            work.append((c, env, qd, sink))

    return reached, allseen, binder_sorts, n_forall, n_exists, max_depth


def census_sub(sig, node, env, letsets, allseen):
    """Walk one `let`-bound value, returning (construct counts, its sort).

    Kept separate from `census` so a binding's hits land in the binding rather
    than at the use site's quantifier depth.  Tree-walk totals still accumulate
    into the shared `allseen`."""
    out = {}
    work = [(node, env)]
    while work:
        nd, ev = work.pop()
        if not isinstance(nd, list):
            s = str(nd)
            if s in letsets:
                for kk, vv in letsets[s].items():
                    out[kk] = out.get(kk, 0) + vv
            continue
        if not nd:
            continue
        h = nd[0]
        hs = None if isinstance(h, list) else str(h)

        def hit(kind):
            out[kind] = out.get(kind, 0) + 1
            allseen[kind] += 1

        if hs is not None:
            if hs in sig.sel_of:
                hit('selector')
            if hs in sig.ctor_of and len(nd) > 1:
                hit('constructor')
            if hs in sig.funs:
                arg, res = sig.funs[hs]
                if res[0] == 'D':
                    hit('uf_dt_result')
                elif sort_mentions_datatype(res):
                    hit('uf_mentions_dt')
                if any(a[0] == 'D' for a in arg):
                    hit('uf_dt_arg')
            if hs == 'select' and len(nd) == 3:
                asort = sort_of(sig, nd[1], ev)
                if asort and asort[0] == 'Array' and sort_mentions_datatype(asort[2]):
                    hit('sel_over_dt_array')
            if hs == '=' and len(nd) == 3:
                for side in (nd[1], nd[2]):
                    s = sort_of(sig, side, ev)
                    if s and s[0] == 'D':
                        hit('eq_dt')
                        break
            if hs == 'ite' and len(nd) == 4:
                s = sort_of(sig, nd[2], ev) or sort_of(sig, nd[3], ev)
                if s and s[0] == 'D':
                    hit('ite_dt')
        elif isinstance(h, list) and len(h) >= 3 and str(h[0]) == '_' and str(h[1]) == 'is':
            hit('tester')
        for c in (nd[1:] if hs is not None else nd):
            work.append((c, ev))
    return out, sort_of(sig, node, env)


# ---------------------------------------------------------------- per file


COLUMNS = [
    'file', 'parse', 'n_dt', 'n_inexact_dt', 'n_w1_dt',
    'w1', 'w1_dt', 'w1_sort', 'w2', 'w3', 'w3_mentions',
    'predicted', 'n_assert', 'n_forall', 'n_exists', 'max_qdepth',
    'dt_binders', 'arraydt_binders',
] + ['r_' + c for c in CONSTRUCTS] + ['a_' + c for c in CONSTRUCTS] + ['unresolved_sorts']


def classify(path):
    row = {c: 'NA' for c in COLUMNS}
    row['file'] = os.path.basename(path)
    try:
        with open(path, 'r', errors='replace') as fh:
            text = fh.read()
        forms = list(parse(tokenize(text)))
    except Exception as exc:                      # noqa: BLE001 -- reported, not raised
        row['parse'] = 'PARSE-FAIL:' + type(exc).__name__
        return row
    row['parse'] = 'OK'

    sig = Sig()
    asserts = []
    for f in forms:
        if not isinstance(f, list) or not f:
            continue
        head = str(f[0]) if not isinstance(f[0], list) else ''
        if head == 'declare-sort' and len(f) >= 2:
            sig.usorts.add(str(f[1]))
        elif head == 'declare-datatypes':
            read_datatype_decl(f, sig)
        elif head == 'assert' and len(f) >= 2:
            asserts.append(f[1])
    resolve(sig)
    for f in forms:
        if not isinstance(f, list) or not f:
            continue
        head = str(f[0]) if not isinstance(f[0], list) else ''
        if head == 'declare-fun' and len(f) >= 4:
            args = [norm_sort(a, sig.dt_raw, sig.usorts)
                    for a in (f[2] if isinstance(f[2], list) else [])]
            sig.funs[str(f[1])] = (args, norm_sort(f[3], sig.dt_raw, sig.usorts))
        elif head == 'declare-const' and len(f) >= 3:
            sig.funs[str(f[1])] = ([], norm_sort(f[2], sig.dt_raw, sig.usorts))
        elif head == 'define-fun' and len(f) >= 4:
            args = [norm_sort(a[1], sig.dt_raw, sig.usorts)
                    for a in (f[2] if isinstance(f[2], list) else [])
                    if isinstance(a, list) and len(a) >= 2]
            sig.defs[str(f[1])] = (args, norm_sort(f[3], sig.dt_raw, sig.usorts))

    row['n_dt'] = len(sig.dt)
    inexact = [d for d in sig.dt if not exact(sig, d)]
    row['n_inexact_dt'] = len(inexact)
    w1hits = [(d, register_refuses(sig, d)) for d in sig.dt]
    w1hits = [(d, r) for d, r in w1hits if r]
    row['n_w1_dt'] = len(w1hits)
    row['w1'] = '1' if w1hits else '0'
    row['w1_dt'] = w1hits[0][1][0] if w1hits else 'NONE'
    row['w1_sort'] = ('/'.join(str(x) for x in w1hits[0][1][1])) if w1hits else 'NONE'

    # W2: a declare-fun with a datatype-sorted ARGUMENT whose dt is inexact.
    # W3: a declare-fun whose RESULT is an inexact datatype; `w3_mentions` is
    #     its sibling arm -- a result sort mentioning a dt without being one.
    w2 = any(a[0] == 'D' and not exact(sig, a[1])
             for arg, _ in sig.funs.values() for a in arg)
    w3 = any(res[0] == 'D' and not exact(sig, res[1]) for _, res in sig.funs.values())
    w3m = any(res[0] != 'D' and sort_mentions_datatype(res)
              for _, res in sig.funs.values())
    row['w2'] = '1' if w2 else '0'
    row['w3'] = '1' if w3 else '0'
    row['w3_mentions'] = '1' if w3m else '0'
    # The FIRST wording `check_with_datatype_native` reaches, in its own order:
    # `register_datatype` runs while the scan builds layouts, before the
    # Ackermann validation loop that holds :904 and :963; and within that loop
    # the result-sort arm (:904) precedes the argument arm (:963).
    row['predicted'] = ('W1' if w1hits else 'W3' if w3
                        else 'W3M' if w3m else 'W2' if w2 else 'NONE')

    reached = {k: 0 for k in CONSTRUCTS}
    allseen = {k: 0 for k in CONSTRUCTS}
    binders, nf, ne, md = [], 0, 0, 0
    for a in asserts:
        r, s, b, f_, e_, d_ = census(sig, a, under_quantifier_only=True)
        for k in CONSTRUCTS:
            reached[k] += r[k]
            allseen[k] += s[k]
        binders += b
        nf += f_
        ne += e_
        md = max(md, d_)
    row['n_assert'] = len(asserts)
    row['n_forall'] = nf
    row['n_exists'] = ne
    row['max_qdepth'] = md
    row['dt_binders'] = sum(1 for b in binders if b[0] == 'D')
    row['arraydt_binders'] = sum(
        1 for b in binders if b[0] == 'Array' and sort_mentions_datatype(b))
    for k in CONSTRUCTS:
        row['r_' + k] = reached[k]
        row['a_' + k] = allseen[k]
    row['unresolved_sorts'] = sig.unresolved
    return row


def main():
    if len(sys.argv) < 2:
        sys.stderr.write(__doc__)
        return 2
    print('\t'.join(COLUMNS))
    bad = 0
    for p in sys.argv[1:]:
        row = classify(p)
        if str(row['parse']) != 'OK':
            bad += 1
        print('\t'.join(str(row[c]) for c in COLUMNS))
    # The exit status depends on the FINDING: a census that could not parse its
    # own subject must not exit 0 (CLAUDE.md, evidence discipline).
    if bad:
        sys.stderr.write(f'PARSE-FAIL on {bad} of {len(sys.argv) - 1} files\n')
        return 3
    return 0


if __name__ == '__main__':
    sys.exit(main())
