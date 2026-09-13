#!/usr/bin/env python3
"""How is the OUTER array of a nested array sort actually used?

Sizing instrument for the design alternative that needs no `Sort` change at
all: an array of arrays `(Array I1 (Array I2 E))` is a function
`I1 -> (Array I2 E)`, and this solver ALREADY decides array-valued uninterpreted
function results (ADR-0084/0092/0093; probes `q1`-`q3` in `probes/`). Currying
the outer level therefore lands on a route that exists -- but only for the
syntactic positions currying can express.

For every outer-array-sorted term occurrence this classifies the position:

    select   (select X i)              -> a UF application.  EXPRESSIBLE.
    store    (store X i v)             -> a fresh UF plus the two ROW
                                          constraints.  EXPRESSIBLE.
    eq       (= X Y) / (distinct X Y)  -> outer extensionality.  NOT expressible
                                          without a Skolem index; counted, not
                                          assumed away.
    binder   a quantified variable of outer-array sort  -> a second-order
                                          quantifier after currying.  NOT
                                          expressible.
    arg      an argument of some other application       -> NOT expressible.
    other    anything else                               -> NOT expressible.

A file is CURRYABLE when every outer occurrence is `select` or `store`.

The sort discipline here is deliberately partial: it seeds the outer-array set
from declarations, `define-fun` bodies, `let` bindings and binders, and
propagates through `store`/`ite`/`let`. It does NOT do full inference. Every
construct it cannot follow is counted as `other` -- i.e. it can only ever call a
file LESS curryable than it is, never more. That direction is the point: this
number is a LOWER bound on what currying reaches, and an over-estimate would be
the failure mode that matters.

Usage: outer-use-census.py <file-list> [--per-file]
"""
import collections
import re
import sys

TOK = re.compile(r'\(|\)|[^\s()]+')


def strip_comments(text):
    out = []
    in_str = in_qsym = False
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if in_str:
            out.append(c)
            if c == '"':
                in_str = False
            i += 1
        elif in_qsym:
            out.append(c)
            if c == '|':
                in_qsym = False
            i += 1
        elif c == '"':
            in_str = True
            out.append(c)
            i += 1
        elif c == '|':
            in_qsym = True
            out.append(c)
            i += 1
        elif c == ';':
            while i < n and text[i] != '\n':
                i += 1
        else:
            out.append(c)
            i += 1
    return ''.join(out)


def sexprs(text):
    stack, cur = [], []
    for m in TOK.finditer(text):
        t = m.group(0)
        if t == '(':
            stack.append(cur)
            cur = []
        elif t == ')':
            if not stack:
                continue
            done, cur = cur, stack.pop()
            cur.append(done)
        else:
            cur.append(t)
    return cur


def resolve(sort, aliases, depth=0):
    if depth > 40:
        return sort
    if isinstance(sort, str) and sort in aliases:
        return resolve(aliases[sort], aliases, depth + 1)
    return sort


def is_array_sort(sort, aliases):
    s = resolve(sort, aliases)
    return isinstance(s, list) and len(s) == 3 and s[0] == 'Array'


def is_nested_array_sort(sort, aliases):
    """`(Array A B)` where A or B is itself an array sort."""
    s = resolve(sort, aliases)
    if not (isinstance(s, list) and len(s) == 3 and s[0] == 'Array'):
        return False
    return is_array_sort(s[1], aliases) or is_array_sort(s[2], aliases)


class Scan:
    def __init__(self):
        self.aliases = {}
        self.outer = set()       # symbol names of outer-array sort
        self.hits = collections.Counter()

    def note_decl(self, name, sort):
        if is_nested_array_sort(sort, self.aliases):
            self.outer.add(name)

    def is_outer_term(self, t, env):
        """True when `t` denotes a term of nested-array sort, as far as this
        partial discipline can tell."""
        if isinstance(t, str):
            return t in env or t in self.outer
        if not t:
            return False
        h = t[0]
        if h == 'store' and len(t) == 4:
            return self.is_outer_term(t[1], env)
        if h == 'ite' and len(t) == 4:
            return self.is_outer_term(t[2], env) or self.is_outer_term(t[3], env)
        if h == 'as' and len(t) == 3:
            return is_nested_array_sort(t[2], self.aliases)
        return False

    def walk(self, t, env, pos):
        """Classify occurrences. `pos` is the syntactic role of `t`."""
        if isinstance(t, str):
            if t in env or t in self.outer:
                self.hits[pos] += 1
            return
        if not t:
            return
        h = t[0] if isinstance(t[0], str) else None

        if h in ('forall', 'exists') and len(t) == 3 and isinstance(t[1], list):
            env2 = set(env)
            for b in t[1]:
                if isinstance(b, list) and len(b) == 2:
                    if is_nested_array_sort(b[1], self.aliases):
                        env2.add(b[0])
                        self.hits['binder'] += 1
                    else:
                        env2.discard(b[0])
            self.walk(t[2], env2, 'other')
            return

        if h == 'let' and len(t) == 3 and isinstance(t[1], list):
            env2 = set(env)
            for b in t[1]:
                if isinstance(b, list) and len(b) == 2:
                    self.walk(b[1], env, 'letbind')
                    if self.is_outer_term(b[1], env):
                        env2.add(b[0])
                    else:
                        env2.discard(b[0])
            self.walk(t[2], env2, 'other')
            return

        if h == 'select' and len(t) == 3:
            self.walk(t[1], env, 'select')
            self.walk(t[2], env, 'other')
            return

        if h == 'store' and len(t) == 4:
            self.walk(t[1], env, 'store')
            self.walk(t[2], env, 'other')
            self.walk(t[3], env, 'other')
            return

        if h in ('=', 'distinct'):
            role = 'eq' if any(self.is_outer_term(a, env) for a in t[1:]) else 'other'
            for a in t[1:]:
                self.walk(a, env, role)
            return

        if h == 'ite' and len(t) == 4:
            self.walk(t[1], env, 'other')
            self.walk(t[2], env, pos)
            self.walk(t[3], env, pos)
            return

        # Any other application: its arguments are in an unexpressible position.
        for a in t[1:] if h else t:
            self.walk(a, env, 'arg')


def scan_file(path):
    try:
        text = strip_comments(open(path, errors='replace').read())
    except OSError:
        return None
    s = Scan()
    cmds = sexprs(text)
    for cmd in cmds:
        if not isinstance(cmd, list) or not cmd:
            continue
        k = cmd[0]
        if k == 'define-sort' and len(cmd) == 4 and cmd[2] == []:
            s.aliases[cmd[1]] = cmd[3]
        elif k == 'declare-const' and len(cmd) == 3:
            s.note_decl(cmd[1], cmd[2])
        elif k in ('declare-fun',) and len(cmd) == 4 and cmd[2] == []:
            s.note_decl(cmd[1], cmd[3])
        elif k == 'define-fun' and len(cmd) == 5 and cmd[2] == []:
            s.note_decl(cmd[1], cmd[3])
    for cmd in cmds:
        if not isinstance(cmd, list) or not cmd:
            continue
        if cmd[0] == 'assert' and len(cmd) == 2:
            s.walk(cmd[1], set(), 'other')
        elif cmd[0] == 'define-fun' and len(cmd) == 5:
            s.walk(cmd[4], set(), 'other')
    return s.hits


BAD = ('eq', 'binder', 'arg', 'other', 'letbind')


def main():
    listing = '--per-file' in sys.argv
    paths = [ln.strip() for ln in open(sys.argv[1]) if ln.strip()]
    tot = collections.Counter()
    curryable = 0
    nonempty = 0
    blockers = collections.Counter()
    for p in paths:
        h = scan_file(p)
        if h is None:
            continue
        if not h:
            continue
        nonempty += 1
        tot.update(h)
        bad = [k for k in BAD if h.get(k)]
        if not bad:
            curryable += 1
        else:
            blockers[','.join(bad)] += 1
        if listing:
            print(('CURRYABLE' if not bad else 'BLOCKED   ' + ','.join(bad)), p)
    print(f"files with an outer-array occurrence: {nonempty} of {len(paths)}")
    print(f"CURRYABLE (every occurrence is select/store): {curryable}"
          f"  ({100.0 * curryable / nonempty if nonempty else 0:.1f}%)")
    print("occurrence positions, summed over files:")
    for k, v in tot.most_common():
        print(f"   {k:8s} {v}")
    print("blocking position sets:")
    for k, v in blockers.most_common(8):
        print(f"   {v:7d}  {k}")


main()
