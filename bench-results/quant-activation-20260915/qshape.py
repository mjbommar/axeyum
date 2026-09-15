#!/usr/bin/env python3
"""QUANT-ACTIVATION -- classify an SMT-LIB file by the QUANTIFIER SHAPE that
decides whether `prove_unsat_by_mbqi_inner`'s five guards divert it to
e-matching, and whether e-matching then holds a POSITIVELY OCCURRING universal
that is not a unit assertion -- the `rej_nocontext` shape ADR-2113 measured at
100.0 % of 2,139,815 rejections.

    qshape.py <file.smt2> [<file.smt2> ...]     one TSV row per file
    qshape.py --from-list <list-of-paths>

WHY A PARSER AND NOT A GREP.  The guards in `auto.rs` (`prove_unsat_by_mbqi_inner`)
are decided by the TERM TREE, not by text: `nested-binder-in-matrix` is "strip
the whole `forall` prefix, does the matrix still hold a quantifier", and
`quantifier-below-top-level` is "this assertion's ROOT is not a `forall` and it
holds a quantifier somewhere".  A file with `(assert (forall ((x Int)) (or ...
(forall ...))))` and a file with `(assert (or P (forall ...)))` both "contain a
nested forall" to a grep and land in DIFFERENT guards here.

WHY POLARITY.  `(assert (not (forall x. B)))` is an EXISTENTIAL -- skolemized,
not instantiated, and not this lane's subject.  Counting it as a nested
universal would inflate the ceiling with the one shape activation cannot reach.
Polarity is tracked through `not`, `=>` (antecedent flips), `and`, `or`, and
`ite` (branches keep polarity, the CONDITION is bipolar, as are the arguments
of a Bool `=` and of `xor`/`distinct`).  A bipolar occurrence is counted on
BOTH sides, which is conservative in the direction that matters: it can only
make the universal column larger, so a SMALL universal count is a strong
negative and a large one is an upper bound.  Both are reported.

`let` IS RESOLVED, NOT EXPANDED.  CLAUDE.md records a lane's `let`-expander
reaching 63.4 GB on this corpus and taking the host down; these files nest
`let` hundreds deep with shared bodies, so substitution is exponential.  A
`let` binding's value is walked in place at the polarity of its reference site,
memoised on (binding identity, polarity, unit flag, binder flag), so the cost
is linear in the term DAG rather than in its tree unfolding.

THE COUNTS ARE OVER THE DAG, NOT THE UNFOLDED TREE, and this was a real defect
before it was a design note.  The first version SUMMED a `let`-bound value's
findings at every reference site -- the count substitution would have produced.
On one `UFNIA` file that column came back as a 105-DIGIT INTEGER: the sharing in
this corpus is exponential, so a tree count is not a quantity anyone can read
and a per-division SUM of them is meaningless.  Each class is now a SET of
`forall` node identities, so a universal shared under twenty `let` references
is one universal, which is what it is in the arena the solver builds.

EVERY COUNT IS EMITTED, NEVER A SINGLE LABEL.  Sizing a bucket by its label is
how a census reports one cause where the raw columns hold four.
"""

import sys

MAX_TOKENS = 40_000_000   # a file past this is REPORTED, never silently skipped


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
                raise ValueError('unterminated-quoted-symbol')
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
        if len(out) > MAX_TOKENS:
            raise ValueError('token-budget-exceeded')
    return out


def parse_forms(tokens):
    """Iterate top-level forms.  ITERATIVE, never recursive: these files nest
    `let` hundreds deep and a recursive parser dies on the interpreter's stack
    before it reaches the first assertion."""
    stack = []
    for t in tokens:
        if t == '(':
            stack.append([])
        elif t == ')':
            if not stack:
                raise ValueError('unbalanced-close')
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
    if stack:
        raise ValueError('unbalanced-open')


BINDERS = ('forall', 'exists')

# The six classes.  Each is a SET of `forall`/`exists` NODE IDENTITIES, so a
# binder shared under twenty `let` references is one binder -- which is what it
# is in the arena the solver builds.  A node reached at two polarities lands in
# two classes, and that is a real fact about the file, not double counting.
#
#   pos_forall_unit      positive forall reachable through `and` only, no binder above
#   pos_forall_split     positive forall NOT reachable through `and` only, no binder
#                        above -- THE `rej_nocontext` SHAPE
#   forall_under_binder  any forall (either polarity) inside another binder's body
#   exists_pos           positive exists / negative forall (skolem territory)
#   any_quant            any binder node at all
#   multi_binder_unit    a unit-position forall whose prefix binds >= 2 variables
#
# and the two that split `pos_forall_split` by what the SHIPPED whitelist does
# with it.  `PositiveContext`'s doc requires EVERY path step to be a `BoolAnd`
# or `BoolOr` argument, so:
#   split_whitelisted    path is `and`/`or` only -- a context IS computed today
#                        and the tuple is handed off, not dropped
#   split_refused        the path crosses a `not`, a `=>`, an `ite` branch or a
#                        boolean `=`/`xor` -- `context: None`, and every matched
#                        tuple is dropped as `rej_nocontext`.  THIS is the
#                        lever's target, and the two columns are reported apart
#                        because a single "split" number cannot tell a shape the
#                        engine already handles from one it throws away.
CLASSES = ('pos_forall_unit', 'pos_forall_split', 'forall_under_binder',
           'exists_pos', 'any_quant', 'multi_binder_unit',
           'split_whitelisted', 'split_refused')


class Walker:
    def __init__(self):
        self.memo = set()
        self.found = {c: set() for c in CLASSES}

    def _mark(self, cls, node):
        self.found[cls].add(id(node))

    def walk(self, node, env, pol, unit, under_binder, wl=True):
        """`pol` in (+1, -1, 0=bipolar); `unit` stays True while the node is
        still reachable from the assertion root through `and` alone at positive
        polarity; `wl` stays True while every step so far has been a `BoolAnd`
        or `BoolOr` argument, which is exactly the shipped `PositiveContext`
        whitelist.  Findings accumulate into `self.found`; the memo records only
        that a (node, position) pair has already been walked, so the cost is
        linear in the DAG and never in its tree unfolding."""
        key = (id(node), pol, unit, under_binder, wl)
        if key in self.memo:
            return
        self.memo.add(key)
        if not isinstance(node, list):
            b = env.get(node)
            if b is not None:
                self.walk(b[0], b[1], pol, unit, under_binder, wl)
            return
        if not node:
            return
        head = node[0]
        if isinstance(head, list):
            for a in node:
                self.walk(a, env, 0, False, under_binder, False)
            return
        if head in BINDERS:
            if len(node) < 3:
                return
            nvars = len(node[1]) if isinstance(node[1], list) else 1
            self._mark('any_quant', node)
            is_forall = (head == 'forall')
            positive = pol in (1, 0)   # bipolar counts on BOTH sides, deliberately
            if is_forall and positive:
                if under_binder:
                    self._mark('forall_under_binder', node)
                elif unit:
                    self._mark('pos_forall_unit', node)
                    if nvars >= 2:
                        self._mark('multi_binder_unit', node)
                else:
                    self._mark('pos_forall_split', node)
                    self._mark('split_whitelisted' if wl else 'split_refused', node)
            elif is_forall:
                if under_binder:
                    self._mark('forall_under_binder', node)
                else:
                    self._mark('exists_pos', node)   # a negative forall IS an exists
            elif positive:
                self._mark('exists_pos', node)
            self.walk(node[2], env, pol, False, True, False)
            return
        if head == 'let':
            if len(node) < 3:
                return
            env2 = dict(env)
            for binding in node[1]:
                if isinstance(binding, list) and len(binding) == 2:
                    env2[binding[0]] = (binding[1], env)
            # A `let` is not a term node on the Rust side -- the arena holds the
            # substituted body -- so it is not a path step and does not leave
            # the whitelist.
            self.walk(node[2], env2, pol, unit, under_binder, wl)
            return
        if head == 'not':
            for a in node[1:]:
                self.walk(a, env, -pol, False, under_binder, False)
            return
        if head == 'and':
            for a in node[1:]:
                self.walk(a, env, pol, unit and pol == 1, under_binder, wl)
            return
        if head == 'or':
            for a in node[1:]:
                self.walk(a, env, pol, False, under_binder, wl)
            return
        if head == '=>':
            for a in node[1:-1]:
                self.walk(a, env, -pol, False, under_binder, False)
            if len(node) >= 2:
                self.walk(node[-1], env, pol, False, under_binder, False)
            return
        if head == 'ite':
            if len(node) >= 2:
                self.walk(node[1], env, 0, False, under_binder, False)
            for a in node[2:]:
                self.walk(a, env, pol, False, under_binder, False)
            return
        if head == '!':
            # An annotation: the first argument keeps position, the rest are
            # attributes (`:pattern`, `:named`) and are walked bipolar.
            if len(node) > 1:
                self.walk(node[1], env, pol, unit, under_binder, wl)
            for a in node[2:]:
                self.walk(a, env, 0, False, under_binder, False)
            return
        for a in node[1:]:
            self.walk(a, env, 0, False, under_binder, False)


def has_quant(node, env):
    """Plain existence of any binder, `let`-resolved.  Polarity-blind, exactly
    as `has_quantifier` is on the Rust side."""
    seen = set()
    stack = [(node, env)]
    while stack:
        n, e = stack.pop()
        if isinstance(n, list):
            if n and not isinstance(n[0], list):
                if n[0] in BINDERS:
                    return True
                if n[0] == 'let' and len(n) >= 3:
                    e2 = dict(e)
                    for b in n[1]:
                        if isinstance(b, list) and len(b) == 2:
                            e2[b[0]] = (b[1], e)
                    stack.append((n[2], e2))
                    continue
            for a in n:
                stack.append((a, e))
        else:
            b = e.get(n)
            if b is not None and id(b[0]) not in seen:
                seen.add(id(b[0]))
                stack.append(b)
    return False


def _resolve_head(cur, cenv):
    """Follow `let` references and `let` bodies down to the first real node."""
    guard = 0
    while True:
        guard += 1
        if guard > 100000:
            return cur, cenv
        if not isinstance(cur, list):
            b = cenv.get(cur)
            if b is None:
                return cur, cenv
            cur, cenv = b
            continue
        if cur and cur[0] == 'let' and len(cur) >= 3:
            e2 = dict(cenv)
            for b in cur[1]:
                if isinstance(b, list) and len(b) == 2:
                    e2[b[0]] = (b[1], cenv)
            cur, cenv = cur[2], e2
            continue
        return cur, cenv


def strip_forall_prefix(node, env):
    """Mirror the prefix peel in `prove_unsat_by_mbqi_inner`: peel `Forall`
    nodes off the ROOT.  Returns (prefix_len, matrix, matrix_env, arity_ok)."""
    prefix = 0
    cur, cenv = _resolve_head(node, env)
    while isinstance(cur, list) and cur and cur[0] == 'forall':
        if len(cur) != 3:
            return prefix, cur, cenv, False
        prefix += len(cur[1]) if isinstance(cur[1], list) else 1
        cur, cenv = _resolve_head(cur[2], cenv)
    return prefix, cur, cenv, True


def predict_mbqi_exit(asserts, env0):
    """Simulate `prove_unsat_by_mbqi_inner`'s five guards IN ORDER.  The first
    that fires is what `mbqi_shape_probe` prints."""
    saw_top_universal = False
    multi = False
    for a in asserts:
        cur, cenv = _resolve_head(a, env0)
        if isinstance(cur, list) and cur and cur[0] == 'forall':
            plen, matrix, menv, ok = strip_forall_prefix(cur, cenv)
            if not ok:
                return 'forall-arity'
            if has_quant(matrix, menv):
                return 'nested-binder-in-matrix'
            if plen != 1:
                multi = True
            saw_top_universal = True
        elif has_quant(cur, cenv):
            return 'quantifier-below-top-level'
    if not saw_top_universal:
        return 'no-top-level-universal'
    if multi:
        return 'multi-binder-prefix'
    return 'refutation-loop'


COLS = ('file', 'status', 'asserts', 'pos_forall_unit', 'pos_forall_split',
        'split_whitelisted', 'split_refused', 'forall_under_binder',
        'exists_pos', 'any_quant', 'multi_binder_unit',
        'mbqi_exit_pred', 'activation_target', 'widen_target')


def _na(path, status, asserts='NA'):
    row = {c: 'NA' for c in COLS}
    row['file'] = path
    row['status'] = status
    row['asserts'] = asserts
    return row


def classify(path):
    try:
        with open(path, 'r', errors='replace') as fh:
            text = fh.read()
        toks = tokenize(text)
    except (OSError, ValueError) as exc:
        return _na(path, 'PARSE-FAIL:%s' % (exc if isinstance(exc, ValueError) else type(exc).__name__))
    asserts = []
    try:
        for form in parse_forms(toks):
            if isinstance(form, list) and len(form) >= 2 and form[0] == 'assert':
                asserts.append(form[1])
    except ValueError as exc:
        return _na(path, 'PARSE-FAIL:%s' % exc)
    env0 = {}
    walker = Walker()
    try:
        for a in asserts:
            walker.walk(a, env0, 1, True, False)
        exit_pred = predict_mbqi_exit(asserts, env0)
    except RecursionError:
        return _na(path, 'RECURSION-OVERFLOW', len(asserts))
    except MemoryError:
        return _na(path, 'MEMORY', len(asserts))
    n = {c: len(walker.found[c]) for c in CLASSES}
    # The activation target: a positively occurring universal that the
    # e-matching loop compiles as a NON-UNIT registration -- either below a
    # disjunction at the top level, or inside another binder's matrix.  Both are
    # shapes whose instances are admissible only under an assignment.
    target = 1 if (n['pos_forall_split'] + n['forall_under_binder']) > 0 else 0
    # The narrower, honest one: a universal the SHIPPED whitelist refuses a
    # context for, so its tuples are dropped outright today.  `activation_target`
    # is the shape ceiling; `widen_target` is what this lane's lever can reach.
    widen = 1 if n['split_refused'] > 0 else 0
    row = dict(file=path, status='OK', asserts=len(asserts),
               mbqi_exit_pred=exit_pred, activation_target=target,
               widen_target=widen)
    row.update(n)
    return row


def main(argv):
    args = argv[1:]
    if not args:
        sys.stderr.write('usage: qshape.py [--from-list <list>] <file.smt2> ...\n')
        return 2
    if args[0] == '--from-list':
        with open(args[1]) as fh:
            paths = [line.strip() for line in fh if line.strip()]
    else:
        paths = args
    sys.stdout.write('\t'.join(COLS) + '\n')
    for p in paths:
        row = classify(p)
        sys.stdout.write('\t'.join(str(row[c]) for c in COLS) + '\n')
        sys.stdout.flush()
    return 0


if __name__ == '__main__':
    sys.setrecursionlimit(20000)
    sys.exit(main(sys.argv))
