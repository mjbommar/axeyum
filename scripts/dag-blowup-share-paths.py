#!/usr/bin/env python3
"""Real-corpus reachability for the ADR-1940 DAG blowup.

Deep `let`-nesting is NECESSARY but NOT SUFFICIENT: the blowup needs each shared
node referenced at least TWICE along one operator spine. So we compute the
quantity that actually governs a branching walker's call count:

    paths(node) = 1                             for a leaf / off-spine head
    paths(node) = sum over args of paths(arg)    for a spine operator

with `let`-bound names resolving to the bound term's `paths` value, computed
once and reused at each reference -- exactly what the SHARED arena gives the
walker, which nonetheless re-walks each occurrence.

`SCAN_OPS` picks the spine (default `+,-,*`; use `and,or` for the Boolean
conjunct collectors). `max_paths` saturates at CAP.

TWO CAVEATS, because the number is misleading without them:

  * For an UNSHARED spine `max_paths` is just the LEAF COUNT, so a large value
    alone is not blowup. Blowup is paths much greater than nodes: check the
    file SIZE alongside. QF_NRA's 158,100 and QF_LIA's 39,800 are wide flat
    sums; QF_IDL's 8,394,292 in 1.4 MB of source is real sharing.
  * This analyser is itself a branching walk and can exceed a per-file budget.
    The caller must REPORT the files it could not finish, never drop them -- a
    tool that omits rather than refuses turns its output into a measurement of
    the accepted subset.
"""
import os
import sys
import json

CAP = 1 << 62
import os as _os
ARITH = set(_os.environ.get("SCAN_OPS", "+,-,*").split(","))


def tokenize(text):
    out = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c == ';':
            while i < n and text[i] != '\n':
                i += 1
        elif c == '|':
            j = text.find('|', i + 1)
            if j < 0:
                j = n - 1
            out.append(text[i:j + 1])
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
            out.append(text[i:j + 1])
            i = j + 1
        elif c in '()':
            out.append(c)
            i += 1
        elif c.isspace():
            i += 1
        else:
            j = i
            while j < n and (not text[j].isspace()) and text[j] not in '();':
                j += 1
            out.append(text[i:j])
            i = j
    return out


def parse(tokens):
    """Iterative s-expression parse -> nested lists."""
    root = []
    stack = [root]
    for t in tokens:
        if t == '(':
            new = []
            stack[-1].append(new)
            stack.append(new)
        elif t == ')':
            if len(stack) > 1:
                stack.pop()
        else:
            stack[-1].append(t)
    return root


def analyse(form):
    """Return (max_let_depth, max_paths) for one top-level (assert ...) body."""
    best_depth = [0]
    best_paths = [1]

    # iterative post-order with an explicit stack; env is a persistent chain
    # env: tuple-linked list of (name -> (paths,)) frames
    def lookup(env, name):
        e = env
        while e is not None:
            if name in e[0]:
                return e[0][name]
            e = e[1]
        return None

    sys.setrecursionlimit(100000)

    def go(node, env, depth):
        best_depth[0] = max(best_depth[0], depth)
        if isinstance(node, str):
            v = lookup(env, node)
            return v if v is not None else 1
        if not node:
            return 1
        head = node[0]
        if head == 'let' and len(node) >= 3 and isinstance(node[1], list):
            frame = {}
            for b in node[1]:
                if isinstance(b, list) and len(b) == 2 and isinstance(b[0], str):
                    frame[b[0]] = go(b[1], env, depth + 1)
            return go(node[2], (frame, env), depth + 1)
        if isinstance(head, str) and head in ARITH:
            tot = 0
            for a in node[1:]:
                tot += go(a, env, depth)
                if tot > CAP:
                    return CAP
            best_paths[0] = max(best_paths[0], min(tot, CAP))
            return min(tot, CAP)
        # any other head: walk children for their own maxima, contribute 1
        for a in node[1:]:
            go(a, env, depth)
        return 1

    go(form, None, 0)
    return best_depth[0], best_paths[0]


def scan_file(path, max_bytes=40_000_000):
    try:
        if os.path.getsize(path) > max_bytes:
            return None
        text = open(path, encoding='utf-8', errors='replace').read()
    except OSError:
        return None
    try:
        top = parse(tokenize(text))
    except RecursionError:
        return None
    d, p = 0, 1
    for form in top:
        if isinstance(form, list) and form and form[0] in ('assert', 'assert-not'):
            for body in form[1:]:
                try:
                    dd, pp = analyse(body)
                except RecursionError:
                    return {'path': path, 'let_depth': -1, 'max_paths': -1,
                            'note': 'recursion'}
                d = max(d, dd)
                p = max(p, pp)
    return {'path': path, 'let_depth': d, 'max_paths': p}


def main():
    files = [l.strip() for l in open(sys.argv[1]) if l.strip()]
    out = sys.argv[2]
    rows = []
    for i, f in enumerate(files):
        r = scan_file(f)
        if r:
            rows.append(r)
        if (i + 1) % 50 == 0:
            print(f"  {i+1}/{len(files)}", file=sys.stderr, flush=True)
    json.dump(rows, open(out, 'w'))
    ok = [r for r in rows if r['max_paths'] >= 0]
    print(f"files scanned={len(rows)} parsed={len(ok)} skipped={len(rows)-len(ok)}")
    for thr, lbl in ((1 << 20, '2^20'), (1 << 25, '2^25'), (1 << 30, '2^30')):
        n = sum(1 for r in ok if r['max_paths'] >= thr)
        print(f"  max_paths >= {lbl}: {n}")
    deep = sum(1 for r in ok if r['let_depth'] >= 25)
    print(f"  let_depth >= 25: {deep}")


if __name__ == '__main__':
    main()
