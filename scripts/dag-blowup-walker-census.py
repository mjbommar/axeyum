#!/usr/bin/env python3
"""Scan v2: branching TermId walkers with no memo.

v1 missed the two instances that actually dominated the profile, because it
counted only FREE-function self-recursion (`name(`) and explicitly excluded a
dot-preceded call.  Both `lra::IntCollector::linearize` and
`dl_online::ScanState::linear` are methods, and the second is not recursive at
all -- it is an explicit WORKLIST, which is the standard remedy for stack
overflow and does nothing about path count.

v2 counts three shapes:
  R  self-recursion, free-function or `self.name(` method
  W  explicit worklist: `while let Some(..) = <v>.pop()` with >=2 pushes in body
Both filtered to bodies mentioning TermId, and flagged for a memo token.

A LEAD GENERATOR, not a finding.
"""
import os
import re
import sys
import json

ROOT = sys.argv[1] if len(sys.argv) > 1 else "."
FN_RE = re.compile(
    r'^(\s*)(?:pub(?:\([^)]*\))?\s+)?(?:const\s+)?(?:async\s+)?fn\s+'
    r'([A-Za-z_][A-Za-z0-9_]*)\s*(?:<[^>]*>)?\s*\(', re.M)
MEMO_RE = re.compile(r'\b(memo|cache|cached|seen|visited|interned|done_set)\b', re.I)
POP_RE = re.compile(r'while\s+let\s+Some\s*\(.*?\)\s*=\s*([A-Za-z_][A-Za-z0-9_]*)\s*\.pop\(\)')


def find_body(src, open_paren_idx):
    depth = 0
    i = open_paren_idx
    n = len(src)
    while i < n:
        c = src[i]
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
            if depth == 0:
                break
        i += 1
    sig_end = i
    j = sig_end
    while j < n and src[j] != '{':
        if src[j] == ';':
            return None, None
        j += 1
    if j >= n:
        return None, None
    depth = 0
    k = j
    while k < n:
        c = src[k]
        if c == '"':
            k += 1
            while k < n and src[k] != '"':
                if src[k] == '\\':
                    k += 1
                k += 1
        elif c == '/' and k + 1 < n and src[k + 1] == '/':
            while k < n and src[k] != '\n':
                k += 1
        elif c == '{':
            depth += 1
        elif c == '}':
            depth -= 1
            if depth == 0:
                return src[open_paren_idx:sig_end + 1], src[j:k + 1]
        k += 1
    return None, None


rows = []
for dirpath, dirnames, filenames in os.walk(ROOT):
    dirnames[:] = [d for d in dirnames if d not in ('target', '.git', 'references', 'node_modules')]
    for fname in filenames:
        if not fname.endswith('.rs'):
            continue
        path = os.path.join(dirpath, fname)
        if '/src/' not in path:
            continue
        src = open(path, encoding='utf-8', errors='replace').read()
        for m in FN_RE.finditer(src):
            name = m.group(2)
            sig, body = find_body(src, m.end() - 1)
            if body is None:
                continue
            if 'TermId' not in sig and 'TermId' not in body:
                continue
            free = len(re.findall(r'(?<![A-Za-z0-9_.])' + re.escape(name) + r'\s*\(', body))
            meth = len(re.findall(r'self\s*\.\s*' + re.escape(name) + r'\s*\(', body))
            rec = free + meth
            shapes = []
            if rec >= 2:
                shapes.append('R')
            wl = POP_RE.search(body)
            if wl:
                var = wl.group(1)
                pushes = len(re.findall(re.escape(var) + r'\s*\.push\(', body))
                if pushes >= 2:
                    shapes.append('W')
            if not shapes:
                continue
            has_memo = bool(MEMO_RE.search(sig)) or bool(MEMO_RE.search(body))
            line = src[:m.start()].count('\n') + 1
            rows.append({
                'path': os.path.relpath(path, ROOT),
                'line': line,
                'fn': name,
                'shape': ''.join(shapes),
                'self_calls': rec,
                'memo_token': has_memo,
                'depth_cap': bool(re.search(r'depth\s*>\s*\d', body)),
            })

rows.sort(key=lambda r: (r['memo_token'], r['path'], r['line']))
no_memo = [r for r in rows if not r['memo_token']]
print(f"branching TermId walkers: {len(rows)}  (R={sum(1 for r in rows if 'R' in r['shape'])}, "
      f"W={sum(1 for r in rows if 'W' in r['shape'])})")
print(f"  ... no memo/cache/seen token anywhere: {len(no_memo)}  "
      f"(R={sum(1 for r in no_memo if 'R' in r['shape'])}, "
      f"W={sum(1 for r in no_memo if 'W' in r['shape'])})")
print(f"  ... of those, carrying a depth cap: {sum(1 for r in no_memo if r['depth_cap'])}")
if '--json' in sys.argv:
    json.dump(rows, open(sys.argv[sys.argv.index('--json') + 1], 'w'), indent=1)
if '--list' in sys.argv:
    for r in no_memo:
        print(f"{r['path']}:{r['line']}\t{r['fn']}\t{r['shape']}\tcalls={r['self_calls']}"
              f"\tcap={'Y' if r['depth_cap'] else 'n'}")
