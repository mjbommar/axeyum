#!/usr/bin/env python3
"""The declared sort of every argument of every over-cap `distinct`."""
import io
import re
import sys
from multiprocessing import Pool

CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"
MIN_OVER = 363


def scan(rel):
    path = CORPUS + rel
    try:
        s = io.open(path, encoding='utf-8', errors='replace').read()
    except OSError:
        return (rel, 'READ-ERROR', 0)
    decls = {}
    for m in re.finditer(r'\(declare-fun\s+(\S+)\s*\(\s*\)\s*([A-Za-z0-9_]+)\s*\)', s):
        decls[m.group(1)] = m.group(2)
    for m in re.finditer(r'\(declare-const\s+(\S+)\s+([A-Za-z0-9_]+)\s*\)', s):
        decls[m.group(1)] = m.group(2)
    sorts_declared = set(re.findall(r'\(declare-sort\s+(\S+)', s))
    best = None
    start = 0
    while True:
        i = s.find("(distinct", start)
        if i < 0:
            break
        d = 0
        k = i
        while k < len(s):
            c = s[k]
            if c == '(':
                d += 1
            elif c == ')':
                d -= 1
                if d == 0:
                    break
            k += 1
        body = s[i + len("(distinct"):k]
        args = body.split()
        if '(' not in body and (best is None or len(args) > len(best)):
            best = args
        start = i + 1
    if best is None or len(best) < MIN_OVER:
        return (rel, 'NO-FLAT-OVER-CAP', 0)
    kinds = {}
    for a in best:
        srt = decls.get(a)
        if srt is None:
            kinds['UNDECLARED'] = kinds.get('UNDECLARED', 0) + 1
        elif srt in sorts_declared:
            kinds['UNINTERPRETED:' + srt] = kinds.get('UNINTERPRETED:' + srt, 0) + 1
        else:
            kinds[srt] = kinds.get(srt, 0) + 1
    summary = ','.join(f"{k}={v}" for k, v in sorted(kinds.items()))
    return (rel, summary, len(best))


def main():
    rels = [l.strip() for l in sys.stdin if l.strip()]
    with Pool(16) as p:
        for rel, summary, n in p.imap_unordered(scan, rels, chunksize=4):
            print(f"{n}\t{summary}\t{rel}")


if __name__ == '__main__':
    main()
