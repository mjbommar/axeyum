#!/usr/bin/env python3
"""Max `distinct` arity per file, by S-expression tokenisation.

Counts the number of TOP-LEVEL argument groups of every `(distinct ...)`
application and reports the maximum per file, plus how many applications in
that file exceed the parser's pairwise cap.

Handles: line comments (`;`), string literals ("..." with "" escape),
quoted symbols (|...|). Reports (file, max_arity, n_over_cap, total_distinct).
"""
import sys, os
from multiprocessing import Pool

CAP = 65536  # MAX_DISTINCT_EXPANSION_PAIRS
# n(n-1)/2 > CAP  <=>  n >= 363
MIN_OVER = 363


def scan(path):
    try:
        with open(path, 'rb') as fh:
            s = fh.read()
    except OSError:
        return (path, -1, 0, 0)
    n = len(s)
    i = 0
    # stack of [is_distinct_app, argcount, counting]
    stack = []
    maxar = 0
    over = 0
    total = 0
    while i < n:
        c = s[i]
        if c == 0x3B:  # ;
            j = s.find(b'\n', i)
            i = n if j < 0 else j + 1
            continue
        if c == 0x22:  # "
            i += 1
            while i < n:
                if s[i] == 0x22:
                    if i + 1 < n and s[i + 1] == 0x22:
                        i += 2
                        continue
                    i += 1
                    break
                i += 1
            # a string is one atom -> counts as an argument of the enclosing app
            if stack:
                stack[-1][1] += 1
            continue
        if c == 0x7C:  # |
            j = s.find(b'|', i + 1)
            i = n if j < 0 else j + 1
            if stack:
                stack[-1][1] += 1
            continue
        if c == 0x28:  # (
            # a new list: it is an argument of the enclosing app (unless it is
            # the head position, which for a list head is still an argument in
            # SMT-LIB only for indexed ops; treat uniformly, head is an atom)
            if stack:
                stack[-1][1] += 1
            # read head atom
            j = i + 1
            while j < n and s[j] in b' \t\r\n':
                j += 1
            k = j
            while k < n and s[k] not in b' \t\r\n()|;"':
                k += 1
            head = s[j:k]
            stack.append([head == b'distinct', 0, 0])
            i += 1
            continue
        if c == 0x29:  # )
            if stack:
                isd, cnt, _ = stack.pop()
                if isd:
                    total += 1
                    cnt -= 1  # head atom `distinct` itself
                    if cnt > maxar:
                        maxar = cnt
                    if cnt >= MIN_OVER:
                        over += 1
            i += 1
            continue
        if c in b' \t\r\n':
            i += 1
            continue
        # atom
        k = i
        while k < n and s[k] not in b' \t\r\n()|;"':
            k += 1
        if stack:
            stack[-1][1] += 1
        i = k if k > i else i + 1
        continue
    return (path, maxar, over, total)


def main():
    paths = [l.rstrip('\n') for l in sys.stdin if l.strip()]
    with Pool(16) as p:
        for path, maxar, over, total in p.imap_unordered(scan, paths, chunksize=32):
            print(f"{maxar}\t{over}\t{total}\t{path}")


if __name__ == '__main__':
    main()
