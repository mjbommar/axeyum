#!/usr/bin/env python3
"""Textual census: which SMT-LIB files contain a NESTED array sort?

A nested array sort is `(Array A B)` where A or B is itself (after 0-arity
`define-sort` alias expansion) an array sort.

Deliberately independent of the Rust parser: this is the *denominator* check
for the refusal `nested array element sort is unsupported`, derived from file
text rather than from whichever gate happens to fire first.

Usage: census_nested.py [--list] <root>...
  default: one TSV summary line per root
  --list : print one path per line for files WITH a nested array sort
"""
import os
import re
import sys

TOK = re.compile(r'\(|\)|[^\s()]+')


def sexprs(text):
    """Yield top-level s-expressions as nested lists of str."""
    stack = []
    cur = []
    for m in TOK.finditer(text):
        t = m.group(0)
        if t == '(':
            stack.append(cur)
            cur = []
        elif t == ')':
            if not stack:
                continue
            done = cur
            cur = stack.pop()
            cur.append(done)
        else:
            cur.append(t)
    for x in cur:
        yield x


def strip_comments(text):
    out = []
    in_str = False
    in_qsym = False
    i = 0
    n = len(text)
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


def is_array(sort, aliases, depth=0):
    if depth > 40:
        return False
    if isinstance(sort, str):
        a = aliases.get(sort)
        return is_array(a, aliases, depth + 1) if a is not None else False
    if isinstance(sort, list) and sort and sort[0] == 'Array':
        return True
    return False


def nested_hits(sort, aliases, depth=0):
    """Count (Array A B) nodes where A or B is an array sort."""
    if depth > 200 or not isinstance(sort, list):
        return 0
    n = 0
    if len(sort) == 3 and sort[0] == 'Array':
        if is_array(sort[1], aliases) or is_array(sort[2], aliases):
            n += 1
    for s in sort:
        n += nested_hits(s, aliases, depth + 1)
    return n


def scan(path):
    try:
        with open(path, 'r', errors='replace') as f:
            text = f.read()
    except OSError:
        return None
    text = strip_comments(text)
    aliases = {}
    total = 0
    for cmd in sexprs(text):
        if not isinstance(cmd, list) or not cmd:
            continue
        if cmd[0] == 'define-sort' and len(cmd) == 4 and cmd[2] == []:
            aliases[cmd[1]] = cmd[3]
        total += nested_hits(cmd, aliases)
    return total


def main():
    args = sys.argv[1:]
    listing = False
    if args and args[0] == '--list':
        listing = True
        args = args[1:]
    for root in args:
        div = os.path.basename(root.rstrip('/'))
        files = 0
        with_nested = 0
        errs = 0
        for dirpath, _, fnames in os.walk(root):
            for fn in sorted(fnames):
                if not fn.endswith('.smt2'):
                    continue
                files += 1
                p = os.path.join(dirpath, fn)
                r = scan(p)
                if r is None:
                    errs += 1
                elif r > 0:
                    with_nested += 1
                    if listing:
                        print(p, flush=True)
        if not listing:
            pct = 100.0 * with_nested / files if files else 0.0
            print(f"{div}\t{files}\t{with_nested}\t{pct:.1f}%\t{errs}", flush=True)


main()
