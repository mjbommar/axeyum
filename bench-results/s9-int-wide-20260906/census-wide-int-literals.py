#!/usr/bin/env python3
"""Census of benchmark files carrying integer literals beyond the `i128` range.

Answers exactly one question, for one division listing at a time: which files
contain a **bare numeral** — an all-ASCII-digit atom, which is the precise shape
`crates/axeyum-smtlib/src/parse.rs` feeds to `a.parse::<i128>()` before emitting
``integer literal `…` exceeds the modeled `Int` range`` — that does not fit
`i128`, how large the largest such numeral is, and in what syntactic position it
appears.

The tokenizer mirrors `crates/axeyum-smtlib/src/sexpr.rs`: whitespace- and
paren-delimited atoms, `;` line comments, `"…"` string literals (with `""`
escaping) and `|…|` quoted symbols. Quoted and string tokens are therefore never
mistaken for numerals, and a numeral inside an indexed identifier
(`(_ bv5 32)`) is reported with its enclosing head `_` so it can be told apart
from a term-position literal.

This is a *scan*, not the parser. `validate-census-against-parser.sh` in this
directory cross-checks its verdict against the real front door.

Usage:
    python3 census-wide-int-literals.py <listing.txt> [out.tsv]
"""

import os
import sys

I128_MAX = (1 << 127) - 1


def tokenize(text):
    """Yield ``(kind, value)`` where kind is ``open`` | ``close`` | ``atom``."""
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c in " \t\r\n":
            i += 1
            continue
        if c == ";":
            while i < n and text[i] != "\n":
                i += 1
            continue
        if c == "(":
            yield ("open", "(")
            i += 1
            continue
        if c == ")":
            yield ("close", ")")
            i += 1
            continue
        if c == '"':
            j = i + 1
            while j < n:
                if text[j] == '"':
                    if j + 1 < n and text[j + 1] == '"':
                        j += 2
                        continue
                    j += 1
                    break
                j += 1
            yield ("atom", text[i:j])
            i = j
            continue
        if c == "|":
            j = text.find("|", i + 1)
            j = n if j < 0 else j + 1
            yield ("atom", text[i:j])
            i = j
            continue
        j = i
        while j < n and text[j] not in ' \t\r\n()";|':
            j += 1
        yield ("atom", text[i:j])
        i = j


def scan(path):
    """Return ``(best, occurrences, heads)`` for one file.

    ``best`` is ``(value, enclosing_head, grandparent_head, arg_index)`` for the
    numerically largest out-of-range numeral, or ``None`` if the file has none.
    """
    with open(path, "r", errors="replace") as handle:
        text = handle.read()
    stack = []  # each frame: [head_or_None, args_seen_so_far]
    best = None
    occurrences = 0
    heads = {}
    for kind, val in tokenize(text):
        if kind == "open":
            stack.append([None, 0])
            continue
        if kind == "close":
            if stack:
                stack.pop()
            if stack:
                stack[-1][1] += 1
            continue
        if stack and stack[-1][0] is None:
            stack[-1][0] = val
        elif stack:
            stack[-1][1] += 1
        if val.isdigit() and int(val) > I128_MAX:
            value = int(val)
            head = stack[-1][0] if stack else "<toplevel>"
            grandparent = stack[-2][0] if len(stack) >= 2 else "<toplevel>"
            arg_index = stack[-1][1] if stack else 0
            occurrences += 1
            heads[head] = heads.get(head, 0) + 1
            if best is None or value > best[0]:
                best = (value, head, grandparent, arg_index)
    return best, occurrences, heads


def declared_status(path):
    """The `:status` attribute, or `none` if the file declares none."""
    with open(path, "r", errors="replace") as handle:
        for line in handle:
            if ":status" in line:
                for token in line.replace("(", " ").replace(")", " ").split():
                    if token in ("sat", "unsat", "unknown"):
                        return token
    return "none"


def main():
    if len(sys.argv) < 2:
        print(__doc__, file=sys.stderr)
        return 2
    listing = sys.argv[1]
    out = sys.argv[2] if len(sys.argv) > 2 else None
    with open(listing) as handle:
        paths = [line.strip() for line in handle if line.strip()]
    rows = []
    missing = 0
    for path in paths:
        if not os.path.exists(path):
            missing += 1
            print(f"MISSING\t{path}", file=sys.stderr)
            continue
        best, occurrences, heads = scan(path)
        if best is None:
            continue
        value, head, grandparent, arg_index = best
        top_head = max(heads.items(), key=lambda kv: (kv[1], kv[0]))[0]
        rows.append(
            (
                path,
                value.bit_length(),
                len(str(value)),
                occurrences,
                head,
                grandparent,
                arg_index,
                top_head,
                declared_status(path),
                os.path.getsize(path),
            )
        )
    rows.sort(key=lambda row: (-row[1], row[0]))
    header = (
        "file\tmax_literal_bits\tmax_literal_digits\twide_literal_occurrences\t"
        "max_enclosing_head\tmax_grandparent_head\tmax_arg_index\t"
        "modal_enclosing_head\tdeclared_status\tbytes"
    )
    lines = [header]
    lines.extend("\t".join(str(cell) for cell in row) for row in rows)
    text = "\n".join(lines) + "\n"
    if out:
        with open(out, "w") as handle:
            handle.write(text)
    else:
        sys.stdout.write(text)
    print(
        f"# listed={len(paths)} missing={missing} with_wide_literal={len(rows)}",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
