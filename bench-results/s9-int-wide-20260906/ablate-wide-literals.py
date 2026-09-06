#!/usr/bin/env python3
"""Re-run of ADR-0376's decisive ablation, on today's tree.

ADR-0376 (2026-08-04) deferred the `Int` widening on a measurement, not on
cost: with **every** literal above `i128::MAX` removed from the problem, all six
files the reference solver decides were *still* `unknown`, so the binding
constraint was the decision procedure (`MAX_INT_BLAST_WIDTH = 64`, and a
measured magnitude cliff between `2^24` and `2^32`), not the literal type.

A blocker recorded a month ago is a claim about a tree that no longer exists, so
this rebuilds the same two ablations and they are re-measured before any code is
written. Each writes files that a perfect bignum IR would be *no better than*:

  rescale  every out-of-range numeral -> `2^60 + i` (distinct, in range)
  delete   every top-level `(assert …)` mentioning an out-of-range numeral

Usage:
    python3 ablate-wide-literals.py <listing.txt> <out_dir> [rescale|delete]
"""

import os
import sys

I128_MAX = (1 << 127) - 1
BASE = 1 << 60


def tokenize_spans(text):
    """Yield ``(kind, value, start, end)`` spans covering every token."""
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
        if c in "()":
            yield ("open" if c == "(" else "close", c, i, i + 1)
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
            yield ("atom", text[i:j], i, j)
            i = j
            continue
        if c == "|":
            j = text.find("|", i + 1)
            j = n if j < 0 else j + 1
            yield ("atom", text[i:j], i, j)
            i = j
            continue
        j = i
        while j < n and text[j] not in ' \t\r\n()";|':
            j += 1
        yield ("atom", text[i:j], i, j)
        i = j


def rescale(text):
    """Replace each out-of-range numeral with a distinct `2^60 + i`."""
    edits = []
    seen = {}
    for kind, val, start, end in tokenize_spans(text):
        if kind == "atom" and val.isdigit() and int(val) > I128_MAX:
            if val not in seen:
                seen[val] = str(BASE + len(seen))
            edits.append((start, end, seen[val]))
    out = []
    prev = 0
    for start, end, replacement in edits:
        out.append(text[prev:start])
        out.append(replacement)
        prev = end
    out.append(text[prev:])
    return "".join(out), len(edits)


def delete_asserts(text):
    """Drop every top-level `(assert …)` containing an out-of-range numeral."""
    spans = list(tokenize_spans(text))
    keep = []
    prev = 0
    dropped = 0
    idx = 0
    while idx < len(spans):
        kind, val, start, end = spans[idx]
        if kind != "open":
            idx += 1
            continue
        head = spans[idx + 1] if idx + 1 < len(spans) else None
        if head is None or head[0] != "atom" or head[1] != "assert":
            idx += 1
            continue
        depth = 0
        j = idx
        wide = False
        while j < len(spans):
            k, v, _s, _e = spans[j]
            if k == "open":
                depth += 1
            elif k == "close":
                depth -= 1
                if depth == 0:
                    break
            elif v.isdigit() and int(v) > I128_MAX:
                wide = True
            j += 1
        close_end = spans[j][3] if j < len(spans) else len(text)
        if wide:
            keep.append(text[prev:start])
            prev = close_end
            dropped += 1
        idx = j + 1
    keep.append(text[prev:])
    return "".join(keep), dropped


def main():
    if len(sys.argv) < 3:
        print(__doc__, file=sys.stderr)
        return 2
    listing, out_dir = sys.argv[1], sys.argv[2]
    mode = sys.argv[3] if len(sys.argv) > 3 else "rescale"
    os.makedirs(out_dir, exist_ok=True)
    with open(listing) as handle:
        paths = [line.strip() for line in handle if line.strip()]
    for path in paths:
        with open(path, "r", errors="replace") as handle:
            text = handle.read()
        if mode == "rescale":
            new, count = rescale(text)
        elif mode == "delete":
            new, count = delete_asserts(text)
        else:
            print(f"unknown mode {mode}", file=sys.stderr)
            return 2
        target = os.path.join(out_dir, os.path.basename(path))
        with open(target, "w") as handle:
            handle.write(new)
        # A rewrite that changed nothing is a silent no-op, and a no-op ablation
        # would report the unmodified file's verdict as the ablation's result.
        if count == 0:
            print(f"NO-OP\t{path}", file=sys.stderr)
        print(f"{mode}\t{count}\t{target}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
