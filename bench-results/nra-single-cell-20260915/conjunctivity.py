#!/usr/bin/env python3
"""How many of the in-bounds files are actually CONJUNCTIVE?

Lane NRA-SINGLE-CELL, ADR-2121. A correction to this lane's own exit-criterion-1
sizing, made after the capability probe found the route declining
`non-conjunctive` on files the sizing had counted as in shape.

`shape-features.py` (ADR-2110) records `has_top_or`, which tests the **outermost
node of each assertion**. The `meti-tarski` benchmarks are a single assertion
built from one enormous `let`-bound `and` tree, so a disjunction sitting six
levels inside it does not move `has_top_or` -- and ADR-2110's own decision 1
records exactly this on `atan-vega-3-chunk-0242`: "one `or` ends the exact
decider before any projection".

So `has_top_or == 0` was the wrong question. The right one is whether ANY
non-conjunctive connective appears anywhere under the assertion after `let`
expansion, because that is what `collect_multi_conjuncts` walks.

This script asks it: expand every `let`, then walk the whole term looking for
`or`, `=>`, `xor`, `ite`, `distinct`, or a negation of anything but a
comparison. It prints the corrected ceiling beside the one the sizing published,
so the difference is visible rather than quietly replacing it.
"""

from __future__ import annotations

import argparse
import collections
import re
import sys
from pathlib import Path

NONCONJUNCTIVE = {"or", "=>", "implies", "xor", "ite", "distinct"}
COMPARISONS = {"<", "<=", ">", ">=", "=", "not="}


def tokenize(text: str) -> list[str]:
    text = re.sub(r";[^\n]*", " ", text)
    text = text.replace("(", " ( ").replace(")", " ) ")
    return text.split()


def parse(tokens: list[str], pos: int = 0):
    """A minimal s-expression reader. Returns (node, next_pos)."""
    if tokens[pos] == "(":
        out = []
        pos += 1
        while tokens[pos] != ")":
            node, pos = parse(tokens, pos)
            out.append(node)
        return out, pos + 1
    return tokens[pos], pos + 1


def expand_lets(node, env: dict):
    """Substitute every `let` binding, so the walk sees the real term."""
    if isinstance(node, str):
        return env.get(node, node)
    if not node:
        return node
    if node[0] == "let" and len(node) == 3:
        inner = dict(env)
        for name, value in node[1]:
            inner[name] = expand_lets(value, env)
        return expand_lets(node[2], inner)
    return [expand_lets(c, env) for c in node]


def find_nonconjunctive(node, out: collections.Counter) -> None:
    if isinstance(node, str) or not node:
        return
    head = node[0]
    if isinstance(head, str):
        if head in NONCONJUNCTIVE:
            out[head] += 1
        elif head == "not":
            # `not <comparison>` is a comparison; `not <anything else>` is not.
            arg = node[1] if len(node) > 1 else None
            if not (isinstance(arg, list) and arg and arg[0] in COMPARISONS):
                out["not-nonatomic"] += 1
    for child in node[1:]:
        find_nonconjunctive(child, out)


def classify(path: Path) -> tuple[bool, collections.Counter]:
    tokens = tokenize(path.read_text(encoding="utf-8", errors="replace"))
    pos = 0
    found: collections.Counter[str] = collections.Counter()
    while pos < len(tokens):
        node, pos = parse(tokens, pos)
        if isinstance(node, list) and node and node[0] == "assert":
            find_nonconjunctive(expand_lets(node[1], {}), found)
    return (not found), found


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--list", required=True)
    ap.add_argument("--corpus-root", required=True)
    ap.add_argument("--tsv")
    args = ap.parse_args()

    files = [
        ln for ln in Path(args.list).read_text(encoding="utf-8").splitlines() if ln
    ]
    root = Path(args.corpus_root)
    rows = []
    conj = 0
    reasons: collections.Counter[str] = collections.Counter()
    for rel in files:
        try:
            ok, found = classify(root / rel)
        except (OSError, IndexError, RecursionError) as exc:
            print(f"UNREADABLE {rel}: {exc}", file=sys.stderr)
            return 1
        conj += int(ok)
        for k, v in found.items():
            reasons[k] += v
        rows.append((rel, "yes" if ok else "no", ";".join(sorted(found))))

    print(f"files examined                      : {len(files)}")
    print(f"CONJUNCTIVE after `let` expansion   : {conj}")
    print(f"carrying a non-conjunctive connective: {len(files) - conj}")
    print("\nconnectives found (total occurrences):")
    for k, v in reasons.most_common():
        print(f"  {k:18s} {v:6d}")

    if args.tsv:
        with open(args.tsv, "w", encoding="utf-8") as fh:
            fh.write("file\tconjunctive\tconnectives\n")
            for r in rows:
                fh.write("\t".join(r) + "\n")
        print(f"\nwrote {args.tsv}")
    return 0


if __name__ == "__main__":
    sys.setrecursionlimit(100000)
    raise SystemExit(main())
