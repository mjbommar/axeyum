#!/usr/bin/env python3
"""Why the eager split leaves residual products: print the SHAPE of every
product the narrow-box rewrite could not split, so the sizing bracket names a
reason rather than a count."""
import argparse
import collections
import importlib.util
import os

spec = importlib.util.spec_from_file_location(
    "sur", os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "qf-nia-sat-eager-split-surrogate.py"))
sur = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sur)


def shape(node, boxes):
    if isinstance(node, str):
        if sur.as_int(node) is not None:
            return "num"
        return "boxvar" if node in boxes else "var"
    if node and node[0] == "*":
        return "mul"
    if node and node[0] == "ite":
        return "ite"
    return node[0] if node and isinstance(node[0], str) else "app"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", required=True)
    ap.add_argument("--limit", type=int, default=3)
    args = ap.parse_args()
    files = [l.strip() for l in open(args.list) if l.strip()][: args.limit]
    for path in files:
        forms = sur.parse(sur.tokenize(open(path, errors="replace").read()))
        asserts = [f[1] for f in forms if isinstance(f, list) and f and f[0] == "assert"]
        boxes = sur.harvest_bounds(asserts)
        shapes = collections.Counter()
        examples = {}
        # walk every `*` node iteratively
        stack = [a for a in asserts]
        while stack:
            cur = stack.pop()
            if not isinstance(cur, list):
                continue
            if cur and cur[0] == "*" and len(cur) == 3:
                a, b = cur[1], cur[2]
                if sur.as_int(a) is None and sur.as_int(b) is None:
                    na = isinstance(a, str) and a in boxes
                    nb = isinstance(b, str) and b in boxes
                    if not na and not nb:
                        k = (shape(a, boxes), shape(b, boxes))
                        shapes[k] += 1
                        if k not in examples:
                            buf = []
                            sur.render(cur, buf)
                            examples[k] = "".join(buf)[:110]
            stack.extend(c for c in cur if isinstance(c, list))
        print(f"\n=== {os.path.basename(path)[:78]}")
        print(f"    boxes harvested: {len(boxes)}")
        for k, n in shapes.most_common(6):
            print(f"    residual {k[0]:8s} * {k[1]:8s}  n={n:4d}   e.g. {examples[k]}")


if __name__ == "__main__":
    main()
