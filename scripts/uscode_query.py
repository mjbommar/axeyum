#!/usr/bin/env python3
"""Query a lifted U.S. Code section (output of scripts/uscode_lift.py).

    python3 scripts/uscode_query.py LIFTED.json show c/4/A/i
    python3 scripts/uscode_query.py LIFTED.json cited-by c/4/A/i
    python3 scripts/uscode_query.py LIFTED.json cites g
    python3 scripts/uscode_query.py LIFTED.json term "protected computer"
    python3 scripts/uscode_query.py LIFTED.json quantities [--kind money_usd]
    python3 scripts/uscode_query.py LIFTED.json summary

Provision arguments are paths below the section (`c/4/A/i`) or full
identifiers (`/us/usc/t18/s1030/c/4/A/i`). `cited-by` includes references to
the provision's descendants, which is what a rule author needs before changing
a shared definition such as a list of harm factors.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


def load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def full_id(lifted: dict[str, Any], arg: str) -> str:
    base = lifted["section"]["id"]
    if arg.startswith(base):
        return arg
    return base + "/" + arg.strip("/")


def cite(lifted: dict[str, Any], provision_id: str) -> str:
    for node in lifted["provisions"]:
        if node["id"] == provision_id:
            return node["citation"]
    return provision_id


def within(provision_id: str, root: str) -> bool:
    return provision_id == root or provision_id.startswith(root + "/")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("lifted", type=Path)
    parser.add_argument("command", choices=["show", "cited-by", "cites", "term", "quantities", "summary"])
    parser.add_argument("arg", nargs="?")
    parser.add_argument("--kind")
    args = parser.parse_args()
    lifted = load(args.lifted)
    nodes = {node["id"]: node for node in lifted["provisions"]}

    if args.command == "summary":
        summary = lifted["summary"]
        print(f"{lifted['section']['citation']}: {lifted['section']['heading']}")
        print(f"  source: {lifted['source']['edition']}, current through {lifted['source']['current_through']}")
        print(f"  provisions: {summary['provisions']} " + json.dumps(summary["by_level"]))
        print(
            f"  cross-references: {summary['internal_references']} internal "
            f"({summary['resolved_targets']} resolved targets), {summary['external_references']} external"
        )
        print(f"  definitions: {summary['definitions']}; quantities: {summary['quantities']}")
        print(f"  editorial footnotes: {summary['editorial_footnotes']}")
        return 0

    if args.command == "quantities":
        for quantity in lifted["quantities"]:
            if args.kind and quantity["kind"] != args.kind:
                continue
            value = "life" if quantity["value"] is None else quantity["value"]
            unit = "" if quantity["value"] is None else (quantity.get("unit") or "")
            print(
                f"{cite(lifted, quantity['provision'])}: {quantity['kind']} "
                f"{quantity['comparator']} {value} {unit}".rstrip()
                + f'   "{quantity["raw"]}"'
            )
        return 0

    if not args.arg:
        print("error: this command needs an argument", file=sys.stderr)
        return 2

    if args.command == "term":
        for entry in lifted["definitions"]:
            if entry["term"] == args.arg:
                print(f'defined: {cite(lifted, entry["provision"])} ("{entry["term"]}" {entry["verb"]})')
        for entry in lifted["term_uses"]:
            if entry["term"] == args.arg:
                print(f"used in {len(entry['provisions'])} provisions:")
                for provision in entry["provisions"]:
                    print(f"  {cite(lifted, provision)}")
        return 0

    target = full_id(lifted, args.arg)
    if target not in nodes:
        print(f"error: no provision {target}", file=sys.stderr)
        return 1

    if args.command == "show":
        def emit(node_id: str, depth: int) -> None:
            node = nodes[node_id]
            print("  " * depth + f"({node['enumerator']}) {node['text'] or '—'}")
            for child in node["children"]:
                emit(child, depth + 1)
            if node.get("continuation"):
                print("  " * depth + node["continuation"])

        print(nodes[target]["citation"])
        emit(target, 0)
        return 0

    if args.command == "cited-by":
        hits = []
        for ref in lifted["cross_references"]:
            reached = sorted({t for t in ref["targets"] if within(t, target)})
            if reached:
                hits.append((ref["from"], ref["raw"], reached))
        print(f"{nodes[target]['citation']} and its descendants are cited {len(hits)} times:")
        for origin, raw, reached in hits:
            names = ", ".join(cite(lifted, t).split(" ")[-1] for t in reached)
            print(f'  {cite(lifted, origin)}  "{raw}"  -> {names}')
        return 0

    if args.command == "cites":
        for ref in lifted["cross_references"]:
            if within(ref["from"], target):
                if ref["scope"] == "internal":
                    names = ", ".join(cite(lifted, t).split(" ")[-1] for t in ref["targets"])
                    print(f'  {cite(lifted, ref["from"])}  "{ref["raw"]}"  -> {names}')
                else:
                    print(f'  {cite(lifted, ref["from"])}  "{ref["raw"]}"  -> {ref["citation"]} (external)')
        return 0
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
