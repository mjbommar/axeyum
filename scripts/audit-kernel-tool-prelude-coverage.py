#!/usr/bin/env python3
"""Which `axeyum-lean-kernel` instruments build which preludes, and which say so.

An empty result from a tool that was never pointed at your subject is
indistinguishable from a strong negative result. That is the measured root
cause of repeated lane-hours spent re-deriving lemmas that were already in the
tree: `shape_search` built 17 of the crate's 31 `pub fn build_*_prelude`
functions and returned nothing for `--ns FO` against a 4,839-row dump, while
its own internal cross-check passed because both halves of that check were
hand-written and omitted the same builders.

This script measures the same property for EVERY example in the crate, and
gates one rule:

    an instrument that builds three or more preludes must print a
    `coverage:` line saying which.

Three is the line between a single-subject probe (`creal_eval_cost` builds
`creal`; nothing about its output invites a whole-kernel reading) and a
multi-prelude instrument whose silence about scope is what gets misread.

`--check` enforces the rule as a RATCHET against `PIN_UNCOVERED`, because the
rule was introduced against a population that already violated it 13 times.
The ratchet is two-sided on purpose: a run that finds FEWER violations than the
pin also fails, with an instruction to lower the pin. A one-sided ratchet
silently stops measuring the moment somebody fixes things faster than they
update the number.

Method notes, since each of these has produced a wrong answer somewhere in this
repository:

* The authority is read from `src/` on every run, never from a literal list.
* `*_tests.rs` files are excluded, and whole-line `//` comments are stripped,
  so a builder merely DISCUSSED in prose is not counted as one that is called.
* A builder's edges are read from that builder's own function BODY. That is the
  conservative direction: a call hidden in a helper is MISSED, which reports a
  tool as blinder than it is -- a false alarm, never a false all-clear.
"""

from __future__ import annotations

import argparse
import os
import re
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), os.pardir)
SRC = os.path.join(ROOT, "crates", "axeyum-lean-kernel", "src")
EXAMPLES = os.path.join(ROOT, "crates", "axeyum-lean-kernel", "examples")

# An instrument building at least this many preludes must declare its coverage.
COVERAGE_THRESHOLD = 3

# Measured 2026-09-06 on the commit that introduced this script: instruments at
# or above the threshold that do NOT print a coverage line. Lower it as tools
# are fixed; `--check` fails in both directions.
PIN_UNCOVERED = 13


def strip_line_comments(text: str) -> str:
    return "\n".join(
        line for line in text.split("\n") if not line.lstrip().startswith("//")
    )


def source_files() -> list[str]:
    out = []
    for directory, _, files in os.walk(SRC):
        for name in sorted(files):
            if name.endswith(".rs") and not name.endswith("_tests.rs"):
                out.append(os.path.join(directory, name))
    return sorted(out)


def item_body(path: str, name: str) -> str:
    """The body of a top-level `fn <name>`; column-0 `}` ends it."""
    body, inside = [], False
    for line in open(path, encoding="utf-8").read().split("\n"):
        if not inside:
            if line.startswith(f"pub fn {name}") or line.startswith(f"fn {name}"):
                inside = True
            continue
        if line == "}":
            break
        body.append(line)
    return "\n".join(body)


def builder_inventory() -> tuple[dict[str, str], set[str]]:
    """`{exported builder: defining file}` and the `*_prelude` subset."""
    lib = strip_line_comments(
        open(os.path.join(SRC, "lib.rs"), encoding="utf-8").read()
    )
    defs: dict[str, str] = {}
    for path in source_files():
        for line in open(path, encoding="utf-8"):
            match = re.match(r"pub fn (build_[A-Za-z0-9_]+)", line)
            if match and match.group(1) in lib:
                defs[match.group(1)] = path
    preludes = {name for name in defs if name.endswith("_prelude")}
    return defs, preludes


def call_graph(defs: dict[str, str]) -> dict[str, set[str]]:
    graph = {}
    for name, path in defs.items():
        body = strip_line_comments(item_body(path, name))
        graph[name] = {
            other for other in defs if other != name and f"{other}(" in body
        }
    return graph


def reachable(direct: set[str], graph: dict[str, set[str]]) -> set[str]:
    seen: set[str] = set()
    stack = list(direct)
    while stack:
        name = stack.pop()
        if name in seen:
            continue
        seen.add(name)
        stack.extend(graph.get(name, ()))
    return seen


def audit() -> list[dict]:
    defs, preludes = builder_inventory()
    if len(preludes) < 25:
        sys.exit(
            f"the builder scan found only {len(preludes)} prelude builders; the "
            "authority scan is broken and every verdict below would be "
            "meaningless (positive control: 31 existed on 2026-09-06)"
        )
    graph = call_graph(defs)
    rows = []
    for name in sorted(os.listdir(EXAMPLES)):
        if not name.endswith(".rs"):
            continue
        path = os.path.join(EXAMPLES, name)
        raw = open(path, encoding="utf-8").read()
        text = strip_line_comments(raw)
        direct = {builder for builder in defs if f"{builder}(" in text}
        if not direct:
            continue
        covered = reachable(direct, graph)
        rows.append(
            {
                "tool": name,
                "preludes": sorted(covered & preludes),
                "non_prelude": sorted(covered - preludes),
                "blind": sorted(preludes - covered),
                "declares": bool(re.search(r'"coverage: ', raw)),
                "total_preludes": len(preludes),
            }
        )
    rows.sort(key=lambda row: (-len(row["preludes"]), row["tool"]))
    return rows


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="enforce the coverage-declaration ratchet (non-zero on drift)",
    )
    parser.add_argument(
        "--blind", action="store_true", help="also print each tool's blind set"
    )
    args = parser.parse_args()

    rows = audit()
    total = rows[0]["total_preludes"] if rows else 0
    print(f"{'tool':44s} {'preludes':>9s} {'other':>6s} {'declares':>9s}")
    for row in rows:
        print(
            f"{row['tool']:44s} {len(row['preludes']):>4d}/{total:<4d} "
            f"{len(row['non_prelude']):>6d} {str(row['declares']):>9s}"
        )
        if args.blind and row["blind"]:
            short = " ".join(
                b.removeprefix("build_").removesuffix("_prelude")
                for b in row["blind"]
            )
            print(f"    blind: {short}")

    at_threshold = [r for r in rows if len(r["preludes"]) >= COVERAGE_THRESHOLD]
    uncovered = [r for r in at_threshold if not r["declares"]]
    print()
    print(
        f"control: {len(rows)} instruments build a prelude, "
        f"{len(at_threshold)} build >= {COVERAGE_THRESHOLD}, "
        f"{len(uncovered)} of those declare no coverage (pin {PIN_UNCOVERED})"
    )
    for row in uncovered:
        print(f"  UNDECLARED  {row['tool']}  builds {len(row['preludes'])}")

    if not args.check:
        return 0

    if not at_threshold:
        print(
            "FAIL: no instrument builds >= "
            f"{COVERAGE_THRESHOLD} preludes, so this check examined nothing "
            "and its pass would mean nothing"
        )
        return 1
    if len(uncovered) > PIN_UNCOVERED:
        print(
            f"FAIL: {len(uncovered)} instruments build >= {COVERAGE_THRESHOLD} "
            f"preludes without declaring coverage, pin is {PIN_UNCOVERED}. A "
            "multi-prelude instrument that does not say what it built lets an "
            "empty result read as a strong negative."
        )
        return 1
    if len(uncovered) < PIN_UNCOVERED:
        print(
            f"FAIL: only {len(uncovered)} undeclared instruments remain and the "
            f"pin still says {PIN_UNCOVERED}. Lower PIN_UNCOVERED to "
            f"{len(uncovered)} in this script. A ratchet that is not tightened "
            "stops measuring."
        )
        return 1
    print("OK: coverage-declaration ratchet holds")
    return 0


if __name__ == "__main__":
    sys.exit(main())
