#!/usr/bin/env python3
"""Measure the intra-crate module dependency graph of `axeyum-solver`.

WHY THIS EXISTS
---------------
`docs/refactor-2026-08/03-solver-decomposition.md` proposes cutting crates out
of `axeyum-solver`. A cut point with a dependency cycle across it is not a cut
point, so the proposal needs a *measured* graph, and three separate naive
measurements of that graph were wrong before this script existed:

1. A `grep 'crate::(\\w+)'` sweep counts **rustdoc intra-doc links**
   (``[`crate::qfbv_alethe::foo`]``) as dependencies. On this crate that
   invented 231 edges and inflated the largest cycle from 23 modules to 55.
2. It also counts `#[cfg(test)]` code. `dl_online -> evidence` exists only in
   `dl_online/tests.rs`, which is a test module, not a dependency of the crate.
3. Stripping both still **undercounts**, because this crate imports through its
   own 267-entry re-export facade: `array_bv_abs.rs` says
   `use crate::{Evidence, SolverConfig};`, not `use crate::evidence::...`. Six
   hundred item names resolve back to a defining module that no `crate::<mod>`
   path ever names. Ignoring them hid 340 real edges and split one 65-module
   cycle into fragments that looked extractable.

So: strip comments and string literals, strip `#[cfg(test)]` items (including
test-only files reached through `#[cfg(test)] mod tests;`), resolve every
facade re-export in `lib.rs` back to its defining module, and only then build
the graph.

WHAT IT ENFORCES (`--check`)
----------------------------
* **No new module may enter a dependency cycle.** The in-cycle set may shrink
  freely; gaining a member fails. Set comparison, not a count, so a swap that
  keeps the total constant is still caught.
* **The evidence/reconstruction layer stays a layer.** The baseline records
  which modules sit above the theory core with *zero* edges pointing back down
  into them from outside. That zero is the entire precondition for extracting
  a proof/evidence crate (candidate `D1`); if it stops being zero, the
  boundary has silently closed and the plan needs rewriting, not the code.
* **Coverage floors.** Every number this script prints is also a number it
  refuses to go below. A refactor that renames `src/` out from under it, or a
  parser change that stops matching, would otherwise print a clean bill of
  health over nothing -- the failure mode this repository has shipped more
  often than any solver bug.

Usage:
    scripts/analyze_solver_module_graph.py                 # report
    scripts/analyze_solver_module_graph.py --check         # ratchet (gate)
    scripts/analyze_solver_module_graph.py --write-baseline
    scripts/analyze_solver_module_graph.py --src DIR --json OUT
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from collections import defaultdict

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_SRC = os.path.join(REPO, "crates", "axeyum-solver", "src")
DEFAULT_BASELINE = os.path.join(
    REPO, "docs", "refactor-2026-08", "solver-module-graph-baseline.json"
)

# See `check()`: the floors catch a tool that stopped looking, not a refactor.
COVERAGE_TOLERANCE = 0.8


# --------------------------------------------------------------------------
# Lexing: remove everything that is not code.
# --------------------------------------------------------------------------


def strip_comments(text: str) -> str:
    """Blank out comments, string literals, and char literals.

    Newlines are preserved so byte offsets still map to line numbers. Doc
    comments are comments: an intra-doc link is not a dependency.
    """
    out: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        raw = re.match(r'r(#*)"', text[i:])
        if raw and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_")):
            hashes = len(raw.group(1))
            j = i + len(raw.group(0))
            end = text.find('"' + "#" * hashes, j)
            j = n if end < 0 else end + 1 + hashes
            out.append("".join(c if c == "\n" else " " for c in text[i:j]))
            i = j
            continue
        if ch == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == '"':
                    j += 1
                    break
                j += 1
            out.append("".join(c if c == "\n" else " " for c in text[i:j]))
            i = j
            continue
        if ch == "'" and i + 2 < n and text[i + 1] != "\\" and text[i + 2] == "'":
            out.append("   ")
            i += 3
            continue
        if ch == "/" and i + 1 < n and text[i + 1] == "/":
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
            continue
        if ch == "/" and i + 1 < n and text[i + 1] == "*":
            depth = 1
            j = i + 2
            while j < n and depth > 0:
                if text[j] == "/" and j + 1 < n and text[j + 1] == "*":
                    depth += 1
                    j += 2
                elif text[j] == "*" and j + 1 < n and text[j + 1] == "/":
                    depth -= 1
                    j += 2
                else:
                    j += 1
            out.append("".join(c if c == "\n" else " " for c in text[i:j]))
            i = j
            continue
        out.append(ch)
        i += 1
    return "".join(out)


CFG_TEST = re.compile(r"#\[cfg\((?:test|all\(\s*test\b[^)]*\))\)\]")
ATTR_START = re.compile(r"\s*#")


def strip_cfg_test(text: str) -> tuple[str, set[str]]:
    """Blank out every `#[cfg(test)]` item.

    Returns the surviving text and the names of modules declared
    `#[cfg(test)] mod <name>;`, whose backing files are test-only.
    """
    test_mods: set[str] = set()
    out = list(text)
    for match in CFG_TEST.finditer(text):
        i = match.end()
        # Skip whitespace and any further attributes on the same item.
        while True:
            while i < len(text) and text[i] in " \t\r\n":
                i += 1
            if i < len(text) and text[i] == "#":
                depth = 0
                j = i
                while j < len(text):
                    if text[j] == "[":
                        depth += 1
                    elif text[j] == "]":
                        depth -= 1
                        if depth == 0:
                            j += 1
                            break
                    j += 1
                i = j
                continue
            break
        decl = re.match(
            r"(pub(\([^)]*\))?\s+)?mod\s+([A-Za-z_][A-Za-z0-9_]*)\s*;", text[i:]
        )
        if decl:
            test_mods.add(decl.group(3))
            end = i + decl.end()
        else:
            j = i
            end = None
            while j < len(text):
                if text[j] == "{":
                    depth = 0
                    while j < len(text):
                        if text[j] == "{":
                            depth += 1
                        elif text[j] == "}":
                            depth -= 1
                            if depth == 0:
                                j += 1
                                break
                        j += 1
                    end = j
                    break
                if text[j] == ";":
                    end = j + 1
                    break
                j += 1
            if end is None:
                end = len(text)
        for k in range(match.start(), end):
            if out[k] != "\n":
                out[k] = " "
    return "".join(out), test_mods


# --------------------------------------------------------------------------
# Graph construction
# --------------------------------------------------------------------------

FACADE_RE = re.compile(
    r"pub\s+use\s+((?:crate::)?[A-Za-z_][A-Za-z0-9_:]*)::(\{[^}]*\}|[A-Za-z_][A-Za-z0-9_]*)\s*;"
)
PATH_RE = re.compile(r"\bcrate::([A-Za-z_][A-Za-z0-9_]*)")
BRACE_USE_RE = re.compile(r"\buse\s+crate::\{([^}]*)\}")


def top_level_modules(src: str) -> set[str]:
    mods = set()
    for entry in os.listdir(src):
        path = os.path.join(src, entry)
        if entry.endswith(".rs") and entry != "lib.rs":
            mods.add(entry[:-3])
        elif os.path.isdir(path):
            mods.add(entry)
    return mods


def facade_map(src: str, mods: set[str]) -> dict[str, str]:
    """Map every item re-exported by `lib.rs` to the module that defines it.

    This is what turns `use crate::{Evidence, SolverConfig};` into the edges
    `-> evidence` and `-> backend`. Without it the graph is a fiction.
    """
    lib_path = os.path.join(src, "lib.rs")
    if not os.path.exists(lib_path):
        return {}
    with open(lib_path, encoding="utf-8", errors="replace") as handle:
        lib = strip_comments(handle.read())
    facade: dict[str, str] = {}
    for match in FACADE_RE.finditer(lib):
        path = match.group(1)
        if path.startswith("crate::"):
            path = path[len("crate::") :]
        top = path.split("::")[0]
        if top not in mods:
            continue
        body = match.group(2)
        items = (
            [x.strip() for x in body[1:-1].split(",")]
            if body.startswith("{")
            else [body]
        )
        for item in items:
            if " as " in item:
                item = item.split(" as ")[-1]
            item = item.strip()
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", item):
                facade.setdefault(item, top)
    return facade


def owner(src: str, path: str) -> str:
    head = os.path.relpath(path, src).split(os.sep)[0]
    return head[:-3] if head.endswith(".rs") else head


def build_graph(src: str) -> dict:
    mods = top_level_modules(src)
    facade = facade_map(src, mods)

    files = []
    for root, _dirs, names in os.walk(src):
        files.extend(os.path.join(root, n) for n in names if n.endswith(".rs"))
    files.sort()

    kept_text: dict[str, str] = {}
    test_files: set[str] = set()
    for path in files:
        with open(path, encoding="utf-8", errors="replace") as handle:
            raw = handle.read()
        kept, test_mods = strip_cfg_test(strip_comments(raw))
        kept_text[path] = kept
        directory = os.path.dirname(path)
        stem = os.path.splitext(os.path.basename(path))[0]
        subdir = os.path.join(directory, stem)
        for name in test_mods:
            for candidate in (
                os.path.join(subdir, name + ".rs"),
                os.path.join(directory, name + ".rs"),
                os.path.join(subdir, name, "mod.rs"),
            ):
                if os.path.exists(candidate):
                    test_files.add(os.path.realpath(candidate))

    lines: dict[str, int] = defaultdict(int)
    edges: dict[str, dict[str, int]] = defaultdict(lambda: defaultdict(int))
    detail: dict[str, list] = defaultdict(list)
    scanned = 0

    for path in files:
        who = owner(src, path)
        if who == "lib":
            continue
        if os.path.realpath(path) in test_files:
            continue
        scanned += 1
        kept = kept_text[path]
        lines[who] += kept.count("\n")
        rel = os.path.relpath(path, src)

        def record(target: str, pos: int) -> None:
            if target in mods and target != who:
                edges[who][target] += 1
                if len(detail[f"{who}|{target}"]) < 4:
                    detail[f"{who}|{target}"].append(
                        [rel, kept[:pos].count("\n") + 1]
                    )

        for match in PATH_RE.finditer(kept):
            name = match.group(1)
            if name in mods:
                record(name, match.start())
            elif name in facade:
                record(facade[name], match.start())
        for match in BRACE_USE_RE.finditer(kept):
            for item in match.group(1).split(","):
                head = item.strip().split("::")[0].strip()
                if not head:
                    continue
                if head in mods:
                    record(head, match.start())
                elif head in facade:
                    record(facade[head], match.start())

    return {
        "modules": sorted(mods),
        "lines": dict(lines),
        "edges": {k: dict(v) for k, v in sorted(edges.items())},
        "detail": dict(detail),
        "files_scanned": scanned,
        "test_files_skipped": len(test_files),
        "facade_items": len(facade),
        "edge_count": sum(sum(v.values()) for v in edges.values()),
    }


def strongly_connected(graph: dict) -> list[list[str]]:
    """Tarjan, iterative (the graph is wide and Python's stack is not)."""
    succ = {k: sorted(v) for k, v in graph["edges"].items()}
    nodes = sorted(graph["modules"])
    index: dict[str, int] = {}
    low: dict[str, int] = {}
    on_stack: dict[str, bool] = {}
    stack: list[str] = []
    counter = [0]
    comps: list[list[str]] = []

    def walk(root: str) -> None:
        work = [(root, 0)]
        while work:
            node, child = work[-1]
            if child == 0:
                index[node] = low[node] = counter[0]
                counter[0] += 1
                stack.append(node)
                on_stack[node] = True
            recursed = False
            kids = succ.get(node, [])
            for i in range(child, len(kids)):
                kid = kids[i]
                if kid not in index:
                    work[-1] = (node, i + 1)
                    work.append((kid, 0))
                    recursed = True
                    break
                if on_stack.get(kid):
                    low[node] = min(low[node], index[kid])
            if recursed:
                continue
            if low[node] == index[node]:
                comp = []
                while True:
                    top = stack.pop()
                    on_stack[top] = False
                    comp.append(top)
                    if top == node:
                        break
                comps.append(sorted(comp))
            work.pop()
            if work:
                parent = work[-1][0]
                low[parent] = min(low[parent], low[node])

    for node in nodes:
        if node not in index:
            walk(node)
    return comps


def summarize(graph: dict, layer: list[str]) -> dict:
    comps = strongly_connected(graph)
    cycles = sorted((c for c in comps if len(c) > 1), key=lambda c: (-len(c), c[0]))
    in_cycles = sorted({m for c in cycles for m in c})
    layer_set = set(layer)
    intruders = []
    for source, targets in graph["edges"].items():
        if source in layer_set:
            continue
        for target in targets:
            if target in layer_set:
                intruders.append(f"{source} -> {target}")
    largest = set(cycles[0]) if cycles else set()
    from_core = sorted(e for e in intruders if e.split(" -> ")[0] in largest)
    return {
        "modules": len(graph["modules"]),
        "files_scanned": graph["files_scanned"],
        "test_files_skipped": graph["test_files_skipped"],
        "facade_items": graph["facade_items"],
        "edge_count": graph["edge_count"],
        "cycles": [
            {"size": len(c), "lines": sum(graph["lines"].get(m, 0) for m in c), "modules": c}
            for c in cycles
        ],
        "modules_in_cycles": in_cycles,
        "evidence_layer": sorted(layer_set),
        "edges_into_evidence_layer": sorted(intruders),
        "edges_from_largest_cycle_into_evidence_layer": from_core,
    }


DEFAULT_LAYER = [
    "array_bv_abs",
    "evidence",
    "int_reconstruct",
    "reconstruct",
    "regex_reconstruct",
    "smtlib",
    "word_reconstruct",
]


def report(summary: dict, graph: dict) -> None:
    print("axeyum-solver intra-crate module graph")
    print(f"  modules             {summary['modules']}")
    print(f"  files scanned       {summary['files_scanned']}")
    print(f"  test files skipped  {summary['test_files_skipped']}")
    print(f"  facade items mapped {summary['facade_items']}")
    print(f"  code edges          {summary['edge_count']}")
    print(f"  modules in cycles   {len(summary['modules_in_cycles'])}")
    total = sum(graph["lines"].values())
    print(f"  code lines (no comments/tests) {total}")
    print()
    for cycle in summary["cycles"]:
        pct = 100.0 * cycle["lines"] / total if total else 0.0
        print(f"  cycle of {cycle['size']:>3} modules, {cycle['lines']:>7} lines ({pct:.1f}%)")
        print(f"      {', '.join(cycle['modules'])}")
    print()
    print(f"  evidence layer      {', '.join(summary['evidence_layer'])}")
    print(f"  edges into it from outside: {len(summary['edges_into_evidence_layer'])}")
    for edge in summary["edges_into_evidence_layer"]:
        print(f"      {edge}")
    core = summary["edges_from_largest_cycle_into_evidence_layer"]
    print(
        f"  of which from the largest cycle (the theory core): {len(core)}"
        + ("" if core else "  <- the layer is one-way over the core")
    )
    for edge in core:
        print(f"      {edge}")


def check(summary: dict, baseline: dict) -> int:
    failures = []

    # Coverage floors are PROPORTIONAL, not exact. Breaking a cycle removes an
    # edge, and a gate that failed on that would punish exactly the work it
    # exists to encourage. What must never happen is the tool quietly measuring
    # nothing -- a renamed `src/`, a parser that stopped matching, a crate moved
    # out from under it. Those collapse the numbers to near zero, not by 20%.
    for field in ("modules", "files_scanned", "facade_items", "edge_count"):
        recorded = baseline["coverage_floor"][field]
        if recorded == 0:
            continue
        floor = max(1, int(recorded * COVERAGE_TOLERANCE))
        got = summary[field]
        if got < floor:
            failures.append(
                f"COVERAGE: {field} = {got}, below {floor} "
                f"({COVERAGE_TOLERANCE:.0%} of the recorded {recorded}). "
                "This gate may be looking at the wrong tree or have stopped parsing."
            )

    base_cycles = set(baseline["modules_in_cycles"])
    now_cycles = set(summary["modules_in_cycles"])
    entered = sorted(now_cycles - base_cycles)
    if entered:
        failures.append(
            "NEW CYCLE MEMBERS: "
            + ", ".join(entered)
            + " -- a module that was acyclic now sits in a dependency cycle. "
            "That closes a cut point; see docs/refactor-2026-08/03-solver-decomposition.md."
        )

    base_intruders = set(baseline["edges_into_evidence_layer"])
    now_intruders = set(summary["edges_into_evidence_layer"])
    new_intruders = sorted(now_intruders - base_intruders)
    if new_intruders:
        failures.append(
            "EVIDENCE LAYER BACK-EDGE: "
            + ", ".join(new_intruders)
            + " -- something outside the evidence/reconstruction layer now "
            "depends on it. That layer being one-way is the whole precondition "
            "for extracting it as a crate (candidate D1)."
        )

    from_core = sorted(
        set(summary["edges_from_largest_cycle_into_evidence_layer"])
        - set(baseline.get("edges_from_largest_cycle_into_evidence_layer", []))
    )
    if from_core:
        failures.append(
            "THEORY CORE -> EVIDENCE LAYER: "
            + ", ".join(from_core)
            + " -- the largest dependency cycle (the theory core) now reaches "
            "up into the evidence layer. The two were strictly ordered; they "
            "are now one component."
        )

    left = sorted(base_cycles - now_cycles)
    gone = sorted(base_intruders - now_intruders)
    if left:
        print(f"progress: {len(left)} module(s) left the cycle set: {', '.join(left)}")
    if gone:
        print(f"progress: {len(gone)} back-edge(s) removed: {', '.join(gone)}")
    if left or gone:
        print("Re-run with --write-baseline to ratchet the improvement in.")

    if failures:
        print()
        for failure in failures:
            print(f"FAIL: {failure}")
        return 1
    print(
        f"OK: {summary['modules']} modules, {summary['edge_count']} edges, "
        f"{len(summary['modules_in_cycles'])} in cycles, "
        f"{len(summary['edges_into_evidence_layer'])} back-edges into the evidence layer."
    )
    return 0


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--src", default=DEFAULT_SRC)
    parser.add_argument("--baseline", default=DEFAULT_BASELINE)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--write-baseline", action="store_true")
    parser.add_argument("--json", help="dump the full graph (with edge call sites)")
    parser.add_argument(
        "--layer",
        help="comma-separated evidence-layer modules (default: the recorded layer)",
    )
    args = parser.parse_args(argv)

    if not os.path.isdir(args.src):
        print(f"FAIL: no such source directory: {args.src}", file=sys.stderr)
        return 2

    graph = build_graph(args.src)
    if args.layer is not None:
        layer = [m for m in args.layer.split(",") if m]
    elif os.path.exists(args.baseline):
        with open(args.baseline, encoding="utf-8") as handle:
            layer = json.load(handle).get("evidence_layer", DEFAULT_LAYER)
    else:
        layer = DEFAULT_LAYER
    summary = summarize(graph, layer)

    if args.json:
        with open(args.json, "w", encoding="utf-8") as handle:
            json.dump(graph, handle, indent=1, sort_keys=True)

    if args.write_baseline:
        payload = {
            "_comment": (
                "Generated by scripts/analyze_solver_module_graph.py "
                "--write-baseline. Ratchet for docs/refactor-2026-08/"
                "03-solver-decomposition.md. Regenerate only to record an "
                "IMPROVEMENT; a regression must be fixed, not re-baselined."
            ),
            "coverage_floor": {
                "modules": summary["modules"],
                "files_scanned": summary["files_scanned"],
                "facade_items": summary["facade_items"],
                "edge_count": summary["edge_count"],
            },
            "modules_in_cycles": summary["modules_in_cycles"],
            "cycles": [
                {"size": c["size"], "modules": c["modules"]} for c in summary["cycles"]
            ],
            "evidence_layer": summary["evidence_layer"],
            "edges_into_evidence_layer": summary["edges_into_evidence_layer"],
            "edges_from_largest_cycle_into_evidence_layer": summary[
                "edges_from_largest_cycle_into_evidence_layer"
            ],
        }
        with open(args.baseline, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=1, sort_keys=True)
            handle.write("\n")
        print(f"wrote {args.baseline}")
        report(summary, graph)
        return 0

    if args.check:
        if not os.path.exists(args.baseline):
            print(f"FAIL: no baseline at {args.baseline}", file=sys.stderr)
            return 2
        with open(args.baseline, encoding="utf-8") as handle:
            baseline = json.load(handle)
        report(summary, graph)
        print()
        return check(summary, baseline)

    report(summary, graph)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
