#!/usr/bin/env python3
"""Decide whether a proposed `axeyum-solver` module GROUP can become a directory.

WHY THIS EXISTS
---------------
`docs/refactor-2026-08/03-solver-decomposition.md` item `D3` proposes making
each theory group a directory module. On 2026-08-17 a lane measured the four
proposed groups and refuted three of them, reporting `arithmetic: 34 modules,
ratio 0.247, p=0.002 / 0.045 -- a real cluster`. That measurement **committed no
script**, so its group membership is unrecoverable from the repository, and the
next lane to act on it could not reproduce the number it was told to act on.
This file is that measurement as code. Two things it adds:

1. **A membership rule you can read.** Cohesion is not a property of "the
   arithmetic group"; it is a property of a particular set of modules. Sweeping
   the plausible boundaries (`--sweep`) moves the arithmetic verdict from
   p < 0.0001 to p = 0.38 without any code changing. A ratio quoted without its
   membership is not a measurement.

2. **The collapse simulation, which is the part that actually decides.** A
   directory is ONE node in `analyze_solver_module_graph.py`'s graph:
   `top_level_modules` lists `src/` entries and `owner()` takes the first path
   component, so `src/arith/lia.rs` and `src/arith/nra.rs` are both module
   `arith`. Grouping therefore *merges* nodes, and merging nodes creates cycles
   between whatever the members separately touched. That is invisible to a
   cohesion ratio and it is exactly what the ratchet forbids.

   So this runs the real `summarize()` and the real `check()` from the ratchet
   against the *simulated post-move* graph, and exits non-zero when the move
   would turn the gate red -- before any file is moved.

WHAT IT ENFORCES
----------------
Exit status is the finding, not "the script ran":

  0  the proposed group can be collapsed into a directory with the module-graph
     ratchet still green AND without growing the largest dependency cycle
  1  it cannot -- the failures are printed, from the ratchet's own `check()`
  2  usage / missing baseline

The cycle-MASS check is additional to the ratchet on purpose. The ratchet
counts modules in cycles; `D1` was mis-ranked for exactly that reason ("Direction
was never the obstacle; mass was, and nothing was watching mass"). Collapsing a
group moves the group's whole line count into one node, so a grouping can leave
the module count nearly unchanged while nearly doubling the mass of the largest
cycle. Measured for arithmetic: 24 -> 25 modules, 58,215 -> 103,514 lines.

Usage:
    scripts/analyze_solver_group_collapse.py --group arith-core
    scripts/analyze_solver_group_collapse.py --group arith-core --check
    scripts/analyze_solver_group_collapse.py --sweep
    scripts/analyze_solver_group_collapse.py --modules lia,lra,simplex --check
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import random
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
_SCRIPT = os.path.join(REPO, "scripts", "analyze_solver_module_graph.py")
_spec = importlib.util.spec_from_file_location("solver_module_graph", _SCRIPT)
assert _spec and _spec.loader
mg = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(mg)

TRIALS = 20000
SEED = 20260817

# ---------------------------------------------------------------------------
# Named groups. Each is a LITERAL module list, not a regex, because a regex is
# a rule you have to re-derive and these are the sets the numbers refer to.
# ---------------------------------------------------------------------------

ARITH_CORE = [
    "alethe_lra", "cas_certificate", "cas_poly", "combined_theory_lia",
    "dl_online", "dpll_lia", "int_real_relax", "lia", "lia_gcd", "lia_online",
    "lia_theory", "lra", "lra_online", "lra_theory", "nia_linearize",
    "nia_square", "nra", "nra_even_power", "nra_real_root", "simplex",
    "uf_arith", "uflia_online", "uflra_online",
]
ARITH_INTERPOLANTS = [
    "lia_interpolant", "lia_interpolant_cnf", "lra_interpolant_cnf",
    "qfuflia_alethe", "uflia_interpolant", "uflra_interpolant",
]
ARITH_MODEL_CHECKING = ["imc", "imc_lia", "imc_lra", "pdr", "pdr_lia", "pdr_lra"]
ARITH_OPTIMIZATION = ["optimize", "pb", "pbls"]
# `int_reconstruct` matches an `int` name rule and is in the EVIDENCE LAYER.
# The doc's stated precedence (arithmetic before evidence) puts it here; the
# baseline's layer definition puts it there. It cannot be both, which is one
# reason the unrecorded rule matters.
ARITH_EVIDENCE = ["int_reconstruct"]

GROUPS = {
    "arith-core": ARITH_CORE,
    "arith-interp": ARITH_CORE + ARITH_INTERPOLANTS,
    "arith-interp-mc": ARITH_CORE + ARITH_INTERPOLANTS + ARITH_MODEL_CHECKING,
    "arith-wide": (ARITH_CORE + ARITH_INTERPOLANTS + ARITH_MODEL_CHECKING
                   + ARITH_OPTIMIZATION),
    "arith-maximal": (ARITH_CORE + ARITH_INTERPOLANTS + ARITH_MODEL_CHECKING
                      + ARITH_OPTIMIZATION + ARITH_EVIDENCE),
    # The three groups the 2026-08-17 measurement refuted, kept so the refutation
    # stays runnable rather than only quoted.
    "strings": ["strings", "string_theory", "word_alethe", "word_reconstruct",
                "lex_reconstruct", "regex_reconstruct"],
    "uf": ["euf", "euf_egraph", "euf_alethe", "uf_arith", "uf_fmf"],
}

SWEEP = ["arith-core", "arith-interp", "arith-interp-mc", "arith-wide",
         "arith-maximal", "uf", "strings"]


# ---------------------------------------------------------------------------
# Cohesion
# ---------------------------------------------------------------------------


def directed_edges(graph: dict) -> set[tuple[str, str]]:
    return {(s, t) for s, targets in graph["edges"].items() for t in targets}


def cohesion(edges: set[tuple[str, str]], lines: dict, group) -> dict:
    members = set(group)
    internal = sum(1 for s, t in edges if s in members and t in members)
    out = sum(1 for s, t in edges if s in members and t not in members)
    inn = sum(1 for s, t in edges if s not in members and t in members)
    crossing = out + inn
    return {
        "n": len(members),
        "lines": sum(lines.get(m, 0) for m in members),
        "internal": internal,
        "out": out,
        "in": inn,
        "crossing": crossing,
        "ratio": internal / crossing if crossing else 0.0,
    }


def quintiles(graph: dict, edges: set[tuple[str, str]]) -> dict[str, int]:
    """Total-degree quintile per module, so hubs are compared against hubs."""
    degree = {m: 0 for m in graph["modules"]}
    for source, target in edges:
        degree[source] += 1
        degree[target] += 1
    order = sorted(degree, key=lambda m: (degree[m], m))
    return {m: (i * 5) // len(order) for i, m in enumerate(order)}


def nulls(graph: dict, edges, lines, group, trials: int = TRIALS) -> dict:
    """Uniform and degree-quintile-matched nulls at fixed group size."""
    observed = cohesion(edges, lines, group)["ratio"]
    pool = sorted(graph["modules"])
    size = len(group)

    rng = random.Random(SEED)
    total = 0.0
    hits = 0
    for _ in range(trials):
        ratio = cohesion(edges, lines, rng.sample(pool, size))["ratio"]
        total += ratio
        hits += ratio >= observed

    quint = quintiles(graph, edges)
    by_quint: dict[int, list[str]] = {}
    for module, q in quint.items():
        by_quint.setdefault(q, []).append(module)
    for q in by_quint:
        by_quint[q].sort()
    want: dict[int, int] = {}
    for module in group:
        want[quint[module]] = want.get(quint[module], 0) + 1

    rng = random.Random(SEED)
    dq_total = 0.0
    dq_hits = 0
    for _ in range(trials):
        pick: list[str] = []
        for q, k in want.items():
            pick += rng.sample(by_quint[q], k)
        ratio = cohesion(edges, lines, pick)["ratio"]
        dq_total += ratio
        dq_hits += ratio >= observed

    return {
        "observed": observed,
        "uniform_mean": total / trials,
        "uniform_p": hits / trials,
        "degree_matched_mean": dq_total / trials,
        "degree_matched_p": dq_hits / trials,
        "trials": trials,
    }


# ---------------------------------------------------------------------------
# The collapse
# ---------------------------------------------------------------------------


def collapse(graph: dict, group, label: str) -> dict:
    """The graph as it would be AFTER `src/<label>/` swallows every member.

    Faithful to `analyze_solver_module_graph.py`: a directory is one module, so
    member->member edges vanish and every member's outward edge becomes the
    directory's. Line counts add up into the one node -- which is the point.
    """
    members = set(group)
    collapsed: dict = {
        "modules": sorted((set(graph["modules"]) - members) | {label}),
        "lines": {},
        "edges": {},
        "detail": {},
        "files_scanned": graph["files_scanned"],
        "test_files_skipped": graph["test_files_skipped"],
        "facade_items": graph["facade_items"],
        "edge_count": 0,
    }
    for module, count in graph["lines"].items():
        key = label if module in members else module
        collapsed["lines"][key] = collapsed["lines"].get(key, 0) + count
    for source, targets in graph["edges"].items():
        src = label if source in members else source
        for target, count in targets.items():
            dst = label if target in members else target
            if src == dst:
                continue
            collapsed["edges"].setdefault(src, {})
            collapsed["edges"][src][dst] = collapsed["edges"][src].get(dst, 0) + count
    collapsed["edge_count"] = sum(sum(v.values()) for v in collapsed["edges"].values())
    return collapsed


def largest_cycle_mass(summary: dict) -> tuple[int, int]:
    if not summary["cycles"]:
        return 0, 0
    return summary["cycles"][0]["size"], summary["cycles"][0]["lines"]


def evaluate(graph: dict, baseline: dict, group, label: str) -> dict:
    layer = baseline["evidence_layer"]
    before = mg.summarize(graph, layer)
    after = mg.summarize(collapse(graph, group, label), layer)
    entered = sorted(set(after["modules_in_cycles"]) - set(baseline["modules_in_cycles"]))
    before_size, before_mass = largest_cycle_mass(before)
    after_size, after_mass = largest_cycle_mass(after)
    return {
        "before": before,
        "after": after,
        "entered_cycles": entered,
        "before_cycle": (before_size, before_mass),
        "after_cycle": (after_size, after_mass),
    }


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------


def report_group(name: str, graph, edges, lines, baseline, group, label, run_nulls):
    print(f"=== {name}: {len(group)} modules ===")
    stats = cohesion(edges, lines, group)
    print(f"  modules {stats['n']}, {stats['lines']} code lines")
    print(f"  internal {stats['internal']}, crossing {stats['crossing']} "
          f"({stats['out']} out / {stats['in']} in), ratio {stats['ratio']:.3f}")
    if run_nulls:
        n = nulls(graph, edges, lines, group)
        print(f"  uniform null        mean {n['uniform_mean']:.3f}  "
              f"p = {n['uniform_p']:.4f}")
        print(f"  degree-matched null mean {n['degree_matched_mean']:.3f}  "
              f"p = {n['degree_matched_p']:.4f}   ({n['trials']} trials, seed {SEED})")

    result = evaluate(graph, baseline, group, label)
    after = result["after"]
    bs, bm = result["before_cycle"]
    as_, am = result["after_cycle"]
    print(f"  -- collapsed into src/{label}/ --")
    print(f"  modules {result['before']['modules']} -> {after['modules']}, "
          f"call sites {result['before']['edge_count']} -> {after['edge_count']}")
    print(f"  in cycles {len(result['before']['modules_in_cycles'])} -> "
          f"{len(after['modules_in_cycles'])}")
    print(f"  largest cycle {bs} modules / {bm} lines -> "
          f"{as_} modules / {am} lines")
    if result["entered_cycles"]:
        print(f"  newly in a cycle: {', '.join(result['entered_cycles'])}")
    return result


def verdict(result: dict, baseline: dict, label: str) -> int:
    """Non-zero when the proposed grouping would turn the gate red."""
    print()
    status = mg.check(result["after"], baseline)
    _, before_mass = result["before_cycle"]
    _, after_mass = result["after_cycle"]
    if after_mass > before_mass:
        factor = f"{after_mass / before_mass:.2f}x" if before_mass else "from nothing"
        print(
            f"FAIL: LARGEST CYCLE GREW: {before_mass} -> {after_mass} lines "
            f"({factor}) -- the group's whole mass is now "
            "one node inside the theory core's dependency cycle. The module "
            "count barely moves; the mass is what blocks a later crate cut. See "
            "docs/refactor-2026-08/03-solver-decomposition.md D1."
        )
        status = 1
    if status == 0:
        print(f"OK: src/{label}/ can be created without turning the gate red.")
    else:
        print(f"REFUSED: do not create src/{label}/ -- see the failures above.")
    return status


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--src", default=mg.DEFAULT_SRC)
    parser.add_argument("--baseline", default=mg.DEFAULT_BASELINE)
    parser.add_argument("--group", choices=sorted(GROUPS), help="a named group")
    parser.add_argument("--modules", help="comma-separated module names")
    parser.add_argument("--label", default="arith", help="directory name")
    parser.add_argument("--sweep", action="store_true",
                        help="every named group, cohesion + collapse")
    parser.add_argument("--check", action="store_true",
                        help="exit non-zero if the grouping would turn the gate red")
    parser.add_argument("--no-nulls", action="store_true", help="skip the null models")
    args = parser.parse_args(argv)

    if not os.path.isdir(args.src):
        print(f"FAIL: no such source directory: {args.src}", file=sys.stderr)
        return 2
    if not os.path.exists(args.baseline):
        print(f"FAIL: no baseline at {args.baseline}", file=sys.stderr)
        return 2
    with open(args.baseline, encoding="utf-8") as handle:
        baseline = json.load(handle)

    graph = mg.build_graph(args.src)
    known = set(graph["modules"])
    edges = directed_edges(graph)
    lines = graph["lines"]
    print(f"axeyum-solver: {len(known)} modules, {len(edges)} distinct edges, "
          f"{graph['edge_count']} call sites, {sum(lines.values())} code lines\n")

    if args.sweep:
        for name in SWEEP:
            members = [m for m in GROUPS[name] if m in known]
            report_group(name, graph, edges, lines, baseline, members,
                         args.label, not args.no_nulls)
            print()
        return 0

    if args.modules:
        members = [m.strip() for m in args.modules.split(",") if m.strip()]
        name = "--modules"
    elif args.group:
        members = list(GROUPS[args.group])
        name = args.group
    else:
        parser.error("one of --group, --modules or --sweep is required")

    missing = [m for m in members if m not in known]
    if missing:
        # A group naming modules that do not exist would silently measure a
        # smaller set and report a cleaner answer. That is the empty-result trap.
        print(f"FAIL: not modules of this crate: {', '.join(missing)}", file=sys.stderr)
        return 2

    result = report_group(name, graph, edges, lines, baseline, members,
                          args.label, not args.no_nulls)
    if args.check:
        return verdict(result, baseline, args.label)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
