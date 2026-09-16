#!/usr/bin/env python3
"""QUANT-REACH-DIFF worked examples: DERIVE (not live-profile) the trigger
each side's shipped default algorithm selects for a given `forall` body, by
applying the documented algorithm by hand in Python.

This is necessary because neither side prints its chosen pattern in a form
this lane's tooling can capture without writing Rust (forbidden by this
lane's brief) or a z3 build with trace macros enabled (this host's
`/usr/bin/z3` rejects `-tr:*`; verified: `z3 -tr:trigger ...` ->
"invalid command line option: -tr"). `smt.qi.profile=true` (`-v:5`) prints
only per-quantifier instantiation COUNTS (`[quantifier_instances] k!N :
count : cost : max-generation : avg`), never the pattern term itself --
verified on this host, see `bench-results/quant-reach-diff-20260916/README.md`
worked-examples section.

Both derivations are DETERMINISTIC re-implementations of the cited
algorithms, applied to the SAME source `forall` body text (ADR-2113 4a):

  ours: `select_triggers`, `crates/axeyum-solver/src/qinst_egraph.rs:9765`.
        Pre-order walk of `Op::Apply` subterms
        (`collect_app_candidates:10095`, which explicitly stops at a nested
        forall/exists, matching this script's `collect_candidates`); the
        FIRST candidate covering every bound variable wins, no ranking. Falls
        back to greedy set cover if no single candidate is full-cover.

  z3:   `pattern_inference.cpp` (this host has no z3 clone under
        `references/`; read from the MAIN checkout, read-only, per this
        lane's brief). `candidates2unary_patterns` (`:458-467`) makes every
        full-cover candidate its own alternative; `filter_bigger_patterns`
        (`:391-396`) keeps only the MINIMAL ones (drops a candidate that
        properly contains another full-cover candidate); `pattern_weight_lt`
        (`:399-408`) ranks by (more free variables [tied here -- both cover
        all vars], then SMALLEST size). This script's `select_trigger_z3`
        implements exactly that ranking, `witness_size` counting AST nodes
        as a stand-in for z3's own internal weight.

Neither derivation handles multi-patterns, `filter_looping_patterns`, or
ground-subterm exclusion -- ADR-2113 4a's own finding is that trigger
ALTERNATIVES are not the blocker (0 of 478 NEVER-MATCHED universals), so a
single-pattern approximation is what the worked examples need.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("z3_proof_instances", HERE.parent.parent / "scripts" / "z3-proof-instances.py")
assert SPEC is not None and SPEC.loader is not None
Z3PI = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(Z3PI)

INTERPRETED = {
    "+", "-", "*", "div", "mod", "abs", "<=", "<", ">=", ">", "=", "distinct",
    "and", "or", "not", "=>", "xor", "ite", "let", "true", "false",
    "forall", "exists", "!", "_",
}


def free_vars_in(node, bound_names: set, acc: set) -> None:
    if isinstance(node, str):
        if node in bound_names:
            acc.add(node)
        return
    if not node:
        return
    head = node[0]
    if isinstance(head, str) and head in ("forall", "exists"):
        return
    for child in node:
        free_vars_in(child, bound_names, acc)


def collect_candidates(node, bound_names: set, out: list) -> None:
    if isinstance(node, str) or not node:
        return
    head = node[0]
    if isinstance(head, str) and head in ("forall", "exists"):
        return
    if isinstance(head, str) and head not in INTERPRETED:
        acc: set = set()
        free_vars_in(node, bound_names, acc)
        if acc:
            out.append((node, acc))
    for child in node[1:]:
        collect_candidates(child, bound_names, out)


def witness_size(node) -> int:
    if isinstance(node, str):
        return 1
    return 1 + sum(witness_size(c) for c in node)


def is_proper_subterm(haystack, needle_render: str) -> bool:
    def search(n, top):
        if not top and Z3PI.render(n) == needle_render:
            return True
        if isinstance(n, list):
            return any(search(c, False) for c in n)
        return False

    return search(haystack, True)


def select_triggers_ours(body, bound_names: set):
    """Replica of `select_triggers` (`qinst_egraph.rs:9765`): first
    pre-order full-cover candidate, else greedy set cover."""
    candidates: list = []
    collect_candidates(body, bound_names, candidates)
    allv = set(bound_names)
    for node, cov in candidates:
        if cov == allv:
            return [node]
    uncovered = set(allv)
    chosen = []
    remaining = candidates[:]
    while uncovered:
        best = None
        best_n = -1
        for node, cov in remaining:
            n = len(cov & uncovered)
            if n > best_n:
                best = node
                best_n = n
                best_cov = cov
        if best is None or best_n <= 0:
            return None
        uncovered -= best_cov
        chosen.append(best)
    return chosen


def select_trigger_z3(body, bound_names: set):
    """Replica of z3's auto single-pattern selection: full-cover candidates,
    minimality filter, smallest-size tiebreak."""
    candidates: list = []
    collect_candidates(body, bound_names, candidates)
    allv = set(bound_names)
    full = []
    seen = set()
    for node, cov in candidates:
        if cov == allv:
            r = Z3PI.render(node)
            if r not in seen:
                seen.add(r)
                full.append(node)
    if not full:
        return select_triggers_ours(body, bound_names)
    minimal = [
        n
        for n in full
        # Drop the CONTAINER, keep the contained (z3's `filter_bigger_patterns`):
        # exclude `n` if some OTHER full-cover candidate `o` sits properly
        # inside `n` -- `n` is then the bigger one and every match of `n`
        # carries a match of `o`, so `o` is strictly cheaper to match.
        if not any(
            Z3PI.render(n) != Z3PI.render(o) and is_proper_subterm(n, Z3PI.render(o))
            for o in full
        )
    ]
    ranked = minimal if minimal else full
    ranked.sort(key=lambda n: (witness_size(n), Z3PI.render(n)))
    return [ranked[0]]


def main(argv: list) -> int:
    if len(argv) != 3:
        sys.stderr.write("trigger_derive.py <body.smt2-term> <space-separated-bound-vars>\n")
        return 2
    body_text = Path(argv[1]).read_text()
    bound_names = set(argv[2].split())
    body = Z3PI.parse(Z3PI.tokenize(body_text))
    ours = select_triggers_ours(body, bound_names)
    z3t = select_trigger_z3(body, bound_names)
    print("ours:", [Z3PI.render(n) for n in (ours or [])])
    print("z3:  ", [Z3PI.render(n) for n in (z3t or [])])
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
