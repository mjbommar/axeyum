#!/usr/bin/env python3
"""Derive a kernel-route fact's `depends_on` from the proof term, not from prose.

CLAUDE.md's flywheel ends with *"the concept DAG and the fact ledger say what to
prove next"*. That arrow is `depends_on`, and it is the weakest one:
`check-fact-dag.py` measures **65 of 109 facts isolated** — neither resting on
anything nor supporting anything — so proving one usually unlocks nothing.

Some of that is honest. An SMT-LIB propositional refutation really does not rest
on a Nat lemma, and `Nat.le_refl` really has no dependencies. But 13 of the
isolated facts are `kernel-lean`, and for those the truth is in the proof term:
measured 2026-08-17, `Nat.gcd_succ` uses `Nat.mod_lt` and `WellFounded.fix_eq`,
`Nat.mul_one` uses `Nat.zero_add`, and `Nat.add_sub_cancel_left` uses four
theorems — while all three declared nothing. Nothing could tell an honestly
isolated fact from an unrecorded one, because the information existed only
inside the kernel.

So this does not ask anyone to write dependencies down. It reads them out of the
admitted proof, via `Kernel::theorem_dependencies` (the half of the constant
closure `axiom_footprint` discards), and requires the ledger to agree. That is
ADR-0465's position — *the ledger is derived, not transcribed* — applied to the
other ledger column.

# What it enforces, and what it deliberately does not

ONLY this: if fact A's theorem directly uses theorem B, and B is itself a fact
in this ledger, then A must declare B in `depends_on`.

It does NOT require every used theorem to be a fact — most prelude lemmas are
not, and demanding a fact per lemma would be a bureaucratic bound on proving
things. It does NOT touch non-kernel routes, where `depends_on` means something
this script cannot see. And it does not object to a fact declaring MORE than the
proof term uses: a `depends_on` may record a mathematical dependency that the
mechanised proof happened to route around.

Reported, never inferred: theorem names come from each fact's own
`checker_command`, so a fact whose command stops naming a theorem drops out of
the enforced set rather than being silently assumed correct — and that drop-out
is itself reported.

The five that currently drop out are not a regex miss; I checked. Their evidence
is a Rust test invocation (`cargo test -p axeyum-lean-kernel --lib
rat_normalize_reduces_two_quarters_to_one_half`) or an example with a
`--require-empty`-style flag, rather than `nat_theorem_inventory -- <name>`. A
fact backed that way names no prelude theorem, so there is no proof term to read
a dependency out of, and enforcing against it would mean guessing. Widening the
name pattern would not help and would only make the guess look official.
"""

from __future__ import annotations

import json
import pathlib
import re
import subprocess
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts/facts"

KERNEL_ROUTES = {"kernel-lean"}
# `grep -qE '^Nat\.mul_one[[:space:]]'` and `grep -qxF 'Nat.pow_add<TAB>3<TAB>…'`
# A prelude theorem name as a checker command writes it. Three shapes, all real:
# `Nat.mul_one` plain; `Nat\.mul_one` escaped for a regex; and
# `Int[.]Characterization[.]categorical` bracket-escaped for `grep -E`, which is
# how the characterization facts write it. Segments repeat, because the names
# are namespaced — matching only ONE segment yields `Int.Characterization`,
# which is not a theorem, and the fact then drops out silently.
#
# Measured 2026-08-18: the single-segment form left 8 of 43 kernel-route facts
# unenforced, including every fact added that day.
# No apostrophe. Lean permits primed names, but a checker command quotes its
# grep pattern with `'`, so allowing one lets the name absorb the CLOSING QUOTE
# — `Int[.]Characterization[.]categorical'` is then looked up, is not in the
# graph, and the fact is silently skipped. Measured 2026-08-18: 0 of the 312
# theorems this kernel declares contain a prime, so excluding it costs nothing
# today. If a primed name ever appears, this must handle quoting rather than
# widening the class back.
_SEG = r"[A-Za-z0-9_]+"
_DOT = r"(?:\\?\.|\[\.\])"
THEOREM_RE = re.compile(
    rf"\^?((?:Nat|Int|Real|Rat|List|Bool|Prop|Acc|WellFounded|Str)(?:{_DOT}{_SEG})+)"
)


def inventory() -> dict[str, list[str]]:
    """`theorem -> [direct theorem dependency]`, read out of the kernel."""
    proc = subprocess.run(
        [
            "cargo", "run", "-q", "-p", "axeyum-lean-kernel",
            "--example", "theorem_dependency_inventory",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=1800,
        check=True,
    )
    graph: dict[str, list[str]] = {}
    for line in proc.stdout.splitlines():
        if not line.strip():
            continue
        name, _, deps = line.partition("\t")
        graph[name] = [d for d in deps.split(",") if d]
    return graph


def theorem_of(fact: dict[str, Any]) -> str | None:
    """The theorem a kernel-route fact is about, from its own checker command."""
    for item in fact.get("evidence") or []:
        found = THEOREM_RE.search(item.get("checker_command", ""))
        if found:
            return found.group(1).replace("\\", "").replace("[.]", ".")
    return None


def load() -> dict[str, dict[str, Any]]:
    return {
        json.loads(p.read_text(encoding="utf-8"))["id"]: json.loads(
            p.read_text(encoding="utf-8")
        )
        for p in sorted(FACTS.glob("*.json"))
    }


def evaluate(
    facts: dict[str, dict[str, Any]], graph: dict[str, list[str]]
) -> tuple[list[str], dict[str, Any]]:
    kernel_facts = {
        i: d
        for i, d in facts.items()
        if d.get("proof_route") in KERNEL_ROUTES
        and d.get("epistemic_status") in {"proved", "computed"}
    }
    theorem_to_fact: dict[str, str] = {}
    unnamed: list[str] = []
    for ident, data in kernel_facts.items():
        name = theorem_of(data)
        if name is None:
            unnamed.append(ident)
        else:
            theorem_to_fact.setdefault(name, ident)

    failures: list[str] = []
    missing_edges = 0
    for ident, data in kernel_facts.items():
        name = theorem_of(data)
        if name is None or name not in graph:
            continue
        declared = set(data.get("depends_on") or [])
        for used in graph[name]:
            needed = theorem_to_fact.get(used)
            if needed is None or needed == ident:
                continue
            if needed not in declared:
                missing_edges += 1
                failures.append(
                    f"{ident}: its theorem `{name}` directly uses `{used}`, which this "
                    f"ledger records as {needed}, but `depends_on` does not name it. "
                    "The dependency is in the proof term; the ledger should not have "
                    "to be told separately"
                )
    stats = {
        "kernel_facts": len(kernel_facts),
        "named_theorems": len(theorem_to_fact),
        "unnamed": unnamed,
        "missing_edges": missing_edges,
        "graph_theorems": len(graph),
    }
    return failures, stats


def main(argv: list[str]) -> int:
    graph = inventory()
    if len(graph) < 100:
        print(
            f"DEPENDS_DERIVED_ERROR|the dependency inventory returned only {len(graph)} "
            "theorems; it is looking at the wrong environment and an empty graph would "
            "make every check below pass vacuously",
            file=sys.stderr,
        )
        return 1
    failures, stats = evaluate(load(), graph)
    if "--quiet" not in argv and stats["unnamed"]:
        print(
            "  kernel-route facts whose checker command names no theorem "
            f"(not enforced): {', '.join(stats['unnamed'])}"
        )
    print(
        "DEPENDS_DERIVED|kernel_facts={kernel_facts}|named={named_theorems}|"
        "graph={graph_theorems}|missing_edges={missing_edges}".format(**stats)
    )
    for failure in failures:
        print(f"DEPENDS_DERIVED_ERROR|{failure}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
