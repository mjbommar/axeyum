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
#
# `(?<![A-Za-z])` and the `AxReal`-before-`Real` ordering are both load-bearing
# after ADR-0522. Without the boundary, `AxReal.add_comm` matches at offset 2 and
# yields `Real.add_comm` -- a name no kernel declares. That is worse than missing
# it: `unnamed` never fires (a name WAS found), the graph lookup misses, and the
# fact is skipped with nothing printed. Measured 2026-08-19, the silent-skip path
# this file's header promises to report instead.
#
# `CReal|Complex|CPoint` added 2026-08-25: this list previously covered
# `Nat`/`Int`/`Rat` and the axiomatized `AxReal`, but never the constructed
# carriers `CReal` (159 theorems), `Complex` (84) and `CPoint` (88), so every
# fact whose checker names a theorem in one of those namespaces silently fell
# into `unnamed` -- 331 theorems this gate never enforced anything over.
# `CReal` is the substring hazard CLAUDE.md documents for `contains("Real.")`;
# the SAME `(?<![A-Za-z])` boundary that already keeps `AxReal.add_comm` from
# yielding a false `Real.add_comm` match ALSO keeps a name like `XCReal.foo`
# (nothing declares one, but it is the near-miss control) from matching at the
# `CReal` offset, because the character before that offset is a letter. See
# `test_theorem_re_does_not_match_near_miss_carrier_prefix` for the check.
_SEG = r"[A-Za-z0-9_]+"
_DOT = r"(?:\\?\.|\[\.\])"
_NS = "AxReal|AxNat|Nat|Int|Real|Rat|List|Bool|Prop|Acc|WellFounded|Str|CReal|Complex|CPoint"
THEOREM_RE = re.compile(rf"\^?(?<![A-Za-z])((?:{_NS})(?:{_DOT}{_SEG})+)")


def inventory() -> dict[str, list[str]]:
    """`theorem -> [direct theorem dependency]`, read out of the kernel.

    `--release` is MANDATORY, not a speed nicety. Since `f74fb3a3e` this tool
    unconditionally builds `creal`/`complex`/`cpoint` (its own module doc says
    so explicitly: "`--release` IS NOW MANDATORY"), which recurses deep enough
    through `Kernel::add_declaration` to blow a debug build's default thread
    stack -- the same resource limit CLAUDE.md already documents for
    `prelude_theorem_inventory --include-constructed`. Measured 2026-08-25 on
    this tree: the debug form SIGABRTs (`Signals.SIGABRT`, "has overflowed its
    stack") every time, so this checker -- wired into both `scripts/check.sh`
    and `just check` -- could not validate ANY kernel-route fact's
    `depends_on`, including the 175 that predate this fix. Nothing was wrong
    with any fact; the checker itself never ran to completion.
    """
    proc = subprocess.run(
        [
            "cargo", "run", "-q", "--release", "-p", "axeyum-lean-kernel",
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
    """The theorem a kernel-route fact is about.

    `formal.kernel_theorem`, when the KEY IS PRESENT, is authoritative and
    extraction is not consulted at all -- including when its value is `null`,
    which means "this fact is not about exactly one kernel theorem" (a
    package-level result bundling several laws/theorems) and must not fall
    back to guessing. That distinguishes a deliberate "no single subject"
    from an unfilled field, which is what makes the key's PRESENCE the signal
    rather than its truthiness.

    Only when the key is ABSENT does this fall back to the historical
    behaviour: the first dotted theorem name matched in the fact's own
    evidence `checker_command`s, in evidence order. That extraction is a
    convenience for the common case (one theorem, named once, nothing else in
    the command looks like a theorem name) and is demonstrably NOT reliable
    in general -- it can match an embedded formal-statement fragment instead
    of the theorem under test (`F:cassini-identity-over-constructed-integers`
    extracted `Int.sub`, not the actual subject `Int.fib_cassini`, until this
    field existed), or collide two unrelated facts onto the same name
    (`F:complex-mul-assoc` and `F:complex-ring-constructed-axiom-free` both
    extracted `Complex.mul_assoc`). `formal.kernel_theorem` exists precisely
    to let a fact's author pin the right answer where extraction cannot be
    trusted, without touching every fact where it already agrees.
    """
    formal = fact.get("formal") or {}
    if "kernel_theorem" in formal:
        value = formal["kernel_theorem"]
        return value if isinstance(value, str) else None
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


def load_with_paths() -> dict[str, tuple[pathlib.Path, dict[str, Any]]]:
    """Like `load`, but keeps each fact's own file path -- `--fix` needs it to
    patch the right file, and `load` alone throws that away."""
    result: dict[str, tuple[pathlib.Path, dict[str, Any]]] = {}
    for p in sorted(FACTS.glob("*.json")):
        data = json.loads(p.read_text(encoding="utf-8"))
        result[data["id"]] = (p, data)
    return result


def _kernel_index(
    facts: dict[str, dict[str, Any]],
) -> tuple[dict[str, dict[str, Any]], dict[str, str], list[str]]:
    """`(kernel_facts, theorem -> owning fact, facts naming no theorem)`.

    Shared by `evaluate` and `missing_edges_by_fact` so `--fix` adds exactly
    what the check would otherwise report as a failure -- never more, never
    less -- by construction rather than by keeping two traversals in sync.
    """
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
    return kernel_facts, theorem_to_fact, unnamed


def evaluate(
    facts: dict[str, dict[str, Any]], graph: dict[str, list[str]]
) -> tuple[list[str], dict[str, Any]]:
    kernel_facts, theorem_to_fact, unnamed = _kernel_index(facts)

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


def missing_edges_by_fact(
    facts: dict[str, dict[str, Any]], graph: dict[str, list[str]]
) -> dict[str, list[str]]:
    """`fact id -> sorted fact ids its depends_on is missing`.

    Same traversal as `evaluate`, collapsed from a message-per-edge to a
    fact-id-set-per-fact, which is the shape `--fix` needs to patch a file
    once instead of once per missing edge.
    """
    kernel_facts, theorem_to_fact, _unnamed = _kernel_index(facts)
    result: dict[str, list[str]] = {}
    for ident, data in kernel_facts.items():
        name = theorem_of(data)
        if name is None or name not in graph:
            continue
        declared = set(data.get("depends_on") or [])
        needed_set: set[str] = set()
        for used in graph[name]:
            needed = theorem_to_fact.get(used)
            if needed is None or needed == ident:
                continue
            if needed not in declared:
                needed_set.add(needed)
        if needed_set:
            result[ident] = sorted(needed_set)
    return result


# Matches a fact file's single top-level `depends_on` array verbatim, brackets
# included. Safe as a non-nesting `[^\[\]]*`: every `depends_on` entry is a
# plain `F:...` string (checked over the whole committed ledger before this
# regex was written -- no entry contains `[` or `]`), so the array never
# nests and this is the exact span, not an approximation of it.
_DEPENDS_ON_RE = re.compile(r'"depends_on":\s*(\[[^\[\]]*\])')


def _patch_depends_on(text: str, additional: list[str]) -> str:
    """Add `additional` fact ids to the file's OWN `depends_on` array via text
    substitution -- never a JSON re-dump, which reformats unrelated compact
    arrays elsewhere in the document (measured the day this was written; see
    docs/research/11-design-review/2026-08-29-two-gaps-the-gate-sweep-exposed.md).

    Preserves whatever style the array already uses: a single-line array
    (including `[]`) stays single-line; a multi-line array keeps its own
    entry indent and closing-bracket indent, read from the array itself
    rather than assumed, since the committed ledger has dozens of distinct
    indent widths across files written by different lanes' tools.
    """
    match = _DEPENDS_ON_RE.search(text)
    if not match:
        raise ValueError("no depends_on array found")
    array_text = match.group(1)
    current = json.loads(array_text)
    new_items = [x for x in additional if x not in current]
    if not new_items:
        return text
    merged = list(current) + sorted(new_items)
    if "\n" not in array_text:
        replacement = "[" + ", ".join(json.dumps(x) for x in merged) + "]"
    else:
        entry_indent_match = re.search(r"\[\s*\n([ \t]*)", array_text)
        closing_indent_match = re.search(r"\n([ \t]*)\]\s*$", array_text)
        entry_indent = entry_indent_match.group(1) if entry_indent_match else "    "
        closing_indent = closing_indent_match.group(1) if closing_indent_match else ""
        body = ",\n".join(f"{entry_indent}{json.dumps(x)}" for x in merged)
        replacement = f"[\n{body}\n{closing_indent}]"
    start, end = match.span(1)
    return text[:start] + replacement + text[end:]


def fix(facts_by_path: dict[str, tuple[pathlib.Path, dict[str, Any]]],
        graph: dict[str, list[str]]) -> int:
    """Patch every fact whose `depends_on` is missing an edge `evaluate` would
    otherwise report, writing only the `depends_on` array of the files that
    need it. Reloads from disk afterwards and re-runs `evaluate` as a
    self-check: a malformed substitution is caught here, not by whoever next
    reads these files.
    """
    facts = {ident: data for ident, (_p, data) in facts_by_path.items()}
    missing = missing_edges_by_fact(facts, graph)
    if not missing:
        print("DEPENDS_DERIVED_FIX|nothing to fix")
        return 0
    total_edges = 0
    for ident in sorted(missing):
        path, _data = facts_by_path[ident]
        text = path.read_text(encoding="utf-8")
        new_text = _patch_depends_on(text, missing[ident])
        if new_text == text:
            continue
        path.write_text(new_text, encoding="utf-8")
        total_edges += len(missing[ident])
        print(f"DEPENDS_DERIVED_FIX|{ident}|added={','.join(missing[ident])}")
    print(f"DEPENDS_DERIVED_FIX|facts={len(missing)}|edges={total_edges}")

    reloaded = {ident: data for ident, (_p, data) in load_with_paths().items()}
    failures, _stats = evaluate(reloaded, graph)
    if failures:
        for failure in failures:
            print(f"DEPENDS_DERIVED_ERROR|{failure}", file=sys.stderr)
        print(
            "DEPENDS_DERIVED_FIX_ERROR|fix did not close every edge -- see errors above",
            file=sys.stderr,
        )
        return 1
    return 0


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
    if "--fix" in argv:
        return fix(load_with_paths(), graph)
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
