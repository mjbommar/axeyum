#!/usr/bin/env python3
"""Generate proof-free Lean statement adapters from fact `formal.statement`s.

The agent's tier-C producers consume a *frozen NDJSON export* of a theorem's
STATEMENT (its type, proof-isolated, elaborated against Mathlib). Only a handful
of facts had a hand-written adapter, so only a handful were attemptable. Every
open fact already carries its statement as `lean4-surface` text; this wraps each
in a proof-free `def <name> : Prop := <statement>` so `lean4export` can freeze
its elaborated type. No proof, axiom, theorem, or opaque declaration is emitted
-- the adapter is exactly what the proof-isolation importer requires.

Emits ONE `.lean` module for a batch, and a JSON map `fact_id -> target_def`.
Compilation and export happen on the pinned Mathlib host (s5); this script only
produces the source that goes there.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys

NAMESPACE = "Axeyum.Autogenesis.Statement.Generated"


def camel(fact_id: str) -> str:
    slug = fact_id.split(":", 1)[1]
    slug = re.sub(r"^ml430-", "", slug)
    slug = re.sub(r"-[0-9a-f]{6,}$", "", slug)  # drop the content hash tail
    parts = [p for p in slug.split("-") if p]
    return parts[0] + "".join(p.capitalize() for p in parts[1:])


def has_top_level_arrow(stmt: str) -> bool:
    """Classify implication/iff statements for legacy artifact reproduction.

    The 2026-08-25 experiment attributed an empty output file to arrow
    semantics.  A 2026-08-26 stdout-streamed replay against the same Mathlib,
    Lean and lean4export versions exported and proof-isolated three such goals.
    Keep this syntactic classifier only because old censuses used it.
    """
    return ("→" in stmt) or ("->" in stmt) or ("↔" in stmt) or ("<->" in stmt)


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--facts-dir", default="artifacts/facts")
    ap.add_argument("--fact", action="append", default=[], help="fact id (repeatable)")
    ap.add_argument("--module", required=True, help="Lean module name, e.g. AxeyumGeneratedBatchV1")
    ap.add_argument("--out-lean", required=True)
    ap.add_argument("--out-map", required=True)
    ap.add_argument(
        "--exportable-only",
        action="store_true",
        help=(
            "legacy replay filter: skip arrow/iff statements as the 2026-08-25 "
            "census did; arrows are now known to export when stdout is captured correctly"
        ),
    )
    args = ap.parse_args(argv)

    facts = {}
    for p in pathlib.Path(args.facts_dir).glob("*.json"):
        d = json.loads(p.read_text())
        facts[d["id"]] = d

    lines = ["import Mathlib", "", f"namespace {NAMESPACE}", ""]
    mapping = {}
    names_seen = set()
    for fid in args.fact:
        d = facts.get(fid)
        if d is None:
            print(f"GEN_ADAPTER|skip|{fid}|not a known fact", file=sys.stderr)
            continue
        f = d.get("formal", {})
        stmt = (f.get("statement") or "").strip()
        lang = f.get("language", "")
        if not stmt or not lang.startswith("lean4"):
            print(f"GEN_ADAPTER|skip|{fid}|no lean4 statement", file=sys.stderr)
            continue
        arrow = has_top_level_arrow(stmt)
        if arrow and args.exportable_only:
            print(f"GEN_ADAPTER|skip|{fid}|arrow-bearing (legacy replay filter)", file=sys.stderr)
            continue
        print(
            f"GEN_ADAPTER|class|{fid}|{'arrow-exportable' if arrow else 'exportable'}",
            file=sys.stderr,
        )
        name = camel(fid)
        while name in names_seen:
            name = name + "X"
        names_seen.add(name)
        lines.append(f"def {name} : Prop :=")
        lines.append(f"  {stmt}")
        lines.append("")
        mapping[fid] = f"{NAMESPACE}.{name}"
    lines.append(f"end {NAMESPACE}")

    pathlib.Path(args.out_lean).write_text("\n".join(lines) + "\n")
    pathlib.Path(args.out_map).write_text(json.dumps(mapping, indent=2, sort_keys=True) + "\n")
    print(
        f"GEN_ADAPTER|module={args.module}|defs={len(mapping)}|lean={args.out_lean}|map={args.out_map}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
