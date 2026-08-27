#!/usr/bin/env python3
"""Generate `artifacts/import-backlog.json` from the fact ledger (ADR-0601 SS3).

`scripts/validate-facts.py` already COUNTS this population every run --
"external: 164 settled elsewhere but not here (import backlog)" -- and
nothing before this script CONSUMED that count. ADR-0601 SS3: *"The 164-item
backlog becomes a produced artifact: external-proved x epistemically-open x
curriculum-reachable, ordered by the curriculum DAG, consumable by the
selector as import candidates."*

WHAT A ROW IS. A fact with `epistemic_status == "open"` and
`external_status == "proved"` -- settled in the wider literature, not yet
established here, and not a problem for the self-extension loop to try to
solve from scratch (that is exactly the distinction
`scripts/validate-facts.py`'s backlog counter already draws; this script
reads the SAME two fields the same way, not a broader "closed" notion, so its
row count always equals that counter's number on the same tree).

CURRICULUM MAPPING. A fact carries no direct link to a
`docs/curriculum/curriculum.toml` node -- `concept_refs` point at the
`math-education` concept graph (ids like `C:commutativity`), a DIFFERENT
vocabulary from curriculum node ids (`propositional-logic`,
`modular-arithmetic`, ...). The two vocabularies overlap only where a
concept_ref's `C:`-stripped id happens to equal a curriculum node id exactly
(measured on this tree: 4 of 23 curriculum nodes -- `counting`, `integers`,
`modular-arithmetic`, `predicate-logic`). This script uses exactly that exact
-- and only that -- match: a fact maps to a curriculum node when one of its
`concept_refs` has `graph == "math-education"` and `ref` (with the `C:`
prefix stripped) equals a `docs/curriculum/curriculum.toml` node id, verbatim.
No fuzzy/substring/title matching -- a crude classifier that flags a whole
shape is not a measurement (CLAUDE.md), and a title-similarity heuristic here
would manufacture curriculum edges nobody asserted. A fact with no such match
gets `curriculum_node: null`; that is the honest, and current, majority case.

DEPENDENCY READINESS. `dependency_ready` is true when EVERY id in
`depends_on` names a fact whose `epistemic_status` is one of
`{"proved", "computed", "refuted"}` (this repo's `OURS_SETTLED`, imported
from `scripts/validate-facts.py` rather than re-typed) -- i.e. every
prerequisite is something WE have already established, vacuously true for an
empty `depends_on`. This is a STATEMENT ABOUT THE LEDGER'S depends_on EDGES,
not a proof-theoretic dependency: `depends_on` is curriculum/ordering
metadata per the fact schema, and this field inherits that same caveat.

ORDERING -- THE DESIGN CONTENT. Rows are sorted:

  1. `dependency_ready` facts before blocked ones (a ready row can be
     imported without first importing anything else);
  2. within that, `curriculum_node`-mapped facts before unmapped ones
     (a curriculum-reachable import extends a DAG a reader can navigate;
     an unmapped one is an island);
  3. within that, by the curriculum node's own DAG position -- `(layer,
     node id)` from `curriculum.toml` -- so mapped rows read in the same
     foundations-first order the curriculum tour itself uses;
  4. finally by fact id, ascending, for full determinism and as the sole key
     for the (majority) unmapped population.

This is the whole point of producing the artifact rather than leaving the
164 as a bare count: a consumer (the frontier selector, `scripts/
fact-frontier.py`, owned by a different lane -- NOT modified here) can walk
the list top-to-bottom and get "importable now, DAG-adjacent first" for free,
without re-deriving any of the above itself. Shape documented in
`docs/autogenesis/263-import-backlog-artifact.md`.

Regenerate with `python3 scripts/gen-import-backlog.py`; `--check` fails
when the committed artifact differs from a fresh generation, mirroring
`scripts/gen-plan.py --check`'s convention -- the standard generated-artifact
gate in this repository.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import sys
import tomllib
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
FACTS_DIR = ROOT / "artifacts" / "facts"
CURRICULUM = ROOT / "docs" / "curriculum" / "curriculum.toml"
OUTPUT = ROOT / "artifacts" / "import-backlog.json"

# Reuse the ledger's own fact-loading and status vocabulary rather than
# re-typing it -- `scripts/validate-facts.py`'s backlog counter and this
# script's row population must never drift apart, since a mismatch here
# would be exactly the kind of silent divergence CLAUDE.md warns about
# (a report that stops measuring the thing its name promises).
_SPEC = importlib.util.spec_from_file_location(
    "validate_facts", ROOT / "scripts" / "validate-facts.py"
)
assert _SPEC is not None and _SPEC.loader is not None
VALIDATE_FACTS = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(VALIDATE_FACTS)

SCHEMA_VERSION = 1


class BacklogError(Exception):
    pass


def load_facts() -> dict[str, dict[str, Any]]:
    facts: dict[str, dict[str, Any]] = {}
    for path in sorted(FACTS_DIR.glob("*.json")):
        try:
            fact = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            raise BacklogError(f"{path.name}: not valid JSON: {exc}") from exc
        fid = fact.get("id")
        if fid:
            facts[fid] = fact
    return facts


def load_curriculum_nodes() -> dict[str, dict[str, Any]]:
    """`{node_id: {"layer": int, "title": str}}` from `curriculum.toml`."""
    if not CURRICULUM.is_file():
        raise BacklogError(f"missing {CURRICULUM}")
    doc = tomllib.loads(CURRICULUM.read_text(encoding="utf-8"))
    nodes: dict[str, dict[str, Any]] = {}
    for node in doc.get("node", []):
        node_id = node.get("id")
        if not node_id:
            continue
        nodes[node_id] = {
            "layer": node.get("layer"),
            "title": node.get("title"),
        }
    return nodes


def map_curriculum_node(fact: dict[str, Any], nodes: dict[str, dict[str, Any]]) -> str | None:
    """Exact-match a fact's `math-education` concept_refs against curriculum
    node ids (see the module docstring for why this is exact, not fuzzy).
    The FIRST matching ref (in the fact's own `concept_refs` order) wins, so
    the result is deterministic even when a fact happens to carry more than
    one ref that matches -- verified empirically to be rare, but breaking
    the tie by input order rather than leaving it to dict/set iteration is
    what keeps this a public API promise (CLAUDE.md: "no hash-map iteration
    order in output")."""
    for ref in fact.get("concept_refs") or []:
        if not isinstance(ref, dict):
            continue
        if ref.get("graph") != "math-education":
            continue
        raw = ref.get("ref") or ""
        node_id = raw[2:] if raw.startswith("C:") else raw
        if node_id in nodes:
            return node_id
    return None


def dependency_ready(fact: dict[str, Any], facts: dict[str, dict[str, Any]]) -> bool:
    for dep_id in fact.get("depends_on") or []:
        dep = facts.get(dep_id)
        if dep is None or dep.get("epistemic_status") not in VALIDATE_FACTS.OURS_SETTLED:
            return False
    return True


def build_rows(
    facts: dict[str, dict[str, Any]], nodes: dict[str, dict[str, Any]]
) -> list[dict[str, Any]]:
    backlog = [
        f
        for f in facts.values()
        if f.get("epistemic_status") == "open" and f.get("external_status") == "proved"
    ]

    rows = []
    for fact in backlog:
        node_id = map_curriculum_node(fact, nodes)
        node = nodes.get(node_id) if node_id else None
        rows.append(
            {
                "id": fact["id"],
                "statement": fact.get("statement", ""),
                "depends_on": sorted(fact.get("depends_on") or []),
                "dependency_ready": dependency_ready(fact, facts),
                "curriculum_node": node_id,
                "curriculum_layer": node["layer"] if node else None,
                "curriculum_title": node["title"] if node else None,
            }
        )

    def sort_key(row: dict[str, Any]) -> tuple:
        return (
            0 if row["dependency_ready"] else 1,
            0 if row["curriculum_node"] is not None else 1,
            row["curriculum_layer"] if row["curriculum_layer"] is not None else 999,
            row["curriculum_node"] or "",
            row["id"],
        )

    rows.sort(key=sort_key)
    return rows


def render(rows: list[dict[str, Any]]) -> str:
    document = {
        "schema_version": SCHEMA_VERSION,
        "generated_by": "scripts/gen-import-backlog.py",
        "generated_from": [
            "artifacts/facts/*.json",
            "docs/curriculum/curriculum.toml",
        ],
        "description": (
            "Facts with epistemic_status=open and external_status=proved: "
            "settled in the wider literature, not yet established here "
            "(ADR-0601 SS3). Never edit by hand -- regenerate with "
            "`python3 scripts/gen-import-backlog.py`."
        ),
        "ordering": (
            "dependency_ready rows before blocked ones; within that, "
            "curriculum_node-mapped rows before unmapped ones, ordered by "
            "(curriculum_layer, curriculum_node); ties (and the whole "
            "unmapped population) broken by fact id ascending. See "
            "docs/autogenesis/263-import-backlog-artifact.md."
        ),
        "count": len(rows),
        "rows": rows,
    }
    return json.dumps(document, indent=2, ensure_ascii=False, sort_keys=False) + "\n"


def display(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail when the committed artifact differs from a fresh generation",
    )
    args = parser.parse_args()

    try:
        facts = load_facts()
        nodes = load_curriculum_nodes()
        rows = build_rows(facts, nodes)
        rendered = render(rows)
    except BacklogError as error:
        print(f"gen-import-backlog: ERROR: {error}", file=sys.stderr)
        return 1

    if args.check:
        current = OUTPUT.read_text(encoding="utf-8") if OUTPUT.is_file() else None
        if current != rendered:
            print(
                f"gen-import-backlog: ERROR: {display(OUTPUT)} is not what "
                "scripts/gen-import-backlog.py produces. It is generated: rerun "
                "`python3 scripts/gen-import-backlog.py` and commit the result.",
                file=sys.stderr,
            )
            return 1
    else:
        OUTPUT.write_text(rendered, encoding="utf-8")

    ready = sum(1 for r in rows if r["dependency_ready"])
    mapped = sum(1 for r in rows if r["curriculum_node"] is not None)
    print(
        "IMPORT-BACKLOG|"
        f"rows={len(rows)}|"
        f"dependency_ready={ready}|"
        f"curriculum_mapped={mapped}|"
        f"bytes={len(rendered.encode('utf-8'))}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
