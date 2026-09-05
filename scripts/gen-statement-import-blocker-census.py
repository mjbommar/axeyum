#!/usr/bin/env python3
"""Build the population for the statement-import blocker census.

Emits one JSONL row per `F:ml430-*` mirror fact: its id, the pinned Mathlib
declaration name, its fragment (family), its `formal.statement` surface text,
its epistemic status, and whether the nursery manifests hold it out.

Held-out membership is derived from `scripts/check-dispatchable-frontier.py
--json`, never by hand -- the manifests are the split authority (ADR-0603 and
the nursery preregistration rule), and a hand list would drift silently.

The rows this emits are an INPUT to the census driver; nothing here runs Lean
or the importer. Usage:

    python3 scripts/gen-statement-import-blocker-census.py --out rows.jsonl
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
FACTS = ROOT / "artifacts" / "facts"

TITLE_NAME = re.compile(r"^Mathlib v4\.30 source proposition (?P<name>\S+)$")
PROVENANCE_NAME = re.compile(r"statement-only extraction of `(?P<name>[^`]+)`")
# The outcome-blind mutation controls are DERIVED statements, not mirrors of a
# Mathlib declaration; they name the base they were mutated from instead.
MUTATION_TITLE = re.compile(r"^Outcome-blind mutation of (?P<name>\S+)$")
MUTATION_PROVENANCE = re.compile(r"mutation of (?P<name>\S+)$")


def source_name(document: dict) -> str:
    """The pinned Mathlib declaration name this mirror was extracted from.

    It is the title's name, cross-checked against `provenance.source`. Two
    independent spellings must agree -- reading only one would silently accept a
    mirror whose title drifted from the name the extraction actually used.

    `formal.kernel_theorem` is NOT this name and must not be substituted for it:
    on a proved mirror that field is OUR kernel's declaration, which may be
    spelled differently from Mathlib's (`Int.dvd_coe_gcd` upstream is
    `Int.dvd_gcd` here). It is carried separately in the emitted row.
    """
    title = document.get("title", "")
    source = (document.get("provenance") or {}).get("source", "")
    mutation = bool(MUTATION_TITLE.match(title))
    title_pattern = MUTATION_TITLE if mutation else TITLE_NAME
    source_pattern = MUTATION_PROVENANCE if mutation else PROVENANCE_NAME
    title_match = title_pattern.match(title)
    from_title = title_match.group("name") if title_match else None
    provenance_match = source_pattern.search(source)
    from_provenance = provenance_match.group("name") if provenance_match else None
    observed = {name for name in (from_title, from_provenance) if name}
    if len(observed) != 1:
        raise SystemExit(
            f"{document['id']}: source name is not unambiguous across "
            f"title/provenance: {sorted(observed)}"
        )
    return observed.pop(), "mutation-control" if mutation else "mirror"


def held_out_ids(root: pathlib.Path) -> set[str]:
    """Held-out fact ids, read from the frontier checker's own JSON."""
    completed = subprocess.run(
        [sys.executable, str(root / "scripts/check-dispatchable-frontier.py"), "--json"],
        capture_output=True,
        text=True,
        cwd=str(root),
    )
    if completed.returncode != 0:
        raise SystemExit(
            f"check-dispatchable-frontier.py exited {completed.returncode}: {completed.stderr}"
        )
    document = json.loads(completed.stdout)
    ids = set()
    for entry in document.get("held_out", []):
        if isinstance(entry, str):
            ids.add(entry)
        elif isinstance(entry, dict):
            for key in ("fact", "fact_id", "id"):
                if isinstance(entry.get(key), str):
                    ids.add(entry[key])
                    break
    if not ids:
        raise SystemExit(
            "the frontier checker reported no held-out ids; refusing to emit a "
            "population whose holdout column would be uniformly false"
        )
    return ids


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=pathlib.Path, required=True)
    parser.add_argument(
        "--status",
        default="all",
        choices=["all", "open", "proved"],
        help="restrict to one epistemic status (default: all, so the proved "
        "mirrors serve as the positive control population)",
    )
    args = parser.parse_args()

    holdout = held_out_ids(ROOT)
    rows = []
    for path in sorted(FACTS.glob("F-ml430-*.json")):
        document = json.loads(path.read_text(encoding="utf-8"))
        formal = document.get("formal") or {}
        status = document.get("epistemic_status", "?")
        if args.status != "all" and status != args.status:
            continue
        name, kind = source_name(document)
        rows.append(
            {
                "fact_id": document["id"],
                "source_name": name,
                "row_kind": kind,
                "kernel_theorem": formal.get("kernel_theorem", ""),
                "fragment": formal.get("fragment", "?"),
                "statement": formal.get("statement", ""),
                "language": formal.get("language", "?"),
                "epistemic_status": status,
                "held_out": document["id"] in holdout,
            }
        )
    if not rows:
        raise SystemExit("no ml430 mirrors matched; refusing to emit an empty population")

    args.out.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows))
    open_rows = sum(1 for row in rows if row["epistemic_status"] == "open")
    print(
        f"POPULATION|rows={len(rows)}|open={open_rows}|proved={len(rows) - open_rows}"
        f"|held_out={sum(1 for row in rows if row['held_out'])}|out={args.out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
