#!/usr/bin/env python3
"""Validate and render the reconstruction-prelude axiom ledger.

Unlike a source-text call-site count, the authoritative inventory is emitted by
constructing each prelude in an independent kernel and enumerating admitted
``Declaration::Axiom`` values.  Canonical rendered types are SHA-256 bound so a
name-preserving type change fails the gate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
from collections import Counter
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "docs" / "plan" / "lean-axiom-ledger-v1.json"
OUT_MD = ROOT / "docs" / "plan" / "generated" / "lean-axiom-ledger.md"
SOURCE_COMMAND = (
    "cargo run --quiet -p axeyum-lean-kernel --example prelude_axiom_inventory"
)
EXPECTED_COUNTS = {"real": 30, "integer": 34, "string": 1}
SOURCE_PATHS = {
    "real": "crates/axeyum-lean-kernel/src/arith_prelude.rs",
    "integer": "crates/axeyum-lean-kernel/src/int_prelude.rs",
    "string": "crates/axeyum-lean-kernel/src/string_prelude.rs",
}
CLASSIFICATIONS = {
    "unclassified",
    "primitive-interface",
    "external-assumption",
    "derivable-theorem",
    "defect",
}
DISCHARGE_STATES = {
    "unreviewed",
    "retained",
    "planned",
    "in-progress",
    "discharged",
    "rejected",
}


class LedgerError(RuntimeError):
    """The source inventory or ledger is malformed."""


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def entry_key(entry: dict[str, Any]) -> tuple[str, str]:
    return str(entry["prelude"]), str(entry["name"])


def run_source_inventory() -> list[dict[str, str]]:
    environment = os.environ.copy()
    environment["CARGO_TERM_COLOR"] = "never"
    completed = subprocess.run(
        SOURCE_COMMAND.split(),
        cwd=ROOT,
        env=environment,
        check=False,
        capture_output=True,
        text=True,
    )
    if completed.returncode != 0:
        raise LedgerError(
            "prelude inventory command failed "
            f"({completed.returncode}): {completed.stderr.strip()}"
        )

    rows: list[dict[str, str]] = []
    for line_number, line in enumerate(completed.stdout.splitlines(), start=1):
        parts = line.split("\t")
        if len(parts) != 3:
            raise LedgerError(
                f"inventory line {line_number} must have three tab-separated fields"
            )
        prelude, name, type_hex = parts
        if prelude not in EXPECTED_COUNTS:
            raise LedgerError(f"inventory line {line_number}: unknown prelude {prelude!r}")
        if not name:
            raise LedgerError(f"inventory line {line_number}: empty name")
        try:
            canonical_type = bytes.fromhex(type_hex).decode("utf-8")
        except (ValueError, UnicodeDecodeError) as error:
            raise LedgerError(
                f"inventory line {line_number}: invalid UTF-8 type hex"
            ) from error
        rows.append(
            {
                "prelude": prelude,
                "name": name,
                "canonical_type": canonical_type,
                "type_sha256": hashlib.sha256(canonical_type.encode()).hexdigest(),
            }
        )

    keys = [entry_key(row) for row in rows]
    if keys != sorted(keys):
        raise LedgerError("source inventory must be sorted by prelude and name")
    if len(set(keys)) != len(keys):
        raise LedgerError("source inventory contains duplicate prelude/name keys")
    counts = Counter(row["prelude"] for row in rows)
    if dict(counts) != EXPECTED_COUNTS:
        raise LedgerError(
            f"source inventory counts {dict(counts)} do not match {EXPECTED_COUNTS}"
        )
    if len(rows) != 65:
        raise LedgerError(f"source inventory must contain 65 rows, found {len(rows)}")
    return rows


def new_manifest(source_rows: list[dict[str, str]]) -> dict[str, Any]:
    entries = []
    for row in source_rows:
        prelude = row["prelude"]
        entries.append(
            {
                **row,
                "source_path": SOURCE_PATHS[prelude],
                "classification": "unclassified",
                "owner": "axeyum-lean-kernel",
                "review_owner": "TL3.2",
                "discharge_status": "unreviewed",
                "discharge_evidence": [],
                "note": "Type is admitted and well-formed; truth or intended semantics are not yet classified.",
            }
        )
    return {
        "version": 1,
        "title": "Axeyum Lean reconstruction prelude axiom ledger",
        "as_of": "2026-07-21",
        "source_command": SOURCE_COMMAND,
        "type_identity": "sha256 of Kernel::render_lean(declaration.ty) UTF-8 bytes",
        "expected_counts": {**EXPECTED_COUNTS, "total": 65},
        "classification_definitions": {
            "unclassified": "No semantic classification has been accepted yet.",
            "primitive-interface": "A carrier or operation intentionally remains an abstract interface constant.",
            "external-assumption": "A proposition intentionally remains a named assumption of the profile.",
            "derivable-theorem": "The declaration should be replaced by a checked theorem term.",
            "defect": "The declaration is false, malformed in intent, redundant unsafely, or otherwise must not remain trusted.",
        },
        "discharge_definitions": {
            "unreviewed": "No row-specific discharge decision has been accepted.",
            "retained": "The assumption is intentionally retained with a published boundary.",
            "planned": "A concrete theorem/import route is assigned but not implemented.",
            "in-progress": "The assigned discharge implementation is active.",
            "discharged": "A retained checked theorem artifact replaces assumption credit.",
            "rejected": "The declaration is removed or prohibited from the supported profile.",
        },
        "entries": entries,
    }


def load_manifest() -> dict[str, Any]:
    with MANIFEST.open(encoding="utf-8") as handle:
        return json.load(handle)


def validate_manifest(
    data: dict[str, Any], source_rows: list[dict[str, str]]
) -> list[str]:
    failures: list[str] = []
    if data.get("version") != 1:
        failures.append("manifest version must be 1")
    if data.get("source_command") != SOURCE_COMMAND:
        failures.append("source_command drift")
    if data.get("expected_counts") != {**EXPECTED_COUNTS, "total": 65}:
        failures.append("expected_counts must remain real=30 integer=34 string=1 total=65")
    if set(data.get("classification_definitions", {})) != CLASSIFICATIONS:
        failures.append("classification definitions do not match the allowed states")
    if set(data.get("discharge_definitions", {})) != DISCHARGE_STATES:
        failures.append("discharge definitions do not match the allowed states")

    entries = data.get("entries")
    if not isinstance(entries, list):
        return failures + ["entries must be a list"]
    keys = [entry_key(entry) for entry in entries if isinstance(entry, dict)]
    if len(keys) != len(entries):
        return failures + ["every entry must be an object"]
    if keys != sorted(keys):
        failures.append("entries must be sorted by prelude and name")
    if len(set(keys)) != len(keys):
        failures.append("entries contain duplicate prelude/name keys")
    if len(entries) != 65:
        failures.append(f"ledger must contain 65 entries, found {len(entries)}")

    actual_by_key = {entry_key(row): row for row in source_rows}
    ledger_by_key = {entry_key(row): row for row in entries}
    missing = sorted(set(actual_by_key) - set(ledger_by_key))
    extra = sorted(set(ledger_by_key) - set(actual_by_key))
    if missing:
        failures.append(f"ledger missing source axioms: {missing}")
    if extra:
        failures.append(f"ledger has non-source axioms: {extra}")

    for entry in entries:
        key = entry_key(entry)
        label = f"{key[0]}::{key[1]}"
        actual = actual_by_key.get(key)
        if actual is not None:
            if entry.get("canonical_type") != actual["canonical_type"]:
                failures.append(f"{label}: canonical type drift")
            if entry.get("type_sha256") != actual["type_sha256"]:
                failures.append(f"{label}: type digest drift")
        digest = str(entry.get("type_sha256", ""))
        if len(digest) != 64 or any(char not in "0123456789abcdef" for char in digest):
            failures.append(f"{label}: type_sha256 must be lowercase 64-hex")
        canonical_type = entry.get("canonical_type")
        if not isinstance(canonical_type, str) or not canonical_type:
            failures.append(f"{label}: canonical_type is required")
        elif hashlib.sha256(canonical_type.encode()).hexdigest() != digest:
            failures.append(f"{label}: stored type and digest disagree")

        prelude = entry.get("prelude")
        source_path = entry.get("source_path")
        if source_path != SOURCE_PATHS.get(prelude):
            failures.append(f"{label}: wrong source_path")
        elif not (ROOT / source_path).is_file():
            failures.append(f"{label}: source_path does not exist")
        if entry.get("classification") not in CLASSIFICATIONS:
            failures.append(f"{label}: invalid classification")
        if entry.get("discharge_status") not in DISCHARGE_STATES:
            failures.append(f"{label}: invalid discharge_status")
        for field in ("owner", "review_owner", "note"):
            if not entry.get(field):
                failures.append(f"{label}: missing non-empty {field}")
        evidence = entry.get("discharge_evidence")
        if not isinstance(evidence, list):
            failures.append(f"{label}: discharge_evidence must be a list")
            evidence = []
        for path_text in evidence:
            if not isinstance(path_text, str) or not (ROOT / path_text).is_file():
                failures.append(f"{label}: missing discharge evidence {path_text!r}")
        if entry.get("discharge_status") == "discharged" and not evidence:
            failures.append(f"{label}: discharged row requires retained evidence")
        if entry.get("classification") == "derivable-theorem" and entry.get(
            "discharge_status"
        ) == "retained":
            failures.append(f"{label}: derivable theorem cannot be retained as an axiom")

    return failures


def md_escape(value: str) -> str:
    return value.replace("|", "\\|").replace("\n", " ")


def render(data: dict[str, Any]) -> str:
    entries = data["entries"]
    counts = Counter(entry["prelude"] for entry in entries)
    classifications = Counter(entry["classification"] for entry in entries)
    discharges = Counter(entry["discharge_status"] for entry in entries)
    real_names = {entry["name"] for entry in entries if entry["prelude"] == "real"}
    int_names = {entry["name"] for entry in entries if entry["prelude"] == "integer"}
    shared = sorted(real_names & int_names)

    lines = [
        "# Lean reconstruction prelude axiom ledger",
        "",
        "> **Generated; do not edit by hand.** Source: "
        "[`docs/plan/lean-axiom-ledger-v1.json`](../lean-axiom-ledger-v1.json). "
        "Regenerate with `python3 scripts/gen-lean-axiom-ledger.py`; use `--check` "
        "to rebuild the isolated kernel preludes and reject name/type drift.",
        "",
        "This ledger inventories declarations actually admitted as axioms after "
        "constructing each reconstruction prelude. It is not a call-site grep, and "
        "type well-formedness is not a proof that an assumption is true.",
        "",
        "## Snapshot",
        "",
        f"- **65 total assumptions:** real {counts['real']}, integer "
        f"{counts['integer']}, string {counts['string']}.",
        "- The earlier 64-row call-site census missed "
        "`axeyum.string.append`, which is inserted directly as "
        "`Declaration::Axiom` rather than through `declare_axiom(...)`.",
        f"- {len(shared)} names are shared by the isolated real and integer "
        "preludes; they cannot coexist safely until TL3.3 namespaces them.",
        "- Classification: "
        + ", ".join(f"{key} {classifications[key]}" for key in sorted(classifications))
        + ".",
        "- Discharge: "
        + ", ".join(f"{key} {discharges[key]}" for key in sorted(discharges))
        + ".",
        "",
        "## Machine-checked contract",
        "",
        f"- Source command: `{data['source_command']}`.",
        f"- Type identity: {data['type_identity']}.",
        "- Any added/removed axiom, renamed declaration, or canonical type change "
        "fails validation before the generated ledger can remain current.",
        "- Every row has source, semantic classification, owner, review owner, "
        "discharge state, and retained-evidence fields.",
        "- `discharged` requires a real repository evidence path; a "
        "`derivable-theorem` may not be marked `retained`.",
        "",
        "## Ledger",
        "",
        "| Prelude | Name | Type SHA-256 | Classification | Discharge | Owner | Source |",
        "|---|---|---|---|---|---|---|",
    ]
    for entry in entries:
        source = f"[source](../../../{entry['source_path']})"
        lines.append(
            f"| `{entry['prelude']}` | `{md_escape(entry['name'])}` | "
            f"`{entry['type_sha256']}` | `{entry['classification']}` | "
            f"`{entry['discharge_status']}` | `{entry['owner']}` / "
            f"`{entry['review_owner']}` | {source} |"
        )

    lines.extend(
        [
            "",
            "## Shared real/integer names",
            "",
            "These are separate declarations only because the preludes are built in "
            "separate kernels today. Their collision is an explicit TL3.3 blocker:",
            "",
            ", ".join(f"`{name}`" for name in shared) + ".",
            "",
            "## Next classification gate",
            "",
            "TL3.2 must move every `unclassified` row to exactly one of "
            "`primitive-interface`, `external-assumption`, `derivable-theorem`, or "
            "`defect`, assign a discharge target, and preserve the type digest while "
            "the assumption remains live. TL3.4 cannot claim an axiom reduction until "
            "this ledger observes a checked replacement and the runtime population "
            "falls accordingly.",
            "",
        ]
    )
    return "\n".join(lines)


def write_manifest(data: dict[str, Any]) -> None:
    MANIFEST.write_text(
        json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="fail on stale generated output")
    parser.add_argument(
        "--bootstrap",
        action="store_true",
        help="create the initial unclassified ledger from the constructed preludes",
    )
    args = parser.parse_args()

    try:
        source_rows = run_source_inventory()
    except LedgerError as error:
        print(f"LEAN_AXIOM_LEDGER_ERROR|{error}", file=sys.stderr)
        return 1

    if args.bootstrap:
        if MANIFEST.exists():
            print(f"refusing to overwrite existing {relative(MANIFEST)}", file=sys.stderr)
            return 1
        write_manifest(new_manifest(source_rows))

    if not MANIFEST.is_file():
        print(f"missing ledger: {relative(MANIFEST)}; use --bootstrap once", file=sys.stderr)
        return 1
    data = load_manifest()
    failures = validate_manifest(data, source_rows)
    if failures:
        for failure in failures:
            print(f"LEAN_AXIOM_LEDGER_ERROR|{failure}", file=sys.stderr)
        return 1

    rendered = render(data)
    if args.check:
        if not OUT_MD.is_file() or OUT_MD.read_text(encoding="utf-8") != rendered:
            print(
                f"stale generated file: {relative(OUT_MD)}; run "
                "python3 scripts/gen-lean-axiom-ledger.py",
                file=sys.stderr,
            )
            return 1
    else:
        OUT_MD.parent.mkdir(parents=True, exist_ok=True)
        OUT_MD.write_text(rendered, encoding="utf-8")

    counts = Counter(entry["prelude"] for entry in data["entries"])
    print(
        "LEAN_AXIOM_LEDGER|"
        f"total={len(data['entries'])}|real={counts['real']}|"
        f"integer={counts['integer']}|string={counts['string']}|"
        f"unclassified={sum(entry['classification'] == 'unclassified' for entry in data['entries'])}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
