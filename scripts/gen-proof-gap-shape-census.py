#!/usr/bin/env python3
"""Generate a deduplicated structural census of uncertified UNSAT routes.

Write mode invokes the Rust SMT-LIB parser diagnostic to capture source-level
operator heads and the reachable parsed-IR DAG. Check mode is cheap: it binds
the committed census to the exact producer hash, dominance-audit population,
and benchmark content hashes, then regenerates the aggregate JSON/Markdown in
memory. A producer or source change therefore requires an explicit fresh run.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
AUDIT_DIR = ROOT / "bench-results" / "dominance"
PRODUCER = (
    ROOT
    / "crates"
    / "axeyum-smtlib"
    / "examples"
    / "proof_gap_shape_census.rs"
)
OUT_JSON = ROOT / "docs" / "plan" / "generated" / "proof-gap-shape-census.json"
OUT_MD = ROOT / "docs" / "plan" / "generated" / "proof-gap-shape-census.md"

TAG_DESCRIPTIONS = {
    "real-nonlinear": "Parsed IR contains real multiplication.",
    "string-concat": "Source uses string concatenation.",
    "string-regex": "Source uses regex construction or membership.",
    "int-divmod": "Parsed IR contains integer division or modulo.",
    "int-nonlinear": "Parsed IR contains integer multiplication.",
    "int-pow2": "Parsed IR contains cvc5 `int.pow2`.",
    "string-replace": "Source uses a string replacement operator.",
    "string-code": "Source uses `str.to_code`.",
    "arrays": "Parsed IR contains array select/store.",
    "uf": "Parsed IR contains uninterpreted-function application.",
    "string-lex": "Source uses lexicographic string comparison.",
    "string-length": "Source uses string length.",
    "string-contains": "Source uses string containment.",
    "sequence-index": "Source uses sequence indexing.",
    "real-division": "Parsed IR contains real division.",
    "uncategorized": "No current high-level tag matched; inspect exact heads/ops.",
}


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_uncertified_occurrences() -> list[dict]:
    occurrences = []
    for path in sorted(AUDIT_DIR.glob("*.json")):
        audit = json.loads(path.read_text(encoding="utf-8"))
        if not audit.get("complete_audit"):
            continue
        for instance in audit.get("instances", []):
            if (
                instance.get("baseline_outcome") == "unsat"
                and instance.get("audit_outcome") == "unsat"
                and instance.get("evidence_certified") is not True
            ):
                occurrences.append(
                    {
                        "audit_logic": audit.get("logic") or "unknown",
                        "audit_slice": audit.get("slice")
                        or audit.get("baseline")
                        or "unknown",
                        "file": instance["file"],
                        "evidence_checked": instance.get("evidence_checked") is True,
                    }
                )
    occurrences.sort(
        key=lambda row: (row["file"], row["audit_logic"], row["audit_slice"])
    )
    if not occurrences:
        raise RuntimeError("no uncertified evidence-audit UNSAT instances found")
    return occurrences


def run_producer(paths: list[str]) -> list[dict]:
    command = [
        "cargo",
        "run",
        "--quiet",
        "-p",
        "axeyum-smtlib",
        "--example",
        "proof_gap_shape_census",
        "--",
        *paths,
    ]
    env = os.environ.copy()
    env.setdefault("CARGO_BUILD_JOBS", "2")
    result = subprocess.run(
        command,
        cwd=ROOT,
        env=env,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    data = json.loads(result.stdout)
    if data.get("version") != 1 or not isinstance(data.get("instances"), list):
        raise RuntimeError("unexpected proof_gap_shape_census output schema")
    return data["instances"]


def feature_tags(row: dict) -> list[str]:
    heads = set(row["source_heads"])
    ops = set(row["ir_ops"])
    tags = []
    if "RealMul" in ops:
        tags.append("real-nonlinear")
    if "str.++" in heads:
        tags.append("string-concat")
    if any(head.startswith("re.") for head in heads) or "str.in_re" in heads:
        tags.append("string-regex")
    if {"IntDiv", "IntMod"} & ops:
        tags.append("int-divmod")
    if "IntMul" in ops:
        tags.append("int-nonlinear")
    if "IntPow2" in ops:
        tags.append("int-pow2")
    if any(head.startswith("str.replace") for head in heads):
        tags.append("string-replace")
    if "str.to_code" in heads:
        tags.append("string-code")
    if {"Select", "Store"} & ops:
        tags.append("arrays")
    if "Apply" in ops:
        tags.append("uf")
    if "str.<=" in heads:
        tags.append("string-lex")
    if "str.len" in heads:
        tags.append("string-length")
    if "str.contains" in heads:
        tags.append("string-contains")
    if "seq.nth" in heads:
        tags.append("sequence-index")
    if "RealDiv" in ops:
        tags.append("real-division")
    if not tags:
        tags.append("uncategorized")
    return tags


def validate_raw_files(raw_files: list[dict], expected_paths: list[str]) -> None:
    actual_paths = sorted(row["file"] for row in raw_files)
    if actual_paths != expected_paths:
        missing = sorted(set(expected_paths) - set(actual_paths))
        extra = sorted(set(actual_paths) - set(expected_paths))
        raise RuntimeError(f"shape population mismatch: missing={missing}, extra={extra}")
    for row in raw_files:
        path = ROOT / row["file"]
        if not path.is_file():
            raise RuntimeError(f"missing benchmark source: {row['file']}")
        current = sha256(path)
        if row.get("sha256") != current:
            raise RuntimeError(
                f"benchmark hash changed for {row['file']}: "
                f"recorded={row.get('sha256')} current={current}"
            )


def prevalence(
    content_rows: list[dict], key: str, occurrence_counts: dict[str, int]
) -> list[dict]:
    counts: dict[str, dict[str, int]] = defaultdict(
        lambda: {"unique_contents": 0, "audit_occurrences": 0}
    )
    for row in content_rows:
        for feature in row[key]:
            counts[feature]["unique_contents"] += 1
            counts[feature]["audit_occurrences"] += occurrence_counts[row["sha256"]]
    return [
        {key[:-1] if key.endswith("s") else key: feature, **values}
        for feature, values in sorted(
            counts.items(),
            key=lambda item: (
                -item[1]["unique_contents"],
                -item[1]["audit_occurrences"],
                item[0],
            ),
        )
    ]


def build_report(occurrences: list[dict], raw_files: list[dict]) -> dict:
    expected_paths = sorted({row["file"] for row in occurrences})
    validate_raw_files(raw_files, expected_paths)
    occurrence_by_path = Counter(row["file"] for row in occurrences)
    occurrence_rows_by_path: dict[str, list[dict]] = defaultdict(list)
    for occurrence in occurrences:
        occurrence_rows_by_path[occurrence["file"]].append(occurrence)

    files = []
    for raw in sorted(raw_files, key=lambda row: row["file"]):
        file_row = dict(raw)
        file_row["tags"] = feature_tags(raw)
        file_row["audit_occurrences"] = occurrence_rows_by_path[raw["file"]]
        files.append(file_row)

    by_hash: dict[str, list[dict]] = defaultdict(list)
    for row in files:
        by_hash[row["sha256"]].append(row)

    content_rows = []
    content_occurrences = {}
    for digest, group in sorted(by_hash.items()):
        canonical = min(group, key=lambda row: row["file"])
        paths = sorted(row["file"] for row in group)
        audit_occurrences = sum(occurrence_by_path[path] for path in paths)
        content_occurrences[digest] = audit_occurrences
        if any(row["source_heads"] != canonical["source_heads"] for row in group):
            raise RuntimeError(f"same-content source-head mismatch for {digest}")
        if any(row["ir_ops"] != canonical["ir_ops"] for row in group):
            raise RuntimeError(f"same-content IR-op mismatch for {digest}")
        content_rows.append(
            {
                "sha256": digest,
                "canonical_file": canonical["file"],
                "files": paths,
                "audit_occurrences": audit_occurrences,
                "declared_logic": canonical.get("logic") or "unknown",
                "assertions": canonical["assertions"],
                "unique_ir_terms": canonical["unique_ir_terms"],
                "tags": canonical["tags"],
                "source_heads": sorted(canonical["source_heads"]),
                "ir_ops": sorted(canonical["ir_ops"]),
            }
        )
    content_rows.sort(
        key=lambda row: (row["declared_logic"], row["canonical_file"], row["sha256"])
    )

    tag_counts: dict[str, dict[str, int]] = defaultdict(
        lambda: {"unique_contents": 0, "audit_occurrences": 0}
    )
    for row in content_rows:
        for tag in row["tags"]:
            tag_counts[tag]["unique_contents"] += 1
            tag_counts[tag]["audit_occurrences"] += row["audit_occurrences"]
    feature_families = [
        {
            "family": tag,
            **values,
            "description": TAG_DESCRIPTIONS[tag],
        }
        for tag, values in sorted(
            tag_counts.items(),
            key=lambda item: (
                -item[1]["unique_contents"],
                -item[1]["audit_occurrences"],
                item[0],
            ),
        )
    ]

    declared_logics = Counter(row["declared_logic"] for row in content_rows)
    source_domains = {
        "arithmetic": sum(
            row["declared_logic"] in {"QF_AUFLIA", "QF_NIA", "QF_NRA", "QF_UFLIA"}
            for row in content_rows
        ),
        "string_sequence": sum(
            row["declared_logic"] in {"QF_S", "QF_SEQ", "QF_SLIA"}
            for row in content_rows
        ),
    }

    return {
        "version": 1,
        "producer": {"path": rel(PRODUCER), "sha256": sha256(PRODUCER)},
        "summary": {
            "audit_occurrences": len(occurrences),
            "evidence_checked_occurrences": sum(
                row["evidence_checked"] for row in occurrences
            ),
            "evidence_unchecked_occurrences": sum(
                not row["evidence_checked"] for row in occurrences
            ),
            "unique_paths": len(files),
            "unique_content_sha256": len(content_rows),
            "exact_duplicate_groups": sum(len(group) > 1 for group in by_hash.values()),
            "zero_ir_term_contents": sum(
                row["unique_ir_terms"] == 0 for row in content_rows
            ),
            "arithmetic_contents": source_domains["arithmetic"],
            "string_sequence_contents": source_domains["string_sequence"],
        },
        "declared_logics": [
            {"logic": logic, "unique_contents": count}
            for logic, count in sorted(
                declared_logics.items(), key=lambda item: (-item[1], item[0])
            )
        ],
        "feature_families": feature_families,
        "source_head_prevalence": prevalence(
            content_rows, "source_heads", content_occurrences
        ),
        "ir_op_prevalence": prevalence(content_rows, "ir_ops", content_occurrences),
        "contents": content_rows,
        "files": files,
    }


def render_json(report: dict) -> str:
    return json.dumps(report, indent=2, sort_keys=True) + "\n"


def markdown(report: dict) -> str:
    summary = report["summary"]
    lines = [
        "# Generated uncertified proof-route shape census",
        "",
        "> Generated by `scripts/gen-proof-gap-shape-census.py` using the exact",
        "> Axeyum SMT-LIB parser and reachable IR. Do not hand-edit.",
        "",
        "This report analyzes only evidence-audit UNSAT instances whose evidence is",
        "not marked certified. Feature families are non-exclusive structural tags,",
        "not explanations of why the solver concluded UNSAT and not authorization to",
        "implement a proof rule.",
        "",
        "## Denominators",
        "",
        "| Population | Count |",
        "|---|---:|",
        f"| Audit-row occurrences | {summary['audit_occurrences']} |",
        f"| Evidence-checked occurrences | {summary['evidence_checked_occurrences']} |",
        f"| Evidence-unchecked occurrences | {summary['evidence_unchecked_occurrences']} |",
        f"| Unique normalized paths | {summary['unique_paths']} |",
        f"| Unique exact contents (SHA-256) | {summary['unique_content_sha256']} |",
        f"| Exact duplicate groups | {summary['exact_duplicate_groups']} |",
        f"| Unique contents with zero reachable parsed-IR terms | {summary['zero_ir_term_contents']} |",
        "",
        f"The raw 54 count contracts to **{summary['unique_content_sha256']} unique benchmark contents**.",
        "Two UFLIA paths occur in overlapping audit rows, and five cross-path exact",
        "duplicate groups remain after path deduplication. Mechanism prevalence below",
        "uses unique contents, with raw audit occurrences shown separately.",
        "",
        "## Declared-logic population",
        "",
        "| Declared logic | Unique contents |",
        "|---|---:|",
    ]
    for row in report["declared_logics"]:
        lines.append(f"| {row['logic']} | {row['unique_contents']} |")

    lines.extend(
        [
            "",
            "## Non-exclusive structural families",
            "",
            "| Family | Unique contents | Audit occurrences | Structural criterion |",
            "|---|---:|---:|---|",
        ]
    )
    for row in report["feature_families"]:
        lines.append(
            f"| `{row['family']}` | {row['unique_contents']} | "
            f"{row['audit_occurrences']} | {row['description']} |"
        )

    lines.extend(
        [
            "",
            "## Per-content census",
            "",
            "| Logic | Canonical file | Paths | Audit occurrences | IR terms | Structural families |",
            "|---|---|---:|---:|---:|---|",
        ]
    )
    for row in report["contents"]:
        tags = ", ".join(f"`{tag}`" for tag in row["tags"])
        lines.append(
            f"| {row['declared_logic']} | `{row['canonical_file']}` | "
            f"{len(row['files'])} | {row['audit_occurrences']} | "
            f"{row['unique_ir_terms']} | {tags} |"
        )

    lines.extend(
        [
            "",
            "## Research interpretation",
            "",
            f"- The population is bifurcated: **{summary['arithmetic_contents']} arithmetic** and **{summary['string_sequence_contents']} string/sequence** unique contents. A single reconstruction feature cannot close the uncertified lane.",
            "- Real nonlinear multiplication is the largest single structural family,",
            "  but operator presence does not distinguish an SOS-capable refutation from",
            "  a different nonlinear argument. The next producer must record the actual",
            "  refuter/reduction identity and premises.",
            f"- **{summary['zero_ir_term_contents']} unique contents have zero reachable parsed-IR terms** because front-end handling discharges them before the ordinary assertion DAG. Certificate provenance must begin at that early-fold seam.",
            "- String lowering frequently becomes BV structure in parsed IR. Source heads",
            "  and lowered IR operators are therefore both retained; neither alone is an",
            "  adequate proof taxonomy.",
            "- Exact duplicates must remain deduplicated when prioritizing mechanisms,",
            "  while audit-row occurrences remain useful for regression impact.",
            "",
            "## Next instrumentation gate",
            "",
            "Before implementing a new proof mechanism, extend evidence production to",
            "record a stable route ID, source-to-lowered obligation map, checker identity,",
            "and the first uncertified reduction for every `bare-unsat`. Re-run this exact",
            "47-content population and select work only when one route appears across",
            "multiple independent source families. Syntax co-occurrence alone is not a",
            "causal mechanism.",
            "",
        ]
    )
    return "\n".join(lines)


def write_or_check(path: Path, content: str, check: bool) -> bool:
    if check:
        actual = path.read_text(encoding="utf-8") if path.exists() else None
        if actual != content:
            print(f"stale generated artifact: {rel(path)}", file=sys.stderr)
            return False
        return True
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    return True


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check", action="store_true", help="validate committed census without Cargo"
    )
    args = parser.parse_args()
    occurrences = load_uncertified_occurrences()
    expected_paths = sorted({row["file"] for row in occurrences})
    if args.check:
        if not OUT_JSON.exists():
            print(f"missing generated artifact: {rel(OUT_JSON)}", file=sys.stderr)
            return 1
        committed = json.loads(OUT_JSON.read_text(encoding="utf-8"))
        raw_files = committed.get("files", [])
    else:
        raw_files = run_producer(expected_paths)

    try:
        report = build_report(occurrences, raw_files)
    except RuntimeError as error:
        print(f"proof-gap shape census failed: {error}", file=sys.stderr)
        return 1
    ok_json = write_or_check(OUT_JSON, render_json(report), args.check)
    ok_md = write_or_check(OUT_MD, markdown(report), args.check)
    summary = report["summary"]
    print(
        "PROOF_GAP_SHAPES|"
        f"occurrences={summary['audit_occurrences']}|"
        f"paths={summary['unique_paths']}|"
        f"contents={summary['unique_content_sha256']}|"
        f"duplicate_groups={summary['exact_duplicate_groups']}|"
        f"arithmetic={summary['arithmetic_contents']}|"
        f"string_sequence={summary['string_sequence_contents']}|"
        f"zero_ir={summary['zero_ir_term_contents']}"
    )
    return 0 if ok_json and ok_md else 1


if __name__ == "__main__":
    raise SystemExit(main())
