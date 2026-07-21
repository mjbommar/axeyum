#!/usr/bin/env python3
"""Generate the G1 cross-regime measurement provenance matrix.

This generator deliberately keeps the curated/regression scoreboard and the
partial public inventory as separate measurement regimes.  It gives them one
identity/provenance vocabulary, computes exact-content overlap, and refuses to
invent a cross-regime score or a semantic-deduplication claim.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import sys
from collections import defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "docs" / "plan" / "measurement-provenance-v1.json"
OUTPUT_JSON = ROOT / "docs" / "plan" / "generated" / "measurement-provenance-matrix.json"
OUTPUT_MD = ROOT / "docs" / "plan" / "generated" / "measurement-provenance-matrix.md"
GEN_SCOREBOARD = ROOT / "scripts" / "gen-scoreboard.py"
SCHEMA = "axeyum.measurement-provenance-matrix.v1"


def load_json(path: Path) -> dict:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def load_scoreboard_module():
    spec = importlib.util.spec_from_file_location("axeyum_gen_scoreboard", GEN_SCOREBOARD)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {GEN_SCOREBOARD}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def normalize_scoreboard_id(value: str) -> str:
    for marker in ("non-incremental/", "quantified/"):
        if marker in value:
            suffix = value.split(marker, 1)[1]
            return suffix if marker == "non-incremental/" else f"quantified/{suffix}"
    return value.removeprefix("./")


def normalize_public_id(value: str) -> str:
    marker = "non-incremental/"
    if marker not in value:
        raise ValueError(f"public inventory path lacks {marker!r}: {value}")
    return value.split(marker, 1)[1]


def coverage_class(decided: int, total: int) -> str:
    ratio = decided / total if total else 0.0
    if ratio >= 0.8:
        return "decide-strong"
    if ratio >= 0.2:
        return "partial"
    return "frontier"


def exact_stats(ids_by_hash: dict[str, set[str]]) -> dict[str, int]:
    unique_ids = {item for ids in ids_by_hash.values() for item in ids}
    return {
        "unique_normalized_ids": len(unique_ids),
        "unique_content_sha256": len(ids_by_hash),
        "exact_duplicate_groups": sum(len(ids) > 1 for ids in ids_by_hash.values()),
        "exact_duplicate_excess": len(unique_ids) - len(ids_by_hash),
    }


def manifest_regime(manifest: dict, regime_id: str) -> dict:
    matches = [item for item in manifest["regimes"] if item["id"] == regime_id]
    if len(matches) != 1:
        raise ValueError(f"expected one manifest regime {regime_id!r}")
    return matches[0]


def validate_manifest(manifest: dict) -> None:
    if manifest.get("schema_version") != 1:
        raise ValueError("measurement provenance schema_version must be 1")
    if [item.get("id") for item in manifest.get("regimes", [])] != [
        "regression-scoreboard",
        "public-inventory",
    ]:
        raise ValueError("manifest regimes must be regression-scoreboard, public-inventory")
    for regime in manifest["regimes"]:
        for value in regime.get("artifacts", {}).values():
            path = Path(value)
            if path.is_absolute() or ".." in path.parts or not (ROOT / path).exists():
                raise ValueError(f"unsafe or missing artifact path: {value}")
        if regime.get("official_selection") is not False:
            raise ValueError(f"{regime['id']}: v1 regimes are not official selections")


def build_scoreboard(manifest: dict) -> tuple[list[dict], dict, dict[str, set[str]]]:
    policy = manifest_regime(manifest, "regression-scoreboard")
    scoreboard = load_scoreboard_module()
    source_rows = scoreboard.load_division_baselines() + scoreboard.load_synthetic_baselines()
    rows: list[dict] = []
    global_ids_by_hash: dict[str, set[str]] = defaultdict(set)
    file_occurrences = 0
    aggregate_only = 0

    for source in source_rows:
        artifact = load_json(ROOT / source["file"])
        instances = artifact.get("instances", [])
        timeout_ms = (artifact.get("config") or {}).get("timeout_ms")
        if timeout_ms is None:
            timeout_ms = artifact.get("timeout_ms")
        if not isinstance(timeout_ms, (int, float)) or timeout_ms <= 0:
            raise ValueError(f"{source['file']}: missing positive PAR-2 wall limit")
        row_ids_by_hash: dict[str, set[str]] = defaultdict(set)
        if instances:
            if len(instances) != source["files"]:
                raise ValueError(f"{source['file']}: instance/file count drift")
            for instance in instances:
                raw_path = Path(instance["file"])
                path = raw_path if raw_path.is_absolute() else ROOT / raw_path
                if not path.is_file():
                    raise ValueError(f"missing scoreboard benchmark: {instance['file']}")
                normalized = normalize_scoreboard_id(instance["file"])
                digest = sha256_file(path)
                row_ids_by_hash[digest].add(normalized)
                global_ids_by_hash[digest].add(normalized)
                file_occurrences += 1
        else:
            aggregate_only += source["files"]

        stats = exact_stats(row_ids_by_hash) if instances else {
            "unique_normalized_ids": None,
            "unique_content_sha256": None,
            "exact_duplicate_groups": None,
            "exact_duplicate_excess": None,
        }
        population_class = (
            "synthetic-graduated" if not instances else policy["population_class"]
        )
        rows.append(
            {
                "regime_id": policy["id"],
                "population_id": source["slice"],
                "logic": source["logic"],
                "population_class": population_class,
                "selection_class": policy["selection_class"],
                "official_selection": False,
                "raw_cases": source["files"],
                "file_backed_occurrences": len(instances),
                "aggregate_only_cases": source["files"] - len(instances),
                **stats,
                "sat": source["sat"],
                "unsat": source["unsat"],
                "decided": source["decided"],
                "declined_or_no_answer": source["unknown"] + source["unsupported"],
                "soundness_metric": "disagreement",
                "soundness_failures": source["disagree"],
                "wall_limit_s": timeout_ms / 1000.0,
                "par2_mean_wall_s": source["par2"],
                "par2_source": policy["score_source"],
                "coverage_class": coverage_class(source["decided"], source["files"]),
                "oracle_source": source["ground_truth"],
                "neutral_oracle_status": policy["neutral_oracle_status"],
                "source_family_status": "declared-corpus-slice",
                "operator_profile_status": "logic-only",
                "near_duplicate_status": "not-measured",
            }
        )

    summary = {
        "rows": len(rows),
        "logic_labels": len({row["logic"] for row in rows}),
        "raw_cases": sum(row["raw_cases"] for row in rows),
        "file_backed_occurrences": file_occurrences,
        "aggregate_only_cases": aggregate_only,
        **exact_stats(global_ids_by_hash),
        "repeated_path_occurrence_excess": file_occurrences
        - len({item for ids in global_ids_by_hash.values() for item in ids}),
        "decided": sum(row["decided"] for row in rows),
        "soundness_failures": sum(row["soundness_failures"] for row in rows),
        "neutral_oracle_rows": sum(
            row["neutral_oracle_status"] == "present-on-exact-population" for row in rows
        ),
    }
    if summary["rows"] != policy["expected_rows"]:
        raise ValueError(f"scoreboard row drift: {summary['rows']}")
    if summary["raw_cases"] != policy["expected_raw_cases"]:
        raise ValueError(f"scoreboard population drift: {summary['raw_cases']}")
    return rows, summary, global_ids_by_hash


def classify_public(result: dict) -> str:
    reported = result.get("reported_status")
    expected = result.get("expected_status")
    if reported is None:
        return "no_answer"
    if reported == "unknown":
        return "declined"
    if expected not in {"sat", "unsat"} or reported == expected:
        return "decided_correct"
    return "wrong"


def build_public(manifest: dict) -> tuple[list[dict], dict, dict[str, set[str]]]:
    policy = manifest_regime(manifest, "public-inventory")
    artifacts = policy["artifacts"]
    inventory = load_json(ROOT / artifacts["inventory"])
    raw = load_json(ROOT / artifacts["raw"])
    provenance = load_json(ROOT / artifacts["provenance"])
    provenance_by_id = {item["id"]: item for item in provenance["benchmarks"]}
    if len(provenance_by_id) != len(provenance["benchmarks"]):
        raise ValueError("duplicate normalized IDs in public provenance")

    per_logic: dict[str, dict] = defaultdict(
        lambda: {
            "ids_by_hash": defaultdict(set),
            "families": set(),
            "sat": 0,
            "unsat": 0,
            "declined": 0,
            "no_answer": 0,
            "wrong": 0,
            "known_status_cases": 0,
            "unknown_status_cases": 0,
            "known_status_agreements": 0,
            "known_status_disagreements": 0,
            "unadjudicated_decisions": 0,
            "par2_wall": 0.0,
        }
    )
    wall_limit = float(policy["wall_limit_s"])
    global_ids_by_hash: dict[str, set[str]] = defaultdict(set)

    for raw_path, by_solver in sorted(raw.items()):
        result = by_solver.get(inventory["solver"])
        if result is None:
            raise ValueError(f"public raw row lacks {inventory['solver']}: {raw_path}")
        benchmark_id = normalize_public_id(raw_path)
        prov = provenance_by_id.get(benchmark_id)
        if prov is None:
            raise ValueError(f"public provenance lacks {benchmark_id}")
        outcome = classify_public(result)
        if outcome != prov["outcome_class"]:
            raise ValueError(f"public outcome drift for {benchmark_id}: {outcome}")
        logic = result["logic"]
        if logic != prov["logic"]:
            raise ValueError(f"public logic drift for {benchmark_id}")
        cell = per_logic[logic]
        cell["ids_by_hash"][prov["sha256"]].add(benchmark_id)
        cell["families"].add(prov["source_family"])
        global_ids_by_hash[prov["sha256"]].add(benchmark_id)
        known_status = result.get("expected_status") in {"sat", "unsat"}
        cell["known_status_cases" if known_status else "unknown_status_cases"] += 1
        if outcome == "decided_correct":
            cell[result["reported_status"]] += 1
            cell[
                "known_status_agreements" if known_status else "unadjudicated_decisions"
            ] += 1
            cell["par2_wall"] += float(result["wall_time"])
        else:
            cell[outcome] += 1
            if outcome == "wrong":
                cell["known_status_disagreements"] += 1
            cell["par2_wall"] += 2.0 * wall_limit

    rows: list[dict] = []
    for logic, cell in sorted(per_logic.items()):
        recorded = inventory["per_logic"][logic]
        raw_cases = sum(
            cell[key] for key in ("sat", "unsat", "declined", "no_answer", "wrong")
        )
        decided = cell["sat"] + cell["unsat"]
        if raw_cases != recorded["total"] or decided != recorded.get("decided_correct", 0):
            raise ValueError(f"public inventory count drift for {logic}")
        if cell["wrong"] != recorded.get("WRONG", 0):
            raise ValueError(f"public inventory soundness drift for {logic}")
        rows.append(
            {
                "regime_id": policy["id"],
                "population_id": logic,
                "logic": logic,
                "population_class": policy["population_class"],
                "selection_class": policy["selection_class"],
                "official_selection": False,
                "raw_cases": raw_cases,
                "file_backed_occurrences": raw_cases,
                "aggregate_only_cases": 0,
                **exact_stats(cell["ids_by_hash"]),
                "sat": cell["sat"],
                "unsat": cell["unsat"],
                "decided": decided,
                "declined_or_no_answer": cell["declined"] + cell["no_answer"],
                "soundness_metric": "wrong-verdict",
                "soundness_failures": cell["wrong"],
                "known_status_cases": cell["known_status_cases"],
                "unknown_status_cases": cell["unknown_status_cases"],
                "known_status_agreements": cell["known_status_agreements"],
                "known_status_disagreements": cell["known_status_disagreements"],
                "unadjudicated_decisions": cell["unadjudicated_decisions"],
                "wall_limit_s": wall_limit,
                "par2_mean_wall_s": cell["par2_wall"] / raw_cases,
                "par2_source": policy["score_source"],
                "coverage_class": coverage_class(decided, raw_cases),
                "oracle_source": (
                    "benchmark-status-partial+unadjudicated"
                    if cell["unknown_status_cases"]
                    else "benchmark-status"
                ),
                "neutral_oracle_status": policy["neutral_oracle_status"],
                "source_family_status": f"{len(cell['families'])} exact-path families",
                "operator_profile_status": "logic-only",
                "near_duplicate_status": "not-measured",
            }
        )

    summary = {
        "rows": len(rows),
        "logic_labels": len(rows),
        "raw_cases": sum(row["raw_cases"] for row in rows),
        "file_backed_occurrences": sum(row["file_backed_occurrences"] for row in rows),
        "aggregate_only_cases": 0,
        **exact_stats(global_ids_by_hash),
        "source_families": provenance["summary"]["source_families"],
        "decided": sum(row["decided"] for row in rows),
        "known_status_cases": sum(row["known_status_cases"] for row in rows),
        "unknown_status_cases": sum(row["unknown_status_cases"] for row in rows),
        "known_status_agreements": sum(
            row["known_status_agreements"] for row in rows
        ),
        "known_status_disagreements": sum(
            row["known_status_disagreements"] for row in rows
        ),
        "unadjudicated_decisions": sum(
            row["unadjudicated_decisions"] for row in rows
        ),
        "soundness_failures": sum(row["soundness_failures"] for row in rows),
        "neutral_oracle_rows": sum(
            row["neutral_oracle_status"] == "present-on-exact-population" for row in rows
        ),
    }
    if summary["rows"] != policy["expected_rows"]:
        raise ValueError(f"public row drift: {summary['rows']}")
    if summary["raw_cases"] != policy["expected_raw_cases"]:
        raise ValueError(f"public population drift: {summary['raw_cases']}")
    for summary_key, policy_key in (
        ("known_status_cases", "expected_known_status_cases"),
        ("known_status_agreements", "expected_known_status_agreements"),
        ("unadjudicated_decisions", "expected_unadjudicated_decisions"),
    ):
        if summary[summary_key] != policy[policy_key]:
            raise ValueError(
                f"public {summary_key} drift: {summary[summary_key]}"
            )
    for key in ("files", "unique_content_sha256", "exact_duplicate_groups"):
        expected = provenance["summary"][key]
        actual_key = "raw_cases" if key == "files" else key
        if summary[actual_key] != expected:
            raise ValueError(f"public provenance summary drift for {key}")
    return rows, summary, global_ids_by_hash


def build_report(manifest: dict) -> dict:
    validate_manifest(manifest)
    scoreboard_rows, scoreboard_summary, scoreboard_hashes = build_scoreboard(manifest)
    public_rows, public_summary, public_hashes = build_public(manifest)
    overlap = sorted(set(scoreboard_hashes) & set(public_hashes))
    overlap_rows = []
    for digest in overlap:
        overlap_rows.append(
            {
                "sha256": digest,
                "scoreboard_ids": sorted(scoreboard_hashes[digest]),
                "public_ids": sorted(public_hashes[digest]),
            }
        )
    return {
        "schema": SCHEMA,
        "source_manifest": str(MANIFEST.relative_to(ROOT)),
        "official_reference": manifest["official_reference"],
        "shared_contract": manifest["shared_contract"],
        "summary": {
            "regression_scoreboard": scoreboard_summary,
            "public_inventory": public_summary,
            "cross_regime": {
                "unique_content_overlap": len(overlap),
                "public_content_overlap_pct": 100.0 * len(overlap)
                / public_summary["unique_content_sha256"],
                "scoreboard_content_overlap_pct": 100.0 * len(overlap)
                / scoreboard_summary["unique_content_sha256"],
            },
        },
        "rows": scoreboard_rows + public_rows,
        "cross_regime_exact_overlap": overlap_rows,
    }


def fmt_int(value: int | None) -> str:
    return "—" if value is None else str(value)


def fmt_par2(value: float | None) -> str:
    return "—" if value is None else f"{value:.3f}"


def render_markdown(report: dict) -> str:
    score = report["summary"]["regression_scoreboard"]
    public = report["summary"]["public_inventory"]
    overlap = report["summary"]["cross_regime"]
    lines = [
        "# Measurement provenance and coverage matrix",
        "",
        "> **Generated; do not edit by hand.** Source contract: "
        "[`docs/plan/measurement-provenance-v1.json`](../measurement-provenance-v1.json). "
        "Regenerate with `python3 scripts/gen-measurement-provenance.py`; use "
        "`--check` in validation.",
        "",
        "This is one vocabulary over **two separate measurement regimes**, not one "
        "merged score. The official SMT-COMP selection and PAR-2 rules are reference "
        "policies; neither committed population is an official SMT-COMP selection.",
        "",
        "## Denominator audit",
        "",
        "| Regime | Rows | Raw cases | File-backed | Unique paths | Unique bytes | Aggregate-only | Exact alias groups | Decided | Neutral rows |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
        f"| Curated/regression scoreboard | {score['rows']} | {score['raw_cases']} | {score['file_backed_occurrences']} | {score['unique_normalized_ids']} | {score['unique_content_sha256']} | {score['aggregate_only_cases']} | {score['exact_duplicate_groups']} | {score['decided']} | {score['neutral_oracle_rows']} |",
        f"| Partial public inventory | {public['rows']} | {public['raw_cases']} | {public['file_backed_occurrences']} | {public['unique_normalized_ids']} | {public['unique_content_sha256']} | {public['aggregate_only_cases']} | {public['exact_duplicate_groups']} | {public['decided']} | {public['neutral_oracle_rows']} |",
        "",
        f"The public inventory's legacy {public['decided']}/228 scorer field contains "
        f"**{public['known_status_agreements']} known-status agreements** and "
        f"**{public['unadjudicated_decisions']} unadjudicated decisions**. Its "
        f"{public['unknown_status_cases']} benchmarks without known status do not "
        "inherit benchmark-status correctness credit.",
        "",
        f"The scoreboard's {score['file_backed_occurrences']} file occurrences contract to "
        f"{score['unique_normalized_ids']} normalized paths and **{score['unique_content_sha256']} "
        f"unique byte contents**. Its {score['exact_duplicate_groups']} exact-alias groups "
        f"remove {score['exact_duplicate_excess']} further path identities after path "
        f"deduplication; {score['aggregate_only_cases']} synthetic cases have no file identity "
        "and remain explicit.",
        "",
        f"The regimes overlap on **{overlap['unique_content_overlap']} exact contents**: "
        f"{overlap['public_content_overlap_pct']:.1f}% of the 228-file inventory and "
        f"{overlap['scoreboard_content_overlap_pct']:.1f}% of the scoreboard's unique "
        "file-backed contents. The public inventory is therefore a harder differently "
        "weighted view, but not an independent sample. The two decide rates must not be "
        "averaged or treated as replication.",
        "",
        "## Row matrix",
        "",
        "`PAR-2` is a within-row mean in seconds. `Neutral = absent` means no non-Z3 "
        "solver ran the exact row population; a separately sourced 24-file QF_BV "
        "head-to-head does not grant neutral-oracle credit to the 228-file inventory.",
        "",
        "| Regime | Logic / population | Class | Raw | IDs | SHA | Agg | Sat | Unsat | Miss | Fail | Limit | PAR-2 | Truth | Neutral |",
        "|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|",
    ]
    for row in report["rows"]:
        regime = "scoreboard" if row["regime_id"] == "regression-scoreboard" else "public"
        population = f"`{row['logic']}` / `{row['population_id']}`"
        lines.append(
            f"| {regime} | {population} | `{row['coverage_class']}` | "
            f"{row['raw_cases']} | {fmt_int(row['unique_normalized_ids'])} | "
            f"{fmt_int(row['unique_content_sha256'])} | {row['aggregate_only_cases']} | "
            f"{row['sat']} | {row['unsat']} | {row['declined_or_no_answer']} | "
            f"{row['soundness_failures']} | {row['wall_limit_s']:.0f} | "
            f"{fmt_par2(row['par2_mean_wall_s'])} | "
            f"`{row['oracle_source']}` | absent |"
        )
    lines.extend(
        [
            "",
            "## Interpretation boundary",
            "",
            "- `Raw` counts occurrences. `IDs` deduplicates normalized paths. `SHA` "
            "deduplicates exact bytes. None of these is semantic or near-duplicate "
            "clustering.",
            "- The coverage class is Axeyum-relative observed decide rate, not an "
            "intrinsic benchmark-difficulty label.",
            "- PAR-2 remains row-local because rows have different time limits, hosts, "
            "selection policies, configurations, and sometimes only aggregate data.",
            "- Z3 oracle agreement, benchmark `:status`, and neutral multi-solver "
            "agreement are different evidence classes. V1 records zero neutral rows on "
            "these exact populations.",
            "- Source families are strata, not weights. No global parity percentage is "
            "defined by this artifact.",
            "",
            "## Remaining G1 work",
            "",
            "1. Add syntax-normalized and then semantic near-duplicate experiments "
            "without replacing exact-byte identity.",
            "2. Freeze an official-selection manifest from a complete SMT-LIB release "
            "before calling any score SMT-COMP representative.",
            "3. Run non-Z3 external solvers over each exact claimed population and "
            "record SAT/UNSAT decision-set overlap, not only totals.",
            "4. Define a representative-selection rule before computing any deduplicated "
            "PAR-2; v1 intentionally reports deduplicated denominators only.",
            "5. Add operator profiles and a neutral reference difficulty measure before "
            "using the word `difficulty` as anything stronger than observed coverage.",
            "",
            "The complete machine-readable rows and all 99 exact cross-regime overlap "
            "records are in "
            "[`measurement-provenance-matrix.json`](measurement-provenance-matrix.json).",
        ]
    )
    return "\n".join(lines).rstrip() + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        manifest = load_json(MANIFEST)
        report = build_report(manifest)
        rendered_json = json.dumps(report, indent=2, sort_keys=True) + "\n"
        rendered_md = render_markdown(report)
    except (KeyError, TypeError, ValueError, OSError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1

    outputs = ((OUTPUT_JSON, rendered_json), (OUTPUT_MD, rendered_md))
    if args.check:
        stale = [path for path, text in outputs if not path.is_file() or path.read_text(encoding="utf-8") != text]
        if stale:
            for path in stale:
                print(f"ERROR: {path.relative_to(ROOT)} is stale", file=sys.stderr)
            return 1
    else:
        for path, text in outputs:
            path.write_text(text, encoding="utf-8")

    score = report["summary"]["regression_scoreboard"]
    public = report["summary"]["public_inventory"]
    overlap = report["summary"]["cross_regime"]
    print(
        "MEASUREMENT_PROVENANCE|"
        f"rows={len(report['rows'])}|"
        f"score_raw={score['raw_cases']}|score_sha={score['unique_content_sha256']}|"
        f"public_raw={public['raw_cases']}|public_sha={public['unique_content_sha256']}|"
        f"public_known_agree={public['known_status_agreements']}|"
        f"public_unadjudicated={public['unadjudicated_decisions']}|"
        f"overlap_sha={overlap['unique_content_overlap']}|neutral_rows=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
