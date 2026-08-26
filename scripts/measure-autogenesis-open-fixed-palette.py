#!/usr/bin/env python3
"""Measure bounded application over proof-free open-goal capsules.

The NDJSON capsules and their fact-to-definition map are external inputs.  This
script records their hashes and replays the same fixed, target-independent
candidate palette for every goal.  It never changes fact status or registers
an operation.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import Counter
from pathlib import Path
from typing import Any

from axeyum import producers
from axeyum.kernel import Declaration

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "artifacts/autogenesis/open-fixed-palette-census-v1.json"
NURSERY = ROOT / "artifacts/autogenesis/nursery-v1.json"
CANDIDATES = tuple(
    sorted(
        (
            "Eq.refl",
            "Eq.symm",
            "Eq.trans",
            "congrArg",
            "Nat.zero_add",
            "Nat.add_zero",
            "Nat.mul_one",
            "Nat.one_mul",
            "Nat.le_refl",
            "Nat.le_trans",
            "Nat.succ_le_succ",
            "Nat.zero_le",
            "Nat.not_succ_le_zero",
        )
    )
)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def capsule_path(directory: Path, fact_id: str) -> Path:
    return directory / f"{fact_id.replace(':', '-', 1)}.ndjson"


def classify_statement_import_error(message: str) -> dict[str, Any]:
    trusted = re.search(r'trusted declaration "([^"]+)" \(([^)]+)\)', message)
    if trusted:
        return {
            "reason_kind": "TrustedDeclarationInStatementClosure",
            "trusted_declaration": trusted.group(1),
            "trusted_declaration_kind": trusted.group(2),
        }
    candidate = re.search(
        r'candidate declaration "([^"]+)" occurs (\d+) times; expected one',
        message,
    )
    if candidate:
        return {
            "reason_kind": "CandidateDeclarationUnavailable",
            "candidate_declaration": candidate.group(1),
            "candidate_occurrence_count": int(candidate.group(2)),
        }
    candidate_trusted = re.search(
        r'candidate declaration "([^"]+)" reaches (\d+) trusted declaration\(s\)',
        message,
    )
    if candidate_trusted:
        return {
            "reason_kind": "CandidateClosureReachesTrustedDeclaration",
            "candidate_declaration": candidate_trusted.group(1),
            "candidate_trusted_declaration_count": int(candidate_trusted.group(2)),
        }
    return {"reason_kind": "UnclassifiedStatementImportError", "message": message}


def eligible_mapping(
    mapping: dict[str, str], nursery: dict[str, Any]
) -> tuple[dict[str, str], list[str]]:
    partitions = {
        row["fact_id"]: row["partition"]
        for row in nursery.get("entries", [])
        if isinstance(row, dict)
        and isinstance(row.get("fact_id"), str)
        and isinstance(row.get("partition"), str)
    }
    missing = sorted(set(mapping) - set(partitions))
    if missing:
        raise ValueError(f"mapping contains facts absent from the nursery: {missing}")
    unsupported = sorted(
        fact_id
        for fact_id in mapping
        if partitions[fact_id] not in {"train", "development", "held-out"}
    )
    if unsupported:
        raise ValueError(f"mapping contains unsupported nursery partitions: {unsupported}")
    excluded = sorted(
        fact_id for fact_id in mapping if partitions[fact_id] == "held-out"
    )
    eligible = {
        fact_id: target
        for fact_id, target in mapping.items()
        if partitions[fact_id] in {"train", "development"}
    }
    return eligible, excluded


def population_mapping(population: dict[str, Any]) -> dict[str, str]:
    outcomes = population.get("outcomes")
    if not isinstance(outcomes, list):
        raise ValueError("population must contain an outcomes array")
    mapping = {}
    for row in outcomes:
        if (
            not isinstance(row, dict)
            or not isinstance(row.get("fact_id"), str)
            or not isinstance(row.get("target_definition"), str)
        ):
            raise ValueError(
                "every population outcome must name string fact_id and target_definition"
            )
        if row["fact_id"] in mapping:
            raise ValueError("population contains duplicate fact_id rows")
        mapping[row["fact_id"]] = row["target_definition"]
    return mapping


def measure(
    mapping_path: Path | None,
    capsule_directory: Path,
    population_path: Path | None = None,
    must_decline_path: Path | None = None,
    ranking_path: Path | None = None,
    transport_native_candidates: bool = False,
    retrieved_induction: bool = False,
) -> dict[str, Any]:
    if transport_native_candidates and ranking_path is None:
        raise ValueError("native candidate transport requires --ranking")
    if retrieved_induction and not transport_native_candidates:
        raise ValueError("retrieved induction requires --transport-native-candidates")
    population_bytes = population_path.read_bytes() if population_path else None
    if mapping_path is None:
        if population_bytes is None:
            raise ValueError("either mapping_path or population_path is required")
        mapping_bytes = population_bytes
        mapping = population_mapping(json.loads(population_bytes))
    else:
        mapping_bytes = mapping_path.read_bytes()
        mapping = json.loads(mapping_bytes)
    nursery_bytes = NURSERY.read_bytes()
    nursery = json.loads(nursery_bytes)
    mapping, excluded_held_out = eligible_mapping(mapping, nursery)
    population_source = None
    if population_path is not None:
        assert population_bytes is not None
        selected_mapping = population_mapping(json.loads(population_bytes))
        selected = set(selected_mapping)
        absent = sorted(selected - set(mapping))
        if absent:
            raise ValueError(f"population contains facts absent from mapping: {absent}")
        mapping = {
            fact_id: target
            for fact_id, target in mapping.items()
            if fact_id in selected
        }
        mismatched = sorted(
            fact_id
            for fact_id, target in mapping.items()
            if selected_mapping[fact_id] != target
        )
        if mismatched:
            raise ValueError(
                f"population target definitions disagree with mapping: {mismatched}"
            )
        population_source = {
            "path": str(population_path),
            "sha256": digest(population_bytes),
        }
    must_decline_ids: set[str] = set()
    must_decline_source = None
    if must_decline_path is not None:
        must_decline_bytes = must_decline_path.read_bytes()
        must_decline = json.loads(must_decline_bytes)
        entries = must_decline.get("entries")
        if not isinstance(entries, list):
            raise ValueError("must-decline population must contain an entries array")
        for entry in entries:
            if not isinstance(entry, dict) or not isinstance(entry.get("fact_id"), str):
                raise ValueError("every must-decline entry must name a string fact_id")
            if entry["fact_id"] in must_decline_ids:
                raise ValueError("must-decline population contains duplicate fact_id rows")
            must_decline_ids.add(entry["fact_id"])
        must_decline_source = {
            "path": str(must_decline_path),
            "sha256": digest(must_decline_bytes),
        }
    ranked_candidates: dict[str, tuple[str, ...]] = {}
    ranking_source = None
    if ranking_path is not None:
        ranking_bytes = ranking_path.read_bytes()
        ranking = json.loads(ranking_bytes)
        held_out = set(ranking.get("excluded_held_out_fact_ids", []))
        for goal in ranking.get("goals", []):
            if not isinstance(goal, dict) or not isinstance(goal.get("fact_id"), str):
                raise ValueError("every ranking goal must name a string fact_id")
            fact_id = goal["fact_id"]
            if fact_id in held_out:
                raise ValueError(f"held-out fact appears in ranking goals: {fact_id}")
            candidates = goal.get("candidates")
            if not isinstance(candidates, list):
                raise ValueError(f"ranking goal has no candidate list: {fact_id}")
            ranked_candidates[fact_id] = tuple(
                row["kernel_declaration_id"]
                for row in candidates
                if isinstance(row, dict)
                and isinstance(row.get("kernel_declaration_id"), str)
            )
        absent = sorted(set(mapping) - set(ranked_candidates))
        if absent:
            raise ValueError(f"measured facts are absent from ranking: {absent}")
        ranking_source = {"path": str(ranking_path), "sha256": digest(ranking_bytes)}
    outcomes = []
    for fact_id, target_definition in sorted(mapping.items()):
        path = capsule_path(capsule_directory, fact_id)
        data = path.read_bytes()
        row: dict[str, Any] = {
            "fact_id": fact_id,
            "target_definition": target_definition,
            "capsule_bytes": len(data),
            "capsule_sha256": digest(data),
            "evaluation_class": (
                "must-decline-control"
                if fact_id in must_decline_ids
                else "positive-target"
            ),
        }
        candidate_names = ranked_candidates.get(fact_id, CANDIDATES)
        row["candidate_declarations"] = list(candidate_names)
        try:
            imported = producers.import_candidate_statement_ndjson(
                data,
                None,
                target_definition,
                list(CANDIDATES if transport_native_candidates else candidate_names),
            )
            kernel = imported.kernel()
            if transport_native_candidates:
                executable_candidates = []
                transport_outcomes = []
                for candidate_name in candidate_names:
                    if kernel.get_declaration(candidate_name) is not None:
                        executable_candidates.append(
                            kernel.name(candidate_name, must_exist=True)
                        )
                        transport_outcomes.append(
                            {
                                "candidate_declaration": candidate_name,
                                "result": "capsule-existing",
                            }
                        )
                        continue
                    try:
                        transported = producers.transport_native_candidate(
                            imported, candidate_name
                        )
                        executable_candidates.append(transported.candidate)
                        transport_outcomes.append(
                            {
                                "candidate_declaration": candidate_name,
                                "result": transported.disposition,
                                "source_closure_size": transported.source_closure_size,
                                "added_theorems": transported.added_theorems,
                                "added_definitions": transported.added_definitions,
                                "receipt_sha256": transported.receipt_sha256,
                            }
                        )
                    except producers.CandidateTransportError as error:
                        transport_outcomes.append(
                            {
                                "candidate_declaration": candidate_name,
                                "result": "transport-declined",
                                "reason_kind": error.variant,
                                "debug": error.debug,
                            }
                        )
                row["candidate_transport"] = transport_outcomes
            else:
                executable_candidates = [
                    kernel.name(name, must_exist=True) for name in candidate_names
                ]
            if retrieved_induction:
                candidate = producers.propose_bounded_induction_with_rewrites(
                    kernel,
                    imported.goal(),
                    executable_candidates,
                )
            else:
                candidate = producers.propose_bounded_application(
                    kernel,
                    imported.goal(),
                    executable_candidates,
                )
            admitted = kernel.name("Axeyum.OpenCensus.Verified", must_exist=False)
            kernel.add_declaration(
                Declaration.theorem(admitted, [], imported.goal(), candidate.proof)
            )
            row.update(
                result="accepted",
                axiom_footprint=kernel.axiom_footprint(admitted),
                theorem_dependencies=kernel.theorem_dependencies(admitted),
                binders_used=candidate.binders_used,
                **(
                    {"inductions_used": candidate.inductions_used}
                    if retrieved_induction
                    else {
                        "application_depth": candidate.application_depth,
                        "terms_considered": candidate.terms_considered,
                    }
                ),
            )
        except producers.Declined as decline:
            row.update(result="declined", reason_kind=decline.reason.kind)
        except producers.StatementImportError as error:
            message = str(error)
            row.update(result="import_rejected", **classify_statement_import_error(message))
        outcomes.append(row)

    counts = Counter(row["result"] for row in outcomes)
    decline_reasons = Counter(
        row["reason_kind"] for row in outcomes if row["result"] == "declined"
    )
    rejection_declarations = Counter(
        row.get("trusted_declaration")
        or row.get("candidate_declaration")
        or "<unclassified>"
        for row in outcomes
        if row["result"] == "import_rejected"
    )
    class_counts = Counter(row["evaluation_class"] for row in outcomes)
    result_class_counts = Counter(
        (row["result"], row["evaluation_class"]) for row in outcomes
    )
    transport_counts = Counter(
        transport["result"]
        for row in outcomes
        for transport in row.get("candidate_transport", [])
    )
    transport_decline_reasons = Counter(
        transport["reason_kind"]
        for row in outcomes
        for transport in row.get("candidate_transport", [])
        if transport["result"] == "transport-declined"
    )
    result = {
        "schema_version": 4 if retrieved_induction else (3 if transport_native_candidates else 2),
        "kind": (
            "axeyum-open-ranked-transport-induction-census"
            if retrieved_induction
            else (
                "axeyum-open-ranked-transport-application-census"
                if transport_native_candidates
                else "axeyum-open-fixed-palette-census"
            )
        ),
        "state": "train-development-measurement-held-out-excluded",
        "authority": "measurement only; no operation registration or fact admission",
        "supersedes": "the initial 80-row exploratory run, which improperly executed the grammar on 23 held-out targets; it found no proof and read no source proof body, but its held-out outcomes are contaminated and carry no evaluation credit",
        "source": {
            "mathlib_commit": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
            "lean_version": "4.30.0",
            "lean4export_format": "3.1.0",
            "mapping_sha256": digest(mapping_bytes),
            "nursery_sha256": digest(nursery_bytes),
            "external_capsule_directory": str(capsule_directory),
        },
        "strategy": {
            "producer": (
                "bounded-induction-with-retrieved-rewrites"
                if retrieved_induction
                else "bounded-application"
            ),
            "candidate_rule": (
                "held-out-safe deterministic per-goal ranking"
                if ranking_path is not None
                else "one fixed target-independent palette for every goal"
            ),
            "candidate_declarations": (
                None if ranking_path is not None else list(CANDIDATES)
            ),
            "native_candidate_transport": transport_native_candidates,
            "retrieved_induction": retrieved_induction,
            "forbidden_inputs": [
                "target theorem proof",
                "held-out goal identities or statements",
                "per-target hand-authored candidate selection",
                "candidate theorem proof bodies during retrieval",
                "transitive declaration closure as search candidates",
            ],
        },
        "census": {
            "population": len(outcomes),
            "excluded_held_out": len(excluded_held_out),
            "accepted": counts["accepted"],
            "declined": counts["declined"],
            "import_rejected": counts["import_rejected"],
            "conversion_percent": round(
                100 * counts["accepted"] / len(outcomes), 1
            ),
            "decline_reasons": dict(sorted(decline_reasons.items())),
            "rejection_declarations": dict(sorted(rejection_declarations.items())),
            "evaluation_classes": dict(sorted(class_counts.items())),
            "result_by_evaluation_class": {
                result: {
                    classification: result_class_counts[(result, classification)]
                    for classification in ("positive-target", "must-decline-control")
                }
                for result in ("accepted", "declined", "import_rejected")
            },
            "candidate_transport": {
                "outcomes": dict(sorted(transport_counts.items())),
                "decline_reasons": dict(sorted(transport_decline_reasons.items())),
            },
        },
        "excluded_held_out_fact_ids": excluded_held_out,
        "outcomes": outcomes,
        "limitations": (
            "Ranked native theorem transport supplies explicit premises to bounded induction and retrieved equality rewriting. Held-out rows are excluded before capsule access. Import and transport rejections measure compatibility boundaries, not proposition falsehood."
            if retrieved_induction
            else (
                "Ranked native theorem transport makes retrieved premises executable but does not enlarge the bounded application grammar. Held-out rows are excluded before capsule access. Import and transport rejections measure compatibility boundaries, not proposition falsehood."
                if transport_native_candidates
                else "One fixed elementary palette is a negative baseline, not a general producer evaluation. Held-out rows are excluded before capsule access. Import rejections measure statement-boundary incompatibility, not solver inability or proposition falsehood."
            )
        ),
    }
    if population_source is not None:
        result["source"]["population_filter"] = population_source
    if must_decline_source is not None:
        result["source"]["must_decline_population"] = must_decline_source
    if ranking_source is not None:
        result["source"]["candidate_ranking"] = ranking_source
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mapping", type=Path)
    parser.add_argument("--capsule-directory", type=Path, required=True)
    parser.add_argument(
        "--population",
        type=Path,
        help="optional committed census whose outcomes define the exact fact subset",
    )
    parser.add_argument(
        "--ranking",
        type=Path,
        help="optional held-out-safe per-goal candidate ranking",
    )
    parser.add_argument(
        "--transport-native-candidates",
        action="store_true",
        help="compose each ranked native theorem independently into the imported goal kernel",
    )
    parser.add_argument(
        "--retrieved-induction",
        action="store_true",
        help="run bounded induction with the transported ranked declarations as rewrite premises",
    )
    parser.add_argument(
        "--must-decline-population",
        type=Path,
        help="optional independently checked false-control population",
    )
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.mapping is None and args.population is None:
        parser.error("one of --mapping or --population is required")
    rendered = json.dumps(
        measure(
            args.mapping,
            args.capsule_directory,
            args.population,
            args.must_decline_population,
            args.ranking,
            args.transport_native_candidates,
            args.retrieved_induction,
        ),
        indent=2,
        sort_keys=True,
    ) + "\n"
    if args.check:
        if not args.output.is_file() or args.output.read_text() != rendered:
            print("OPEN_FIXED_PALETTE_CENSUS_ERROR|artifact is stale")
            return 1
    else:
        args.output.write_text(rendered)
    census = json.loads(rendered)["census"]
    print(
        "OPEN_FIXED_PALETTE_CENSUS|"
        f"population={census['population']}|accepted={census['accepted']}|"
        f"declined={census['declined']}|import_rejected={census['import_rejected']}|"
        f"excluded_held_out={census['excluded_held_out']}|"
        f"conversion_percent={census['conversion_percent']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
