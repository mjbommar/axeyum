#!/usr/bin/env python3
"""Derive deterministic, non-executed child shards for Lean U2 profiles."""

from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
import sys
from pathlib import Path
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

MANIFEST = ROOT / "docs/plan/lean-u2-official-child-shards-v1.json"
OUT_JSON = ROOT / "docs/plan/generated/lean-u2-official-child-shards.json"
OUT_MD = ROOT / "docs/plan/generated/lean-u2-official-child-shards.md"

U2_PATH = ROOT / "docs/plan/lean-u2-test-authority-v1.json"
PROFILES_PATH = ROOT / "docs/plan/lean-u2-official-ci-profiles-v1.json"
R3_PATH = ROOT / "docs/plan/lean-u2-official-execution-tl0.6.3-m0-r3-v1.json"

SCHEMA = "axeyum-lean-u2-official-child-shards-v1"
REPORT_SCHEMA = "axeyum-lean-u2-official-child-shards-report-v1"
AS_OF = "2026-07-22"
MAX_CASES_PER_SHARD = 64

SOURCE_HASHES = {
    "docs/plan/lean-u2-test-authority-v1.json": (
        "d7446e7965bac100ac6b5c607cbb7c87b5b80063fc23b3ec998fff2736d5d18e"
    ),
    "docs/plan/lean-u2-official-ci-profiles-v1.json": (
        "4817d177828797f9dab9e62cf7647732d2b9c3788db7b7b4e3461bc868948548"
    ),
    "docs/plan/lean-u2-official-execution-tl0.6.3-m0-r3-v1.json": (
        "fe04cd96fb9f08c8a0e834ec11f954c3c8172912332da28fc2a92adf0cedb475"
    ),
}
VALIDATOR_HASHES = {
    "scripts/gen-lean-u2-test-authority.py": (
        "2c173c2621c374179ee346aa8cc710a84e8c37792b2ead25d4e80f8144ad34ba"
    ),
    "scripts/gen-lean-u2-official-ci-profiles.py": (
        "4b4b2d0fca8acaee1f90e8a7f143067db6596e6aa7d558e9a877639db878e246"
    ),
    "scripts/lean_u2_official_execution_r3_result.py": (
        "955f91838debb65b939492108d8a5cd66a0cb5834f9b1e03a69d80a8afbe3f73"
    ),
}

MEMBERSHIP_DOMAIN = "axeyum-lean-u2-official-membership-plan-v1"
SHARD_DOMAIN = "axeyum-lean-u2-official-child-shard-v1"
SELECTION_DOMAIN = "axeyum-lean-u2-official-selection-binding-v1"
ATTEMPT_DOMAIN = "axeyum-lean-u2-official-attempt-binding-v1"
HISTORY_DOMAIN = "axeyum-lean-u2-official-historical-observation-v1"

ZERO_CREDITS = {
    "official_executed_attempts": 0,
    "official_completed_cases": 0,
    "official_profile_completions": 0,
    "official_provider_completions": 0,
    "axeyum_outcomes": 0,
    "paired_cells": 0,
    "performance_rows": 0,
    "complete_populations": 0,
    "complete_axes": 0,
    "satisfied_gates": 0,
    "parity_credit": 0,
}
CLAIMS = {
    "parent_memberships_partitioned": True,
    "selection_bindings_complete": True,
    "attempt_bindings_complete": True,
    "historical_observation_annotated": True,
    "official_execution_complete": False,
    "official_provider_reproduced": False,
    "axeyum_observed": False,
    "matched_pair_formed": False,
    "performance_measured": False,
    "lean_parity_established": False,
}


class ShardError(RuntimeError):
    """A fail-closed child-shard derivation or validation failure."""


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        allow_nan=False,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def domain_digest(domain: str, value: Any) -> str:
    return sha256_bytes(domain.encode("ascii") + b"\0" + canonical_bytes(value))


def seal(record: dict[str, Any], domain: str) -> dict[str, Any]:
    result = copy.deepcopy(record)
    result["record_sha256"] = domain_digest(
        domain, {key: value for key, value in result.items() if key != "record_sha256"}
    )
    return result


def json_text(value: Any) -> str:
    return json.dumps(value, indent=2, ensure_ascii=False) + "\n"


def load_json(path: Path) -> dict[str, Any]:
    try:
        with path.open(encoding="utf-8") as handle:
            value = json.load(handle)
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise ShardError(f"cannot read canonical JSON {path}: {error}") from error
    if not isinstance(value, dict):
        raise ShardError(f"top-level JSON must be an object: {path}")
    return value


def load_script(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ShardError(f"cannot import validator {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def validate_frozen_inputs() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    for relative, expected in SOURCE_HASHES.items():
        path = ROOT / relative
        if not path.is_file() or sha256_file(path) != expected:
            raise ShardError(f"frozen source authority drift: {relative}")
    for relative, expected in VALIDATOR_HASHES.items():
        path = ROOT / relative
        if not path.is_file() or sha256_file(path) != expected:
            raise ShardError(f"frozen validator source drift: {relative}")

    u2 = load_json(U2_PATH)
    profiles = load_json(PROFILES_PATH)
    r3 = load_json(R3_PATH)
    u2_validator = load_script(
        "lean_u2_child_shards_u2_validator",
        ROOT / "scripts/gen-lean-u2-test-authority.py",
    )
    profiles_validator = load_script(
        "lean_u2_child_shards_profiles_validator",
        ROOT / "scripts/gen-lean-u2-official-ci-profiles.py",
    )
    r3_validator = load_script(
        "lean_u2_child_shards_r3_validator",
        ROOT / "scripts/lean_u2_official_execution_r3_result.py",
    )
    failures = [
        *(f"U2: {item}" for item in u2_validator.validate_manifest(u2)),
        *(f"profiles: {item}" for item in profiles_validator.validate_manifest(profiles)),
        *(f"R3: {item}" for item in r3_validator.validate_result_authority(r3)),
    ]
    if failures:
        raise ShardError("invalid frozen parent authority: " + "; ".join(failures))
    return u2, profiles, r3


def logical_seals(relative: str, value: dict[str, Any]) -> dict[str, str]:
    if relative.endswith("lean-u2-test-authority-v1.json"):
        return {
            "cases_sha256": value["cases_sha256"],
            "content_files_sha256": value["content_files_sha256"],
        }
    if relative.endswith("lean-u2-official-ci-profiles-v1.json"):
        return {
            "selection_sets_sha256": value["selection_sets_sha256"],
            "attempts_sha256": value["attempts_sha256"],
        }
    return {"record_sha256": value["record_sha256"]}


def build_authority() -> dict[str, Any]:
    u2, profiles, r3 = validate_frozen_inputs()
    cases = u2["cases"]
    case_by_id = {case["id"]: case for case in cases}
    if len(case_by_id) != len(cases):
        raise ShardError("registration authority contains duplicate case IDs")

    selection_to_key: dict[str, tuple[str, ...]] = {}
    membership_selections: dict[tuple[str, ...], list[str]] = {}
    digest_to_key: dict[str, tuple[str, ...]] = {}
    for selection in profiles["selection_sets"]:
        case_ids = selection["selected_case_ids"]
        if any(case_id not in case_by_id for case_id in case_ids):
            raise ShardError(f"{selection['id']}: unknown registered case")
        observed_digest = domain_digest(
            "axeyum-lean-u2-official-selected-case-ids-v1", case_ids
        )
        parent_digest = selection["selected_ids_sha256"]
        # Parent digests use their own documented canonical-JSON domain. Retain
        # both identities; exact list equality is the only deduplication key.
        key = tuple(case_ids)
        prior_key = digest_to_key.get(parent_digest)
        if prior_key is not None and prior_key != key:
            raise ShardError("parent selected-list digest collision")
        digest_to_key[parent_digest] = key
        selection_to_key[selection["id"]] = key
        membership_selections.setdefault(key, []).append(selection["id"])
        if len(case_ids) != selection["selected_count"]:
            raise ShardError(f"{selection['id']}: selected count drift")
        if not observed_digest:
            raise ShardError("unreachable selected-list digest failure")

    historical_case_id = r3["case"]["id"]
    historical_case = case_by_id.get(historical_case_id)
    if historical_case is None:
        raise ShardError("historical R3 case is absent from U2 registration")

    membership_id_by_key: dict[tuple[str, ...], str] = {}
    parent_digest_by_key: dict[tuple[str, ...], str] = {}
    for selection in profiles["selection_sets"]:
        key = selection_to_key[selection["id"]]
        parent_digest = selection["selected_ids_sha256"]
        current = parent_digest_by_key.setdefault(key, parent_digest)
        if current != parent_digest:
            raise ShardError("equal ordered membership has unequal parent digest")
        membership_id_by_key[key] = f"membership-{parent_digest}"
    if len(set(membership_id_by_key.values())) != len(membership_id_by_key):
        raise ShardError("membership ID collision")

    shards: list[dict[str, Any]] = []
    membership_plans: list[dict[str, Any]] = []
    for key, membership_id in sorted(
        membership_id_by_key.items(), key=lambda item: item[1]
    ):
        case_ids = list(key)
        shard_ids = []
        for ordinal, start in enumerate(range(0, len(case_ids), MAX_CASES_PER_SHARD)):
            if ordinal >= 10_000:
                raise ShardError("membership exceeds four-digit shard ordinal capacity")
            shard_case_ids = case_ids[start : start + MAX_CASES_PER_SHARD]
            shard_id = f"{membership_id}--shard-{ordinal:04d}"
            shard_ids.append(shard_id)
            shards.append(
                seal(
                    {
                        "id": shard_id,
                        "membership_plan_id": membership_id,
                        "ordinal": ordinal,
                        "start_offset": start,
                        "end_offset": start + len(shard_case_ids),
                        "case_count": len(shard_case_ids),
                        "case_ids_sha256": domain_digest(
                            "axeyum-lean-u2-official-child-shard-case-ids-v1",
                            shard_case_ids,
                        ),
                        "case_ids": shard_case_ids,
                        "first_case_id": shard_case_ids[0],
                        "last_case_id": shard_case_ids[-1],
                        "historical_observation_case_ids": (
                            [historical_case_id]
                            if historical_case_id in shard_case_ids
                            else []
                        ),
                        "outcome": "not-run",
                        "execution_credit": 0,
                        "completion_credit": 0,
                    },
                    SHARD_DOMAIN,
                )
            )
        membership_plans.append(
            seal(
                {
                    "id": membership_id,
                    "selected_count": len(case_ids),
                    "selected_ids_sha256": parent_digest_by_key[key],
                    "selection_set_ids": membership_selections[key],
                    "shard_count": len(shard_ids),
                    "shard_ids_sha256": domain_digest(
                        "axeyum-lean-u2-official-membership-shard-ids-v1", shard_ids
                    ),
                    "shard_ids": shard_ids,
                },
                MEMBERSHIP_DOMAIN,
            )
        )

    membership_by_id = {row["id"]: row for row in membership_plans}
    selection_bindings = []
    for selection in profiles["selection_sets"]:
        membership_id = membership_id_by_key[selection_to_key[selection["id"]]]
        membership = membership_by_id[membership_id]
        selection_bindings.append(
            seal(
                {
                    "selection_set_id": selection["id"],
                    "source_selection_sha256": selection["sha256"],
                    "membership_plan_id": membership_id,
                    "selected_count": selection["selected_count"],
                    "selected_ids_sha256": selection["selected_ids_sha256"],
                    "shard_ids": membership["shard_ids"],
                    "outcome": "not-run",
                },
                SELECTION_DOMAIN,
            )
        )
    selection_binding_by_id = {
        row["selection_set_id"]: row for row in selection_bindings
    }

    attempt_bindings = []
    for attempt in profiles["attempts"]:
        selection = selection_binding_by_id[attempt["selection_set_id"]]
        attempt_bindings.append(
            seal(
                {
                    "attempt_id": attempt["id"],
                    "source_attempt_sha256": attempt["sha256"],
                    "cell_id": attempt["cell_id"],
                    "phase": attempt["phase"],
                    "selection_set_id": attempt["selection_set_id"],
                    "membership_plan_id": selection["membership_plan_id"],
                    "shard_ids": selection["shard_ids"],
                    "outcome": "not-run",
                },
                ATTEMPT_DOMAIN,
            )
        )

    r3_summary = r3["summary"]
    historical = seal(
        {
            "authority_path": R3_PATH.relative_to(ROOT).as_posix(),
            "authority_physical_sha256": SOURCE_HASHES[R3_PATH.relative_to(ROOT).as_posix()],
            "authority_record_sha256": r3["record_sha256"],
            "case_id": historical_case_id,
            "registration_case_sha256": historical_case["sha256"],
            "r3_case_record_sha256": r3["case"]["record_sha256"],
            "process_attempts": r3_summary["process_attempts"],
            "completed_process_attempts": r3_summary["completed_process_attempts"],
            "official_outcomes": r3_summary["official_outcomes"],
            "official_passes": r3_summary["official_passes"],
            "official_failures": r3_summary["official_failures"],
            "parent_profiles_completed": r3_summary["parent_profiles_completed"],
            "providers_completed": r3_summary["providers_completed"],
            "axeyum_outcomes": r3_summary["axeyum_outcomes"],
            "paired_cells": r3_summary["paired_cells"],
            "performance_rows": r3_summary["performance_rows"],
            "credit_scope": "historical-local-singleton-only",
            "completes_m1_shard": False,
        },
        HISTORY_DOMAIN,
    )

    selected_union = sorted(
        {case_id for key in membership_id_by_key for case_id in key}
    )
    source_values = {
        U2_PATH.relative_to(ROOT).as_posix(): u2,
        PROFILES_PATH.relative_to(ROOT).as_posix(): profiles,
        R3_PATH.relative_to(ROOT).as_posix(): r3,
    }
    source_authorities = [
        {
            "path": relative,
            "physical_sha256": physical_sha,
            "schema": source_values[relative]["schema"],
            "logical_seals": logical_seals(relative, source_values[relative]),
        }
        for relative, physical_sha in SOURCE_HASHES.items()
    ]
    validator_sources = [
        {"path": relative, "sha256": source_sha}
        for relative, source_sha in VALIDATOR_HASHES.items()
    ]
    authority = {
        "schema": SCHEMA,
        "as_of": AS_OF,
        "status": "complete-derivation-not-run",
        "scope": "official-u2-child-shard-derivation-not-execution-or-parity",
        "target": profiles["target"],
        "policy": {
            "method": "exact-membership-deduplication-plus-contiguous-bounded-partition",
            "max_cases_per_shard": MAX_CASES_PER_SHARD,
            "preserve_parent_order": True,
            "deduplicate_exact_ordered_membership_only": True,
            "representative_sample": False,
            "canonical_json": "UTF-8; sorted keys; compact separators; no NaN/infinity",
            "digest_construction": "ASCII domain + NUL + canonical JSON bytes",
        },
        "source_authorities": source_authorities,
        "validator_sources": validator_sources,
        "membership_plans_sha256": domain_digest(
            "axeyum-lean-u2-official-membership-plans-v1", membership_plans
        ),
        "membership_plans": membership_plans,
        "shards_sha256": domain_digest(
            "axeyum-lean-u2-official-child-shards-v1", shards
        ),
        "shards": shards,
        "selection_bindings_sha256": domain_digest(
            "axeyum-lean-u2-official-selection-bindings-v1", selection_bindings
        ),
        "selection_bindings": selection_bindings,
        "attempt_bindings_sha256": domain_digest(
            "axeyum-lean-u2-official-attempt-bindings-v1", attempt_bindings
        ),
        "attempt_bindings": attempt_bindings,
        "historical_observation": historical,
        "summary": {
            "registration_cases": len(cases),
            "selection_sets": len(selection_bindings),
            "official_attempts": len(attempt_bindings),
            "distinct_membership_plans": len(membership_plans),
            "distinct_membership_case_occurrences": sum(
                row["selected_count"] for row in membership_plans
            ),
            "physical_child_shards": len(shards),
            "selection_expanded_shard_occurrences": sum(
                len(row["shard_ids"]) for row in selection_bindings
            ),
            "attempt_expanded_shard_occurrences": sum(
                len(row["shard_ids"]) for row in attempt_bindings
            ),
            "selected_case_union": len(selected_union),
            "selected_case_union_sha256": domain_digest(
                "axeyum-lean-u2-official-selected-case-union-v1", selected_union
            ),
            "historical_unique_observed_cases": 1,
            "outcomes_observed_by_m1": 0,
        },
        "claims": CLAIMS,
        "credits": ZERO_CREDITS,
        "residual": [
            "Preregister executable, provider, environment, resource, attempt, completion, and retry identities before executing a child shard.",
            "Execute official child shards and retain complete or explicitly incomplete raw evidence without converting official outcomes into native parity credit.",
            "Implement native Axeyum surfaces and form exact official/Axeyum pairs before any functional parity claim.",
        ],
    }
    return seal(authority, SCHEMA)


def validate_authority(authority: Any) -> list[str]:
    try:
        expected = build_authority()
    except ShardError as error:
        return [str(error)]
    if not isinstance(authority, dict):
        return ["child-shard authority must be an object"]
    if authority != expected:
        return ["canonical child-shard derivation, closure, state, or seal drift"]
    return []


def make_report(authority: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema": REPORT_SCHEMA,
        "generated_from": MANIFEST.relative_to(ROOT).as_posix(),
        "generated_from_sha256": sha256_file(MANIFEST),
        "authority_record_sha256": authority["record_sha256"],
        "status": authority["status"],
        "scope": authority["scope"],
        "target": authority["target"],
        "policy": authority["policy"],
        "summary": authority["summary"],
        "membership_plans": [
            {
                "id": row["id"],
                "selected_count": row["selected_count"],
                "selection_set_ids": row["selection_set_ids"],
                "shard_count": row["shard_count"],
                "selected_ids_sha256": row["selected_ids_sha256"],
                "record_sha256": row["record_sha256"],
            }
            for row in authority["membership_plans"]
        ],
        "selection_bindings": [
            {
                "selection_set_id": row["selection_set_id"],
                "membership_plan_id": row["membership_plan_id"],
                "selected_count": row["selected_count"],
                "shard_count": len(row["shard_ids"]),
                "outcome": row["outcome"],
            }
            for row in authority["selection_bindings"]
        ],
        "historical_observation": authority["historical_observation"],
        "claims": authority["claims"],
        "credits": authority["credits"],
        "residual": authority["residual"],
        "verdict": "complete deterministic child-shard derivation; no execution or parity outcome",
    }


def render_markdown(report: dict[str, Any]) -> str:
    summary = report["summary"]
    lines = [
        "# Lean U2 official child-shard derivation",
        "",
        "> **Generated; do not edit by hand.** Regenerate with `python3 "
        "scripts/gen-lean-u2-official-child-shards.py`; validate with `--check`.",
        "",
        "> **Verdict: complete deterministic child-shard derivation; no execution "
        "or parity outcome.** Every shard and official attempt remains `not-run`.",
        "",
        f"Pinned Lean `{report['target']['version']}` at "
        f"`{report['target']['commit']}`. Exact duplicate ordered memberships are "
        f"factored before contiguous partitions of at most "
        f"{report['policy']['max_cases_per_shard']} cases.",
        "",
        "## Derived closure",
        "",
        f"- {summary['registration_cases']:,} registered U2 cases.",
        f"- {summary['selection_sets']} official selection-set bindings and "
        f"{summary['official_attempts']} official attempt bindings.",
        f"- {summary['distinct_membership_plans']} distinct ordered memberships "
        f"covering {summary['distinct_membership_case_occurrences']:,} factored "
        "case occurrences.",
        f"- {summary['physical_child_shards']} physical child shards; "
        f"{summary['selection_expanded_shard_occurrences']} selection-expanded and "
        f"{summary['attempt_expanded_shard_occurrences']:,} attempt-expanded shard "
        "occurrences.",
        f"- {summary['selected_case_union']:,} unique registered cases in the union.",
        f"- {summary['historical_unique_observed_cases']} historical M0 unique case "
        "annotated; zero M1 outcomes observed.",
        "",
        "## Distinct memberships",
        "",
        "| Membership | Selected | Shards | Referencing selections |",
        "|---|---:|---:|---|",
    ]
    for row in report["membership_plans"]:
        selections = ", ".join(f"`{item}`" for item in row["selection_set_ids"])
        lines.append(
            f"| `{row['id']}` | {row['selected_count']:,} | "
            f"{row['shard_count']} | {selections} |"
        )
    lines.extend(
        [
            "",
            "## Selection bindings",
            "",
            "| Selection | Membership | Cases | Shards | State |",
            "|---|---|---:|---:|---|",
        ]
    )
    for row in report["selection_bindings"]:
        lines.append(
            f"| `{row['selection_set_id']}` | `{row['membership_plan_id']}` | "
            f"{row['selected_count']:,} | {row['shard_count']} | "
            f"`{row['outcome']}` |"
        )
    history = report["historical_observation"]
    lines.extend(
        [
            "",
            "## Historical M0 annotation",
            "",
            f"`{history['case_id']}` retains {history['official_outcomes']} official "
            f"outcomes ({history['official_passes']} pass, "
            f"{history['official_failures']} failure) across "
            f"{history['process_attempts']} process attempts. This is "
            "`historical-local-singleton-only` evidence and completes no M1 shard, "
            "parent profile, provider, Axeyum outcome, pair, performance row, or "
            "parity gate.",
            "",
            "## Non-credit boundary",
            "",
            "- The partition is complete scheduling metadata, not execution.",
            "- A shard, shard zero, or ordered prefix is not a representative sample.",
            "- All execution, completion, native, pair, performance, population, "
            "axis, gate, and parity credits remain zero.",
            "",
            "## Remaining work",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in report["residual"])
    lines.append("")
    return "\n".join(lines)


def expected_outputs(authority: dict[str, Any]) -> dict[Path, str]:
    report = make_report(authority)
    return {OUT_JSON: json_text(report), OUT_MD: render_markdown(report)}


def write_outputs(authority: dict[str, Any]) -> None:
    for path, contents in expected_outputs(authority).items():
        path.write_text(contents, encoding="utf-8")


def check_outputs(authority: dict[str, Any]) -> list[str]:
    failures = []
    for path, contents in expected_outputs(authority).items():
        if not path.is_file():
            failures.append(f"missing generated output {path.relative_to(ROOT)}")
        elif path.read_text(encoding="utf-8") != contents:
            failures.append(f"stale generated output {path.relative_to(ROOT)}")
    return failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        expected = build_authority()
        if args.check:
            if not MANIFEST.is_file():
                raise ShardError(f"missing authority {MANIFEST.relative_to(ROOT)}")
            observed = load_json(MANIFEST)
            failures = validate_authority(observed)
            if not failures and observed != expected:
                failures.append("committed authority differs from canonical derivation")
            failures.extend(check_outputs(observed) if not failures else [])
            if failures:
                raise ShardError("; ".join(failures))
        else:
            MANIFEST.write_text(json_text(expected), encoding="utf-8")
            write_outputs(expected)
    except ShardError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    summary = expected["summary"]
    print(
        "LEAN_U2_CHILD_SHARDS|"
        f"memberships={summary['distinct_membership_plans']}|"
        f"shards={summary['physical_child_shards']}|"
        f"selections={summary['selection_sets']}|"
        f"attempts={summary['official_attempts']}|outcomes=0|pairs=0|parity=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
