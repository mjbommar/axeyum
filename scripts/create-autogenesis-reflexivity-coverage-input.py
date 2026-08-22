#!/usr/bin/env python3
"""Generate the proof-free train/development input for reflexivity coverage."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import sys
from collections.abc import Callable
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
NURSERY = ROOT / "artifacts/autogenesis/nursery-v1.json"
SOURCE_POLICY = ROOT / "artifacts/autogenesis/mathlib-nursery-source-policy-v1.json"
FACTS = ROOT / "artifacts/facts"
PARTITIONS = {"train", "development"}
TARGET_ROOT = "Axeyum.Autogenesis.Coverage"


class CoverageInputError(RuntimeError):
    """The coverage input would violate the frozen evaluation boundary."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode()).hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise CoverageInputError(f"{path} is not an object")
    return value


def fact_path(fact_id: str) -> pathlib.Path:
    return FACTS / (fact_id.replace("F:", "F-") + ".json")


LIVE_POPULATION = 157


def build(
    nursery: dict[str, Any],
    fact_loader: Callable[[str], dict[str, Any]],
    modules_by_family: dict[str, str],
    expected: int | None = None,
) -> tuple[str, dict[str, Any]]:
    if nursery.get("state") != "frozen-evaluation":
        raise CoverageInputError("nursery is not frozen")
    selected = sorted(
        (
            entry
            for entry in nursery.get("entries", [])
            if entry.get("partition") in PARTITIONS
        ),
        key=lambda entry: entry["fact_id"],
    )
    # LIVE_POPULATION is the tripwire for generating a NEW census: an unexplained
    # change to the evaluation population must stop this rather than silently
    # re-size it. 157 = train 78 + development 79, after the `natural-gcd` family
    # left held-out on 2026-08-22 (ADR-0542).
    #
    # `expected` exists because RE-VERIFYING an OLD census is a different
    # question. A frozen capture is evidence about the population as it stood
    # when it was taken, so checking it against the LIVE manifest guarantees it
    # goes stale the moment the population legitimately changes -- which is
    # exactly what happened on 2026-08-22, turning a valid 2026-08-19 census into
    # a red gate that said nothing about the census. The re-verifier passes the
    # count its own manifest records instead.
    want = LIVE_POPULATION if expected is None else expected
    if len(selected) != want:
        raise CoverageInputError(
            f"expected {want} train/development entries, found {len(selected)}"
        )
    if {entry["partition"] for entry in selected} != PARTITIONS:
        raise CoverageInputError("coverage input does not contain both open partitions")

    families = {entry["family"] for entry in selected}
    if not families <= set(modules_by_family):
        raise CoverageInputError("source policy lacks a selected family module")
    imports = sorted({modules_by_family[family] for family in families})
    source = [
        *(f"import {module}" for module in imports),
        "",
        "namespace Axeyum.Autogenesis.Coverage",
        "",
    ]
    rows: list[dict[str, Any]] = []
    for index, entry in enumerate(selected):
        fact = fact_loader(entry["fact_id"])
        if fact.get("id") != entry["fact_id"]:
            raise CoverageInputError(f"fact identity mismatch for {entry['fact_id']}")
        formal = fact.get("formal", {})
        if formal.get("language") != "lean4-surface":
            raise CoverageInputError(f"unexpected language for {entry['fact_id']}")
        statement = formal.get("statement")
        if not isinstance(statement, str) or not statement.strip():
            raise CoverageInputError(f"missing statement for {entry['fact_id']}")
        local_name = f"r{index:03d}"
        target = f"{TARGET_ROOT}.{local_name}"
        source.append(f"def {local_name} : Prop :=")
        source.extend(f"  {line}" for line in statement.splitlines())
        source.append("")
        rows.append(
            {
                "fact_id": entry["fact_id"],
                "family": entry["family"],
                "partition": entry["partition"],
                "target_definition": target,
                "artifact_file": f"{local_name}.ndjson",
                "source_module": modules_by_family[entry["family"]],
                "statement_sha256": sha256_text(statement),
            }
        )
    source.extend(["end Axeyum.Autogenesis.Coverage", ""])
    rendered = "\n".join(source)
    mapping: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-reflexivity-coverage-input",
        "state": "proof-free-source-input",
        "authority": {
            "nursery_sha256": digest(nursery),
            "partitions_inspected": ["development", "train"],
            "held_out_inspected": False,
            "proof_bodies_accessed": False,
            "target_outcomes_accessed": False,
            "facts_opened": len(rows),
        },
        "lean_module": "AxeyumAutogenesisReflexivityCoverage",
        "imports": imports,
        "lean_source_sha256": sha256_text(rendered),
        "rows": rows,
    }
    mapping["input_sha256"] = digest(mapping)
    return rendered, mapping


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-output", type=pathlib.Path, required=True)
    parser.add_argument("--mapping-output", type=pathlib.Path, required=True)
    args = parser.parse_args()
    try:
        policy = load(SOURCE_POLICY)
        modules_by_family = {
            row["theme"]: row["module"] for row in policy.get("families", [])
        }
        source, mapping = build(
            load(NURSERY), lambda fact_id: load(fact_path(fact_id)), modules_by_family
        )
        args.lean_output.write_text(source)
        args.mapping_output.write_text(
            json.dumps(mapping, indent=2, ensure_ascii=False) + "\n"
        )
        print(
            "AUTOGENESIS_REFLEXIVITY_COVERAGE_INPUT_OK|"
            f"{mapping['input_sha256']}|rows={len(mapping['rows'])}|held_out=0"
        )
        return 0
    except (OSError, KeyError, TypeError, json.JSONDecodeError, CoverageInputError) as error:
        print(f"autogenesis-reflexivity-coverage-input: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
