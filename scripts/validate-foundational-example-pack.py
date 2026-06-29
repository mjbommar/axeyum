#!/usr/bin/env python3
"""Validate foundational math example-pack structure.

Usage:
  python3 scripts/validate-foundational-example-pack.py
  python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/template-v0
"""

from __future__ import annotations

import json
import re
import sys
from math import gcd
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCHEMA = ROOT / "artifacts" / "ontology" / "foundational-example-pack.schema.json"
CONCEPTS = ROOT / "artifacts" / "ontology" / "foundational-concepts.json"
DEFAULT_ROOT = ROOT / "artifacts" / "examples" / "math"
REQUIRED_FILES = {"README.md", "metadata.json", "model.md", "checks.md", "expected.json"}

CLAIM_STATUS = {"template", "planned", "witnessed", "checked", "proof-gap"}
TRUST_STATUS = {"template", "planned", "replay-only", "checked-evidence", "proof-gap", "numerical"}
EXPECTED_RESULT = {"sat", "unsat", "unknown", "not-run"}
PROOF_STATUS = {"template", "checked", "replay-only", "proof-gap", "lean-horizon", "not-required"}


class ValidationError(Exception):
    pass


def fail(message: str) -> None:
    raise ValidationError(message)


def load_json(path: Path) -> Any:
    try:
        with path.open("r", encoding="utf-8") as handle:
            return json.load(handle)
    except json.JSONDecodeError as error:
        fail(f"{path.relative_to(ROOT)} is invalid JSON: {error}")


def require_keys(context: str, value: dict[str, Any], keys: set[str]) -> None:
    missing = sorted(keys - set(value))
    if missing:
        fail(f"{context} missing required keys: {', '.join(missing)}")


def require_string(context: str, value: Any) -> None:
    if not isinstance(value, str) or not value:
        fail(f"{context} must be a non-empty string")


def require_string_list(context: str, value: Any, *, nonempty: bool = True) -> list[str]:
    if not isinstance(value, list):
        fail(f"{context} must be a list")
    if nonempty and not value:
        fail(f"{context} must not be empty")
    seen: set[str] = set()
    for index, item in enumerate(value):
        if not isinstance(item, str) or not item:
            fail(f"{context}[{index}] must be a non-empty string")
        if item in seen:
            fail(f"{context} repeats {item!r}")
        seen.add(item)
    return value


def check_source(context: str, source: str) -> None:
    if source.startswith(("http://", "https://")):
        return
    path_part = source.split("#", 1)[0]
    if not path_part:
        return
    if not (ROOT / path_part).exists():
        fail(f"{context} references missing local source: {source}")


def concept_indexes() -> tuple[set[str], set[str], set[str]]:
    data = load_json(CONCEPTS)
    rows = data["rows"]
    concept_ids = {row["id"] for row in rows}
    field_ids = {field_id for row in rows for field_id in row["field_ids"]}
    curriculum_nodes = {
        row["curriculum_node"]
        for row in rows
        if row["kind"] == "curriculum-node" and row["curriculum_node"]
    }
    return concept_ids, field_ids, curriculum_nodes


def validate_metadata(
    pack_dir: Path,
    metadata: dict[str, Any],
    concept_ids: set[str],
    field_ids: set[str],
    curriculum_nodes: set[str],
) -> None:
    require_keys(
        "metadata",
        metadata,
        {
            "schema_version",
            "id",
            "title",
            "domain",
            "claim_status",
            "trust_status",
            "concept_ids",
            "field_ids",
            "curriculum_nodes",
            "axeyum_fragments",
            "validator_command",
            "source_refs",
            "expected_results",
            "graduation_criteria",
        },
    )
    if metadata["schema_version"] != 1:
        fail("metadata.schema_version must be 1")
    if metadata["id"] != pack_dir.name:
        fail(f"metadata.id must match directory name {pack_dir.name!r}")
    if not re.fullmatch(r"[a-z0-9][a-z0-9-]*", metadata["id"]):
        fail("metadata.id must be lowercase kebab case")
    require_string("metadata.title", metadata["title"])
    if metadata["domain"] not in {"mathematics", "computer-science", "logic", "statistics"}:
        fail(f"metadata.domain invalid: {metadata['domain']!r}")
    if metadata["claim_status"] not in CLAIM_STATUS:
        fail(f"metadata.claim_status invalid: {metadata['claim_status']!r}")
    if metadata["trust_status"] not in TRUST_STATUS:
        fail(f"metadata.trust_status invalid: {metadata['trust_status']!r}")
    pack_concepts = set(require_string_list("metadata.concept_ids", metadata["concept_ids"]))
    missing_concepts = sorted(pack_concepts - concept_ids)
    if missing_concepts:
        fail(f"metadata.concept_ids references unknown concepts: {', '.join(missing_concepts)}")
    pack_fields = set(require_string_list("metadata.field_ids", metadata["field_ids"]))
    missing_fields = sorted(pack_fields - field_ids)
    if missing_fields:
        fail(f"metadata.field_ids references unknown fields: {', '.join(missing_fields)}")
    nodes = set(require_string_list("metadata.curriculum_nodes", metadata["curriculum_nodes"], nonempty=False))
    missing_nodes = sorted(nodes - curriculum_nodes)
    if missing_nodes:
        fail(f"metadata.curriculum_nodes references unknown nodes: {', '.join(missing_nodes)}")
    require_string_list("metadata.axeyum_fragments", metadata["axeyum_fragments"])
    require_string("metadata.validator_command", metadata["validator_command"])
    sources = require_string_list("metadata.source_refs", metadata["source_refs"])
    for source in sources:
        check_source("metadata.source_refs", source)
    expected_ids = require_string_list(
        "metadata.expected_results",
        metadata["expected_results"],
        nonempty=metadata["claim_status"] != "template",
    )
    if metadata["claim_status"] == "template" and metadata["trust_status"] != "template":
        fail("template claim_status requires template trust_status")
    criteria = require_string_list("metadata.graduation_criteria", metadata["graduation_criteria"])
    if metadata["claim_status"] != "template" and not criteria:
        fail("non-template packs require graduation criteria")
    return expected_ids


def validate_expected(metadata: dict[str, Any], expected: dict[str, Any], expected_ids: list[str]) -> None:
    require_keys("expected", expected, {"schema_version", "pack_id", "witnesses", "checks"})
    if expected["schema_version"] != 1:
        fail("expected.schema_version must be 1")
    if expected["pack_id"] != metadata["id"]:
        fail("expected.pack_id must match metadata.id")

    witness_ids: set[str] = set()
    for index, witness in enumerate(expected["witnesses"]):
        require_keys(f"witnesses[{index}]", witness, {"id", "description", "values"})
        witness_id = witness["id"]
        if witness_id in witness_ids:
            fail(f"duplicate witness id {witness_id}")
        witness_ids.add(witness_id)
        require_string(f"witnesses[{index}].description", witness["description"])
        if not isinstance(witness["values"], dict):
            fail(f"witnesses[{index}].values must be an object")

    check_ids: set[str] = set()
    for index, check in enumerate(expected["checks"]):
        require_keys(
            f"checks[{index}]",
            check,
            {"id", "claim", "expected_result", "validation", "proof_status", "notes"},
        )
        check_id = check["id"]
        if check_id in check_ids:
            fail(f"duplicate check id {check_id}")
        check_ids.add(check_id)
        require_string(f"checks[{index}].claim", check["claim"])
        if check["expected_result"] not in EXPECTED_RESULT:
            fail(f"{check_id}.expected_result invalid: {check['expected_result']!r}")
        require_string(f"checks[{index}].validation", check["validation"])
        if check["proof_status"] not in PROOF_STATUS:
            fail(f"{check_id}.proof_status invalid: {check['proof_status']!r}")
        for witness_id in check.get("witnesses", []):
            if witness_id not in witness_ids:
                fail(f"{check_id} references unknown witness {witness_id}")
        if "data" in check and not isinstance(check["data"], dict):
            fail(f"{check_id}.data must be an object when present")
        require_string(f"checks[{index}].notes", check["notes"])

    if set(expected_ids) != check_ids:
        fail(
            "metadata.expected_results must match expected.checks ids: "
            f"metadata={sorted(expected_ids)} expected={sorted(check_ids)}"
        )
    validate_pack_semantics(metadata, expected)


def require_int(context: str, value: Any) -> int:
    if not isinstance(value, int):
        fail(f"{context} must be an integer")
    return value


def witness_by_id(expected: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {witness["id"]: witness for witness in expected["witnesses"]}


def single_witness_values(check: dict[str, Any], witnesses: dict[str, dict[str, Any]]) -> dict[str, Any]:
    ids = check.get("witnesses", [])
    if len(ids) != 1:
        fail(f"{check['id']} must reference exactly one witness")
    values = witnesses[ids[0]]["values"]
    if not isinstance(values, dict):
        fail(f"{check['id']} witness values must be an object")
    return values


def has_mod_inverse(a: int, modulus: int) -> bool:
    return any((a * candidate) % modulus == 1 for candidate in range(modulus))


def validate_modular_arithmetic(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    crt = checks["crt-coprime-witness"]
    if crt["expected_result"] != "sat":
        fail("crt-coprime-witness must expect sat")
    crt_values = single_witness_values(crt, witnesses)
    x = require_int("crt witness x", crt_values.get("x"))
    congruences = crt_values.get("congruences")
    if not isinstance(congruences, list) or len(congruences) < 2:
        fail("crt witness congruences must contain at least two congruences")
    moduli: list[int] = []
    for index, congruence in enumerate(congruences):
        if not isinstance(congruence, dict):
            fail(f"crt congruence {index} must be an object")
        remainder = require_int(f"crt congruence {index}.remainder", congruence.get("remainder"))
        modulus = require_int(f"crt congruence {index}.modulus", congruence.get("modulus"))
        if modulus <= 1:
            fail(f"crt congruence {index}.modulus must be > 1")
        if x % modulus != remainder % modulus:
            fail(f"crt witness does not satisfy x == {remainder} mod {modulus}")
        moduli.append(modulus)
    for left_index, left in enumerate(moduli):
        for right in moduli[left_index + 1 :]:
            if gcd(left, right) != 1:
                fail(f"CRT moduli must be coprime: {left}, {right}")

    inverse = checks["modular-inverse-witness"]
    if inverse["expected_result"] != "sat":
        fail("modular-inverse-witness must expect sat")
    inv_values = single_witness_values(inverse, witnesses)
    a = require_int("inverse witness a", inv_values.get("a"))
    modulus = require_int("inverse witness modulus", inv_values.get("modulus"))
    inv = require_int("inverse witness inverse", inv_values.get("inverse"))
    if modulus <= 1:
        fail("inverse modulus must be > 1")
    if gcd(a, modulus) != 1:
        fail("inverse witness a must be coprime to modulus")
    if (a * inv) % modulus != 1:
        fail("inverse witness does not multiply to 1 modulo modulus")

    nonunit = checks["composite-nonunit-no-inverse"]
    if nonunit["expected_result"] != "unsat":
        fail("composite-nonunit-no-inverse must expect unsat")
    data = nonunit.get("data", {})
    a = require_int("nonunit data a", data.get("a"))
    modulus = require_int("nonunit data modulus", data.get("modulus"))
    if modulus <= 1:
        fail("nonunit modulus must be > 1")
    if gcd(a, modulus) == 1:
        fail("nonunit data must use a non-coprime residue")
    if has_mod_inverse(a, modulus):
        fail("nonunit check found an inverse unexpectedly")

    fermat = checks["fermat-units-mod-prime"]
    if fermat["expected_result"] != "unsat":
        fail("fermat-units-mod-prime must expect unsat")
    data = fermat.get("data", {})
    modulus = require_int("fermat data modulus", data.get("modulus"))
    exponent = require_int("fermat data exponent", data.get("exponent"))
    if modulus <= 1:
        fail("fermat modulus must be > 1")
    for a in range(1, modulus):
        if gcd(a, modulus) == 1 and pow(a, exponent, modulus) != 1:
            fail(f"fermat counterexample found: a={a}, modulus={modulus}, exponent={exponent}")


def validate_pack_semantics(metadata: dict[str, Any], expected: dict[str, Any]) -> None:
    if metadata["id"] == "modular-arithmetic-v0":
        validate_modular_arithmetic(expected)


def validate_pack(pack_dir: Path, concept_ids: set[str], field_ids: set[str], curriculum_nodes: set[str]) -> None:
    if not pack_dir.is_dir():
        fail(f"{pack_dir} is not a directory")
    missing = sorted(name for name in REQUIRED_FILES if not (pack_dir / name).exists())
    if missing:
        fail(f"{pack_dir.relative_to(ROOT)} missing files: {', '.join(missing)}")
    load_json(SCHEMA)
    metadata = load_json(pack_dir / "metadata.json")
    expected = load_json(pack_dir / "expected.json")
    expected_ids = validate_metadata(pack_dir, metadata, concept_ids, field_ids, curriculum_nodes)
    validate_expected(metadata, expected, expected_ids)


def pack_dirs_from_args(args: list[str]) -> list[Path]:
    if args:
        return [(ROOT / arg).resolve() if not Path(arg).is_absolute() else Path(arg) for arg in args]
    if not DEFAULT_ROOT.exists():
        fail(f"default pack root is missing: {DEFAULT_ROOT.relative_to(ROOT)}")
    return sorted(path for path in DEFAULT_ROOT.iterdir() if path.is_dir())


def main(argv: list[str]) -> int:
    concept_ids, field_ids, curriculum_nodes = concept_indexes()
    pack_dirs = pack_dirs_from_args(argv)
    if not pack_dirs:
        fail("no example packs found")
    for pack_dir in pack_dirs:
        validate_pack(pack_dir, concept_ids, field_ids, curriculum_nodes)
    print(f"validated {len(pack_dirs)} foundational example pack(s)")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except ValidationError as error:
        print(f"validate-foundational-example-pack: {error}", file=sys.stderr)
        raise SystemExit(1)
