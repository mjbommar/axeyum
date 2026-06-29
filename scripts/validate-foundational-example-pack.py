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
from fractions import Fraction
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


def require_fraction(context: str, value: Any) -> Fraction:
    if not isinstance(value, str) or not value:
        fail(f"{context} must be a non-empty fraction string")
    try:
        return Fraction(value)
    except ValueError as error:
        fail(f"{context} is not a valid exact fraction: {error}")


def require_fraction_vector(context: str, value: Any) -> list[Fraction]:
    if not isinstance(value, list) or not value:
        fail(f"{context} must be a non-empty vector")
    return [require_fraction(f"{context}[{index}]", item) for index, item in enumerate(value)]


def require_fraction_matrix(context: str, value: Any) -> list[list[Fraction]]:
    if not isinstance(value, list) or not value:
        fail(f"{context} must be a non-empty matrix")
    matrix = [
        require_fraction_vector(f"{context}[{row_index}]", row)
        for row_index, row in enumerate(value)
    ]
    width = len(matrix[0])
    for row_index, row in enumerate(matrix):
        if len(row) != width:
            fail(f"{context}[{row_index}] must have width {width}")
    return matrix


def require_mat_vec_shape(context: str, matrix: list[list[Fraction]], vector: list[Fraction]) -> None:
    if len(matrix[0]) != len(vector):
        fail(f"{context} matrix width must match vector length")


def require_mat_mul_shape(
    context: str,
    left: list[list[Fraction]],
    right: list[list[Fraction]],
) -> None:
    if len(left[0]) != len(right):
        fail(f"{context} left width must match right height")


def mat_vec(matrix: list[list[Fraction]], vector: list[Fraction]) -> list[Fraction]:
    return [
        sum((coefficient * vector[index] for index, coefficient in enumerate(row)), Fraction(0))
        for row in matrix
    ]


def mat_mul(left: list[list[Fraction]], right: list[list[Fraction]]) -> list[list[Fraction]]:
    columns = list(zip(*right))
    return [
        [sum((a * b for a, b in zip(row, column)), Fraction(0)) for column in columns]
        for row in left
    ]


def require_square_matrix(context: str, matrix: list[list[Fraction]]) -> None:
    if len(matrix) != len(matrix[0]):
        fail(f"{context} must be square")


def validate_lu_shape(l_matrix: list[list[Fraction]], u_matrix: list[list[Fraction]]) -> None:
    require_square_matrix("L matrix", l_matrix)
    require_square_matrix("U matrix", u_matrix)
    if len(l_matrix) != len(u_matrix):
        fail("L and U matrices must have the same dimension")
    dimension = len(l_matrix)
    for row_index in range(dimension):
        if l_matrix[row_index][row_index] != 1:
            fail("L matrix must have unit diagonal")
        for col_index in range(row_index + 1, dimension):
            if l_matrix[row_index][col_index] != 0:
                fail("L matrix must be lower triangular")
        for col_index in range(row_index):
            if u_matrix[row_index][col_index] != 0:
                fail("U matrix must be upper triangular")


def validate_rationals_lra(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    density = checks["density-between-witness"]
    if density["expected_result"] != "sat":
        fail("density-between-witness must expect sat")
    values = single_witness_values(density, witnesses)
    a = require_fraction("density a", values.get("a"))
    b = require_fraction("density b", values.get("b"))
    midpoint = require_fraction("density midpoint", values.get("midpoint"))
    if not a < midpoint < b:
        fail("density witness must satisfy a < midpoint < b")
    if midpoint != (a + b) / 2:
        fail("density midpoint must be exactly (a + b) / 2")

    inverse = checks["additive-inverse-witness"]
    if inverse["expected_result"] != "sat":
        fail("additive-inverse-witness must expect sat")
    values = single_witness_values(inverse, witnesses)
    x = require_fraction("inverse x", values.get("x"))
    neg_x = require_fraction("inverse inverse", values.get("inverse"))
    total = require_fraction("inverse sum", values.get("sum"))
    if x + neg_x != total or total != 0:
        fail("additive inverse witness must sum to exactly zero")

    trichotomy = checks["trichotomy-fixed-unsat"]
    if trichotomy["expected_result"] != "unsat":
        fail("trichotomy-fixed-unsat must expect unsat")
    data = trichotomy.get("data", {})
    left = require_fraction("trichotomy left", data.get("left"))
    right = require_fraction("trichotomy right", data.get("right"))
    relations = [left < right, left == right, left > right]
    if sum(1 for relation in relations if relation) != 1:
        fail("trichotomy fixed pair must satisfy exactly one relation")

    transitivity = checks["order-transitivity-fixed-unsat"]
    if transitivity["expected_result"] != "unsat":
        fail("order-transitivity-fixed-unsat must expect unsat")
    data = transitivity.get("data", {})
    lower = require_fraction("transitivity a", data.get("a"))
    middle = require_fraction("transitivity b", data.get("b"))
    upper = require_fraction("transitivity c", data.get("c"))
    if not (lower < middle and middle < upper):
        fail("transitivity fixed data must satisfy a < b < c")
    if not lower < upper:
        fail("transitivity fixed data unexpectedly violates a < c")


def validate_linear_algebra_rational(expected: dict[str, Any]) -> None:
    witnesses = witness_by_id(expected)
    checks = {check["id"]: check for check in expected["checks"]}

    solution = checks["matrix-vector-solution"]
    if solution["expected_result"] != "sat":
        fail("matrix-vector-solution must expect sat")
    values = single_witness_values(solution, witnesses)
    matrix = require_fraction_matrix("matrix-vector matrix", values.get("matrix"))
    vector = require_fraction_vector("matrix-vector solution", values.get("solution"))
    rhs = require_fraction_vector("matrix-vector rhs", values.get("rhs"))
    require_mat_vec_shape("matrix-vector solution", matrix, vector)
    if len(matrix) != len(rhs):
        fail("matrix-vector matrix height must match rhs length")
    if mat_vec(matrix, vector) != rhs:
        fail("matrix-vector witness does not satisfy Ax = b")

    lu = checks["lu-factorization-witness"]
    if lu["expected_result"] != "sat":
        fail("lu-factorization-witness must expect sat")
    values = single_witness_values(lu, witnesses)
    matrix = require_fraction_matrix("LU matrix", values.get("matrix"))
    l_matrix = require_fraction_matrix("L matrix", values.get("l"))
    u_matrix = require_fraction_matrix("U matrix", values.get("u"))
    require_square_matrix("LU target matrix", matrix)
    validate_lu_shape(l_matrix, u_matrix)
    require_mat_mul_shape("LU factorization", l_matrix, u_matrix)
    if mat_mul(l_matrix, u_matrix) != matrix:
        fail("LU witness does not satisfy L*U = A")

    inconsistent = checks["singular-system-inconsistent"]
    if inconsistent["expected_result"] != "unsat":
        fail("singular-system-inconsistent must expect unsat")
    data = inconsistent.get("data", {})
    row = require_fraction_vector("inconsistent row", data.get("row"))
    rhs = require_fraction("inconsistent rhs", data.get("rhs"))
    multiple = require_fraction("inconsistent multiple", data.get("multiple"))
    scaled_row = require_fraction_vector("inconsistent scaled row", data.get("scaled_row"))
    scaled_rhs = require_fraction("inconsistent scaled rhs", data.get("scaled_rhs"))
    if len(row) != len(scaled_row):
        fail("inconsistent row and scaled row must have the same width")
    if scaled_row != [multiple * item for item in row]:
        fail("inconsistent scaled row must equal multiple times the original row")
    if scaled_rhs == multiple * rhs:
        fail("inconsistent scaled rhs must contradict the scaled original rhs")


def validate_pack_semantics(metadata: dict[str, Any], expected: dict[str, Any]) -> None:
    if metadata["id"] == "modular-arithmetic-v0":
        validate_modular_arithmetic(expected)
    if metadata["id"] == "rationals-lra-v0":
        validate_rationals_lra(expected)
    if metadata["id"] == "linear-algebra-rational-v0":
        validate_linear_algebra_rational(expected)


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
