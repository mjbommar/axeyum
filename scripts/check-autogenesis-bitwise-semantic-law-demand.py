#!/usr/bin/env python3
"""Check the exact semantic-law demand for Nat.testBit_bitwise."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "artifacts/autogenesis/bitwise-semantic-law-demand-v1.json"
CANDIDATE = ROOT / "artifacts/autogenesis/imported-testbit-bitwise-candidate-v1.json"
GRAPH = ROOT / "artifacts/autogenesis/imported-implementation-demand-v1.json"


def validate(data: dict[str, Any]) -> dict[str, int]:
    if data.get("kind") != "axeyum-autogenesis-semantic-law-demand":
        raise ValueError("wrong artifact kind")
    if data.get("state") != "law-interface-required-before-reconstruction":
        raise ValueError("semantic-law demand state changed")
    authority = data.get("authority", "")
    for denied in ("no proof authority", "no transport", "no fact-transition"):
        if denied not in authority:
            raise ValueError(f"authority does not deny {denied}")

    candidate = json.loads(CANDIDATE.read_text())
    expected = candidate["candidate"]
    subject = data.get("candidate", {})
    if subject.get("name") != expected.get("name"):
        raise ValueError("candidate name drifted")
    if subject.get("alpha_type_expression_sha256") != expected.get(
        "alpha_type_expression_sha256"
    ):
        raise ValueError("candidate type identity drifted")

    graph = json.loads(GRAPH.read_text())
    graph_identities = {
        (node.get("name"), node.get("content_sha256")) for node in graph["nodes"]
    }
    operations = data.get("operations")
    if not isinstance(operations, list) or len(operations) != 2:
        raise ValueError("operation identity population changed")
    for operation in operations:
        if (operation.get("name"), operation.get("content_sha256")) not in graph_identities:
            raise ValueError("operation identity is absent from implementation graph")
        if operation.get("axiom_footprint") != ["propext"]:
            raise ValueError("imported operation footprint changed")
        for field in ("alpha_type_expression_sha256", "alpha_value_expression_sha256"):
            value = operation.get(field)
            if not isinstance(value, str) or len(value) != 64:
                raise ValueError(f"imported operation {field} is malformed")
        dependencies = operation.get("direct_declaration_dependencies")
        if not isinstance(dependencies, list) or dependencies != sorted(dependencies):
            raise ValueError("imported operation dependency identity changed")

    laws = data.get("laws")
    if not isinstance(laws, list) or len(laws) != 6:
        raise ValueError("semantic-law population changed")
    names = [law.get("name") for law in laws]
    if names != [
        "testBit_zero_value",
        "testBit_low",
        "testBit_succ",
        "boolean_numeric_observation_transport",
        "bitwise_equation",
        "double_add_div",
    ]:
        raise ValueError("semantic-law order or identity changed")
    imported_dependencies = set(expected["direct_theorem_dependencies"])
    for law in laws:
        if (
            law.get("availability") == "imported-candidate-dependency-assumption-bearing"
            and law.get("source_declaration") not in imported_dependencies
        ):
            raise ValueError("claimed imported law is absent from direct dependencies")

    index = json.loads(
        (ROOT / "artifacts/autogenesis/kernel-lemma-search-index-v1.json").read_text()
    )
    indexed = {row["kernel_declaration_id"]: row for row in index["lemmas"]}
    analogues = data.get("native_analogues")
    if not isinstance(analogues, list) or len(analogues) != 2:
        raise ValueError("native analogue population changed")
    for analogue in analogues:
        declaration_id = analogue.get("kernel_declaration_id")
        live = indexed.get(declaration_id)
        if live is None or live.get("axiom_footprint_size") != 0:
            raise ValueError("native analogue is absent or assumption-bearing")
        if analogue.get("canonical_type") != live.get("canonical_type"):
            raise ValueError("native analogue type identity drifted")
        if "Eq.{1} AxNat" not in analogue["canonical_type"]:
            raise ValueError("native analogue no longer exposes the numeric result sort")
    transport = laws[3]
    if (
        transport.get("availability")
        != "native-view-constructed-imported-equivalence-missing"
    ):
        raise ValueError("Boolean/numeric observation transport status changed")
    bridge = data.get("native_boolean_bridge", {})
    if bridge.get("axiom_footprint_size") != 0:
        raise ValueError("native Boolean observation bridge gained assumptions")
    if bridge.get("imported_equivalence_status") != "missing":
        raise ValueError("unproved imported observation equivalence gained credit")
    bridge_type = bridge.get("canonical_type", "")
    if "Eq.{1} Bool" not in bridge_type or "testBitBool" not in bridge_type:
        raise ValueError("native Boolean observation bridge type changed")
    if bridge.get("zero_axiom_footprint_size") != 0:
        raise ValueError("zero observation theorem gained assumptions")
    zero_type = bridge.get("zero_canonical_type", "")
    if "testBitBool AxNat.zero" not in zero_type or "Bool.false" not in zero_type:
        raise ValueError("zero observation theorem type changed")
    if bridge.get("input_bound_axiom_footprint_size") != 0:
        raise ValueError("input sufficient-width theorem gained assumptions")
    input_bound_type = bridge.get("input_bound_canonical_type", "")
    if "AxNat.le" not in input_bound_type or "Bool.false" not in input_bound_type:
        raise ValueError("input sufficient-width theorem type changed")
    algebra = data.get("native_observation_algebra", {})
    if algebra.get("axiom_footprint_size") != 0:
        raise ValueError("native observation algebra gained assumptions")
    if (
        algebra.get("nat_reification_status")
        != "target-owned-total-theorem-checked-imported-equivalence-missing"
    ):
        raise ValueError("unproved Nat reification gained credit")
    algebra_type = algebra.get("canonical_type", "")
    if "bitwiseObservation" not in algebra_type or "testBitBool" not in algebra_type:
        raise ValueError("native observation algebra type changed")
    reification = data.get("native_reification", {})
    if reification.get("base_axiom_footprint_size") != 0:
        raise ValueError("bounded reification base gained assumptions")
    if reification.get("step_axiom_footprint_size") != 0:
        raise ValueError("bounded reification step gained assumptions")
    if (
        reification.get("roundtrip_status")
        != "target-owned-unbounded-checked-imported-equivalence-missing"
    ):
        raise ValueError("bounded reification status changed")
    if "reifyBits" not in reification.get("base_canonical_type", ""):
        raise ValueError("bounded reification base type changed")
    step_type = reification.get("step_canonical_type", "")
    if "reifyBits" not in step_type or "boolToBit" not in step_type:
        raise ValueError("bounded reification step type changed")
    if reification.get("boolean_digit_roundtrip_axiom_footprint_size") != 0:
        raise ValueError("Boolean digit roundtrip gained assumptions")
    digit_type = reification.get("boolean_digit_roundtrip_canonical_type", "")
    if "Eq.{1} Bool" not in digit_type or "boolToBit" not in digit_type:
        raise ValueError("Boolean digit roundtrip type changed")
    if reification.get("boolean_digit_bound_axiom_footprint_size") != 0:
        raise ValueError("Boolean digit bound gained assumptions")
    bound_type = reification.get("boolean_digit_bound_canonical_type", "")
    if "AxNat.le" not in bound_type or "boolToBit" not in bound_type:
        raise ValueError("Boolean digit bound type changed")
    if reification.get("direct_boolean_roundtrip_axiom_footprint_size") != 0:
        raise ValueError("direct Boolean digit roundtrip gained assumptions")
    direct_type = reification.get("direct_boolean_roundtrip_canonical_type", "")
    if "Eq.{1} Bool" not in direct_type or "bitToBool" not in direct_type:
        raise ValueError("direct Boolean digit roundtrip type changed")
    for prefix, required in (
        ("boolean_digit_divmod", "AxNat.divMod"),
        ("boolean_digit_div", "AxNat.div"),
        ("boolean_digit_mod", "AxNat.mod"),
    ):
        if reification.get(f"{prefix}_axiom_footprint_size") != 0:
            raise ValueError(f"{prefix} gained assumptions")
        canonical_type = reification.get(f"{prefix}_canonical_type", "")
        if required not in canonical_type or "boolToBit" not in canonical_type:
            raise ValueError(f"{prefix} type changed")
    for prefix in ("one_bit_normalization", "one_bit_roundtrip"):
        if reification.get(f"{prefix}_axiom_footprint_size") != 0:
            raise ValueError(f"{prefix} gained assumptions")
        canonical_type = reification.get(f"{prefix}_canonical_type", "")
        if "reifyBits" not in canonical_type:
            raise ValueError(f"{prefix} type changed")
    if reification.get("reification_bound_axiom_footprint_size") != 0:
        raise ValueError("universal reification bound gained assumptions")
    bound_type = reification.get("reification_bound_canonical_type", "")
    if "AxNat.lt" not in bound_type or "AxNat.pow" not in bound_type:
        raise ValueError("universal reification bound type changed")
    if reification.get("numeric_roundtrip_axiom_footprint_size") != 0:
        raise ValueError("numeric reification roundtrip gained assumptions")
    numeric_type = reification.get("numeric_roundtrip_canonical_type", "")
    if "AxNat.sumRange" not in numeric_type or "AxNat.testBit" not in numeric_type:
        raise ValueError("numeric reification roundtrip type changed")
    for prefix in (
        "low_reification_base",
        "low_reification_step",
        "low_reification_roundtrip",
        "low_reification_outside",
    ):
        if reification.get(f"{prefix}_axiom_footprint_size") != 0:
            raise ValueError(f"{prefix} gained assumptions")
        if "reifyBitsLow" not in reification.get(f"{prefix}_canonical_type", ""):
            raise ValueError(f"{prefix} type changed")
    if reification.get("bounded_bitwise_axiom_footprint_size") != 0:
        raise ValueError("bounded bitwise theorem gained assumptions")
    bounded_bitwise_type = reification.get("bounded_bitwise_canonical_type", "")
    if (
        "bitwiseReifyLow" not in bounded_bitwise_type
        or "testBitBool" not in bounded_bitwise_type
        or "AxNat.lt" not in bounded_bitwise_type
    ):
        raise ValueError("bounded bitwise theorem type changed")
    if reification.get("total_bitwise_axiom_footprint_size") != 0:
        raise ValueError("total bitwise theorem gained assumptions")
    total_bitwise_type = reification.get("total_bitwise_canonical_type", "")
    if (
        "bitwiseTotal" not in total_bitwise_type
        or "testBitBool" not in total_bitwise_type
        or "Bool.false" not in total_bitwise_type
    ):
        raise ValueError("total bitwise theorem type changed")

    exclusion = data.get("countermodel_exclusion", {})
    if exclusion.get("excluded_by_law") != "testBit_succ":
        raise ValueError("countermodel exclusion law changed")
    test_bit = lambda n, _i: n == 1
    n, i = exclusion.get("n"), exclusion.get("i")
    if (n, i) != (2, 0):
        raise ValueError("countermodel exclusion witness changed")
    lhs = test_bit(n, i + 1)
    rhs = test_bit(n // 2, i)
    if lhs == rhs:
        raise ValueError("semantic law no longer excludes the countermodel")
    if (exclusion.get("law_lhs"), exclusion.get("law_rhs")) != (lhs, rhs):
        raise ValueError("countermodel exclusion receipt changed")
    oracle = validate_finite_reification_oracle(data.get("finite_reification_oracle"))
    return {
        "finite_vectors": oracle["vectors"],
        "laws": len(laws),
        "native_analogues": len(analogues),
        "native_boolean_bridges": 1,
        "native_observation_algebras": 1,
        "native_reifications": 1,
        "operations": len(operations),
    }


def validate_finite_reification_oracle(receipt: Any) -> dict[str, int]:
    if not isinstance(receipt, dict):
        raise TypeError("finite reification oracle receipt is absent")
    authority = receipt.get("authority", "")
    if "no proof" not in authority or "no theorem authority" not in authority:
        raise ValueError("finite reification oracle authority widened")
    max_bits = receipt.get("max_bits")
    if max_bits != 12:
        raise ValueError("finite reification oracle bound changed")
    vectors = 0
    inside = 0
    outside = 0
    for width in range(max_bits + 1):
        for mask in range(1 << width):
            vectors += 1
            reified = sum(((mask >> index) & 1) << index for index in range(width))
            for index in range(width):
                inside += 1
                if ((reified >> index) & 1) != ((mask >> index) & 1):
                    raise ValueError("finite reification oracle found an inside mismatch")
            outside += 1
            if ((reified >> width) & 1) != 0:
                raise ValueError("finite reification oracle found an outside mismatch")
    observed = {
        "vectors": vectors,
        "inside_observations": inside,
        "outside_zero_observations": outside,
    }
    if any(receipt.get(key) != value for key, value in observed.items()):
        raise ValueError("finite reification oracle receipt changed")
    return observed


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact", type=Path, default=ARTIFACT)
    args = parser.parse_args()
    try:
        result = validate(json.loads(args.artifact.read_text()))
    except (OSError, TypeError, ValueError, json.JSONDecodeError) as error:
        print(f"BITWISE_SEMANTIC_LAW_DEMAND_ERROR|{error}")
        return 1
    print(
        "BITWISE_SEMANTIC_LAW_DEMAND_OK|"
        f"laws={result['laws']}|operations={result['operations']}|"
        f"native_analogues={result['native_analogues']}|"
        f"native_boolean_bridges={result['native_boolean_bridges']}|"
        f"native_observation_algebras={result['native_observation_algebras']}|"
        f"native_reifications={result['native_reifications']}|"
        f"finite_vectors={result['finite_vectors']}|"
        "countermodel_excluded=true|reconstruction_eligible=false"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
