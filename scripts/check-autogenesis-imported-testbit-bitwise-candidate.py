#!/usr/bin/env python3
"""Check the exact imported Nat.testBit_bitwise candidate audit."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "artifacts/autogenesis/imported-testbit-bitwise-candidate-v1.json"


def validate(data: dict[str, Any], verify_external: bool) -> dict[str, int]:
    if data.get("kind") != "axeyum-autogenesis-imported-candidate-audit":
        raise ValueError("wrong artifact kind")
    if data.get("state") != "independently-imported-assumption-bearing-candidate":
        raise ValueError("candidate state is not fail-closed")
    authority = data.get("authority", "")
    for denied in ("no semantic contract", "no transport", "no fact-transition"):
        if denied not in authority:
            raise ValueError(f"authority does not deny {denied}")
    candidate = data.get("candidate", {})
    if candidate.get("name") != "Nat.testBit_bitwise":
        raise ValueError("wrong candidate declaration")
    for field in (
        "type_expression_sha256",
        "alpha_type_expression_sha256",
        "declaration_content_sha256",
        "direct_dependency_sha256",
    ):
        value = candidate.get(field)
        if not isinstance(value, str) or len(value) != 64:
            raise ValueError(f"candidate {field} is malformed")
    canonical_type = candidate.get("canonical_type", "")
    if "AxNat.testBit (AxNat.bitwise f x y)" not in canonical_type:
        raise ValueError("candidate canonical type lost the generic bitwise observation")
    kernel = data.get("kernel_import", {})
    if kernel.get("axiom_free") is not False:
        raise ValueError("candidate must not be represented as axiom-free")
    expected_footprint = ["Quot", "Quot.lift", "Quot.mk", "Quot.sound", "propext"]
    if kernel.get("axiom_footprint") != expected_footprint:
        raise ValueError("reviewed axiom footprint changed")
    if kernel.get("imported_axioms") != ["Quot.sound", "propext"]:
        raise ValueError("reviewed imported axiom set changed")
    dependencies = candidate.get("direct_theorem_dependencies")
    if not isinstance(dependencies, list) or dependencies != sorted(dependencies):
        raise ValueError("direct theorem dependencies are absent or unstable")
    if len(dependencies) != 29:
        raise ValueError("reviewed direct theorem dependency count changed")
    stream = data.get("external_stream", {})
    target = data.get("reconstruction_target", {})
    if target.get("axiom_footprint") != [] or target.get("abstractions") != 2:
        raise ValueError("proof-free reconstruction target boundary changed")
    if target.get("declarations") != 12 or target.get("normalization_rewrites") != 0:
        raise ValueError("proof-free reconstruction target population changed")
    if target.get("logical_status") != "refuted-unconstrained-abstraction":
        raise ValueError("generalized target logical status changed")
    if target.get("execution_eligible") is not False:
        raise ValueError("refuted generalized target became execution eligible")
    validate_countermodel(target.get("countermodel"))
    floor = data.get("statement_trust_floor", {})
    if floor.get("axiom_footprint") != ["propext"]:
        raise ValueError("statement trust floor changed")
    if floor.get("proof_reconstruction_eligible") is not False:
        raise ValueError("structural statement floor gained proof-reconstruction credit")
    if floor.get("required_route") != (
        "reconstruct-clean-definitions-or-accept-weaker-imported-definition-trust"
    ):
        raise ValueError("structural statement route changed")
    receipt_path = ROOT / floor.get("receipt_path", "")
    receipt_raw = receipt_path.read_bytes()
    if hashlib.sha256(receipt_raw).hexdigest() != floor.get("receipt_sha256"):
        raise ValueError("statement trust floor receipt identity changed")
    receipt = json.loads(receipt_raw)
    controls = receipt.get("controls", [])
    if len(controls) != 2 or any(
        row.get("axiom_footprint") != ["propext"]
        or row.get("direct_theorem_dependencies") != []
        for row in controls
    ):
        raise ValueError("statement trust floor receipt does not support the route")
    if verify_external:
        for label, receipt in (("candidate", stream), ("target", target)):
            path = Path(receipt.get("path", ""))
            raw = path.read_bytes()
            if len(raw) != receipt.get("bytes"):
                raise ValueError(f"external {label} stream byte count changed")
            if hashlib.sha256(raw).hexdigest() != receipt.get("sha256"):
                raise ValueError(f"external {label} stream digest changed")
    return {
        "direct_theorem_dependencies": len(dependencies),
        "axiom_footprint": len(expected_footprint),
        "statement_axiom_floor": len(floor["axiom_footprint"]),
    }


def validate_countermodel(model: Any) -> None:
    if not isinstance(model, dict):
        raise TypeError("generalized target countermodel is absent")
    if model.get("f") != "and" or model.get("testBit") != "is_one":
        raise ValueError("generalized target countermodel functions changed")
    if model.get("bitwise") != "constant_zero":
        raise ValueError("generalized target countermodel bitwise changed")
    x, y, i = (model.get(name) for name in ("x", "y", "i"))
    if (x, y, i) != (1, 1, 0):
        raise ValueError("generalized target countermodel inputs changed")
    test_bit = lambda n, _i: n == 1
    bitwise = lambda _f, _x, _y: 0
    operation = lambda left, right: left and right
    premise = operation(False, False)
    lhs = test_bit(bitwise(operation, x, y), i)
    rhs = operation(test_bit(x, i), test_bit(y, i))
    if premise is not False or lhs is not False or rhs is not True or lhs == rhs:
        raise ValueError("generalized target countermodel no longer refutes the goal")
    if (model.get("premise_f_false_false"), model.get("lhs"), model.get("rhs")) != (
        premise,
        lhs,
        rhs,
    ):
        raise ValueError("generalized target countermodel receipt changed")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact", type=Path, default=ARTIFACT)
    parser.add_argument("--verify-external", action="store_true")
    args = parser.parse_args()
    try:
        census = validate(json.loads(args.artifact.read_text()), args.verify_external)
    except (OSError, TypeError, ValueError, json.JSONDecodeError) as error:
        print(f"IMPORTED_TESTBIT_BITWISE_CANDIDATE_ERROR|{error}")
        return 1
    print(
        "IMPORTED_TESTBIT_BITWISE_CANDIDATE_OK|"
        f"direct_theorems={census['direct_theorem_dependencies']}|"
        f"footprint={census['axiom_footprint']}|"
        f"statement_floor={census['statement_axiom_floor']}|axiom_free=false"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
