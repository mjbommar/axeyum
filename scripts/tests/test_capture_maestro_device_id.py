from __future__ import annotations

import copy
import importlib.util
import json
import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/capture-maestro-device-id.py"
SPEC = importlib.util.spec_from_file_location("capture_maestro_device_id", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def registration() -> dict[str, object]:
    return json.loads(MODULE.DEFAULT_REGISTRATION.read_text(encoding="utf-8"))


def test_committed_registration_and_producers_validate() -> None:
    value = registration()
    MODULE.validate_registration(value)
    MODULE.validate_producers(value)


def test_registration_rejects_target_order_and_hash_drift() -> None:
    value = registration()
    value["targets"] = list(reversed(value["targets"]))
    with pytest.raises(MODULE.CaptureError, match="target order drift"):
        MODULE.validate_registration(value)

    value = registration()
    value["critical_files"][0]["sha256"] = "0" * 63
    with pytest.raises(MODULE.CaptureError, match="bad SHA-256"):
        MODULE.validate_registration(value)


def test_moduleid_normalization_is_exact_and_narrow() -> None:
    first = b"; ModuleID = '/tmp/a.ll'\nsource_filename = \"kernel\"\ndefine i1 @f() { ret i1 0 }\n"
    second = first.replace(b"/tmp/a.ll", b"/other/b.ll")
    assert MODULE.moduleid_agnostic(first) == MODULE.moduleid_agnostic(second)

    with pytest.raises(MODULE.CaptureError):
        MODULE.moduleid_agnostic(first.replace(b"; ModuleID", b"; module"))
    with pytest.raises(MODULE.CaptureError):
        MODULE.moduleid_agnostic(first + b"; ModuleID = 'second'\n")


def test_admission_output_is_closed_and_identity_projection_drops_only_observations() -> None:
    output = "\n".join(
        [
            "stage=accepted",
            "kind=straight_line_scalar",
            "function=f",
            "parameter_widths=64",
            "return_width=32",
            "blocks=1",
            "phis=0",
            "instructions=3",
            "canonical_bytes=72",
        ]
    )
    parsed = MODULE.parse_admission(output)
    assert parsed["function"] == "f"
    with pytest.raises(MODULE.CaptureError):
        MODULE.parse_admission(output + "\nunexpected=value")

    result = {
        "identity_sha256": "0" * 64,
        "observations": {"wall_ms": 10},
        "stable": {"sha256": "1" * 64},
    }
    projected = MODULE.identity_projection(copy.deepcopy(result))
    assert projected == {"stable": {"sha256": "1" * 64}}
