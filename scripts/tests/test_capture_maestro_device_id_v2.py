from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/capture-maestro-device-id-v2.py"
SPEC = importlib.util.spec_from_file_location("capture_maestro_device_id_v2", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def test_committed_registration_validates_and_reuses_exact_v1_source_identity() -> None:
    registration = json.loads(MODULE.DEFAULT_REGISTRATION.read_text(encoding="utf-8"))
    base = MODULE.validate_registration(registration)
    assert base["upstream"]["commit"] == "650a3f62c386d113b4cbbc11645d945d57620cbb"
    assert registration["final_rustc_tail"] == [
        "-Ccodegen-units=1",
        "-Clink-dead-code",
        "--emit=llvm-ir",
    ]


def test_encoded_flags_preserve_export_and_remap_every_target_dependency() -> None:
    root = Path("/tmp/two-root-a")
    assert MODULE.encoded_flags(root).split("\x1f") == [
        "-Zexport-executable-symbols",
        "--remap-path-prefix=/tmp/two-root-a=/axeyum-external/maestro",
    ]


def test_registration_rejects_flag_order_or_final_tail_remap() -> None:
    registration = json.loads(MODULE.DEFAULT_REGISTRATION.read_text(encoding="utf-8"))
    registration["encoded_rustflags"] = list(reversed(registration["encoded_rustflags"]))
    with pytest.raises(MODULE.CAPTURE.CaptureError):
        MODULE.validate_registration(registration)

    registration = json.loads(MODULE.DEFAULT_REGISTRATION.read_text(encoding="utf-8"))
    registration["final_rustc_tail"].append("--remap-path-prefix=/bad=/bad")
    with pytest.raises(MODULE.CAPTURE.CaptureError):
        MODULE.validate_registration(registration)
