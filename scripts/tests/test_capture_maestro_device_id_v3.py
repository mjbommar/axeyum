from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/capture-maestro-device-id-v3.py"
SPEC = importlib.util.spec_from_file_location("capture_maestro_device_id_v3", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def registration() -> dict[str, object]:
    return json.loads(MODULE.DEFAULT_REGISTRATION.read_text(encoding="utf-8"))


def test_committed_registration_and_registered_bwrap_probe_validate() -> None:
    value = registration()
    base = MODULE.validate_registration(value)
    report = MODULE.probe_bwrap(value)
    assert base["upstream"]["commit"] == "650a3f62c386d113b4cbbc11645d945d57620cbb"
    assert report["sha256"] == value["bwrap"]["sha256"]
    assert report["version"] == "bubblewrap 0.11.1"


@pytest.mark.parametrize(
    ("field", "replacement"),
    [
        ("sha256", "0" * 64),
        ("version", "bubblewrap 0.11.0"),
        ("path", "/bin/false"),
        ("base_argv", list(reversed(MODULE.EXPECTED_BWRAP_BASE))),
    ],
)
def test_registration_rejects_bwrap_identity_or_argv_drift(
    field: str, replacement: object
) -> None:
    value = registration()
    value["bwrap"][field] = replacement
    with pytest.raises(MODULE.CAPTURE.CaptureError):
        MODULE.validate_registration(value)


def test_registration_rejects_mount_environment_and_tail_drift() -> None:
    value = registration()
    value["namespace"]["virtual_target"] = "/wrong/target"
    with pytest.raises(MODULE.CAPTURE.CaptureError):
        MODULE.validate_registration(value)

    value = registration()
    value["namespace"]["environment"] = list(
        reversed(value["namespace"]["environment"])
    )
    with pytest.raises(MODULE.CAPTURE.CaptureError):
        MODULE.validate_registration(value)

    value = registration()
    value["final_rustc_tail"].append("--remap-path-prefix=/bad=/bad")
    with pytest.raises(MODULE.CAPTURE.CaptureError):
        MODULE.validate_registration(value)


def test_namespace_commands_differ_only_at_two_host_bind_sources(tmp_path: Path) -> None:
    value = registration()
    base = MODULE.validate_registration(value)
    paths = [tmp_path / name for name in ("source-a", "target-a", "source-b", "target-b")]
    for path in paths:
        path.mkdir()
    first = MODULE.namespace_argv(paths[0], paths[1], value, base)
    second = MODULE.namespace_argv(paths[2], paths[3], value, base)
    normalized_first = [
        "<source>" if item == str(paths[0]) else "<target>" if item == str(paths[1]) else item
        for item in first
    ]
    normalized_second = [
        "<source>" if item == str(paths[2]) else "<target>" if item == str(paths[3]) else item
        for item in second
    ]
    assert normalized_first == normalized_second
    assert first.index(str(paths[0])) < first.index(str(paths[1]))
    assert "--remap-path-prefix" not in " ".join(first)
    assert "CARGO_ENCODED_RUSTFLAGS" not in first


def test_physical_roots_and_ambient_flags_fail_closed(tmp_path: Path) -> None:
    paths = [tmp_path / name for name in ("a", "b", "c", "d")]
    MODULE.validate_distinct_physical_roots(paths)
    with pytest.raises(MODULE.CAPTURE.CaptureError):
        MODULE.validate_distinct_physical_roots([paths[0], paths[0], paths[2], paths[3]])
    for name in MODULE.AMBIENT_RUSTFLAGS:
        with pytest.raises(MODULE.CAPTURE.CaptureError):
            MODULE.reject_ambient_rustflags({name: "-Ctarget-cpu=native"})


def test_path_and_full_module_gates_reject_drift(tmp_path: Path) -> None:
    value = registration()
    source = tmp_path / "source-a"
    target = tmp_path / "target-a"
    clean = b"/axeyum-vroot/source /axeyum-vroot/target\n"
    observed = MODULE.path_observation(clean, [tmp_path, source, target], value)
    assert observed["virtual_source_occurrences"] == 1
    assert observed["virtual_target_occurrences"] == 1
    with pytest.raises(MODULE.CAPTURE.CaptureError):
        MODULE.path_observation(clean + str(source).encode(), [source], value)

    common = {
        "module_bytes": 10,
        "module_sha256": "1" * 64,
        "virtual_source_occurrences": 7,
        "virtual_target_occurrences": 0,
    }
    MODULE.require_module_identity([dict(common), dict(common)])
    changed = dict(common)
    changed["module_sha256"] = "2" * 64
    with pytest.raises(MODULE.CAPTURE.CaptureError):
        MODULE.require_module_identity([dict(common), changed])
    changed = dict(common)
    changed["virtual_source_occurrences"] = 8
    with pytest.raises(MODULE.CAPTURE.CaptureError):
        MODULE.require_module_identity([dict(common), changed])
