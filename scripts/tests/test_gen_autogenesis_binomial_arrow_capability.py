"""Failure controls for the binomial arrow capability and measurement."""

from __future__ import annotations

import copy
import importlib.util
import json
import os
import shutil
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(module)
    return module


CAP = load(
    "binomial_arrow_capability",
    ROOT / "scripts/gen-autogenesis-binomial-arrow-capability.py",
)
MEASURE = load(
    "binomial_arrow_measurement",
    ROOT / "scripts/check-autogenesis-binomial-arrow-measurement.py",
)


class CapabilityTests(unittest.TestCase):
    def test_external_pack_is_proof_isolated(self) -> None:
        self.assertEqual(CAP.build()["census"]["proof_isolated_imports"], 3)

    def test_changed_target_stream_is_refused(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            pack = Path(td) / "pack"
            shutil.copytree(CAP.PACK, pack)
            stream = next((pack / "target-only").glob("*.ndjson"))
            os.chmod(stream, 0o644)
            stream.write_bytes(stream.read_bytes() + b"\n")
            with self.assertRaisesRegex(ValueError, "stream changed"):
                CAP.build(pack)

    def test_changed_measurement_stream_is_refused(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            pack = Path(td) / "pack"
            shutil.copytree(CAP.PACK, pack)
            stream = next((pack / "streams").glob("*.ndjson"))
            os.chmod(stream, 0o644)
            stream.write_bytes(stream.read_bytes() + b"\n")
            with self.assertRaisesRegex(ValueError, "measurement stream changed"):
                CAP.build(pack)


class MeasurementTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = json.loads(MEASURE.RESULT.read_text())
        cls.capability = json.loads(MEASURE.CAPABILITY.read_text())

    def test_committed_measurement_passes(self) -> None:
        MEASURE.check(self.result, self.capability)

    def test_invented_acceptance_is_refused(self) -> None:
        changed = copy.deepcopy(self.result)
        changed["outcomes"][0]["result"] = "accepted"
        with self.assertRaisesRegex(ValueError, "honest decline"):
            MEASURE.check(changed, self.capability)

    def test_changed_decline_reason_is_refused(self) -> None:
        changed = copy.deepcopy(self.result)
        changed["outcomes"][0]["reason_kind"] = "NoTypedApplication"
        with self.assertRaisesRegex(ValueError, "decline reason changed"):
            MEASURE.check(changed, self.capability)

    def test_changed_capsule_identity_is_refused(self) -> None:
        changed = copy.deepcopy(self.result)
        changed["outcomes"][0]["capsule_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "capsule changed"):
            MEASURE.check(changed, self.capability)


if __name__ == "__main__":
    unittest.main()
