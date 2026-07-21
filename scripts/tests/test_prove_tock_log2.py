import argparse
import importlib.util
import io
import os
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/prove-tock-log2.py"
SPEC = importlib.util.spec_from_file_location("prove_tock_log2", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
PRODUCER = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = PRODUCER
SPEC.loader.exec_module(PRODUCER)


def capture_error(callable_):
    with unittest.TestCase().assertRaises(PRODUCER.CaptureError) as raised:
        callable_()
    return raised.exception.stage, raised.exception.kind


def valid_output() -> str:
    lines = []
    for target, width in (("log_base_two", 32), ("log_base_two_u64", 64)):
        for property_name in ("defined", "zero", "floor_log2", "msb"):
            lines.append(
                f"TOCK_PROOF|target={target}|width={width}|property={property_name}"
                "|outcome=proved|evidence=alethe_bitblast_resolution"
                "|backend=sat-bv|trust=bit-blast:certified,tseitin:certified,"
                "sat-refutation:certified|terms=100|wall_us=10"
            )
        for mutation in ("wrong_index", "inverted_zero", "high_partition"):
            lines.append(
                f"TOCK_CONTROL|target={target}|width={width}|mutation={mutation}"
                "|outcome=disproved|witness=2|reflected=1|native=1|mutated=0"
                "|replay=pass|wall_us=5"
            )
    lines.append(
        "TOCK_SCOREBOARD|functions=2|proved=8|refuted_replayed=6|unknown=0"
        "|disagree=0|query_wall_us=110|runner_wall_us=120"
    )
    return "\n".join(lines) + "\n"


class ProveTockLog2Tests(unittest.TestCase):
    def test_live_registration_and_capture_inputs_validate_prequery(self):
        registration = PRODUCER.read_registration(PRODUCER.DEFAULT_REGISTRATION)
        committed = PRODUCER.validate_capture(registration)
        self.assertEqual(
            committed["capture_identity_sha256"],
            registration["capture"]["identity_sha256"],
        )

    def test_parser_requires_exact_rows_certified_trust_and_replay(self):
        parsed = PRODUCER.parse_runner_output(valid_output())
        self.assertEqual(len(parsed["proofs"]), 8)
        self.assertEqual(len(parsed["controls"]), 6)
        self.assertEqual(parsed["scoreboard"]["disagree"], "0")

        missing = valid_output().replace(
            valid_output().splitlines()[0] + "\n", "", 1
        )
        self.assertEqual(
            capture_error(lambda: PRODUCER.parse_runner_output(missing)),
            ("result", "proof_count"),
        )
        uncertified = valid_output().replace(
            "bit-blast:certified", "bit-blast:trusted", 1
        )
        self.assertEqual(
            capture_error(lambda: PRODUCER.parse_runner_output(uncertified)),
            ("result", "proof_trust"),
        )
        disagreement = valid_output().replace("reflected=1|native=1", "reflected=1|native=2", 1)
        self.assertEqual(
            capture_error(lambda: PRODUCER.parse_runner_output(disagreement)),
            ("result", "control_disagree"),
        )

    def test_identity_excludes_only_observations_and_row_timings(self):
        base = {
            "schema": "result",
            "proofs": [{"property": "defined", "wall_us": "10"}],
            "controls": [{"mutation": "wrong", "witness": "2", "wall_us": "5"}],
            "observations": {"peak_rss_kib": 1},
        }
        identity = PRODUCER.result_identity(base)
        changed_timing = {
            **base,
            "proofs": [{"property": "defined", "wall_us": "999"}],
            "controls": [{"mutation": "wrong", "witness": "2", "wall_us": "888"}],
            "observations": {"peak_rss_kib": 999},
        }
        self.assertEqual(identity, PRODUCER.result_identity(changed_timing))
        changed_witness = {
            **base,
            "controls": [{"mutation": "wrong", "witness": "3", "wall_us": "5"}],
        }
        self.assertNotEqual(identity, PRODUCER.result_identity(changed_witness))

    def test_archive_parent_traversal_is_rejected(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            archive = root / "archive.tar"
            with tarfile.open(archive, "w") as stream:
                info = tarfile.TarInfo("../escape")
                payload = b"escape"
                info.size = len(payload)
                stream.addfile(info, io.BytesIO(payload))
            self.assertEqual(
                capture_error(lambda: PRODUCER.safe_extract(archive, root / "out", [])),
                ("source", "archive_path"),
            )
            safe_archive = root / "safe.tar"
            with tarfile.open(safe_archive, "w") as stream:
                regular = tarfile.TarInfo("regular")
                payload = b"regular"
                regular.size = len(payload)
                stream.addfile(regular, io.BytesIO(payload))
                link = tarfile.TarInfo("corpus/public")
                link.type = tarfile.SYMTYPE
                link.linkname = "/unregistered/absolute/path"
                stream.addfile(link)
            destination = root / "safe-out"
            PRODUCER.safe_extract(safe_archive, destination, ["corpus/public"])
            self.assertEqual((destination / "regular").read_bytes(), b"regular")
            self.assertFalse((destination / "corpus/public").exists())

    def test_runner_failure_removes_partial_output(self):
        target_parent = ROOT / "target/tock-log2-20260721"
        target_parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=target_parent) as raw:
            output = Path(raw) / "proof"
            partial = output.with_name(f".{output.name}.partial-{os.getpid()}")
            args = argparse.Namespace(
                registration=ROOT / "registration.json",
                output=output,
            )
            registration = {
                "tools": {
                    "gnu_time": {"path": "/usr/bin/time"},
                    "cargo": {"path": "/cargo"},
                    "rustc": {"path": "/rustc"},
                },
                "capture": {},
                "canonical": [],
                "solver": {},
            }

            def materialize(_registration, destination):
                destination.mkdir()

            completed = mock.Mock(returncode=1, stdout="", stderr="runner failed")
            with (
                mock.patch.object(PRODUCER, "read_registration", return_value=registration),
                mock.patch.object(PRODUCER, "validate_capture"),
                mock.patch.object(
                    PRODUCER,
                    "validate_pushed_head",
                    return_value={"commit": "c", "tree": "t", "tracking": "c"},
                ),
                mock.patch.object(PRODUCER, "materialize_head", side_effect=materialize),
                mock.patch.object(PRODUCER.SUPPORT, "resource_snapshot", return_value={}),
                mock.patch.object(PRODUCER.SUPPORT, "resource_delta", return_value={}),
                mock.patch.object(PRODUCER.subprocess, "run", return_value=completed),
            ):
                self.assertEqual(
                    capture_error(lambda: PRODUCER.run_scoreboard(args)),
                    ("runner", "cargo_test"),
                )
            self.assertFalse(output.exists())
            self.assertFalse(partial.exists())


if __name__ == "__main__":
    unittest.main()
