"""Real filesystem/process-kill fixtures for ADR-0344 E1."""

from __future__ import annotations

import importlib.util
import json
import os
import stat
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SMTCOMP = ROOT / "scripts" / "smtcomp_repro"
sys.path.insert(0, str(SMTCOMP))

GEN_SPEC = importlib.util.spec_from_file_location(
    "gen_smtcomp_resume_contract_for_fs",
    ROOT / "scripts" / "gen-smtcomp-resume-contract.py",
)
assert GEN_SPEC and GEN_SPEC.loader
GEN = importlib.util.module_from_spec(GEN_SPEC)
sys.modules[GEN_SPEC.name] = GEN
GEN_SPEC.loader.exec_module(GEN)

from resume_contract import ContractError, canonical_bytes, seal_record  # noqa: E402
from resume_fs import (  # noqa: E402
    CheckpointConflict,
    atomic_install_json,
    materialize_bundle,
    recover_orphan_temporaries,
    validate_bundle_directory,
)


WORKER = SMTCOMP / "resume_fs_fixture_worker.py"
PHASES = (
    "before_temp_open",
    "after_temp_fsync",
    "after_final_link",
    "after_commit",
)


def temporary_directory() -> tempfile.TemporaryDirectory[str]:
    parent = os.environ.get("AXEYUM_FS_FIXTURE_PARENT")
    return tempfile.TemporaryDirectory(dir=parent)


def wait_for(path: Path, process: subprocess.Popen[bytes]) -> None:
    deadline = time.monotonic() + 5.0
    while time.monotonic() < deadline:
        if path.exists():
            return
        if process.poll() is not None:
            raise AssertionError(f"fixture worker exited early: {process.returncode}")
        time.sleep(0.01)
    raise AssertionError(f"fixture worker did not reach marker: {path}")


class ResumeFilesystemTests(unittest.TestCase):
    def test_same_record_is_idempotent_but_conflict_is_preserved(self) -> None:
        bundle = GEN.make_bundle()
        record = bundle.records[0]
        with temporary_directory() as tmp:
            directory = Path(tmp) / "records"
            filename = f"{record['result_key']}.json"
            self.assertEqual(atomic_install_json(directory, filename, record), "installed")
            self.assertEqual(
                stat.S_IMODE((directory / filename).stat().st_mode), 0o444
            )
            self.assertEqual(
                atomic_install_json(directory, filename, record), "existing-valid"
            )
            changed = dict(record)
            changed["wall_time_ns"] += 1
            changed = seal_record(changed)
            with self.assertRaises(CheckpointConflict):
                atomic_install_json(directory, filename, changed)
            self.assertEqual(json.loads((directory / filename).read_bytes()), record)
            conflicts = list((Path(tmp) / "quarantine" / "conflicts").iterdir())
            self.assertEqual(len(conflicts), 1)
            self.assertEqual(json.loads(conflicts[0].read_bytes()), changed)

    def test_orphan_temporary_is_quarantined_not_promoted(self) -> None:
        with temporary_directory() as tmp:
            directory = Path(tmp) / "records"
            directory.mkdir()
            orphan = directory / ".result.json.tmp-1-dead"
            orphan.write_bytes(b'{"truncated":')
            recovered = recover_orphan_temporaries(directory)
            self.assertEqual(len(recovered), 1)
            self.assertFalse(orphan.exists())
            self.assertEqual(recovered[0].read_bytes(), b'{"truncated":')
            self.assertFalse((directory / "result.json").exists())

    def test_orphan_recovery_is_scoped_to_owned_result_targets(self) -> None:
        with temporary_directory() as tmp:
            directory = Path(tmp) / "records"
            directory.mkdir()
            owned = directory / ".owned.json.tmp-1-dead"
            foreign = directory / ".foreign.json.tmp-2-live"
            malformed = directory / ".tmp-unowned"
            owned.write_bytes(b"owned")
            foreign.write_bytes(b"foreign")
            malformed.write_bytes(b"malformed")

            recovered = recover_orphan_temporaries(
                directory, eligible_targets={"owned.json"}
            )

            self.assertEqual(len(recovered), 1)
            self.assertEqual(recovered[0].read_bytes(), b"owned")
            self.assertFalse(owned.exists())
            self.assertEqual(foreign.read_bytes(), b"foreign")
            self.assertEqual(malformed.read_bytes(), b"malformed")

    def test_forced_kills_resume_to_uninterrupted_canonical_output(self) -> None:
        baseline_bundle = GEN.make_bundle(interrupted=True)
        with temporary_directory() as tmp:
            base = Path(tmp)
            baseline_root = base / "baseline"
            materialize_bundle(baseline_root, baseline_bundle)
            baseline = validate_bundle_directory(baseline_root)

            for phase in PHASES:
                with self.subTest(phase=phase):
                    bundle = GEN.make_bundle(interrupted=True)
                    run_root = base / phase
                    records_dir = run_root / "records"
                    record = bundle.records[0]
                    payload = run_root / "payload.json"
                    payload.parent.mkdir(parents=True)
                    payload.write_bytes(canonical_bytes(record))
                    marker = run_root / "worker.marker"
                    process = subprocess.Popen(
                        [
                            sys.executable,
                            str(WORKER),
                            "--directory",
                            str(records_dir),
                            "--filename",
                            f"{record['result_key']}.json",
                            "--payload",
                            str(payload),
                            "--stop-phase",
                            phase,
                            "--marker",
                            str(marker),
                        ],
                        cwd=ROOT,
                        stdout=subprocess.DEVNULL,
                        stderr=subprocess.DEVNULL,
                    )
                    try:
                        wait_for(marker, process)
                        process.kill()
                        process.wait(timeout=5)
                    finally:
                        if process.poll() is None:
                            process.kill()
                            process.wait(timeout=5)

                    recover_orphan_temporaries(records_dir)
                    for row in bundle.records:
                        atomic_install_json(
                            records_dir, f"{row['result_key']}.json", row
                        )
                    materialize_bundle(run_root, bundle, include_records=False)
                    payload.unlink()
                    marker.unlink()
                    self.assertEqual(validate_bundle_directory(run_root), baseline)

    def test_filename_key_drift_is_rejected(self) -> None:
        bundle = GEN.make_bundle()
        with temporary_directory() as tmp:
            root = Path(tmp)
            materialize_bundle(root, bundle)
            record_file = next((root / "records").iterdir())
            wrong = record_file.with_name("0" * 64 + ".json")
            record_file.rename(wrong)
            with self.assertRaisesRegex(ContractError, "filename/key mismatch"):
                validate_bundle_directory(root)


if __name__ == "__main__":
    unittest.main()
