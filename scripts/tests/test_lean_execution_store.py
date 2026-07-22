from __future__ import annotations

import copy
import json
import os
import stat
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import lean_execution_store as STORE


class LeanExecutionStoreContractTests(unittest.TestCase):
    def descriptor(self) -> dict:
        return STORE.capture_storage_class(STORE.STORAGE_CLASS_IDS[0], STORE.ROOT)

    def materialize(self, parent: Path) -> Path:
        root = parent / "store"
        STORE.initialize_store(root, self.descriptor())
        STORE.install_dependencies(root)
        STORE.install_completion(root)
        return root

    def test_fixture_is_exact_interrupted_resumed_and_zero_credit(self) -> None:
        bundle = STORE.fixture_bundle()
        self.assertEqual(bundle["control_id"], "interrupted-resumed")
        self.assertEqual(len(bundle["attempts"]), 2)
        self.assertIsNone(bundle["attempts"][0]["terminal"])
        self.assertEqual(bundle["completion"]["terminal_less_attempt_ids"], ["attempt-001"])
        self.assertTrue(all(value == 0 for value in bundle["credits"].values()))

    def test_store_manifest_is_exact_self_hashed_and_zero_credit(self) -> None:
        manifest = STORE.build_store_manifest(self.descriptor())
        self.assertEqual(STORE.validate_store_manifest(manifest), [])
        self.assertEqual(manifest["real_outcomes"], 0)
        self.assertEqual(manifest["parity_credit"], 0)
        changed = copy.deepcopy(manifest)
        changed["completion_installed_last"] = False
        self.assertTrue(STORE.validate_store_manifest(changed))

    def test_storage_descriptor_rejects_identity_and_network_drift(self) -> None:
        descriptor = self.descriptor()
        changed = copy.deepcopy(descriptor)
        changed["fs_type"] = "nfs4"
        self.assertNotEqual(changed.get("identity_sha256"), STORE.object_digest(changed, "identity_sha256"))
        with mock.patch.object(STORE, "mount_identity", return_value={**descriptor["mount"], "fs_type": "nfs4"}):
            with self.assertRaisesRegex(STORE.StoreEvidenceError, "network filesystem"):
                STORE.capture_storage_class(STORE.STORAGE_CLASS_IDS[0], STORE.ROOT)

    def test_preflight_exercises_hardlink_no_replace_and_fsync(self) -> None:
        STORE.preflight_storage_class(self.descriptor())

    def test_complete_store_is_read_only_and_canonical(self) -> None:
        with tempfile.TemporaryDirectory(dir=STORE.ROOT) as temporary:
            root = self.materialize(Path(temporary))
            first = STORE.validate_complete_store(root)
            second = STORE.validate_complete_store(root)
            self.assertEqual(first, second)
            for relative in STORE._accepted_record_paths(
                STORE.load_canonical(root / "store.json"), include_completion=True
            ):
                self.assertEqual(stat.S_IMODE((root / relative).stat().st_mode), 0o444)

    def test_identical_reinstall_is_idempotent(self) -> None:
        with tempfile.TemporaryDirectory(dir=STORE.ROOT) as temporary:
            root = Path(temporary) / "store"
            STORE.initialize_store(root, self.descriptor())
            path, value = STORE.fixture_dependencies()[0]
            self.assertEqual(STORE._install_relative(root, path, value), "installed")
            self.assertEqual(STORE._install_relative(root, path, value), "existing-valid")

    def test_conflict_preserves_original_and_quarantines_incoming(self) -> None:
        with tempfile.TemporaryDirectory(dir=STORE.ROOT) as temporary:
            root = Path(temporary) / "store"
            STORE.initialize_store(root, self.descriptor())
            path = "cases/case-a.json"
            value = dict(STORE.fixture_dependencies())[path]
            STORE._install_relative(root, path, value)
            changed = copy.deepcopy(value)
            changed["outcome"] = "failed"
            changed["sha256"] = STORE.EVIDENCE_CONTRACT.object_digest(changed, "sha256")
            with self.assertRaises(STORE.CheckpointConflict):
                STORE._install_relative(root, path, changed)
            self.assertEqual(STORE.load_canonical(root / path), value)
            conflicts = list((root / "quarantine" / "conflicts").iterdir())
            self.assertEqual(len(conflicts), 1)
            self.assertEqual(STORE.load_canonical(conflicts[0]), changed)

    def test_truncated_orphan_is_quarantined_not_promoted(self) -> None:
        with tempfile.TemporaryDirectory(dir=STORE.ROOT) as temporary:
            root = Path(temporary) / "store"
            STORE.initialize_store(root, self.descriptor())
            directory = root / "cases"
            directory.mkdir()
            orphan = directory / ".case-a.json.tmp-1-dead"
            orphan.write_bytes(b'{"truncated":')
            recovered = STORE.recover_store_orphans(root)
            self.assertEqual(len(recovered), 1)
            self.assertFalse(orphan.exists())
            self.assertFalse((directory / "case-a.json").exists())
            self.assertEqual(recovered[0].read_bytes(), b'{"truncated":')

    def test_missing_dependency_blocks_completion(self) -> None:
        with tempfile.TemporaryDirectory(dir=STORE.ROOT) as temporary:
            root = Path(temporary) / "store"
            STORE.initialize_store(root, self.descriptor())
            STORE.install_dependencies(root, omit="cases/case-a.json")
            with self.assertRaisesRegex(STORE.StoreEvidenceError, "missing store record"):
                STORE.install_completion(root)

    def test_lost_attempt_and_digest_mutations_block_completion(self) -> None:
        for relative in ("attempts/attempt-001.json", "cases/case-a.json"):
            with self.subTest(relative=relative), tempfile.TemporaryDirectory(dir=STORE.ROOT) as temporary:
                root = Path(temporary) / "store"
                STORE.initialize_store(root, self.descriptor())
                STORE.install_dependencies(root, omit=relative)
                with self.assertRaises(STORE.StoreEvidenceError):
                    STORE.install_completion(root)

    def test_namespace_symlink_extra_and_writable_record_reject(self) -> None:
        with tempfile.TemporaryDirectory(dir=STORE.ROOT) as temporary:
            root = self.materialize(Path(temporary))
            (root / "unexpected").write_text("x")
            with self.assertRaisesRegex(STORE.StoreEvidenceError, "unexpected store entry"):
                STORE.validate_complete_store(root)
        with tempfile.TemporaryDirectory(dir=STORE.ROOT) as temporary:
            root = self.materialize(Path(temporary))
            case = root / "cases/case-a.json"
            case.chmod(0o644)
            with self.assertRaisesRegex(STORE.StoreEvidenceError, "not read-only"):
                STORE.validate_complete_store(root)
        with tempfile.TemporaryDirectory(dir=STORE.ROOT) as temporary:
            root = Path(temporary) / "store"
            STORE.initialize_store(root, self.descriptor())
            (root / "cases").symlink_to(root / "run", target_is_directory=True)
            with self.assertRaises(STORE.StoreEvidenceError):
                STORE.install_dependencies(root)

    def test_result_builder_rejects_partial_population(self) -> None:
        with tempfile.TemporaryDirectory(dir=STORE.ROOT) as temporary:
            root = Path(temporary)
            root.joinpath("storage-classes.json").write_bytes(b"{}\n")
            with self.assertRaises(STORE.StoreEvidenceError):
                STORE.build_result_authority(root, implementation_revision="0" * 40)


@unittest.skipUnless(
    os.name == "posix" and Path("/proc/self/mountinfo").is_file() and Path("/dev/shm").is_dir(),
    "Linux mountinfo and /dev/shm required",
)
class LeanExecutionStoreLiveTests(unittest.TestCase):
    def test_full_sixteen_cell_matrix_and_result_authority(self) -> None:
        with tempfile.TemporaryDirectory(dir=STORE.ROOT) as temporary:
            evidence_root = Path(temporary) / "evidence"
            STORE.run_matrix(output_root=evidence_root)
            storage, cells = STORE.validate_evidence_root(evidence_root)
            self.assertEqual(len(storage["storage_classes"]), 2)
            self.assertEqual(len(cells), 16)
            self.assertTrue(all(cell["process"]["signal"] == 9 for cell in cells))
            self.assertTrue(
                all(
                    cell["canonical_projection_sha256"]
                    == cell["baseline_projection_sha256"]
                    for cell in cells
                )
            )
            authority = STORE.build_result_authority(
                evidence_root, implementation_revision="0" * 40
            )
            self.assertEqual(authority["summary"]["kill_cells"], 16)
            self.assertEqual(authority["summary"]["sigkill_cells"], 16)
            self.assertEqual(authority["summary"]["projection_equal_cells"], 16)
            self.assertEqual(authority["summary"]["real_outcomes"], 0)
            self.assertEqual(authority["summary"]["parity_credit"], 0)
            self.assertIn("not power-loss", STORE.render_markdown(authority))


if __name__ == "__main__":
    unittest.main()
