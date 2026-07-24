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

    def rewrite_record(self, path: Path, value: dict) -> None:
        path.chmod(0o600)
        path.write_bytes(STORE.canonical_bytes(value))
        path.chmod(0o444)

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
        self.assertEqual(set(descriptor), STORE.STORAGE_DESCRIPTOR_FIELDS)
        self.assertEqual(descriptor["statfs_magic"], STORE.statfs_magic(STORE.ROOT))
        self.assertEqual(STORE.validate_storage_descriptor(descriptor), [])
        changed = copy.deepcopy(descriptor)
        changed["fs_type"] = "nfs4"
        self.assertNotEqual(changed.get("identity_sha256"), STORE.object_digest(changed, "identity_sha256"))
        changed = copy.deepcopy(descriptor)
        changed["power_loss_proven"] = True
        changed["identity_sha256"] = STORE.object_digest(changed, "identity_sha256")
        self.assertTrue(STORE.validate_storage_descriptor(changed))
        changed = copy.deepcopy(descriptor)
        changed["mount"]["mount_options"] = 7
        changed["identity_sha256"] = STORE.object_digest(changed, "identity_sha256")
        self.assertTrue(STORE.validate_storage_descriptor(changed))
        retained_elsewhere = copy.deepcopy(descriptor)
        retained_elsewhere["class_root"] = str(
            Path(descriptor["mount"]["mount_point"])
            / "different"
            / "checkout"
            / "axeyum"
        )
        retained_elsewhere["identity_sha256"] = STORE.object_digest(
            retained_elsewhere, "identity_sha256"
        )
        self.assertEqual(STORE.validate_storage_descriptor(retained_elsewhere), [])
        outside_mount = copy.deepcopy(descriptor)
        outside_mount["class_root"] = "/different/checkout/axeyum"
        outside_mount["mount"]["mount_point"] = "/observed/mount"
        outside_mount["identity_sha256"] = STORE.object_digest(
            outside_mount, "identity_sha256"
        )
        self.assertEqual(
            STORE.validate_storage_descriptor(outside_mount),
            ["storage class root is outside its observed mount"],
        )
        with mock.patch.object(STORE, "mount_identity", return_value={**descriptor["mount"], "fs_type": "nfs4"}):
            with self.assertRaisesRegex(STORE.StoreEvidenceError, "network filesystem"):
                STORE.capture_storage_class(STORE.STORAGE_CLASS_IDS[0], STORE.ROOT)

    def test_preflight_exercises_hardlink_no_replace_and_fsync(self) -> None:
        STORE.preflight_storage_class(self.descriptor())
        with mock.patch.object(STORE.os, "link", side_effect=OSError("unsupported")):
            with self.assertRaises(OSError):
                STORE.preflight_storage_class(self.descriptor())

    def test_every_record_family_rejects_exact_field_and_self_hash_drift(self) -> None:
        families = {
            "run/run.json": "identity_sha256",
            "attempts/attempt-001.json": "sha256",
            "cases/case-a.json": "sha256",
            "artifacts/controller-main.json": "record_sha256",
            "completion/completion.json": "sha256",
        }
        for relative, hash_field in families.items():
            for mutation in ("extra-field", "self-hash"):
                with self.subTest(relative=relative, mutation=mutation), tempfile.TemporaryDirectory(
                    dir=STORE.ROOT
                ) as temporary:
                    root = self.materialize(Path(temporary))
                    record_path = root / relative
                    changed = STORE.load_canonical(record_path)
                    if mutation == "extra-field":
                        changed["unexpected"] = True
                        changed[hash_field] = STORE.EVIDENCE_CONTRACT.object_digest(
                            changed, hash_field
                        )
                    else:
                        changed[hash_field] = "0" * 64
                    self.rewrite_record(record_path, changed)
                    with self.assertRaisesRegex(
                        STORE.StoreEvidenceError, "content identity drift"
                    ):
                        STORE.validate_complete_store(root)

    def test_unsafe_paths_and_store_root_symlinks_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory(dir=STORE.ROOT) as temporary:
            parent = Path(temporary)
            root = parent / "store"
            STORE.initialize_store(root, self.descriptor())
            value = STORE.fixture_dependencies()[0][1]
            for relative in ("record.json", "../record.json", "cases/../record.json"):
                with self.subTest(relative=relative), self.assertRaises(
                    STORE.StoreEvidenceError
                ):
                    STORE._install_relative(root, relative, value)
            with self.assertRaises(STORE.StoreEvidenceError):
                STORE._install_relative(root, str(parent / "absolute.json"), value)
            (root / "quarantine").symlink_to(root / "run", target_is_directory=True)
            with self.assertRaisesRegex(STORE.StoreEvidenceError, "quarantine"):
                STORE._install_relative(root, "run/run.json", value)
        with tempfile.TemporaryDirectory(dir=STORE.ROOT) as temporary:
            parent = Path(temporary)
            real = parent / "real"
            real.mkdir()
            alias = parent / "store"
            alias.symlink_to(real, target_is_directory=True)
            with self.assertRaises(STORE.StoreEvidenceError):
                STORE.initialize_store(alias, self.descriptor())

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

    def test_wrong_filename_duplicate_and_reordered_manifest_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory(dir=STORE.ROOT) as temporary:
            root = self.materialize(Path(temporary))
            (root / "cases/case-a.json").rename(root / "cases/case-z.json")
            with self.assertRaises(STORE.StoreEvidenceError):
                STORE.validate_complete_store(root)
        with tempfile.TemporaryDirectory(dir=STORE.ROOT) as temporary:
            root = self.materialize(Path(temporary))
            duplicate = root / "cases/case-z.json"
            duplicate.write_bytes((root / "cases/case-a.json").read_bytes())
            duplicate.chmod(0o444)
            with self.assertRaisesRegex(STORE.StoreEvidenceError, "unexpected store record"):
                STORE.validate_complete_store(root)
        manifest = STORE.build_store_manifest(self.descriptor())
        reordered = copy.deepcopy(manifest)
        reordered["dependency_records"].reverse()
        reordered["record_sha256"] = STORE.domain_digest(
            STORE.STORE_SCHEMA,
            {key: value for key, value in reordered.items() if key != "record_sha256"},
        )
        self.assertTrue(STORE.validate_store_manifest(reordered))
        duplicated = copy.deepcopy(manifest)
        duplicated["dependency_records"].append(
            copy.deepcopy(duplicated["dependency_records"][0])
        )
        duplicated["record_sha256"] = STORE.domain_digest(
            STORE.STORE_SCHEMA,
            {key: value for key, value in duplicated.items() if key != "record_sha256"},
        )
        self.assertTrue(STORE.validate_store_manifest(duplicated))

    def test_completion_before_dependencies_and_different_second_completion_fail(self) -> None:
        with tempfile.TemporaryDirectory(dir=STORE.ROOT) as temporary:
            root = Path(temporary) / "store"
            STORE.initialize_store(root, self.descriptor())
            STORE._install_relative(
                root, STORE.TARGET_PATHS["completion"], STORE.fixture_completion()
            )
            with self.assertRaises(STORE.StoreEvidenceError):
                STORE.install_completion(root)
        with tempfile.TemporaryDirectory(dir=STORE.ROOT) as temporary:
            root = self.materialize(Path(temporary))
            changed = STORE.fixture_completion()
            changed["state"] = "different"
            changed["sha256"] = STORE.EVIDENCE_CONTRACT.object_digest(changed, "sha256")
            with self.assertRaises(STORE.CheckpointConflict):
                STORE._install_relative(root, STORE.TARGET_PATHS["completion"], changed)

    def test_attempt_attribution_and_completion_record_set_drift_fail(self) -> None:
        bundle = STORE.fixture_bundle()
        wrong_attempt = copy.deepcopy(bundle)
        wrong_attempt["cases"][0]["attempt_id"] = "attempt-001"
        wrong_attempt["cases"][0]["sha256"] = STORE.EVIDENCE_CONTRACT.object_digest(
            wrong_attempt["cases"][0], "sha256"
        )
        self.assertTrue(STORE.EVIDENCE_CONTRACT.validate_bundle(wrong_attempt))
        for field in ("terminal_less_attempt_ids", "case_records_sha256", "artifact_records_sha256"):
            changed = copy.deepcopy(bundle)
            changed["completion"][field] = [] if field.endswith("ids") else "0" * 64
            changed["completion"]["sha256"] = STORE.EVIDENCE_CONTRACT.object_digest(
                changed["completion"], "sha256"
            )
            with self.subTest(field=field):
                self.assertTrue(STORE.EVIDENCE_CONTRACT.validate_bundle(changed))

    def test_projection_excludes_paths_pids_and_quarantine_names(self) -> None:
        with tempfile.TemporaryDirectory(dir=STORE.ROOT) as first_parent, tempfile.TemporaryDirectory(
            dir=STORE.ROOT
        ) as second_parent:
            first = self.materialize(Path(first_parent))
            second = self.materialize(Path(second_parent))
            for root, name in ((first, "pid-111"), (second, "pid-999")):
                quarantine = root / "quarantine/orphans"
                quarantine.mkdir(parents=True)
                (quarantine / name).write_text(name)
            self.assertEqual(
                STORE.validate_complete_store(first), STORE.validate_complete_store(second)
            )

    def test_fixture_cannot_claim_real_lean_u2_or_parity_execution(self) -> None:
        bundle = STORE.fixture_bundle()
        self.assertTrue(bundle["synthetic"])
        self.assertEqual(bundle["run"]["system_profile"], "synthetic-contract-control")
        self.assertEqual(
            bundle["run"]["command"], ["synthetic-lean-runner", "--contract-only"]
        )
        self.assertEqual(bundle["credits"], STORE.EVIDENCE_CONTRACT.zero_credits())
        manifest = STORE.build_store_manifest(self.descriptor())
        self.assertEqual(manifest["real_outcomes"], 0)
        self.assertEqual(manifest["parity_credit"], 0)

    def test_preregistered_source_identities_are_frozen(self) -> None:
        historical_primitive = next(
            row
            for row in STORE.HISTORICAL_RESULT_SOURCE_INPUTS
            if row["path"] == "scripts/smtcomp_repro/resume_fs.py"
        )
        self.assertEqual(
            historical_primitive["sha256"],
            "1968e7b6424c2dd9273bff5041e96fc21b83ec01b2205dcc840d5dc942be1aec",
        )
        self.assertEqual(
            STORE.sha256_file(STORE.PRIMITIVE),
            "a60e6d300f193c5f7ee8444573e84a35d145f65a79c444000a0f6e5bf1416a5e",
        )
        self.assertEqual(
            STORE.PRIMITIVE.relative_to(STORE.ROOT).as_posix(),
            "scripts/lean_vendored_resume_fs.py",
        )
        self.assertEqual(
            STORE.WORKER.relative_to(STORE.ROOT).as_posix(),
            "scripts/lean_resume_fs_fixture_worker.py",
        )
        self.assertEqual(
            STORE.PREREGISTRATION_COMMIT,
            "8bad614645137164eafec6ab6cf068e5035695b5",
        )

    def test_process_evidence_requires_exact_non_lean_worker_semantics(self) -> None:
        phase = "after_commit"
        target = "cases/case-a.json"
        with tempfile.TemporaryDirectory(dir=STORE.ROOT) as temporary:
            evidence = Path(temporary) / "evidence"
            evidence.mkdir()
            (evidence / "stdout.bin").write_bytes(b"")
            (evidence / "stderr.bin").write_bytes(b"")
            (evidence / "marker.bin").write_bytes((phase + "\n").encode())
            work = Path(temporary) / "work"
            command = [
                os.path.realpath(STORE.sys.executable),
                str(STORE.WORKER.resolve()),
                "--directory",
                str(work / "store/cases"),
                "--filename",
                "case-a.json",
                "--payload",
                str(work / "payload.json"),
                "--stop-phase",
                phase,
                "--marker",
                str(work / "phase.marker"),
            ]
            environment = {
                "LANG": "C.UTF-8",
                "PYTHONHASHSEED": "0",
                "PYTHONPATH": str(STORE.LEAN_SCRIPTS),
            }
            process = {
                "command": command,
                "command_sha256": STORE.digest(command),
                "environment": environment,
                "environment_sha256": STORE.digest(environment),
                "executable_sha256": STORE.sha256_file(
                    Path(os.path.realpath(STORE.sys.executable))
                ),
                "worker_sha256": STORE.sha256_file(STORE.WORKER),
                "primitive_sha256": STORE.sha256_file(STORE.PRIMITIVE),
                "pid": 123,
                "process_group_id": 123,
                "return_code": -9,
                "signal": 9,
                "marker_sha256": STORE.sha256_file(evidence / "marker.bin"),
                "stdout": {
                    "sha256": STORE.sha256_file(evidence / "stdout.bin"),
                    "bytes": 0,
                },
                "stderr": {
                    "sha256": STORE.sha256_file(evidence / "stderr.bin"),
                    "bytes": 0,
                },
            }
            self.assertEqual(
                STORE.validate_process_evidence(
                    process,
                    target_path=target,
                    phase=phase,
                    evidence_directory=evidence,
                ),
                [],
            )
            self.assertIn(
                "kill cell source identity drift",
                STORE.validate_process_evidence(
                    process,
                    target_path=target,
                    phase=phase,
                    evidence_directory=evidence,
                    expected_worker_sha256=STORE.sha256_file(STORE.WORKER),
                    expected_primitive_sha256="0" * 64,
                ),
            )
            relocated = copy.deepcopy(process)
            relocated_root = Path("/var/tmp/independent-axeyum-worktree")
            relocated["command"][1] = str(
                relocated_root / STORE.WORKER.relative_to(STORE.ROOT)
            )
            relocated["command_sha256"] = STORE.digest(relocated["command"])
            relocated["environment"]["PYTHONPATH"] = str(
                relocated_root / STORE.LEAN_SCRIPTS.relative_to(STORE.ROOT)
            )
            relocated["environment_sha256"] = STORE.digest(relocated["environment"])
            self.assertEqual(
                STORE.validate_process_evidence(
                    relocated,
                    target_path=target,
                    phase=phase,
                    evidence_directory=evidence,
                ),
                [],
            )
            relocated["environment"]["PYTHONPATH"] = str(STORE.LEAN_SCRIPTS)
            relocated["environment_sha256"] = STORE.digest(relocated["environment"])
            self.assertIn(
                "kill cell environment drift",
                STORE.validate_process_evidence(
                    relocated,
                    target_path=target,
                    phase=phase,
                    evidence_directory=evidence,
                ),
            )
            changed = copy.deepcopy(process)
            changed["command"][1] = "/usr/bin/lean"
            changed["command_sha256"] = STORE.digest(changed["command"])
            self.assertTrue(
                STORE.validate_process_evidence(
                    changed,
                    target_path=target,
                    phase=phase,
                    evidence_directory=evidence,
                )
            )
            changed = copy.deepcopy(process)
            changed["unexpected"] = True
            self.assertEqual(
                STORE.validate_process_evidence(
                    changed,
                    target_path=target,
                    phase=phase,
                    evidence_directory=evidence,
                ),
                ["kill cell process evidence fields must be exact"],
            )

    def test_unknown_implementation_revision_fails_closed(self) -> None:
        with self.assertRaisesRegex(STORE.StoreEvidenceError, "not an ancestor"):
            STORE.validate_implementation_revision("0" * 40, [STORE.PRIMITIVE])

    def test_historical_result_source_selection_is_exact(self) -> None:
        authority = json.loads(STORE.RESULT_AUTHORITY.read_bytes())
        self.assertEqual(STORE.validate_result_authority(authority), [])
        self.assertEqual(
            authority["preregistration"]["implementation_revision"],
            STORE.HISTORICAL_IMPLEMENTATION_REVISION,
        )
        self.assertEqual(
            STORE.result_source_inputs(STORE.HISTORICAL_IMPLEMENTATION_REVISION),
            authority["source_inputs"],
        )

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
                evidence_root,
                implementation_revision=STORE.subprocess.run(
                    ["git", "rev-parse", "HEAD"],
                    cwd=STORE.ROOT,
                    check=True,
                    stdout=STORE.subprocess.PIPE,
                    text=True,
                ).stdout.strip(),
            )
            self.assertEqual(authority["summary"]["kill_cells"], 16)
            self.assertEqual(authority["summary"]["sigkill_cells"], 16)
            self.assertEqual(authority["summary"]["projection_equal_cells"], 16)
            self.assertEqual(authority["summary"]["real_outcomes"], 0)
            self.assertEqual(authority["summary"]["parity_credit"], 0)
            self.assertIn("not power-loss", STORE.render_markdown(authority))


if __name__ == "__main__":
    unittest.main()
