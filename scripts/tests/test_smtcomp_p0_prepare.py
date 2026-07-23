"""Preparation-only P0 composition and fail-closed mutation gates."""

from __future__ import annotations

import hashlib
import json
import os
import platform
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
SMTCOMP = ROOT / "scripts" / "smtcomp_repro"
sys.path.insert(0, str(SMTCOMP))

from p0_prepare import (  # noqa: E402
    SOLVER_ENVIRONMENT,
    Sentinel,
    SolverCell,
    prepare_p0,
    run_sentinels,
    validate_preparation,
)
from p0_execute import (  # noqa: E402
    ADMISSION_PATH,
    AXEYUM_CLOSURE_RESULT_PATH,
    BITWUZLA_RECOVERY_PATH,
    CELL_RESULT_SCHEMA,
    CLOSURE_ADMISSION_PATH,
    CVC5_RESULT_PATH,
    adjudicate_cell,
    cell_result_root,
    migrate_legacy_adjudication,
    publish_cell_result,
    require_integrated_admission,
    require_integrated_bitwuzla_recovery,
    require_integrated_cell_admission,
    validate_cell_result,
    validate_cell_launch,
)
from resume_contract import ContractError, canonical_bytes, digest  # noqa: E402
from resume_fs import read_canonical_json  # noqa: E402
from resume_runner import sha256_file, toolchain_identity_sha256  # noqa: E402


FAKE_SOLVER = """#!/usr/bin/env python3
import pathlib
import sys

text = pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")
print("unsat" if "EXPECT_UNSAT" in text else "sat", flush=True)
"""


def _seal(value: dict) -> dict:
    result = dict(value)
    result["record_sha256"] = digest(result)
    return result


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _cell_result_fixture(root: Path) -> tuple[Path, dict, Path]:
    preparation = root / "preparation"
    run_dir = preparation / "cells" / "axeyum"
    (run_dir / "records").mkdir(parents=True)
    (preparation / "complete.json").write_bytes(b'{"fixture":"complete"}\n')
    cells = []
    for solver_id in ("axeyum", "cvc5", "bitwuzla"):
        cell_root = preparation / "cells" / solver_id
        cell_root.mkdir(parents=True, exist_ok=True)
        manifest = preparation / "inputs" / f"{solver_id}-run-manifest.json"
        manifest.parent.mkdir(parents=True, exist_ok=True)
        manifest.write_bytes(
            canonical_bytes({"identity_sha256": f"{solver_id:0<64}"[:64]})
        )
        cells.append(
            {
                "solver_id": solver_id,
                "attempt_root": str(cell_root),
                "run_manifest_path": str(manifest),
            }
        )
    record = {
        "benchmark_id": "QF_FP/fixture.smt2",
        "benchmark_sha256": "b" * 64,
        "expected_status": "sat",
        "reported_status": "sat",
        "result_key": "r" * 64,
        "termination_class": "completed",
    }
    (run_dir / "records" / f"{record['result_key']}.json").write_bytes(
        canonical_bytes(record)
    )
    (run_dir / "resource-completion.json").write_bytes(
        canonical_bytes({"record_sha256": "c" * 64})
    )
    (run_dir / "multi-host-completion.json").write_bytes(
        canonical_bytes({"record_sha256": "d" * 64})
    )
    completion = {"cells": cells, "record_sha256": "e" * 64}
    return preparation, completion, run_dir


def _accepted_root(shared: Path, corpus: Path) -> Path:
    rows = [
        (
            "non-incremental/QF_AUFLIA/fixture/sat.smt2",
            "QF_AUFLIA",
            "(set-logic QF_AUFLIA)\n(set-info :status sat)\n(check-sat)\n",
        ),
        (
            "non-incremental/QF_FP/fixture/unsat.smt2",
            "QF_FP",
            "(set-logic QF_FP)\n(set-info :status unsat)\n; EXPECT_UNSAT\n(check-sat)\n",
        ),
    ]
    attempt = shared / "accepted-staging"
    attempt.mkdir()
    selected = attempt / "official-selected.txt"
    selected.write_text("".join(f"{row[0]}\n" for row in rows), encoding="utf-8")
    ledger = attempt / "selected-files.jsonl"
    ledger_rows = []
    for benchmark_id, logic, content in rows:
        path = corpus / benchmark_id
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
        ledger_rows.append(
            canonical_bytes(
                {
                    "archive": f"{logic}.tar.zst",
                    "benchmark_id": benchmark_id,
                    "bytes": path.stat().st_size,
                    "logic": logic,
                    "sha256": _sha(path),
                }
            )
        )
    ledger.write_bytes(b"".join(ledger_rows))
    completion = {
        "artifacts": {
            "official-selected.txt": _sha(selected),
            "selected-files.jsonl": _sha(ledger),
        },
        "authority_sha256": "a" * 64,
        "metadata_rows": len(rows),
        "payload_sha256": "",
        "schema": "axeyum-smtcomp-official-selection-v1",
        "selected_files": len(rows),
        "selection_observed": True,
        "status": "complete",
    }
    completion["payload_sha256"] = digest(
        {key: value for key, value in completion.items() if key != "payload_sha256"}
    )
    complete = attempt / "complete.json"
    complete.write_bytes(canonical_bytes(completion))
    accepted = shared / f"accepted-{_sha(complete)}"
    attempt.rename(accepted)
    return accepted


def _filesystem(shared: Path) -> dict:
    value = {
        "source": "fixture:/nfs",
        "filesystem_type": "nfs4",
        "mount_point": str(shared),
        "options": ["hard", "local_lock=none", "vers=4.1"],
    }
    value["class_sha256"] = digest(value)
    return value


def _observations(shared: Path) -> list[dict]:
    filesystem = _filesystem(shared)
    common = {
        "schema": "axeyum.smtcomp-host-observation.v1",
        "kernel_release": platform.release(),
        "machine": platform.machine(),
        "python_version": platform.python_version(),
        "python_executable_sha256": sha256_file(Path(sys.executable)),
        "toolchain_identity_sha256": toolchain_identity_sha256(),
        "cgroup_controllers": ["cpu", "memory", "pids"],
        "user_systemd_transient": True,
        "shared_filesystem": filesystem,
        "shared_filesystem_class_sha256": filesystem["class_sha256"],
    }
    return [_seal({**common, "hostname": f"host-{index}"}) for index in range(3)]


class P0PrepareTests(unittest.TestCase):
    def test_integrated_admission_requires_exact_origin_main_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            result = root / ADMISSION_PATH
            result.parent.mkdir(parents=True)
            result.write_bytes(b"accepted result\n")
            with mock.patch(
                "p0_execute.subprocess.check_output",
                side_effect=[b"", b"different result\n"],
            ):
                with self.assertRaisesRegex(ContractError, "different P0 admission"):
                    require_integrated_admission(root)
            with mock.patch(
                "p0_execute.subprocess.check_output",
                side_effect=[b"", result.read_bytes()],
            ):
                require_integrated_admission(root)

    def test_later_cell_admission_requires_integrated_axeyum_closure_result(
        self,
    ) -> None:
        with mock.patch("p0_execute.require_integrated_admission") as base:
            with mock.patch("p0_execute.require_integrated_path") as path:
                require_integrated_cell_admission(ROOT, "axeyum")
                base.assert_called_once_with(ROOT)
                self.assertEqual(
                    [call.args[1] for call in path.call_args_list],
                    [
                        CLOSURE_ADMISSION_PATH,
                        Path("scripts/smtcomp_repro/p0_execute.py"),
                        Path("scripts/smtcomp_repro/resume_runner.py"),
                    ],
                )

        with mock.patch("p0_execute.require_integrated_admission") as base:
            with mock.patch("p0_execute.require_integrated_path") as path:
                require_integrated_cell_admission(ROOT, "cvc5")
                base.assert_called_once_with(ROOT)
                self.assertEqual(
                    [call.args[1] for call in path.call_args_list],
                    [
                        CLOSURE_ADMISSION_PATH,
                        Path("scripts/smtcomp_repro/p0_execute.py"),
                        Path("scripts/smtcomp_repro/resume_runner.py"),
                        AXEYUM_CLOSURE_RESULT_PATH,
                    ],
                )

        with mock.patch("p0_execute.require_integrated_admission") as base:
            with mock.patch("p0_execute.require_integrated_path") as path:
                require_integrated_cell_admission(ROOT, "bitwuzla")
                base.assert_called_once_with(ROOT)
                self.assertEqual(
                    [call.args[1] for call in path.call_args_list],
                    [
                        CLOSURE_ADMISSION_PATH,
                        Path("scripts/smtcomp_repro/p0_execute.py"),
                        Path("scripts/smtcomp_repro/resume_runner.py"),
                        AXEYUM_CLOSURE_RESULT_PATH,
                        CVC5_RESULT_PATH,
                    ],
                )

        with mock.patch("p0_execute.require_integrated_cell_admission") as base:
            with mock.patch("p0_execute.require_integrated_path") as path:
                require_integrated_bitwuzla_recovery(ROOT)
                base.assert_called_once_with(ROOT, "bitwuzla")
                self.assertEqual(
                    [call.args[1] for call in path.call_args_list],
                    [
                        BITWUZLA_RECOVERY_PATH,
                        Path("scripts/smtcomp_repro/multi_host.py"),
                        Path("scripts/smtcomp_repro/resume_fs.py"),
                    ],
                )

    def test_cell_results_stay_outside_run_root_and_resume_completion_last(self) -> None:
        for interrupted_phase in ("after_external_adjudication", "after_raw_export"):
            with self.subTest(interrupted_phase=interrupted_phase):
                with tempfile.TemporaryDirectory() as tmp:
                    preparation, completion, run_dir = _cell_result_fixture(Path(tmp))
                    raw = b'{"QF_FP/fixture.smt2":{"axeyum":{}}}'

                    def interrupt(phase: str) -> None:
                        if phase == interrupted_phase:
                            raise RuntimeError(phase)

                    patches = (
                        mock.patch("p0_execute.finalize_multi_host_run", return_value={}),
                        mock.patch(
                            "p0_execute.validate_bundle_directory",
                            return_value=b"canonical-bundle",
                        ),
                        mock.patch("p0_execute.legacy_raw_bytes", return_value=raw),
                    )
                    with patches[0], patches[1], patches[2]:
                        with self.assertRaisesRegex(RuntimeError, interrupted_phase):
                            publish_cell_result(
                                preparation_root=preparation,
                                completion=completion,
                                cell_id="axeyum",
                                run_dir=run_dir,
                                phase_hook=interrupt,
                            )
                        partial = cell_result_root(preparation, "axeyum")
                        self.assertFalse((partial / "complete.json").exists())
                        self.assertTrue((partial / "p0-cell-adjudication.json").exists())
                        self.assertEqual(
                            (partial / "raw-results.json").exists(),
                            interrupted_phase == "after_raw_export",
                        )
                        result = publish_cell_result(
                            preparation_root=preparation,
                            completion=completion,
                            cell_id="axeyum",
                            run_dir=run_dir,
                        )
                        self.assertEqual(result["schema"], CELL_RESULT_SCHEMA)
                        self.assertTrue(result["safe_to_continue"])
                        self.assertEqual(result["raw_result_count"], 1)
                        self.assertEqual(
                            validate_cell_result(
                                preparation_root=preparation,
                                completion=completion,
                                cell_id="axeyum",
                                run_dir=run_dir,
                            ),
                            result,
                        )
                        unexpected = partial / "unexpected.json"
                        unexpected.write_bytes(b"{}")
                        with self.assertRaisesRegex(
                            ContractError, "unexpected P0 cell-result artifact"
                        ):
                            validate_cell_result(
                                preparation_root=preparation,
                                completion=completion,
                                cell_id="axeyum",
                                run_dir=run_dir,
                            )
                        unexpected.unlink()
                        raw_path = partial / "raw-results.json"
                        raw_path.chmod(0o644)
                        raw_path.write_bytes(b"{}")
                        with self.assertRaisesRegex(ContractError, "raw export drift"):
                            validate_cell_result(
                                preparation_root=preparation,
                                completion=completion,
                                cell_id="axeyum",
                                run_dir=run_dir,
                            )
                    self.assertFalse((run_dir / "p0-cell-adjudication.json").exists())
                    self.assertFalse((run_dir / "raw-results.json").exists())
                    self.assertEqual(
                        sorted(
                            path.name
                            for path in cell_result_root(
                                preparation, "axeyum"
                            ).iterdir()
                        ),
                        ["complete.json", "p0-cell-adjudication.json", "raw-results.json"],
                    )

    def test_cell_result_conflict_stops_before_raw_or_completion(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            preparation, completion, run_dir = _cell_result_fixture(Path(tmp))
            result_root = cell_result_root(preparation, "axeyum")
            result_root.mkdir(parents=True)
            (result_root / "p0-cell-adjudication.json").write_bytes(b"conflict")
            with (
                mock.patch("p0_execute.finalize_multi_host_run", return_value={}),
                mock.patch(
                    "p0_execute.validate_bundle_directory",
                    return_value=b"canonical-bundle",
                ),
                mock.patch(
                    "p0_execute.legacy_raw_bytes",
                    return_value=b'{"QF_FP/fixture.smt2":{"axeyum":{}}}',
                ),
                self.assertRaisesRegex(ContractError, "immutable checkpoint conflict"),
            ):
                publish_cell_result(
                    preparation_root=preparation,
                    completion=completion,
                    cell_id="axeyum",
                    run_dir=run_dir,
                )
            self.assertFalse((result_root / "raw-results.json").exists())
            self.assertFalse((result_root / "complete.json").exists())

    def test_legacy_adjudication_quarantine_is_exact_and_idempotent(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            run_dir = Path(tmp)
            data = canonical_bytes({"schema": "legacy-fixture"})
            digest_hex = hashlib.sha256(data).hexdigest()
            source = run_dir / "p0-cell-adjudication.json"
            source.write_bytes(data)

            def interrupt(phase: str) -> None:
                if phase == "after_legacy_quarantine":
                    raise RuntimeError(phase)

            with self.assertRaisesRegex(RuntimeError, "after_legacy_quarantine"):
                migrate_legacy_adjudication(
                    run_dir=run_dir,
                    adjudication_sha256=digest_hex,
                    phase_hook=interrupt,
                )
            destination = (
                run_dir
                / "quarantine"
                / f"p0-cell-adjudication-layout-v1-{digest_hex}.json"
            )
            self.assertFalse(source.exists())
            self.assertEqual(destination.read_bytes(), data)
            migrate_legacy_adjudication(
                run_dir=run_dir,
                adjudication_sha256=digest_hex,
            )
            with self.assertRaisesRegex(ContractError, "source adjudication mismatch"):
                migrate_legacy_adjudication(
                    run_dir=run_dir,
                    adjudication_sha256="0" * 64,
                )
            source.write_bytes(data)
            with self.assertRaisesRegex(ContractError, "duplicate adjudication"):
                migrate_legacy_adjudication(
                    run_dir=run_dir,
                    adjudication_sha256=digest_hex,
                )

    def test_adjudication_finds_known_and_cross_solver_conflicts(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            cells = []
            for solver_id in ("axeyum", "cvc5", "bitwuzla"):
                run_root = root / solver_id
                (run_root / "records").mkdir(parents=True)
                run_manifest = run_root / "run-manifest.json"
                run_manifest.write_bytes(
                    canonical_bytes({"identity_sha256": solver_id * 8})
                )
                cells.append(
                    {
                        "solver_id": solver_id,
                        "attempt_root": str(run_root),
                        "run_manifest_path": str(run_manifest),
                    }
                )
            shared = {
                "benchmark_id": "QF_FP/fixture/conflict.smt2",
                "benchmark_sha256": "b" * 64,
                "expected_status": "sat",
            }
            (root / "axeyum" / "records" / "ax.json").write_bytes(
                canonical_bytes({**shared, "result_key": "ax", "reported_status": "sat", "termination_class": "completed"})
            )
            (root / "cvc5" / "records" / "cv.json").write_bytes(
                canonical_bytes({**shared, "result_key": "cv", "reported_status": "unsat", "termination_class": "completed"})
            )
            result = adjudicate_cell(
                completion={"cells": cells},
                cell_id="cvc5",
                run_dir=root / "cvc5",
            )
            self.assertFalse(result["safe_to_continue"])
            self.assertEqual(len(result["known_status_contradictions"]), 1)
            self.assertEqual(len(result["cross_solver_disagreements"]), 1)

    def test_wrong_fp_sentinel_stops_preparation(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            solver = root / "always-sat"
            solver.write_text(FAKE_SOLVER, encoding="utf-8")
            solver.chmod(0o755)
            sentinel_path = root / "qf-abvfp.smt2"
            sentinel_path.write_text("(check-sat)\n", encoding="utf-8")
            cells = [
                SolverCell("axeyum", solver, "test", "all", 19_000),
                SolverCell("cvc5", solver, "test", "all"),
                SolverCell("bitwuzla", solver, "test", "fp"),
            ]
            with self.assertRaisesRegex(ContractError, "FP incident sentinel failed"):
                run_sentinels(
                    solvers=cells,
                    copied_binaries={cell.solver_id: solver for cell in cells},
                    sentinels=[
                        Sentinel(
                            "qf-abvfp",
                            sentinel_path,
                            _sha(sentinel_path),
                            "qf_abvfp",
                        )
                    ],
                    output_dir=root / "outputs",
                )

    def test_prepares_three_cells_without_launch_and_detects_mutation(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            shared = Path(tmp).resolve()
            corpus = shared / "corpus"
            corpus.mkdir()
            accepted = _accepted_root(shared, corpus)
            corpus_manifest = shared / "corpus-audit.json"
            corpus_manifest.write_bytes(b'{"fixture":"corpus"}\n')
            binaries = []
            for solver_id in ("axeyum", "cvc5", "bitwuzla"):
                path = shared / f"source-{solver_id}"
                path.write_text(FAKE_SOLVER, encoding="utf-8")
                path.chmod(0o755)
                binaries.append(path)
            sentinels = []
            for sentinel_id, kind, unsat in (
                ("qf-abvfp", "qf_abvfp", True),
                ("qf-bvfp", "qf_bvfp", True),
                ("qf-auflia", "qf_auflia", False),
            ):
                path = shared / f"{sentinel_id}.smt2"
                path.write_text(
                    "(check-sat)\n" + ("; EXPECT_UNSAT\n" if unsat else ""),
                    encoding="utf-8",
                )
                sentinels.append(Sentinel(sentinel_id, path, _sha(path), kind))

            filesystem = _filesystem(shared)
            with mock.patch(
                "multi_host.shared_filesystem_observation", return_value=filesystem
            ):
                attempt = prepare_p0(
                    repository_root=ROOT,
                    source_root=SMTCOMP,
                    shared_root=shared,
                    accepted_root=accepted,
                    corpus_root=corpus,
                    source_corpus_manifest=corpus_manifest,
                    attempt_id="test-p0-preparation",
                    solvers=[
                        SolverCell("axeyum", binaries[0], "test", "all", 19_000),
                        SolverCell("cvc5", binaries[1], "test", "all"),
                        SolverCell("bitwuzla", binaries[2], "test", "fp"),
                    ],
                    sentinels=sentinels,
                    observations=_observations(shared),
                    expected_selection=None,
                    expected_oracles=None,
                    require_clean=False,
                )
                completion = validate_preparation(attempt)

                _completion, _plan, run_dir, commands = validate_cell_launch(
                    repository_root=ROOT,
                    preparation_root=attempt,
                    cell_id="axeyum",
                    acknowledged_completion_sha256=_sha(attempt / "complete.json"),
                    require_integrated=False,
                )
                self.assertEqual(run_dir, attempt / "cells" / "axeyum")
                self.assertEqual(sorted(commands), ["initial-0", "initial-1", "initial-2"])
                with self.assertRaisesRegex(ContractError, "prior P0 cell is incomplete"):
                    validate_cell_launch(
                        repository_root=ROOT,
                        preparation_root=attempt,
                        cell_id="cvc5",
                        acknowledged_completion_sha256=_sha(attempt / "complete.json"),
                        require_integrated=False,
                    )

            self.assertEqual(completion["status"], "prepared-no-launch")
            self.assertFalse(completion["launch_authorized"])
            self.assertEqual(completion["solver_environment"], SOLVER_ENVIRONMENT)
            self.assertEqual(len(completion["cells"]), 3)
            self.assertEqual(len(completion["sentinels"]), 8)
            for cell in completion["cells"]:
                self.assertEqual(len(cell["commands"]), 6)
                run_root = Path(cell["attempt_root"])
                run_manifest = Path(cell["run_manifest_path"])
                self.assertEqual(run_manifest.parent, attempt / "inputs")
                self.assertFalse((run_root / "run-manifest.json").exists())
                self.assertEqual(list((run_root / "records").iterdir()), [])
                run = read_canonical_json(run_manifest)
                self.assertEqual(
                    run["identity"]["solver_environment_sha256"],
                    digest(SOLVER_ENVIRONMENT),
                )
                for command in cell["commands"]:
                    command_record = read_canonical_json(Path(command["path"]))
                    self.assertEqual(
                        Path(command_record["run_manifest_path"]), run_manifest
                    )
                    argv = command_record["argv"]
                    self.assertIn("AYU_THREADS=1", argv)
                    self.assertIn("OMP_NUM_THREADS=1", argv)
                    self.assertIn("RAYON_NUM_THREADS=1", argv)

            command_path = Path(completion["cells"][0]["commands"][0]["path"])
            original_command = command_path.read_bytes()
            command = json.loads(original_command)
            command["run_manifest_path"] = str(attempt / "inputs" / "wrong.json")
            command["record_sha256"] = digest(
                {key: value for key, value in command.items() if key != "record_sha256"}
            )
            command_path.chmod(0o644)
            command_path.write_bytes(canonical_bytes(command))
            with self.assertRaisesRegex(ContractError, "artifact drift"):
                validate_cell_launch(
                    repository_root=ROOT,
                    preparation_root=attempt,
                    cell_id="axeyum",
                    acknowledged_completion_sha256=_sha(attempt / "complete.json"),
                    require_integrated=False,
                )
            command_path.write_bytes(original_command)

            environment = attempt / "inputs" / "environment.json"
            environment.chmod(0o644)
            environment.write_bytes(b"{}\n")
            with self.assertRaisesRegex(ContractError, "artifact drift"):
                validate_preparation(attempt)


if __name__ == "__main__":
    unittest.main()
