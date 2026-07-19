import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "run-glaurung-concretization-sweep.py"
SPEC = importlib.util.spec_from_file_location("run_glaurung_concretization_sweep", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ConcretizationSweepRunnerTests(unittest.TestCase):
    def test_validate_registration_requires_claim_contract(self) -> None:
        registration = {
            "schema": MODULE.REGISTRATION_SCHEMA,
            "policies": [
                {
                    "label": label,
                    "policy_id": policy_id,
                    "harness_choice": harness_choice,
                }
                for label, policy_id, harness_choice in MODULE.EXPECTED_POLICIES
            ],
            "strata": [
                {
                    "name": "positive-control",
                    "kind": "validated-positive",
                    "driver_source": "source-manifest",
                    "driver_sha256": ["positive-sha"],
                    "work": {
                        "repetitions": 2,
                        "deadline_secs": 1,
                        "max_analyzed_functions": 1,
                        "solve_budget": 1,
                        "solve_secs": 1,
                        "process_timeout_secs": 1,
                        "check_timeout_ms": 1,
                    },
                },
                {
                    "name": "tcpip-discovery",
                    "kind": "unlabeled-discovery",
                    "driver_source": "tcpip",
                    "driver_sha256": ["tcpip-sha"],
                    "work": {
                        "repetitions": 2,
                        "deadline_secs": 1,
                        "max_analyzed_functions": 1,
                        "solve_budget": 1,
                        "solve_secs": 1,
                        "process_timeout_secs": 1,
                        "check_timeout_ms": 1,
                    },
                },
            ],
            "acceptance": {"positive_control": "exact"},
            "claim_limits": ["bounded test campaign"],
        }
        MODULE.validate_registration(registration)

        del registration["claim_limits"]
        with self.assertRaisesRegex(RuntimeError, "claim limits"):
            MODULE.validate_registration(registration)

    def test_measure_command_uses_preferred_policy_and_exact_work(self) -> None:
        policy = {
            "label": "min-unsigned",
            "policy_id": "glaurung-min-unsigned-v1",
            "harness_choice": "min-unsigned",
        }
        work = {
            "repetitions": 2,
            "deadline_secs": 60,
            "max_analyzed_functions": 100,
            "solve_budget": 50000,
            "solve_secs": 60,
            "process_timeout_secs": 120,
            "check_timeout_ms": 250,
        }
        command = MODULE.measure_command(
            python_executable="python3",
            measure_script=Path("/repo/scripts/measure.py"),
            glaurung_repo=Path("/glaurung"),
            z3_binary=Path("/bin/z3-authority"),
            axeyum_binary=Path("/bin/ax-authority"),
            drivers=[Path("/drivers/a.sys"), Path("/drivers/b.sys")],
            policy=policy,
            work=work,
            out=Path("/out/report.json"),
        )
        self.assertEqual(command[:2], ["python3", "/repo/scripts/measure.py"])
        self.assertIn("--acceptance-population", command)
        self.assertEqual(
            command[command.index("--acceptance-population") + 1],
            "high-confidence",
        )
        self.assertEqual(command.count("--driver"), 2)
        self.assertEqual(
            command[command.index("--concretization-policy") + 1],
            "min-unsigned",
        )
        self.assertNotIn("--canonical-model-choice", command)
        self.assertEqual(command[command.index("--solve-budget") + 1], "50000")

    def test_measure_command_omits_policy_for_any_model_default(self) -> None:
        policy = {
            "label": "any-model",
            "policy_id": "glaurung-any-model-v1",
            "harness_choice": None,
        }
        work = {
            "repetitions": 2,
            "deadline_secs": 60,
            "max_analyzed_functions": 100,
            "solve_budget": 50000,
            "solve_secs": 60,
            "process_timeout_secs": 120,
            "check_timeout_ms": 250,
        }
        command = MODULE.measure_command(
            python_executable="python3",
            measure_script=Path("/measure.py"),
            glaurung_repo=Path("/glaurung"),
            z3_binary=Path("/z3"),
            axeyum_binary=Path("/ax"),
            drivers=[Path("/a.sys")],
            policy=policy,
            work=work,
            out=Path("/report.json"),
        )
        self.assertNotIn("--concretization-policy", command)
        self.assertNotIn("--canonical-model-choice", command)

    def test_prepare_output_directory_refuses_existing_content(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            output = root / "output"
            MODULE.prepare_output_directory(output)
            self.assertTrue(output.is_dir())
            (output / "partial.json").write_text("{}\n", encoding="utf-8")
            with self.assertRaisesRegex(RuntimeError, "nonempty"):
                MODULE.prepare_output_directory(output)

    def test_resolve_driver_inputs_joins_manifest_and_named_discovery(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "source"
            source.mkdir()
            positive = source / "positive.sys"
            positive.write_bytes(b"positive")
            discovery = root / "tcpip.sys"
            discovery.write_bytes(b"tcpip")
            manifest_path = root / "manifest.json"
            manifest = {
                "drivers": [
                    {
                        "binary_path": "positive.sys",
                        "sha256": MODULE.file_sha256(positive),
                    }
                ]
            }
            manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
            registration = {
                "source_manifest_path": str(manifest_path),
                "source_manifest_sha256": MODULE.file_sha256(manifest_path),
                "strata": [
                    {
                        "name": "positive-control",
                        "driver_source": "source-manifest",
                        "driver_sha256": [MODULE.file_sha256(positive)],
                    },
                    {
                        "name": "tcpip-discovery",
                        "driver_source": "tcpip",
                        "driver_sha256": [MODULE.file_sha256(discovery)],
                    },
                ],
            }
            resolved = MODULE.resolve_driver_inputs(
                registration,
                repository_root=root,
                source_repository=source,
                named_inputs={"tcpip": discovery},
            )
        self.assertEqual(resolved["positive-control"], [positive.resolve()])
        self.assertEqual(resolved["tcpip-discovery"], [discovery.resolve()])

    def test_resolve_driver_inputs_rejects_hash_or_extra_input(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "source"
            source.mkdir()
            positive = source / "positive.sys"
            positive.write_bytes(b"positive")
            discovery = root / "tcpip.sys"
            discovery.write_bytes(b"tcpip")
            manifest_path = root / "manifest.json"
            manifest_path.write_text(
                json.dumps(
                    {
                        "drivers": [
                            {"binary_path": "positive.sys", "sha256": "wrong"}
                        ]
                    }
                ),
                encoding="utf-8",
            )
            registration = {
                "source_manifest_path": str(manifest_path),
                "source_manifest_sha256": MODULE.file_sha256(manifest_path),
                "strata": [
                    {
                        "name": "positive-control",
                        "driver_source": "source-manifest",
                        "driver_sha256": ["wrong"],
                    }
                ],
            }
            with self.assertRaisesRegex(RuntimeError, "binary hash"):
                MODULE.resolve_driver_inputs(
                    registration,
                    repository_root=root,
                    source_repository=source,
                    named_inputs={"unused": discovery},
                )


if __name__ == "__main__":
    unittest.main()
