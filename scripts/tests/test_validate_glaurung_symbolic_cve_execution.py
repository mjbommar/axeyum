import importlib.util
import pathlib
import subprocess
import tempfile
import unittest


SCRIPT = (
    pathlib.Path(__file__).resolve().parents[1]
    / "validate-glaurung-symbolic-cve-execution.py"
)
SPEC = importlib.util.spec_from_file_location("validate_symbolic_cve_execution", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


QUALIFICATION_SHA = "a" * 64


def qualification() -> dict:
    return {
        "schema": "axeyum.glaurung-symbolic-cve-qualification.v2",
        "valid": True,
        "claim": "pre-execution symbolic-CVE corpus qualification only",
        "summary": {"rows": 2, "current_fragment_candidates": 1},
        "rows": [
            {
                "cve": "CVE-TEST-0001",
                "current_fragment_candidate": True,
                "effective_source_file": "drivers/test/direct.c",
                "handler_fn": "direct_ioctl",
                "ioctl_cmd": "TEST_DIRECT",
                "vulnerability_class": "int-overflow",
                "fixing_commit": "1" * 40,
                "vulnerable_parent_commit": "2" * 40,
                "patch_sha256": "3" * 64,
            },
            {
                "cve": "CVE-TEST-0002",
                "current_fragment_candidate": False,
                "effective_source_file": "drivers/test/race.c",
                "handler_fn": "race_ioctl",
                "ioctl_cmd": "TEST_RACE",
                "vulnerability_class": "uaf",
                "fixing_commit": "4" * 40,
                "vulnerable_parent_commit": "5" * 40,
                "patch_sha256": "6" * 64,
            },
        ],
    }


def registration() -> dict:
    return {
        "schema": "axeyum.glaurung-symbolic-cve-execution-registration.v1",
        "qualification_sha256": QUALIFICATION_SHA,
        "expected_candidates": 1,
        "artifact_protocol": {
            "architecture": "aarch64",
            "kernel_config_target": "defconfig",
            "llvm_suffix": "-18",
            "translation_unit_mode": "kbuild-command-replay-embedded-bitcode-v1",
        },
        "glaurung_baseline": {
            "revision": "7" * 40,
            "limitation": "no-linux-symbolic-detector-v1",
            "files": {"src/analysis/linux_ioctl.rs": "8" * 64},
        },
        "rows": [
            {
                "cve": "CVE-TEST-0001",
                "source_file": "drivers/test/direct.c",
                "object_target": "drivers/test/direct.o",
                "handler_symbol": "direct_ioctl",
                "entry_kind": "file-operations-ioctl",
                "entry_abi": "x0=file,x1=cmd,x2=arg",
                "attacker_inputs": ["cmd", "arg"],
                "environment_requirements": ["file private_data"],
                "vulnerability_obligation": {
                    "vulnerable": "reachable-safety-violation",
                    "fixed": "same-witness-infeasible",
                    "sink": "integer-overflow",
                },
            }
        ],
    }


def resolved_sources() -> dict:
    return {
        "CVE-TEST-0001": {
            "vulnerable_source_sha256": "9" * 64,
            "fixed_source_sha256": "b" * 64,
            "makefile": "drivers/test/Makefile",
            "makefile_object_present_vulnerable": True,
            "makefile_object_present_fixed": True,
            "handler_present_vulnerable": True,
            "handler_present_fixed": True,
        }
    }


class SymbolicCveExecutionRegistrationTests(unittest.TestCase):
    def test_accepts_exact_candidate_and_preserves_unrun_boundaries(self) -> None:
        report = MODULE.validate_registration(
            qualification(),
            registration(),
            resolved_sources(),
            qualification_sha256=QUALIFICATION_SHA,
            glaurung_revision="7" * 40,
            glaurung_hashes={"src/analysis/linux_ioctl.rs": "8" * 64},
        )
        self.assertTrue(report["valid"])
        self.assertEqual(report["summary"]["qualified_candidates"], 1)
        self.assertEqual(report["summary"]["builds_executed"], 0)
        self.assertEqual(report["summary"]["frontend_rows_executed"], 0)
        self.assertEqual(report["rows"][0]["build_status"], "not-run")
        self.assertEqual(report["rows"][0]["frontend_status"], "not-run")

    def test_rejects_qualification_hash_drift(self) -> None:
        with self.assertRaisesRegex(ValueError, "qualification SHA-256"):
            MODULE.validate_registration(
                qualification(),
                registration(),
                resolved_sources(),
                qualification_sha256="f" * 64,
                glaurung_revision="7" * 40,
                glaurung_hashes={"src/analysis/linux_ioctl.rs": "8" * 64},
            )

    def test_rejects_missing_or_extra_candidate_rows(self) -> None:
        bad = registration()
        bad["rows"] = []
        with self.assertRaisesRegex(ValueError, "candidate CVEs"):
            MODULE.validate_registration(
                qualification(),
                bad,
                resolved_sources(),
                qualification_sha256=QUALIFICATION_SHA,
                glaurung_revision="7" * 40,
                glaurung_hashes={"src/analysis/linux_ioctl.rs": "8" * 64},
            )

    def test_rejects_non_translation_unit_object_target(self) -> None:
        bad = registration()
        bad["rows"][0]["object_target"] = "drivers/test/combined.o"
        with self.assertRaisesRegex(ValueError, "translation-unit object"):
            MODULE.validate_registration(
                qualification(),
                bad,
                resolved_sources(),
                qualification_sha256=QUALIFICATION_SHA,
                glaurung_revision="7" * 40,
                glaurung_hashes={"src/analysis/linux_ioctl.rs": "8" * 64},
            )

    def test_rejects_empty_environment_or_obligation(self) -> None:
        for field in ("environment_requirements", "attacker_inputs"):
            bad = registration()
            bad["rows"][0][field] = []
            with self.subTest(field=field), self.assertRaisesRegex(
                ValueError, field
            ):
                MODULE.validate_registration(
                    qualification(),
                    bad,
                    resolved_sources(),
                    qualification_sha256=QUALIFICATION_SHA,
                    glaurung_revision="7" * 40,
                    glaurung_hashes={"src/analysis/linux_ioctl.rs": "8" * 64},
                )

    def test_rejects_glaurung_revision_or_file_drift(self) -> None:
        with self.assertRaisesRegex(ValueError, "Glaurung revision"):
            MODULE.validate_registration(
                qualification(),
                registration(),
                resolved_sources(),
                qualification_sha256=QUALIFICATION_SHA,
                glaurung_revision="c" * 40,
                glaurung_hashes={"src/analysis/linux_ioctl.rs": "8" * 64},
            )
        with self.assertRaisesRegex(ValueError, "Glaurung file hashes"):
            MODULE.validate_registration(
                qualification(),
                registration(),
                resolved_sources(),
                qualification_sha256=QUALIFICATION_SHA,
                glaurung_revision="7" * 40,
                glaurung_hashes={"src/analysis/linux_ioctl.rs": "d" * 64},
            )

    def test_resolves_real_git_source_and_makefile_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            repo = pathlib.Path(tmp)
            subprocess.run(["git", "init", "-q", str(repo)], check=True)
            subprocess.run(
                ["git", "-C", str(repo), "config", "user.email", "test@example.invalid"],
                check=True,
            )
            subprocess.run(
                ["git", "-C", str(repo), "config", "user.name", "Test"],
                check=True,
            )
            source = repo / "drivers/test/direct.c"
            source.parent.mkdir(parents=True)
            source.write_text("long direct_ioctl(void) { return 1; }\n")
            (source.parent / "Makefile").write_text("obj-m += direct.o\n")
            subprocess.run(["git", "-C", str(repo), "add", "."], check=True)
            subprocess.run(["git", "-C", str(repo), "commit", "-qm", "vulnerable"], check=True)
            parent = subprocess.check_output(
                ["git", "-C", str(repo), "rev-parse", "HEAD"], text=True
            ).strip()
            source.write_text("long direct_ioctl(void) { return 0; }\n")
            subprocess.run(["git", "-C", str(repo), "commit", "-qam", "fixed"], check=True)
            fixed = subprocess.check_output(
                ["git", "-C", str(repo), "rev-parse", "HEAD"], text=True
            ).strip()
            rows = [
                {
                    "cve": "CVE-TEST-0001",
                    "source_file": "drivers/test/direct.c",
                    "object_target": "drivers/test/direct.o",
                    "handler_symbol": "direct_ioctl",
                    "vulnerable_parent_commit": parent,
                    "fixing_commit": fixed,
                }
            ]
            evidence = MODULE.resolve_linux_sources(repo, rows)
            self.assertTrue(evidence["CVE-TEST-0001"]["handler_present_vulnerable"])
            self.assertTrue(evidence["CVE-TEST-0001"]["handler_present_fixed"])
            self.assertTrue(
                evidence["CVE-TEST-0001"]["makefile_object_present_vulnerable"]
            )
            self.assertNotEqual(
                evidence["CVE-TEST-0001"]["vulnerable_source_sha256"],
                evidence["CVE-TEST-0001"]["fixed_source_sha256"],
            )


if __name__ == "__main__":
    unittest.main()
