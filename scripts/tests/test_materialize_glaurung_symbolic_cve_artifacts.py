import hashlib
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock


SCRIPT = (
    Path(__file__).resolve().parents[1]
    / "materialize-glaurung-symbolic-cve-artifacts.py"
)
SPEC = importlib.util.spec_from_file_location(
    "materialize_glaurung_symbolic_cve_artifacts", SCRIPT
)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def preflight() -> dict:
    return {
        "schema": "axeyum.glaurung-symbolic-cve-execution-preflight.v1",
        "valid": True,
        "artifact_protocol": {
            "architecture": "aarch64",
            "kernel_config_target": "defconfig",
            "llvm_suffix": "-18",
            "translation_unit_mode": "kbuild-command-replay-embedded-bitcode-v1",
        },
        "summary": {
            "qualified_candidates": 1,
            "builds_executed": 0,
            "frontend_rows_executed": 0,
            "detector_rows_executed": 0,
        },
        "rows": [
            {
                "cve": "CVE-TEST-0001",
                "source_file": "drivers/test/direct.c",
                "object_target": "drivers/test/direct.o",
                "makefile": "drivers/test/Makefile",
                "handler_symbol": "direct_ioctl",
                "vulnerable_parent_commit": "1" * 40,
                "fixing_commit": "2" * 40,
                "vulnerable_source_sha256": "3" * 64,
                "fixed_source_sha256": "4" * 64,
                "build_status": "not-run",
                "frontend_status": "not-run",
                "detector_status": "not-run",
            }
        ],
    }


def campaign(preflight_raw: bytes, script_raw: bytes) -> dict:
    return {
        "schema": "axeyum.glaurung-symbolic-cve-artifact-campaign.v1",
        "preflight_sha256": digest(preflight_raw),
        "builder": {
            "path": "scripts/materialize-glaurung-symbolic-cve-artifacts.py",
            "sha256": digest(script_raw),
        },
        "expected_candidates": 1,
        "expected_sides": 2,
        "build": {
            "architecture": "arm64",
            "config_target": "defconfig",
            "llvm_suffix": "-18",
            "make_jobs": 1,
        },
        "command_replay": {
            "compiler": "clang-18",
            "remove_argument_prefixes": ["-Wa,"],
            "add_arguments": ["-fembed-bitcode=all"],
            "rewrite_output": True,
            "rewrite_dependency_output": True,
        },
        "tools": [
            "git",
            "make",
            "clang-18",
            "ld.lld-18",
            "llvm-ar-18",
            "llvm-dis-18",
            "llvm-nm-18",
            "llvm-objcopy-18",
            "llvm-objdump-18",
            "llvm-readelf-18",
            "llvm-readobj-18",
            "llvm-strip-18",
        ],
        "tool_identities": {
            name: {
                "sha256": "5" * 64,
                "version_first_line": f"{name} test version",
            }
            for name in [
                "git",
                "make",
                "clang-18",
                "ld.lld-18",
                "llvm-ar-18",
                "llvm-dis-18",
                "llvm-nm-18",
                "llvm-objcopy-18",
                "llvm-objdump-18",
                "llvm-readelf-18",
                "llvm-readobj-18",
                "llvm-strip-18",
            ]
        },
    }


class SymbolicCveArtifactMaterializationTests(unittest.TestCase):
    def test_parses_exact_saved_command(self) -> None:
        raw = (
            "savedcmd_drivers/test/direct.o := clang-18 -DNAME='\"direct\"' "
            "-c -o drivers/test/direct.o /src/drivers/test/direct.c\n"
            "source_drivers/test/direct.o := /src/drivers/test/direct.c\n"
        ).encode()
        command = MODULE.parse_saved_command(
            raw,
            object_target="drivers/test/direct.o",
            source_file="drivers/test/direct.c",
        )
        self.assertEqual(command[0], "clang-18")
        self.assertEqual(command[-1], "/src/drivers/test/direct.c")
        self.assertIn('-DNAME="direct"', command)

    def test_rejects_saved_command_key_source_or_shell_drift(self) -> None:
        cases = [
            (
                b"savedcmd_drivers/test/other.o := clang-18 -c -o drivers/test/direct.o /src/drivers/test/direct.c\n",
                "saved command",
            ),
            (
                b"savedcmd_drivers/test/direct.o := clang-18 -c -o drivers/test/direct.o /src/drivers/test/other.c\n",
                "source",
            ),
            (
                b"savedcmd_drivers/test/direct.o := clang-18 -c -o drivers/test/direct.o /src/drivers/test/direct.c ; touch bad\n",
                "shell operator",
            ),
        ]
        for raw, message in cases:
            with self.subTest(message=message), self.assertRaisesRegex(
                ValueError, message
            ):
                MODULE.parse_saved_command(
                    raw,
                    object_target="drivers/test/direct.o",
                    source_file="drivers/test/direct.c",
                )

    def test_transforms_only_registered_arguments_and_outputs(self) -> None:
        original = [
            "clang-18",
            "-Wp,-MMD,drivers/test/.direct.o.d",
            "-Wa,-march=armv8.5-a",
            "-DKEEP=-Wa,inside",
            "-c",
            "-o",
            "drivers/test/direct.o",
            "/src/drivers/test/direct.c",
        ]
        transformed = MODULE.transform_compile_command(
            original,
            embedded_object=Path("/artifact/embedded.o"),
            dependency_file=Path("/artifact/embedded.d"),
        )
        self.assertEqual(transformed[0], "clang-18")
        self.assertNotIn("-Wa,-march=armv8.5-a", transformed)
        self.assertIn("-DKEEP=-Wa,inside", transformed)
        self.assertIn("-fembed-bitcode=all", transformed)
        self.assertIn("/artifact/embedded.o", transformed)
        self.assertIn("-Wp,-MMD,/artifact/embedded.d", transformed)
        self.assertNotIn("drivers/test/direct.o", transformed)
        self.assertNotIn("drivers/test/.direct.o.d", transformed)

    def test_rejects_ambiguous_or_pretransformed_command(self) -> None:
        cases = [
            ["clang-18", "-c", "x.c"],
            ["clang-18", "-c", "-o", "a.o", "-o", "b.o", "x.c"],
            ["clang-18", "-fembed-bitcode=all", "-c", "-o", "a.o", "x.c"],
            ["gcc", "-c", "-o", "a.o", "x.c"],
        ]
        for command in cases:
            with self.subTest(command=command), self.assertRaises(ValueError):
                MODULE.transform_compile_command(
                    command,
                    embedded_object=Path("embedded.o"),
                    dependency_file=Path("embedded.d"),
                )

    def test_extracts_and_frames_all_executable_sections(self) -> None:
        object_bytes = bytes(range(64))
        readobj = [
            {
                "FileSummary": {
                    "Format": "elf64-littleaarch64",
                    "Arch": "aarch64",
                    "AddressSize": "64bit",
                },
                "Sections": [
                    {
                        "Section": {
                            "Name": {"Name": ".text"},
                            "Flags": {"Flags": [{"Name": "SHF_EXECINSTR"}]},
                            "Offset": 4,
                            "Size": 4,
                        }
                    },
                    {
                        "Section": {
                            "Name": {"Name": ".init.text"},
                            "Flags": {
                                "Flags": [
                                    {"Name": "SHF_ALLOC"},
                                    {"Name": "SHF_EXECINSTR"},
                                ]
                            },
                            "Offset": 12,
                            "Size": 3,
                        }
                    },
                ],
            }
        ]
        evidence = MODULE.parse_elf_evidence(
            json.dumps(readobj).encode(), object_bytes
        )
        self.assertEqual(evidence["format"], "elf64-littleaarch64")
        self.assertEqual(evidence["arch"], "aarch64")
        self.assertEqual(evidence["section_names"], [".text", ".init.text"])
        self.assertEqual(evidence["section_sizes"], [4, 3])
        self.assertEqual(
            evidence["framed_bytes"],
            MODULE.frame_executable_sections(
                [(".text", object_bytes[4:8]), (".init.text", object_bytes[12:15])]
            ),
        )

    def test_rejects_wrong_arch_duplicate_or_out_of_bounds_sections(self) -> None:
        base = {
            "FileSummary": {
                "Format": "elf64-littleaarch64",
                "Arch": "aarch64",
                "AddressSize": "64bit",
            },
            "Sections": [
                {
                    "Section": {
                        "Name": {"Name": ".text"},
                        "Flags": {"Flags": [{"Name": "SHF_EXECINSTR"}]},
                        "Offset": 0,
                        "Size": 1,
                    }
                }
            ],
        }
        wrong_arch = json.loads(json.dumps(base))
        wrong_arch["FileSummary"]["Arch"] = "x86_64"
        duplicate = json.loads(json.dumps(base))
        duplicate["Sections"].append(duplicate["Sections"][0])
        out_of_bounds = json.loads(json.dumps(base))
        out_of_bounds["Sections"][0]["Section"]["Size"] = 2
        for value, raw, message in [
            (wrong_arch, b"x", "AArch64"),
            (duplicate, b"x", "duplicate"),
            (out_of_bounds, b"x", "bounds"),
        ]:
            with self.subTest(message=message), self.assertRaisesRegex(
                ValueError, message
            ):
                MODULE.parse_elf_evidence(json.dumps([value]).encode(), raw)

    def test_requires_exact_elf_and_ir_handler_symbols(self) -> None:
        nm = b"00000000 t direct_ioctl\n00000010 t direct_ioctl_extra\n"
        ir = b"define internal i64 @direct_ioctl(ptr %arg) { ret i64 0 }\n"
        self.assertTrue(MODULE.nm_has_symbol(nm, "direct_ioctl"))
        self.assertFalse(MODULE.nm_has_symbol(nm, "irect_ioctl"))
        self.assertTrue(MODULE.ir_has_function(ir, "direct_ioctl"))
        self.assertFalse(MODULE.ir_has_function(ir, "direct_ioctl_extra"))

    def test_validates_exact_campaign_and_preexecution_boundary(self) -> None:
        preflight_raw = (json.dumps(preflight(), sort_keys=True) + "\n").encode()
        script_raw = b"builder-v1"
        value = MODULE.validate_campaign(
            campaign(preflight_raw, script_raw),
            preflight(),
            preflight_raw=preflight_raw,
            script_raw=script_raw,
        )
        self.assertEqual(value["expected_sides"], 2)
        self.assertEqual(value["make_jobs"], 1)

    def test_rejects_campaign_hash_transform_or_executed_preflight_drift(self) -> None:
        preflight_value = preflight()
        preflight_raw = (json.dumps(preflight_value, sort_keys=True) + "\n").encode()
        script_raw = b"builder-v1"
        bad_hash = campaign(preflight_raw, script_raw)
        bad_hash["preflight_sha256"] = "0" * 64
        bad_transform = campaign(preflight_raw, script_raw)
        bad_transform["command_replay"]["remove_argument_prefixes"] = ["-W"]
        executed = preflight()
        executed["summary"]["builds_executed"] = 1
        for camp, flight, message in [
            (bad_hash, preflight_value, "preflight SHA-256"),
            (bad_transform, preflight_value, "command-replay"),
            (campaign(preflight_raw, script_raw), executed, "zero-execution"),
        ]:
            with self.subTest(message=message), self.assertRaisesRegex(
                ValueError, message
            ):
                MODULE.validate_campaign(
                    camp,
                    flight,
                    preflight_raw=preflight_raw,
                    script_raw=script_raw,
                )

    def test_rejects_observed_toolchain_identity_drift(self) -> None:
        expected = {
            "clang-18": {
                "sha256": "5" * 64,
                "version_first_line": "clang version 18",
            }
        }
        actual = {
            "clang-18": {
                "resolved_path": "/usr/bin/clang-18",
                "sha256": "5" * 64,
                "version_first_line": "clang version 18",
            }
        }
        MODULE.validate_tool_identities(expected, actual)
        actual["clang-18"]["sha256"] = "6" * 64
        with self.assertRaisesRegex(ValueError, "tool identity"):
            MODULE.validate_tool_identities(expected, actual)

    def test_refuses_existing_output_before_creation(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            output = root / "out"
            output.mkdir()
            with self.assertRaisesRegex(ValueError, "refusing to overwrite"):
                MODULE.prepare_output_root(output)
            absent = root / "absent"
            MODULE.prepare_output_root(absent)
            self.assertTrue(absent.is_dir())

    def test_validation_report_preserves_zero_build_boundary(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            preflight_raw = (json.dumps(preflight(), sort_keys=True) + "\n").encode()
            campaign_value = campaign(preflight_raw, SCRIPT.read_bytes())
            campaign_path = root / "campaign.json"
            preflight_path = root / "preflight.json"
            campaign_path.write_text(json.dumps(campaign_value) + "\n")
            preflight_path.write_bytes(preflight_raw)
            actual_tools = {
                name: {**identity, "resolved_path": f"/tools/{name}"}
                for name, identity in campaign_value["tool_identities"].items()
            }
            with (
                mock.patch.object(MODULE, "_require_clean_repo", return_value="a" * 40),
                mock.patch.object(MODULE, "_preflight_git_identities"),
                mock.patch.object(MODULE, "_resolve_tools", return_value=actual_tools),
            ):
                report = MODULE.validate_campaign_environment(
                    campaign_path=campaign_path,
                    preflight_path=preflight_path,
                    linux_repo=root,
                )
            self.assertTrue(report["valid"])
            self.assertEqual(report["registered_sides"], 2)
            self.assertEqual(report["builds_executed"], 0)


if __name__ == "__main__":
    unittest.main()
