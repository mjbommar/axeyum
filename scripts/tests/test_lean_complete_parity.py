from __future__ import annotations

import copy
import importlib.util
import sys
import unittest
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "gen_lean_complete_parity",
    ROOT / "scripts" / "gen-lean-complete-parity.py",
)
assert SPEC and SPEC.loader
GEN = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GEN
SPEC.loader.exec_module(GEN)


class LeanCompleteParityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.data = GEN.load_manifest()
        self.normalization_data = GEN.load_json(GEN.U2_NORMALIZATION_CONTRACTS)
        self.kernel_normalizer = next(
            contract
            for contract in self.normalization_data["contracts"]
            if contract["id"] == "lean-kernel-assurance-v1"
        )

    def population(self, population_id: str) -> dict:
        return next(item for item in self.data["populations"] if item["id"] == population_id)

    def axis(self, axis_id: str) -> dict:
        return next(item for item in self.data["axes"] if item["id"] == axis_id)

    def gate(self, gate_id: str) -> dict:
        return next(item for item in self.data["terminal_gates"] if item["id"] == gate_id)

    def paired_authority(self, population_id: str) -> dict:
        return next(
            item
            for item in self.data["paired_population_authorities"]
            if item["population"] == population_id
        )

    @staticmethod
    def retained_evidence() -> list[dict[str, str]]:
        return [
            {
                "path": "docs/plan/lean4-complete-parity-contract-2026-07-22.md",
                "detail": "Synthetic schema control only.",
            }
        ]

    def paired_execution(
        self, state: str, digest_byte: str, result_class: str = "success"
    ) -> dict:
        value = digest_byte * 64
        execution = {
            "record_state": state,
            "result_class": result_class if state == "complete" else None,
            "executable_sha256": value,
            "configuration_sha256": value,
            "command_sha256": value,
            "environment_sha256": value,
            "platform_id": "linux-x86-64-control",
            "resource_envelope_sha256": value,
            "attempt_id": f"attempt-{digest_byte}",
            "completion_sha256": value,
            "outcome_sha256": value,
            "assurance_sha256": value,
            "diagnostics_sha256": value,
            "duration_ms": 1,
            "peak_rss_kib": 1,
            "artifact_bytes": 1,
            "evidence": self.retained_evidence(),
            "record_sha256": None,
        }
        if state != "complete":
            for field in execution:
                if field not in {"record_state", "evidence", "record_sha256"}:
                    execution[field] = None
        execution["record_sha256"] = GEN.paired_execution_digest(execution)
        return execution

    def paired_cell(
        self,
        *,
        outcome: str = "agree-success",
        official_state: str = "complete",
        axeyum_state: str = "complete",
        official_result: str = "success",
        axeyum_result: str = "success",
        official_normalized: str | None = "2" * 64,
        axeyum_normalized: str | None = "2" * 64,
    ) -> dict:
        cell = {
            "id": "bounded-probe",
            "population": "U1",
            "population_member_id": "kernel-probe",
            "profile_id": "linux-control",
            "axis": "A1",
            "layer": self.kernel_normalizer["layer"],
            "source_sha256": "c" * 64,
            "dependency_sha256": "d" * 64,
            "source_family": "probe",
            "official": self.paired_execution(
                official_state, "a", official_result
            ),
            "axeyum": self.paired_execution(axeyum_state, "b", axeyum_result),
            "comparison": {},
            "cell_sha256": None,
        }
        comparison = {
            "outcome": outcome,
            "normalization_id": self.kernel_normalizer["id"],
            "normalization_sha256": self.kernel_normalizer["contract_sha256"],
            "contract_sha256": "f" * 64,
            "official_record_sha256": cell["official"]["record_sha256"],
            "axeyum_record_sha256": cell["axeyum"]["record_sha256"],
            "official_normalized_sha256": (
                official_normalized if official_state == "complete" else None
            ),
            "axeyum_normalized_sha256": (
                axeyum_normalized if axeyum_state == "complete" else None
            ),
            "result_sha256": None,
            "completed": True,
            "evidence": self.retained_evidence(),
        }
        comparison["result_sha256"] = GEN.paired_comparison_digest(comparison)
        cell["comparison"] = comparison
        cell["cell_sha256"] = GEN.paired_cell_digest(cell)
        return cell

    def reseal_pair(self, cell: dict) -> None:
        cell["official"]["record_sha256"] = GEN.paired_execution_digest(
            cell["official"]
        )
        cell["axeyum"]["record_sha256"] = GEN.paired_execution_digest(
            cell["axeyum"]
        )
        comparison = cell["comparison"]
        comparison["official_record_sha256"] = cell["official"]["record_sha256"]
        comparison["axeyum_record_sha256"] = cell["axeyum"]["record_sha256"]
        comparison["result_sha256"] = GEN.paired_comparison_digest(comparison)
        cell["cell_sha256"] = GEN.paired_cell_digest(cell)
        if self.data.get("paired_cells"):
            authority = self.paired_authority(cell["population"])
            authority["expected_cell_seals_sha256"] = (
                GEN.paired_cell_seals_digest([cell])
            )

    def register_bounded_pair(self, cell: dict) -> None:
        self.data["paired_cells"] = [cell]
        authority = self.paired_authority(cell["population"])
        authority.update(
            {
                "state": "bounded_profile",
                "expected_cells": 1,
                "expected_ids_sha256": GEN.paired_id_digest([cell["id"]]),
                "expected_cell_seals_sha256": GEN.paired_cell_seals_digest([cell]),
                "evidence": self.retained_evidence(),
                "residual": "Synthetic bounded schema control; no terminal credit.",
            }
        )

    def failures(self) -> list[str]:
        return GEN.validate_manifest(self.data)

    def test_m2_3_dispatch_preregistration_matches_u2_authority(self) -> None:
        authority = GEN.load_json(GEN.U2_AUTHORITY)
        cases = authority["cases"]
        route_counts = {"wrapper": 0, "lake-inline": 0, "lint": 0}
        wrapper_runners = set()
        for case in cases:
            command = case["registration"]["command"]
            if (
                command[0] == "$BASH"
                and command[1] == "$LEAN_ROOT/tests/with_stage1_test_env.sh"
            ):
                route_counts["wrapper"] += 1
                wrapper_runners.add(command[2])
            elif command[0:2] == ["$BASH", "-c"]:
                route_counts["lake-inline"] += 1
            elif command == ["$PYTHON3", "lint.py"]:
                route_counts["lint"] += 1
            else:
                self.fail(f"unregistered M2.3 dispatch route: {case['id']}")
        self.assertEqual(
            route_counts, {"wrapper": 3670, "lake-inline": 52, "lint": 1}
        )
        self.assertEqual(len(wrapper_runners), 41)
        self.assertIn(
            "$LEAN_ROOT/tests/compile_bench/run_test.sh", wrapper_runners
        )
        self.assertIn("$LEAN_ROOT/tests/elab_bench/run_test.sh", wrapper_runners)

        inline_profiles = {"default+full-lake": 0, "full-lake": 0}
        for case in cases:
            if case["kind"] != "lake-directory":
                continue
            if case["profiles"] == ["default", "full-lake"]:
                inline_profiles["default+full-lake"] += 1
            elif case["profiles"] == ["full-lake"]:
                inline_profiles["full-lake"] += 1
            else:
                self.fail(f"unexpected Lake profile set: {case['id']}")
        self.assertEqual(
            inline_profiles, {"default+full-lake": 7, "full-lake": 45}
        )

        suffix_counts = {
            suffix: sum(
                sidecar.endswith(suffix)
                for case in cases
                for sidecar in case["sidecars"]
            )
            for suffix in (
                ".init.sh",
                ".before.sh",
                ".after.sh",
                ".out.expected",
                ".out.ignored",
                ".no_interpret",
                ".do_interpret",
                ".no_compile",
            )
        }
        self.assertEqual(
            suffix_counts,
            {
                ".init.sh": 27,
                ".before.sh": 6,
                ".after.sh": 0,
                ".out.expected": 1480,
                ".out.ignored": 60,
                ".no_interpret": 6,
                ".do_interpret": 2,
                ".no_compile": 1,
            },
        )

    def test_m2_4_lake_project_preregistration_matches_u2_authority(self) -> None:
        authority = GEN.load_json(GEN.U2_AUTHORITY)
        lake_cases = [
            case for case in authority["cases"] if case["kind"] == "lake-directory"
        ]
        self.assertEqual(len(lake_cases), 52)
        self.assertEqual(
            sum(case["profiles"] == ["default", "full-lake"] for case in lake_cases),
            7,
        )
        self.assertEqual(
            sum(case["profiles"] == ["full-lake"] for case in lake_cases), 45
        )
        self.assertEqual(len({case["support_scope"] for case in lake_cases}), 52)

        selected_scripts = {case["source_path"] for case in lake_cases}
        tracked_lake_scripts = {
            row["path"]
            for row in authority["content_files"]
            if row["path"].endswith("/test.sh")
            and (
                row["path"].startswith("tests/lake/examples/")
                or row["path"].startswith("tests/lake/tests/")
            )
        }
        self.assertEqual(len(tracked_lake_scripts), 55)
        self.assertEqual(
            tracked_lake_scripts - selected_scripts,
            {
                "tests/lake/examples/bootstrap/test.sh",
                "tests/lake/tests/online/test.sh",
                "tests/lake/tests/toolchain/test.sh",
            },
        )

        prefixes = tuple(f"{case['support_scope'].rstrip('/')}/" for case in lake_cases)
        support_rows = [
            row
            for row in authority["content_files"]
            if row["path"].startswith(prefixes)
        ]
        self.assertEqual(len(support_rows), 1045)
        self.assertEqual(sum(row["bytes"] for row in support_rows), 250_410)

        config_roots: dict[str, set[str]] = {}
        for row in support_rows:
            path = row["path"]
            basename = path.rsplit("/", 1)[-1]
            if basename in {"lakefile.lean", "lakefile.toml"}:
                config_roots.setdefault(path.rsplit("/", 1)[0], set()).add(basename)
        self.assertEqual(len(config_roots), 70)
        self.assertEqual(
            sum(files == {"lakefile.lean"} for files in config_roots.values()), 46
        )
        self.assertEqual(
            sum(files == {"lakefile.toml"} for files in config_roots.values()), 17
        )
        self.assertEqual(sum(len(files) == 2 for files in config_roots.values()), 7)
        self.assertEqual(
            sum(row["path"].endswith("/lakefile.lean") for row in support_rows), 53
        )
        self.assertEqual(
            sum(row["path"].endswith("/lakefile.toml") for row in support_rows), 24
        )
        self.assertEqual(
            sum(row["path"].endswith("/lake-manifest.json") for row in support_rows),
            0,
        )
        self.assertEqual(
            sum(row["path"].endswith("/lean-toolchain") for row in support_rows), 1
        )

        no_tracked_config = {
            case["id"]
            for case in lake_cases
            if not any(
                root == case["support_scope"]
                or root.startswith(f"{case['support_scope']}/")
                for root in config_roots
            )
        }
        self.assertEqual(
            no_tracked_config,
            {
                "tests/lake/tests/13013/test.sh",
                "tests/lake/tests/api/test.sh",
                "tests/lake/tests/depTree/test.sh",
                "tests/lake/tests/env/test.sh",
                "tests/lake/tests/init/test.sh",
                "tests/lake/tests/old/test.sh",
                "tests/lake/tests/serve/test.sh",
                "tests/lake/tests/toml/test.sh",
                "tests/lake/tests/translateConfig/test.sh",
            },
        )

    def test_m2_5_compiler_runtime_ffi_preregistration_matches_m1(self) -> None:
        content = GEN.load_json(GEN.U2_NATIVE_CONTENT)
        cases = content["case_rows"]
        compiler_direct = [
            case for case in cases if "compiler-runtime" in case["direct_surfaces"]
        ]
        compiler_closure = [
            case for case in cases if "compiler-runtime" in case["surface_closure"]
        ]
        ffi_direct = [case for case in cases if "ffi" in case["direct_surfaces"]]
        self.assertEqual(len(compiler_direct), 841)
        self.assertEqual(len(compiler_closure), 860)
        self.assertEqual(len(ffi_direct), 24)
        self.assertEqual(
            sum(
                "compiler-runtime" in case["m0_direct_surfaces"]
                for case in cases
            ),
            282,
        )
        self.assertEqual(
            sum(
                "compiler-runtime" in case["content_observed_surfaces"]
                for case in cases
            ),
            559,
        )
        self.assertEqual(
            sum("ffi" in case["content_observed_surfaces"] for case in cases), 24
        )
        self.assertEqual(
            sum("lean.evaluation-command" in case["exact_signal_ids"] for case in cases),
            539,
        )
        self.assertEqual(
            sum("lean.compiler-api" in case["exact_signal_ids"] for case in cases),
            28,
        )
        self.assertEqual(
            sum("lean.ffi-declaration" in case["exact_signal_ids"] for case in cases),
            22,
        )
        self.assertEqual(
            sum("c.abi-declaration" in case["exact_signal_ids"] for case in cases),
            3,
        )
        self.assertEqual(
            sum("toml.native-link-field" in case["exact_signal_ids"] for case in cases),
            1,
        )

        compile_cases = [case for case in cases if case["family"] == "compile"]
        self.assertEqual(len(compile_cases), 60)
        no_interpret = {
            file_row["path"]
            for file_row in content["file_rows"]
            if file_row["path"].startswith("tests/compile/")
            and file_row["path"].endswith(".lean.no_interpret")
        }
        self.assertEqual(
            no_interpret,
            {
                "tests/compile/StackOverflow.lean.no_interpret",
                "tests/compile/StackOverflowTask.lean.no_interpret",
                "tests/compile/init.lean.no_interpret",
                "tests/compile/initUnboxed.lean.no_interpret",
                "tests/compile/lazylist.lean.no_interpret",
                "tests/compile/map_big.lean.no_interpret",
            },
        )
        self.assertEqual(len(compile_cases) - len(no_interpret), 54)

    def test_m2_6_editor_rpc_preregistration_corrects_version_overlay(self) -> None:
        content = GEN.load_json(GEN.U2_NATIVE_CONTENT)
        cases = content["case_rows"]
        editor_direct = [
            case for case in cases if "editor-rpc" in case["direct_surfaces"]
        ]
        self.assertEqual(len(editor_direct), 147)
        self.assertEqual(
            sum("editor-rpc" in case["m0_direct_surfaces"] for case in cases),
            137,
        )
        self.assertEqual(
            sum(
                "editor-rpc" in case["content_observed_surfaces"]
                for case in cases
            ),
            22,
        )
        self.assertEqual(
            sum("lean.server-api" in case["exact_signal_ids"] for case in cases),
            18,
        )
        self.assertEqual(
            sum("json.rpc-method" in case["exact_signal_ids"] for case in cases),
            0,
        )
        self.assertEqual(
            sum("text.rpc-candidate" in case["exact_signal_ids"] for case in cases),
            0,
        )

        rejected_case_paths = {
            "tests/lake/examples/deps/test.sh": {
                "tests/lake/examples/deps/bar/lake-manifest.expected.json",
            },
            "tests/lake/tests/manifest/test.sh": {
                "tests/lake/tests/manifest/lake-manifest-latest.json",
                "tests/lake/tests/manifest/lake-manifest-v1.0.0.json",
                "tests/lake/tests/manifest/lake-manifest-v1.1.0.json",
                "tests/lake/tests/manifest/lake-manifest-v1.2.0.json",
                "tests/lake/tests/manifest/lake-manifest-v4.json",
                "tests/lake/tests/manifest/lake-manifest-v5.json",
                "tests/lake/tests/manifest/lake-manifest-v6.json",
                "tests/lake/tests/manifest/lake-manifest-v7.json",
            },
            "tests/lake/tests/reservoirConfig/test.sh": {
                "tests/lake/tests/reservoirConfig/expected.json",
            },
            "tests/lake/tests/toml/test.sh": {
                "tests/lake/tests/toml/tests/valid/inline-table/end-in-bool.json",
            },
        }
        version_cases = {
            case["case_id"]: case
            for case in cases
            if "json.document-version" in case["exact_signal_ids"]
        }
        self.assertEqual(set(version_cases), set(rejected_case_paths))
        self.assertEqual(
            {
                case_id: {
                    evidence["path"]
                    for evidence in case["signal_evidence"]
                    if evidence["signal_id"] == "json.document-version"
                }
                for case_id, case in version_cases.items()
            },
            rejected_case_paths,
        )
        self.assertEqual(sum(map(len, rejected_case_paths.values())), 11)
        for case in version_cases.values():
            self.assertEqual(case["family"], "lake")
            self.assertEqual(case["kind"], "lake-directory")
            self.assertEqual(
                set(case["exact_signal_ids"])
                & {
                    "json.document-version",
                    "json.rpc-method",
                    "lean.server-api",
                    "text.rpc-candidate",
                },
                {"json.document-version"},
            )

        raw_version_paths = {
            row["path"]
            for row in content["file_rows"]
            if any(
                hit["signal_id"] == "json.document-version"
                for hit in row["signal_hits"]
            )
        }
        self.assertEqual(
            raw_version_paths - set().union(*rejected_case_paths.values()),
            {
                "tests/server/diags.lean.content_diag.json",
                "tests/server/edits_diag.json",
            },
        )

        qualified = [
            case
            for case in editor_direct
            if case["case_id"] not in rejected_case_paths
        ]
        self.assertEqual(len(qualified), 143)
        self.assertEqual(
            Counter(case["family"] for case in qualified),
            Counter(
                {
                    "server_interactive": 132,
                    "elab": 5,
                    "server": 4,
                    "doc-examples": 1,
                    "misc_dir": 1,
                }
            ),
        )
        self.assertEqual(
            Counter(case["kind"] for case in qualified),
            Counter({"pile": 142, "directory": 1}),
        )

    def test_m2_7_variant_merge_preregistration_matches_m2_0(self) -> None:
        dependency = GEN.load_json(GEN.U2_NATIVE_DEPENDENCY)
        selections = dependency["selection_rows"]
        variants = dependency["provider_variants"]
        cases = dependency["case_rows"]

        self.assertEqual(len(selections), 8)
        self.assertEqual(len(variants), 111)
        self.assertEqual(len(cases), 3_723)
        self.assertEqual(
            dependency["summary"]["case_variant_occurrences"], 408_374
        )
        self.assertEqual(
            Counter(case["provider_variant_count"] for case in cases),
            Counter({111: 3_476, 104: 202, 34: 45}),
        )
        self.assertEqual(
            sum(case["provider_variant_count"] for case in cases), 408_374
        )
        self.assertEqual(
            Counter(len(case["applicable_selection_set_ids"]) for case in cases),
            Counter({8: 3_476, 6: 202, 3: 45}),
        )
        self.assertTrue(
            all(
                case["variant_factoring"] == "selection-set-reference"
                for case in cases
            )
        )

        self.assertEqual(len({variant["context_id"] for variant in variants}), 17)
        self.assertEqual(
            Counter(variant["event"] for variant in variants),
            Counter(
                {
                    "pull_request": 72,
                    "workflow_dispatch": 10,
                    "schedule": 10,
                    "push-tag-v4.30.0": 10,
                    "push": 5,
                    "merge_group": 4,
                }
            ),
        )
        self.assertEqual(
            Counter(variant["phase"] for variant in variants),
            Counter({"primary": 85, "rebootstrap": 26}),
        )
        self.assertEqual(
            Counter(variant["preset"] for variant in variants),
            Counter({"release": 97, "sanitize": 7, "reldebug": 7}),
        )
        self.assertEqual(
            Counter(variant["target_stage"] for variant in variants),
            Counter({"stage1": 111}),
        )

        selection_counts = {
            selection["selection_set_id"]: (
                selection["selected_count"],
                len(selection["provider_variant_ids"]),
            )
            for selection in selections
        }
        self.assertEqual(
            selection_counts,
            {
                "default-all": (3_678, 57),
                "default-filtered-aec7358564e4": (3_678, 8),
                "default-filtered-bfb0a7b69c6e": (3_677, 5),
                "default-filtered-d1bb9722e72c": (3_477, 5),
                "full-lake-all": (3_723, 28),
                "full-lake-filtered-6325d6cffd5d": (3_723, 4),
                "full-lake-filtered-cbb2894dd43f": (3_722, 2),
                "full-lake-filtered-d803b176baa6": (3_477, 2),
            },
        )
        selection_ids_by_content: dict[tuple[int, str], set[str]] = {}
        for selection in selections:
            key = (selection["selected_count"], selection["selected_ids_sha256"])
            selection_ids_by_content.setdefault(key, set()).add(
                selection["selection_set_id"]
            )
        self.assertEqual(len(selection_ids_by_content), 5)
        self.assertEqual(
            {
                frozenset(selection_ids)
                for selection_ids in selection_ids_by_content.values()
                if len(selection_ids) > 1
            },
            {
                frozenset(
                    {"default-all", "default-filtered-aec7358564e4"}
                ),
                frozenset(
                    {
                        "default-filtered-d1bb9722e72c",
                        "full-lake-filtered-d803b176baa6",
                    }
                ),
                frozenset(
                    {"full-lake-all", "full-lake-filtered-6325d6cffd5d"}
                ),
            },
        )

        merge_resolver = next(
            resolver
            for resolver in dependency["resolvers"]
            if resolver["id"] == "m2.7-variant-merge-v1"
        )
        self.assertEqual(merge_resolver["milestone"], "M2.7")
        self.assertEqual(merge_resolver["state"], "not-run")
        self.assertEqual(
            merge_resolver["edge_classes"],
            [
                "conditional-on-profile",
                "conditional-on-platform",
                "conditional-on-branch",
            ],
        )
        self.assertEqual(
            dependency["summary"]["provider_state_counts"], {"unbound": 111}
        )
        self.assertEqual(dependency["summary"]["nodes"], 0)
        self.assertEqual(dependency["summary"]["edges"], 0)
        self.assertEqual(dependency["summary"]["resolved_case_closures"], 0)
        self.assertEqual(dependency["summary"]["native_outcomes"], 0)
        self.assertEqual(dependency["summary"]["paired_cells"], 0)

    def test_m3_review_preregistration_remains_noncrediting(self) -> None:
        dependency = GEN.load_json(GEN.U2_NATIVE_DEPENDENCY)
        u2 = self.population("U2")

        self.assertEqual(len(dependency["case_rows"]), 3_723)
        self.assertEqual(len(dependency["provider_variants"]), 111)
        self.assertEqual(
            dependency["summary"]["case_variant_occurrences"], 408_374
        )
        self.assertEqual(
            dependency["summary"]["provider_state_counts"], {"unbound": 111}
        )
        self.assertEqual(dependency["summary"]["resolved_case_closures"], 0)
        self.assertEqual(dependency["summary"]["native_outcomes"], 0)
        self.assertEqual(dependency["summary"]["paired_cells"], 0)

        merge_resolver = next(
            resolver
            for resolver in dependency["resolvers"]
            if resolver["id"] == "m2.7-variant-merge-v1"
        )
        self.assertEqual(merge_resolver["state"], "not-run")
        self.assertEqual(u2["state"], "bounded_profile")
        self.assertIsNone(u2["raw_denominator"])
        self.assertIsNone(u2["normalized_denominator"])
        self.assertIsNone(u2["content_digest"])
        self.assertFalse(
            any(
                "m3" in evidence["path"].lower()
                and "result" in evidence["path"].lower()
                for evidence in u2["evidence"]
            )
        )

        self.assertEqual(
            sum(
                population["state"] == "complete_authority"
                for population in self.data["populations"]
            ),
            0,
        )
        self.assertEqual(
            sum(axis["state"] == "complete" for axis in self.data["axes"]), 0
        )
        self.assertEqual(len(self.data["paired_cells"]), 0)
        self.assertFalse(self.data["terminal_claim_enabled"])

    def test_committed_registry_is_valid_and_rendering_is_deterministic(self) -> None:
        self.assertEqual(self.failures(), [])
        first = GEN.build_report(self.data)
        second = GEN.build_report(copy.deepcopy(self.data))
        self.assertEqual(first, second)
        markdown = GEN.render_markdown(first)
        self.assertIn("complete Lean 4.30 parity not established", markdown)
        self.assertIn("Expected / registered terminal cells: **0 / 0**", markdown)
        self.assertFalse(first["terminal"]["ready"])
        self.assertEqual(first["bounded_snapshot"]["axiom_ledger"]["rows"], 65)
        self.assertEqual(
            first["bounded_snapshot"]["construct_matrix"]["independently_admitted"],
            6,
        )
        u2 = first["bounded_snapshot"]["u2_test_authority"]
        self.assertEqual(
            [(item["id"], item["registered"]) for item in u2["profiles"]],
            [("default", 3678), ("full-lake", 3723)],
        )
        official = first["bounded_snapshot"]["u2_official_execution_authority"]
        self.assertEqual(official["process_attempts"], 4)
        self.assertEqual(official["incomplete_process_attempts"], 2)
        self.assertEqual(official["official_outcomes"], 2)
        self.assertEqual(official["official_passes"], 1)
        self.assertEqual(official["official_failures"], 1)
        self.assertEqual(official["axeyum_outcomes"], 0)
        self.assertEqual(official["paired_cells"], 0)
        self.assertEqual(official["credits"]["parity_credit"], 0)
        m2 = first["bounded_snapshot"]["u2_m2_execution_contract"]
        self.assertEqual(m2["case_count"], 64)
        self.assertEqual(m2["first_case_id"], "compile/uint_fold.lean")
        self.assertEqual(m2["last_case_id"], "docparse/block_0004.txt")
        self.assertFalse(m2["live_execution_surface"])
        self.assertEqual(m2["official_outcomes"], 0)
        self.assertEqual(m2["parity_credit"], 0)
        self.assertEqual(m2["store"]["fixed_json"], 15)
        self.assertEqual(m2["store"]["fixed_raw"], 4)
        self.assertEqual(m2["store"]["case_records"], 64)
        self.assertTrue(m2["runner"]["run_command_exposed"])
        self.assertFalse(m2["runner"]["live_execution_observed"])
        self.assertEqual(m2["r3_incomplete"]["terminal_class"], "wall-timeout")
        self.assertEqual(m2["r3_incomplete"]["files"], 17)
        self.assertEqual(m2["r3_incomplete"]["bytes"], 4_908_035)
        self.assertEqual(m2["r3_incomplete"]["official_outcomes"], 0)
        self.assertEqual(m2["r3_incomplete"]["parity_credit"], 0)
        self.assertEqual(u2["outcomes"]["paired_registered"], 0)
        u2_ci = first["bounded_snapshot"]["u2_ci_profile_authority"]
        self.assertEqual(u2_ci["derivation"]["contexts"], 17)
        self.assertEqual(u2_ci["derivation"]["candidate_cells"], 153)
        self.assertEqual(u2_ci["derivation"]["ctest_attempts"], 111)
        self.assertEqual(u2_ci["derivation"]["selection_sets"], 8)
        self.assertEqual(u2_ci["outcomes"]["official_executed_attempts"], 0)
        u2_shards = first["bounded_snapshot"]["u2_child_shard_authority"]
        self.assertEqual(u2_shards["status"], "complete-derivation-not-run")
        self.assertEqual(u2_shards["summary"]["distinct_membership_plans"], 5)
        self.assertEqual(u2_shards["summary"]["physical_child_shards"], 289)
        self.assertEqual(
            u2_shards["summary"]["selection_expanded_shard_occurrences"], 461
        )
        self.assertEqual(
            u2_shards["summary"]["attempt_expanded_shard_occurrences"], 6451
        )
        self.assertTrue(u2_shards["claims"]["parent_memberships_partitioned"])
        self.assertFalse(u2_shards["claims"]["official_execution_complete"])
        self.assertTrue(all(value == 0 for value in u2_shards["credits"].values()))
        u2_surfaces = first["bounded_snapshot"]["u2_native_surface_authority"]
        self.assertEqual(
            u2_surfaces["status"],
            "complete-harness-floor-content-and-dependencies-not-run",
        )
        self.assertEqual(u2_surfaces["summary"]["registration_cases"], 3723)
        self.assertEqual(
            u2_surfaces["summary"]["classification_state_counts"],
            {"harness-floor": 3723},
        )
        self.assertEqual(
            u2_surfaces["summary"]["content_refinement_counts"],
            {"not-run": 3723},
        )
        self.assertEqual(
            u2_surfaces["summary"]["module_dependency_closure_counts"],
            {"not-run": 3723},
        )
        self.assertEqual(u2_surfaces["credits"]["paired_cells"], 0)
        self.assertEqual(u2_surfaces["credits"]["parity_credit"], 0)
        self.assertFalse(u2_surfaces["claims"]["pinned_content_refined"])
        u2_content = first["bounded_snapshot"]["u2_native_content_authority"]
        self.assertEqual(
            u2_content["status"],
            "complete-tracked-content-census-dependency-closure-not-run",
        )
        self.assertEqual(u2_content["summary"]["tracked_content_files"], 7004)
        self.assertEqual(u2_content["summary"]["registration_cases"], 3723)
        self.assertEqual(u2_content["summary"]["signal_hits"], 90909)
        self.assertEqual(
            u2_content["summary"]["cases_with_generated_wrapper_residual"],
            3670,
        )
        self.assertEqual(
            u2_content["summary"]["content_refinement_counts"],
            {"complete-census": 3723},
        )
        self.assertEqual(
            u2_content["summary"]["module_dependency_closure_counts"],
            {"not-run": 3723},
        )
        self.assertTrue(u2_content["claims"]["content_signal_census_complete"])
        self.assertFalse(u2_content["claims"]["module_dependency_closure_complete"])
        self.assertTrue(all(value == 0 for value in u2_content["credits"].values()))
        execution = first["bounded_snapshot"]["execution_evidence_authority"]
        self.assertEqual(execution["lane_policies"], 2)
        self.assertEqual(execution["termination_classes"], 12)
        self.assertEqual(execution["synthetic_controls"], 5)
        self.assertEqual(execution["mutation_classes"], 19)
        self.assertTrue(execution["all_synthetic_controls_valid"])
        self.assertEqual(execution["observed"]["real_runs"], 0)
        process = first["bounded_snapshot"]["execution_process_authority"]
        self.assertEqual(process["registered_controls"], 8)
        self.assertEqual(process["retained_process_attempts"], 8)
        self.assertEqual(process["classification_counts"], {
            "exited": 2,
            "signaled": 1,
            "wall-timeout": 1,
            "memory-limit": 2,
            "launch-failed": 1,
            "preflight-invalid": 1,
        })
        self.assertEqual(process["retained_files"], 40)
        self.assertEqual(process["raw_artifacts"], 16)
        self.assertEqual(process["case_records"], 0)
        self.assertEqual(process["completion_records"], 0)
        self.assertTrue(all(value == 0 for value in process["credits"].values()))
        store = first["bounded_snapshot"]["execution_store_authority"]
        self.assertEqual(store["storage_classes"], 2)
        self.assertEqual(store["kill_cells"], 16)
        self.assertEqual(store["sigkill_cells"], 16)
        self.assertEqual(store["projection_equal_cells"], 16)
        self.assertEqual(store["evidence_files"], 65)
        self.assertEqual(store["real_outcomes"], 0)
        self.assertEqual(store["completed_u2_cases"], 0)
        self.assertEqual(store["paired_cells"], 0)
        self.assertEqual(store["performance_rows"], 0)
        self.assertEqual(store["parity_credit"], 0)
        self.assertTrue(store["claims"]["process_sigkill_recovery"])
        self.assertFalse(store["claims"]["power_loss_recovery"])
        acceptance = first["bounded_snapshot"]["execution_acceptance_authority"]
        self.assertEqual(acceptance["status"], "accepted-no-credit-real-controls")
        self.assertEqual(acceptance["observed_external_process_attempts"], 3)
        self.assertEqual(acceptance["failed_external_process_attempts"], 1)
        self.assertEqual(acceptance["completed_external_controls"], 2)
        self.assertEqual(acceptance["retained_files"], 67)
        self.assertEqual(acceptance["retained_bytes"], 142523)
        self.assertEqual(acceptance["u2_cases"], 0)
        self.assertEqual(acceptance["official_outcomes"], 0)
        self.assertEqual(acceptance["axeyum_outcomes"], 0)
        self.assertEqual(acceptance["paired_cells"], 0)
        self.assertEqual(acceptance["performance_rows"], 0)
        self.assertTrue(acceptance["claims"]["real_process_controls"])
        self.assertFalse(acceptance["claims"]["official_u2_execution"])
        self.assertTrue(all(value == 0 for value in acceptance["credits"].values()))
        source_paths = {item["path"] for item in first["source_identities"]}
        self.assertIn(".github/workflows/ci.yml", source_paths)
        self.assertIn(
            "docs/plan/lean4-complete-parity-contract-2026-07-22.md", source_paths
        )
        self.assertIn("scripts/gen-lean-complete-parity.py", source_paths)
        self.assertIn("docs/plan/lean-u2-test-authority-v1.json", source_paths)
        self.assertIn("docs/plan/lean-u2-official-ci-profiles-v1.json", source_paths)
        self.assertIn("docs/plan/lean-u2-official-child-shards-v1.json", source_paths)
        self.assertIn("scripts/gen-lean-u2-official-child-shards.py", source_paths)
        self.assertIn(
            "docs/plan/lean-u2-native-surface-classification-v1.json",
            source_paths,
        )
        self.assertIn(
            "scripts/gen-lean-u2-native-surface-classification.py",
            source_paths,
        )
        self.assertIn(
            "docs/plan/lean-u2-native-surface-content-v1.json",
            source_paths,
        )
        self.assertIn(
            "scripts/gen-lean-u2-native-surface-content.py",
            source_paths,
        )
        dependency = first["bounded_snapshot"]["u2_native_dependency_authority"]
        self.assertEqual(dependency["summary"]["registration_cases"], 3723)
        self.assertEqual(dependency["summary"]["provider_variants"], 111)
        self.assertEqual(dependency["summary"]["case_variant_occurrences"], 408374)
        self.assertEqual(dependency["summary"]["nodes"], 0)
        self.assertEqual(dependency["summary"]["edges"], 0)
        self.assertEqual(dependency["summary"]["resolved_case_closures"], 0)
        self.assertFalse(dependency["claims"]["provider_identity_bound"])
        self.assertFalse(dependency["claims"]["lean_parity_established"])
        self.assertTrue(all(value == 0 for value in dependency["credits"].values()))
        self.assertIn(
            "docs/plan/lean-u2-native-dependency-v1.json",
            source_paths,
        )
        self.assertIn(
            "scripts/gen-lean-u2-native-dependency.py",
            source_paths,
        )
        header = first["bounded_snapshot"]["u2_native_header_contract_authority"]
        self.assertEqual(header["summary"]["corpus_rows"], 4092)
        self.assertEqual(header["summary"]["corpus_bytes"], 9_697_571)
        self.assertEqual(header["summary"]["batches"], 32)
        self.assertEqual(header["summary"]["controls"], 14)
        self.assertEqual(header["summary"]["planned_processes"], 39)
        self.assertEqual(header["summary"]["observed_processes"], 0)
        self.assertEqual(header["summary"]["declared_header_edges"], 0)
        self.assertFalse(header["claims"]["fast_parser_observed"])
        self.assertFalse(header["claims"]["header_declarations_complete"])
        self.assertTrue(all(value == 0 for value in header["credits"].values()))
        normalization = first["bounded_snapshot"][
            "u2_normalization_contract_authority"
        ]
        self.assertEqual(normalization["status"], "bounded-contract-only")
        self.assertEqual(normalization["summary"]["contracts"], 9)
        self.assertEqual(normalization["summary"]["compared_fields"], 68)
        self.assertEqual(normalization["summary"]["ignored_rules"], 18)
        self.assertEqual(normalization["summary"]["raw_extractors_implemented"], 0)
        self.assertEqual(
            normalization["summary"]["semantic_canonicalizers_implemented"], 0
        )
        self.assertFalse(normalization["claims"]["parents_complete"])
        self.assertFalse(normalization["claims"]["lean_complete_parity"])
        self.assertIn(
            "docs/plan/lean-u2-normalization-contracts-v1.json",
            source_paths,
        )
        self.assertIn("scripts/lean_u2_normalization_contracts.py", source_paths)
        self.assertIn(
            "docs/plan/lean-u2-matched-execution-tl0.6.5-normalization-r3-result-2026-07-23.md",
            source_paths,
        )
        self.assertIn(
            "docs/plan/lean-u2-native-header-contract-m2.1-v1.json",
            source_paths,
        )
        self.assertIn(
            "docs/plan/lean-u2-native-dependency-tl0.6.4-m2.3-runner-generated-plan-2026-07-23.md",
            source_paths,
        )
        self.assertIn(
            "docs/plan/lean-u2-native-dependency-tl0.6.4-m2.4-lake-project-plan-2026-07-23.md",
            source_paths,
        )
        self.assertIn(
            "docs/plan/lean-u2-native-dependency-tl0.6.4-m2.5-compiler-runtime-ffi-plan-2026-07-23.md",
            source_paths,
        )
        self.assertIn(
            "docs/plan/lean-complete-parity-worktree-portability-r1-result-2026-07-23.md",
            source_paths,
        )
        self.assertIn(
            "scripts/lean_u2_native_dependency_m2_1.py",
            source_paths,
        )
        self.assertIn(
            "scripts/lean_u2_header_full_parser.lean",
            source_paths,
        )
        self.assertIn("docs/plan/lean-execution-evidence-v1.json", source_paths)
        self.assertIn("docs/plan/lean-execution-process-v1.json", source_paths)
        self.assertIn("docs/plan/lean-execution-store-v1.json", source_paths)
        self.assertIn("docs/plan/lean-execution-acceptance-v1.json", source_paths)
        self.assertIn("scripts/lean_execution_acceptance.py", source_paths)
        self.assertIn(
            "docs/plan/lean-u2-official-execution-tl0.6.3-m0-r3-v1.json",
            source_paths,
        )
        self.assertIn("scripts/lean_u2_official_execution.py", source_paths)
        self.assertIn("scripts/lean_u2_official_execution_r3_result.py", source_paths)
        self.assertIn("scripts/lean_u2_official_execution_m2.py", source_paths)
        self.assertIn(
            "scripts/tests/test_lean_u2_official_execution_m2.py", source_paths
        )
        self.assertIn("scripts/lean_u2_official_execution_m2_store.py", source_paths)
        self.assertIn(
            "scripts/tests/test_lean_u2_official_execution_m2_store.py",
            source_paths,
        )
        self.assertIn("scripts/lean_u2_official_execution_m2_run.py", source_paths)
        self.assertIn(
            "scripts/tests/test_lean_u2_official_execution_m2_run.py",
            source_paths,
        )
        self.assertIn("scripts/lean_u2_official_execution_m2_r2.py", source_paths)
        self.assertIn(
            "scripts/tests/test_lean_u2_official_execution_m2_r2.py", source_paths
        )
        self.assertIn("scripts/lean_u2_official_execution_m2_r3.py", source_paths)
        self.assertIn(
            "scripts/tests/test_lean_u2_official_execution_m2_r3.py", source_paths
        )
        self.assertIn("scripts/lean_u2_official_execution_m2_r4.py", source_paths)
        self.assertIn(
            "scripts/tests/test_lean_u2_official_execution_m2_r4.py", source_paths
        )
        self.assertIn("scripts/lean_u2_official_execution_m2_r5.py", source_paths)
        self.assertIn(
            "scripts/tests/test_lean_u2_official_execution_m2_r5.py", source_paths
        )
        self.assertIn(
            "scripts/lean_u2_official_execution_m2_r5_diagnostic.py", source_paths
        )
        self.assertIn(
            "scripts/tests/test_lean_u2_official_execution_m2_r5_diagnostic.py",
            source_paths,
        )
        self.assertIn("scripts/lean_u2_official_execution_m2_r6.py", source_paths)
        self.assertIn(
            "scripts/tests/test_lean_u2_official_execution_m2_r6.py", source_paths
        )
        self.assertIn(
            "scripts/lean_u2_official_execution_m2_r6_result.py", source_paths
        )
        self.assertIn(
            "scripts/tests/test_lean_u2_official_execution_m2_r6_result.py",
            source_paths,
        )
        self.assertIn(
            "docs/plan/lean-u2-official-execution-tl0.6.3-m2-r6-v1.json",
            source_paths,
        )
        self.assertIn(
            "docs/plan/lean-u2-official-execution-tl0.6.3-m2-r1-result-v1.json",
            source_paths,
        )
        self.assertIn(
            "docs/plan/lean-u2-official-execution-tl0.6.3-m2-r1-result-2026-07-22.md",
            source_paths,
        )

    def test_u2_registration_is_bounded_not_terminal_authority(self) -> None:
        population = self.population("U2")
        self.assertEqual(population["state"], "bounded_profile")
        self.assertIsNone(population["raw_denominator"])
        self.assertIsNone(population["normalized_denominator"])
        self.assertIsNone(population["content_digest"])
        self.assertIn(
            "All 111 full official workflow attempts",
            population["residual"],
        )
        self.assertIn(
            "Current credited local execution coverage is 66 official outcomes",
            population["residual"],
        )

    def test_population_order_and_incomplete_denominators_are_fail_closed(self) -> None:
        self.data["populations"][0], self.data["populations"][1] = (
            self.data["populations"][1],
            self.data["populations"][0],
        )
        self.assertTrue(any("population ids/order" in failure for failure in self.failures()))

        self.data = GEN.load_manifest()
        self.population("U1")["raw_denominator"] = 12
        self.assertTrue(
            any("cannot publish terminal denominators" in failure for failure in self.failures())
        )

    def test_complete_population_requires_both_denominators_and_digest(self) -> None:
        population = self.population("U1")
        population["state"] = "complete_authority"
        self.assertTrue(
            any("needs raw denominator" in failure for failure in self.failures())
        )
        self.assertTrue(
            any("needs normalized denominator" in failure for failure in self.failures())
        )
        self.assertTrue(any("needs content digest" in failure for failure in self.failures()))

    def test_axis_credit_requires_evidence_and_complete_dependencies(self) -> None:
        self.axis("A3")["state"] = "partial"
        self.assertTrue(
            any(
                "A3: retained evidence is required" in failure
                for failure in self.failures()
            )
        )

        self.data = GEN.load_manifest()
        self.axis("A1")["populations"] = ["U1"]
        self.assertTrue(
            any("population dependencies must match" in failure for failure in self.failures())
        )

        self.data = GEN.load_manifest()
        self.axis("A1")["state"] = "complete"
        self.assertTrue(
            any(
                "complete axis depends on incomplete populations" in failure
                for failure in self.failures()
            )
        )

    def test_derived_gates_and_claim_switch_cannot_be_hand_promoted(self) -> None:
        self.gate("G1")["state"] = "satisfied"
        self.assertTrue(
            any(
                "G1: state disagrees with derived registry evidence" in failure
                for failure in self.failures()
            )
        )

        self.data = GEN.load_manifest()
        self.data["terminal_claim_enabled"] = True
        self.assertTrue(
            any(
                "terminal_claim_enabled must exactly equal" in failure
                for failure in self.failures()
            )
        )

        self.data = GEN.load_manifest()
        self.gate("G4")["state"] = "satisfied"
        self.assertTrue(
            any(
                "G4: retained evidence is required" in failure
                for failure in self.failures()
            )
        )

    def test_paired_taxonomy_and_cells_require_exact_identity(self) -> None:
        self.assertEqual(
            {"official", "axeyum", "comparison"} & GEN.PAIRED_CELL_FIELDS,
            {"official", "axeyum", "comparison"},
        )
        self.assertNotIn("command_sha256", GEN.PAIRED_CELL_FIELDS)
        self.assertIn("command_sha256", GEN.PAIRED_EXECUTION_FIELDS)
        self.assertIn("attempt_id", GEN.PAIRED_EXECUTION_FIELDS)
        self.assertIn("record_sha256", GEN.PAIRED_EXECUTION_FIELDS)
        self.assertIn("result_class", GEN.PAIRED_EXECUTION_FIELDS)
        self.assertIn("cell_sha256", GEN.PAIRED_CELL_FIELDS)
        self.assertIn("official_record_sha256", GEN.PAIRED_COMPARISON_FIELDS)
        self.assertIn("axeyum_record_sha256", GEN.PAIRED_COMPARISON_FIELDS)
        self.assertIn("official_normalized_sha256", GEN.PAIRED_COMPARISON_FIELDS)
        self.assertIn("axeyum_normalized_sha256", GEN.PAIRED_COMPARISON_FIELDS)
        self.assertIn("completed", GEN.PAIRED_COMPARISON_FIELDS)
        self.data["outcome_classes"][-1] = "other"
        self.assertTrue(any("outcome_classes/order" in failure for failure in self.failures()))

        self.data = GEN.load_manifest()
        cell = self.paired_cell()
        cell["source_sha256"] = "bad"
        cell["dependency_sha256"] = "bad"
        cell["official"]["evidence"] = []
        self.register_bounded_pair(cell)
        failures = self.failures()
        self.assertTrue(any("source_sha256 must be" in failure for failure in failures))
        self.assertTrue(any("dependency_sha256 must be" in failure for failure in failures))
        self.assertTrue(
            any(
                "bounded-probe.official: retained evidence" in failure
                for failure in failures
            )
        )

    def test_valid_bounded_pair_has_independent_execution_records(self) -> None:
        cell = self.paired_cell()
        self.register_bounded_pair(cell)
        self.assertEqual(self.failures(), [])
        self.assertNotEqual(
            cell["official"]["command_sha256"], cell["axeyum"]["command_sha256"]
        )

        cell["official"]["command_sha256"] = None
        self.assertTrue(
            any(
                "complete execution requires command_sha256" in failure
                for failure in self.failures()
            )
        )
        self.assertTrue(
            any(
                "record_sha256 must match canonical execution" in failure
                for failure in self.failures()
            )
        )

    def test_paired_seals_bind_both_executions_comparison_and_cell(self) -> None:
        cell = self.paired_cell()
        self.register_bounded_pair(cell)

        cell["official"]["command_sha256"] = "9" * 64
        failures = self.failures()
        self.assertTrue(
            any("record_sha256 must match canonical execution" in failure for failure in failures)
        )

        self.data = GEN.load_manifest()
        cell = self.paired_cell()
        self.register_bounded_pair(cell)
        cell["comparison"]["official_record_sha256"] = "9" * 64
        failures = self.failures()
        self.assertTrue(
            any("official record seal must match cited execution" in failure for failure in failures)
        )
        self.assertTrue(
            any("result_sha256 must match canonical comparison" in failure for failure in failures)
        )

        self.data = GEN.load_manifest()
        cell = self.paired_cell()
        self.register_bounded_pair(cell)
        cell["comparison"]["normalization_sha256"] = "9" * 64
        failures = self.failures()
        self.assertTrue(
            any("result_sha256 must match canonical comparison" in failure for failure in failures)
        )

        self.data = GEN.load_manifest()
        cell = self.paired_cell()
        self.register_bounded_pair(cell)
        cell["profile_id"] = "changed-profile"
        self.assertTrue(
            any("cell_sha256 must match canonical cell" in failure for failure in self.failures())
        )

    def test_paired_normalizer_must_be_registered_layer_matched_and_current(self) -> None:
        cell = self.paired_cell()
        self.register_bounded_pair(cell)
        cell["comparison"]["normalization_id"] = "invented-normalizer-v1"
        self.reseal_pair(cell)
        self.assertTrue(
            any("is not registered" in failure for failure in self.failures())
        )

        self.data = GEN.load_manifest()
        cell = self.paired_cell()
        self.register_bounded_pair(cell)
        cell["layer"] = "parser-macro"
        self.reseal_pair(cell)
        self.assertTrue(
            any("must match normalization layer" in failure for failure in self.failures())
        )

        self.data = GEN.load_manifest()
        cell = self.paired_cell()
        self.register_bounded_pair(cell)
        cell["comparison"]["normalization_sha256"] = "9" * 64
        self.reseal_pair(cell)
        self.assertTrue(
            any(
                "normalization_sha256 must match registered contract" in failure
                for failure in self.failures()
            )
        )

    def test_paired_authority_binds_resealed_cell_content(self) -> None:
        cell = self.paired_cell()
        self.register_bounded_pair(cell)
        cell["profile_id"] = "changed-profile"
        cell["cell_sha256"] = GEN.paired_cell_digest(cell)
        failures = self.failures()
        self.assertFalse(any("cell_sha256 must match canonical cell" in failure for failure in failures))
        self.assertTrue(
            any("registered cell-seal digest must match authority" in failure for failure in failures)
        )

    def test_paired_outcome_requires_coherent_side_states(self) -> None:
        self.register_bounded_pair(
            self.paired_cell(axeyum_state="not-run", outcome="agree-success")
        )
        self.assertTrue(
            any(
                "must equal derived 'not-run'" in failure
                for failure in self.failures()
            )
        )

        self.data = GEN.load_manifest()
        self.register_bounded_pair(self.paired_cell(outcome="not-run"))
        self.assertTrue(
            any(
                "must equal derived 'agree-success'" in failure
                for failure in self.failures()
            )
        )

        self.data = GEN.load_manifest()
        self.register_bounded_pair(self.paired_cell(outcome="invalid-run"))
        self.assertTrue(
            any(
                "must equal derived 'agree-success'" in failure
                for failure in self.failures()
            )
        )

    def test_all_paired_outcomes_are_derived(self) -> None:
        rows = (
            ("agree-success", {}),
            (
                "agree-reject",
                {"official_result": "reject", "axeyum_result": "reject"},
            ),
            (
                "official-only",
                {
                    "official_result": "success",
                    "axeyum_result": "decline",
                    "axeyum_normalized": None,
                },
            ),
            (
                "axeyum-only",
                {"official_result": "reject", "axeyum_result": "success"},
            ),
            (
                "semantic-mismatch",
                {"axeyum_normalized": "3" * 64},
            ),
            (
                "unadjudicated",
                {"axeyum_normalized": None},
            ),
            (
                "not-run",
                {"axeyum_state": "not-run", "axeyum_normalized": None},
            ),
            (
                "invalid-run",
                {"axeyum_state": "invalid", "axeyum_normalized": None},
            ),
        )
        for outcome, arguments in rows:
            with self.subTest(outcome=outcome):
                self.data = GEN.load_manifest()
                self.register_bounded_pair(
                    self.paired_cell(outcome=outcome, **arguments)
                )
                self.assertEqual(self.failures(), [])

    def test_resealed_semantic_mutations_reject_stale_outcome(self) -> None:
        cell = self.paired_cell()
        self.register_bounded_pair(cell)
        cell["comparison"]["axeyum_normalized_sha256"] = "3" * 64
        self.reseal_pair(cell)
        self.assertTrue(
            any(
                "must equal derived 'semantic-mismatch'" in failure
                for failure in self.failures()
            )
        )

        self.data = GEN.load_manifest()
        cell = self.paired_cell()
        self.register_bounded_pair(cell)
        cell["axeyum"]["result_class"] = "decline"
        self.reseal_pair(cell)
        self.assertTrue(
            any(
                "must equal derived 'official-only'" in failure
                for failure in self.failures()
            )
        )

        self.data = GEN.load_manifest()
        cell = self.paired_cell()
        self.register_bounded_pair(cell)
        cell["comparison"]["axeyum_normalized_sha256"] = None
        self.reseal_pair(cell)
        self.assertTrue(
            any(
                "must equal derived 'unadjudicated'" in failure
                for failure in self.failures()
            )
        )

    def test_noncomplete_side_rejects_result_and_normalized_identity(self) -> None:
        cell = self.paired_cell(
            outcome="not-run",
            axeyum_state="not-run",
            axeyum_normalized=None,
        )
        self.register_bounded_pair(cell)
        cell["axeyum"]["result_class"] = "success"
        cell["comparison"]["axeyum_normalized_sha256"] = "3" * 64
        self.reseal_pair(cell)
        failures = self.failures()
        self.assertTrue(
            any("non-complete execution requires null result_class" in failure for failure in failures)
        )
        self.assertTrue(
            any("non-complete axeyum side requires null" in failure for failure in failures)
        )

    def test_paired_authority_blocks_subset_and_digest_vacuity(self) -> None:
        self.register_bounded_pair(self.paired_cell())
        self.gate("G3")["state"] = "satisfied"
        self.gate("G3")["evidence"] = self.retained_evidence()
        self.assertTrue(
            any(
                "G3: state disagrees with derived registry evidence" in failure
                for failure in self.failures()
            )
        )

        self.data = GEN.load_manifest()
        self.register_bounded_pair(self.paired_cell())
        self.paired_authority("U1")["expected_ids_sha256"] = "0" * 64
        self.assertTrue(
            any(
                "registered cell ID digest must match authority" in failure
                for failure in self.failures()
            )
        )

        self.data = GEN.load_manifest()
        self.register_bounded_pair(self.paired_cell())
        self.paired_authority("U1")["expected_cell_seals_sha256"] = "0" * 64
        self.assertTrue(
            any(
                "registered cell-seal digest must match authority" in failure
                for failure in self.failures()
            )
        )

    def test_claim_detector_rejects_affirmative_claims_only(self) -> None:
        self.assertEqual(
            GEN.find_forbidden_claims("Axeyum has complete Lean 4.30 parity."),
            [(1, "Axeyum has complete Lean 4.30 parity")],
        )
        self.assertTrue(GEN.find_forbidden_claims("We have reached 100% Lean 4 parity."))
        self.assertTrue(
            GEN.find_forbidden_claims("Axeyum has **full** Lean 4 compatibility.")
        )
        self.assertTrue(GEN.find_forbidden_claims("Lean 4 parity is complete."))
        self.assertEqual(
            GEN.find_forbidden_claims("Axeyum does not have complete Lean 4 parity."),
            [],
        )
        self.assertEqual(
            GEN.find_forbidden_claims("Complete Lean 4 parity is a long-term target."),
            [],
        )

    def test_missing_evidence_path_is_rejected(self) -> None:
        self.population("U1")["evidence"][0]["path"] = "docs/plan/does-not-exist.json"
        self.assertTrue(any("missing evidence path" in failure for failure in self.failures()))


if __name__ == "__main__":
    unittest.main()
