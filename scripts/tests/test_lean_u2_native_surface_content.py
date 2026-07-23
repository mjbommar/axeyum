from __future__ import annotations

import copy
import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "gen_lean_u2_native_surface_content",
    ROOT / "scripts/gen-lean-u2-native-surface-content.py",
)
assert SPEC and SPEC.loader
GEN = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GEN
SPEC.loader.exec_module(GEN)


class LeanU2NativeSurfaceContentScannerTests(unittest.TestCase):
    def ids(self, data: bytes, path: str = "control.lean") -> set[str]:
        _, _, hits = GEN.scan_content(path, "100644", data)
        return {hit["signal_id"] for hit in hits}

    def test_lean_active_tokens_are_found(self) -> None:
        ids = self.ids(
            b"""
import Lean
syntax "x" : term
macro "m" : term => `(by exact 1)
theorem t : True := by trivial
#eval 1
@[extern "native_f"] opaque nativeF : Nat
def m := Lean.Meta.mkFreshExprMVar
"""
        )
        self.assertTrue(
            {
                "lean.import-command",
                "lean.syntax-declaration",
                "lean.syntax-quotation",
                "lean.declaration",
                "lean.tactic-block",
                "lean.evaluation-command",
                "lean.ffi-declaration",
                "lean.meta-api",
            }.issubset(ids)
        )

    def test_nested_comments_strings_near_identifiers_and_quotation_are_not_tokens(self) -> None:
        ids = self.ids(
            b"""
-- syntax macro by extern Lean.Meta #eval
/- macro /- by extern -/ Lean.Meta -/
def mySyntax := "syntax macro by extern Lean.Meta #eval"
def somebody := 1
def q := `(theorem fake : True := by exact True.intro)
"""
        )
        self.assertEqual(ids, {"lean.declaration", "lean.syntax-quotation"})

    def test_structured_json_requires_parse_and_string_method(self) -> None:
        ids = self.ids(
            b'{"jsonrpc":"2.0","method":"textDocument/hover","params":{"version":3}}',
            "request.json",
        )
        self.assertIn("json.rpc-method", ids)
        self.assertIn("json.document-version", ids)
        malformed = self.ids(b'{"method":"textDocument/hover"', "request.json")
        self.assertEqual(malformed, set())
        nonstring = self.ids(b'{"method":7}', "request.json")
        self.assertNotIn("json.rpc-method", nonstring)

    def test_structured_toml_fields_and_native_link_fields(self) -> None:
        ids = self.ids(
            b'name = "demo"\n[[lean_lib]]\nname = "Demo"\nmore_link_args = ["-lm"]\n',
            "lakefile.toml",
        )
        self.assertIn("toml.project-field", ids)
        self.assertIn("toml.native-link-field", ids)

    def test_shell_comment_and_quotes_do_not_become_candidates(self) -> None:
        ids = self.ids(
            b'# lean lake leanc plugin\necho "lean lake plugin"\nactual=1\n',
            "run_test.sh",
        )
        self.assertNotIn("shell.tool-command", ids)
        self.assertNotIn("shell.native-link-candidate", ids)
        active = self.ids(b"lake build\nleanc -o out in.c\n", "run_test.sh")
        self.assertIn("shell.tool-command", active)
        self.assertIn("shell.native-link-candidate", active)

    def test_c_comments_and_strings_do_not_become_abi_evidence(self) -> None:
        ids = self.ids(
            b'// extern lean_object\nconst char *s = "extern dlopen LEAN_EXPORT";\nint x;\n',
            "ffi.c",
        )
        self.assertNotIn("c.abi-declaration", ids)
        active = self.ids(b"extern lean_object *f(void);\n", "ffi.c")
        self.assertIn("c.abi-declaration", active)

    def test_source_paths_and_scope_prefixes_are_fail_closed(self) -> None:
        self.assertTrue(GEN.safe_relative("tests/elab/a.lean"))
        self.assertFalse(GEN.safe_relative("../tests/elab/a.lean"))
        self.assertFalse(GEN.safe_relative("/tests/elab/a.lean"))
        self.assertTrue(GEN.within_scope("tests/elab/a.lean", "tests/elab"))
        self.assertFalse(GEN.within_scope("tests/elab_extra/a.lean", "tests/elab"))

    def test_generated_wrapper_is_inventoried_not_substituted(self) -> None:
        u2, _, _ = GEN.validate_frozen_inputs()
        paths = [row["path"] for row in u2["content_files"]]
        case = next(row for row in u2["cases"] if row["family"] == "elab")
        projection = GEN.derive_case_files(case, paths)
        self.assertEqual(
            projection["generated_references"],
            ["tests/with_stage1_test_env.sh"],
        )
        self.assertNotIn("tests/with_env.sh.in", projection["wrappers"])
        self.assertNotIn("tests/with_stage1_test_env.sh", paths)

    def test_role_projection_is_complete_and_deterministic(self) -> None:
        u2, _, _ = GEN.validate_frozen_inputs()
        paths = [row["path"] for row in u2["content_files"]]
        roles, projections = GEN.derive_roles(u2, paths)
        self.assertEqual(len(roles), 7004)
        self.assertEqual(len(projections), 3723)
        self.assertEqual(sum(bool(row["hooks"]) for row in projections), 33)
        self.assertEqual(sum(bool(row["generated_references"]) for row in projections), 3670)
        self.assertEqual(
            roles["tests/with_env.sh.in"],
            ["registration-wrapper-template", "shared-support"],
        )


@unittest.skipUnless(GEN.MANIFEST.is_file(), "M1 authority not derived yet")
class LeanU2NativeSurfaceContentAuthorityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.data = GEN.load_json(GEN.MANIFEST)

    def failures(self) -> list[str]:
        return GEN.validate_authority(self.data)

    def reseal_top(self) -> None:
        self.data["record_sha256"] = GEN.domain_digest(
            GEN.SCHEMA,
            {key: value for key, value in self.data.items() if key != "record_sha256"},
        )

    def reseal_file_rows(self) -> None:
        self.data["file_rows_sha256"] = GEN.domain_digest(
            "axeyum-lean-u2-native-content-files-v1", self.data["file_rows"]
        )
        self.reseal_top()

    def reseal_case_rows(self) -> None:
        self.data["case_rows_sha256"] = GEN.domain_digest(
            "axeyum-lean-u2-native-content-cases-v1", self.data["case_rows"]
        )
        self.reseal_top()

    def test_committed_authority_is_valid_and_non_crediting(self) -> None:
        self.assertEqual(self.failures(), [])
        summary = self.data["summary"]
        self.assertEqual(summary["tracked_content_files"], 7004)
        self.assertEqual(summary["registration_cases"], 3723)
        self.assertEqual(summary["content_refinement_counts"], {"complete-census": 3723})
        self.assertEqual(summary["module_dependency_closure_counts"], {"not-run": 3723})
        self.assertEqual(summary["native_outcome_counts"], {"not-run": 3723})
        self.assertTrue(all(value == 0 for value in self.data["credits"].values()))

    def test_file_hit_signal_and_role_mutations_are_rejected(self) -> None:
        row = next(row for row in self.data["file_rows"] if row["signal_hits"])
        row["roles"] = ["unreferenced-content"]
        hit = row["signal_hits"][0]
        hit["surface_effect"] = ["ffi"]
        row["signal_hits"][0] = hit
        row["signal_hits_sha256"] = GEN.domain_digest(
            "axeyum-lean-u2-native-content-file-hits-v1", row["signal_hits"]
        )
        row.update(GEN.seal(row, GEN.FILE_DOMAIN))
        self.reseal_file_rows()
        failures = self.failures()
        self.assertTrue(any("role projection drift" in item for item in failures))
        self.assertTrue(any("signal semantic drift" in item for item in failures))

    def test_shared_evidence_and_m0_floor_removal_are_rejected(self) -> None:
        row = next(row for row in self.data["case_rows"] if row["signal_evidence"])
        evidence = row["signal_evidence"][0]
        evidence["path"] = "tests/util.sh"
        evidence["hit_index"] = 10**9
        row["signal_evidence_sha256"] = GEN.domain_digest(
            "axeyum-lean-u2-native-content-case-evidence-v1", row["signal_evidence"]
        )
        row["m0_direct_surfaces"] = []
        row["direct_surfaces"] = []
        row.update(GEN.seal(row, GEN.CASE_DOMAIN))
        self.reseal_case_rows()
        failures = self.failures()
        self.assertTrue(any("evidence index" in item or "shared/sidecar/runner" in item for item in failures))
        self.assertTrue(any("M0 floor" in item for item in failures))

    def test_generated_residual_and_credit_mutations_are_rejected(self) -> None:
        row = next(row for row in self.data["case_rows"] if row["generated_residuals"])
        row["generated_residuals"] = []
        row["native_outcome"] = "passed"
        row["pairing_credit"] = 1
        row.update(GEN.seal(row, GEN.CASE_DOMAIN))
        self.data["credits"]["paired_cells"] = 1
        self.reseal_case_rows()
        failures = self.failures()
        self.assertTrue(any("generated-wrapper residual drift" in item for item in failures))
        self.assertTrue(any("non-crediting state drift" in item for item in failures))
        self.assertTrue(any("credits drift" in item for item in failures))

    def test_summary_list_and_top_level_seals_have_teeth(self) -> None:
        self.data["summary"]["tracked_content_files"] = 7003
        self.data["file_rows_sha256"] = "0" * 64
        self.data["record_sha256"] = "1" * 64
        failures = self.failures()
        self.assertTrue(any("summary drift" in item for item in failures))
        self.assertTrue(any("file row list seal drift" in item for item in failures))
        self.assertTrue(any("top-level record seal drift" in item for item in failures))

    def test_wrong_source_root_fails_before_derivation(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(GEN.ContentError):
                GEN.build_authority(Path(directory))


if __name__ == "__main__":
    unittest.main()
