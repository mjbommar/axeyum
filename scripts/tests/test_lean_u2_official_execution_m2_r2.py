from __future__ import annotations

import copy
import shutil
import tempfile
import unittest
from pathlib import Path

from scripts import lean_u2_official_execution as BASE
from scripts import lean_u2_official_execution_m2 as M2
from scripts import lean_u2_official_execution_m2_r2 as R2


class LeanU2OfficialExecutionM2R2Tests(unittest.TestCase):
    def test_family_specific_paths_and_exact_work_projection(self) -> None:
        cases = {case["id"]: case for case in M2.selected_contract()["cases"]}
        self.assertEqual(
            R2.case_generated_paths(cases["docparse/arg_0006.txt"]),
            ["tests/docparse/arg_0006.txt.out.produced"],
        )
        self.assertEqual(
            R2.case_generated_paths(cases["compile_bench/identifier_completion.lean"]),
            ["tests/compile_bench/identifier_completion.lean.out.produced"],
        )
        projection = R2.capture_work_projection(R2.WORK_SOURCE, R2.EVIDENCE_ROOT)
        self.assertEqual(len(projection["full"]), 124)
        self.assertEqual(len(projection["retained"]), 67)
        self.assertEqual(len(projection["metadata"]), 56)
        self.assertEqual(sum(row["bytes"] for row in projection["full"]), 950_327_258)

    def test_append_is_zero_credit_completion_last_and_tamper_sensitive(self) -> None:
        with tempfile.TemporaryDirectory(prefix="axeyum-m2-r2-test-") as temporary:
            root = Path(temporary) / "evidence"
            shutil.copytree(
                R2.EVIDENCE_ROOT, root, ignore=shutil.ignore_patterns("diagnostic")
            )
            for path in root.rglob("*"):
                if path.is_file():
                    path.chmod(0o444)
            completion = R2.append_diagnostic(root, R2.WORK_SOURCE)
            self.assertEqual(completion["process_attempts_added"], 0)
            self.assertEqual(completion["official_outcomes"], 0)
            self.assertEqual(R2.validate_completed(root), completion)
            post = BASE.load_canonical(root / "diagnostic/post.json")
            self.assertEqual(post["credits"]["official_outcomes"], 0)
            changed = copy.deepcopy(post)
            changed["credits"]["official_outcomes"] = 64
            changed = BASE.seal(changed, R2.POST_SCHEMA)
            self.assertNotEqual(changed, R2.build_post({
                "full": post["generated_files"],
                "retained": [
                    {key: value for key, value in row.items() if key != "evidence_path"}
                    for row in post["retained_generated"]
                ],
                "metadata": post["manifest_only_generated"],
                "wrapper": post["existing_wrapper"],
            }))


if __name__ == "__main__":
    unittest.main()
