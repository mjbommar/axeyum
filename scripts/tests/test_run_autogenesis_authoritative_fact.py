from __future__ import annotations

import importlib.util
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/run-autogenesis-authoritative-fact.py"
SPEC = importlib.util.spec_from_file_location("run_authoritative_fact", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)


class AuthoritativeFactRunnerTests(unittest.TestCase):
    def test_selected_fact_path_requires_selection_inside_admissible_set(self) -> None:
        fact_id = "F:ml430-nat-add-modeq-left-e3b1fba9"
        resolved_id, path = runner.selected_fact_path(
            {
                "selection": {
                    "selected_fact_id": fact_id,
                    "admissible_fact_ids": [fact_id],
                }
            }
        )
        self.assertEqual(resolved_id, fact_id)
        self.assertEqual(path.name, "F-ml430-nat-add-modeq-left-e3b1fba9.json")

        for selection in (
            {"selected_fact_id": None, "admissible_fact_ids": []},
            {"selected_fact_id": fact_id, "admissible_fact_ids": []},
            {"selected_fact_id": "../outside", "admissible_fact_ids": ["../outside"]},
        ):
            with self.subTest(selection=selection), self.assertRaisesRegex(
                runner.AdmissionRunError, "no exact admissible selected fact"
            ):
                runner.selected_fact_path({"selection": selection})

    def test_artifact_digest_excludes_self_referential_run_receipt(self) -> None:
        import tempfile

        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            (root / "proof.json").write_text("proof\n")
            (root / "run.json").write_text("self\n")
            self.assertEqual(
                runner.artifact_digests(root),
                {
                    "proof.json": runner.file_digest(root / "proof.json"),
                },
            )


if __name__ == "__main__":
    unittest.main()
