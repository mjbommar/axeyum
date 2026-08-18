import contextlib
import importlib.util
import io
import json
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "gen-autogenesis-baseline.py"
SPEC = importlib.util.spec_from_file_location("gen_autogenesis_baseline", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def fact(ident, *, route="kernel-lean", deps=(), status="proved"):
    return {
        "id": ident,
        "epistemic_status": status,
        "proof_route": route,
        "depends_on": list(deps),
    }


class AutogenesisBaselineTests(unittest.TestCase):
    def fixture(self):
        temporary = tempfile.TemporaryDirectory()
        root = Path(temporary.name)
        (root / "artifacts/facts").mkdir(parents=True)
        (root / "docs/plan/generated").mkdir(parents=True)
        (root / "seam.txt").write_text("reviewed marker\n", encoding="utf-8")
        (root / "docs/plan/generated/proof-gap-matrix.json").write_text(
            json.dumps({"summary": {"baseline_unsat": 3, "dominant_unsat": 2}}) + "\n",
            encoding="utf-8",
        )
        seam = ({
            "id": "fixture-seam",
            "state": "manual",
            "owner": "test",
            "source": "seam.txt",
            "marker": "reviewed marker",
            "gap": "fixture gap",
        },)
        return temporary, root, seam

    @staticmethod
    def write_fact(root, name, value):
        (root / "artifacts/facts" / name).write_text(
            json.dumps(value, sort_keys=True) + "\n", encoding="utf-8"
        )

    def test_report_is_deterministic_and_finds_kernel_chain(self):
        temporary, root, seams = self.fixture()
        self.addCleanup(temporary.cleanup)
        self.write_fact(root, "b.json", fact("F:b", status="open"))
        self.write_fact(root, "a.json", fact("F:a", deps=("F:b",), status="open"))

        first = MODULE.build_report(root, seams, semantic_sources=())
        second = MODULE.build_report(root, seams, semantic_sources=())

        self.assertEqual(MODULE.render_json(first), MODULE.render_json(second))
        self.assertEqual(first["ledger"]["kernel_lean_graph"]["edges"], 1)
        self.assertEqual(first["ledger"]["kernel_lean_graph"]["max_depth"], 2)
        chain = next(
            row for row in first["autogenesis1_requirements"]
            if row["id"] == "A1-real-derived-chain"
        )
        self.assertEqual(chain["state"], "candidate")

    def test_missing_review_marker_fails_closed(self):
        temporary, root, seams = self.fixture()
        self.addCleanup(temporary.cleanup)
        self.write_fact(root, "b.json", fact("F:b"))
        (root / "seam.txt").write_text("implementation changed\n", encoding="utf-8")

        with self.assertRaisesRegex(MODULE.BaselineError, "no longer contains"):
            MODULE.build_report(root, seams, semantic_sources=())

    def test_fact_mutation_changes_source_identity(self):
        temporary, root, seams = self.fixture()
        self.addCleanup(temporary.cleanup)
        self.write_fact(root, "b.json", fact("F:b"))
        before = MODULE.build_report(root, seams, semantic_sources=())

        self.write_fact(root, "b.json", fact("F:b", status="open"))
        after = MODULE.build_report(root, seams, semantic_sources=())

        self.assertNotEqual(
            before["source_identity"]["digest"], after["source_identity"]["digest"]
        )

    def test_duplicate_fact_id_fails_closed(self):
        temporary, root, seams = self.fixture()
        self.addCleanup(temporary.cleanup)
        self.write_fact(root, "one.json", fact("F:duplicate"))
        self.write_fact(root, "two.json", fact("F:duplicate"))

        with self.assertRaisesRegex(MODULE.BaselineError, "duplicate fact id"):
            MODULE.build_report(root, seams, semantic_sources=())

    def test_cycle_fails_instead_of_publishing_a_depth(self):
        temporary, root, seams = self.fixture()
        self.addCleanup(temporary.cleanup)
        self.write_fact(root, "a.json", fact("F:a", deps=("F:b",)))
        self.write_fact(root, "b.json", fact("F:b", deps=("F:a",)))

        with self.assertRaisesRegex(MODULE.BaselineError, "dependency cycle"):
            MODULE.build_report(root, seams, semantic_sources=())

    def test_check_detects_stale_outputs(self):
        temporary, root, seams = self.fixture()
        self.addCleanup(temporary.cleanup)
        self.write_fact(root, "b.json", fact("F:b"))
        self.assertEqual(MODULE.check_or_write(root, check=False, seams=seams, semantic_sources=()), 0)
        self.assertEqual(MODULE.check_or_write(root, check=True, seams=seams, semantic_sources=()), 0)
        (root / MODULE.OUT_MD).write_text("stale\n", encoding="utf-8")
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(
                MODULE.check_or_write(root, check=True, seams=seams, semantic_sources=()), 1
            )


if __name__ == "__main__":
    unittest.main()
