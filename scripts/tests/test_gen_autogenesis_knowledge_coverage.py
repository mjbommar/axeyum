"""Controls for the local, self-contained Autogenesis coverage census."""

import contextlib
import copy
import importlib.util
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "gen_autogenesis_knowledge_coverage",
    ROOT / "scripts/gen-autogenesis-knowledge-coverage.py",
)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class KnowledgeCoverageTests(unittest.TestCase):
    def run_against(self, overlay, operations):
        """Render with a scratch overlay/registry; return (status, text)."""
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "coverage.md"
            overlay_path = Path(directory) / "overlay.json"
            operations_path = Path(directory) / "operations.json"
            overlay_path.write_text(json.dumps(overlay))
            operations_path.write_text(json.dumps(operations))
            old = MODULE.OVERLAY, MODULE.OPERATIONS, MODULE.OUTPUT, sys.argv
            try:
                MODULE.OVERLAY = overlay_path
                MODULE.OPERATIONS = operations_path
                MODULE.OUTPUT = output
                sys.argv = ["gen-autogenesis-knowledge-coverage.py"]
                with (
                    contextlib.redirect_stdout(io.StringIO()),
                    contextlib.redirect_stderr(io.StringIO()),
                ):
                    status = MODULE.main()
            finally:
                MODULE.OVERLAY, MODULE.OPERATIONS, MODULE.OUTPUT, sys.argv = old
            return status, (output.read_text() if output.exists() else "")

    @staticmethod
    def committed():
        return (
            json.loads((ROOT / "artifacts/autogenesis/knowledge-overlay-v1.json").read_text()),
            json.loads((ROOT / "artifacts/autogenesis/operations.json").read_text()),
        )

    @staticmethod
    def count(rendered, label):
        line = next(line for line in rendered.splitlines() if line.startswith(f"| {label} |"))
        return int(line.rsplit("|", 2)[1].strip())

    def test_committed_population_renders_and_is_non_empty(self):
        overlay, operations = self.committed()
        status, rendered = self.run_against(overlay, operations)
        self.assertEqual(status, 0)
        self.assertGreater(self.count(rendered, "Facts in their applicability sets"), 0)

    def test_empty_applicability_fails_rather_than_rendering_a_green_zero(self):
        """The vacuity guard. Without it an empty registry renders a table of
        zeroes and exits 0, which is the census equivalent of a checker that
        cannot fail."""
        overlay, operations = self.committed()
        operations["operations"] = []
        status, _rendered = self.run_against(overlay, operations)
        self.assertEqual(status, 1)

    def test_uncredited_facts_are_counted_separately_from_credited_ones(self):
        """Applicability is a registry assertion; credit is read from fact
        evidence. Conflating them would let the registry credit itself."""
        overlay, operations = self.committed()
        status, rendered = self.run_against(overlay, operations)
        self.assertEqual(status, 0)
        applicable = self.count(rendered, "Facts in their applicability sets")
        credited = self.count(rendered, "Credited facts mapped with `established-by`")
        uncredited = self.count(rendered, "Applicable facts with no `established-by` credit")
        self.assertEqual(applicable, credited + uncredited)

    def test_local_semantic_population_is_nonempty(self):
        overlay, operations = self.committed()
        status, rendered = self.run_against(overlay, operations)
        self.assertEqual(status, 0)
        self.assertGreater(self.count(rendered, "Axeyum-owned concepts reached"), 0)
        self.assertGreater(
            self.count(rendered, "Reviewed empty-footprint kernel theorem anchors"), 0
        )
        self.assertNotIn("External concepts reached", rendered)

    def test_kernel_anchor_does_not_inflate_fact_coverage(self):
        overlay, operations = self.committed()
        status, before = self.run_against(overlay, operations)
        self.assertEqual(status, 0)
        link = copy.deepcopy(
            next(link for link in overlay["links"] if link["relation"] == "formalizes")
        )
        link["id"] = "L:synthetic-kernel-anchor"
        link["source"]["id"] = "Nat.add_comm"
        overlay["links"].append(link)
        status, after = self.run_against(overlay, operations)
        self.assertEqual(status, 0)
        self.assertEqual(
            self.count(before, "Fact records with qualified formal content"),
            self.count(after, "Fact records with qualified formal content"),
        )
        self.assertEqual(
            self.count(after, "Reviewed empty-footprint kernel theorem anchors"),
            self.count(before, "Reviewed empty-footprint kernel theorem anchors") + 1,
        )


if __name__ == "__main__":
    unittest.main()
