import contextlib
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
    def render(self, overlay):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "coverage.md"
            overlay_path = Path(directory) / "overlay.json"
            overlay_path.write_text(json.dumps(overlay))
            old = MODULE.OVERLAY, MODULE.OUTPUT, sys.argv
            try:
                MODULE.OVERLAY = overlay_path
                MODULE.OUTPUT = output
                sys.argv = ["gen-autogenesis-knowledge-coverage.py"]
                with contextlib.redirect_stdout(io.StringIO()):
                    self.assertEqual(MODULE.main(), 0)
            finally:
                MODULE.OVERLAY, MODULE.OUTPUT, sys.argv = old
            return output.read_text()

    @staticmethod
    def count(rendered, label):
        line = next(line for line in rendered.splitlines() if line.startswith(f"| {label} |"))
        return int(line.rsplit("|", 2)[1].strip())

    def test_kernel_anchor_does_not_inflate_fact_coverage(self):
        overlay = json.loads((ROOT / "artifacts/autogenesis/knowledge-overlay-v1.json").read_text())
        baseline = self.render(overlay)
        synthetic = json.loads(json.dumps(overlay))
        anchor = next(link for link in synthetic["links"] if link["id"] == "L:kernel-decidable-em-formalizes-excluded-middle")
        anchor["id"] = "L:synthetic-kernel-anchor"
        anchor["source"]["id"] = "Complex.normSq_mul"
        synthetic["links"].append(anchor)
        enriched = self.render(synthetic)
        self.assertEqual(
            self.count(baseline, "Facts with qualified formal content"),
            self.count(enriched, "Facts with qualified formal content"),
        )
        self.assertEqual(
            self.count(baseline, "Reviewed kernel-theorem semantic anchors (separate population)") + 1,
            self.count(enriched, "Reviewed kernel-theorem semantic anchors (separate population)"),
        )


if __name__ == "__main__":
    unittest.main()
