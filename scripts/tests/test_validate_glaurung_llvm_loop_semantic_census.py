#!/usr/bin/env python3

from __future__ import annotations

import copy
import importlib.util
import json
import pathlib
import sys
import tempfile
import unittest


REPO = pathlib.Path(__file__).parents[2]
SCRIPT = REPO / "scripts" / "validate-glaurung-llvm-loop-semantic-census.py"
MANIFEST = (
    REPO
    / "docs"
    / "consumer-track"
    / "verify"
    / "glaurung-llvm-loop-semantic-census-v1.json"
)
RESULT = (
    REPO
    / "docs"
    / "consumer-track"
    / "verify"
    / "glaurung-llvm-loop-semantic-census-v1-result.json"
)
SPEC = importlib.util.spec_from_file_location("validate_glaurung_loop_semantics", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
validator = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = validator
SPEC.loader.exec_module(validator)


class GlaurungLlvmLoopSemanticResultTests(unittest.TestCase):
    def test_exact_result_recomputes_without_dropped_rows(self) -> None:
        result = validator.validate_result(RESULT, MANIFEST)

        self.assertEqual(result["summary"]["rows"], 12)
        self.assertEqual(result["summary"]["accepted"], 0)
        self.assertEqual(result["summary"]["rejected"], 12)
        self.assertEqual(
            result["summary"]["outcome_counts"],
            {"scalar_cfg:unsupported_instruction": 12},
        )
        self.assertEqual(
            result["selection"],
            {
                "bucket": "scalar_cfg:unsupported_instruction",
                "functions": 12,
                "rows": 12,
                "sources": 4,
            },
        )

    def test_result_mutations_fail_closed(self) -> None:
        original = json.loads(RESULT.read_text(encoding="utf-8"))
        mutations = [
            ("summary", lambda value: value["summary"].__setitem__("accepted", 1)),
            ("selection", lambda value: value["selection"].__setitem__("functions", 10)),
            ("drop", lambda value: value["sources"][1]["loops"].clear()),
            (
                "diagnostic",
                lambda value: value["sources"][1]["loops"][0].__setitem__("diagnostic", ""),
            ),
            (
                "hash",
                lambda value: value["sources"][1]["loops"][0].__setitem__(
                    "moduleid_agnostic_extracted_llvm_sha256", "0" * 63
                ),
            ),
            (
                "source",
                lambda value: value["sources"][1]["loops"][0].__setitem__(
                    "source_path", "another.c"
                ),
            ),
        ]
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            for name, mutate in mutations:
                candidate = copy.deepcopy(original)
                mutate(candidate)
                path = root / f"{name}.json"
                path.write_text(json.dumps(candidate), encoding="utf-8")
                with self.subTest(name=name), self.assertRaises(
                    validator.ResultValidationError
                ):
                    validator.validate_result(path, MANIFEST)


if __name__ == "__main__":
    unittest.main()
