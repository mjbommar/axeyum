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
SCRIPT = REPO / "scripts" / "census-glaurung-llvm-loop-semantics.py"
MANIFEST = (
    REPO
    / "docs"
    / "consumer-track"
    / "verify"
    / "glaurung-llvm-loop-semantic-census-v1.json"
)
SPEC = importlib.util.spec_from_file_location("glaurung_llvm_loop_semantics", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
census = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = census
SPEC.loader.exec_module(census)


def row(
    function: str,
    source: str,
    *,
    stage: str = "loop_reflection",
    kind: str = "unsupported_memory",
) -> dict[str, object]:
    return {
        "function": function,
        "kind": kind,
        "source_path": source,
        "stage": stage,
    }


class GlaurungLlvmLoopSemanticCensusTests(unittest.TestCase):
    def test_manifest_is_exact_zero_row(self) -> None:
        manifest = census.load_manifest(MANIFEST)
        self.assertEqual(manifest["result_state"], "zero-row")
        self.assertEqual(manifest["selection"], census.EXPECTED_SELECTION)
        self.assertEqual(len(manifest["producer_files"]), 7)

    def test_classifier_output_preserves_acceptance_and_precise_rejection(self) -> None:
        accepted = census.parse_classifier_output(
            "stage=accepted\nkind=self_loop\nfunction=f\n"
            "state_components=2\niteration_paths=1\n",
            "",
        )
        self.assertEqual(accepted["kind"], "self_loop")
        self.assertEqual(accepted["state_components"], 2)

        rejected = census.parse_classifier_output(
            "stage=loop_reflection\nkind=unsupported_memory\nfunction=f\n"
            "state_components=0\niteration_paths=0\n",
            "canonical scalar loop does not admit memory instructions at 7:3",
        )
        self.assertEqual(rejected["diagnostic"], "canonical scalar loop does not admit memory instructions at 7:3")

        syntax = census.parse_classifier_output(
            "stage=function_syntax\nkind=malformed_header\nfunction=\n"
            "state_components=0\niteration_paths=0\n",
            "function header has no global name at 1:1",
            expected_function="expected_name",
        )
        self.assertEqual(syntax["function"], "expected_name")

    def test_classifier_output_fails_closed_on_dropped_or_inconsistent_fields(self) -> None:
        invalid = [
            (
                "stage=accepted\nkind=self_loop\nfunction=f\n"
                "state_components=2\niteration_paths=1\n",
                "unexpected diagnostic",
            ),
            (
                "stage=loop_reflection\nkind=unsupported_memory\nfunction=f\n"
                "state_components=0\niteration_paths=0\n",
                "",
            ),
            (
                "stage=accepted\nkind=self_loop\nfunction=f\nstate_components=2\n",
                "",
            ),
        ]
        for stdout, stderr in invalid:
            with self.subTest(stdout=stdout), self.assertRaises(census.SemanticCensusError):
                census.parse_classifier_output(stdout, stderr)

    def test_selection_requires_strict_plurality_and_cross_source_diversity(self) -> None:
        selection = census.EXPECTED_SELECTION
        selected = census.select_rejection(
            [
                row("a", "one.c"),
                row("b", "two.c"),
                row("c", "three.c", kind="unsupported_body"),
                row("ok", "four.c", stage="accepted", kind="self_loop"),
            ],
            selection,
        )
        self.assertEqual(
            selected,
            {
                "bucket": "loop_reflection:unsupported_memory",
                "functions": 2,
                "rows": 2,
                "sources": 2,
            },
        )
        self.assertIsNone(
            census.select_rejection([row("a", "one.c"), row("b", "one.c")], selection)
        )
        self.assertIsNone(
            census.select_rejection(
                [row("a", "one.c"), row("b", "two.c", kind="unsupported_body")],
                selection,
            )
        )

    def test_manifest_drift_fails_closed(self) -> None:
        original = census.load_manifest(MANIFEST)
        mutations = [
            ("selection", lambda value: value["selection"].__setitem__("minimum_sources", 1)),
            ("result", lambda value: value.__setitem__("result_state", "observed")),
            (
                "producer",
                lambda value: value["producer_files"][0].__setitem__("sha256", "0" * 63),
            ),
            (
                "output",
                lambda value: value.__setitem__("formal_output", "somewhere-else.json"),
            ),
        ]
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            for name, mutate in mutations:
                candidate = copy.deepcopy(original)
                mutate(candidate)
                path = root / f"{name}.json"
                path.write_text(json.dumps(candidate), encoding="utf-8")
                with self.subTest(name=name), self.assertRaises(census.SemanticCensusError):
                    census.load_manifest(path)


if __name__ == "__main__":
    unittest.main()
