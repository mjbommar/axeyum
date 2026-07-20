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
SCRIPT = REPO / "scripts" / "census-glaurung-llvm-loops.py"
MANIFEST = REPO / "docs" / "consumer-track" / "verify" / "glaurung-llvm-loop-census-v1.json"
RESULT = (
    REPO
    / "docs"
    / "consumer-track"
    / "verify"
    / "glaurung-llvm-loop-census-v1-result.json"
)
SPEC = importlib.util.spec_from_file_location("glaurung_llvm_loop_census", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
census = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = census
SPEC.loader.exec_module(census)


def block(name: str, *tags: str) -> object:
    return census.LoopBlock(name=name, tags=tags)


def row(*blocks: object, depth: int = 1) -> object:
    return census.LoopRow(function="f", depth=depth, blocks=blocks)


class GlaurungLlvmLoopCensusTests(unittest.TestCase):
    def test_parses_real_loopinfo_shapes(self) -> None:
        functions, rows = census.parse_loop_info(
            """Loop info for function 'main':
Loop at depth 1 containing: %13<header><latch><exiting>
Loop info for function 'mathlib_is_prime':
Parallel Loop at depth 1 containing: %19<header><exiting>,%23<exiting>,%15<latch><exiting>
"""
        )

        self.assertEqual(functions, ["main", "mathlib_is_prime"])
        self.assertEqual(len(rows), 2)
        self.assertEqual(rows[0].blocks[0].tags, ("header", "latch", "exiting"))
        self.assertEqual(
            census.classify_loop(rows[0], function_has_nested_loop=False),
            "adr0291_self_loop_shape",
        )
        self.assertEqual(
            census.classify_loop(rows[1], function_has_nested_loop=False),
            "single_latch_early_exit_shape",
        )

    def test_classifies_every_registered_profile(self) -> None:
        cases = [
            (
                row(block("%1", "header", "latch", "exiting")),
                False,
                "adr0291_self_loop_shape",
            ),
            (
                row(block("%1", "header"), block("%2", "latch", "exiting")),
                False,
                "adr0292_single_latch_shape",
            ),
            (
                row(block("%1", "header", "exiting"), block("%2", "latch")),
                False,
                "single_latch_early_exit_shape",
            ),
            (
                row(block("%1", "header"), block("%2", "latch")),
                False,
                "single_latch_no_exit_shape",
            ),
            (
                row(
                    block("%1", "header"),
                    block("%2", "latch", "exiting"),
                    block("%3", "latch"),
                ),
                False,
                "multi_latch_shape",
            ),
            (
                row(block("%1", "header", "latch", "exiting"), depth=2),
                True,
                "nested_shape",
            ),
            (row(block("%1", "latch", "exiting")), False, "other_shape"),
        ]

        for loop, nested, expected in cases:
            with self.subTest(profile=expected):
                self.assertEqual(
                    census.classify_loop(loop, function_has_nested_loop=nested),
                    expected,
                )

    def test_parser_rejects_unregistered_output_syntax(self) -> None:
        malformed = [
            "Loop at depth 1 containing: %1<header><latch><exiting>\n",
            "Loop info for function 'f':\nLoopNest at depth 1 containing: %1\n",
            "Loop info for function 'f':\nLoop at depth 1 containing: 1<header>\n",
            "Loop info for function 'f':\nLoop at depth 1 containing: %1<header>junk\n",
        ]
        for text in malformed:
            with self.subTest(text=text), self.assertRaises(census.CensusError):
                census.parse_loop_info(text)

    def test_manifest_is_exact_zero_row(self) -> None:
        manifest = census.load_manifest(MANIFEST)
        self.assertEqual(manifest["result_state"], "zero-row")
        self.assertEqual(len(manifest["glaurung"]["sources"]), 12)
        self.assertEqual(manifest["loop_analysis"]["profiles"], census.PROFILES)

    def test_manifest_drift_fails_closed(self) -> None:
        original = census.load_manifest(MANIFEST)
        mutations = [
            ("result", lambda value: value.__setitem__("result_state", "observed")),
            ("args", lambda value: value["compile"]["args"].append("-O2")),
            ("profiles", lambda value: value["loop_analysis"]["profiles"].reverse()),
            (
                "hash",
                lambda value: value["glaurung"]["sources"][0].__setitem__("sha256", "0" * 63),
            ),
        ]
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            for name, mutate in mutations:
                candidate = copy.deepcopy(original)
                mutate(candidate)
                path = root / f"{name}.json"
                path.write_text(json.dumps(candidate), encoding="utf-8")
                with self.subTest(name=name), self.assertRaises(census.CensusError):
                    census.load_manifest(path)

    def test_formal_result_recomputes_exactly(self) -> None:
        manifest = census.load_manifest(MANIFEST)
        result = census.load_result(RESULT, MANIFEST, manifest)

        self.assertEqual(result["summary"]["loops"], 12)
        self.assertEqual(result["summary"]["functions_with_loops"], 12)
        self.assertEqual(result["summary"]["profile_counts"]["adr0291_self_loop_shape"], 11)
        self.assertEqual(
            result["summary"]["profile_counts"]["single_latch_early_exit_shape"], 1
        )

    def test_formal_result_drift_fails_closed(self) -> None:
        manifest = census.load_manifest(MANIFEST)
        original = json.loads(RESULT.read_text(encoding="utf-8"))
        mutations = [
            ("total", lambda value: value["summary"].__setitem__("loops", 13)),
            (
                "profile",
                lambda value: value["sources"][1]["loops"][0].__setitem__(
                    "profile", "single_latch_no_exit_shape"
                ),
            ),
            (
                "function",
                lambda value: value["sources"][1]["loops"][0].__setitem__(
                    "function", "missing"
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
                with self.subTest(name=name), self.assertRaises(census.CensusError):
                    census.load_result(path, MANIFEST, manifest)

    def test_retain_exact_creates_reproduces_and_rejects_drift(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory) / "result.json"
            self.assertEqual(census.retain_exact(path, b"first\n"), "created")
            self.assertEqual(census.retain_exact(path, b"first\n"), "reproduced")
            with self.assertRaisesRegex(census.CensusError, "not byte-identical"):
                census.retain_exact(path, b"second\n")


if __name__ == "__main__":
    unittest.main()
