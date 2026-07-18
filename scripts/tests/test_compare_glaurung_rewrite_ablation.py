from __future__ import annotations

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "compare-glaurung-rewrite-ablation.py"
SPEC = importlib.util.spec_from_file_location("compare_glaurung_rewrite_ablation", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)

RULE = "bv.extract_extend.v1"


def artifact(*, disabled: bool, cold_ms: float, drift: bool = False) -> dict:
    enabled = ["bv.extract_nested.v1", RULE, "bv.extract_concat.v1"]
    if disabled:
        enabled.remove(RULE)
    config = {
        "backend_kind": "sat-bv",
        "compare_z3": True,
        "config_hash": "ablation" if disabled else "base",
        "corpus_hash": "corpus-drift" if drift else "corpus",
        "corpus_manifest": {"content_hash": "sha256:" + "3" * 64},
        "experiment": {
            "environment_hash": "sha256:" + "2" * 64,
            "source": {"dirty": False, "revision": "1" * 40},
        },
        "jobs": 1,
        "logic": "QF_BV",
        "min_decided_percent": 100.0,
        "require_deterministic_resources": True,
        "require_in_process_z3": True,
        "require_reproducible_run": True,
        "rewrite": {
            "mode": "default",
            "base_rule_set": "axeyum-rewrite-default-v4",
            "rule_set": (
                "axeyum-rewrite-default-v4-ablation"
                if disabled
                else "axeyum-rewrite-default-v4"
            ),
            "disabled_rule_ids": [RULE] if disabled else [],
            "enabled_rule_ids": enabled,
        },
    }
    instances = []
    for index, (family, fires) in enumerate(
        (("register-slice", True), ("arithmetic", False))
    ):
        term_bits = 160 if disabled and fires else 100
        instances.append(
            {
                "file": f"query-{index}.smt2",
                "outcome": "sat" if index else "unsat",
                "cold_total_ms": cold_ms + index,
                "solve_ms": 0.2,
                "backend_stats": {
                    "term_bits_lowered": term_bits,
                    "aig_and_requests": 80,
                    "aig_nodes": 40,
                    "cnf_variables": 20,
                    "cnf_clauses": 50,
                    "bit_blast_ms": 0.5 if not (disabled and fires) else 0.7,
                    "cnf_encode_ms": 0.3,
                },
                "rewrite": {
                    "elapsed_ms": 0.1,
                    "rule_counts": {RULE: 3} if fires and not disabled else {},
                },
                "oracle": {"decision_agrees": True},
                "corpus_manifest": {
                    "decision_agrees": True,
                    "family": family,
                },
            }
        )
    return {
        "version": 33,
        "config": config,
        "instances": instances,
        "summary": {
            "files": 2,
            "decided": 2,
            "decided_percent": 100.0,
            "errors": 0,
            "disagree": 0,
            "model_replay_failures": 0,
            "oracle": {"compared": 2, "agree": 2, "disagree": 0},
            "manifest": {"compared": 2, "agree": 2, "disagree": 0},
        },
    }


def write_pair(root: Path, repetition: int) -> tuple[Path, Path]:
    base = root / f"base-{repetition}.json"
    ablation = root / f"ablation-{repetition}.json"
    base.write_text(
        json.dumps(artifact(disabled=False, cold_ms=1.0 + repetition / 10)),
        encoding="utf-8",
    )
    ablation.write_text(
        json.dumps(artifact(disabled=True, cold_ms=1.2 + repetition / 10)),
        encoding="utf-8",
    )
    return base, ablation


class RewriteAblationComparisonTests(unittest.TestCase):
    def test_reports_paired_structural_and_timing_deltas(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            pairs = [write_pair(root, repetition) for repetition in (1, 2, 3)]
            result = MODULE.compare(
                [pair[0] for pair in pairs], [pair[1] for pair in pairs]
            )
            self.assertEqual(result["rule_id"], RULE)
            self.assertEqual(result["repetitions"], 3)
            self.assertEqual(result["affected"]["instances"], 1)
            self.assertEqual(result["affected"]["families"], {"register-slice": 1})
            self.assertEqual(result["affected"]["applications"], 3)
            self.assertEqual(
                result["structural_affected_ablation_minus_base"][
                    "term_bits_lowered"
                ]["samples"],
                [60.0, 60.0, 60.0],
            )
            self.assertAlmostEqual(
                result["timing_affected_ablation_minus_base_ms"][
                    "cold_total_ms"
                ]["mean"],
                0.2,
            )

    def test_rejects_non_rewrite_configuration_drift(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            base_paths = []
            ablation_paths = []
            for repetition in (1, 2):
                base, ablation = write_pair(root, repetition)
                base_paths.append(base)
                ablation_paths.append(ablation)
            changed = json.loads(ablation_paths[1].read_text(encoding="utf-8"))
            changed["config"]["corpus_hash"] = "different"
            ablation_paths[1].write_text(json.dumps(changed), encoding="utf-8")
            with self.assertRaisesRegex(
                MODULE.ComparisonError, "configuration drift outside rewrite"
            ):
                MODULE.compare(base_paths, ablation_paths)

    def test_rejects_unlisted_enabled_rule_change(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            base_paths = []
            ablation_paths = []
            for repetition in (1, 2):
                base, ablation = write_pair(root, repetition)
                base_paths.append(base)
                ablation_paths.append(ablation)
            changed = json.loads(ablation_paths[0].read_text(encoding="utf-8"))
            changed["config"]["rewrite"]["enabled_rule_ids"].append("hidden.rule")
            ablation_paths[0].write_text(json.dumps(changed), encoding="utf-8")
            with self.assertRaisesRegex(MODULE.ComparisonError, "enabled rules"):
                MODULE.compare(base_paths, ablation_paths)


if __name__ == "__main__":
    unittest.main()
