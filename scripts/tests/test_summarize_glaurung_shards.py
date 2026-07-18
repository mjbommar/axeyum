from __future__ import annotations

import hashlib
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "summarize-glaurung-shards.py"
SPEC = importlib.util.spec_from_file_location("summarize_glaurung_shards", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_json(path: Path, value: dict) -> str:
    data = (json.dumps(value, sort_keys=True) + "\n").encode()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    return digest(data)


def config(root: Path, tier: str, manifest_digest: str, *, dirty: bool = False) -> dict:
    return {
        "backend": "axeyum-sat-bv rustsat-batsat",
        "compare_backend": "z3 4.13.3.0",
        "compare_z3": True,
        "config_hash": f"config-{tier}",
        "corpus": str(root / tier),
        "corpus_hash": f"corpus-{tier}",
        "corpus_manifest": {
            "content_hash": f"sha256:{manifest_digest}",
            "selected_entries": 1,
            "selected_tier": tier,
        },
        "corpus_source": f"source {tier}",
        "determinism": {
            "profile": "axeyum-bench-fixed-seeds-v1",
            "sat_bv": {
                "adapter": "rustsat-batsat",
                "random_seed": 91_648_253.0,
                "random_var_freq": 0.0,
                "random_polarity": False,
                "random_initial_activity": False,
            },
            "z3": {"random_seed": 0, "set_explicitly": True},
        },
        "experiment": {
            "environment_hash": f"sha256:{'ab' * 32}",
            "source": {"dirty": dirty, "revision": "revision"},
        },
        "jobs": 1,
        "manifest_validation_jobs": 8,
        "timeout_ms": 10_000,
        "resource_limit": 2_000_000,
        "node_budget": 300_000,
        "cnf_variable_budget": 3_000_000,
        "cnf_clause_budget": 8_000_000,
        "resources": {
            "profile": "axeyum-qfbv-cold-bounded-v1",
            "limits": {
                "search": 2_000_000,
                "dag_nodes": 300_000,
                "cnf_variables": 3_000_000,
                "cnf_clauses": 8_000_000,
            },
            "wall_clock_safety_timeout_ms": 10_000,
        },
        "rewrite": {
            "mode": "off",
            "rule_set": None,
        },
        "require_in_process_z3": True,
        "require_reproducible_run": not dirty,
        "require_deterministic_resources": True,
    }


def artifact(
    root: Path,
    tier: str,
    query_path: str,
    expected: str,
    family: str,
    manifest_digest: str,
    *,
    dirty: bool = False,
) -> dict:
    sat = int(expected == "sat")
    unsat = int(expected == "unsat")
    stages = {
        "word_preprocess_s": 0.0,
        "bit_blast_s": 0.1,
        "cnf_encode_s": 0.2,
        "cnf_inprocess_s": 0.0,
        "solve_s": 0.3,
        "model_lift_s": 0.05,
        "model_replay_s": 0.05,
    }
    axeyum = sum(stages.values())
    z3 = 0.5
    return {
        "version": 33,
        "config": config(root, tier, manifest_digest, dirty=dirty),
        "instances": [
            {
                "outcome": expected,
                "model_replay_ms": 0.1 if expected == "sat" else None,
                "corpus_manifest": {
                    "path": query_path,
                    "expected": expected,
                    "family": family,
                    "tiers": [tier],
                    "decision_compared": True,
                    "decision_agrees": True,
                },
                "oracle": {
                    "enabled": True,
                    "decision_compared": True,
                    "decision_agrees": True,
                    "outcome": expected,
                },
                "layer_attribution": {"cnf_variables": 7},
            }
        ],
        "summary": {
            "files": 1,
            "decided": 1,
            "sat": sat,
            "unsat": unsat,
            "unknown": 0,
            "unsupported": 0,
            "errors": 0,
            "disagree": 0,
            "model_replay_failures": 0,
            "manifest": {"expected": 1, "compared": 1, "agree": 1, "disagree": 0},
            "oracle": {
                "enabled": True,
                "compared": 1,
                "agree": 1,
                "disagree": 0,
                "skipped": 0,
            },
            "layer_attribution": {
                "instances": 1,
                "total_pipeline_s": axeyum,
                **stages,
                "construction": {
                    "aig": {"nodes_created": 11},
                    "cnf": {"clauses_emitted": 13},
                },
            },
            "client_comparison": {
                "instances": 1,
                "axeyum_total_s": axeyum,
                "z3_total_s": z3,
                "axeyum_over_z3_ratio": axeyum / z3,
            },
            "rewrite": {
                "applications": 0,
                "changed_instances": 0,
                "decision_changes": 0,
                "decision_matches": 0,
                "sat_unsat_conflicts": 0,
            },
        },
    }


class ShardSummaryTests(unittest.TestCase):
    def make_fixture(self, root: Path, *, dirty: bool = False) -> tuple[Path, Path, list[Path]]:
        shard_root = root / "full-shards"
        hashes = ("00" * 32, "01" * 32)
        expected = ("sat", "unsat")
        families = ("register-slice", "slice-partial")
        parent_files = []
        shards = []
        artifacts = []
        for index in range(2):
            tier = f"full-shard-{index:02d}-of-02"
            query_path = f"queries/{hashes[index]}.smt2"
            parent_files.append(
                {
                    "path": query_path,
                    "expected": expected[index],
                    "family": families[index],
                    "tiers": ["full"],
                }
            )
            child = {
                "version": 1,
                "name": tier,
                "source": "test",
                "logic": "QF_BV",
                "files": [
                    {
                        "path": query_path,
                        "expected": expected[index],
                        "family": families[index],
                        "tiers": [tier],
                    }
                ],
            }
            child_dir = shard_root / tier
            child_digest = write_json(child_dir / "capture-index-v1.json", child)
            manifest = {"version": 1, "logic": "QF_BV", "files": child["files"]}
            manifest_digest = write_json(child_dir / "manifest-v1.json", manifest)
            shards.append(
                {
                    "directory": tier,
                    "tier": tier,
                    "files": 1,
                    "capture_index_sha256": child_digest,
                }
            )
            artifact_path = root / "artifacts" / f"{tier}.json"
            write_json(
                artifact_path,
                artifact(
                    root,
                    tier,
                    query_path,
                    expected[index],
                    families[index],
                    manifest_digest,
                    dirty=dirty,
                ),
            )
            artifact_path.with_suffix(".time").write_text(
                "\tCommand being timed: \"env MEM_LIMIT_GB=4 command\"\n"
                "\tMaximum resident set size (kbytes): 1024\n"
                "\tExit status: 0\n",
                encoding="utf-8",
            )
            artifacts.append(artifact_path)
        parent = {
            "version": 1,
            "name": "full",
            "source": "test",
            "logic": "QF_BV",
            "files": parent_files,
        }
        parent_path = root / "full" / "capture-index-v1.json"
        parent_digest = write_json(parent_path, parent)
        shard_set = {
            "schema": "glaurung-qfbv-shard-set-v1",
            "partition": "u64::from_be_bytes(sha256[0:8]) modulo shard_count",
            "parent_capture_index_sha256": parent_digest,
            "files": 2,
            "shard_count": 2,
            "shards": shards,
        }
        shard_set_path = shard_root / "shard-set-v1.json"
        write_json(shard_set_path, shard_set)
        return shard_set_path, parent_path, artifacts

    def test_aggregates_exact_disjoint_partition(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            shard_set, parent, artifacts = self.make_fixture(Path(directory))
            result = MODULE.summarize(shard_set, parent, "raw", artifacts)
            self.assertTrue(result["aggregate"]["publication_ready"])
            self.assertEqual(result["aggregate"]["files"], 2)
            self.assertEqual(result["aggregate"]["sat"], 1)
            self.assertEqual(result["aggregate"]["unsat"], 1)
            self.assertAlmostEqual(result["aggregate"]["axeyum_total_s"], 1.4)
            self.assertAlmostEqual(result["aggregate"]["z3_total_s"], 1.0)
            self.assertEqual(result["aggregate"]["maximum_resident_set_kib"], 1024)
            self.assertEqual(result["aggregate"]["construction"]["cnf_clauses_emitted"], 26)

    def test_rejects_wrong_instance_verdict(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            shard_set, parent, artifacts = self.make_fixture(Path(directory))
            value = json.loads(artifacts[0].read_text())
            value["instances"][0]["outcome"] = "unsat"
            write_json(artifacts[0], value)
            with self.assertRaisesRegex(MODULE.SummaryError, "outcome does not match"):
                MODULE.summarize(shard_set, parent, "raw", artifacts)

    def test_rejects_dirty_source_unless_explicitly_exploratory(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            shard_set, parent, artifacts = self.make_fixture(Path(directory), dirty=True)
            with self.assertRaisesRegex(MODULE.SummaryError, "publication requires"):
                MODULE.summarize(shard_set, parent, "raw", artifacts)
            result = MODULE.summarize(
                shard_set, parent, "raw", artifacts, allow_exploratory=True
            )
            self.assertFalse(result["aggregate"]["publication_ready"])

    def test_rejects_partition_or_memory_envelope_failure(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            shard_set, parent, artifacts = self.make_fixture(Path(directory))
            artifacts[1].with_suffix(".time").write_text(
                "Maximum resident set size (kbytes): 5000000\nExit status: 0\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(MODULE.SummaryError, "MEM_LIMIT_GB=4"):
                MODULE.summarize(shard_set, parent, "raw", artifacts)


if __name__ == "__main__":
    unittest.main()
