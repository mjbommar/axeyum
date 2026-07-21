import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/prove-tock-log2-v3.py"
SPEC = importlib.util.spec_from_file_location("prove_tock_log2_v3", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
PRODUCER = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = PRODUCER
SPEC.loader.exec_module(PRODUCER)


def capture_error(callable_):
    with unittest.TestCase().assertRaises(PRODUCER.CaptureError) as raised:
        callable_()
    return raised.exception.stage, raised.exception.kind


def valid_v3_output() -> str:
    digest = "0" * 64
    lines = []
    for target, width in (("log_base_two", 32), ("log_base_two_u64", 64)):
        for property_name in ("defined", "zero", "floor_log2", "msb"):
            artifacts = "|".join(
                f"{name}_bytes=1|{name}_sha256={digest}"
                for name in (
                    "faithfulness_dimacs",
                    "faithfulness_drat",
                    "final_dimacs",
                    "final_drat",
                    "final_lrat",
                )
            )
            lines.append(
                f"TOCK_PROOF|target={target}|width={width}|property={property_name}"
                "|outcome=proved|evidence=drat|backend=end-to-end-qfbv"
                "|trust=bit-blast-miter:certified,tseitin:certified,"
                "sat-refutation:certified|faithfulness=miter_drat|recheck=pass|"
                f"{artifacts}|terms=100|wall_us=10"
            )
        for mutation in ("wrong_index", "inverted_zero", "high_partition"):
            lines.append(
                f"TOCK_CONTROL|target={target}|width={width}|mutation={mutation}"
                "|outcome=disproved|witness=2|reflected=1|native=1|mutated=0"
                "|replay=pass|wall_us=5"
            )
    lines.append(
        "TOCK_SCOREBOARD|functions=2|proved=8|refuted_replayed=6|unknown=0"
        "|disagree=0|query_wall_us=110|runner_wall_us=120"
    )
    return "\n".join(lines) + "\n"


class ProveTockLog2V3Tests(unittest.TestCase):
    def test_live_lineage_registration_and_capture_validate_prequery(self):
        negative = PRODUCER.validate_lineage()
        registration = PRODUCER.read_registration(PRODUCER.DEFAULT_REGISTRATION)
        capture = PRODUCER.BASE.validate_capture(registration)
        self.assertEqual(negative["outputs"]["proofs_credited"], 0)
        self.assertEqual(registration["schema"], PRODUCER.REGISTRATION_SCHEMA)
        self.assertEqual(
            capture["capture_identity_sha256"],
            registration["capture"]["identity_sha256"],
        )

    def test_lineage_rejects_mutated_v2_negative(self):
        negative = json.loads(PRODUCER.V2_NEGATIVE.read_text(encoding="utf-8"))
        negative["first_query"]["trust_steps"][0]["certified"] = True
        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "negative.json"
            path.write_text(json.dumps(negative), encoding="utf-8")
            self.assertEqual(
                capture_error(
                    lambda: PRODUCER.validate_lineage(
                        PRODUCER.V2_REGISTRATION,
                        PRODUCER.V2_PREFLIGHT,
                        path,
                    )
                ),
                ("lineage", "v2_negative_hash"),
            )

    def test_registration_changes_only_policy_schema_and_producers(self):
        v2 = json.loads(PRODUCER.V2_REGISTRATION.read_text(encoding="utf-8"))
        v3 = json.loads(PRODUCER.DEFAULT_REGISTRATION.read_text(encoding="utf-8"))
        for field in (
            "archive_policy",
            "canonical",
            "capture",
            "command",
            "expected_rows",
            "resource_scope",
            "source_files",
            "tools",
        ):
            self.assertEqual(v3[field], v2[field], field)
        self.assertEqual(v3["solver"], PRODUCER.EXPECTED_SOLVER)
        self.assertEqual(v3["solver"]["controls"], v2["solver"])
        self.assertEqual(v3["solver"]["proofs"]["deadline_seconds"], 30)
        self.assertEqual(
            v3["solver"]["proofs"]["rechecks"],
            ["faithfulness_drat", "final_drat", "final_lrat_if_present"],
        )

    def test_parser_requires_dual_drat_metadata_and_recheck(self):
        parsed = PRODUCER.parse_runner_output(valid_v3_output())
        self.assertEqual(len(parsed["proofs"]), 8)
        missing_recheck = valid_v3_output().replace("|recheck=pass", "", 1)
        self.assertEqual(
            capture_error(lambda: PRODUCER.parse_runner_output(missing_recheck)),
            ("result", "proof_certificate"),
        )
        bad_hash = valid_v3_output().replace("0" * 64, "not-a-hash", 1)
        self.assertEqual(
            capture_error(lambda: PRODUCER.parse_runner_output(bad_hash)),
            ("result", "proof_artifact_hash"),
        )

    def test_v3_schema_and_output_are_distinct(self):
        self.assertEqual(PRODUCER.DEFAULT_OUTPUT.name, "proof-v3")
        self.assertNotEqual(
            PRODUCER.REGISTRATION_SCHEMA,
            "axeyum.tock-log2-proof-v2-registration.v1",
        )

    def test_no_official_output_exists_prequery(self):
        self.assertFalse(PRODUCER.DEFAULT_OUTPUT.exists())


if __name__ == "__main__":
    unittest.main()
