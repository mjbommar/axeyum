import copy
import importlib.util
import pathlib
import unittest


SCRIPT = (
    pathlib.Path(__file__).resolve().parents[1]
    / "run-glaurung-symbolic-cve-reproducibility.py"
)
SPEC = importlib.util.spec_from_file_location("symbolic_cve_reproducibility", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def side(*, solver: str, witness: str) -> dict:
    return {
        "schema": MODULE.SIDE_SCHEMA,
        "object_id": "CVE-TEST/vulnerable/ordinary",
        "object_sha256": "1" * 64,
        "handler": "handler",
        "solver": solver,
        "max_states": 16,
        "command": None,
        "environment": "generic",
        "admitted": True,
        "execution_acceptable": True,
        "error": None,
        "external_calls": 1,
        "modeled_external_calls": 1,
        "local_calls": 0,
        "modeled_local_calls": 0,
        "sinks": [
            {
                "va": 0x1000,
                "kind": "OutOfBoundsIndex",
                "severity": "constrained",
                "tainted_by": ["IoctlArg"],
                "witness": {"1": witness},
            }
        ],
        "exploration": {
            "runs": 1,
            "completed": 1,
            "state_budget": 0,
            "solve_budget": 0,
            "timeout_budget": 0,
            "deadline": 0,
        },
        "path_stops": {
            "returned": 1,
            "traps": {},
            "off_cfg": 0,
            "loop_limit": 0,
            "model_unavailable": 0,
            "unresolved_symbolic_memory": 0,
            "unsupported_intrinsics": {},
            "residual_unknowns": {},
            "unexpected_fork": 0,
            "budget_exhausted": 0,
            "unexpected_flow": 0,
            "unmodeled_calls": {},
            "stop_sites": {"4096": {"return": 1}},
            "memory_access_sites": {},
            "low_page_access_sites": {},
            "concrete_access_addresses": {"4096": {witness: 1}},
        },
        "concretization": {
            "policy": "glaurung-any-model-v1",
            "attempts": 0,
            "completed": 0,
            "inconclusive": 0,
            "unknown": 0,
            "no_solver": 0,
            "error": 0,
        },
    }


def result(*, authority: str, witness: str, repetition: int) -> dict:
    report = side(solver="axeyum-qfbv" if authority == "axeyum" else "z3", witness=witness)
    row = {
        "cve": "CVE-TEST",
        "handler": "handler",
        "command": None,
        "environment": "generic",
        "pair_detected": True,
        "fixed_side_clean": True,
        "cells": {"vulnerable/ordinary": report},
    }
    value = {"authority": authority, "rows": [row], "repetition": repetition}
    value["exact_digest"] = MODULE.digest(MODULE.exact_result_projection(value))
    value["finding_digest"] = MODULE.digest(MODULE.finding_projection(value))
    value["model_digest"] = MODULE.digest(MODULE.model_projection(value))
    return value


def observation(machine: str, *, drift: bool = False) -> dict:
    rows = [
        result(authority="axeyum", witness="0x10", repetition=0),
        result(authority="z3", witness="0x20", repetition=0),
        result(authority="z3", witness="0x20", repetition=1),
        result(authority="axeyum", witness="0x11" if drift else "0x10", repetition=1),
    ]
    return {
        "schema": MODULE.OBSERVATION_SCHEMA,
        "registration_sha256": "a" * 64,
        "machine": {"id": machine},
        "schedule": [["axeyum", "z3"], ["z3", "axeyum"]],
        "observations": rows,
        "same_machine": {"gate_passed": not drift},
    }


class SymbolicCveReproducibilityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.registration = {
            "_validated_sha256": "a" * 64,
            "minimum_distinct_machines": 2,
        }

    def test_finding_projection_excludes_only_model_choices(self) -> None:
        axeyum = result(authority="axeyum", witness="0x10", repetition=0)
        z3 = result(authority="z3", witness="0x20", repetition=0)
        self.assertEqual(axeyum["finding_digest"], z3["finding_digest"])
        self.assertNotEqual(axeyum["exact_digest"], z3["exact_digest"])
        self.assertNotEqual(axeyum["model_digest"], z3["model_digest"])

        changed = copy.deepcopy(z3)
        changed["rows"][0]["cells"]["vulnerable/ordinary"]["sinks"][0][
            "kind"
        ] = "NullDeref"
        self.assertNotEqual(
            axeyum["finding_digest"],
            MODULE.digest(MODULE.finding_projection(changed)),
        )

    def test_one_machine_is_valid_but_not_cross_machine_evidence(self) -> None:
        analysis = MODULE.analyze_observations(
            self.registration, [observation("machine-a")]
        )
        self.assertFalse(analysis["accepted"])
        self.assertEqual(analysis["reasons"], ["cross_machine_population_missing"])
        self.assertTrue(analysis["backend_finding_identity"])
        self.assertFalse(analysis["backend_model_identity"])

    def test_two_exact_machines_accept_with_model_diversity(self) -> None:
        analysis = MODULE.analyze_observations(
            self.registration,
            [observation("machine-a"), observation("machine-b")],
        )
        self.assertTrue(analysis["accepted"])
        self.assertEqual(analysis["reasons"], [])
        self.assertFalse(analysis["backend_model_identity"])

    def test_same_authority_drift_fails(self) -> None:
        analysis = MODULE.analyze_observations(
            self.registration,
            [observation("machine-a", drift=True), observation("machine-b")],
        )
        self.assertFalse(analysis["accepted"])
        self.assertIn("same_machine_gate_failed", analysis["reasons"])
        self.assertIn("cross_machine_exact_report_drift", analysis["reasons"])

    def test_duplicate_machine_id_is_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, "duplicate machine ID"):
            MODULE.analyze_observations(
                self.registration,
                [observation("machine-a"), observation("machine-a")],
            )

    def test_stored_digest_cannot_override_raw_observation(self) -> None:
        tampered = observation("machine-a")
        tampered["observations"][0]["rows"][0]["cells"][
            "vulnerable/ordinary"
        ]["sinks"][0]["kind"] = "NullDeref"
        with self.assertRaisesRegex(ValueError, "exact_digest does not match row"):
            MODULE.analyze_observations(self.registration, [tampered])


if __name__ == "__main__":
    unittest.main()
