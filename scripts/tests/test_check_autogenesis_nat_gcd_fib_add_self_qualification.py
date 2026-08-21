from __future__ import annotations

import copy
import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-nat-gcd-fib-add-self-qualification.py"
SPEC = importlib.util.spec_from_file_location("check_nat_gcd_fib_add_self_qualification", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class NatGcdFibAddSelfQualificationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.manifest = MODULE.load(MODULE.MANIFEST)

    def reject(self, mutate, message: str) -> None:
        changed = copy.deepcopy(self.manifest)
        mutate(changed)
        with self.assertRaisesRegex(MODULE.QualificationError, message):
            MODULE.validate(changed)

    def test_exact_qualification_is_accepted(self) -> None:
        MODULE.validate(self.manifest)

    def test_candidate_swap_is_rejected(self) -> None:
        self.reject(
            lambda value: value["candidate"].__setitem__("source_name", "Nat.fib_gcd"),
            "candidate",
        )

    def test_relation_mutation_is_rejected(self) -> None:
        self.reject(
            lambda value: value["proof_free_measurement"]["relation_probe"].__setitem__(
                "whnf_head", "Iff"
            ),
            "relation",
        )

    def test_support_route_skip_is_rejected(self) -> None:
        self.reject(
            lambda value: value["qualified_boundary"]["required_local_constructions"].pop(1),
            "boundary",
        )

    def test_proof_or_ledger_credit_is_rejected(self) -> None:
        self.reject(
            lambda value: value["authority"].__setitem__("kernel_submissions", 1),
            "authority",
        )
        self.reject(
            lambda value: value["authority"].__setitem__("ledger_writes", 1),
            "authority",
        )


if __name__ == "__main__":
    unittest.main()
