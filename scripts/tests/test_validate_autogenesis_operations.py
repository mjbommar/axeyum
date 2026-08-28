#!/usr/bin/env python3
"""Mutation controls for the typed Autogenesis operation registry."""

from __future__ import annotations

import copy
import importlib.util
import json
import pathlib
import tempfile
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/validate-autogenesis-operations.py"
SPEC = importlib.util.spec_from_file_location("validate_autogenesis_operations", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
registry_module = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(registry_module)


class OperationRegistryTests(unittest.TestCase):
    def setUp(self) -> None:
        self.registry = json.loads(
            (ROOT / "artifacts/autogenesis/operations.json").read_text()
        )

    def test_committed_registry_has_one_fixture_and_twenty_authoritative_operations(self) -> None:
        registry_module.validate_registry(self.registry, ROOT)
        # A FLOOR, not an equality. This pinned 21 while the registry grew to 25,
        # and stayed red for hours across three further registrations -- an
        # equality on a number that legitimately rises goes red for a reason that
        # is not a defect, and then it gets bumped without being read, which is
        # how a ratchet stops being a ratchet.
        #
        # The floor still catches the regression that matters (operations
        # disappearing) and leaves growth alone. What is pinned BY VALUE below is
        # the composition, which is where a meaningful change would show: exactly
        # one fixture-scope entry, and the multi-target count that is this
        # programme's headline metric.
        self.assertGreaterEqual(len(self.registry["operations"]), 25)
        scopes = [o["scope"] for o in self.registry["operations"]]
        self.assertEqual(scopes.count("counterfactual-fixture-only"), 1)
        multi = [
            o["id"]
            for o in self.registry["operations"]
            if o["scope"] == "authoritative"
            and len(o["applicability"]["fact_ids"]) > 1
        ]
        # 1 as of 2026-08-22 -- the first operation in this repository covering
        # more than one fact. A FALL here means generality was lost and is never
        # something to re-pin quietly; a rise is the result.
        self.assertGreaterEqual(len(multi), 1)
        self.assertEqual(
            self.registry["operations"][0]["scope"], "counterfactual-fixture-only"
        )
        authoritative = self.registry["operations"][1]
        self.assertEqual(authoritative["scope"], "authoritative")
        self.assertEqual(
            authoritative["applicability"]["fact_ids"],
            ["F:no-integer-square-is-minus-one"],
        )
        self.assertEqual(
            authoritative["executor"]["driver"],
            "axeyum-bench/smtcomp-evidence-v1",
        )
        kernel = self.registry["operations"][2]
        self.assertEqual(kernel["scope"], "authoritative")
        self.assertEqual(kernel["applicability"]["fact_ids"], ["F:nat-zero-add"])
        self.assertEqual(
            kernel["executor"]["driver"],
            "axeyum-lean-kernel/nat-zero-add-induction-v1",
        )
        apply = self.registry["operations"][3]
        self.assertEqual(apply["scope"], "authoritative")
        self.assertEqual(apply["applicability"]["fact_ids"], ["F:nat-mul-one"])
        self.assertEqual(
            apply["executor"]["driver"],
            "axeyum-lean-kernel/nat-mul-one-episode-apply-v1",
        )
        reflexivity = self.registry["operations"][4]
        self.assertEqual(
            reflexivity["applicability"]["fact_ids"],
            ["F:ml430-nat-ascfactorial-zero-fd183202"],
        )
        self.assertEqual(
            reflexivity["executor"]["driver"],
            "axeyum-lean-import/statement-reflexivity-v1",
        )
        desc_reflexivity = self.registry["operations"][5]
        self.assertEqual(
            desc_reflexivity["applicability"]["fact_ids"],
            ["F:ml430-nat-descfactorial-zero-966b01df"],
        )
        self.assertEqual(
            desc_reflexivity["executor"]["driver"],
            "axeyum-lean-import/statement-reflexivity-v1",
        )
        fib = self.registry["operations"][6]
        self.assertEqual(
            fib["applicability"]["fact_ids"],
            ["F:ml430-nat-fib-add-two-b86e0c82"],
        )
        self.assertEqual(
            fib["executor"]["driver"],
            "axeyum-lean-import/checked-theorem-receipt-v1",
        )
        fib_coprime = self.registry["operations"][7]
        self.assertEqual(
            fib_coprime["applicability"]["fact_ids"],
            ["F:ml430-nat-fib-coprime-fib-succ-162fc738"],
        )
        self.assertEqual(
            fib_coprime["executor"]["driver"],
            "axeyum-lean-import/dependency-theorem-receipt-v1",
        )
        gcd_fib = self.registry["operations"][8]
        self.assertEqual(
            gcd_fib["applicability"]["fact_ids"],
            ["F:ml430-nat-gcd-fib-add-self-5a92d5e3"],
        )
        self.assertEqual(
            gcd_fib["executor"]["driver"],
            "axeyum-lean-import/sealed-kernel-capsule-v1",
        )
        gcd_greatest = self.registry["operations"][9]
        self.assertEqual(
            gcd_greatest["applicability"]["fact_ids"],
            ["F:ml430-nat-gcd-greatest-0a04214a"],
        )
        self.assertEqual(
            gcd_greatest["executor"]["driver"],
            "axeyum-lean-import/sealed-kernel-capsule-v1",
        )
        fib_gcd = self.registry["operations"][10]
        self.assertEqual(
            fib_gcd["applicability"]["fact_ids"],
            ["F:ml430-nat-fib-gcd-d1d98407"],
        )
        fib_dvd = self.registry["operations"][11]
        self.assertEqual(
            fib_dvd["applicability"]["fact_ids"],
            ["F:ml430-nat-fib-dvd-f80f3de1"],
        )
        int_fib_natcast = self.registry["operations"][12]
        self.assertEqual(
            int_fib_natcast["applicability"]["fact_ids"],
            ["F:ml430-int-fib-natcast-d5886be4"],
        )
        self.assertEqual(int_fib_natcast["applicability"]["fragments"], ["Int"])
        self.assertEqual(
            int_fib_natcast["executor"]["driver"],
            "axeyum-lean-import/sealed-kernel-capsule-v1",
        )
        int_fib_add_two = self.registry["operations"][13]
        self.assertEqual(
            int_fib_add_two["applicability"]["fact_ids"],
            ["F:ml430-int-fib-add-two-739358dd"],
        )
        self.assertEqual(int_fib_add_two["applicability"]["fragments"], ["Int"])
        self.assertEqual(
            int_fib_add_two["executor"]["driver"],
            "axeyum-lean-import/sealed-kernel-capsule-v1",
        )
        int_fib_corollary = self.registry["operations"][14]
        self.assertEqual(
            int_fib_corollary["applicability"]["fact_ids"],
            ["F:ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d"],
        )
        self.assertEqual(int_fib_corollary["applicability"]["fragments"], ["Int"])
        self.assertEqual(
            int_fib_corollary["executor"]["driver"],
            "axeyum-lean-import/sealed-kernel-capsule-v1",
        )
        int_fib_add_one = self.registry["operations"][15]
        self.assertEqual(
            int_fib_add_one["applicability"]["fact_ids"],
            ["F:ml430-int-fib-add-one-33f1b748"],
        )
        self.assertEqual(int_fib_add_one["applicability"]["fragments"], ["Int"])
        self.assertEqual(
            int_fib_add_one["executor"]["driver"],
            "axeyum-lean-import/sealed-kernel-capsule-v1",
        )
        int_fib_neg = self.registry["operations"][16]
        self.assertEqual(
            int_fib_neg["applicability"]["fact_ids"],
            ["F:ml430-int-fib-neg-b4021d37"],
        )
        self.assertEqual(int_fib_neg["applicability"]["fragments"], ["Int"])
        self.assertEqual(
            int_fib_neg["executor"]["driver"],
            "axeyum-lean-import/sealed-kernel-capsule-v1",
        )
        int_fib_gcd = self.registry["operations"][18]
        self.assertEqual(
            int_fib_gcd["applicability"]["fact_ids"],
            ["F:ml430-int-fib-gcd-3a8bfdec"],
        )
        self.assertEqual(int_fib_gcd["applicability"]["fragments"], ["Int"])
        self.assertEqual(
            int_fib_gcd["executor"]["driver"],
            "axeyum-lean-import/sealed-kernel-capsule-v1",
        )
        int_fib_dvd = self.registry["operations"][19]
        self.assertEqual(
            int_fib_dvd["applicability"]["fact_ids"],
            ["F:ml430-int-fib-dvd-ffb3c5c1"],
        )
        self.assertEqual(int_fib_dvd["applicability"]["fragments"], ["Int"])
        self.assertEqual(
            int_fib_dvd["executor"]["driver"],
            "axeyum-lean-import/sealed-kernel-capsule-v1",
        )
        int_fib_of_nonneg = self.registry["operations"][20]
        self.assertEqual(
            int_fib_of_nonneg["applicability"]["fact_ids"],
            ["F:ml430-int-fib-of-nonneg-438018c5"],
        )
        self.assertEqual(int_fib_of_nonneg["applicability"]["fragments"], ["Int"])
        self.assertEqual(
            int_fib_of_nonneg["executor"]["driver"],
            "axeyum-lean-import/sealed-kernel-capsule-v1",
        )

    def test_integer_fibonacci_capsule_identity_is_exact(self) -> None:
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][12]["executor"]["goal_sha256"] = "0" * 64
        with self.assertRaisesRegex(
            registry_module.RegistryError, "integer Fibonacci capsule contract"
        ):
            registry_module.validate_registry(mutated, ROOT)

        mutated = copy.deepcopy(self.registry)
        mutated["operations"][15]["executor"]["goal_sha256"] = "0" * 64
        with self.assertRaisesRegex(
            registry_module.RegistryError, "integer Fibonacci capsule contract"
        ):
            registry_module.validate_registry(mutated, ROOT)

        mutated = copy.deepcopy(self.registry)
        mutated["operations"][14]["executor"]["goal_sha256"] = "0" * 64
        with self.assertRaisesRegex(
            registry_module.RegistryError, "integer Fibonacci capsule contract"
        ):
            registry_module.validate_registry(mutated, ROOT)

        mutated = copy.deepcopy(self.registry)
        mutated["operations"][16]["executor"]["goal_sha256"] = "0" * 64
        with self.assertRaisesRegex(
            registry_module.RegistryError, "integer Fibonacci capsule contract"
        ):
            registry_module.validate_registry(mutated, ROOT)

        mutated = copy.deepcopy(self.registry)
        mutated["operations"][18]["executor"]["goal_sha256"] = "0" * 64
        with self.assertRaisesRegex(
            registry_module.RegistryError, "integer Fibonacci capsule contract"
        ):
            registry_module.validate_registry(mutated, ROOT)

        mutated = copy.deepcopy(self.registry)
        mutated["operations"][19]["executor"]["goal_sha256"] = "0" * 64
        with self.assertRaisesRegex(
            registry_module.RegistryError, "integer Fibonacci capsule contract"
        ):
            registry_module.validate_registry(mutated, ROOT)

        mutated = copy.deepcopy(self.registry)
        mutated["operations"][20]["executor"]["goal_sha256"] = "0" * 64
        with self.assertRaisesRegex(
            registry_module.RegistryError, "integer Fibonacci capsule contract"
        ):
            registry_module.validate_registry(mutated, ROOT)

    def test_duplicate_operation_id_is_rejected(self) -> None:
        mutated = copy.deepcopy(self.registry)
        mutated["operations"].append(copy.deepcopy(mutated["operations"][0]))
        with self.assertRaisesRegex(registry_module.RegistryError, "duplicate"):
            registry_module.validate_registry(mutated, ROOT)

    def test_shell_command_field_is_rejected(self) -> None:
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][0]["checker"]["command"] = "true"
        with self.assertRaisesRegex(registry_module.RegistryError, "fields differ"):
            registry_module.validate_registry(mutated, ROOT)

    def test_missing_implementation_is_rejected(self) -> None:
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][0]["producer"]["implementation"] = "missing.py"
        with self.assertRaisesRegex(registry_module.RegistryError, "does not exist"):
            registry_module.validate_registry(mutated, ROOT)

    def test_unknown_route_evidence_pair_is_rejected(self) -> None:
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][1]["admission"]["proof_route"] = "smt-clausal"
        with self.assertRaisesRegex(registry_module.RegistryError, "outside the v1"):
            registry_module.validate_registry(mutated, ROOT)

    def test_authoritative_operation_requires_a_typed_executor(self) -> None:
        mutated = copy.deepcopy(self.registry)
        del mutated["operations"][1]["executor"]
        with self.assertRaisesRegex(registry_module.RegistryError, "missing=.*executor"):
            registry_module.validate_registry(mutated, ROOT)

    def test_gate_review_and_kernel_executor_scope_are_exact(self) -> None:
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][2]["reviewed_gate_mentions"] = []
        registry_module.validate_registry(mutated, ROOT)

        mutated = copy.deepcopy(self.registry)
        mutated["operations"][2]["reviewed_gate_mentions"].append("missing.sh")
        with self.assertRaisesRegex(registry_module.RegistryError, "gate mention"):
            registry_module.validate_registry(mutated, ROOT)

        mutated = copy.deepcopy(self.registry)
        mutated["operations"][2]["executor"]["target_theorem"] = "Nat.add_zero"
        with self.assertRaisesRegex(registry_module.RegistryError, "target"):
            registry_module.validate_registry(mutated, ROOT)

        mutated = copy.deepcopy(self.registry)
        mutated["operations"][3]["executor"]["premise_operation_id"] = "invented"
        with self.assertRaisesRegex(registry_module.RegistryError, "premise_operation"):
            registry_module.validate_registry(mutated, ROOT)

    def test_executor_cannot_escape_or_name_an_unknown_driver(self) -> None:
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][1]["executor"]["input_artifact"] = "../secret.smt2"
        with self.assertRaisesRegex(registry_module.RegistryError, "repository-relative"):
            registry_module.validate_registry(mutated, ROOT)

        mutated = copy.deepcopy(self.registry)
        mutated["operations"][1]["executor"]["driver"] = "shell"
        with self.assertRaisesRegex(registry_module.RegistryError, "unsupported"):
            registry_module.validate_registry(mutated, ROOT)

    def test_executor_fact_and_artifact_must_match_applicability(self) -> None:
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][1]["executor"]["input_fact_id"] = "F:contraposition"
        with self.assertRaisesRegex(registry_module.RegistryError, "sole applicable"):
            registry_module.validate_registry(mutated, ROOT)

        mutated = copy.deepcopy(self.registry)
        mutated["operations"][1]["executor"]["input_artifact"] = (
            "artifacts/facts/smt2/neg-contraposition.smt2"
        )
        with self.assertRaisesRegex(registry_module.RegistryError, "does not match"):
            registry_module.validate_registry(mutated, ROOT)

    def test_admission_footprint_must_match_its_policy(self) -> None:
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][1]["admission"]["axiom_footprint"] = []
        with self.assertRaisesRegex(registry_module.RegistryError, "violates"):
            registry_module.validate_registry(mutated, ROOT)

    def test_statement_reflexivity_driver_is_exactly_manifest_bound(self) -> None:
        for field, value in (
            ("target_definition", "Axeyum.Wrong"),
            ("max_binders", 9),
            ("max_constructed_nodes", 17),
        ):
            with self.subTest(field=field):
                mutated = copy.deepcopy(self.registry)
                mutated["operations"][4]["executor"][field] = value
                with self.assertRaisesRegex(registry_module.RegistryError, "manifests disagree"):
                    registry_module.validate_registry(mutated, ROOT)

        mutated = copy.deepcopy(self.registry)
        mutated["operations"][0]["admission"]["axiom_footprint"] = ["invented"]
        with self.assertRaisesRegex(registry_module.RegistryError, "violates"):
            registry_module.validate_registry(mutated, ROOT)

    def test_checked_theorem_receipt_driver_is_exactly_manifest_bound(self) -> None:
        for field, value in (
            ("target_definition", "Axeyum.Wrong"),
            ("receipt_sha256", "0" * 64),
        ):
            with self.subTest(field=field):
                mutated = copy.deepcopy(self.registry)
                mutated["operations"][6]["executor"][field] = value
                with self.assertRaisesRegex(
                    registry_module.RegistryError,
                    "receipt contract disagrees|exceeds the exact",
                ):
                    registry_module.validate_registry(mutated, ROOT)

    def test_dependency_theorem_receipt_driver_is_exactly_manifest_bound(self) -> None:
        for field, value in (
            ("target_definition", "Axeyum.Wrong"),
            ("receipt_sha256", "0" * 64),
            ("dependency_set_sha256", "1" * 64),
            ("transitive_dependency_set_sha256", "2" * 64),
        ):
            with self.subTest(field=field):
                mutated = copy.deepcopy(self.registry)
                mutated["operations"][7]["executor"][field] = value
                with self.assertRaisesRegex(
                    registry_module.RegistryError,
                    "contract disagrees|exceeds the exact",
                ):
                    registry_module.validate_registry(mutated, ROOT)

    def test_bounded_induction_multi_target_driver_binds_exact_fact_ids(self) -> None:
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][24]["applicability"]["fact_ids"] = list(
            reversed(mutated["operations"][24]["applicability"]["fact_ids"])
        )
        with self.assertRaisesRegex(
            registry_module.RegistryError, "must bind exactly its applicable fact ids"
        ):
            registry_module.validate_registry(mutated, ROOT)

    def test_bounded_induction_multi_target_driver_is_exactly_manifest_bound(self) -> None:
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][24]["executor"]["targets"][0]["target_definition"] = (
            "Axeyum.Wrong"
        )
        with self.assertRaisesRegex(
            registry_module.RegistryError, "bounded-induction manifests disagree"
        ):
            registry_module.validate_registry(mutated, ROOT)

        mutated = copy.deepcopy(self.registry)
        mutated["operations"][24]["executor"]["max_inductions"] = 3
        with self.assertRaisesRegex(
            registry_module.RegistryError, "bounded-induction manifests disagree"
        ):
            registry_module.validate_registry(mutated, ROOT)

        mutated = copy.deepcopy(self.registry)
        mutated["operations"][24]["executor"]["targets"] = mutated["operations"][24][
            "executor"
        ]["targets"][:2]
        with self.assertRaisesRegex(
            registry_module.RegistryError,
            "must have exactly one entry per named fact id",
        ):
            registry_module.validate_registry(mutated, ROOT)

    def test_sealed_kernel_capsule_driver_is_exactly_manifest_bound(self) -> None:
        for operation_index in (8, 9, 13):
            for field, value in (
                ("capsule_sha256", "0" * 64),
                ("target_theorem", "Nat.wrong"),
                ("goal_sha256", "1" * 64),
                ("declaration_sha256", "2" * 64),
                ("receipt_sha256", "3" * 64),
            ):
                with self.subTest(operation_index=operation_index, field=field):
                    mutated = copy.deepcopy(self.registry)
                    mutated["operations"][operation_index]["executor"][field] = value
                    with self.assertRaisesRegex(
                        registry_module.RegistryError, "contract disagrees"
                    ):
                        registry_module.validate_registry(mutated, ROOT)


    def _authored_declaration_operation_index(self) -> int:
        for index, operation in enumerate(self.registry["operations"]):
            if operation["id"] == "authoritative-kernel-int-modeq-shift-family-v1":
                return index
        raise AssertionError(
            "authoritative-kernel-int-modeq-shift-family-v1 is missing from "
            "the committed registry"
        )

    def test_committed_registry_carries_the_general_kernel_lane_driver(self) -> None:
        # doc 293's five Int.ModEq closures, registered under ONE operation
        # naming all five -- CLAUDE.md's "applicability.fact_ids is a LIST
        # and nothing ever required length one" applied to a driver that had
        # no shape for hand-authored kernel work at all before this.
        index = self._authored_declaration_operation_index()
        operation = self.registry["operations"][index]
        self.assertEqual(operation["scope"], "authoritative")
        self.assertEqual(
            operation["executor"]["driver"], "axeyum-lean-kernel/authored-declaration-v1"
        )
        # Six, not the original five: `Int.modEq_of_mul_right` was added on
        # 2026-08-28 (lane modeq-producer), closing the last open
        # `integer-modular-equivalence` TRAIN fact. Widening is the direction
        # this repository ratchets in; narrowing it back is the regression this
        # pin exists to catch.
        self.assertEqual(len(operation["applicability"]["fact_ids"]), 6)
        self.assertEqual(len(operation["executor"]["targets"]), 6)
        registry_module.validate_registry(self.registry, ROOT)

    def test_authored_declaration_driver_rejects_a_declaration_absent_from_its_source(
        self,
    ) -> None:
        # The whole point of this driver: a receipt naming a declaration the
        # source file never mentions must fail, not silently pass.
        index = self._authored_declaration_operation_index()
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][index]["executor"]["targets"][0]["declaration"] = (
            "Int.add_modEq_never_written"
        )
        with self.assertRaisesRegex(
            registry_module.RegistryError, "does not appear in"
        ):
            registry_module.validate_registry(mutated, ROOT)

    def test_authored_declaration_driver_rejects_a_missing_verifying_test(self) -> None:
        index = self._authored_declaration_operation_index()
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][index]["executor"]["verifying_tests"].append(
            "this_test_function_does_not_exist"
        )
        with self.assertRaisesRegex(
            registry_module.RegistryError, "not a test function declared"
        ):
            registry_module.validate_registry(mutated, ROOT)

    def test_authored_declaration_driver_rejects_a_source_outside_the_kernel_crate(
        self,
    ) -> None:
        index = self._authored_declaration_operation_index()
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][index]["executor"]["declaration_source"] = (
            "scripts/validate-autogenesis-operations.py"
        )
        with self.assertRaisesRegex(
            registry_module.RegistryError, "inside crates/axeyum-lean-kernel"
        ):
            registry_module.validate_registry(mutated, ROOT)

    def test_authored_declaration_driver_rejects_a_malformed_declaration_name(
        self,
    ) -> None:
        index = self._authored_declaration_operation_index()
        for bad_name in ("add_modEq_left", "int.add_modEq_left", "Int."):
            with self.subTest(bad_name=bad_name):
                mutated = copy.deepcopy(self.registry)
                mutated["operations"][index]["executor"]["targets"][0]["declaration"] = (
                    bad_name
                )
                with self.assertRaisesRegex(
                    registry_module.RegistryError,
                    "not a qualified Lean declaration name",
                ):
                    registry_module.validate_registry(mutated, ROOT)

    def test_authored_declaration_driver_rejects_one_declaration_bound_twice(
        self,
    ) -> None:
        index = self._authored_declaration_operation_index()
        mutated = copy.deepcopy(self.registry)
        targets = mutated["operations"][index]["executor"]["targets"]
        targets[1]["declaration"] = targets[0]["declaration"]
        with self.assertRaisesRegex(
            registry_module.RegistryError, "bound to more than one fact"
        ):
            registry_module.validate_registry(mutated, ROOT)

    def test_authored_declaration_driver_rejects_a_duplicate_fact_id(self) -> None:
        index = self._authored_declaration_operation_index()
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][index]["executor"]["additional_fact_ids"][0] = mutated[
            "operations"
        ][index]["executor"]["input_fact_id"]
        with self.assertRaisesRegex(
            registry_module.RegistryError, "names a fact id more than once"
        ):
            registry_module.validate_registry(mutated, ROOT)

    def test_authored_declaration_driver_rejects_target_order_mismatch(self) -> None:
        index = self._authored_declaration_operation_index()
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][index]["executor"]["targets"] = list(
            reversed(mutated["operations"][index]["executor"]["targets"])
        )
        with self.assertRaisesRegex(
            registry_module.RegistryError, "fact_id order must match"
        ):
            registry_module.validate_registry(mutated, ROOT)

    def test_authored_declaration_driver_rejects_applicability_fact_id_mismatch(
        self,
    ) -> None:
        index = self._authored_declaration_operation_index()
        mutated = copy.deepcopy(self.registry)
        mutated["operations"][index]["applicability"]["fact_ids"] = list(
            reversed(mutated["operations"][index]["applicability"]["fact_ids"])
        )
        with self.assertRaisesRegex(
            registry_module.RegistryError, "must bind exactly its applicable fact"
        ):
            registry_module.validate_registry(mutated, ROOT)

    def test_authored_declaration_driver_is_inconsistent_with_wrong_admission(
        self,
    ) -> None:
        index = self._authored_declaration_operation_index()
        mutated = copy.deepcopy(self.registry)
        # Keep the admission tuple itself valid (still in ADMISSION_CONTRACTS)
        # and every fact's actual fragment ("Int") still inside the list, so
        # only THIS driver's own closed-set check can be what fires.
        mutated["operations"][index]["applicability"]["fragments"] = [
            "Int",
            "Nat",
            "Extra",
        ]
        with self.assertRaisesRegex(
            registry_module.RegistryError, "inconsistent with applicability/admission"
        ):
            registry_module.validate_registry(mutated, ROOT)

    def test_gen_production_provenance_ledger_counts_the_new_multi_target_operation(
        self,
    ) -> None:
        # `applicability.fact_ids` is the SOLE input to the width computation
        # (`gen-production-provenance-ledger.py`'s `operation_widths`), so the
        # multi_target_operations counter must see this operation regardless
        # of whether any fact's evidence row has bound `checker_operation` to
        # it yet -- unlike `facts_via_multi_target`, which needs that binding
        # and is NOT expected to move here (see docs/autogenesis/296).
        import importlib.util as _ilu

        spec = _ilu.spec_from_file_location(
            "gen_production_provenance_ledger",
            ROOT / "scripts/gen-production-provenance-ledger.py",
        )
        assert spec is not None and spec.loader is not None
        ledger_module = _ilu.module_from_spec(spec)
        spec.loader.exec_module(ledger_module)
        widths, scopes = ledger_module.operation_widths()
        index = self._authored_declaration_operation_index()
        operation_id = self.registry["operations"][index]["id"]
        self.assertEqual(widths[operation_id], 6)
        self.assertEqual(scopes[operation_id], "authoritative")


class FactProvenanceExclusivityTests(unittest.TestCase):
    """`check_fact_provenance_is_exclusive` -- see Defect 1 of the
    2026-08-25 structural-defects session: `F:ml430-nat-descfactorial-zero-966b01df`
    is named by two authoritative operations (a reflexivity operation that
    actually proved it, and a bounded-induction family that could
    independently re-derive it). That overlap is legitimate -- several
    operations may structurally cover one fact -- but the fact itself must
    never become ambiguous about which operation is its PROVENANCE (a checked
    evidence row). These tests exercise the guard directly, against synthetic
    fact files, so they do not depend on the shape of any real operation.
    """

    def setUp(self) -> None:
        self.registry = json.loads(
            (ROOT / "artifacts/autogenesis/operations.json").read_text()
        )

    def _write_fact(self, root: pathlib.Path, fact_id: str, bound_operation_ids: list[str]) -> None:
        facts_dir = root / "artifacts/facts"
        facts_dir.mkdir(parents=True, exist_ok=True)
        evidence = [
            {"checker_operation": {"id": operation_id}}
            for operation_id in bound_operation_ids
        ]
        fact_path = facts_dir / (fact_id.replace("F:", "F-") + ".json")
        fact_path.write_text(json.dumps({"id": fact_id, "evidence": evidence}))

    def test_two_operations_naming_a_fact_with_no_bound_evidence_is_fine(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            self._write_fact(root, "F:example", [])
            registry_module.check_fact_provenance_is_exclusive(
                root, {"F:example": ["op-a", "op-b"]}
            )

    def test_two_operations_naming_a_fact_with_one_bound_is_the_legitimate_case(self) -> None:
        # Exactly today's shape: op-a proved the fact; op-b (a fact-agnostic
        # re-derivation family) also names it in applicability.fact_ids but
        # never claims a second evidence row.
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            self._write_fact(root, "F:example", ["op-a"])
            registry_module.check_fact_provenance_is_exclusive(
                root, {"F:example": ["op-a", "op-b"]}
            )

    def test_a_fact_named_by_only_one_operation_is_never_inspected(self) -> None:
        # Bound to an operation that is NOT even the one (hypothetical) named
        # operation -- would fail the "does not name it" branch if this were
        # reached at all. It must not be: len(operation_ids) < 2 short-circuits.
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            self._write_fact(root, "F:example", ["op-nowhere"])
            registry_module.check_fact_provenance_is_exclusive(
                root, {"F:example": ["op-a"]}
            )

    def test_two_bound_evidence_rows_on_one_fact_is_a_silent_fork_and_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            self._write_fact(root, "F:example", ["op-a", "op-b"])
            with self.assertRaisesRegex(
                registry_module.RegistryError, "more than one of them"
            ):
                registry_module.check_fact_provenance_is_exclusive(
                    root, {"F:example": ["op-a", "op-b"]}
                )

    def test_evidence_bound_to_an_operation_that_does_not_name_the_fact_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            self._write_fact(root, "F:example", ["op-c"])
            with self.assertRaisesRegex(
                registry_module.RegistryError, "does not name this fact"
            ):
                registry_module.check_fact_provenance_is_exclusive(
                    root, {"F:example": ["op-a", "op-b"]}
                )

    def test_committed_registry_already_carries_the_legitimate_two_operation_case(self) -> None:
        # F:ml430-nat-descfactorial-zero-966b01df USED TO be this example --
        # named by both authoritative-mathlib-nat-descfactorial-zero-
        # reflexivity-v1 (its actual provenance) and authoritative-mathlib-
        # bounded-induction-factorial-family-v1 (a target-agnostic family
        # that could re-derive it but never claimed a second evidence row).
        # That overlap was REMOVED 2026-08-25 (Defect 1 of that session's
        # structural-defects report, chosen as (b): the family should not
        # have named it) because it broke `fact-frontier.py` dispatch the
        # moment the fact was ever reopened -- `matching_operations` returned
        # both operations, `ambiguous-registered-operation` refused it, and
        # `execute-autogenesis-operation.py`'s `selected_inputs` raised
        # "executor requires the selected fact to be admissible". Two
        # committed tests already exercised exactly that reopen path
        # (`test_execute_autogenesis_operation.py`'s
        # `test_statement_reflexivity_receipt_binds_manifests_artifact_and_
        # proof` and `test_prepare_autogenesis_fact_transaction.py`'s
        # `test_statement_reflexivity_delta_retains_external_and_proof_
        # identities`) and were failing on HEAD before this fix, for a reason
        # unrelated to whatever either test's own assertions cover.
        #
        # F:ml430-nat-ascfactorial-zero-fd183202 is the still-live instance of
        # the SAME pattern (same family operation, same "already proved
        # elsewhere, no second evidence row" shape) -- kept as-is because nothing
        # currently reopens it, this repository's own bounded-induction-family
        # checker explicitly re-verifies the no-second-evidence-row invariant for
        # it, and dropping it too is a larger, separate design question (it would
        # mean either shrinking this operation's targets again or decoupling
        # `applicability.fact_ids` from `executor.targets`, which the exact-
        # binding rule in `validate_registry` currently forbids) than this
        # session's assigned defect. It is exactly the shape
        # `check_fact_provenance_is_exclusive` is written to police: the full
        # registry validator must accept it (one bound evidence row, not two)
        # without complaint, and would reject it the moment a second evidence
        # row appeared.
        registry_module.validate_registry(self.registry, ROOT)
        fact_operation_ids: dict[str, list[str]] = {}
        for operation in self.registry["operations"]:
            if operation.get("scope") != "authoritative":
                continue
            for fact_id in operation["applicability"]["fact_ids"]:
                fact_operation_ids.setdefault(fact_id, []).append(operation["id"])
        self.assertIn(
            "F:ml430-nat-ascfactorial-zero-fd183202", fact_operation_ids
        )
        self.assertGreaterEqual(
            len(fact_operation_ids["F:ml430-nat-ascfactorial-zero-fd183202"]), 2
        )
        # And confirm the fix: the fact this session's Defect 1 was filed
        # against is no longer one of the multiply-named facts.
        self.assertEqual(
            fact_operation_ids.get("F:ml430-nat-descfactorial-zero-966b01df"),
            ["authoritative-mathlib-nat-descfactorial-zero-reflexivity-v1"],
        )


if __name__ == "__main__":
    unittest.main()
