"""Controls for `scripts/validate-correspondences.py`.

One test per guard, each over a document that violates exactly ONE rule. A
fixture breaking several rules at once could not tell you which guard caught it
and -- because this suite is registered in `scripts/tests/mutation_controls.py`
under ``correspondences`` -- would let a guard be deleted while more than one
test died, which the harness reports as an ambiguous result rather than as
coverage.

Each test calls the specific check function rather than the whole validator, so
a mutation to one guard cannot reach another test's assertion.

Three tests are deliberately blunt and are NOT part of the 1:1 mapping: the
committed corpus passes, a document violating many rules fails, and the summary
counts every vocabulary term including the ones nobody has instantiated. None of
them can be killed by removing a single guard.

Two fixtures are drawn from the COMMITTED ledger rather than invented:

  * the `depends_on` refusal uses `F:ml430-nat-fib-add-two` /
    `F:ml430-int-fib-add-two`, a real pair that looks exactly like a
    carrier-transport correspondence and is a proof dependency;
  * the carrier-erasure refusal pairs `Nat.fib_gcd` against `Int.fib_eq_zero`,
    two real facts that are genuinely not the same law.

A synthetic fixture would have proved the guard runs. These prove it discriminates
between cases the repository actually contains.
"""

from __future__ import annotations

import copy
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/validate-correspondences.py"

_spec = importlib.util.spec_from_file_location("validate_correspondences", SCRIPT)
assert _spec is not None and _spec.loader is not None
checker = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(checker)

BASE = ROOT / "artifacts/correspondences/X-fib-eq-zero-across-nat-and-int.json"


def load() -> dict:
    return json.loads(BASE.read_text(encoding="utf-8"))


FACTS = checker.load_facts()
DECLARATIONS = checker.load_kernel_declarations()
CLOSURE = checker.dependency_closure(FACTS)


def endpoints_of(document: dict) -> tuple[dict, dict]:
    return FACTS[document["endpoints"][0]], FACTS[document["endpoints"][1]]


class Vacuity(unittest.TestCase):
    """An empty population must fail. A gate with no subject cannot fail."""

    def test_an_empty_correspondence_directory_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            with self.assertRaises(checker.CorrespondenceError):
                checker.validate(Path(scratch))

    def test_an_empty_fact_ledger_fails_closed(self) -> None:
        original = checker.FACTS
        with tempfile.TemporaryDirectory() as scratch:
            checker.FACTS = Path(scratch)
            try:
                with self.assertRaises(checker.CorrespondenceError):
                    checker.load_facts()
            finally:
                checker.FACTS = original


class NotADependency(unittest.TestCase):
    """The rule the whole artifact exists for."""

    def test_a_pair_the_ledger_already_links_is_refused(self) -> None:
        document = load()
        document["endpoints"] = [
            "F:ml430-nat-fib-add-two-b86e0c82",
            "F:ml430-int-fib-add-two-739358dd",
        ]
        problems: list[str] = []
        checker.check_endpoints(document, "fixture", FACTS, CLOSURE, problems)
        self.assertTrue(any("depends_on" in p for p in problems), problems)

    def test_the_committed_pair_is_not_linked_by_depends_on(self) -> None:
        problems: list[str] = []
        checker.check_endpoints(load(), "fixture", FACTS, CLOSURE, problems)
        self.assertEqual(problems, [])


class EndpointRules(unittest.TestCase):
    def test_a_self_loop_is_refused(self) -> None:
        document = load()
        document["endpoints"] = [document["endpoints"][0], document["endpoints"][0]]
        problems: list[str] = []
        checker.check_endpoints(document, "fixture", FACTS, CLOSURE, problems)
        self.assertTrue(any("same fact" in p for p in problems), problems)

    def test_an_endpoint_that_is_not_a_fact_is_refused(self) -> None:
        document = load()
        document["endpoints"] = [document["endpoints"][0], "F:no-such-fact-anywhere"]
        problems: list[str] = []
        checker.check_endpoints(document, "fixture", FACTS, CLOSURE, problems)
        self.assertTrue(any("not facts in the ledger" in p for p in problems), problems)

    def test_an_unsettled_endpoint_is_refused(self) -> None:
        document = load()
        document["endpoints"] = [
            "F:ml430-nat-fib-eq-zero-61879073",
            "F:ml430-int-fib-of-odd-66560495",
        ]
        problems: list[str] = []
        checker.check_endpoints(document, "fixture", FACTS, CLOSURE, problems)
        self.assertTrue(any("until both are settled" in p for p in problems), problems)

    def test_two_identical_formal_statements_are_a_duplicate_not_a_correspondence(self) -> None:
        facts = copy.deepcopy(FACTS)
        left, right = load()["endpoints"]
        facts[right]["formal"]["statement"] = facts[left]["formal"]["statement"]
        problems: list[str] = []
        checker.check_endpoints(load(), "fixture", facts, CLOSURE, problems)
        self.assertTrue(any("duplicate" in p for p in problems), problems)


class CarrierTransport(unittest.TestCase):
    """The structural check: erase the carrier, compare the strings."""

    def test_two_facts_in_one_fragment_are_not_a_transport(self) -> None:
        document = load()
        left = FACTS["F:ml430-nat-fib-eq-zero-61879073"]
        problems: list[str] = []
        checker.check_kind_rules(document, "fixture", left, left, problems)
        self.assertTrue(any("One carrier is not a transport" in p for p in problems), problems)

    def test_a_fragment_with_no_carrier_spelling_fails_closed(self) -> None:
        document = load()
        left, right = endpoints_of(document)
        left = copy.deepcopy(left)
        left["formal"]["fragment"] = "QF_FP"
        problems: list[str] = []
        checker.check_kind_rules(document, "fixture", left, right, problems)
        self.assertTrue(any("no carrier spelling" in p for p in problems), problems)

    def test_two_different_laws_do_not_survive_carrier_erasure(self) -> None:
        document = load()
        left = FACTS["F:ml430-nat-fib-gcd-d1d98407"]
        right = FACTS["F:ml430-int-fib-eq-zero-8193c7cb"]
        problems: list[str] = []
        checker.check_kind_rules(document, "fixture", left, right, problems)
        self.assertTrue(any("two different statements" in p for p in problems), problems)

    def test_the_committed_pair_survives_carrier_erasure(self) -> None:
        document = load()
        left, right = endpoints_of(document)
        problems: list[str] = []
        checker.check_kind_rules(document, "fixture", left, right, problems)
        self.assertEqual(problems, [])


class IndependentFormalization(unittest.TestCase):
    def test_two_facts_on_one_proof_route_are_one_formalization(self) -> None:
        document = load()
        document["correspondence_kind"] = "independent-formalization"
        left, right = endpoints_of(document)
        problems: list[str] = []
        checker.check_kind_rules(document, "fixture", left, right, problems)
        self.assertTrue(any("DIFFERENT routes" in p for p in problems), problems)


class Specialization(unittest.TestCase):
    def test_a_specialization_with_no_route_is_refused(self) -> None:
        document = load()
        document["correspondence_kind"] = "specialization"
        document["derivation_status"] = "asserted"
        left, right = endpoints_of(document)
        problems: list[str] = []
        checker.check_kind_rules(document, "fixture", left, right, problems)
        self.assertTrue(any("without the argument" in p for p in problems), problems)


    def test_a_specialization_whose_every_via_ref_is_null_is_refused(self) -> None:
        """The rule above only refuses an EMPTY route; this refuses an empty one
        dressed as prose. Found by a lane using the gate, not by the gate."""
        document = load()
        document["correspondence_kind"] = "specialization"
        document["derivation_status"] = "route-recorded"
        document["via"] = [{"step": "instantiate the general form at n = 2", "ref": None}]
        left, right = endpoints_of(document)
        problems: list[str] = []
        checker.check_kind_rules(document, "fixture", left, right, problems)
        self.assertTrue(any("not one of them names a `ref`" in p for p in problems), problems)

    def test_a_specialization_with_one_real_ref_among_nulls_is_accepted(self) -> None:
        """The discriminating half: null refs are legitimate for prose steps, so
        the rule must fire on ALL-null and not on ANY-null."""
        document = load()
        document["correspondence_kind"] = "specialization"
        document["derivation_status"] = "route-recorded"
        document["via"] = [
            {"step": "rearrange", "ref": None},
            {"step": "instantiate", "ref": "kernel:Int.fib_cassini"},
        ]
        left, right = endpoints_of(document)
        problems: list[str] = []
        checker.check_kind_rules(document, "fixture", left, right, problems)
        self.assertEqual(problems, [])

    def test_a_specialization_whose_via_ref_is_blank_is_refused(self) -> None:
        """`""` is a string, so an `isinstance(..., str)` test alone passes it."""
        document = load()
        document["correspondence_kind"] = "specialization"
        document["derivation_status"] = "route-recorded"
        document["via"] = [{"step": "instantiate", "ref": "   "}]
        left, right = endpoints_of(document)
        problems: list[str] = []
        checker.check_kind_rules(document, "fixture", left, right, problems)
        self.assertTrue(any("not one of them names a `ref`" in p for p in problems), problems)


class KernelSpelling(unittest.TestCase):
    """`AxNat` is the kernel's spelling of the CONSTRUCTED naturals -- the `Ax`
    is *axeyum*, not *axiomatised*. Without it in CARRIERS the word-boundary
    erasure can never fire on a kernel-spelled statement, because the `x`
    defeats `(?<![A-Za-z])Nat`, and every such transport fails closed."""

    def test_axnat_is_erased_as_the_nat_carrier(self) -> None:
        self.assertEqual(
            checker.erase_carrier("AxNat.add is commutative", "Nat"),
            f"{checker.CARRIER_PLACEHOLDER}.add is commutative",
        )

    def test_a_kernel_spelled_transport_survives_erasure(self) -> None:
        """The end-to-end consequence, not just the helper: the same law over
        two carriers, each written the way the kernel renders it."""
        document = load()
        left, right = endpoints_of(document)
        left = copy.deepcopy(left)
        right = copy.deepcopy(right)
        left["formal"]["fragment"] = "Nat"
        right["formal"]["fragment"] = "Int"
        left["formal"]["statement"] = "for every n, AxNat.fib n is a AxNat"
        right["formal"]["statement"] = "for every n, Int.fib n is a Int"
        problems: list[str] = []
        checker.check_kind_rules(document, "fixture", left, right, problems)
        self.assertEqual(problems, [])

    def test_axreal_is_not_erased_as_the_nat_carrier(self) -> None:
        """The discriminating case. `AxReal` IS an axiomatisation -- 30 assumed
        laws -- and a genuinely different carrier from `AxNat`. Erasing one as
        the other would call an axiom-free theorem and an axiom-bearing one the
        same law."""
        self.assertEqual(
            checker.erase_carrier("AxReal.add is commutative", "Nat"),
            "AxReal.add is commutative",
        )


class DerivationBacking(unittest.TestCase):
    """`derivation_status` must be earned by what is in the document."""

    def test_asserted_with_a_route_is_a_contradiction(self) -> None:
        document = load()
        document["derivation_status"] = "asserted"
        document["external_status"] = "classical"
        document["evidence"] = []
        problems: list[str] = []
        checker.check_backing(document, "fixture", FACTS, DECLARATIONS, problems)
        self.assertTrue(any("no route is written down" in p for p in problems), problems)

    def test_a_via_step_naming_no_fact_is_refused(self) -> None:
        document = load()
        document["via"] = [{"step": "a step long enough to pass the floor", "ref": "F:no-such-fact"}]
        problems: list[str] = []
        checker.check_backing(document, "fixture", FACTS, DECLARATIONS, problems)
        self.assertTrue(any("not a fact in the ledger" in p for p in problems), problems)

    def test_a_via_step_naming_an_unobserved_kernel_declaration_is_refused(self) -> None:
        document = load()
        document["via"] = [
            {"step": "a step long enough to pass the floor", "ref": "kernel:Rat.det2_mul"}
        ]
        problems: list[str] = []
        checker.check_backing(document, "fixture", FACTS, DECLARATIONS, problems)
        self.assertTrue(any("kernel projection has observed" in p for p in problems), problems)

    def test_a_via_ref_that_is_neither_shape_is_refused(self) -> None:
        document = load()
        document["via"] = [{"step": "a step long enough to pass the floor", "ref": "Rat.det2_mul"}]
        problems: list[str] = []
        checker.check_backing(document, "fixture", FACTS, DECLARATIONS, problems)
        self.assertTrue(any("neither an F: fact id" in p for p in problems), problems)

    def test_mechanized_here_with_a_missing_step_is_refused(self) -> None:
        document = load()
        document["derivation_status"] = "mechanized-here"
        document["evidence"] = [
            {
                "kind": "kernel-term",
                "supports": "a supports string long enough to clear the schema floor",
                "checker_command": "true",
                "artifact": "x",
            }
        ]
        problems: list[str] = []
        checker.check_backing(document, "fixture", FACTS, DECLARATIONS, problems)
        self.assertTrue(any("not mechanized" in p for p in problems), problems)

    def test_mechanized_here_with_no_evidence_is_refused(self) -> None:
        document = load()
        document["derivation_status"] = "mechanized-here"
        document["via"] = [s for s in document["via"] if s["ref"] is not None]
        document["evidence"] = []
        problems: list[str] = []
        checker.check_backing(document, "fixture", FACTS, DECLARATIONS, problems)
        self.assertTrue(any("must name the command" in p for p in problems), problems)

    def test_evidence_without_a_checker_command_is_refused(self) -> None:
        document = load()
        document["derivation_status"] = "mechanized-here"
        document["via"] = [s for s in document["via"] if s["ref"] is not None]
        document["evidence"] = [
            {
                "kind": "kernel-term",
                "supports": "a supports string long enough to clear the schema floor",
                "checker_command": "   ",
                "artifact": "x",
            }
        ]
        problems: list[str] = []
        checker.check_backing(document, "fixture", FACTS, DECLARATIONS, problems)
        self.assertTrue(any("no checker_command" in p for p in problems), problems)

    def test_evidence_under_a_weaker_status_is_refused(self) -> None:
        document = load()
        document["evidence"] = [
            {
                "kind": "kernel-term",
                "supports": "a supports string long enough to clear the schema floor",
                "checker_command": "true",
                "artifact": "x",
            }
        ]
        problems: list[str] = []
        checker.check_backing(document, "fixture", FACTS, DECLARATIONS, problems)
        self.assertTrue(any("is the contradiction" in p for p in problems), problems)

    def test_novel_here_without_a_mechanized_derivation_is_refused(self) -> None:
        document = load()
        document["external_status"] = "novel-here"
        problems: list[str] = []
        checker.check_backing(document, "fixture", FACTS, DECLARATIONS, problems)
        self.assertTrue(any("pure tone" in p for p in problems), problems)


class Prose(unittest.TestCase):
    """Floors set from measured practice next door, not from a round number."""

    def test_a_short_claim_is_refused(self) -> None:
        document = load()
        document["claim"] = "they are the same"
        problems: list[str] = []
        checker.check_prose(document, "fixture", problems)
        self.assertTrue(any("claim is shorter" in p for p in problems), problems)

    def test_a_short_transport_is_refused(self) -> None:
        document = load()
        document["transport"] = "a cast"
        problems: list[str] = []
        checker.check_prose(document, "fixture", problems)
        self.assertTrue(any("transport is shorter" in p for p in problems), problems)

    def test_a_transport_copied_from_the_claim_is_refused(self) -> None:
        document = load()
        document["transport"] = document["claim"]
        problems: list[str] = []
        checker.check_prose(document, "fixture", problems)
        self.assertTrue(any("different questions" in p for p in problems), problems)


class Identity(unittest.TestCase):
    def test_a_filename_that_disagrees_with_the_id_is_refused(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            path = Path(scratch) / "X-wrong-name.json"
            path.write_text(json.dumps(load()), encoding="utf-8")
            problems, _ = checker.validate(Path(scratch))
            self.assertTrue(any("implies filename" in p for p in problems), problems)

    def test_a_duplicate_id_is_refused(self) -> None:
        # Two files cannot share a filename, so the clash carries a DIFFERENT
        # endpoint pair: that keeps the duplicate-pair guard quiet, and the
        # assertion below names only the duplicate-id message, so the
        # filename guard's mutation cannot kill this test either.
        with tempfile.TemporaryDirectory() as scratch:
            first = load()
            (Path(scratch) / (first["id"].replace("X:", "X-", 1) + ".json")).write_text(
                json.dumps(first), encoding="utf-8"
            )
            clash = load()
            clash["endpoints"] = [
                "F:ml430-nat-fib-dvd-f80f3de1",
                "F:ml430-int-fib-dvd-ffb3c5c1",
            ]
            (Path(scratch) / "X-clash.json").write_text(json.dumps(clash), encoding="utf-8")
            problems, _ = checker.validate(Path(scratch))
            self.assertTrue(any("duplicate id" in p for p in problems), problems)

    def test_a_second_adjudication_of_one_pair_is_refused(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            first = load()
            second = load()
            second["id"] = "X:second-opinion"
            for document in (first, second):
                name = document["id"].replace("X:", "X-", 1) + ".json"
                (Path(scratch) / name).write_text(json.dumps(document), encoding="utf-8")
            problems, _ = checker.validate(Path(scratch))
            self.assertTrue(any("one adjudication per pair" in p for p in problems), problems)


class Structure(unittest.TestCase):
    """Shape and enum membership. One violation per fixture, as above."""

    def check(self, mutate) -> list[str]:
        document = load()
        mutate(document)
        problems: list[str] = []
        checker.check_structure(document, "fixture", problems)
        return problems

    def test_an_unknown_key_is_refused(self) -> None:
        problems = self.check(lambda d: d.__setitem__("bridges_to", []))
        self.assertTrue(any("unknown key" in p for p in problems), problems)

    def test_a_missing_required_key_is_refused(self) -> None:
        problems = self.check(lambda d: d.pop("transport"))
        self.assertTrue(any("missing required key" in p for p in problems), problems)

    def test_a_wrong_schema_version_is_refused(self) -> None:
        problems = self.check(lambda d: d.__setitem__("schema_version", 2))
        self.assertTrue(any("schema_version must be 1" in p for p in problems), problems)

    def test_a_wrong_kind_is_refused(self) -> None:
        problems = self.check(lambda d: d.__setitem__("kind", "axeyum-fact"))
        self.assertTrue(any("kind must be" in p for p in problems), problems)

    def test_an_id_outside_the_pattern_is_refused(self) -> None:
        problems = self.check(lambda d: d.__setitem__("id", "F:not-a-correspondence"))
        self.assertTrue(any("id must match" in p for p in problems), problems)

    def test_an_unknown_correspondence_kind_is_refused(self) -> None:
        problems = self.check(lambda d: d.__setitem__("correspondence_kind", "bridges-to"))
        self.assertTrue(any("correspondence_kind must be" in p for p in problems), problems)

    def test_an_unknown_derivation_status_is_refused(self) -> None:
        problems = self.check(lambda d: d.__setitem__("derivation_status", "obvious"))
        self.assertTrue(any("derivation_status must be" in p for p in problems), problems)

    def test_an_unknown_external_status_is_refused(self) -> None:
        problems = self.check(lambda d: d.__setitem__("external_status", "well-known"))
        self.assertTrue(any("external_status must be" in p for p in problems), problems)

    def test_a_correspondence_with_three_endpoints_is_refused(self) -> None:
        problems = self.check(lambda d: d["endpoints"].append("F:ml430-nat-fib-pos-9e67bd8e"))
        self.assertTrue(any("exactly two fact ids" in p for p in problems), problems)

    def test_an_endpoint_outside_the_fact_pattern_is_refused(self) -> None:
        problems = self.check(lambda d: d["endpoints"].__setitem__(1, "Int.fib_eq_zero"))
        self.assertTrue(any("every endpoint must match" in p for p in problems), problems)

    def test_a_via_that_is_not_an_array_is_refused(self) -> None:
        problems = self.check(lambda d: d.__setitem__("via", "two steps"))
        self.assertTrue(any("must be arrays" in p for p in problems), problems)

    def test_a_malformed_provenance_date_is_refused(self) -> None:
        problems = self.check(lambda d: d["provenance"].__setitem__("date", "August 2026"))
        self.assertTrue(any("provenance.date" in p for p in problems), problems)

    def test_provenance_with_no_sources_is_refused(self) -> None:
        problems = self.check(lambda d: d["provenance"].__setitem__("sources", []))
        self.assertTrue(any("at least one file" in p for p in problems), problems)


class Blunt(unittest.TestCase):
    """Not part of the 1:1 mapping: no single deletion can kill these."""

    def test_the_committed_corpus_passes(self) -> None:
        problems, summary = checker.validate()
        self.assertEqual(problems, [])
        self.assertGreater(summary["correspondences"], 0)
        self.assertGreater(summary["facts"], 0)

    def test_a_document_violating_many_rules_fails(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            document = load()
            document["claim"] = "no"
            document["transport"] = "no"
            document["derivation_status"] = "asserted"
            document["external_status"] = "novel-here"
            # The endpoints stay REAL on purpose. Naming two nonexistent facts
            # here would make this blunt test die alongside the endpoint guard's
            # own control, which is the ambiguous result the 1:1 mapping exists
            # to avoid -- measured, it killed 2.
            (Path(scratch) / "X-fib-eq-zero-across-nat-and-int.json").write_text(
                json.dumps(document), encoding="utf-8"
            )
            problems, _ = checker.validate(Path(scratch))
            self.assertGreater(len(problems), 2)

    def test_the_summary_reports_every_vocabulary_term_including_the_zeroes(self) -> None:
        _, summary = checker.validate()
        self.assertEqual(set(summary["kinds"]), set(checker.KINDS))
        self.assertEqual(set(summary["derivations"]), set(checker.DERIVATION_STATUSES))
        self.assertEqual(set(summary["externals"]), set(checker.EXTERNAL_STATUSES))


if __name__ == "__main__":
    unittest.main()
