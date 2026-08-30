#!/usr/bin/env python3
"""Mutation controls for the must-decline-population census gate.

Every guard below has a nonempty killed-set, and no two guards share a
killed-set member -- deleting any one guard kills a different, disjoint set
of these tests, so none can be removed while the suite stays green.

    file-missing            -> {a_missing_nursery_is_an_error,
                                 a_missing_ground_truth_is_an_error,
                                 a_missing_census_is_an_error}
    file-unreadable         -> {an_unreadable_nursery_is_an_error,
                                 an_unreadable_ground_truth_is_an_error,
                                 an_unreadable_census_is_an_error}
    vacuity (empty subject) -> {an_empty_must_decline_population_is_an_error}
    census-schema           -> {a_census_missing_admissible_proofs_is_rejected}
    set-mismatch (extra)    -> {ground_truth_naming_an_extra_fact_id_is_rejected,
                                 ground_truth_smuggling_a_held_out_fact_id_is_rejected}
    set-mismatch (missing)  -> {ground_truth_missing_a_must_decline_fact_id_is_rejected}
    unrecognized check_kind -> {an_unrecognized_check_kind_is_rejected}
    witness-eval-error      -> {a_witness_missing_a_required_field_fails_closed}
    witness-not-refuting    -> {a_witness_that_does_not_refute_is_rejected}
    must-decline-admitted   -> {a_census_admitting_a_must_decline_fact_is_void}

The discriminating controls matter more than the failing ones: a gate that
voids every census is as useless as one that voids none.
`test_a_clean_synthetic_census_passes` and
`test_the_committed_repository_passes` show the PASS side; without them a
constant-FAIL gate would look identical to a working one.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-autogenesis-must-decline-population.py"
SPEC = importlib.util.spec_from_file_location("must_decline_population", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
guard = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(guard)

TRAIN_ID = "F:fixture-mutation-train-0000beef"
DEV_ID = "F:fixture-mutation-dev-0000cafe"
HELD_ID = "F:fixture-mutation-held-0000dead"
EXTERNAL_ID = "F:fixture-external-not-a-mutation"


def base_nursery() -> dict:
    return {
        "entries": [
            {
                "fact_id": TRAIN_ID,
                "partition": "train",
                "provenance_class": "generated-mutation",
            },
            {
                "fact_id": DEV_ID,
                "partition": "development",
                "provenance_class": "generated-mutation",
            },
            {
                "fact_id": HELD_ID,
                "partition": "held-out",
                "provenance_class": "generated-mutation",
            },
            {
                "fact_id": EXTERNAL_ID,
                "partition": "train",
                "provenance_class": "external-transcribed",
            },
        ]
    }


def base_ground_truth() -> dict:
    return {
        "entries": [
            {
                "fact_id": TRAIN_ID,
                "check_kind": "factorial_polarity_reversed",
                "witness": {"n": 0},
            },
            {
                "fact_id": DEV_ID,
                "check_kind": "coprime_polarity_reversed",
                "witness": {"a": 0, "b": 0},
            },
        ]
    }


def base_census(admissible: list[dict] | None = None) -> dict:
    return {"admissible_proofs": admissible if admissible is not None else []}


class MustDeclinePopulationTests(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self._tmp.name)
        self.nursery = self.root / "nursery.json"
        self.ground_truth = self.root / "ground-truth.json"
        self.census = self.root / "census.json"
        self.write(self.nursery, base_nursery())
        self.write(self.ground_truth, base_ground_truth())
        self.write(self.census, base_census())

    def tearDown(self) -> None:
        self._tmp.cleanup()

    @staticmethod
    def write(path: pathlib.Path, value: object) -> None:
        path.write_text(json.dumps(value))

    def argv(self) -> list[str]:
        return [
            "--nursery",
            str(self.nursery),
            "--ground-truth",
            str(self.ground_truth),
            "--census",
            str(self.census),
        ]

    def run_guard(self, argv: list[str] | None = None) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = guard.main(argv if argv is not None else self.argv())
        return code, out.getvalue(), err.getvalue()

    # --- the clean state, and the real repository ------------------------
    def test_a_clean_synthetic_census_passes(self) -> None:
        code, out, err = self.run_guard()
        self.assertEqual(code, 0, err)
        self.assertIn("verdict=PASS", out)
        self.assertIn("must_decline=2", out)
        self.assertIn("ground_truth_verified=2", out)

    def test_the_committed_repository_passes(self) -> None:
        code, out, err = self.run_guard([])
        self.assertEqual(code, 0, err)
        self.assertIn("verdict=PASS", out)
        # Pinned at 11, raised from 10 on 2026-08-30. The ADR-0542 amendment
        # moved `natural-logarithm` out of held-out, which correctly brought
        # its generated-mutation row into the population (`partition !=
        # 'held-out'`) and left the ground truth behind; f74325fb5 supplied
        # the missing witness. One mutation row remains held-out
        # (`natural-square-root`, the only surviving v1 blind family) and is
        # deliberately still absent.
        # A drop would mean a mutation row silently left the population; a
        # rise means a new one was added without extending the ground truth
        # (which would already fail via the set-mismatch guard).
        self.assertIn("must_decline=11", out)
        self.assertIn("ground_truth_verified=11", out)

    # --- guard: every input file must exist -------------------------------
    def test_a_missing_nursery_is_an_error(self) -> None:
        self.nursery.unlink()
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertNotIn("verdict=PASS", out)
        self.assertIn("nursery manifest is missing", err)

    def test_a_missing_ground_truth_is_an_error(self) -> None:
        self.ground_truth.unlink()
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertNotIn("verdict=PASS", out)
        self.assertIn("ground-truth artifact is missing", err)

    def test_a_missing_census_is_an_error(self) -> None:
        self.census.unlink()
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertNotIn("verdict=PASS", out)
        self.assertIn("census is missing", err)

    # --- guard: every input file must parse as JSON ------------------------
    def test_an_unreadable_nursery_is_an_error(self) -> None:
        self.nursery.write_text("{not json")
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertNotIn("verdict=PASS", out)
        self.assertIn("nursery manifest is unreadable", err)

    def test_an_unreadable_ground_truth_is_an_error(self) -> None:
        self.ground_truth.write_text("{not json")
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertNotIn("verdict=PASS", out)
        self.assertIn("ground-truth artifact is unreadable", err)

    def test_an_unreadable_census_is_an_error(self) -> None:
        self.census.write_text("{not json")
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertNotIn("verdict=PASS", out)
        self.assertIn("census is unreadable", err)

    # --- guard: an empty must-decline population is a fail-closed error ----
    def test_an_empty_must_decline_population_is_an_error(self) -> None:
        self.write(
            self.nursery,
            {
                "entries": [
                    {
                        "fact_id": EXTERNAL_ID,
                        "partition": "train",
                        "provenance_class": "external-transcribed",
                    }
                ]
            },
        )
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertNotIn("verdict=PASS", out)
        self.assertIn("must-decline population is empty", err)

    # --- guard: an unrecognized census schema is rejected -------------------
    def test_a_census_missing_admissible_proofs_is_rejected(self) -> None:
        self.write(self.census, {"coverage": {"admissible-proof": 0}})
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertNotIn("verdict=PASS", out)
        self.assertIn("not recognized", err)

    # --- guard: ground truth must exactly name the must-decline population -
    def test_ground_truth_naming_an_extra_fact_id_is_rejected(self) -> None:
        gt = base_ground_truth()
        gt["entries"].append(
            {
                "fact_id": EXTERNAL_ID,
                "check_kind": "factorial_polarity_reversed",
                "witness": {"n": 0},
            }
        )
        self.write(self.ground_truth, gt)
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertNotIn("verdict=PASS", out)
        self.assertIn("outside the current must-decline population", err)

    def test_ground_truth_smuggling_a_held_out_fact_id_is_rejected(self) -> None:
        """A held-out fact id has no legitimate reason to be in this artifact
        at all -- it is never in the must-decline set the nursery computes, so
        including it is caught as an ordinary 'extra' entry. This is what
        stands between the ground-truth artifact and the held-out isolation
        breach this programme has already suffered once."""
        gt = base_ground_truth()
        gt["entries"].append(
            {
                "fact_id": HELD_ID,
                "check_kind": "factorial_polarity_reversed",
                "witness": {"n": 0},
            }
        )
        self.write(self.ground_truth, gt)
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertNotIn("verdict=PASS", out)
        self.assertIn("outside the current must-decline population", err)
        self.assertIn(HELD_ID, err)

    def test_ground_truth_missing_a_must_decline_fact_id_is_rejected(self) -> None:
        gt = base_ground_truth()
        gt["entries"] = [gt["entries"][0]]  # drop DEV_ID
        self.write(self.ground_truth, gt)
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertNotIn("verdict=PASS", out)
        self.assertIn("is missing fact id(s)", err)
        self.assertIn(DEV_ID, err)

    # --- guard: every witness must be checkable and must actually refute ---
    def test_an_unrecognized_check_kind_is_rejected(self) -> None:
        gt = base_ground_truth()
        gt["entries"][0]["check_kind"] = "not-a-real-check"
        self.write(self.ground_truth, gt)
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertNotIn("verdict=PASS", out)
        self.assertIn("unrecognized check_kind", err)

    def test_a_witness_missing_a_required_field_fails_closed(self) -> None:
        gt = base_ground_truth()
        gt["entries"][0]["witness"] = {}  # factorial_polarity_reversed needs "n"
        self.write(self.ground_truth, gt)
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertNotIn("verdict=PASS", out)
        self.assertIn("could not be evaluated", err)

    def test_a_witness_that_does_not_refute_is_rejected(self) -> None:
        gt = base_ground_truth()
        # 0 ||| 0 == 0 &&& 0 == 0: this witness does NOT refute the (wrong)
        # check_kind swapped in here, which is exactly what the guard must
        # catch -- a ground-truth row whose "counterexample" is not one.
        gt["entries"][0]["check_kind"] = "bitwise_operator_substituted"
        gt["entries"][0]["witness"] = {"n": 0, "m": 0}
        self.write(self.ground_truth, gt)
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertNotIn("verdict=PASS", out)
        self.assertIn("does NOT refute", err)

    # --- the headline guard: an admitted must-decline row voids the census -
    def test_a_census_admitting_a_must_decline_fact_is_void(self) -> None:
        self.write(
            self.census,
            base_census([{"fact_id": TRAIN_ID, "ledger_state_during_census": "open"}]),
        )
        code, out, err = self.run_guard()
        self.assertEqual(code, 1)
        self.assertIn("verdict=FAIL", out)
        self.assertIn("violations=1", out)
        self.assertIn("must-decline-fact-admitted", err)
        self.assertIn(TRAIN_ID, err)

    def test_an_admissible_proof_for_an_unrelated_fact_still_passes(self) -> None:
        """The discriminating other half of the guard above: admitting
        something that is NOT in the must-decline population must not void
        the census. A gate that flags every admission would be useless."""
        self.write(
            self.census,
            base_census(
                [{"fact_id": EXTERNAL_ID, "ledger_state_during_census": "proved"}]
            ),
        )
        code, out, err = self.run_guard()
        self.assertEqual(code, 0, err)
        self.assertIn("verdict=PASS", out)



class MustDeclineLedgerGuardTests(unittest.TestCase):
    """The census and the ledger are two doors into the same room.

    Added 2026-08-22 after a mutation showed the census guard alone was not
    enough: marking the known-false `n! = 0` as `proved` with a forged-but-
    well-formed evidence row passed `validate-facts.py`, this gate, the held-out
    isolation gate and the nursery gate -- four green checks over a statement
    refuted by `0! = 1`.
    """

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.facts = pathlib.Path(self._tmp.name)
        self.fact_id = "F:ml430-mutation-deadbeef"
        self.path = self.facts / "F-ml430-mutation-deadbeef.json"

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def write(self, status: str) -> None:
        self.path.write_text(json.dumps({"id": self.fact_id, "epistemic_status": status}))

    def test_a_settled_must_decline_fact_is_a_violation(self) -> None:
        self.write("proved")
        self.assertEqual(
            len(guard.scan_ledger({self.fact_id}, self.facts)), 1
        )

    def test_a_computed_must_decline_fact_is_also_a_violation(self) -> None:
        self.write("computed")
        self.assertEqual(len(guard.scan_ledger({self.fact_id}, self.facts)), 1)

    def test_an_open_must_decline_fact_is_not_a_violation(self) -> None:
        """Discriminating: a guard that flags every must-decline fact would fire
        on the committed tree, where all nine are correctly `open`."""
        self.write("open")
        self.assertEqual(guard.scan_ledger({self.fact_id}, self.facts), [])

    def test_a_missing_fact_file_is_skipped_not_flagged(self) -> None:
        self.assertEqual(guard.scan_ledger({self.fact_id}, self.facts), [])

    def test_the_committed_ledger_has_no_settled_must_decline_fact(self) -> None:
        """The live assertion. If this ever fails, a statement with a recorded
        counterexample has been admitted and everything downstream is suspect."""
        ids = {
            e["fact_id"]
            for e in json.loads(guard.GROUND_TRUTH.read_text())["entries"]
        }
        self.assertEqual(len(ids), 11)
        self.assertEqual(guard.scan_ledger(ids, guard.FACTS), [])


if __name__ == "__main__":
    unittest.main()
