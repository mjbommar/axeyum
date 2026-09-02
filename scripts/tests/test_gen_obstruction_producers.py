#!/usr/bin/env python3
"""Controls for `gen-obstruction-producers.py`'s `Nat.testBit` classification.

WHY THIS EXISTS
---------------

ADR-1545 corrected the `nat-testbit-bool-codomain` obstruction row from
`removability: new-construction` to `not-removable`.  The row it replaced did
not merely have the wrong label: its stated *reason* asserted, of a
`Bool`-valued `testBit` view and its bridge theorem, that "neither is built" --
and both are built, axiom-free, in
`crates/axeyum-lean-kernel/examples/nat_testbit_bool_bridge.rs`, and have been
since 2026-08-26 without moving a single mirror.

That is a claim about the tree that went stale silently, in the field a
selector reads.  Prose in the generator's docstring is what carried the earlier
`fastFib` correction (ADR-0840) and it did not stop this one from being written
next to it.  So the corrected classification is pinned here instead, and this
module is registered in `scripts/tests/mutation_controls.py` under
`obstruction-testbit-classification`: each guard below is killed by exactly one
deletion in the generator.

`test_population_is_not_empty` is the vacuity control and is deliberately NOT
one of the 1:1 mutation targets -- it exists so the other four cannot pass by
classifying an empty population.

SETTLEMENT POLICY (ADR-1510, applied to this compiler)
------------------------------------------------------

`TestSettlementPolicy` pins the second defect this file exists for, found on
`main` 2026-09-02. `compile_pointwise_bit_extensionality` hard-coded two
targets and died -- exit 2, before ANY artifact was written -- the moment they
were flipped to `proved` (`8822d5033`, 2026-08-30) by the very recipe the
contract predicted. Everything downstream went with it: `obstructions.json`
could not be regenerated, `check-obstruction-producers.py` was red on G1 plus
two G7, and 2 of 13 cases in `scripts/tests/test-obstruction-producers.sh`
failed because they shell out to the dying generator. Success and defect had
the same exit status, which is exactly the shape ADR-1510 decided against for
producer contracts one arrow upstream: a claim sized against a population that
then empties must RETIRE, not error.

The two guards are separate and are killed by DIFFERENT mutations:
`test_exhausted_population_retires_rather_than_erroring` owns retirement (the
`contract_kind` fulfilled branch), and
`test_partial_settlement_keeps_live_targets_and_records_settled` owns the
partial case (the `partition_settled` live branch). Neither is expressible as
"the population is empty", which is why one test could not cover both.
"""

from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/gen-obstruction-producers.py"

_spec = importlib.util.spec_from_file_location("gen_obstruction_producers", SCRIPT)
assert _spec is not None and _spec.loader is not None
gen = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gen)

BOOL_ROW = "nat-testbit-bool-codomain"
LIST_ROW = "nat-testbit-list-bool-getI"

# The ADR that decided this, cited so a future edit cannot quietly drop the
# reasoning and leave a bare label behind.
DECISION_ADR = (
    "docs/research/09-decisions/adr-1545-the-testbit-codomain-is-the-"
    "outermost-link-of-a-chain-and-the-bool-view-is-already-built.md"
)


def _classified() -> tuple[list[str], dict[str, dict]]:
    """(the real blocked population, the rows the classifier produced).

    Read from the LEDGER and the divergence registry through the generator's
    own loaders, never from a literal id list -- a literal would measure this
    file's memory of the frontier rather than the frontier.
    """
    facts = gen.load_facts()
    registry = gen.load_json(gen.REGISTRY_PATH)["constructions"]
    blocked = gen.registry_blocked_open_mirrors(facts, registry)
    population = blocked.get("Nat.testBit", [])
    rows = {row["id"]: row for row in gen.classify_testbit(population, facts)}
    return population, rows


class TestTestBitClassification(unittest.TestCase):
    def setUp(self) -> None:
        self.population, self.rows = _classified()

    # --- vacuity control (not a 1:1 mutation target) -----------------------

    def test_population_is_not_empty(self) -> None:
        """Positive control: there is something to classify.

        Every assertion below is about rows derived from this population. If
        `Nat.testBit` ever stops blocking any open mirror, these tests would
        pass by classifying nothing, and that silence is exactly the failure
        mode the repository keeps finding. Fail loudly instead: the right
        response is to retire this suite with the obstruction, deliberately.
        """
        self.assertTrue(
            self.population,
            "no open ml430 mirror is blocked on Nat.testBit any more, so every "
            "other test in this module is vacuous",
        )
        self.assertTrue(self.rows, "a non-empty population produced no rows")

    # --- the four guards, one mutation each --------------------------------

    def test_bool_row_is_not_removable(self) -> None:
        """ADR-1545's decision, in the field a selector reads.

        `new-construction` means "build the thing and the block goes away".
        Measured at the pinned Lean/Mathlib source, building the `Bool` view
        does not remove this block -- it was built and removed nothing --
        because Mathlib's `testBit m n := 1 &&& (m >>> n) != 0` diverges in its
        BODY as well as its codomain, over a `Nat.shiftRight` this kernel does
        not have.
        """
        row = self.rows.get(BOOL_ROW)
        self.assertIsNotNone(row, f"{BOOL_ROW} was not classified at all")
        self.assertEqual(
            row["removability"],
            "not-removable",
            "ADR-1545 decided this obstruction is not removable by any "
            "codomain construction; a `new-construction` label here sends a "
            "lane at work that has already been done and flipped nothing",
        )

    def test_bool_row_cites_the_deciding_adr(self) -> None:
        """The label without the reasoning is how the last one went stale."""
        row = self.rows.get(BOOL_ROW)
        self.assertIsNotNone(row, f"{BOOL_ROW} was not classified at all")
        self.assertIn(
            DECISION_ADR,
            row["evidence"],
            f"{BOOL_ROW} must cite {DECISION_ADR}, which carries the "
            "measurement its `removability` rests on",
        )

    def test_every_path_shaped_evidence_entry_exists(self) -> None:
        """Mirrors `check-obstruction-producers.py`'s G9, at the source.

        G9 accepts a `not-removable` row if AT LEAST ONE evidence entry names
        a real file, so a row with four good citations and one typo passes it.
        Here every path-shaped entry must resolve, and the set is derived from
        the row rather than listed, so a new citation is checked the moment it
        is added.
        """
        checked = 0
        for oid in (BOOL_ROW, LIST_ROW):
            row = self.rows.get(oid)
            if row is None:
                continue
            for entry in row["evidence"]:
                head = entry.split("#", 1)[0].strip()
                # Prose entries ("fact statement contains '.bits.getI'") are
                # legitimate evidence and are not paths; a path is recognised
                # by naming a real directory this repository has.
                if not head.startswith(("artifacts/", "crates/", "docs/", "scripts/")):
                    continue
                checked += 1
                self.assertTrue(
                    (ROOT / head).exists(),
                    f"{oid} cites {head!r}, which does not exist in this tree",
                )
        self.assertGreater(
            checked, 0, "no path-shaped evidence was examined; this test is vacuous"
        )

    def test_the_split_matches_what_the_statements_say(self) -> None:
        """The two rows are blocked for DIFFERENT reasons; keep them apart.

        The `List Bool` group is not a subset of the codomain group with extra
        work attached -- it needs `List` and `Inhabited`, two types this kernel
        does not have, so no construction decision reaches it. The expected
        membership is recomputed here from each fact's own statement, so a
        classifier that files a fact under the wrong reason dies, and so does
        one that drops a fact entirely.
        """
        facts = gen.load_facts()
        expected_list = {
            fid
            for fid in self.population
            if any(
                token in gen.statement_of(facts[fid])
                for token in ("bits", "getI", "List")
            )
        }
        expected_bool = set(self.population) - expected_list

        got_list = set(self.rows.get(LIST_ROW, {}).get("blocked_fact_ids", []))
        got_bool = set(self.rows.get(BOOL_ROW, {}).get("blocked_fact_ids", []))

        self.assertEqual(got_list, expected_list)
        self.assertEqual(got_bool, expected_bool)
        self.assertEqual(
            got_list | got_bool,
            set(self.population),
            "the two rows must partition the blocked population: a fact in "
            "neither is silently unclassified",
        )
        self.assertEqual(
            got_list & got_bool, set(), "a fact was filed under both reasons"
        )


P2_TARGETS = (
    "F:ml430-nat-and-or-distrib-left-fe131f64",
    "F:ml430-nat-and-or-distrib-right-0daaa284",
)

# One P1 hypothesis with a proved twin mirror, so that forcing it back to `open`
# produces an APPLICABLE live target rather than a decline. Read from the
# generator's own table rather than pinned here, so a renamed hypothesis fails
# loudly instead of silently making the partial-settlement case vacuous.
P1_WITH_TWIN = next(
    h["fact_id"] for h in gen.P1_HYPOTHESES if h.get("twin_mirror")
)


class TestSettlementPolicy(unittest.TestCase):
    """A closed target is SPENT, never an error (ADR-1510 applied here)."""

    def test_exhausted_population_retires_rather_than_erroring(self) -> None:
        """P2's whole population closed; the record must say so, not die.

        This is the regression for the `main` red gate: the generator exited 2
        with `P2 target ... is missing or not open; hypothesis is stale` and
        wrote nothing at all. A retired contract has to name what closed and
        with which commit, or the retirement is unauditable -- an unfalsifiable
        claim replaced by an unverifiable one.
        """
        facts = gen.load_facts()
        doc = gen.compile_pointwise_bit_extensionality(facts)
        self.assertEqual(
            doc["kind"],
            "fulfilled",
            "both P2 targets are settled in the ledger, so this contract is "
            "retired; any other kind means it is still claiming prospective "
            "work it does not have",
        )
        self.assertEqual(
            doc["applicability"]["fact_ids"],
            [],
            "a retired contract claims no live targets",
        )
        self.assertTrue(doc.get("outcome"), "a retirement with no outcome")
        spent = {e["fact_id"]: e for e in doc.get("spent") or []}
        self.assertEqual(
            set(spent),
            set(P2_TARGETS),
            "the retirement must name every target that closed underneath it",
        )
        for fid, entry in spent.items():
            self.assertNotEqual(
                gen.status_of(facts[fid]),
                "open",
                f"{fid} is recorded as spent but is still open",
            )
            self.assertTrue(
                entry.get("settled_commit"),
                f"{fid} is recorded as spent with no settling commit; a "
                f"retirement that cannot say what closed the target is "
                f"unauditable",
            )
            self.assertTrue(entry.get("settled_date"), f"{fid}: no settled_date")

    def test_partial_settlement_keeps_live_targets_and_records_settled(self) -> None:
        """Some closed, some open: keep the live ones, record the settled ones.

        The empty-population case and this one are different guards. A compiler
        that only handled exhaustion would still, on a partial close, either
        drop the settled targets without trace or keep claiming them as
        prospective work -- and G7 would then fire on a contract that is
        actually healthy.

        Driven by putting ONE of P1's settled hypotheses back to `open` in a
        copy of the ledger, so the live and settled halves are both non-empty
        and both come from real data.
        """
        facts = {k: dict(v) for k, v in gen.load_facts().items()}
        facts[P1_WITH_TWIN]["epistemic_status"] = "open"
        doc = gen.compile_extensional_duplicate_close(
            facts, gen.declared_nat_prelude_names()
        )
        live = doc["applicability"]["fact_ids"]
        spent_ids = {e["fact_id"] for e in doc.get("spent") or []}
        self.assertEqual(
            live,
            [P1_WITH_TWIN],
            "the one still-open hypothesis must stay in applicability",
        )
        self.assertEqual(
            doc["kind"],
            "capsule",
            "one live target is a capsule, which is the label "
            "check-obstruction-producers.py's G6 names for it",
        )
        self.assertTrue(
            spent_ids, "the hypotheses that closed left no record at all"
        )
        self.assertNotIn(
            P1_WITH_TWIN,
            spent_ids,
            "a live target may not also be recorded as spent",
        )
        self.assertEqual(
            live and set(live) & spent_ids,
            set(),
            "applicability and spent must be disjoint",
        )


if __name__ == "__main__":
    unittest.main()
