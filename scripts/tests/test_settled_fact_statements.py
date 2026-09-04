#!/usr/bin/env python3
"""Controls for `scripts/check-settled-fact-statements.py`.

One test per guard, each built to die when its own guard is removed and no
other. Every test builds its own facts and manifest in a temp directory: reading
live `artifacts/` would make the suite drift as facts land, and a fixture that
passes because of today's repository state stops controlling on a day nobody is
watching.

The S1 guards (absence, slack, prose drift, declaration repointing, the
`theorem <name> :` header bind, and `--write` refusing to launder) are the point
of this file. The gate they live in was, until S1, unable to fail on the single
most common way a statement goes unwatched: never being pinned at all. A suite
that did not separate "absent" from "drifted" would let that regress silently.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SUBJECT = ROOT / "scripts/check-settled-fact-statements.py"


def load_subject():
    spec = importlib.util.spec_from_file_location("check_settled_fact_statements", SUBJECT)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def sha(text: str) -> str:
    return hashlib.sha256(str(text).encode()).hexdigest()


class SettledFactStatementControls(unittest.TestCase):
    def setUp(self):
        self._dir = tempfile.TemporaryDirectory()
        self.tmp = pathlib.Path(self._dir.name)
        self.facts = self.tmp / "facts"
        self.facts.mkdir()
        self.module = load_subject()
        self.module.FACTS = self.facts
        self.module.PINS = self.tmp / "pins.json"

    def tearDown(self):
        self._dir.cleanup()

    def write_fact(
        self,
        fact_id,
        statement,
        language="lean4",
        status="proved",
        prose="PROSE",
        kernel_theorem=None,
    ):
        formal = {"language": language, "statement": statement}
        if kernel_theorem is not None:
            formal["kernel_theorem"] = kernel_theorem
        (self.facts / f"{fact_id.replace(':', '-')}.json").write_text(
            json.dumps(
                {
                    "id": fact_id,
                    "epistemic_status": status,
                    "statement": prose,
                    "formal": formal,
                }
            ),
            encoding="utf-8",
        )

    def write_pins(self, pins, amendments=None, floor=None):
        manifest = {"pins": pins, "amendments": amendments or []}
        if floor is not None:
            manifest["coverage_floor"] = floor
        (self.tmp / "pins.json").write_text(json.dumps(manifest), encoding="utf-8")

    def run_check(self, argv=("--quiet",)):
        try:
            return self.module.check(list(argv))
        except self.module.StatementDriftError:
            return 2

    def pin(self, fact_id, statement, prose="PROSE", kernel_theorem=None, language="lean4"):
        row = {
            "fact_id": fact_id,
            "language": language,
            "statement_sha256": sha(statement),
            "prose_sha256": sha(prose),
        }
        if kernel_theorem is not None:
            row["kernel_theorem"] = kernel_theorem
        return row

    def healthy(self):
        """Two settled facts, both fully pinned, ratchet exactly tight."""
        self.write_fact("F:a", "STMT A")
        self.write_fact("F:b", "STMT B")
        self.write_pins(
            [self.pin("F:a", "STMT A"), self.pin("F:b", "STMT B")],
            floor={"max_unpinned_settled": 0, "min_identity_bound": 0, "max_header_exempt": 0},
        )

    def test_healthy_passes(self):
        """Positive control. Without it, a guard rejecting EVERYTHING would
        satisfy every negative test below and look like a working gate."""
        self.healthy()
        self.assertEqual(self.run_check(), 0)

    # --- guard: an unamended statement change is a violation ---------------
    def test_unamended_statement_change_is_a_violation(self):
        self.healthy()
        self.write_fact("F:a", "STMT A REWRITTEN TO MATCH THE PROOF")
        self.assertEqual(self.run_check(), 1)

    # --- guard: a correct amendment permits the change ---------------------
    def test_amended_change_passes(self):
        self.healthy()
        self.write_fact("F:a", "STMT A CORRECTED")
        self.write_pins(
            [self.pin("F:a", "STMT A"), self.pin("F:b", "STMT B")],
            [
                {
                    "fact_id": "F:a",
                    "from_sha256": sha("STMT A"),
                    "to_sha256": sha("STMT A CORRECTED"),
                    "reason": "kernel-dumped type replaces a hand-written seed",
                }
            ],
            floor={"max_unpinned_settled": 0, "min_identity_bound": 0, "max_header_exempt": 0},
        )
        self.assertEqual(self.run_check(), 0)

    # --- guard: the amendment must describe THIS change --------------------
    def test_amendment_with_wrong_digests_is_a_violation(self):
        """An amendment naming a different edit must not license this one, or
        one amendment becomes a permanent waiver for a fact."""
        self.healthy()
        self.write_fact("F:a", "STMT A REWRITTEN")
        self.write_pins(
            [self.pin("F:a", "STMT A"), self.pin("F:b", "STMT B")],
            [
                {
                    "fact_id": "F:a",
                    "from_sha256": sha("SOMETHING ELSE"),
                    "to_sha256": sha("SOMETHING ELSE AGAIN"),
                    "reason": "unrelated",
                }
            ],
            floor={"max_unpinned_settled": 0, "min_identity_bound": 0, "max_header_exempt": 0},
        )
        self.assertEqual(self.run_check(), 1)

    def test_amendment_with_wrong_from_digest_is_a_violation(self):
        """The amendment lands on the right NEW statement but claims to start
        from a statement the fact never had.

        Without this the two halves of the digest check are not separable: the
        both-wrong fixture above is caught by the `to_sha256` clause alone, so
        the `from_sha256` clause could be deleted with the suite still green --
        measured, it survived its first mutation run for exactly that reason.
        The clause matters: an amendment whose `from` is wrong has not recorded
        the edit that happened, and reviewing it tells you nothing about what
        the statement used to say."""
        self.healthy()
        self.write_fact("F:a", "STMT A REWRITTEN")
        self.write_pins(
            [self.pin("F:a", "STMT A"), self.pin("F:b", "STMT B")],
            [
                {
                    "fact_id": "F:a",
                    "from_sha256": sha("A STATEMENT THIS FACT NEVER CARRIED"),
                    "to_sha256": sha("STMT A REWRITTEN"),
                    "reason": "records the wrong starting point",
                }
            ],
            floor={"max_unpinned_settled": 0, "min_identity_bound": 0, "max_header_exempt": 0},
        )
        self.assertEqual(self.run_check(), 1)

    # --- guard: an amendment must be a record, not a rubber stamp ----------
    def test_amendment_without_a_reason_is_an_error(self):
        self.healthy()
        self.write_pins(
            [self.pin("F:a", "STMT A"), self.pin("F:b", "STMT B")],
            [{"fact_id": "F:a", "from_sha256": sha("x"), "to_sha256": sha("y")}],
            floor={"max_unpinned_settled": 0, "min_identity_bound": 0, "max_header_exempt": 0},
        )
        self.assertEqual(self.run_check(), 2)

    # --- guard: a silent retraction is reported ----------------------------
    def test_silent_retraction_is_a_violation(self):
        self.healthy()
        self.write_fact("F:a", "STMT A", status="open")
        self.assertEqual(self.run_check(), 1)

    # --- guard: fail closed on an empty manifest ---------------------------
    def test_empty_pin_manifest_is_an_error(self):
        self.healthy()
        self.write_pins(
            [], floor={"max_unpinned_settled": 0, "min_identity_bound": 0, "max_header_exempt": 0}
        )
        self.assertEqual(self.run_check(), 2)

    # --- guard: fail closed when there are no settled facts ----------------
    def test_no_settled_facts_is_an_error(self):
        self.healthy()
        self.write_fact("F:a", "STMT A", status="open")
        self.write_fact("F:b", "STMT B", status="open")
        self.assertEqual(self.run_check(), 2)

    # === S1 guards =========================================================

    # --- guard: a manifest with no ratchet cannot fail on absence ----------
    def test_missing_coverage_floor_is_an_error(self):
        """Fail closed. Without a floor the gate has no opinion about absence,
        which is precisely the state S1 found it in."""
        self.healthy()
        self.write_pins([self.pin("F:a", "STMT A"), self.pin("F:b", "STMT B")], floor=None)
        self.assertEqual(self.run_check(), 2)

    def test_non_integer_coverage_floor_is_an_error(self):
        self.healthy()
        self.write_pins(
            [self.pin("F:a", "STMT A")],
            floor={"max_unpinned_settled": "0", "min_identity_bound": 0, "max_header_exempt": 0},
        )
        self.assertEqual(self.run_check(), 2)

    # --- guard: an unpinned settled fact is a GAP, above the allowance ------
    def test_unpinned_settled_fact_above_allowance_is_a_violation(self):
        """The headline S1 fix. Before it, this exact fixture exited 0."""
        self.healthy()
        self.write_fact("F:c", "STMT C")
        self.assertEqual(self.run_check(), 1)

    def test_unpinned_settled_fact_within_allowance_passes(self):
        """Landing a fact must not be reported as DRIFT, and a ratchet set
        above zero must actually tolerate the slot it allows -- otherwise the
        absence guard is indistinguishable from a gate that rejects all growth."""
        self.write_fact("F:a", "STMT A")
        self.write_fact("F:b", "STMT B")
        self.write_fact("F:c", "STMT C")
        self.write_pins(
            [self.pin("F:a", "STMT A"), self.pin("F:b", "STMT B")],
            floor={"max_unpinned_settled": 1, "min_identity_bound": 0, "max_header_exempt": 0},
        )
        self.assertEqual(self.run_check(), 0)

    # --- guard: a SLACK allowance is itself a violation ---------------------
    def test_slack_unpinned_allowance_is_a_violation(self):
        """Without this, a lane loosens the floor once and the loosened value
        survives forever -- a ratchet that can be hand-edited is decoration."""
        self.write_fact("F:a", "STMT A")
        self.write_pins(
            [self.pin("F:a", "STMT A")],
            floor={"max_unpinned_settled": 5, "min_identity_bound": 0, "max_header_exempt": 0},
        )
        self.assertEqual(self.run_check(), 1)

    # --- guard: the reader-facing statement must not drift ------------------
    def test_prose_statement_change_is_a_violation(self):
        """The formal side is untouched here. Only the field a human reads
        changed, and before S1 nothing in the ledger watched it."""
        self.healthy()
        self.write_fact("F:a", "STMT A", prose="A COMPLETELY DIFFERENT CLAIM")
        self.assertEqual(self.run_check(), 1)

    def test_prose_change_with_matching_amendment_passes(self):
        self.healthy()
        self.write_fact("F:a", "STMT A", prose="A CORRECTED DESCRIPTION")
        self.write_pins(
            [self.pin("F:a", "STMT A"), self.pin("F:b", "STMT B")],
            [
                {
                    "fact_id": "F:a",
                    "from_sha256": sha("STMT A"),
                    "to_sha256": sha("STMT A"),
                    "reason": "prose corrected; formal side unchanged",
                    "from_prose_sha256": sha("PROSE"),
                    "to_prose_sha256": sha("A CORRECTED DESCRIPTION"),
                }
            ],
            floor={"max_unpinned_settled": 0, "min_identity_bound": 0, "max_header_exempt": 0},
        )
        self.assertEqual(self.run_check(), 0)

    # --- guard: a fact must not be repointed at another declaration ---------
    def test_kernel_theorem_repointing_is_a_violation(self):
        """`F:a`'s statement text and prose are byte-identical to its pin; only
        the declaration it claims moved.

        The fixture is deliberately `cas-term` and deliberately carries a second
        stable fact. A `lean4` fixture would let the HEADER guard fire on the
        same mutation, and a lone fact would drop `identity_bound` below its
        floor -- either way this guard could be deleted with the test still
        passing for the wrong reason, which is how it survived its first
        mutation run."""
        self.write_fact("F:a", "STMT A", language="cas-term", kernel_theorem="Foo.baz")
        self.write_fact("F:b", "STMT B", language="cas-term", kernel_theorem="Foo.b2")
        self.write_pins(
            [
                self.pin("F:a", "STMT A", kernel_theorem="Foo.bar", language="cas-term"),
                self.pin("F:b", "STMT B", kernel_theorem="Foo.b2", language="cas-term"),
            ],
            floor={"max_unpinned_settled": 0, "min_identity_bound": 1, "max_header_exempt": 0},
        )
        self.assertEqual(self.run_check(), 1)

    def test_kernel_theorem_unchanged_passes(self):
        """Positive control for the repointing guard: the same fixture with the
        declaration left alone must pass, or a guard rejecting every pinned
        `kernel_theorem` would satisfy the test above."""
        self.write_fact("F:a", "STMT A", language="cas-term", kernel_theorem="Foo.bar")
        self.write_fact("F:b", "STMT B", language="cas-term", kernel_theorem="Foo.b2")
        self.write_pins(
            [
                self.pin("F:a", "STMT A", kernel_theorem="Foo.bar", language="cas-term"),
                self.pin("F:b", "STMT B", kernel_theorem="Foo.b2", language="cas-term"),
            ],
            floor={"max_unpinned_settled": 0, "min_identity_bound": 2, "max_header_exempt": 0},
        )
        self.assertEqual(self.run_check(), 0)

    # --- guard: the rendered header must name the claimed declaration -------
    def test_statement_headed_by_another_declaration_is_a_violation(self):
        """A content hash says "changed". This says "changed into a rendering of
        a DIFFERENT theorem", which is the sharpest form of statement error."""
        self.write_fact("F:a", "theorem Foo.elsewhere : STMT", kernel_theorem="Foo.bar")
        self.write_pins(
            [self.pin("F:a", "theorem Foo.elsewhere : STMT", kernel_theorem="Foo.bar")],
            floor={"max_unpinned_settled": 0, "min_identity_bound": 1, "max_header_exempt": 0},
        )
        self.assertEqual(self.run_check(), 1)

    def test_matching_header_passes(self):
        """Positive control for the header bind: without it, a guard that
        rejected every headed statement would pass the negative above."""
        self.write_fact("F:a", "theorem Foo.bar : STMT", kernel_theorem="Foo.bar")
        self.write_pins(
            [self.pin("F:a", "theorem Foo.bar : STMT", kernel_theorem="Foo.bar")],
            floor={"max_unpinned_settled": 0, "min_identity_bound": 1, "max_header_exempt": 0},
        )
        self.assertEqual(self.run_check(), 0)

    def test_universe_polymorphic_header_matches_its_declaration(self):
        """`render_lean` writes `Foo.bar.{u}` for a universe-polymorphic theorem
        while the kernel's name is `Foo.bar`; the bind must strip the suffix.
        Killed by removing UNIVERSE_SUFFIX from header_name."""
        self.write_fact("F:a", "theorem Foo.bar.{u} : STMT", kernel_theorem="Foo.bar")
        self.write_pins(
            [self.pin("F:a", "theorem Foo.bar.{u} : STMT", kernel_theorem="Foo.bar")],
            floor={"max_unpinned_settled": 0, "min_identity_bound": 1, "max_header_exempt": 0},
        )
        self.assertEqual(self.run_check(), 0)

    def test_universe_polymorphic_header_of_another_declaration_is_a_violation(self):
        """The suffix strip must not weaken the bind: a polymorphic rendering of
        a DIFFERENT theorem is still a violation."""
        self.write_fact("F:a", "theorem Foo.elsewhere.{u} : STMT", kernel_theorem="Foo.bar")
        self.write_pins(
            [self.pin("F:a", "theorem Foo.elsewhere.{u} : STMT", kernel_theorem="Foo.bar")],
            floor={"max_unpinned_settled": 0, "min_identity_bound": 1, "max_header_exempt": 0},
        )
        self.assertEqual(self.run_check(), 1)

    # --- guard: a new headerless statement is counted, not ignored ----------
    def test_new_headerless_statement_above_allowance_is_a_violation(self):
        self.write_fact("F:a", "((x0 : AxNat) -> STMT)", kernel_theorem="Foo.bar")
        self.write_pins(
            [self.pin("F:a", "((x0 : AxNat) -> STMT)", kernel_theorem="Foo.bar")],
            floor={"max_unpinned_settled": 0, "min_identity_bound": 1, "max_header_exempt": 0},
        )
        self.assertEqual(self.run_check(), 1)

    # --- guard: losing an identity binding is a violation --------------------
    def test_identity_binding_below_floor_is_a_violation(self):
        """Dropping `kernel_theorem` un-binds a fact from its declaration while
        leaving every hash intact, so no drift guard sees it.

        The amendment here is what isolates this guard: without it the
        REPOINTING guard fires on the same edit and the test passes whether or
        not the identity floor is enforced. With the repoint licensed, falling
        below the floor is the only thing left to complain about -- an amended
        repoint is still a lost binding, and the ledger should say so."""
        self.write_fact("F:a", "theorem Foo.bar : STMT", kernel_theorem=None)
        self.write_pins(
            [self.pin("F:a", "theorem Foo.bar : STMT", kernel_theorem="Foo.bar")],
            [
                {
                    "fact_id": "F:a",
                    "from_sha256": sha("theorem Foo.bar : STMT"),
                    "to_sha256": sha("theorem Foo.bar : STMT"),
                    "reason": "declaration link dropped deliberately",
                }
            ],
            floor={"max_unpinned_settled": 0, "min_identity_bound": 1, "max_header_exempt": 0},
        )
        self.assertEqual(self.run_check(), 1)

    def test_slack_identity_floor_is_a_violation(self):
        self.write_fact("F:a", "theorem Foo.bar : STMT", kernel_theorem="Foo.bar")
        self.write_pins(
            [self.pin("F:a", "theorem Foo.bar : STMT", kernel_theorem="Foo.bar")],
            floor={"max_unpinned_settled": 0, "min_identity_bound": 0, "max_header_exempt": 0},
        )
        self.assertEqual(self.run_check(), 1)

    # === `--write` ==========================================================

    def test_write_refuses_to_launder_an_unamended_change(self):
        """`--write` used to rebuild pins from current state unconditionally, so
        anyone who ran it after a drift re-pinned the damage and the gate went
        green. This is that path."""
        self.healthy()
        self.write_fact("F:a", "STMT A SILENTLY REWRITTEN")
        before = (self.tmp / "pins.json").read_text()
        self.assertEqual(self.run_check(["--write"]), 1)
        # The manifest is byte-identical: the refusal happens before any write,
        # so a drift cannot be laundered even partially. This test deliberately
        # does NOT re-assert that the plain check still fails -- that belongs to
        # the drift guard, and asserting it here would make one mutation kill
        # two tests and blur which guard is load-bearing.
        self.assertEqual((self.tmp / "pins.json").read_text(), before)

    def test_write_pins_a_newly_settled_fact(self):
        """Positive control for `--write`: without it, a `--write` that refused
        everything would satisfy the laundering test above."""
        self.healthy()
        self.write_fact("F:c", "STMT C")
        self.assertEqual(self.run_check(["--write"]), 0)
        self.assertEqual(self.run_check(), 0)
        manifest = json.loads((self.tmp / "pins.json").read_text())
        self.assertIn("F:c", {r["fact_id"] for r in manifest["pins"]})

    def test_write_preserves_the_superseded_statement(self):
        """The roadmap's "preserve previous statements when correcting a row"."""
        self.healthy()
        self.write_fact("F:a", "STMT A CORRECTED")
        self.write_pins(
            [self.pin("F:a", "STMT A"), self.pin("F:b", "STMT B")],
            [
                {
                    "fact_id": "F:a",
                    "from_sha256": sha("STMT A"),
                    "to_sha256": sha("STMT A CORRECTED"),
                    "reason": "corrected",
                }
            ],
            floor={"max_unpinned_settled": 0, "min_identity_bound": 0, "max_header_exempt": 0},
        )
        self.assertEqual(self.run_check(["--write"]), 0)
        manifest = json.loads((self.tmp / "pins.json").read_text())
        row = next(r for r in manifest["pins"] if r["fact_id"] == "F:a")
        self.assertEqual(row["statement_sha256"], sha("STMT A CORRECTED"))
        self.assertEqual([h["statement_sha256"] for h in row["history"]], [sha("STMT A")])

    def test_write_only_tightens_the_ratchet(self):
        """A loosened floor must not survive a `--write`, or the ratchet is a
        suggestion."""
        self.write_fact("F:a", "STMT A")
        self.write_pins(
            [self.pin("F:a", "STMT A")],
            floor={"max_unpinned_settled": 99, "min_identity_bound": 0, "max_header_exempt": 99},
        )
        self.assertEqual(self.run_check(["--write"]), 0)
        floor = json.loads((self.tmp / "pins.json").read_text())["coverage_floor"]
        self.assertEqual(floor["max_unpinned_settled"], 0)
        self.assertEqual(floor["max_header_exempt"], 0)


if __name__ == "__main__":
    unittest.main()
