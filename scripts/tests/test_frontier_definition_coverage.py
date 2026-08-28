#!/usr/bin/env python3
"""Fail-closed controls for `fact-frontier.py`'s kernel declaration coverage
check (docs/plan/status/202-frontier-split.md).

The deficiency this guards: `fact-frontier.py` used to print "proof route
only -- needs a kernel proof" for BOTH a fact whose statement is expressible
and unproved, AND a fact whose statement names a function this kernel has
never declared (so no proof can even be attempted). Measured 2026-08-28
(docs/research/11-design-review/2026-08-28-is-the-open-frontier-stale.md):
at least 30 of 128 open facts were in the second state.

Every test below is a GUARD -- deleting the code it tests must make exactly
that test fail and no other. The three clauses combined in
`missing_declarations`'s filter (namespace-known, not-declared,
not-corroborated-by-a-proved-fact) are tested in isolation from each other by
construction: each fixture holds the other two clauses trivially true so only
the clause under test can flip the result.
"""

from __future__ import annotations

import importlib.util
import os
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/fact-frontier.py"
SPEC = importlib.util.spec_from_file_location("fact_frontier_defcov", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
frontier = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(frontier)


def fact(fact_id: str, *, status: str, statement: str, fragment: str = "Nat") -> dict:
    return {
        "id": fact_id,
        "epistemic_status": status,
        "external_status": "proved",
        "formal": {"language": "lean4-surface", "fragment": fragment, "statement": statement},
        "depends_on": [],
    }


class MissingDeclarationsGuardsTests(unittest.TestCase):
    """Each test isolates exactly one of the three `and`-clauses."""

    def test_unknown_namespace_is_not_flagged(self) -> None:
        # `Set` is not a namespace this kernel implements at all (no
        # `Set.*` declaration anywhere), so a candidate under it must never
        # be reported as a missing DEFINITION -- that would conflate
        # Mathlib scaffolding vocabulary with a genuine gap.
        index = frontier.KernelIndex(names=frozenset(), namespaces=frozenset({"Nat"}), row_count=1)
        missing = frontier.missing_declarations(
            "∀ {n : ℕ}, AntitoneOn (fun b : ℕ => Nat.log b n) (Set.Ioi 1)", index, set()
        )
        self.assertNotIn("Set.Ioi", missing)

    def test_declared_name_is_not_flagged(self) -> None:
        # The core "must not cry wolf" control the brief asks for by name:
        # a fact naming a function that DOES exist must not be reported as
        # blocked.
        index = frontier.KernelIndex(
            names=frozenset({"Nat.add"}), namespaces=frozenset({"Nat"}), row_count=1
        )
        missing = frontier.missing_declarations("∀ (a b : ℕ), Nat.add a b = Nat.add b a", index, set())
        self.assertEqual(missing, [])

    def test_undeclared_name_is_flagged(self) -> None:
        index = frontier.KernelIndex(
            names=frozenset({"Nat.add"}), namespaces=frozenset({"Nat"}), row_count=1
        )
        missing = frontier.missing_declarations("∀ (n : ℕ), Nat.log 2 n = 0", index, set())
        self.assertEqual(missing, ["Nat.log"])

    def test_name_corroborated_by_a_proved_fact_is_not_flagged(self) -> None:
        # `Nat.Prime`/`Nat.Coprime` are the measured real case: absent from
        # the declared environment (primality is built inline), but used by
        # already-PROVED facts. Without this corroboration, this check would
        # misreport every prime/coprime fact as unstatable.
        index = frontier.KernelIndex(
            names=frozenset({"Nat.add"}), namespaces=frozenset({"Nat"}), row_count=1
        )
        proven = {"Nat.Prime"}
        missing = frontier.missing_declarations(
            "∀ (k : ℕ), Nat.Prime k → k = k", index, proven
        )
        self.assertEqual(missing, [])

    def test_uncorroborated_undeclared_name_is_still_flagged(self) -> None:
        # The mirror of the previous test: corroboration must not swallow a
        # genuinely absent name just because SOME unrelated name is proven.
        index = frontier.KernelIndex(
            names=frozenset({"Nat.add"}), namespaces=frozenset({"Nat"}), row_count=1
        )
        proven = {"Nat.Prime"}
        missing = frontier.missing_declarations("∀ (n : ℕ), Nat.clog 2 n = 0", index, proven)
        self.assertEqual(missing, ["Nat.clog"])


class DotNotationResolutionTests(unittest.TestCase):
    """`n.sqrt` (Lean dot-notation sugar) must resolve the same as `Nat.sqrt`."""

    def test_bound_receiver_resolves_via_its_binder_type(self) -> None:
        candidates = frontier.candidate_identifiers("∀ (n : ℕ), n.sqrt = n.sqrt")
        self.assertIn("Nat.sqrt", candidates)

    def test_chained_dot_calls_resolve_every_segment(self) -> None:
        candidates = frontier.candidate_identifiers("∀ (n : ℕ), n.succ.sqrt ≤ n.sqrt.succ")
        self.assertIn("Nat.succ", candidates)
        self.assertIn("Nat.sqrt", candidates)

    def test_receiver_with_unresolved_binder_type_invents_no_namespace(self) -> None:
        # `f`'s type is a function type, not one of `TYPE_TO_NAMESPACE`'s
        # carriers -- this must not be silently guessed at.
        candidates = frontier.candidate_identifiers(
            "∀ (f : Bool → Bool → Bool), f.sqrt = f.sqrt"
        )
        self.assertFalse(any(c.endswith(".sqrt") for c in candidates))

    def test_compound_receiver_is_not_resolved(self) -> None:
        # Documented blind spot: `(n * n).sqrt` -- the receiver is not a bare
        # identifier. Pinned so a future change to the regex is noticed
        # either way (tightening or silently widening the gap).
        candidates = frontier.candidate_identifiers("∀ (n : ℕ), (n * n).sqrt = n")
        self.assertFalse(any(c.endswith(".sqrt") for c in candidates))


class KernelIndexValidationGuardsTests(unittest.TestCase):
    """A broken/partial projection must be REJECTED, not silently trusted."""

    def test_zero_row_index_is_rejected(self) -> None:
        # Isolated from the positive-control check: names/namespaces here
        # DO carry every required control, only `row_count` is wrong -- the
        # shape a truncated or SIGABRT'd run would actually produce is
        # row_count == 0 with empty names, but this fixture proves the
        # row_count guard fires on its own.
        index = frontier.KernelIndex(
            names=frozenset(frontier.KERNEL_INDEX_POSITIVE_CONTROLS),
            namespaces=frozenset({"Nat", "Int"}),
            row_count=0,
        )
        with self.assertRaises(frontier.KernelIndexError):
            frontier.validate_kernel_index(index)

    def test_index_missing_a_positive_control_is_rejected(self) -> None:
        # Isolated from the row_count guard: row_count is nonzero here, only
        # the required controls are absent -- the shape a build that only
        # reached SOME preludes (a partial `emit` run) would produce.
        index = frontier.KernelIndex(
            names=frozenset({"Unrelated.thing"}),
            namespaces=frozenset({"Unrelated"}),
            row_count=1,
        )
        with self.assertRaises(frontier.KernelIndexError):
            frontier.validate_kernel_index(index)

    def test_healthy_index_is_accepted(self) -> None:
        index = frontier.KernelIndex(
            names=frozenset(frontier.KERNEL_INDEX_POSITIVE_CONTROLS),
            namespaces=frozenset({"Nat", "Int"}),
            row_count=len(frontier.KERNEL_INDEX_POSITIVE_CONTROLS),
        )
        frontier.validate_kernel_index(index)  # must not raise


class HeldOutPartitionWarningTests(unittest.TestCase):
    """The queue must say when a fact is blind evaluation population.

    Motivating measurement (2026-08-28): all 35 `nat.log`/`nat.sqrt`/`nat.clog`
    mirror facts are held-out -- 35 of the 37 rows -- and that is precisely the
    set identified as "the highest-leverage work on the frontier". Three lanes
    were dispatched at those families. Nothing was spent only because each lane
    independently declined to flip the mirrors; the queue said nothing.
    """

    def test_the_real_ledger_has_held_out_rows(self) -> None:
        """Non-vacuity: if this is empty, every other assertion is hollow."""
        self.assertGreater(len(frontier.held_out_fact_ids()), 0)

    def test_a_held_out_fact_is_warned_about(self) -> None:
        held_out = sorted(frontier.held_out_fact_ids())
        self.assertTrue(held_out, "fixture requires a held-out row")
        fact = {"id": held_out[0], "depends_on": [], "formal": {"fragment": "Nat"}}
        line = frontier.describe(fact, {fact["id"]: fact}, set(), {}, {}, False, None)
        self.assertIn("HELD-OUT", line)

    def test_a_non_held_out_fact_is_NOT_warned_about(self) -> None:
        """The direction that matters: warn on everything and it is noise."""
        fact = {
            "id": "F:definitely-not-in-the-nursery",
            "depends_on": [],
            "formal": {"fragment": "Nat"},
        }
        line = frontier.describe(fact, {fact["id"]: fact}, set(), {}, {}, False, None)
        self.assertNotIn("HELD-OUT", line)

    def test_a_missing_nursery_degrades_to_no_warning(self) -> None:
        """Annotation must never crash `just next`."""
        original = frontier.ROOT
        try:
            frontier.ROOT = pathlib.Path("/does/not/exist")
            frontier.held_out_fact_ids.__wrapped__ if hasattr(
                frontier.held_out_fact_ids, "__wrapped__"
            ) else None
            self.assertEqual(frontier.held_out_fact_ids(), frozenset())
        finally:
            frontier.ROOT = original


class LoadKernelIndexCrashSafetyTests(unittest.TestCase):
    """`load_kernel_index` backs `just next`; it must never raise."""

    def test_missing_captured_file_degrades_to_none(self) -> None:
        result = frontier.load_kernel_index(path=ROOT / "does" / "not" / "exist.tsv")
        self.assertIsNone(result)

    def test_a_stale_projection_binary_is_treated_as_no_answer(self) -> None:
        """A binary older than a kernel source must NOT be believed.

        This is the defect that motivated the guard: `Nat.sqrt` landed, and a
        projection binary compiled three source files earlier still reported
        14 facts BLOCKED on it -- a FALSE ABSENCE, which tells a lane to build
        something that already exists. The binary was not broken; it was
        answering about the tree it was compiled against.

        Both directions are asserted, because a guard that always says "stale"
        would suppress the whole classification and look safe while doing
        nothing.
        """
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            src = root / "crates" / "axeyum-lean-kernel" / "src"
            src.mkdir(parents=True)
            binary = root / "projection"
            binary.write_text("#!/bin/sh\ntrue\n")

            source = src / "thing.rs"
            source.write_text("// newer than the binary\n")
            os.utime(binary, (1_000_000, 1_000_000))
            os.utime(source, (2_000_000, 2_000_000))

            original_root = frontier.ROOT
            try:
                frontier.ROOT = root
                self.assertTrue(
                    frontier.kernel_projection_is_stale(binary),
                    "a source newer than the binary must read as stale",
                )
                os.utime(source, (500_000, 500_000))
                self.assertFalse(
                    frontier.kernel_projection_is_stale(binary),
                    "a source older than the binary must read as fresh -- "
                    "otherwise the guard suppresses every classification",
                )
            finally:
                frontier.ROOT = original_root

    def test_an_unreadable_projection_binary_is_treated_as_stale(self) -> None:
        """Cannot-tell degrades to no-answer, never to a confident absence."""
        self.assertTrue(
            frontier.kernel_projection_is_stale(
                pathlib.Path("/does/not/exist/projection")
            )
        )

    def test_malformed_captured_file_degrades_to_none(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            bad = pathlib.Path(tmp) / "bad.tsv"
            bad.write_text("not\tenough\n")  # too few rows, no positive controls
            result = frontier.load_kernel_index(path=bad)
            self.assertIsNone(result)

    def test_well_formed_captured_file_loads_and_flags_correctly(self) -> None:
        # End-to-end: a captured TSV in `kernel_declaration_projection`'s
        # real row shape, carrying every positive control plus `Nat.add` but
        # NOT `Nat.log` -- the real measured shape of the deficiency.
        rows = [
            f"nat\tdefinition\t{name}\t0\t\t\t\t{name}"
            for name in (*frontier.KERNEL_INDEX_POSITIVE_CONTROLS, "Nat.add")
        ]
        with tempfile.TemporaryDirectory() as tmp:
            good = pathlib.Path(tmp) / "good.tsv"
            good.write_text("\n".join(rows) + "\n")
            index = frontier.load_kernel_index(path=good)
        self.assertIsNotNone(index)
        self.assertEqual(
            frontier.missing_declarations("∀ (n : ℕ), Nat.log 2 n = 0", index, set()),
            ["Nat.log"],
        )
        self.assertEqual(
            frontier.missing_declarations("∀ (a b : ℕ), Nat.add a b = 0", index, set()),
            [],
        )


class DescribeOverridesReachTextTests(unittest.TestCase):
    """`describe()` must report the blocker BEFORE decidable/proof-route text."""

    def test_missing_definition_takes_precedence_over_decidable(self) -> None:
        f = fact("F:example-blocked", status="open", statement="Nat.log 2 3 = 0", fragment="QF_BV")
        line = frontier.describe(
            f, {f["id"]: f}, False, {}, decidable={"QF_BV"}, held=None,
            missing_defs=["Nat.log"],
        )
        self.assertIn("BLOCKED", line)
        self.assertIn("Nat.log", line)
        self.assertNotIn("DECIDABLE", line)

    def test_no_missing_definitions_falls_back_to_ordinary_classification(self) -> None:
        f = fact("F:example-open", status="open", statement="Nat.add 2 3 = 5", fragment="QF_BV")
        line = frontier.describe(
            f, {f["id"]: f}, False, {}, decidable={"QF_BV"}, held=None, missing_defs=None,
        )
        self.assertIn("DECIDABLE", line)
        self.assertNotIn("BLOCKED", line)


if __name__ == "__main__":
    unittest.main()
