"""Controls for `check-fact-depends-derived.py`.

It passes on the committed ledger, which proves nothing on its own — the ledger
was edited until it did. So each guard is driven to fail here, and the two
non-guards are pinned as well: this check deliberately does NOT object to a fact
declaring more than its proof uses, nor to a used theorem that is not a fact.
Both restraints matter, because a check that demanded either would make proving
things more expensive without making the ledger truer.
"""

from __future__ import annotations

import importlib.util
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_fact_depends_derived", ROOT / "scripts" / "check-fact-depends-derived.py"
)
assert SPEC and SPEC.loader
DD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(DD)


def fact(ident: str, theorem: str, depends: list[str] | None = None) -> dict:
    return {
        "id": ident,
        "proof_route": "kernel-lean",
        "epistemic_status": "proved",
        "depends_on": depends or [],
        "evidence": [
            {
                "checker_command": (
                    "cargo run -q -p axeyum-lean-kernel --example nat_theorem_inventory "
                    f"-- x 2>/dev/null | grep -qE '^{theorem}[[:space:]]'"
                )
            }
        ],
    }


class TheTheoremNameComesFromTheFactsOwnCommand(unittest.TestCase):
    def test_an_escaped_grep_pattern_is_read(self) -> None:
        self.assertEqual(
            DD.theorem_of(fact("F:a", r"Nat\.mul_one")), "Nat.mul_one"
        )

    def test_a_command_naming_no_theorem_yields_none(self) -> None:
        data = fact("F:a", "Nat.mul_one")
        data["evidence"] = [{"checker_command": "cargo run -q --example something_else"}]
        self.assertIsNone(DD.theorem_of(data))


class AnExplicitFormalKernelTheoremOverridesExtraction(unittest.TestCase):
    """`F:cassini-identity-over-constructed-integers` extracted `Int.sub` --
    matched out of its OWN formal-statement fragment embedded in the
    checker_command -- instead of its actual subject `Int.fib_cassini`, until
    `formal.kernel_theorem` existed to pin the right answer. `F:complex-ring-
    constructed-axiom-free` and `F:complex-mul-assoc` both extracted
    `Complex.mul_assoc` and collided, until an explicit `null` marked the
    package-level fact as having no single subject."""

    def test_an_explicit_string_wins_even_when_extraction_would_disagree(self) -> None:
        data = fact("F:a", "Nat.mul_one")
        data["formal"] = {"kernel_theorem": "Nat.zero_add"}
        self.assertEqual(DD.theorem_of(data), "Nat.zero_add")

    def test_an_explicit_null_means_no_single_subject_even_though_evidence_names_one(
        self,
    ) -> None:
        data = fact("F:a", "Nat.mul_one")
        data["formal"] = {"kernel_theorem": None}
        self.assertIsNone(DD.theorem_of(data))

    def test_an_absent_key_still_falls_back_to_extraction(self) -> None:
        data = fact("F:a", "Nat.mul_one")
        data["formal"] = {"language": "lean4"}
        self.assertEqual(DD.theorem_of(data), "Nat.mul_one")


class EachGuardCanFail(unittest.TestCase):
    def test_a_missing_derived_edge_fails(self) -> None:
        facts = {
            "F:a": fact("F:a", r"Nat\.mul_one"),
            "F:b": fact("F:b", r"Nat\.zero_add"),
        }
        graph = {"Nat.mul_one": ["Nat.zero_add"], "Nat.zero_add": []}
        failures, stats = DD.evaluate(facts, graph)
        self.assertEqual(stats["missing_edges"], 1)
        self.assertTrue(any("does not name it" in f for f in failures), failures)

    def test_a_declared_edge_passes(self) -> None:
        facts = {
            "F:a": fact("F:a", r"Nat\.mul_one", ["F:b"]),
            "F:b": fact("F:b", r"Nat\.zero_add"),
        }
        graph = {"Nat.mul_one": ["Nat.zero_add"], "Nat.zero_add": []}
        failures, _ = DD.evaluate(facts, graph)
        self.assertEqual(failures, [])


class TheRestraintsArePinnedToo(unittest.TestCase):
    def test_a_used_theorem_that_is_not_a_fact_is_not_demanded(self) -> None:
        """Most prelude lemmas are not facts. Requiring one per lemma would tax
        proving rather than improve the ledger."""
        facts = {"F:a": fact("F:a", r"Nat\.mul_one")}
        graph = {"Nat.mul_one": ["Nat.some_helper"]}
        failures, stats = DD.evaluate(facts, graph)
        self.assertEqual(failures, [])
        self.assertEqual(stats["missing_edges"], 0)

    def test_declaring_more_than_the_proof_uses_is_allowed(self) -> None:
        """A `depends_on` may record a mathematical dependency the mechanised
        proof routed around; that is a statement about the mathematics, not an
        error about the term."""
        facts = {
            "F:a": fact("F:a", r"Nat\.mul_one", ["F:b", "F:c"]),
            "F:b": fact("F:b", r"Nat\.zero_add"),
            "F:c": fact("F:c", r"Nat\.add_comm"),
        }
        graph = {"Nat.mul_one": ["Nat.zero_add"], "Nat.zero_add": [], "Nat.add_comm": []}
        failures, _ = DD.evaluate(facts, graph)
        self.assertEqual(failures, [])

    def test_a_fact_naming_no_theorem_is_reported_not_enforced(self) -> None:
        data = fact("F:a", r"Nat\.mul_one")
        data["evidence"] = [{"checker_command": "cargo run -q --example other"}]
        failures, stats = DD.evaluate({"F:a": data}, {"Nat.mul_one": ["Nat.zero_add"]})
        self.assertEqual(failures, [])
        self.assertEqual(stats["unnamed"], ["F:a"])

    def test_a_non_kernel_route_is_untouched(self) -> None:
        data = fact("F:a", r"Nat\.mul_one")
        data["proof_route"] = "smt-term-level"
        failures, stats = DD.evaluate({"F:a": data}, {"Nat.mul_one": ["Nat.zero_add"]})
        self.assertEqual(failures, [])
        self.assertEqual(stats["kernel_facts"], 0)


class AnEmptyGraphIsAFailureNotAPass(unittest.TestCase):
    """The vacuity floor, which had NO test until it was mutation-checked.

    If the inventory returns nothing — wrong environment, renamed example,
    build failure swallowed — then every fact trivially satisfies "declares
    everything its proof uses", and the check reports success while looking at
    nothing. That is this repository's signature defect, so the floor fails
    instead. Deleting it now kills this test.
    """

    def test_a_tiny_graph_fails_rather_than_passing_vacuously(self) -> None:
        original = DD.inventory
        DD.inventory = lambda: {"Nat.mul_one": []}
        try:
            self.assertEqual(DD.main(["--quiet"]), 1)
        finally:
            DD.inventory = original

    def test_a_full_graph_is_not_rejected_by_the_floor(self) -> None:
        """The floor must not be so high that a healthy run trips it."""
        original = DD.inventory
        DD.inventory = lambda: {f"Nat.t{i}": [] for i in range(139)}
        try:
            self.assertEqual(DD.main(["--quiet"]), 0)
        finally:
            DD.inventory = original


class TheCommittedLedgerAgreesWithTheKernel(unittest.TestCase):
    def test_it_passes_end_to_end(self) -> None:
        """Builds the prelude, so it is the slow one; it is also the only test
        here that would notice the inventory itself breaking."""
        self.assertEqual(DD.main(["--quiet"]), 0)


class ATheoremNameIsWrittenThreeWaysInCheckerCommands(unittest.TestCase):
    """The pattern reads names out of shell commands, and those commands escape
    for whatever tool they pipe into. Measured 2026-08-18, matching only the
    plain form left 8 of 43 kernel-route facts unenforced — including every fact
    added that day — and the checker reported `missing_edges=0` regardless."""

    def test_a_plain_name_matches(self) -> None:
        found = DD.THEOREM_RE.search("nat_theorem_inventory -- Nat.mul_one")
        self.assertEqual(found.group(1), "Nat.mul_one")

    def test_a_regex_escaped_name_matches(self) -> None:
        found = DD.THEOREM_RE.search(r"grep -qE '^Nat\.pow_add\s'")
        self.assertEqual(found.group(1), r"Nat\.pow_add")

    def test_a_grep_bracket_escaped_namespaced_name_matches(self) -> None:
        """How the characterization facts write it. Matching one segment yields
        `Int.Characterization`, which is not a theorem, so the fact drops out
        silently rather than failing."""
        found = DD.THEOREM_RE.search(
            "grep -qE '^int-categoricity[[:space:]]+Int[.]Characterization[.]categorical'"
        )
        self.assertEqual(found.group(1), "Int[.]Characterization[.]categorical")

    def test_the_bracket_form_resolves_to_a_real_theorem_name(self) -> None:
        """Matching is not enough: the name must be normalised before it can be
        looked up in the kernel's graph."""
        fact = {"evidence": [{"checker_command": "x Int[.]Characterization[.]categorical y"}]}
        self.assertEqual(DD.theorem_of(fact), "Int.Characterization.categorical")

    def test_a_command_naming_no_theorem_still_yields_none(self) -> None:
        """The control: five facts legitimately run a Rust test instead, and must
        keep dropping out rather than being matched by accident."""
        fact = {
            "evidence": [
                {
                    "checker_command": "cargo test -p axeyum-lean-kernel --lib "
                    "rat_add_renormalises_and_neg_is_an_involution"
                }
            ]
        }
        self.assertIsNone(DD.theorem_of(fact))


class TheConstructedCarriersAreEnforcedToo(unittest.TestCase):
    """`CReal`/`Complex`/`CPoint` were absent from `_NS` until 2026-08-25, so
    every fact whose checker named a theorem in one of those namespaces fell
    into `unnamed` — 331 theorems (159 CReal, 84 Complex, 88 CPoint) this gate
    never enforced anything over. Widening the class must not repeat the
    `AxReal`/`Real` substring trap CLAUDE.md documents: `CReal` is a literal
    substring of nothing in `_NS`, but the boundary must still hold for any
    name that merely ENDS in one of these tokens."""

    def test_creal_matches(self) -> None:
        found = DD.THEOREM_RE.search("theorem_dependency_inventory -- CReal.add_comm")
        self.assertEqual(found.group(1), "CReal.add_comm")

    def test_complex_matches(self) -> None:
        found = DD.THEOREM_RE.search("theorem_dependency_inventory -- Complex.mul_comm")
        self.assertEqual(found.group(1), "Complex.mul_comm")

    def test_cpoint_matches(self) -> None:
        found = DD.THEOREM_RE.search("theorem_dependency_inventory -- CPoint.dot_comm")
        self.assertEqual(found.group(1), "CPoint.dot_comm")

    def test_a_near_miss_carrier_prefix_is_not_matched_as_creal(self) -> None:
        """`XCReal.foo` is not a name any kernel declares. The same
        `(?<![A-Za-z])` boundary that keeps `AxReal.add_comm` from spuriously
        yielding `Real.add_comm` must also keep this from matching at the
        `CReal` offset — the character immediately before it is a letter."""
        found = DD.THEOREM_RE.search("cargo run -- XCReal.foo")
        self.assertIsNone(found)

    def test_axreal_still_wins_over_real_next_to_a_real_creal_name(self) -> None:
        """Regression control for the ORIGINAL substring trap, now run
        alongside the widened class: `AxReal.add_comm` must still yield
        `AxReal.add_comm`, never `Real.add_comm`, even with `CReal` present in
        `_NS`."""
        found = DD.THEOREM_RE.search("nat_theorem_inventory -- AxReal.add_comm")
        self.assertEqual(found.group(1), "AxReal.add_comm")


if __name__ == "__main__":
    unittest.main()
