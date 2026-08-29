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
import json
import pathlib
import tempfile
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


def write_fact_file(
    path: pathlib.Path,
    ident: str,
    theorem: str,
    depends_on_literal: str,
    extra_before: str = "",
) -> None:
    """Write a fact file with `depends_on` written EXACTLY as
    `depends_on_literal` (any valid JSON array text -- single-line, `[]`, or a
    multi-line indented block), so tests can pin the surrounding formatting
    and check it survives a patch untouched."""
    path.write_text(
        "{\n"
        f'  "schema_version": 1,\n'
        f'  "id": {json.dumps(ident)},\n'
        f'  "title": "test fixture",\n'
        + extra_before
        + f'  "epistemic_status": "proved",\n'
        f'  "external_status": "proved",\n'
        f'  "depends_on": {depends_on_literal},\n'
        f'  "proof_route": "kernel-lean",\n'
        f'  "evidence": [\n'
        f'    {{\n'
        f'      "id": {json.dumps(f"kernel-{theorem}")},\n'
        f'      "kind": "kernel-term",\n'
        f'      "checker_command": {json.dumps(f"nat_theorem_inventory -- {theorem}")}\n'
        f'    }}\n'
        f'  ]\n'
        "}\n",
        encoding="utf-8",
    )


class MissingEdgesByFactMatchesEvaluate(unittest.TestCase):
    """`--fix` must add exactly what `evaluate` would otherwise report as a
    failure -- never more, never less. The two traversals share `_kernel_index`
    but recombine its output differently (per-message vs. per-fact-set), so
    this pins them to agree on the total edge count."""

    def test_edge_totals_agree_between_the_two_traversals(self) -> None:
        facts = {
            "F:a": fact("F:a", r"Nat\.mul_one"),
            "F:b": fact("F:b", r"Nat\.zero_add"),
            "F:c": fact("F:c", r"Nat\.add_comm"),
        }
        graph = {
            "Nat.mul_one": ["Nat.zero_add", "Nat.add_comm"],
            "Nat.zero_add": [],
            "Nat.add_comm": [],
        }
        failures, stats = DD.evaluate(facts, graph)
        missing = DD.missing_edges_by_fact(facts, graph)
        self.assertEqual(stats["missing_edges"], sum(len(v) for v in missing.values()))
        self.assertEqual(len(failures), sum(len(v) for v in missing.values()))

    def test_a_fact_does_not_need_itself_even_if_the_graph_says_so(self) -> None:
        """A theorem cannot be its own dependency in this ledger's accounting
        -- `needed == ident` is explicitly excluded in both traversals."""
        facts = {"F:a": fact("F:a", r"Nat\.mul_one")}
        graph = {"Nat.mul_one": ["Nat.mul_one"]}
        missing = DD.missing_edges_by_fact(facts, graph)
        self.assertEqual(missing, {})

    def test_nothing_missing_yields_an_empty_mapping(self) -> None:
        facts = {
            "F:a": fact("F:a", r"Nat\.mul_one", ["F:b"]),
            "F:b": fact("F:b", r"Nat\.zero_add"),
        }
        graph = {"Nat.mul_one": ["Nat.zero_add"], "Nat.zero_add": []}
        self.assertEqual(DD.missing_edges_by_fact(facts, graph), {})


class PatchDependsOnPreservesEverythingElse(unittest.TestCase):
    """Surgical text substitution, never a JSON re-dump: a lane tried the
    re-dump on 2026-08-29, watched it reformat unrelated compact arrays
    across the file, and reverted before committing. Every guard here is
    about NOT touching anything but the `depends_on` array's own bytes."""

    def test_the_regex_stops_at_the_first_closing_bracket_never_the_last(
        self,
    ) -> None:
        """The `[^\\[\\]]*` non-nesting class is what makes the array span
        exact rather than approximate. A greedy `.*` would still match on
        every committed multi-line file (`.` does not cross the newline
        `depends_on` always has before its own closing `]`), so only a
        same-line adversarial case exercises the difference."""
        text = '{"depends_on": ["F:a"], "other": [1,2,3]}'
        found = DD._DEPENDS_ON_RE.search(text)
        self.assertEqual(found.group(1), '["F:a"]')

    def test_single_line_empty_array_gets_new_entries(self) -> None:
        text = '{\n  "depends_on": [],\n  "other": "x"\n}\n'
        patched = DD._patch_depends_on(text, ["F:b", "F:a"])
        self.assertEqual(json.loads(patched)["depends_on"], ["F:a", "F:b"])
        self.assertNotIn("\n", DD._DEPENDS_ON_RE.search(patched).group(1))

    def test_single_line_nonempty_array_appends_in_sorted_order(self) -> None:
        text = '{\n  "depends_on": ["F:a", "F:c"],\n  "other": "x"\n}\n'
        patched = DD._patch_depends_on(text, ["F:b"])
        self.assertEqual(json.loads(patched)["depends_on"], ["F:a", "F:c", "F:b"])

    def test_multiline_array_keeps_its_own_entry_and_closing_indent(self) -> None:
        text = (
            '{\n'
            '  "depends_on": [\n'
            '        "F:int-add-assoc",\n'
            '        "F:int-add-comm"\n'
            '    ],\n'
            '  "other": "unchanged"\n'
            "}\n"
        )
        patched = DD._patch_depends_on(text, ["F:int-le-dest"])
        self.assertEqual(
            json.loads(patched)["depends_on"],
            ["F:int-add-assoc", "F:int-add-comm", "F:int-le-dest"],
        )
        self.assertIn('\n        "F:int-le-dest"\n    ]', patched)

    def test_a_field_already_satisfying_the_request_is_untouched_byte_for_byte(
        self,
    ) -> None:
        """The false-positive control: asking to add something already
        present must not rewrite the array at all -- not even to the same
        semantic content in different bytes. The array deliberately has NO
        space after its commas, which a reformat-via-`json.dumps` would add
        back (`", "` is the module's own join separator) -- so this fails if
        the no-op short-circuit is ever deleted, even though the reformatted
        array would still parse to the same list."""
        text = '{\n  "depends_on": ["F:a","F:b"],\n  "other": "x"\n}\n'
        patched = DD._patch_depends_on(text, ["F:a"])
        self.assertEqual(patched, text)

    def test_raises_when_the_file_has_no_depends_on_array(self) -> None:
        with self.assertRaises(ValueError):
            DD._patch_depends_on('{\n  "other": "x"\n}\n', ["F:a"])

    def test_only_the_depends_on_span_changes_everything_else_is_byte_identical(
        self,
    ) -> None:
        """Mask the `depends_on` array out of both texts and require the rest
        to match exactly -- the direct test of the constraint this whole
        function exists to satisfy."""
        text = (
            '{\n'
            '  "schema_version": 1,\n'
            '  "id": "F:x",\n'
            '  "depends_on": [\n'
            '        "F:a"\n'
            '    ],\n'
            '  "evidence": [{"checker_command": "x [1, 2, 3] y"}]\n'
            "}\n"
        )
        patched = DD._patch_depends_on(text, ["F:z"])

        def masked(t: str) -> str:
            return DD._DEPENDS_ON_RE.sub('"depends_on": MASK', t)

        self.assertEqual(masked(text), masked(patched))
        self.assertNotEqual(text, patched)


class MainDispatchesTheFixFlag(unittest.TestCase):
    """`--fix` is a branch in `main`, not a separate entry point -- so a
    deleted dispatch line falls through to the read-only check, which never
    writes and would leave this test's regressed file un-repaired."""

    def test_main_with_fix_writes_the_missing_edge_and_returns_zero(self) -> None:
        with tempfile.TemporaryDirectory() as tmp_str:
            tmp = pathlib.Path(tmp_str)
            write_fact_file(tmp / "F-a.json", "F:a", r"Nat\.mul_one", "[]")
            write_fact_file(tmp / "F-b.json", "F:b", r"Nat\.zero_add", "[]")

            original_facts_dir = DD.FACTS
            original_inventory = DD.inventory
            try:
                DD.FACTS = tmp
                DD.inventory = lambda: {
                    "Nat.mul_one": ["Nat.zero_add"],
                    "Nat.zero_add": [],
                    **{f"Nat.pad{i}": [] for i in range(140)},  # clear the floor
                }
                rc = DD.main(["--fix"])
            finally:
                DD.FACTS = original_facts_dir
                DD.inventory = original_inventory

            self.assertEqual(rc, 0)
            a_data = json.loads((tmp / "F-a.json").read_text(encoding="utf-8"))
            self.assertEqual(a_data["depends_on"], ["F:b"])

    def test_main_without_fix_on_the_same_regression_reports_failure_only(
        self,
    ) -> None:
        """The control: the identical regressed ledger, through the DEFAULT
        (non-`--fix`) path, must fail without writing anything."""
        with tempfile.TemporaryDirectory() as tmp_str:
            tmp = pathlib.Path(tmp_str)
            write_fact_file(tmp / "F-a.json", "F:a", r"Nat\.mul_one", "[]")
            write_fact_file(tmp / "F-b.json", "F:b", r"Nat\.zero_add", "[]")
            before = (tmp / "F-a.json").read_bytes()

            original_facts_dir = DD.FACTS
            original_inventory = DD.inventory
            try:
                DD.FACTS = tmp
                DD.inventory = lambda: {
                    "Nat.mul_one": ["Nat.zero_add"],
                    "Nat.zero_add": [],
                    **{f"Nat.pad{i}": [] for i in range(140)},
                }
                rc = DD.main(["--quiet"])
            finally:
                DD.FACTS = original_facts_dir
                DD.inventory = original_inventory

            self.assertEqual(rc, 1)
            self.assertEqual((tmp / "F-a.json").read_bytes(), before)


class FixWritesOnlyWhatIsMissing(unittest.TestCase):
    """End-to-end `--fix`, over a scratch fact ledger (never the committed
    one) so a broken mutant cannot touch what any other lane is compiling
    against."""

    def _facts_by_path(self, tmp: pathlib.Path):
        return {
            ident: (path, json.loads(path.read_text(encoding="utf-8")))
            for ident, path in {
                "F:a": tmp / "F-a.json",
                "F:b": tmp / "F-b.json",
            }.items()
        }

    def test_the_drifting_fact_is_patched_and_the_healthy_one_is_untouched(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmp_str:
            tmp = pathlib.Path(tmp_str)
            write_fact_file(tmp / "F-a.json", "F:a", r"Nat\.mul_one", "[]")
            write_fact_file(tmp / "F-b.json", "F:b", r"Nat\.zero_add", "[]")
            healthy_bytes_before = (tmp / "F-b.json").read_bytes()

            graph = {"Nat.mul_one": ["Nat.zero_add"], "Nat.zero_add": []}
            original_facts_dir = DD.FACTS
            try:
                DD.FACTS = tmp
                rc = DD.fix(self._facts_by_path(tmp), graph)
            finally:
                DD.FACTS = original_facts_dir

            self.assertEqual(rc, 0)
            a_data = json.loads((tmp / "F-a.json").read_text(encoding="utf-8"))
            self.assertEqual(a_data["depends_on"], ["F:b"])
            # The false-positive control: F:b needed nothing, so its file must
            # be byte-for-byte untouched, not merely semantically equivalent.
            self.assertEqual((tmp / "F-b.json").read_bytes(), healthy_bytes_before)

    def test_a_fully_healthy_ledger_reports_nothing_to_fix_and_writes_nothing(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmp_str:
            tmp = pathlib.Path(tmp_str)
            write_fact_file(tmp / "F-a.json", "F:a", r"Nat\.mul_one", '["F:b"]')
            write_fact_file(tmp / "F-b.json", "F:b", r"Nat\.zero_add", "[]")
            before = {p.name: p.read_bytes() for p in tmp.glob("*.json")}

            graph = {"Nat.mul_one": ["Nat.zero_add"], "Nat.zero_add": []}
            original_facts_dir = DD.FACTS
            try:
                DD.FACTS = tmp
                rc = DD.fix(self._facts_by_path(tmp), graph)
            finally:
                DD.FACTS = original_facts_dir

            self.assertEqual(rc, 0)
            after = {p.name: p.read_bytes() for p in tmp.glob("*.json")}
            self.assertEqual(before, after)

    def test_the_reload_self_check_fails_the_fix_if_a_patch_did_not_take(
        self,
    ) -> None:
        """If `_patch_depends_on` is broken and silently fails to add the
        edge it claims to, `fix` must not report success -- it re-reads its
        own writes from disk and re-evaluates rather than trusting the
        in-memory patch."""
        with tempfile.TemporaryDirectory() as tmp_str:
            tmp = pathlib.Path(tmp_str)
            write_fact_file(tmp / "F-a.json", "F:a", r"Nat\.mul_one", "[]")
            write_fact_file(tmp / "F-b.json", "F:b", r"Nat\.zero_add", "[]")

            graph = {"Nat.mul_one": ["Nat.zero_add"], "Nat.zero_add": []}
            original_facts_dir = DD.FACTS
            original_patch = DD._patch_depends_on
            try:
                DD.FACTS = tmp
                DD._patch_depends_on = lambda text, additional: text  # no-op mutant
                rc = DD.fix(self._facts_by_path(tmp), graph)
            finally:
                DD.FACTS = original_facts_dir
                DD._patch_depends_on = original_patch

            self.assertEqual(rc, 1)


if __name__ == "__main__":
    unittest.main()
