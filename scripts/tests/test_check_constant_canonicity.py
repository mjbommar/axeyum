"""Tests for `scripts/check-constant-canonicity.py`.

Every failure case is asserted against `evaluate()` -- which returns the
findings list -- rather than against `main()`'s exit status. That is
deliberate and is what makes the mutation controls in
`scripts/tests/mutation_controls.py` discriminate: if every failure test
went through `main()`, the single mutation `return 1` -> `return 0` would
kill all of them at once, and a control that kills eleven tests measures
nothing about the eleven guards. `MainExitStatusTests` is the one place
`main()`'s status is asserted, so that mutation kills exactly one test.

Fixtures are synthetic projections in the real
`kernel_declaration_projection` TSV shape (8 tab-separated fields:
label, kind, name, footprint, type-deps, all-deps, theorem-deps, type).
The end-to-end proof that the gate fires on a real kernel that really
declares two pi-shaped constants is recorded in ADR-1320; these tests are
the per-guard controls.
"""

from __future__ import annotations

import importlib.util
import os
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(
    os.environ.get(
        "CHECK_CONSTANT_CANONICITY_SCRIPT",
        str(Path(__file__).parents[1] / "check-constant-canonicity.py"),
    )
)
SPEC = importlib.util.spec_from_file_location("check_constant_canonicity", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def row(kind: str, name: str, type_deps: str, ctype: str, label: str = "t") -> str:
    return "\t".join([label, kind, name, "0", type_deps, type_deps, "", ctype])


# A miniature environment in the real projection shape. `CReal` is an
# inductive at `Sort (1)` (a data carrier); `WellFounded` is a definition
# whose result is `Prop`, so `Nat.lt_well_founded` -- a genuine nullary
# definition -- is a PROOF and must be excluded from the population without
# any hand-written exemption.
PROJECTION = "\n".join(
    [
        row("inductive", "CReal", "", "Sort (1)"),
        row("definition", "CReal.zero", "CReal", "CReal"),
        row("definition", "CReal.one", "CReal", "CReal"),
        row("definition", "CReal.pi", "CReal", "CReal"),
        row("definition", "CReal.piMachin", "CReal", "CReal"),
        row("definition", "CReal.add", "CReal", "((x0 : CReal) -> ((x1 : CReal) -> CReal))"),
        row(
            "theorem",
            "CReal.pi_eq_machin",
            "CReal.Equiv,CReal.pi,CReal.piMachin",
            "CReal.Equiv CReal.pi CReal.piMachin",
        ),
        row(
            "theorem",
            "CReal.zero_lt_one",
            "CReal.lt,CReal.zero,CReal.one",
            "CReal.lt CReal.zero CReal.one",
        ),
    ]
)

# The `Prop` case lives in its OWN fixture, not the shared one. In the shared
# fixture an un-excluded `Nat.lt_well_founded` would be an unadjudicated
# constant in every test, so deleting the exclusion would kill ten tests --
# and a control that kills ten measures nothing about the guard it names.
PROP_PROJECTION = "\n".join(
    [
        row("inductive", "CReal", "", "Sort (1)"),
        row("definition", "CReal.zero", "CReal", "CReal"),
        row(
            "definition",
            "WellFounded",
            "",
            "((x0 : Sort (u)) -> ((x1 : ((x1 : x0) -> ((x2 : x0) -> Prop))) -> Prop))",
        ),
        row(
            "definition",
            "Nat.lt_well_founded",
            "WellFounded",
            "WellFounded.{1} AxNat AxNat.lt",
        ),
    ]
)

HEADER = "\t".join(MODULE.COLUMNS)
BASE_ROWS = [
    "CReal\tCReal.zero\tzero\tcanonical\t-\tThe additive identity.",
    "CReal\tCReal.one\tone\tcanonical\t-\tThe multiplicative identity.",
    "CReal\tCReal.pi\tpi\tcanonical\t-\tArchimedes constant.",
]


def registry(*extra: str) -> list:
    """Load a registry made of the base rows plus `extra`."""
    text = "\n".join(["# comment", HEADER, *BASE_ROWS, *extra]) + "\n"
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "registry.tsv"
        path.write_text(text)
        return MODULE.load_registry(path)


def findings(*extra: str, projection: str = PROJECTION) -> list[str]:
    decls = MODULE.parse_projection(projection)
    pop = MODULE.constants(decls)
    return MODULE.evaluate(pop, registry(*extra), decls)


def codes(items: list[str]) -> list[str]:
    return sorted({item.split()[0] for item in items})


ALTERNATE_OK = "CReal\tCReal.piMachin\tpi\talternate\tCReal.pi_eq_machin\tMachin's construction."


class PopulationTests(unittest.TestCase):
    def test_the_population_is_the_nullary_data_valued_definitions(self):
        # Deliberately a superset assertion, not an equality: the `Prop`
        # exclusion has its own test below, and asserting the exact set here
        # too would make one mutation kill two tests.
        pop = MODULE.constants(MODULE.parse_projection(PROJECTION))
        self.assertLessEqual(
            {"CReal.one", "CReal.pi", "CReal.piMachin", "CReal.zero"}, set(pop)
        )
        self.assertNotIn("CReal", pop)  # the inductive carrier is not a constant

    def test_a_nullary_prop_valued_definition_is_excluded_as_a_proof(self):
        """`Nat.lt_well_founded` is nullary but lands in `Prop`.

        The exclusion is DERIVED -- `WellFounded`'s own declaration is looked
        up and its result sort read -- not a hand-written exemption. Deleting
        the derivation would demand a registry row for every proof-valued
        definition in the kernel, which is the shape of gate lanes disable.
        """
        decls = MODULE.parse_projection(PROP_PROJECTION)
        pop = MODULE.constants(decls)
        self.assertEqual(sorted(pop), ["CReal.zero"])
        self.assertTrue(MODULE.is_proof_valued("WellFounded.{1} AxNat AxNat.lt", decls))
        self.assertFalse(MODULE.is_proof_valued("CReal", decls))

    def test_a_function_valued_definition_is_not_a_constant(self):
        pop = MODULE.constants(MODULE.parse_projection(PROJECTION))
        self.assertNotIn("CReal.add", pop)

    def test_dependencies_are_read_from_the_type_column_not_the_proof_column(self):
        """A bridge must be STATED, not merely used.

        The projection carries both a theorem's type dependencies (column 5)
        and its all-kinds dependencies including the proof term (column 6).
        Reading the wrong one would accept as a bridge any theorem whose PROOF
        happens to touch both constants while its statement relates nothing --
        `CReal.e_converges`'s proof touches 60-odd declarations its type never
        mentions.
        """
        raw = "\t".join(
            [
                "t", "theorem", "CReal.stated_about_order", "0",
                "CReal.lt",                      # type dependencies
                "CReal.lt,CReal.pi,CReal.piMachin",  # proof-term dependencies
                "", "CReal.lt CReal.zero CReal.one",
            ]
        )
        decls = MODULE.parse_projection(raw)
        self.assertEqual(decls["CReal.stated_about_order"].type_deps, frozenset({"CReal.lt"}))

    def test_a_name_declared_in_several_preludes_unions_its_type_dependencies(self):
        text = "\n".join(
            [
                PROJECTION,
                row("theorem", "CReal.pi_eq_machin", "CReal.pi", "CReal.Equiv CReal.pi CReal.piMachin", "complex"),
            ]
        )
        decls = MODULE.parse_projection(text)
        self.assertEqual(
            decls["CReal.pi_eq_machin"].type_deps,
            frozenset({"CReal.Equiv", "CReal.pi", "CReal.piMachin"}),
        )


class CleanTests(unittest.TestCase):
    def test_a_fully_adjudicated_environment_has_no_findings(self):
        self.assertEqual(findings(ALTERNATE_OK), [])

    def test_a_bridge_whose_stated_type_names_both_constants_is_accepted(self):
        self.assertEqual(codes(findings(ALTERNATE_OK)), [])


class GuardTests(unittest.TestCase):
    def test_g1_a_constant_with_no_registry_row_fails(self):
        found = findings()  # CReal.piMachin has no row at all
        self.assertEqual(codes(found), ["G1"])
        self.assertIn("CReal.piMachin", found[0])

    def test_g2_a_row_naming_a_constant_the_kernel_lacks_fails(self):
        found = findings(
            ALTERNATE_OK,
            "CReal\tCReal.piChudnovsky\tpi\talternate\tCReal.pi_eq_machin\tRemoved from the kernel.",
        )
        self.assertIn("G2", codes(found))
        self.assertTrue(any("CReal.piChudnovsky" in f for f in found))

    def test_g3_a_row_whose_carrier_is_not_the_kernels_type_fails(self):
        found = findings(
            "Complex\tCReal.piMachin\tpi\tcanonical\t-\tMislabelled carrier, distinct-from:pi."
        )
        self.assertIn("G3", codes(found))

    def test_g4_two_canonical_constants_for_one_object_fails(self):
        found = findings("CReal\tCReal.piMachin\tpi\tcanonical\t-\tAlso pi.")
        self.assertIn("G4", codes(found))

    def test_g5_an_alternate_whose_object_has_no_canonical_fails(self):
        found = findings(
            "CReal\tCReal.piMachin\te\talternate\tCReal.pi_eq_machin\tNo canonical for object e."
        )
        self.assertIn("G5", codes(found))

    def test_g6_an_alternate_naming_no_bridge_fails(self):
        found = findings("CReal\tCReal.piMachin\tpi\talternate\t-\tMachin's construction.")
        self.assertEqual(codes(found), ["G6"])

    def test_g7_a_bridge_that_is_not_a_theorem_in_the_kernel_fails(self):
        absent = findings("CReal\tCReal.piMachin\tpi\talternate\tCReal.pi_eq_leibniz\tMachin.")
        self.assertEqual(codes(absent), ["G7"])
        # A DEFINITION of that name is not a bridge either: a bridge must
        # carry a proof, and a definition is admitted on well-typedness alone.
        wrong_kind = findings("CReal\tCReal.piMachin\tpi\talternate\tCReal.add\tMachin.")
        self.assertEqual(codes(wrong_kind), ["G7"])

    def test_g8_a_bridge_that_does_not_state_the_relation_fails(self):
        """The bridge exists and is a theorem -- about the wrong constants.

        `CReal.zero_lt_one`'s stated type mentions neither pi nor piMachin.
        This is the guard that keeps the registry from being self-certifying:
        without it any real theorem name would satisfy an alternate row.
        """
        found = findings("CReal\tCReal.piMachin\tpi\talternate\tCReal.zero_lt_one\tMachin.")
        self.assertEqual(codes(found), ["G8"])
        self.assertIn("CReal.pi", found[0])


    def test_g9_a_row_with_no_reason_fails(self):
        found = findings("CReal\tCReal.piMachin\tpi\talternate\tCReal.pi_eq_machin\t")
        self.assertIn("G9", codes(found))

    def test_g10_prefix_matching_names_registered_as_different_objects_fails(self):
        found = findings(
            "CReal\tCReal.piMachin\tpi-machin\tcanonical\t-\tMachin series constant."
        )
        self.assertEqual(codes(found), ["G10"])
        self.assertIn("distinct-from:pi", found[0])

    def test_g10_an_explicit_distinct_from_claim_is_accepted(self):
        self.assertEqual(
            findings(
                "CReal\tCReal.piMachin\tpi-machin\tcanonical\t-\t"
                "A different real, distinct-from:pi -- explicit and attributable."
            ),
            [],
        )

    def test_g10_does_not_fire_on_the_constants_that_exist_today(self):
        """No false positive on the real population.

        A heuristic that fires on `CReal.one` versus `CReal.cosOne` would be
        turned off within a day. Measured over the 16 real constants: zero.
        """
        pairs = [
            ("zero", "one"), ("one", "cosOne"), ("cosOne", "sinOne"),
            ("e", "cosOne"), ("two", "three"), ("inv2", "inv3"),
        ]
        for left, right in pairs:
            with self.subTest(pair=(left, right)):
                ls, rs = MODULE.stem(f"CReal.{left}"), MODULE.stem(f"CReal.{right}")
                short, long_ = (ls, rs) if len(ls) <= len(rs) else (rs, ls)
                self.assertFalse(
                    len(short) >= MODULE.MIN_STEM and long_.startswith(short),
                    f"{left}/{right} would collide",
                )
        self.assertTrue(MODULE.stem("CReal.piMachin").startswith(MODULE.stem("CReal.pi")))

    def test_g11_two_rows_for_one_constant_fails(self):
        found = findings(
            "CReal\tCReal.piMachin\tpi\talternate\tCReal.pi_eq_machin\tMachin.",
            "CReal\tCReal.piMachin\tpi\talternate\tCReal.pi_eq_machin\tMachin again.",
        )
        self.assertIn("G11", codes(found))


class RegistryFormatTests(unittest.TestCase):
    def _load(self, text: str):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "r.tsv"
            path.write_text(text)
            return MODULE.load_registry(path)

    def test_a_row_with_the_wrong_field_count_is_an_error(self):
        with self.assertRaises(MODULE.RegistryError):
            self._load(f"{HEADER}\nCReal\tCReal.pi\tpi\tcanonical\n")

    def test_an_unknown_role_is_an_error(self):
        with self.assertRaises(MODULE.RegistryError):
            self._load(f"{HEADER}\nCReal\tCReal.pi\tpi\tprobably\t-\tReason.\n")

    def test_a_missing_header_is_an_error(self):
        with self.assertRaises(MODULE.RegistryError):
            self._load("CReal\tCReal.pi\tpi\tcanonical\t-\tReason.\n")


class ProjectionFormatTests(unittest.TestCase):
    def test_a_row_with_the_wrong_field_count_is_an_error(self):
        with self.assertRaises(MODULE.ProjectionFormatError):
            MODULE.parse_projection("t\tdefinition\tCReal.pi\t0\tCReal\n")

    def test_one_name_declared_with_two_types_is_an_error(self):
        text = "\n".join(
            [
                row("definition", "CReal.pi", "CReal", "CReal"),
                row("definition", "CReal.pi", "CReal", "Complex", "complex"),
            ]
        )
        with self.assertRaises(MODULE.ProjectionFormatError):
            MODULE.parse_projection(text)


class MainExitStatusTests(unittest.TestCase):
    """The ONLY place `main()`'s status is asserted.

    Keeping it in one place is what lets `return 1` -> `return 0` kill
    exactly one test instead of every failure test at once.
    """

    def _run(self, registry_text: str, projection_text: str = PROJECTION) -> int:
        with tempfile.TemporaryDirectory() as tmp:
            reg = Path(tmp) / "r.tsv"
            reg.write_text(registry_text)
            proj = Path(tmp) / "p.tsv"
            proj.write_text(projection_text)
            return MODULE.main(
                ["--registry", str(reg), "--projection-file", str(proj)]
            )

    def _registry(self, *extra: str) -> str:
        return "\n".join([HEADER, *BASE_ROWS, *extra]) + "\n"

    def test_a_clean_run_exits_zero(self):
        self.assertEqual(self._run(self._registry(ALTERNATE_OK)), 0)

    def test_a_finding_exits_one(self):
        """Two INDEPENDENT findings, deliberately.

        With only one, deleting that guard would make this test die too and
        the guard's own control would score two kills. Two findings mean this
        test measures the exit status and nothing else.
        """
        registry_text = self._registry(
            "CReal\tCReal.piMachin\tpi\talternate\tCReal.pi_eq_machin\t",  # G9
            "CReal\tCReal.piLeibniz\tpi\talternate\tCReal.pi_eq_machin\tAbsent.",  # G2
        )
        self.assertEqual(self._run(registry_text), 1)

    def test_an_empty_authority_exits_two_rather_than_passing(self):
        """A projection with no constants is a broken tool, not a clean tree.

        This repository has shipped checkers that exit 0 on completion alone;
        an empty population must never read as "nothing to adjudicate".
        """
        self.assertEqual(self._run(self._registry(ALTERNATE_OK), "t\tinductive\tCReal\t0\t\t\t\tSort (1)"), 2)

    def test_a_malformed_registry_exits_two(self):
        self.assertEqual(self._run("nonsense\n"), 2)

    def test_an_unreadable_projection_file_exits_two(self):
        with tempfile.TemporaryDirectory() as tmp:
            reg = Path(tmp) / "r.tsv"
            reg.write_text(self._registry(ALTERNATE_OK))
            self.assertEqual(
                MODULE.main(
                    ["--registry", str(reg), "--projection-file", str(Path(tmp) / "absent.tsv")]
                ),
                2,
            )


class RealRegistryTests(unittest.TestCase):
    """The shipped registry must parse and cover a plausible carrier set."""

    def test_the_shipped_registry_loads(self):
        rows = MODULE.load_registry(MODULE.DEFAULT_REGISTRY)
        self.assertGreaterEqual(len(rows), 16)
        self.assertEqual(
            sorted({r.carrier for r in rows}), ["CReal", "Complex", "Int", "Rat"]
        )

    def test_every_shipped_row_carries_a_reason(self):
        for r in MODULE.load_registry(MODULE.DEFAULT_REGISTRY):
            with self.subTest(constant=r.constant):
                self.assertTrue(r.reason.strip())


if __name__ == "__main__":
    unittest.main()
