"""Focused tests for `scripts/gen-ledger-coverage.py`.

Each test targets one guard/behaviour; `scripts/tests/mutation_controls.py
ledger-coverage` deletes guards one at a time and requires each deletion to
kill exactly one test.

None of these invoke cargo: `parse_theorem_inventory` is tested against
synthetic TSV text in the tool's own shape, and `resolve_theorem_name` /
`join` / `build_document` are tested against synthetic fact dicts. The one
place a real measurement matters -- "does the committed artifact match a
fresh generation" -- is `scripts/check.sh`'s `gen-ledger-coverage --check`
step, not this file.
"""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "gen-ledger-coverage.py"
SPEC = importlib.util.spec_from_file_location("gen_ledger_coverage", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def fact(fid: str, **overrides) -> dict:
    base = {
        "id": fid,
        "proof_route": "kernel-lean",
        "epistemic_status": "proved",
        "formal": {"language": "lean4", "statement": "theorem Nat.foo : Nat"},
        "evidence": [],
    }
    base.update(overrides)
    return base


class ParseTheoremInventoryTests(unittest.TestCase):
    def test_parses_name_and_footprint_size(self) -> None:
        stdout = "nat\tNat.add_comm\t0\t\n"
        self.assertEqual(MODULE.parse_theorem_inventory(stdout), {"Nat.add_comm": 0})

    def test_dedups_the_same_name_printed_by_several_nested_prelude_groups(self) -> None:
        # `creal`, `complex` and `cpoint` each build the full nested stack
        # from scratch, so a Nat theorem is printed once per group. Without
        # dedup the by-prelude counts would be multiply-counted (module doc).
        stdout = "nat\tNat.add_comm\t0\t\ncreal\tNat.add_comm\t0\t\n"
        self.assertEqual(MODULE.parse_theorem_inventory(stdout), {"Nat.add_comm": 0})

    def test_disagreeing_footprint_sizes_for_the_same_name_is_an_error(self) -> None:
        stdout = "nat\tNat.add_comm\t0\t\ncreal\tNat.add_comm\t1\tsome.axiom\n"
        with self.assertRaises(MODULE.CoverageError):
            MODULE.parse_theorem_inventory(stdout)

    def test_zero_rows_is_an_error_not_a_silent_empty_denominator(self) -> None:
        # The debug-build SIGABRT / missing --include-constructed trap:
        # CLAUDE.md documents both as producing an empty answer that reads
        # as "measured, and nothing to report" rather than "not measured".
        with self.assertRaises(MODULE.CoverageError):
            MODULE.parse_theorem_inventory("")

    def test_malformed_row_is_an_error(self) -> None:
        with self.assertRaises(MODULE.CoverageError):
            MODULE.parse_theorem_inventory("only-two-fields\there\n")


class PreludeOfTests(unittest.TestCase):
    def test_creal_namespace(self) -> None:
        self.assertEqual(MODULE.prelude_of("CReal.mulPowCongr"), "creal")

    def test_nat_namespace(self) -> None:
        self.assertEqual(MODULE.prelude_of("Nat.add_comm"), "nat")

    def test_string_prelude_has_no_capitalised_namespace(self) -> None:
        # `axeyum.string.2.append_assoc` would otherwise split to head
        # "axeyum", which matches nothing in NAMESPACE_TO_PRELUDE and would
        # silently fall through to "logic" -- wrong.
        self.assertEqual(MODULE.prelude_of("axeyum.string.2.append_assoc"), "string")

    def test_bare_logic_name_falls_back_to_logic(self) -> None:
        self.assertEqual(MODULE.prelude_of("mt"), "logic")

    def test_unnamespaced_type_like_and_falls_back_to_logic(self) -> None:
        # "And.left" is not in NAMESPACE_TO_PRELUDE (only the seven
        # constructed-carrier namespaces are); it belongs to the logic
        # prelude and must bucket there, not be silently dropped.
        self.assertEqual(MODULE.prelude_of("And.left"), "logic")


class ResolveTheoremNameTests(unittest.TestCase):
    def test_explicit_field_string_wins(self) -> None:
        f = fact("F:x", formal={"language": "lean4", "kernel_theorem": "Nat.bar"})
        self.assertEqual(MODULE.resolve_theorem_name(f), ("Nat.bar", "field"))

    def test_explicit_field_null_means_no_single_subject_and_does_not_fall_through(
        self,
    ) -> None:
        f = fact(
            "F:x",
            formal={
                "language": "lean4",
                "statement": "theorem Nat.bar : Nat",
                "kernel_theorem": None,
            },
        )
        self.assertEqual(MODULE.resolve_theorem_name(f), (None, None))

    def test_statement_name_with_theorem_keyword(self) -> None:
        f = fact("F:x", formal={"language": "lean4", "statement": "theorem Nat.bar : Nat"})
        self.assertEqual(MODULE.resolve_theorem_name(f), ("Nat.bar", "statement"))

    def test_statement_name_without_keyword(self) -> None:
        # Some facts store `<Name> : <type>` with the `theorem `/`def `
        # keyword already stripped (e.g. `Complex.no_compatible_order`).
        f = fact(
            "F:x", formal={"language": "lean4", "statement": "And.left : Prop -> Prop"}
        )
        self.assertEqual(MODULE.resolve_theorem_name(f), ("And.left", "statement"))

    def test_placeholder_todo_statement_is_not_treated_as_a_declared_name(self) -> None:
        # F:real-lattice-is-constructed-axiom-free carries the literal
        # statement "TODO: the formal statement, precise enough to dispatch".
        f = fact(
            "F:x",
            formal={
                "language": "lean4",
                "statement": "TODO: the formal statement, precise enough to dispatch",
            },
        )
        name, tier = MODULE.resolve_theorem_name(f)
        self.assertNotEqual(name, "TODO")

    def test_non_lean4_statement_does_not_use_the_statement_tier(self) -> None:
        # `lean4-surface` statements use elaborator syntax / Unicode notation
        # (e.g. `n + a ≡ a [ZMOD n]`) and are not `Kernel::render_lean`
        # output, so the "<Name> :" head pattern must not be trusted here.
        f = fact(
            "F:x",
            formal={"language": "lean4-surface", "statement": "Nat.bar : Nat"},
            evidence=[],
        )
        name, tier = MODULE.resolve_theorem_name(f)
        self.assertNotEqual(tier, "statement")
        self.assertIsNone(name)

    def test_falls_back_to_checker_command_when_field_and_statement_both_fail(self) -> None:
        f = fact(
            "F:x",
            formal={"language": "lean4", "statement": "((x0 : Nat) -> Nat)"},
            evidence=[
                {
                    "checker_command": (
                        "cargo run -q --release -p axeyum-lean-kernel "
                        "--example theorem_dependency_inventory -- bar "
                        "2>/dev/null | grep -cE '^Nat\\.bar[[:space:]]'"
                    )
                }
            ],
        )
        name, tier = MODULE.resolve_theorem_name(f)
        self.assertEqual((name, tier), ("Nat.bar", "checker_command"))

    def test_all_three_tiers_failing_is_unresolved(self) -> None:
        f = fact(
            "F:x",
            formal={"language": "lean4", "statement": "((x0 : Nat) -> Nat)"},
            evidence=[{"checker_command": "cargo test -p axeyum-lean-kernel --lib some_test"}],
        )
        self.assertEqual(MODULE.resolve_theorem_name(f), (None, None))


class JoinTests(unittest.TestCase):
    def test_open_facts_are_not_joined(self) -> None:
        facts = {"F:x": fact("F:x", epistemic_status="open")}
        result = MODULE.join(facts)
        self.assertEqual(result.registered, {})
        self.assertEqual(result.kernel_route_established, 0)

    def test_non_kernel_route_facts_are_not_joined(self) -> None:
        facts = {"F:x": fact("F:x", proof_route="smt-term-level")}
        result = MODULE.join(facts)
        self.assertEqual(result.registered, {})

    def test_resolved_fact_is_registered_under_its_theorem_name(self) -> None:
        facts = {"F:x": fact("F:x")}
        result = MODULE.join(facts)
        self.assertEqual(result.registered, {"Nat.foo": ["F:x"]})

    def test_unresolved_fact_is_reported_not_silently_dropped(self) -> None:
        facts = {
            "F:x": fact(
                "F:x",
                formal={"language": "lean4", "statement": "((x0 : Nat) -> Nat)"},
                evidence=[],
            )
        }
        result = MODULE.join(facts)
        self.assertEqual(result.registered, {})
        self.assertEqual(result.unresolved, ["F:x"])


class BuildDocumentTests(unittest.TestCase):
    def test_unregistered_theorem_appears_in_its_prelude_bucket(self) -> None:
        footprints = {"Nat.add_comm": 0, "Nat.mul_comm": 0}
        result = MODULE.join({"F:x": fact("F:x", formal={"language": "lean4", "kernel_theorem": "Nat.add_comm"})})
        document = MODULE.build_document(footprints, result)
        self.assertEqual(document["counts"]["overall"]["kernel_theorems"], 2)
        self.assertEqual(document["counts"]["overall"]["registered"], 1)
        self.assertEqual(document["counts"]["overall"]["unregistered"], 1)
        self.assertIn("Nat.mul_comm", document["counts"]["by_prelude"]["nat"]["unregistered"])

    def test_a_synthetic_unregistered_theorem_changes_the_rendered_document(self) -> None:
        # The demonstration this ledger's --check gate depends on: adding one
        # kernel theorem nobody registered must change the rendered output,
        # which is exactly what makes `--check` fail against a stale commit.
        footprints_before = {"Nat.add_comm": 0}
        footprints_after = {"Nat.add_comm": 0, "Nat.synthetic_gate_demo": 0}
        empty_join = MODULE.join({})
        before = MODULE.render(MODULE.build_document(footprints_before, empty_join))
        after = MODULE.render(MODULE.build_document(footprints_after, empty_join))
        self.assertNotEqual(before, after)

    def test_registered_name_absent_from_denominator_is_reported_as_stray(self) -> None:
        # A fact naming a Definition (e.g. CReal.integral) rather than a
        # Theorem: not a failure, but must be visible, not silently dropped.
        footprints = {"Nat.add_comm": 0}
        result = MODULE.join(
            {"F:x": fact("F:x", formal={"language": "lean4", "kernel_theorem": "CReal.integral"})}
        )
        document = MODULE.build_document(footprints, result)
        self.assertIn("CReal.integral", document["registered_kernel_theorems_not_in_denominator"])

    def test_render_is_deterministic(self) -> None:
        footprints = {"Nat.add_comm": 0, "Nat.mul_comm": 0}
        result = MODULE.join({})
        first = MODULE.render(MODULE.build_document(footprints, result))
        second = MODULE.render(MODULE.build_document(footprints, result))
        self.assertEqual(first, second)


if __name__ == "__main__":
    unittest.main()
