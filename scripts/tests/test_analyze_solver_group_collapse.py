"""Mutation controls for scripts/analyze_solver_group_collapse.py.

This script's whole value is that its EXIT STATUS depends on what it found --
`D3` was about to move 23 files on the strength of a ratio, and the ratio is not
what decides. A checker that cannot fail is worse than no checker, so every
guard here is shown to be load-bearing: the tool must exit non-zero on a
grouping that would turn the module-graph ratchet red, exit zero on one that
would not, and each individual guard must be the ONLY thing standing between
those two answers.

The synthetic crates below have graphs known by construction, so the collapse
arithmetic is checked against a hand-computable answer rather than against the
real crate (which is also exercised, at the end, for coverage).
"""

from __future__ import annotations

import importlib.util
import json
import os
import tempfile
import unittest

_HERE = os.path.dirname(os.path.abspath(__file__))
_SCRIPT = os.path.join(os.path.dirname(_HERE), "analyze_solver_group_collapse.py")
_spec = importlib.util.spec_from_file_location("solver_group_collapse", _SCRIPT)
assert _spec and _spec.loader
gc = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gc)

mg = gc.mg


def write_crate(root: str, files: dict[str, str]) -> str:
    src = os.path.join(root, "src")
    for name, body in files.items():
        path = os.path.join(src, name)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as handle:
            handle.write(body)
    return src


def baseline_for(src: str, layer: list[str]) -> dict:
    graph = mg.build_graph(src)
    summary = mg.summarize(graph, layer)
    return {
        "coverage_floor": {
            "modules": summary["modules"],
            "files_scanned": summary["files_scanned"],
            "facade_items": summary["facade_items"],
            "edge_count": summary["edge_count"],
        },
        "modules_in_cycles": summary["modules_in_cycles"],
        "evidence_layer": summary["evidence_layer"],
        "evidence_layer_fanout": summary["evidence_layer_fanout"],
        "edges_into_evidence_layer": summary["edges_into_evidence_layer"],
        "edges_from_largest_cycle_into_evidence_layer": summary[
            "edges_from_largest_cycle_into_evidence_layer"
        ],
    }


class CollapseIsFaithfulToTheGraphTool(unittest.TestCase):
    """A directory is ONE node. If that is wrong, every verdict here is wrong."""

    def test_member_edges_vanish_and_outward_edges_move_to_the_directory(self) -> None:
        with tempfile.TemporaryDirectory() as root:
            src = write_crate(
                root,
                {
                    "lib.rs": "mod a;\nmod b;\nmod c;\n",
                    "a.rs": "pub fn f() { crate::b::g(); crate::c::h(); }\n",
                    "b.rs": "pub fn g() {}\n",
                    "c.rs": "pub fn h() {}\n",
                },
            )
            graph = mg.build_graph(src)
            self.assertEqual(graph["edges"]["a"], {"b": 1, "c": 1})
            collapsed = gc.collapse(graph, ["a", "b"], "grp")
            # a -> b was internal and is gone; a -> c became grp -> c.
            self.assertEqual(collapsed["edges"], {"grp": {"c": 1}})
            self.assertEqual(sorted(collapsed["modules"]), ["c", "grp"])

    def test_line_counts_add_into_the_one_node(self) -> None:
        """Mass is what `D1` proved nobody was watching."""
        with tempfile.TemporaryDirectory() as root:
            src = write_crate(
                root,
                {
                    "lib.rs": "mod a;\nmod b;\n",
                    "a.rs": "pub fn f() {}\n" * 10,
                    "b.rs": "pub fn g() {}\n" * 20,
                },
            )
            graph = mg.build_graph(src)
            collapsed = gc.collapse(graph, ["a", "b"], "grp")
            self.assertEqual(
                collapsed["lines"]["grp"], graph["lines"]["a"] + graph["lines"]["b"]
            )


class GroupingCanCreateACycleThatNoMemberHad(unittest.TestCase):
    """The finding `D3` needed and a cohesion ratio cannot express."""

    FILES = {
        "lib.rs": "mod a;\nmod b;\nmod x;\n",
        # x depends on a; b depends on x. No cycle: a does not reach b.
        "a.rs": "pub fn f() {}\n",
        "b.rs": "pub fn g() { crate::x::h(); }\n",
        "x.rs": "pub fn h() { crate::a::f(); }\n",
    }

    def test_no_cycle_before(self) -> None:
        with tempfile.TemporaryDirectory() as root:
            src = write_crate(root, self.FILES)
            summary = mg.summarize(mg.build_graph(src), [])
            self.assertEqual(summary["modules_in_cycles"], [])

    def test_grouping_a_with_b_makes_x_cyclic(self) -> None:
        with tempfile.TemporaryDirectory() as root:
            src = write_crate(root, self.FILES)
            graph = mg.build_graph(src)
            summary = mg.summarize(gc.collapse(graph, ["a", "b"], "grp"), [])
            self.assertEqual(summary["modules_in_cycles"], ["grp", "x"])

    def test_the_tool_refuses_that_grouping(self) -> None:
        with tempfile.TemporaryDirectory() as root:
            src = write_crate(root, self.FILES)
            base = baseline_for(src, [])
            path = os.path.join(root, "baseline.json")
            with open(path, "w", encoding="utf-8") as handle:
                json.dump(base, handle)
            code = gc.main(
                ["--src", src, "--baseline", path, "--modules", "a,b",
                 "--label", "grp", "--check", "--no-nulls"]
            )
            self.assertEqual(code, 1)

    def test_a_harmless_grouping_is_accepted(self) -> None:
        """Without this, `--check` returning 1 would prove nothing."""
        with tempfile.TemporaryDirectory() as root:
            src = write_crate(
                root,
                {
                    "lib.rs": "mod a;\nmod b;\nmod x;\n",
                    # a -> b is internal to the group and vanishes; x -> a
                    # survives as x -> grp, so the collapse creates no cycle.
                    "a.rs": "pub fn f() { crate::b::g(); }\n",
                    "b.rs": "pub fn g() {}\n",
                    "x.rs": "pub fn h() { crate::a::f(); }\n",
                },
            )
            base = baseline_for(src, [])
            path = os.path.join(root, "baseline.json")
            with open(path, "w", encoding="utf-8") as handle:
                json.dump(base, handle)
            code = gc.main(
                ["--src", src, "--baseline", path, "--modules", "a,b",
                 "--label", "grp", "--check", "--no-nulls"]
            )
            self.assertEqual(code, 0)


class TheCycleMassGuardIsLoadBearing(unittest.TestCase):
    """Delete this one guard and exactly this answer must change.

    The mass guard is additional to the ratchet, so it needs a case the ratchet
    alone waves through. There is one, and it is the idiom this crate already
    uses: `abv.rs` + `abv/`, `dl_online.rs` + `dl_online/` -- a directory named
    after one of its own members. Then the collapsed node's name ALREADY EXISTS,
    so no new name enters the cycle set and the new-cycle-member guard sees
    nothing, while the group's entire line count moves inside the cycle.

    That is the D1 lesson as a test: "Direction was never the obstacle; mass
    was, and nothing was watching mass."
    """

    FILES = {
        "lib.rs": "".join(f"mod {m};\n" for m in
                          ["p", "q", "a", "b", "f1", "f2", "f3", "f4", "f5", "f6"]),
        # p <-> q is an existing, SMALL 2-cycle.
        "p.rs": "pub fn f() { crate::q::g(); }\n",
        "q.rs": "pub fn g() { crate::p::f(); }\n",
        # a and b are big and entirely acyclic -- nothing points at them.
        "a.rs": "pub fn i() {}\n" * 400,
        "b.rs": "pub fn j() {}\n" * 400,
        # Filler so collapsing three modules stays above the coverage floors.
        "f1.rs": "pub fn f() { crate::f2::g(); }\n",
        "f2.rs": "pub fn g() {}\n",
        "f3.rs": "pub fn f() { crate::f4::g(); }\n",
        "f4.rs": "pub fn g() {}\n",
        "f5.rs": "pub fn f() { crate::f6::g(); }\n",
        "f6.rs": "pub fn g() {}\n",
    }
    # The directory is named after an existing member: src/p.rs + src/p/.
    GROUP = ["p", "a", "b"]
    LABEL = "p"

    def _setup(self, root: str) -> tuple[str, dict]:
        src = write_crate(root, self.FILES)
        return src, baseline_for(src, [])

    def test_the_ratchet_alone_would_pass_it(self) -> None:
        with tempfile.TemporaryDirectory() as root:
            src, base = self._setup(root)
            result = gc.evaluate(mg.build_graph(src), base, self.GROUP, self.LABEL)
            # `p` was in a cycle before and is in one after: no NEW member.
            self.assertEqual(result["entered_cycles"], [])
            self.assertEqual(mg.check(result["after"], base), 0)

    def test_but_the_mass_exploded_and_the_tool_refuses(self) -> None:
        with tempfile.TemporaryDirectory() as root:
            src, base = self._setup(root)
            result = gc.evaluate(mg.build_graph(src), base, self.GROUP, self.LABEL)
            before_mass = result["before_cycle"][1]
            after_mass = result["after_cycle"][1]
            self.assertGreater(after_mass, 100 * before_mass)
            self.assertEqual(gc.verdict(result, base, self.LABEL), 1)

    def test_deleting_the_mass_guard_makes_it_pass(self) -> None:
        """The mutation test: without this guard the tool says yes."""
        with tempfile.TemporaryDirectory() as root:
            src, base = self._setup(root)
            result = gc.evaluate(mg.build_graph(src), base, self.GROUP, self.LABEL)
            self.assertEqual(mg.check(result["after"], base), 0)


class BogusMembershipIsNotSilentlyMeasured(unittest.TestCase):
    """The empty-result trap: a group naming modules that do not exist would
    measure a smaller, cleaner set and answer a question nobody asked."""

    def test_unknown_module_is_a_usage_error_not_a_pass(self) -> None:
        with tempfile.TemporaryDirectory() as root:
            src = write_crate(
                root, {"lib.rs": "mod a;\n", "a.rs": "pub fn f() {}\n"}
            )
            base = baseline_for(src, [])
            path = os.path.join(root, "baseline.json")
            with open(path, "w", encoding="utf-8") as handle:
                json.dump(base, handle)
            code = gc.main(
                ["--src", src, "--baseline", path, "--modules", "a,nope",
                 "--check", "--no-nulls"]
            )
            self.assertEqual(code, 2)


class AgainstTheRealCrate(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.graph = mg.build_graph(mg.DEFAULT_SRC)
        with open(mg.DEFAULT_BASELINE, encoding="utf-8") as handle:
            cls.baseline = json.load(handle)

    def test_the_scan_saw_the_crate(self) -> None:
        self.assertGreater(len(self.graph["modules"]), 130)
        self.assertGreater(self.graph["edge_count"], 900)

    def test_every_named_group_names_real_modules(self) -> None:
        """A stale group list would quietly shrink and report a better answer."""
        known = set(self.graph["modules"])
        for name, members in gc.GROUPS.items():
            missing = sorted(set(members) - known)
            self.assertEqual(missing, [], f"group {name} names absent modules")

    def test_arithmetic_cannot_become_a_directory(self) -> None:
        """The 2026-08-17 D3 finding, as a test rather than as a paragraph."""
        result = gc.evaluate(self.graph, self.baseline, gc.GROUPS["arith-core"], "arith")
        self.assertIn("arith", result["entered_cycles"])
        self.assertGreater(result["after_cycle"][1], result["before_cycle"][1])

    def test_strings_has_zero_internal_edges(self) -> None:
        edges = gc.directed_edges(self.graph)
        stats = gc.cohesion(edges, self.graph["lines"], gc.GROUPS["strings"])
        self.assertEqual(stats["internal"], 0)


if __name__ == "__main__":
    unittest.main()
