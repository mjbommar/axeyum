"""Mutation controls for scripts/analyze_solver_module_graph.py.

The graph this script measures is the evidence for every claim in
`docs/refactor-2026-08/03-solver-decomposition.md`. Three naive versions of the
same measurement gave three different answers before the script existed --
doc-link noise invented 231 edges, `#[cfg(test)]` code invented more, and
ignoring the re-export facade hid 340. So every one of those behaviours is
pinned here on synthetic crates whose true graph is known by construction, and
the ratchet is shown to actually fail rather than merely to exit 0.
"""

from __future__ import annotations

import importlib.util
import json
import os
import tempfile
import unittest

_HERE = os.path.dirname(os.path.abspath(__file__))
_SCRIPT = os.path.join(os.path.dirname(_HERE), "analyze_solver_module_graph.py")
_spec = importlib.util.spec_from_file_location("solver_module_graph", _SCRIPT)
assert _spec and _spec.loader
mg = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(mg)


def write_crate(root: str, files: dict[str, str]) -> str:
    src = os.path.join(root, "src")
    for name, body in files.items():
        path = os.path.join(src, name)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as handle:
            handle.write(body)
    return src


class CommentsAreNotDependencies(unittest.TestCase):
    def test_doc_link_does_not_create_an_edge(self) -> None:
        with tempfile.TemporaryDirectory() as root:
            src = write_crate(
                root,
                {
                    "lib.rs": "mod alpha;\nmod beta;\n",
                    # The ONLY mention of beta is an intra-doc link and a string.
                    "alpha.rs": (
                        "//! See [`crate::beta::thing`] for the other half.\n"
                        "/* crate::beta::thing */\n"
                        'const NOTE: &str = "crate::beta::thing";\n'
                        "pub fn thing() {}\n"
                    ),
                    "beta.rs": "pub fn thing() {}\n",
                },
            )
            graph = mg.build_graph(src)
            self.assertNotIn("beta", graph["edges"].get("alpha", {}))

    def test_real_call_does_create_an_edge(self) -> None:
        with tempfile.TemporaryDirectory() as root:
            src = write_crate(
                root,
                {
                    "lib.rs": "mod alpha;\nmod beta;\n",
                    "alpha.rs": "pub fn go() { crate::beta::thing(); }\n",
                    "beta.rs": "pub fn thing() {}\n",
                },
            )
            graph = mg.build_graph(src)
            self.assertEqual(graph["edges"]["alpha"]["beta"], 1)


class TestCodeIsNotADependency(unittest.TestCase):
    def test_inline_cfg_test_module_is_ignored(self) -> None:
        with tempfile.TemporaryDirectory() as root:
            src = write_crate(
                root,
                {
                    "lib.rs": "mod alpha;\nmod beta;\n",
                    "alpha.rs": (
                        "pub fn go() {}\n"
                        "#[cfg(test)]\n"
                        "mod tests {\n"
                        "    #[test]\n"
                        "    fn t() { crate::beta::thing(); }\n"
                        "}\n"
                    ),
                    "beta.rs": "pub fn thing() {}\n",
                },
            )
            graph = mg.build_graph(src)
            self.assertNotIn("beta", graph["edges"].get("alpha", {}))

    def test_cfg_test_mod_file_is_skipped_entirely(self) -> None:
        """`#[cfg(test)] mod tests;` puts the dependency in another FILE.

        `dl_online/tests.rs` is the real instance: its only reference to
        `evidence` lives there, and counting it made `dl_online` look like a
        cycle member.
        """
        with tempfile.TemporaryDirectory() as root:
            src = write_crate(
                root,
                {
                    "lib.rs": "mod alpha;\nmod beta;\n",
                    "alpha.rs": "pub fn go() {}\n#[cfg(test)]\nmod tests;\n",
                    "alpha/tests.rs": "fn t() { crate::beta::thing(); }\n",
                    "beta.rs": "pub fn thing() {}\n",
                },
            )
            graph = mg.build_graph(src)
            self.assertEqual(graph["test_files_skipped"], 1)
            self.assertNotIn("beta", graph["edges"].get("alpha", {}))


class FacadeReExportsAreDependencies(unittest.TestCase):
    """The measurement that changed the answer.

    `array_bv_abs.rs` says `use crate::{Evidence, SolverConfig};`. No
    `crate::evidence` path appears anywhere in the file, yet it depends on
    `evidence`. Resolving the crate-root re-export is the only way to see it.
    """

    CRATE = {
        "lib.rs": (
            "mod alpha;\nmod evidence;\n"
            "pub use evidence::{Evidence, produce};\n"
        ),
        "alpha.rs": "use crate::{Evidence};\npub fn go(_e: Evidence) {}\n",
        "evidence.rs": "pub struct Evidence;\npub fn produce() {}\n",
    }

    def test_brace_import_of_a_reexported_item_resolves(self) -> None:
        with tempfile.TemporaryDirectory() as root:
            src = write_crate(root, self.CRATE)
            graph = mg.build_graph(src)
            self.assertGreaterEqual(graph["facade_items"], 2)
            self.assertIn("evidence", graph["edges"].get("alpha", {}))

    def test_bare_reexported_call_resolves(self) -> None:
        with tempfile.TemporaryDirectory() as root:
            crate = dict(self.CRATE)
            crate["alpha.rs"] = "pub fn go() { crate::produce(); }\n"
            src = write_crate(root, crate)
            graph = mg.build_graph(src)
            self.assertIn("evidence", graph["edges"].get("alpha", {}))

    def test_hiding_the_facade_hides_the_cycle(self) -> None:
        """Without facade resolution this crate looks acyclic. It is not."""
        with tempfile.TemporaryDirectory() as root:
            crate = dict(self.CRATE)
            crate["evidence.rs"] = (
                "pub struct Evidence;\n"
                "pub fn produce() { crate::alpha::go(Evidence); }\n"
            )
            src = write_crate(root, crate)
            graph = mg.build_graph(src)
            cycles = [c for c in mg.strongly_connected(graph) if len(c) > 1]
            self.assertEqual(cycles, [["alpha", "evidence"]])


class RatchetActuallyFails(unittest.TestCase):
    """A gate that cannot fail is not a gate (finding 8, refactor README)."""

    def _summary(self, crate: dict, layer: list[str]) -> dict:
        with tempfile.TemporaryDirectory() as root:
            src = write_crate(root, crate)
            return mg.summarize(mg.build_graph(src), layer)

    ACYCLIC = {
        "lib.rs": "mod alpha;\nmod beta;\nmod gamma;\n",
        "alpha.rs": "pub fn go() { crate::beta::thing(); }\n",
        "beta.rs": "pub fn thing() {}\n",
        "gamma.rs": "pub fn other() {}\n",
    }

    def _baseline(self, summary: dict) -> dict:
        return {
            "coverage_floor": {
                "modules": summary["modules"],
                "files_scanned": summary["files_scanned"],
                "facade_items": summary["facade_items"],
                "edge_count": summary["edge_count"],
            },
            "modules_in_cycles": summary["modules_in_cycles"],
            "evidence_layer": summary["evidence_layer"],
            "edges_into_evidence_layer": summary["edges_into_evidence_layer"],
            "edges_from_largest_cycle_into_evidence_layer": summary[
                "edges_from_largest_cycle_into_evidence_layer"
            ],
        }

    def test_unchanged_crate_passes(self) -> None:
        summary = self._summary(self.ACYCLIC, ["gamma"])
        self.assertEqual(mg.check(summary, self._baseline(summary)), 0)

    def test_a_new_cycle_fails(self) -> None:
        base = self._baseline(self._summary(self.ACYCLIC, ["gamma"]))
        broken = dict(self.ACYCLIC)
        broken["beta.rs"] = "pub fn thing() { crate::alpha::go(); }\n"
        self.assertEqual(mg.check(self._summary(broken, ["gamma"]), base), 1)

    def test_a_new_back_edge_into_the_layer_fails(self) -> None:
        base = self._baseline(self._summary(self.ACYCLIC, ["gamma"]))
        broken = dict(self.ACYCLIC)
        broken["beta.rs"] = "pub fn thing() { crate::gamma::other(); }\n"
        summary = self._summary(broken, ["gamma"])
        self.assertIn("beta -> gamma", summary["edges_into_evidence_layer"])
        self.assertEqual(mg.check(summary, base), 1)

    def test_losing_coverage_fails(self) -> None:
        """The inert-gate trap: measure almost nothing, exit 0.

        A one-module shrink is legitimate refactoring and must NOT fail (the
        tolerance below). Losing most of the crate is the tool having been
        pointed somewhere else, and must.
        """
        wide = {"lib.rs": "".join(f"mod m{i};\n" for i in range(20))}
        for i in range(20):
            wide[f"m{i}.rs"] = "pub fn go() { crate::m0::go2(); }\n" if i else "pub fn go2() {}\n"
        base = self._baseline(self._summary(wide, ["m19"]))
        self.assertEqual(base["coverage_floor"]["modules"], 20)

        one_gone = {k: v for k, v in wide.items() if k != "m18.rs"}
        one_gone["lib.rs"] = "".join(f"mod m{i};\n" for i in range(20) if i != 18)
        self.assertEqual(mg.check(self._summary(one_gone, ["m19"]), base), 0)

        collapsed = {"lib.rs": "mod m0;\n", "m0.rs": "pub fn go2() {}\n"}
        self.assertEqual(mg.check(self._summary(collapsed, ["m19"]), base), 1)

    def test_an_improvement_passes_and_is_reported(self) -> None:
        cyclic = dict(self.ACYCLIC)
        cyclic["beta.rs"] = "pub fn thing() { crate::alpha::go(); }\n"
        base = self._baseline(self._summary(cyclic, ["gamma"]))
        self.assertEqual(len(base["modules_in_cycles"]), 2)
        fixed = self._summary(self.ACYCLIC, ["gamma"])
        self.assertEqual(mg.check(fixed, base), 0)


class RealCrateInvariants(unittest.TestCase):
    """The claims `03-solver-decomposition.md` now rests on, on the real tree."""

    @classmethod
    def setUpClass(cls) -> None:
        if not os.path.isdir(mg.DEFAULT_SRC):
            raise unittest.SkipTest("axeyum-solver sources not present")
        cls.graph = mg.build_graph(mg.DEFAULT_SRC)
        with open(mg.DEFAULT_BASELINE, encoding="utf-8") as handle:
            cls.baseline = json.load(handle)
        cls.summary = mg.summarize(cls.graph, cls.baseline["evidence_layer"])

    def test_the_scan_saw_the_crate(self) -> None:
        self.assertGreater(self.summary["files_scanned"], 100)
        self.assertGreater(self.summary["facade_items"], 500)
        self.assertGreater(self.summary["edge_count"], 900)

    def test_reconstruct_is_inside_a_cycle(self) -> None:
        """Candidate D1 assumes it is not. It is."""
        self.assertIn("reconstruct", self.summary["modules_in_cycles"])

    def test_ratchet_is_green_on_the_committed_baseline(self) -> None:
        self.assertEqual(mg.check(self.summary, self.baseline), 0)


if __name__ == "__main__":
    unittest.main()
