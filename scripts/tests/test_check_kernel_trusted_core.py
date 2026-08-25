"""Controls for `check-kernel-trusted-core.py`.

The gate passes on the committed tree with 0 failures, which on its own is
indistinguishable from a checker that finds nothing because it looks for
nothing — this repository measured 40 of 162 checker runs exiting 0 on
completion alone. So every one of the five guards is driven to failure here,
and the two that depend on the *scanner* rather than on a comparison (A and D)
are driven against a real mutated copy of the kernel source, not a fabricated
report. A guard that only fails for a hand-built object proves the `if`
statement works, not that the derivation does.

Deleting any single guard from the gate must kill exactly one test here.
"""

from __future__ import annotations

import functools
import importlib.util
import pathlib
import shutil
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_kernel_trusted_core", ROOT / "scripts" / "check-kernel-trusted-core.py"
)
assert SPEC and SPEC.loader
KT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(KT)


@functools.cache
def committed() -> "KT.Report":
    """The committed tree, parsed once. Six tests read it.

    Measured 2026-08-25 (crate at 3,541 functions / 224k lines,
    `crates/axeyum-lean-kernel/src`): parsing took ~495 s before the loose-rule
    fix below (99.5% of that in `re.Pattern.search`, 324,510 calls from
    `Crate._resolve`'s `.method(` receiver-unknown case, which re-scanned the
    WHOLE enclosing file for every same-named candidate at every call site —
    O(call sites * candidates * file size), and dominates once common method
    names like `new`/`get` have hundreds of candidates across the crate).
    `_resolve` now looks up a per-file, precomputed set of which owner-type
    names occur in that file (one combined-alternation regex scan per file,
    not per candidate) instead of re-searching; the `\\b...\\b` match semantics
    are unchanged, so the trusted-line count is identical, just derived in
    ~1.5 s instead of ~495 s. "~2 s" here was stale well before that — it was
    never re-measured as the crate grew from 794 to 3,541 functions."""
    return KT.Report(KT.Crate(KT.SRC))


def mutated_tree(edits: dict[str, tuple[str, str]]) -> pathlib.Path:
    """A throwaway copy of the kernel source with `{file: (find, replace)}` applied."""
    target = pathlib.Path(tempfile.mkdtemp()) / "src"
    shutil.copytree(KT.SRC, target)
    for name, (find, replace) in edits.items():
        path = target / name
        text = path.read_text(encoding="utf-8")
        assert find in text, f"control is stale: {find!r} not in {name}"
        path.write_text(text.replace(find, replace, 1), encoding="utf-8")
    return target


class Fake:
    """A `Report` shaped just enough for `evaluate`, for the comparison guards."""

    def __init__(self, **kw) -> None:
        self.crate = type("C", (), {"fns": [0] * 800, "production": [0] * 44})()
        self.gate_names = set(KT.ADMISSION_GATES)
        self.trusted = set(range(300))
        self.trusted_lines = 5129
        self.trusted_files = set(KT.TRUSTED_FILES)
        for key, value in kw.items():
            setattr(self, key, value)


class GuardAANewInsertionSiteIsAGate(unittest.TestCase):
    """A new way for a declaration to exist must not pass unnoticed.

    Driven through the real scanner: a helper that calls `insert_unchecked` is
    added to `env.rs` and must be reported as an unargued admission gate.
    """

    def test_a_new_insert_unchecked_caller_fails(self) -> None:
        tree = mutated_tree(
            {
                "env.rs": (
                    "    pub(crate) fn insert_unchecked(",
                    "    pub(crate) fn smuggle(&mut self, decl: Declaration) {\n"
                    "        self.insert_unchecked(decl);\n"
                    "    }\n\n"
                    "    pub(crate) fn insert_unchecked(",
                )
            }
        )
        report = KT.Report(KT.Crate(tree))
        failures = KT.evaluate(report, [])
        self.assertTrue(
            any(f.startswith("A:") and "smuggle" in f for f in failures),
            f"the new insertion site was not reported: {failures}",
        )

    def test_an_insert_unchecked_call_inside_cfg_test_is_not_a_gate(self) -> None:
        """The discrimination that makes guard A worth anything.

        `quotient.rs`, `lean_export.rs` and `lean_pp.rs` carry inline
        `#[cfg(test)] mod tests`, and those tests call `insert_unchecked`
        directly six times. A scanner that counted them would report ten
        admission gates on the committed tree and the pin would be noise.
        """
        tree = mutated_tree(
            {
                "env.rs": (
                    "    pub(crate) fn insert_unchecked(",
                    "    pub(crate) fn insert_unchecked(",
                )
            }
        )
        (tree / "env.rs").write_text(
            (tree / "env.rs").read_text(encoding="utf-8")
            + "\n#[cfg(test)]\nmod smuggle_tests {\n"
            "    fn t() { let mut e = 0; e.insert_unchecked(1); }\n}\n",
            encoding="utf-8",
        )
        report = KT.Report(KT.Crate(tree))
        self.assertEqual(report.gate_names, KT.ADMISSION_GATES)
        self.assertEqual([f for f in KT.evaluate(report, []) if f.startswith("A:")], [])

    def test_a_removed_gate_also_fails(self) -> None:
        report = Fake(gate_names={("tc.rs", "add_declaration")})
        self.assertTrue(any(f.startswith("A:") for f in KT.evaluate(report, [])))


class GuardBTheEnvironmentBoundaryIsClosed(unittest.TestCase):
    """The closure is exhaustive only because nothing outside the crate can
    insert. That is a visibility fact, so it is read from the source."""

    def test_a_public_insert_unchecked_fails(self) -> None:
        tree = mutated_tree(
            {"env.rs": ("pub(crate) fn insert_unchecked(", "pub fn insert_unchecked(")}
        )
        leaks = KT.environment_mutators_are_private(tree)
        self.assertTrue(
            any("insert_unchecked" in leak for leak in leaks), f"not caught: {leaks}"
        )
        self.assertTrue(
            any(f.startswith("B:") for f in KT.evaluate(Fake(), leaks)),
            "a leak was found but did not fail the gate",
        )

    def test_the_committed_environment_has_no_public_mutator(self) -> None:
        self.assertEqual(KT.environment_mutators_are_private(KT.SRC), [])

    def test_a_public_read_only_method_is_not_a_leak(self) -> None:
        """`Environment::get`/`contains`/`iter` are `pub` and must stay legal;
        a guard that fired on them would be deleted within a day."""
        leaks = KT.environment_mutators_are_private(KT.SRC)
        self.assertNotIn("Environment::get", " ".join(leaks))


class GuardCTheCeilingCatchesGrowth(unittest.TestCase):
    def test_growth_past_the_ceiling_fails(self) -> None:
        report = Fake(trusted_lines=KT.TRUSTED_LINES_MAX + 1)
        self.assertTrue(any(f.startswith("C:") for f in KT.evaluate(report, [])))

    def test_the_ceiling_has_headroom_but_not_unlimited_headroom(self) -> None:
        """A ceiling far above the measurement cannot fail, which is the same
        thing as not existing."""
        measured = committed().trusted_lines
        self.assertLess(KT.TRUSTED_LINES_MAX, measured * 1.5)
        self.assertGreaterEqual(KT.TRUSTED_LINES_MAX, measured)


class GuardDAFileJoiningTheTrustedCoreIsVisible(unittest.TestCase):
    """The structural guard, and the one that found `lean_export.rs`.

    Driven through the real call-graph closure: one call is added to
    `add_declaration`, and the file that owns the callee must appear.
    """

    def test_calling_the_pretty_printer_from_an_admission_gate_fails(self) -> None:
        tree = mutated_tree(
            {
                "tc.rs": (
                    "        self.check_declaration(&decl)?;",
                    "        let _ = self.axiom_footprint(name);\n"
                    "        self.check_declaration(&decl)?;",
                )
            }
        )
        report = KT.Report(KT.Crate(tree))
        self.assertIn("lean_pp.rs", report.trusted_files)
        failures = KT.evaluate(report, [])
        self.assertTrue(
            any(f.startswith("D:") and "lean_pp.rs" in f for f in failures),
            f"an untrusted file joined the core without failing the gate: {failures}",
        )

    def test_the_committed_tree_does_not_trust_the_pretty_printer(self) -> None:
        self.assertNotIn("lean_pp.rs", committed().trusted_files)

    def test_a_file_leaving_the_core_also_fails(self) -> None:
        report = Fake(trusted_files=KT.TRUSTED_FILES - {"quotient.rs"})
        self.assertTrue(any(f.startswith("D:") for f in KT.evaluate(report, [])))


class GuardEAZeroIsNotAResult(unittest.TestCase):
    def test_an_empty_tree_trips_every_floor(self) -> None:
        empty = pathlib.Path(tempfile.mkdtemp()) / "src"
        empty.mkdir(parents=True)
        report = KT.Report(KT.Crate(empty))
        self.assertEqual(report.trusted_lines, 0)
        failures = KT.evaluate(report, [])
        self.assertTrue(
            sum(1 for f in failures if f.startswith("E:")) >= 4,
            f"a blind scanner passed the floors: {failures}",
        )

    def test_each_floor_fails_on_its_own(self) -> None:
        for kw in (
            {"crate": type("C", (), {"fns": [], "production": [0] * 44})()},
            {"trusted": set()},
            {"trusted_lines": 0},
        ):
            with self.subTest(kw=list(kw)):
                self.assertTrue(
                    any(f.startswith("E:") for f in KT.evaluate(Fake(**kw), []))
                )


class TheScannerReadsRustNotText(unittest.TestCase):
    """Two ways a naive scanner lies, both pinned."""

    def test_a_function_inside_a_string_literal_is_not_a_function(self) -> None:
        code = KT.blank_noncode('let s = "fn ghost(x: u8) { 1 }";\nfn real() { 2 }\n')
        self.assertEqual([f[0] for f in KT.function_spans(code)], ["real"])

    def test_a_lifetime_is_not_a_char_literal(self) -> None:
        """`'a` opens no literal. A scanner that thinks it does swallows the
        rest of the file to the next apostrophe and reports fewer functions."""
        code = KT.blank_noncode("impl<'a> T<'a> { fn f(&'a self) -> u8 { 1 } }\n")
        self.assertEqual([f[0] for f in KT.function_spans(code)], ["f"])

    def test_offsets_survive_blanking(self) -> None:
        text = "// comment\nfn f() { 1 }\n"
        self.assertEqual(len(KT.blank_noncode(text)), len(text))


class TheCommittedTreeIsMeasuredNotAssumed(unittest.TestCase):
    def test_the_gate_passes_and_measured_something(self) -> None:
        report = committed()
        self.assertEqual(KT.evaluate(report, KT.environment_mutators_are_private(KT.SRC)), [])
        self.assertGreaterEqual(len(report.gates), 4)
        self.assertGreater(report.trusted_lines, KT.MIN_TRUSTED_LINES)
        self.assertGreater(report.total_fn_lines, report.trusted_lines * 3)

    def test_the_preludes_are_content_not_checker(self) -> None:
        """16k lines of `nat_prelude/` must be outside the trusted core; if a
        prelude ever lands inside it, the headline number is wrong by 3x."""
        trusted = committed().trusted_files
        for content in ("nat_prelude.rs", "int_prelude.rs", "prelude.rs", "arith_model.rs"):
            self.assertNotIn(content, trusted)


if __name__ == "__main__":
    unittest.main()
