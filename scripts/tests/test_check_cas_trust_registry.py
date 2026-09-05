"""Controls for `scripts/check-cas-trust-registry.py` (math-department file
13, Next Ten item 10, first half).

One test per guard, each written so every OTHER field of its fixture is
valid -- otherwise a mutation would kill several tests at once and the kill
set would not tell you which guard the test actually measures. This mirrors
`scripts/tests/test_check_cas_internal_residue.py`'s own discipline.

Registered in `scripts/tests/mutation_controls.py` under
`cas-trust-registry`, so each guard is deleted and the harness checks that
exactly one test dies.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
GATE = REPO_ROOT / "scripts" / "check-cas-trust-registry.py"


def _load_gate():
    spec = importlib.util.spec_from_file_location("check_cas_trust_registry", GATE)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    # Python 3.14's dataclasses resolve `cls.__module__` through
    # `sys.modules`, so a module built with `module_from_spec` but never
    # registered there raises `AttributeError` the first time a `@dataclass`
    # in it is defined. Register before `exec_module`, as
    # `test_check_cas_substance.py` and friends already must for the same
    # reason on this interpreter.
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def write_file(directory: Path, rel_path: str, content: str) -> Path:
    path = directory / rel_path
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content)
    return path


class ScannerFixtureTests(unittest.TestCase):
    """The brace-aware scanner itself, isolated from the ratchet logic."""

    def setUp(self):
        self.gate = _load_gate()

    def test_cfg_test_module_pub_fn_is_not_counted(self):
        """The exact fixture the task calls out: a `#[cfg(test)]` module
        with a `pub fn` inside it must never be enumerated, even though the
        function is textually `pub fn` and would match a naive regex."""
        src_root = Path(tempfile.mkdtemp())
        write_file(
            src_root,
            "widget.rs",
            """
            /// A real, public function -- must be counted.
            pub fn area(w: i64, h: i64) -> i64 {
                w * h
            }

            #[cfg(test)]
            mod tests {
                use super::*;

                /// Looks exactly like real public API. Must NOT be counted:
                /// it lives inside a #[cfg(test)] module.
                pub fn area_test_helper(w: i64, h: i64) -> i64 {
                    area(w, h) * 2
                }

                #[test]
                fn area_is_positive() {
                    assert!(area_test_helper(2, 3) > 0);
                }
            }
            """,
        )
        _all_types, fns = self.gate.scan_crate(src_root)
        names = {fn.path.rsplit("::", 1)[-1] for fn in fns}
        self.assertIn("area", names)
        self.assertNotIn("area_test_helper", names)
        self.assertEqual(len(fns), 1)

    def test_mod_named_tests_is_excluded_even_without_cfg_test(self):
        """The spec's second exclusion clause: `mod tests` by NAME, not just
        by the `#[cfg(test)]` attribute -- a defensive second trigger."""
        src_root = Path(tempfile.mkdtemp())
        write_file(
            src_root,
            "widget.rs",
            """
            mod tests {
                pub fn should_not_count() -> i64 {
                    1
                }
            }
            """,
        )
        _all_types, fns = self.gate.scan_crate(src_root)
        self.assertEqual(fns, [])

    def test_array_length_semicolon_in_return_type_does_not_truncate_header(self):
        """Regression: `Option<[T; 2]>` contains a `;` that is NOT a
        statement terminator. Before the bracket-depth guard, this silently
        dropped the next function's header -- found on
        `geometry_certify::same_point` in the real crate (an
        `Option<[MvPoly; 2]>` return), which vanished from the scan
        entirely rather than being misclassified."""
        src_root = Path(tempfile.mkdtemp())
        write_file(
            src_root,
            "widget.rs",
            """
            pub fn before() -> i64 {
                1
            }

            pub fn same_point(a: i64, b: i64) -> Option<[i64; 2]> {
                Some([a, b])
            }

            pub fn after() -> i64 {
                2
            }
            """,
        )
        _all_types, fns = self.gate.scan_crate(src_root)
        names = {fn.path.rsplit("::", 1)[-1] for fn in fns}
        self.assertEqual(names, {"before", "same_point", "after"})

    def test_pub_crate_and_pub_super_are_excluded(self):
        src_root = Path(tempfile.mkdtemp())
        write_file(
            src_root,
            "widget.rs",
            """
            pub fn fully_public() -> i64 {
                1
            }

            pub(crate) fn crate_only() -> i64 {
                2
            }

            mod inner {
                pub(super) fn super_only() -> i64 {
                    3
                }
            }
            """,
        )
        _all_types, fns = self.gate.scan_crate(src_root)
        names = {fn.path.rsplit("::", 1)[-1] for fn in fns}
        self.assertEqual(names, {"fully_public"})

    def test_inherent_impl_of_pub_type_is_counted(self):
        src_root = Path(tempfile.mkdtemp())
        write_file(
            src_root,
            "widget.rs",
            """
            pub struct Box2 {
                w: i64,
            }

            impl Box2 {
                pub fn area(&self) -> i64 {
                    self.w * self.w
                }
            }
            """,
        )
        _all_types, fns = self.gate.scan_crate(src_root)
        self.assertEqual([fn.path for fn in fns], ["widget::Box2::area"])

    def test_impl_of_non_pub_type_is_excluded(self):
        src_root = Path(tempfile.mkdtemp())
        write_file(
            src_root,
            "widget.rs",
            """
            struct Hidden {
                w: i64,
            }

            impl Hidden {
                pub fn area(&self) -> i64 {
                    self.w * self.w
                }
            }
            """,
        )
        _all_types, fns = self.gate.scan_crate(src_root)
        self.assertEqual(fns, [])

    def test_trait_impl_body_is_excluded(self):
        src_root = Path(tempfile.mkdtemp())
        write_file(
            src_root,
            "widget.rs",
            """
            pub struct Box2 {
                w: i64,
            }

            pub trait Area {
                fn area(&self) -> i64;
            }

            impl Area for Box2 {
                fn area(&self) -> i64 {
                    self.w * self.w
                }
            }
            """,
        )
        _all_types, fns = self.gate.scan_crate(src_root)
        self.assertEqual(fns, [])


class VocabularyTests(unittest.TestCase):
    def setUp(self):
        self.gate = _load_gate()

    def test_vocabulary_derived_from_suffixes_and_exact_names(self):
        src_root = Path(tempfile.mkdtemp())
        write_file(
            src_root,
            "widget.rs",
            """
            pub struct FooCertificate {
                x: i64,
            }

            pub struct FooEvidence {
                x: i64,
            }

            pub enum ZeroTest {
                Zero,
                Nonzero,
            }

            pub struct NotVocabulary {
                x: i64,
            }
            """,
        )
        all_types, all_fns = self.gate.scan_crate(src_root)
        vocab = self.gate.derive_vocabulary(all_types, all_fns)
        self.assertEqual(set(vocab), {"FooCertificate", "FooEvidence", "ZeroTest"})

    def test_return_type_wrapped_in_option_result_vec_is_certified(self):
        src_root = Path(tempfile.mkdtemp())
        write_file(
            src_root,
            "widget.rs",
            """
            pub struct FooCertificate {
                x: i64,
            }

            pub fn make_opt() -> Option<FooCertificate> {
                None
            }

            pub fn make_res() -> Result<FooCertificate, String> {
                unimplemented!()
            }

            pub fn make_vec() -> Vec<FooCertificate> {
                Vec::new()
            }

            pub fn make_plain() -> i64 {
                1
            }
            """,
        )
        all_types, all_fns = self.gate.scan_crate(src_root)
        vocab_names = set(self.gate.derive_vocabulary(all_types, all_fns))
        by_name = {fn.path.rsplit("::", 1)[-1]: fn for fn in all_fns}
        self.assertEqual(
            self.gate.classify_fn(by_name["make_opt"], vocab_names), "certified"
        )
        self.assertEqual(
            self.gate.classify_fn(by_name["make_res"], vocab_names), "certified"
        )
        self.assertEqual(
            self.gate.classify_fn(by_name["make_vec"], vocab_names), "certified"
        )
        self.assertEqual(
            self.gate.classify_fn(by_name["make_plain"], vocab_names), "uncertified"
        )

    def test_checker_prefix_without_vocab_return_is_checker(self):
        src_root = Path(tempfile.mkdtemp())
        write_file(
            src_root,
            "widget.rs",
            """
            pub fn verify_something(x: i64) -> bool {
                x > 0
            }

            pub fn certify_something(x: i64) -> bool {
                x > 0
            }
            """,
        )
        all_types, all_fns = self.gate.scan_crate(src_root)
        vocab_names = set(self.gate.derive_vocabulary(all_types, all_fns))
        for fn in all_fns:
            self.assertEqual(self.gate.classify_fn(fn, vocab_names), "checker")


class RatchetGateTests(unittest.TestCase):
    """The ratchet's refusal conditions -- run through `main`, mirroring
    `test_check_cas_internal_residue.py`'s structure."""

    def setUp(self):
        self.gate = _load_gate()
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.src_root = self.root / "src"
        self.src_root.mkdir()
        self.ratchet_path = self.root / "registry.ratchet"

    def tearDown(self):
        self.tmp.cleanup()

    def write_crate(self, content: str) -> None:
        write_file(self.src_root, "widget.rs", content)

    def run_gate(self, extra_args=()):
        """Run the gate with stdout/stderr captured into a buffer.

        The gate prints its own `FAIL: ...`/`OK: ...` diagnostics on the
        exact code paths under test here, and those strings look exactly
        like a unittest failure/error header to
        `scripts/tests/mutation_controls.py`'s output scan. Redirecting
        keeps this suite's real pass/fail signal -- the assertions below --
        the only thing that reaches the runner's captured output, exactly as
        `test_check_cas_internal_residue.py`'s own `run_gate` does.
        """
        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer), contextlib.redirect_stderr(buffer):
            status = self.gate.main(
                [
                    "--src-root",
                    str(self.src_root),
                    "--ratchet",
                    str(self.ratchet_path),
                    *extra_args,
                ]
            )
        return status

    CERTIFIED_CRATE = """
        pub struct FooCertificate {
            x: i64,
        }

        pub fn make() -> Option<FooCertificate> {
            None
        }
        """

    # -- baseline behaviour, no mutation tied to these -----------------------

    def test_missing_src_root_is_a_usage_error(self):
        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer), contextlib.redirect_stderr(buffer):
            rc = self.gate.main(
                [
                    "--src-root",
                    str(self.root / "does-not-exist"),
                    "--ratchet",
                    str(self.ratchet_path),
                ]
            )
        self.assertEqual(rc, 2)

    def test_write_then_check_round_trips_clean(self):
        self.write_crate(self.CERTIFIED_CRATE)
        self.assertEqual(self.run_gate(["--write"]), 0)
        self.assertEqual(self.run_gate(), 0)

    def test_a_new_uncertified_function_needs_no_ratchet_edit(self):
        self.write_crate(self.CERTIFIED_CRATE)
        self.assertEqual(self.run_gate(["--write"]), 0)
        self.write_crate(
            self.CERTIFIED_CRATE
            + """
            pub fn brand_new_uncertified() -> i64 {
                1
            }
            """
        )
        self.assertEqual(self.run_gate(), 0)

    def test_read_ratchet_skips_comments_and_blank_lines(self):
        self.ratchet_path.write_text(
            "# a comment\n\nCOUNT\t1\nFN\tfoo::bar\tOption<FooCertificate>\n"
            "VOCAB\tFooCertificate\tstruct\n"
        )
        fns, vocab, count = self.gate.read_ratchet(self.ratchet_path)
        self.assertEqual(fns, {"foo::bar": "Option<FooCertificate>"})
        self.assertEqual(vocab, {"FooCertificate": "struct"})
        self.assertEqual(count, 1)

    def test_read_ratchet_absent_file_is_none(self):
        self.assertIsNone(self.gate.read_ratchet(self.root / "nope.ratchet"))

    # -- guards, each tied to exactly one entry in mutation_controls.py ------

    def test_G1_no_ratchet_file_is_refused(self):
        self.write_crate(self.CERTIFIED_CRATE)
        # Deliberately never call --write: no ratchet file exists.
        self.assertEqual(self.run_gate(), 1)

    def _lower_recorded_floor_to_zero(self) -> None:
        """A named function regressing (G2) or vanishing (G3) always also
        drops the current certified count below whatever floor was recorded
        for it -- the two checks would co-fire on any ordinary fixture, so
        neither test could be attributed to a specific guard's mutation
        (deleting either one alone would leave the other still refusing,
        and the test would not die). Hand-lower the recorded floor to 0
        first, exactly as `test_G4` hand-*raises* it -- this keeps G4
        satisfied (0 is never less than 0) so G2/G3 each fire alone."""
        original = self.ratchet_path.read_text()
        lowered = original.replace("COUNT\t1\n", "COUNT\t0\n")
        self.assertNotEqual(original, lowered, "fixture must contain COUNT\\t1")
        self.ratchet_path.write_text(lowered)

    def test_G2_a_reclassified_certified_function_is_refused(self):
        self.write_crate(self.CERTIFIED_CRATE)
        self.assertEqual(self.run_gate(["--write"]), 0)
        self._lower_recorded_floor_to_zero()
        # `make` still exists, but its return type no longer names the
        # vocabulary -- it regressed from certified to uncertified.
        self.write_crate(
            """
            pub struct FooCertificate {
                x: i64,
            }

            pub fn make() -> i64 {
                0
            }
            """
        )
        self.assertEqual(self.run_gate(), 1)

    def test_G3_a_vanished_certified_function_is_refused(self):
        self.write_crate(self.CERTIFIED_CRATE)
        self.assertEqual(self.run_gate(["--write"]), 0)
        self._lower_recorded_floor_to_zero()
        self.write_crate(
            """
            pub struct FooCertificate {
                x: i64,
            }
            """
        )
        self.assertEqual(self.run_gate(), 1)

    def test_G4_certified_count_below_floor_is_refused(self):
        # The floor is its own `COUNT` row, deliberately decoupled from the
        # `FN` rows (see `read_ratchet`'s docstring) so this guard has an
        # independent code path from G2 (a named function reclassified) and
        # G3 (a named function vanished). Write a clean ratchet, then bump
        # only its COUNT row upward by hand -- every recorded `FN` row still
        # classifies `certified` today (no G2/G3 violation), but the
        # recorded floor now exceeds the real count.
        self.write_crate(self.CERTIFIED_CRATE)
        self.assertEqual(self.run_gate(["--write"]), 0)
        original = self.ratchet_path.read_text()
        bumped = original.replace("COUNT\t1\n", "COUNT\t5\n")
        self.assertNotEqual(original, bumped, "fixture must contain COUNT\\t1")
        self.ratchet_path.write_text(bumped)
        self.assertEqual(self.run_gate(), 1)

    def test_G5_a_vocabulary_type_that_disappeared_is_refused(self):
        # An UNUSED second vocabulary type (`BarCertificate`) is recorded
        # alongside the real, still-valid `FooCertificate` and its still
        # certified `make()` -- so removing only `BarCertificate` isolates
        # this guard: G2 (make still classifies certified), G3 (make still
        # exists) and G4 (the count is unchanged, still >= floor) all stay
        # satisfied, and only the vocabulary-disappearance check fires.
        self.write_crate(
            self.CERTIFIED_CRATE
            + """
            pub struct BarCertificate {
                y: i64,
            }
            """
        )
        self.assertEqual(self.run_gate(["--write"]), 0)
        self.write_crate(self.CERTIFIED_CRATE)
        self.assertEqual(self.run_gate(), 1)

    def test_G6_a_new_certified_function_not_recorded_is_refused(self):
        self.write_crate(self.CERTIFIED_CRATE)
        self.assertEqual(self.run_gate(["--write"]), 0)
        self.write_crate(
            self.CERTIFIED_CRATE
            + """
            pub fn make_two() -> Option<FooCertificate> {
                None
            }
            """
        )
        self.assertEqual(self.run_gate(), 1)


if __name__ == "__main__":
    unittest.main()
