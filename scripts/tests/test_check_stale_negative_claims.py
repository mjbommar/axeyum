"""Controls for `check-stale-negative-claims.py`.

Three incidents on 2026-08-22 (and a fourth found by hand on 2026-08-23, in
`int_prelude/gcd.rs`) shared one shape: a doc comment claiming a symbol was
unproved while a `declare_<that symbol>` sat in the same Rust module, landed
and wired into the build sequence. This suite drives each guard the checker
uses to find that shape -- and to avoid finding it where it is not -- to
failure individually, so a guard that stops doing its job breaks a named test
rather than silently passing.

The real `crates/axeyum-lean-kernel/src` tree is exercised too: it must come
back clean, both because that is the state the audit left it in and because a
checker that always fires is exactly as useless as one that never does.
"""

from __future__ import annotations

import importlib.util
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_stale_negative_claims", ROOT / "scripts" / "check-stale-negative-claims.py"
)
assert SPEC and SPEC.loader
SNC = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SNC)


def write(root: pathlib.Path, rel: str, content: str) -> pathlib.Path:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    return path


class RealTreeIsClean(unittest.TestCase):
    """The actual kernel crate, as the audit left it: zero findings."""

    def test_real_kernel_tree_has_no_findings(self) -> None:
        src = ROOT / "crates" / "axeyum-lean-kernel" / "src"
        findings = SNC.run(src)
        rendered = [f.render() for f in findings]
        self.assertEqual(rendered, [])


class ReintroducedIncidentOne(unittest.TestCase):
    """`creal/product.rs`'s original false claim, reintroduced verbatim in a
    fixture module: a bare-name list directly followed by "are not proved
    here", with every named `declare_*` present in the same module. MUST
    fail.
    """

    def test_flags_reintroduced_claim(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            write(
                root,
                "foo.rs",
                "//! Module doc.\n"
                "\n"
                "/// `mul_assoc`, `left_distrib`, `mul_le_mul_of_nonneg_left` and "
                "`mul_congr`\n"
                "/// are not proved here.\n"
                "fn placeholder() {}\n",
            )
            write(
                root,
                "foo/bar.rs",
                "pub(super) fn declare_mul_assoc() {}\n"
                "pub(super) fn declare_left_distrib() {}\n"
                "pub(super) fn declare_mul_le_mul() {}\n"
                "pub(super) fn declare_mul_congr() {}\n",
            )
            findings = SNC.run(root)
            self.assertEqual(len(findings), 1)
            self.assertIn("mul_assoc", findings[0].bad_names)


class CorrectlyStatedLimitationPasses(unittest.TestCase):
    """A genuine limitation -- a symbol with no matching `declare_` anywhere
    in the module -- must not be flagged. A checker that rejects everything
    is worse than none (CLAUDE.md, this task's own framing).
    """

    def test_true_limitation_not_flagged(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            write(
                root,
                "foo.rs",
                "//! Module doc.\n"
                "\n"
                "/// `neg_add` is not proved here: nothing downstream needs it.\n"
                "fn placeholder() {}\n"
                "\n"
                "pub(super) fn declare_mul_assoc() {}\n",
            )
            findings = SNC.run(root)
            self.assertEqual(findings, [])


class AdjacencyGuard(unittest.TestCase):
    """GUARD: the negation must sit immediately after the name list. Prose
    between the name and the negation (`natAbs`-BASED BOUND, not yet built)
    describes a DIFFERENT noun phrase, not the name itself -- this is a real
    sentence in `int_prelude/dvd.rs` and must not be flagged even though
    `declare_nat_abs` exists in the same module.
    """

    def test_intervening_prose_breaks_the_match(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            write(
                root,
                "foo.rs",
                "//! Module doc.\n"
                "\n"
                "// it would need a `natAbs`-based bound, not yet built, so this\n"
                "// is out of reach for now.\n"
                "\n"
                "pub(super) fn declare_nat_abs() {}\n",
            )
            findings = SNC.run(root)
            self.assertEqual(findings, [])

    def test_claim_regex_requires_adjacency(self) -> None:
        # Direct guard on the compiled pattern itself, independent of file
        # plumbing, so a mutant that loosens `_CLAIM_RE` is caught even if it
        # somehow leaves `run()`'s end-to-end behavior alone.
        text = "it would need a `natAbs`-based bound, not yet built"
        self.assertIsNone(SNC._CLAIM_RE.search(text))
        text2 = "`natAbs` is not built"
        self.assertIsNotNone(SNC._CLAIM_RE.search(text2))


class DottedNamesIgnored(unittest.TestCase):
    """GUARD: `_normalize` never strips a namespace prefix, so a dotted
    reference (`Rat.inv` -> `ratinv`) does not collide with an unrelated
    same-module `declare_<suffix>` (`declare_inv` -> `inv`). This is the
    exact shape of `creal/inverse.rs`'s correct claim about `Rat.inv` sitting
    beside `creal`'s own (unrelated) `declare_inv` for `CReal.inv`. Mutating
    `_normalize` to split on the last `.` and keep only the suffix (the
    "obvious" way to resolve a namespace) reintroduces the collision and
    kills this test.
    """

    def test_dotted_reference_not_flagged(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            write(
                root,
                "foo.rs",
                "//! Module doc.\n"
                "\n"
                "/// The negative branch of `Rat.inv` is not proved here.\n"
                "fn placeholder() {}\n"
                "\n"
                "pub(super) fn declare_inv() {}\n",
            )
            findings = SNC.run(root)
            self.assertEqual(findings, [])


class SelfCorrectingLanguageSuppresses(unittest.TestCase):
    """GUARD: a block that documents its own history and points at the actual
    declaration is not flagged, even when it syntactically matches
    name-list-then-negation -- this is `int_prelude/gcd.rs`'s corrected text
    (see [`declare_mul_neg`] ...) after this session's fix.
    """

    def test_self_correcting_block_not_flagged(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            write(
                root,
                "foo.rs",
                "//! Module doc.\n"
                "\n"
                "// `neg_mul` and `neg_neg` are not declared as public "
                "theorems here.\n"
                "// `Int.mul_neg` is one -- see [`declare_mul_neg`] in "
                "`sub.rs`.\n"
                "\n"
                "pub(super) fn declare_neg_mul() {}\n"
                "pub(super) fn declare_neg_neg() {}\n"
                "pub(super) fn declare_mul_neg() {}\n",
            )
            findings = SNC.run(root)
            self.assertEqual(findings, [])


class ModuleScopingGuard(unittest.TestCase):
    """GUARD: a `declare_` in an UNRELATED module must not satisfy the claim
    -- only `foo.rs` + `foo/*.rs` (Rust's own module boundary) count as one
    scope. This is what distinguishes a genuine cross-module reference from
    the `gcd.rs`/`sub.rs` incident, where both files are `int_prelude`.
    """

    def test_declare_in_sibling_module_does_not_satisfy(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            write(
                root,
                "foo.rs",
                "//! Module doc.\n"
                "\n"
                "/// `mul_assoc` is not proved here.\n"
                "fn placeholder() {}\n",
            )
            write(
                root,
                "quux.rs",
                "pub(super) fn declare_mul_assoc() {}\n",
            )
            findings = SNC.run(root)
            self.assertEqual(findings, [])

    def test_declare_in_same_module_directory_does_satisfy(self) -> None:
        # The `gcd.rs` incident's exact shape: the claim and the `declare_`
        # are in *different files* of the *same* module (`foo.rs` + its
        # `foo/` directory), not the same file.
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            write(
                root,
                "foo.rs",
                "//! Module doc.\n"
                "\n"
                "/// `mul_assoc` is not proved here.\n"
                "fn placeholder() {}\n",
            )
            write(
                root,
                "foo/bar.rs",
                "pub(super) fn declare_mul_assoc() {}\n",
            )
            findings = SNC.run(root)
            self.assertEqual(len(findings), 1)


class NormalizationGuard(unittest.TestCase):
    """GUARD: matching is case/underscore-insensitive, so a camelCase Lean
    name (`modEq_iff_dvd`, this repository's actual naming for the theorem
    incident 3 was about) still resolves against a snake_case `declare_`.
    """

    def test_camel_case_name_matches_snake_case_declare(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            write(
                root,
                "foo.rs",
                "//! Module doc.\n"
                "\n"
                "/// `modEq_iff_dvd` is not built.\n"
                "fn placeholder() {}\n"
                "\n"
                "pub(super) fn declare_modeq_iff_dvd() {}\n",
            )
            findings = SNC.run(root)
            self.assertEqual(len(findings), 1)


class TestFileExclusionGuard(unittest.TestCase):
    """GUARD: a claim inside a file the project itself treats as tests
    (`*_tests.rs`, `tests.rs`) is not scanned."""

    def test_tests_file_is_excluded(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            write(
                root,
                "foo.rs",
                "//! Module doc.\n"
                "\n"
                "pub(super) fn declare_mul_assoc() {}\n",
            )
            write(
                root,
                "foo/foo_tests.rs",
                "/// `mul_assoc` is not proved here.\n"
                "fn placeholder() {}\n",
            )
            findings = SNC.run(root)
            self.assertEqual(findings, [])

    def test_mod_tests_block_is_truncated(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            write(
                root,
                "foo.rs",
                "//! Module doc.\n"
                "\n"
                "pub(super) fn declare_mul_assoc() {}\n"
                "\n"
                "#[cfg(test)]\n"
                "mod tests {\n"
                "    /// `mul_assoc` is not proved here.\n"
                "    fn placeholder() {}\n"
                "}\n",
            )
            findings = SNC.run(root)
            self.assertEqual(findings, [])


class PartialMatchGuard(unittest.TestCase):
    """GUARD: a claim naming several symbols flags on the subset that IS
    contradicted, even when other named symbols in the same list are
    genuinely absent -- a real doc comment can be half right."""

    def test_partial_match_still_flags(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            write(
                root,
                "foo.rs",
                "//! Module doc.\n"
                "\n"
                "/// `mul_assoc` and `truly_absent_lemma` are not proved here.\n"
                "fn placeholder() {}\n"
                "\n"
                "pub(super) fn declare_mul_assoc() {}\n",
            )
            findings = SNC.run(root)
            self.assertEqual(len(findings), 1)
            self.assertEqual(findings[0].bad_names, ["mul_assoc"])


if __name__ == "__main__":
    unittest.main()
