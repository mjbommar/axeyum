#!/usr/bin/env python3
"""Controls for the workspace-wide consumer scan in
``scripts/creal-migrate-registry.py``.

The scan exists because of a measured incident, not a hypothesis.  The ADR-1512
registry split rewrote ``p.<field>`` -> ``p.<module>.<field>`` over ``creal.rs``,
``creal/**`` and ``crates/axeyum-lean-kernel/examples/**`` and over **nothing
else**, so ``crates/axeyum-py/src/kernel/prelude_fields.rs`` -- a GENERATED file
in another crate that names every ``CRealPrelude`` field -- was left addressing
fields that no longer existed.  Main stopped compiling, and the regeneration
that fixed that silently deleted 69 of ``creal``'s 606 names from the Python
binding.

The shipped script is never re-implemented here.  ``AXEYUM_CREAL_MIGRATE_ROOT``
points it at a throwaway tree whose ``creal.rs`` and dependency artifact are
minimal fixtures, so the scan can be driven to refusal and back without touching
the checkout.  Same device as ``AXEYUM_MERGE_HYGIENE_ROOT``.

``--check-external`` runs the scan and stops, which is what lets every scenario
below go through the real entry point rather than through an imported function::

    python3 -m unittest scripts.tests.test_creal_migrate_registry

Each scenario drives ONE decision, and the two negative controls are the point:
a scan that refused everything would pass the refusal test alone.
"""

from __future__ import annotations

import os
import pathlib
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/creal-migrate-registry.py"

# `creal.rs` needs only enough shape for `fields_of` to order the fields and
# for `rewritten_paths` to resolve. The scan runs long before any parsing of
# `intern_names`, which is what makes this fixture honest rather than lucky.
CREAL_RS = """\
//! fixture
pub struct CRealPrelude {
    pub rat: RatPrelude,
    pub widget_lemma: NameId,
    pub other_lemma: NameId,
}
"""


class ConsumerScanControls(unittest.TestCase):
    """One scenario per decision the scan makes."""

    def setUp(self) -> None:
        scratch = pathlib.Path("/data0/axeyum/scratch")
        self._tmp = tempfile.TemporaryDirectory(dir=scratch if scratch.is_dir() else None)
        self.addCleanup(self._tmp.cleanup)
        self.root = pathlib.Path(self._tmp.name) / "tree"

        creal_dir = self.root / "crates/axeyum-lean-kernel/src/creal"
        creal_dir.mkdir(parents=True)
        (self.root / "crates/axeyum-lean-kernel/src/creal.rs").write_text(CREAL_RS)
        (creal_dir / "widget.rs").write_text("// the module that owns widget_lemma\n")

        artifact = self.root / "artifacts/refactor"
        artifact.mkdir(parents=True)
        (artifact / "creal-declare-deps.json").write_text(
            '{"field_names": ["widget_lemma", "other_lemma"], "steps": ['
            '{"module": "widget", "measured_provides": ["widget_lemma"]}]}'
        )
        # No `git init`: `workspace_rust_files` must fall back to a walk rather
        # than treat an unscannable tree as a clean one. That fallback is under
        # test here by construction -- if it ever failed open, every refusal
        # scenario below would go green while finding nothing.

    # -- tree construction --------------------------------------------------

    def write(self, rel: str, text: str) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def scan(self, *args: str) -> subprocess.CompletedProcess:
        env = dict(os.environ)
        for var in ("GIT_INDEX_FILE", "GIT_DIR", "GIT_WORK_TREE"):
            env.pop(var, None)
        env["AXEYUM_CREAL_MIGRATE_ROOT"] = str(self.root)
        return subprocess.run(
            ["python3", str(SCRIPT), "--check-external", *args],
            cwd=ROOT,
            env=env,
            capture_output=True,
            text=True,
            timeout=120,
        )

    # -- the accept case ----------------------------------------------------

    def test_a_tree_with_no_external_consumer_passes(self) -> None:
        """The positive control. Without it the refusal test below is satisfied
        by a scan that refuses unconditionally, which is not a scan."""
        done = self.scan("widget")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("external consumers: none", done.stdout)

    # -- the refusal --------------------------------------------------------

    def test_an_external_consumer_refuses_and_names_the_site(self) -> None:
        """`crates/axeyum-solver` is outside the kernel crate, so nothing will
        rewrite it. The exit status must depend on the finding, and the output
        must name file AND field -- a refusal that does not say where is a
        refusal nobody can act on."""
        self.write("crates/axeyum-solver/src/uses_it.rs", "fn f(p: &X) { let _ = p.widget_lemma; }\n")
        done = self.scan("widget")
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("EXTERNAL CONSUMERS", done.stderr)
        self.assertIn("crates/axeyum-solver/src/uses_it.rs", done.stderr)
        self.assertIn("widget_lemma:1", done.stderr)
        self.assertIn("Refusing", done.stderr)

    def test_allow_external_reports_the_same_sites_and_proceeds(self) -> None:
        """The override is deliberate and visible: the sites are still printed,
        the exit is 0. An override that silenced the finding would be a way to
        make the scan stop mattering."""
        self.write("crates/axeyum-solver/src/uses_it.rs", "fn f(p: &X) { let _ = p.widget_lemma; }\n")
        done = self.scan("--allow-external", "widget")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("crates/axeyum-solver/src/uses_it.rs", done.stderr)
        self.assertIn("migrating anyway", done.stderr)

    # -- the two negative controls ------------------------------------------

    def test_a_consumer_the_rewriter_will_fix_is_not_external(self) -> None:
        """`creal/**` IS rewritten, so a read there is not a finding. Without
        this control the scan could be `any file that mentions the field` --
        which would refuse every migration and teach everyone to pass
        --allow-external."""
        self.write(
            "crates/axeyum-lean-kernel/src/creal/neighbour.rs",
            "fn f(p: &X) { let _ = p.widget_lemma; }\n",
        )
        done = self.scan("widget")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("external consumers: none", done.stdout)

    def test_a_different_modules_field_is_not_this_modules_finding(self) -> None:
        """The scan is per-module: `other_lemma` belongs to no migrated module
        here, so an external read of it must not block `widget`. A scan keyed on
        the whole struct instead of the moving fields would fail this."""
        self.write("crates/axeyum-solver/src/uses_it.rs", "fn f(p: &X) { let _ = p.other_lemma; }\n")
        done = self.scan("widget")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("external consumers: none", done.stdout)

    # -- what the report has to say -----------------------------------------

    def test_a_generated_consumer_is_labelled_generated(self) -> None:
        """The remedy differs: a generated consumer is fixed by rerunning its
        generator, a hand-written one by editing it. Getting that backwards is
        what turned one broken build into an amputated Python surface."""
        self.write(
            "crates/axeyum-py/src/kernel/table.rs",
            "//! GENERATED, do not edit.\nfn f(p: &X) { let _ = p.widget_lemma; }\n",
        )
        done = self.scan("widget")
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        # The LABEL ON THIS SITE'S LINE, not the substring anywhere in stderr:
        # the standing remedy prose says "[GENERATED]" too, so the loose
        # assertion passed with the label hard-coded to "hand-written" (mutant
        # C6 survived on it). A test that cannot fail is worse than no test.
        self.assertIn("table.rs [GENERATED]: widget_lemma:1", done.stderr)

    def test_a_hand_written_consumer_is_labelled_hand_written(self) -> None:
        self.write("crates/axeyum-solver/src/uses_it.rs", "fn f(p: &X) { let _ = p.widget_lemma; }\n")
        done = self.scan("widget")
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("uses_it.rs [hand-written]: widget_lemma:1", done.stderr)

    def test_a_field_named_only_in_a_comment_is_not_a_finding(self) -> None:
        """Accessor hits are read from comment-stripped text: `creal.rs` alone
        carries ~4,900 comment lines full of `p.foo` in prose, and a scan that
        counts those refuses on documentation."""
        self.write(
            "crates/axeyum-solver/src/uses_it.rs",
            "// see p.widget_lemma for the bound\nfn f() {}\n",
        )
        done = self.scan("widget")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)

    def test_a_rustdoc_link_IS_a_finding(self) -> None:
        """...but `CRealPrelude::<field>` in a doc comment is read from the RAW
        text, because a broken intra-doc link is a `-D warnings` failure and it
        lives in exactly the comments the accessor pattern blanks out. The two
        patterns disagree on purpose."""
        self.write(
            "crates/axeyum-solver/src/uses_it.rs",
            "/// see [`CRealPrelude::widget_lemma`]\nfn f() {}\n",
        )
        done = self.scan("widget")
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("widget_lemma:1", done.stderr)


if __name__ == "__main__":
    unittest.main()
