"""Controls for `scripts/check-cas-parity-corpus.py`.

One test per guard, each corrupting exactly ONE thing in an otherwise-valid
scratch fixture (a fake `corpus.json` / `parity_corpus.rs` / `README.md` /
`ground_truth.py` copied into a scratch dir, never the real repository
files) -- otherwise a mutation would kill several tests at once and the
kill set would not tell you which guard the test actually measures. Mirrors
`scripts/tests/test_check_cas_trust_registry.py`'s discipline.

Each test monkeypatches the gate module's path constants to point at the
scratch fixture and calls `main([])` (or `main(["--write"])`) directly, so
this exercises the real CLI entry point end to end rather than only the
pure `run_checks` helper.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
GATE = REPO_ROOT / "scripts" / "check-cas-parity-corpus.py"


def _load_gate():
    spec = importlib.util.spec_from_file_location("check_cas_parity_corpus", GATE)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    # Python 3.14 dataclasses resolve `cls.__module__` through `sys.modules`;
    # register before `exec_module` for the same reason
    # `test_check_cas_trust_registry.py` must (this gate has no dataclasses
    # today, but this keeps the loader identical to its siblings).
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


# A minimal, otherwise-valid two-entry corpus: one `core` main entry and its
# `-ctrl` control, both family "d1". Small enough that every fixture below
# is easy to eyeball, large enough to exercise id/tier parity across two
# entries rather than one.
VALID_ENTRIES = [
    {
        "id": "d1-cubic",
        "area": "differentiate",
        "module": None,
        "tier": "core",
        "description": "d/dx(x^3) = 3x^2",
        "expected": {"kind": "cas_identity", "equal": True, "expr": "3*x^2"},
        "justification": "sympy: sp.diff(x**3, x) == 3*x**2",
    },
    {
        "id": "d1-cubic-ctrl",
        "area": "differentiate",
        "module": None,
        "tier": "core",
        "description": "near-miss control",
        "expected": {"kind": "cas_identity", "equal": False, "expr": "3*x^2+1"},
        "justification": "sympy: sp.diff(x**3, x) != 3*x**2+1",
    },
    {
        "id": "z9-decline",
        "area": "integrate",
        "module": None,
        "tier": "decline_expected",
        "description": "a decline-tier entry with no ground_truth.py claim",
        "expected": {"kind": "decline", "note": "no elementary form"},
        "justification": "cited: Liouville",
    },
]

VALID_HARNESS = """
macro_rules! e {
    ($id:literal, $area:expr, $module:expr, $tier:expr, $f:expr) => {
        Entry { id: $id, area: $area, module: $module, tier: $tier, tracked_by: None, run: $f }
    };
}

fn main() {
    use Tier::{Core, DeclineExpected};
    let entries: Vec<Entry> = vec![
        e!("d1-cubic", Some("differentiate"), None, Core, d1_cubic),
        e!(
            "d1-cubic-ctrl",
            Some("differentiate"),
            None,
            Core,
            d1_cubic_ctrl
        ),
        e!("z9-decline", Some("integrate"), None, DeclineExpected, z9_decline),
    ];
}
"""

VALID_GROUND_TRUTH = '''
def check_differentiate():
    ok(True, "d1 d/dx(x^3) = 3x^2")
    ok(True, "d1-ctrl (hand) the near-miss control is NOT 3x^2+1")
'''


def render_readme(core: int, decline: int, known_defect: int) -> str:
    total = core + decline + known_defect
    return (
        "# Fixture README\n\n"
        "<!-- BEGIN GENERATED: cas-parity-corpus-counts "
        "(scripts/check-cas-parity-corpus.py --write) -->\n"
        f"Tiers: **{core} `core`**, **{decline} `decline_expected`**, "
        f"**{known_defect} `known_defect`**. Total entries: **{total}**.\n"
        "<!-- END GENERATED: cas-parity-corpus-counts -->\n"
)


VALID_README = render_readme(core=2, decline=1, known_defect=0)


def write_fixture(
    tmp: Path,
    entries=None,
    harness_src: str | None = None,
    readme_src: str | None = None,
    ground_truth_src: str | None = None,
) -> None:
    corpus_path = tmp / "corpus.json"
    if entries is None:
        entries = VALID_ENTRIES
    if isinstance(entries, str):
        corpus_path.write_text(entries)  # deliberately raw text (parse-error fixture)
    else:
        corpus_path.write_text(json.dumps(entries, indent=2))

    (tmp / "parity_corpus.rs").write_text(
        VALID_HARNESS if harness_src is None else harness_src
    )
    (tmp / "README.md").write_text(VALID_README if readme_src is None else readme_src)
    (tmp / "ground_truth.py").write_text(
        VALID_GROUND_TRUTH if ground_truth_src is None else ground_truth_src
    )


class RunFixtureMixin:
    def setUp(self):
        self.gate = _load_gate()
        self.tmp = Path(tempfile.mkdtemp())
        self._orig = (
            self.gate.CORPUS_JSON,
            self.gate.HARNESS,
            self.gate.README,
            self.gate.GROUND_TRUTH,
        )
        self.gate.CORPUS_JSON = self.tmp / "corpus.json"
        self.gate.HARNESS = self.tmp / "parity_corpus.rs"
        self.gate.README = self.tmp / "README.md"
        self.gate.GROUND_TRUTH = self.tmp / "ground_truth.py"

    def tearDown(self):
        (
            self.gate.CORPUS_JSON,
            self.gate.HARNESS,
            self.gate.README,
            self.gate.GROUND_TRUTH,
        ) = self._orig

    def run_main(self, argv=()) -> tuple[int, str]:
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            rc = self.gate.main(list(argv))
        return rc, buf.getvalue()


class CleanFixtureTests(RunFixtureMixin, unittest.TestCase):
    """The untouched fixture must pass. Every corruption test below starts
    from exactly this fixture and changes ONE thing."""

    def test_clean_fixture_passes(self):
        write_fixture(self.tmp)
        rc, out = self.run_main([])
        self.assertEqual(rc, 0, out)
        self.assertIn("PASS", out)
        self.assertIn("entries=3", out)
        self.assertIn("core=2", out)
        self.assertIn("decline_expected=1", out)
        self.assertIn("known_defect=0", out)

    def test_write_on_clean_fixture_is_a_no_op(self):
        write_fixture(self.tmp)
        before = (self.tmp / "README.md").read_text()
        rc, out = self.run_main(["--write"])
        after = (self.tmp / "README.md").read_text()
        self.assertEqual(rc, 0, out)
        self.assertEqual(before, after)
        self.assertIn("no_change", out)


class GuardAStaleReadmeCountTests(RunFixtureMixin, unittest.TestCase):
    """Guard (a): the README's generated block must match corpus.json."""

    def test_stale_readme_count_fails(self):
        write_fixture(self.tmp, readme_src=render_readme(core=1, decline=1, known_defect=0))
        rc, out = self.run_main([])
        self.assertEqual(rc, 1, out)
        self.assertIn("guard(a)", out)
        self.assertNotIn("guard(b)", out)
        self.assertNotIn("guard(c)", out)
        self.assertNotIn("guard(d)", out)
        self.assertNotIn("guard(e)", out)

    def test_write_repairs_a_stale_readme_count(self):
        write_fixture(self.tmp, readme_src=render_readme(core=1, decline=1, known_defect=0))
        rc, _out = self.run_main(["--write"])
        self.assertEqual(rc, 0)
        rc2, out2 = self.run_main([])
        self.assertEqual(rc2, 0, out2)
        self.assertIn("PASS", out2)


class GuardBOrphanIdTests(RunFixtureMixin, unittest.TestCase):
    """Guard (b): an id in one ledger with no counterpart in the other,
    both directions."""

    def test_orphan_id_in_json_fails(self):
        # tier `decline_expected`, deliberately, so this fixture trips ONLY
        # guard (b) -- a `core`-tier orphan would also trip guard (e) (no
        # ground_truth.py claim for its family), which would make this
        # control's kill set ambiguous between two guards.
        entries = VALID_ENTRIES + [
            {
                "id": "orphan-in-json",
                "area": None,
                "module": None,
                "tier": "decline_expected",
                "description": "no harness entry",
                "expected": {"kind": "decline", "note": "x"},
                "justification": "hand",
            }
        ]
        write_fixture(
            self.tmp,
            entries=entries,
            readme_src=render_readme(core=2, decline=2, known_defect=0),
        )
        rc, out = self.run_main([])
        self.assertEqual(rc, 1, out)
        self.assertIn("guard(b)", out)
        self.assertIn("orphan-in-json", out)
        self.assertNotIn("guard(e)", out)

    def test_orphan_id_in_harness_fails(self):
        harness = VALID_HARNESS.replace(
            'e!("z9-decline", Some("integrate"), None, DeclineExpected, z9_decline),',
            'e!("z9-decline", Some("integrate"), None, DeclineExpected, z9_decline),\n'
            '        e!("orphan-in-harness", None, None, Core, orphan_fn),',
        )
        write_fixture(self.tmp, harness_src=harness)
        rc, out = self.run_main([])
        self.assertEqual(rc, 1, out)
        self.assertIn("guard(b)", out)
        self.assertIn("orphan-in-harness", out)
        self.assertNotIn("guard(a)", out)
        self.assertNotIn("guard(c)", out)
        self.assertNotIn("guard(d)", out)
        self.assertNotIn("guard(e)", out)


class GuardCTierMismatchTests(RunFixtureMixin, unittest.TestCase):
    """Guard (c): the same id must carry the same tier in corpus.json and
    the harness."""

    def test_tier_mismatch_fails(self):
        harness = VALID_HARNESS.replace(
            'e!("z9-decline", Some("integrate"), None, DeclineExpected, z9_decline),',
            'e!("z9-decline", Some("integrate"), None, Core, z9_decline),',
        )
        write_fixture(self.tmp, harness_src=harness)
        rc, out = self.run_main([])
        self.assertEqual(rc, 1, out)
        self.assertIn("guard(c)", out)
        self.assertIn("z9-decline", out)
        self.assertNotIn("guard(a)", out)
        self.assertNotIn("guard(b)", out)
        self.assertNotIn("guard(d)", out)
        self.assertNotIn("guard(e)", out)


class GuardDCorpusIntegrityTests(RunFixtureMixin, unittest.TestCase):
    """Guard (d): corpus.json must parse and have no duplicate id."""

    def test_duplicate_id_fails(self):
        entries = VALID_ENTRIES + [dict(VALID_ENTRIES[0])]  # duplicate "d1-cubic"
        write_fixture(
            self.tmp,
            entries=entries,
            readme_src=render_readme(core=3, decline=1, known_defect=0),
        )
        rc, out = self.run_main([])
        self.assertEqual(rc, 1, out)
        self.assertIn("guard(d)", out)
        self.assertIn("d1-cubic", out)
        self.assertNotIn("guard(a)", out)
        self.assertNotIn("guard(b)", out)
        self.assertNotIn("guard(c)", out)
        self.assertNotIn("guard(e)", out)

    def test_unparseable_json_fails(self):
        write_fixture(self.tmp, entries="{not valid json")
        rc, out = self.run_main([])
        self.assertEqual(rc, 1, out)
        self.assertIn("schema_error", out)


class GuardEGroundTruthCoverageTests(RunFixtureMixin, unittest.TestCase):
    """Guard (e): every `core`-tier entry needs an independent claim in
    ground_truth.py (by family prefix -- see the gate's own docstring)."""

    def test_missing_ground_truth_for_core_entry_fails(self):
        ground_truth = VALID_GROUND_TRUTH.replace(
            'ok(True, "d1-ctrl (hand) the near-miss control is NOT 3x^2+1")\n', ""
        ).replace('ok(True, "d1 d/dx(x^3) = 3x^2")\n', "")
        write_fixture(self.tmp, ground_truth_src=ground_truth)
        rc, out = self.run_main([])
        self.assertEqual(rc, 1, out)
        self.assertIn("guard(e)", out)
        self.assertIn("d1-cubic", out)
        self.assertNotIn("guard(a)", out)
        self.assertNotIn("guard(b)", out)
        self.assertNotIn("guard(c)", out)
        self.assertNotIn("guard(d)", out)

    def test_missing_ground_truth_for_decline_entry_is_not_a_violation(self):
        """`z9-decline` (tier `decline_expected`) has NO family token in
        `VALID_GROUND_TRUTH` on purpose -- guard (e) must not flag it,
        mirroring the real corpus's `prob7-geometric-symbolic-p` (see the
        gate's docstring)."""
        write_fixture(self.tmp)
        rc, out = self.run_main([])
        self.assertEqual(rc, 0, out)
        self.assertNotIn("z9-decline", out)


if __name__ == "__main__":
    unittest.main()
