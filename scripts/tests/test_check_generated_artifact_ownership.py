#!/usr/bin/env python3
"""Controls for scripts/check-generated-artifact-ownership.py (ADR-0652).

One case per guard, and each asserts BOTH that its own arm fired AND that the
others stayed silent -- so a deleted guard is killed by exactly one case, and
an over-firing guard is killed by every other one.

Every case that asserts a FAIL is paired with the same input made benign, in
the same case. This repository's standing rule is that an empty result and a
wrong query are the same observation; a control that only ever exercises the
failing side cannot tell a fired guard from a broken fixture.

The three sandbox arms (RUNS, CTRL, OWNER) run against SYNTHETIC trees -- two
tiny scripts and one JSON file -- rather than a copy of the repository. That is
not only speed: a synthetic producer can be made to do the wrong thing on
purpose, and the real ones, correctly, cannot.

Run directly, or through the mutation harness:

    python3 -m unittest scripts.tests.test_check_generated_artifact_ownership
    python3 scripts/tests/mutation_controls.py artifact-ownership
"""

from __future__ import annotations

import importlib.util
import json
import pathlib
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SUBJECT = ROOT / "scripts" / "check-generated-artifact-ownership.py"

_spec = importlib.util.spec_from_file_location("_artifact_ownership", SUBJECT)
assert _spec is not None and _spec.loader is not None
own = importlib.util.module_from_spec(_spec)
sys.modules["_artifact_ownership"] = own
_spec.loader.exec_module(own)


ARTIFACT = "artifacts/thing-v1.json"

GOOD_DOC = {
    "alpha": 1,
    "beta": 2,
    "coverage": {"tier_one": 5, "tier_two": 6},
}


def synthetic(runs=(), reads=(), owner_argv=("--write",)) -> "own.Artifact":
    """An Artifact over a two-file tree, shaped like the real registry."""
    return own.Artifact(
        path=ARTIFACT,
        owner=own.Producer("scripts/owner.py", owner_argv, "synthetic owner"),
        required_keys=("alpha", "beta", "coverage"),
        required_nested={"coverage": ("tier_one", "tier_two")},
        runs=tuple(runs),
        reads=tuple(reads),
    )


def render(doc) -> str:
    return json.dumps(doc, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


# The synthetic owner: rewrites the artifact to the canonical document, so it
# restores any perturbation byte-for-byte. Its argv is checked, so a case can
# hand it a flag it does not accept and watch OWNER fire.
OWNER_SRC = f'''#!/usr/bin/env python3
import json, pathlib, sys
if "--write" not in sys.argv[1:]:
    sys.exit(9)
p = pathlib.Path(__file__).resolve().parents[1] / {ARTIFACT!r}
p.write_text(json.dumps({GOOD_DOC!r}, indent=2, sort_keys=True,
                        ensure_ascii=False) + "\\n")
'''

# A second writer: rewrites the artifact WITHOUT `beta`, and exits 0. The
# defect this whole gate exists for, in eight lines.
THIEF_SRC = f'''#!/usr/bin/env python3
import json, pathlib, sys
p = pathlib.Path(__file__).resolve().parents[1] / {ARTIFACT!r}
d = json.loads(p.read_text())
d.pop("beta", None)
p.write_text(json.dumps(d, indent=2, sort_keys=True, ensure_ascii=False) + "\\n")
sys.exit(0)
'''

# A well-behaved producer: writes a DIFFERENT file. Proves the sandbox is
# reachable and writable while the guarded artifact is untouched, which is the
# false-positive control for RUNS.
NEIGHBOUR_SRC = '''#!/usr/bin/env python3
import pathlib
p = pathlib.Path(__file__).resolve().parents[1] / "artifacts/other-v1.json"
p.write_text('{"unrelated": true}\\n')
'''


class SandboxCase(unittest.TestCase):
    """Builds a two-script tree with the canonical artifact in it."""

    def build(self, **scripts: str) -> pathlib.Path:
        tmp = tempfile.TemporaryDirectory(prefix="ownership-control-")
        self.addCleanup(tmp.cleanup)
        root = pathlib.Path(tmp.name)
        (root / "artifacts").mkdir()
        (root / "scripts").mkdir()
        (root / ARTIFACT).write_text(render(GOOD_DOC))
        (root / "scripts" / "owner.py").write_text(OWNER_SRC)
        for name, src in scripts.items():
            (root / "scripts" / f"{name}.py").write_text(src)
        return root


class KeysArm(SandboxCase):
    def test_a_dropped_top_level_key_is_named(self):
        art = synthetic()
        self.assertEqual(own.keys_arm(GOOD_DOC, art), [],
                         "the canonical document must not fire KEYS")
        hurt = {k: v for k, v in GOOD_DOC.items() if k != "beta"}
        fails = own.keys_arm(hurt, art)
        self.assertEqual(len(fails), 1, fails)
        self.assertIn("KEYS", fails[0])
        self.assertIn("'beta'", fails[0])
        # The remedy must name the owner, or the message repeats the mistake
        # `--check` made: advice whose only effect is the deletion.
        self.assertIn("scripts/owner.py", fails[0])

    def test_a_dropped_nested_tier_count_is_named(self):
        art = synthetic()
        hurt = dict(GOOD_DOC, coverage={"tier_one": 5})
        fails = own.keys_arm(hurt, art)
        self.assertEqual(len(fails), 1, fails)
        self.assertIn("tier_two", fails[0])
        # Top level intact, so only the nested check can have fired -- the
        # case that a `coverage` key alone would miss. Both messages carry
        # "missing [", so the discriminator is the top-level one's remedy
        # sentence, which the nested one does not have.
        self.assertIn("`coverage` missing", fails[0])
        self.assertNotIn("derives these", fails[0])

    def test_a_non_object_top_level_is_refused(self):
        self.assertEqual(len(own.keys_arm([1, 2, 3], synthetic())), 1)


class KnownArm(SandboxCase):
    def test_an_unclassified_script_is_named(self):
        art = synthetic(reads=(own.ReadOnly("scripts/reader.py", "n/a"),))
        known = {"scripts/owner.py", "scripts/reader.py"}
        self.assertEqual(own.known_arm(art, known), [])
        fails = own.known_arm(art, known | {"scripts/newcomer.py"})
        self.assertEqual(len(fails), 1, fails)
        self.assertIn("scripts/newcomer.py", fails[0])
        self.assertIn("not classified", fails[0])

    def test_a_stale_classification_is_named(self):
        art = synthetic(reads=(own.ReadOnly("scripts/reader.py", "n/a"),))
        fails = own.known_arm(art, {"scripts/owner.py"})
        self.assertEqual(len(fails), 1, fails)
        self.assertIn("scripts/reader.py", fails[0])
        self.assertIn("no longer names", fails[0])

    def test_discovery_reads_the_tree_not_a_list(self):
        # The positive control that makes the negative meaningful: a name that
        # IS present must be found by the same call that reports absence.
        # Built from parts on purpose. Spelling the basename out here would
        # make THIS file a script that names the artifact, so the KNOWN arm
        # would demand it be classified -- which it correctly did on the
        # first run of this suite.
        real = "mathlib-statable-" + "vocabulary-v1.json"
        found = own.referencing_scripts(real)
        self.assertIn("scripts/gen-autogenesis-statable-vocabulary.py", found)
        absent = own.referencing_scripts(real.replace("v1", "NOPE"))
        self.assertEqual(absent, set())


class ReadsArm(SandboxCase):
    def test_a_declared_reader_that_writes_is_rejected(self):
        art = synthetic(reads=(own.ReadOnly("scripts/reader.py", "n/a"),))
        pure = "import json\nd = json.loads(open('x').read())\nprint(d)\n"
        self.assertEqual(own.reads_arm(art, lambda p: pure), [])
        impure = pure + "open('y', 'w').write('!')\n"
        fails = own.reads_arm(art, lambda p: impure)
        self.assertEqual(len(fails), 1, fails)
        self.assertIn("scripts/reader.py", fails[0])

    def test_write_calls_sees_each_shape_and_no_others(self):
        self.assertEqual(own.write_calls("x = open('a').read()\n"), [])
        self.assertEqual(own.write_calls("p.read_text()\njson.load(f)\n"), [])
        for src in ("p.write_text('a')\n",
                    "p.write_bytes(b'a')\n",
                    "json.dump(d, f)\n",
                    "open('a', 'w')\n",
                    "open('a', mode='a')\n",
                    "shutil.copy('a', 'b')\n",
                    "os.replace('a', 'b')\n",
                    "p.unlink()\n"):
            with self.subTest(src=src):
                self.assertEqual(len(own.write_calls(src)), 1, src)


class RunsArm(SandboxCase):
    def test_a_producer_that_rewrites_the_artifact_is_caught(self):
        root = self.build(thief=THIEF_SRC, neighbour=NEIGHBOUR_SRC)

        good = synthetic(runs=(own.Producer("scripts/neighbour.py", (), "ok"),))
        fails, ran = own.runs_arm(root, good)
        self.assertEqual(ran, 1)
        self.assertEqual(fails, [],
                         "a producer writing a DIFFERENT file must not fire")
        self.assertTrue((root / "artifacts/other-v1.json").is_file(),
                        "the sandbox must be reachable, or RUNS proves nothing")

        bad = synthetic(runs=(own.Producer("scripts/thief.py", (), "bad"),))
        fails, ran = own.runs_arm(root, bad)
        self.assertEqual(ran, 1)
        self.assertEqual(len(fails), 1, fails)
        self.assertIn("scripts/thief.py", fails[0])
        self.assertIn("DELETED ['beta']", fails[0])

    def test_the_artifact_is_restored_after_a_finding(self):
        # One finding must not cascade: the later arms run against the same
        # sandbox, and a left-behind mutation would fire every one of them.
        root = self.build(thief=THIEF_SRC)
        art = synthetic(runs=(own.Producer("scripts/thief.py", (), "bad"),))
        own.runs_arm(root, art)
        self.assertEqual((root / ARTIFACT).read_text(), render(GOOD_DOC))

    def test_a_producer_that_deletes_the_artifact_is_caught(self):
        root = self.build(nuke='import pathlib\n'
                               'pathlib.Path(__file__).resolve().parents[1]'
                               f'.joinpath({ARTIFACT!r}).unlink()\n')
        art = synthetic(runs=(own.Producer("scripts/nuke.py", (), "bad"),))
        fails, _ = own.runs_arm(root, art)
        self.assertEqual(len(fails), 1, fails)
        self.assertIn("DELETED", fails[0])


class CtrlArm(SandboxCase):
    def test_a_blind_comparison_is_reported_as_inert(self):
        root = self.build()
        art = synthetic()
        self.assertEqual(own.ctrl_arm(root, art), [],
                         "the planted writer must be rejected on a sound tree")

        original = own.compare_after_run
        self.addCleanup(setattr, own, "compare_after_run", original)
        own.compare_after_run = lambda *a, **k: None
        fails = own.ctrl_arm(root, art)
        self.assertEqual(len(fails), 1, fails)
        self.assertIn("inert", fails[0])

    def test_the_planted_control_leaves_nothing_behind(self):
        root = self.build()
        own.ctrl_arm(root, synthetic())
        self.assertFalse((root / "scripts/_ownership_control.py").exists())
        self.assertEqual((root / ARTIFACT).read_text(), render(GOOD_DOC))


class OwnerArm(SandboxCase):
    def test_an_owner_that_does_not_restore_is_caught(self):
        root = self.build()
        self.assertEqual(own.owner_arm(root, synthetic()), [],
                         "the synthetic owner does restore, so this must pass")

        # Same tree, same owner script, an argv it refuses: the sandbox is
        # reachable and the restoration still does not happen.
        fails = own.owner_arm(root, synthetic(owner_argv=("--nope",)))
        self.assertEqual(len(fails), 1, fails)
        self.assertIn("did not restore", fails[0])

    def test_the_perturbation_is_real(self):
        # If OWNER perturbed nothing, it would pass against an owner that does
        # nothing at all -- the shape of a control that cannot fail.
        root = self.build(inert="pass\n")
        art = own.Artifact(
            path=ARTIFACT,
            owner=own.Producer("scripts/inert.py", (), "does nothing"),
            required_keys=("alpha", "beta", "coverage"),
            required_nested={},
            runs=(), reads=())
        fails = own.owner_arm(root, art)
        self.assertEqual(len(fails), 1, fails)


class KeyDelta(SandboxCase):
    def test_it_names_what_moved(self):
        a = render({"x": 1, "y": 2})
        self.assertIn("DELETED ['y']", own.key_delta(a, render({"x": 1})))
        self.assertIn("added ['z']",
                      own.key_delta(a, render({"x": 1, "y": 2, "z": 3})))
        self.assertIn("changed ['x']",
                      own.key_delta(a, render({"x": 9, "y": 2})))
        self.assertIn("no longer valid JSON", own.key_delta(a, "{{{"))


class RealTree(SandboxCase):
    """The false-positive control, on the real registry rather than a fixture.

    Sandbox-free arms only. RUNS/CTRL/OWNER against the real tree are what the
    gate itself does; duplicating them here would put a 10-second copy inside
    every mutant of the mutation sweep and measure nothing new.
    """

    def test_the_committed_registry_passes_the_static_arms(self):
        self.assertTrue(own.GUARDED, "an empty registry guards nothing")
        for art in own.GUARDED:
            with self.subTest(artifact=art.path):
                committed = ROOT / art.path
                self.assertTrue(committed.is_file(), art.path)
                doc = json.loads(committed.read_text())
                self.assertEqual(own.keys_arm(doc, art), [])
                found = own.referencing_scripts(
                    pathlib.PurePath(art.path).name)
                self.assertEqual(own.known_arm(art, found), [])
                self.assertEqual(
                    own.reads_arm(art, lambda p: (ROOT / p).read_text()), [])

    def test_the_owner_is_never_also_a_runs_producer(self):
        for art in own.GUARDED:
            with self.subTest(artifact=art.path):
                self.assertNotIn(art.owner.path,
                                 {p.path for p in art.runs},
                                 "the owner writes by design; running it as a "
                                 "non-owner producer would always fire RUNS")


if __name__ == "__main__":
    unittest.main()
