"""Controls for `scripts/check-cas-internal-residue.py` (roadmap W1-13).

One test per guard, each written so every OTHER field of its fixture is
valid -- otherwise a mutation would kill several tests at once and the kill
set would not tell you which guard the test actually measures. This mirrors
`scripts/tests/test_check_cas_substance.py`'s own discipline.

Registered in `scripts/tests/mutation_controls.py` under
`cas-internal-residue`, so each guard is deleted and the harness checks that
exactly one test dies.
"""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
GATE = REPO_ROOT / "scripts" / "check-cas-internal-residue.py"


def _load_gate():
    spec = importlib.util.spec_from_file_location("check_cas_internal_residue", GATE)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def kernel_reconstructed_fact(fact_id: str, fragment: str = "frag-a") -> dict:
    """A minimal `cas-certificate` fact whose evidence names the kernel
    package under an executed `cargo test` segment -- classifies as
    `kernel-reconstructed` by `validate-facts.py`'s own
    `classify_cas_certificate_checker`."""
    return {
        "id": fact_id,
        "proof_route": "cas-certificate",
        "formal": {"fragment": fragment},
        "evidence": [
            {
                "id": "e1",
                "kind": "test-run",
                "supports": ["main"],
                "check_status": "checked",
                "checker_command": "cargo test -p axeyum-lean-kernel --lib fixture -- --exact",
            }
        ],
    }


def cas_internal_fact(fact_id: str, fragment: str = "frag-b") -> dict:
    """A minimal `cas-certificate` fact whose evidence names only the CAS
    package -- classifies as `cas-internal`."""
    return {
        "id": fact_id,
        "proof_route": "cas-certificate",
        "formal": {"fragment": fragment},
        "evidence": [
            {
                "id": "e1",
                "kind": "test-run",
                "supports": ["main"],
                "check_status": "checked",
                "checker_command": "cargo test -p axeyum-cas --lib fixture -- --exact",
            }
        ],
    }


def unrecognized_fact(fact_id: str, fragment: str = "frag-c") -> dict:
    """A `cas-certificate` fact whose checker_command names neither package
    -- classifies as `unrecognized`. `validate-facts.py`'s own `validate_one`
    would refuse this fact; this gate reads raw JSON directly and must catch
    it independently."""
    return {
        "id": fact_id,
        "proof_route": "cas-certificate",
        "formal": {"fragment": fragment},
        "evidence": [
            {
                "id": "e1",
                "kind": "test-run",
                "supports": ["main"],
                "check_status": "checked",
                "checker_command": "echo hello",
            }
        ],
    }


def write_facts(facts_dir: Path, facts: list[dict]) -> None:
    for fact in facts:
        (facts_dir / f"{fact['id'].replace(':', '-')}.json").write_text(json.dumps(fact))


class CasInternalResidueGateTests(unittest.TestCase):
    def setUp(self):
        self.gate = _load_gate()
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.facts_dir = self.root / "artifacts" / "facts"
        self.facts_dir.mkdir(parents=True)
        self.ratchet_path = self.root / "residue.ratchet"

    def tearDown(self):
        self.tmp.cleanup()

    def run_gate(self, extra_args=()):
        """Run the gate with stdout/stderr captured into a buffer.

        The gate prints its own `FAIL: ...`/`OK: ...` diagnostics on the
        exact code paths under test here, and those strings look exactly
        like a unittest failure/error header to
        `scripts/tests/mutation_controls.py`'s output scan. Redirecting
        keeps this suite's real pass/fail signal -- the assertions below --
        the only thing that reaches the runner's captured output, exactly as
        `test_check_cas_substance.py`'s own `run_gate` does.
        """
        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer), contextlib.redirect_stderr(buffer):
            status = self.gate.main(
                [
                    "--facts-root",
                    str(self.root),
                    "--ratchet",
                    str(self.ratchet_path),
                    *extra_args,
                ]
            )
        return status

    # -- baseline behaviour, no mutation tied to these -----------------------

    def test_missing_facts_dir_is_a_usage_error(self):
        empty_root = Path(tempfile.mkdtemp())
        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer), contextlib.redirect_stderr(buffer):
            rc = self.gate.main(
                ["--facts-root", str(empty_root), "--ratchet", str(self.ratchet_path)]
            )
        self.assertEqual(rc, 2)

    def test_update_then_check_round_trips_clean(self):
        write_facts(
            self.facts_dir,
            [kernel_reconstructed_fact("F:kr-1"), cas_internal_fact("F:ci-1")],
        )
        self.assertEqual(self.run_gate(["--update"]), 0)
        self.assertEqual(self.run_gate(), 0)

    def test_a_new_cas_internal_fact_needs_no_ratchet_edit(self):
        write_facts(self.facts_dir, [kernel_reconstructed_fact("F:kr-1")])
        self.assertEqual(self.run_gate(["--update"]), 0)
        # A brand-new cas-internal fact appears -- the floor only tracks
        # kernel-reconstructed rows, so this must NOT fail the gate.
        write_facts(self.facts_dir, [cas_internal_fact("F:ci-new")])
        self.assertEqual(self.run_gate(), 0)

    def test_a_new_kernel_reconstructed_fact_needs_no_ratchet_edit(self):
        write_facts(self.facts_dir, [cas_internal_fact("F:ci-1")])
        self.assertEqual(self.run_gate(["--update"]), 0)
        write_facts(self.facts_dir, [kernel_reconstructed_fact("F:kr-new")])
        self.assertEqual(self.run_gate(), 0)

    def test_read_ratchet_skips_comments_and_blank_lines(self):
        self.ratchet_path.write_text(
            "# a comment\n\nF:kr-1\tkernel-reconstructed\tfrag-a\n"
        )
        recorded = self.gate.read_ratchet(self.ratchet_path)
        self.assertEqual(recorded, {"F:kr-1": ("kernel-reconstructed", "frag-a")})

    def test_read_ratchet_absent_file_is_none(self):
        self.assertIsNone(self.gate.read_ratchet(self.root / "nope.ratchet"))

    # -- guards, each tied to exactly one entry in mutation_controls.py ------

    def test_G1_an_unrecognized_fact_is_refused(self):
        write_facts(self.facts_dir, [kernel_reconstructed_fact("F:kr-1")])
        self.assertEqual(self.run_gate(["--update"]), 0)
        write_facts(self.facts_dir, [unrecognized_fact("F:mystery")])
        self.assertEqual(self.run_gate(), 1)

    def test_G2_a_missing_ratchet_is_refused(self):
        write_facts(self.facts_dir, [kernel_reconstructed_fact("F:kr-1")])
        # Deliberately never call --update: no ratchet file exists.
        self.assertEqual(self.run_gate(), 1)

    def test_G3_a_reclassified_fact_is_refused(self):
        write_facts(self.facts_dir, [kernel_reconstructed_fact("F:kr-1")])
        self.assertEqual(self.run_gate(["--update"]), 0)
        # F:kr-1 is still present, but its checker_command now names only
        # the CAS -- reconstruction regressed to cas-internal.
        write_facts(self.facts_dir, [cas_internal_fact("F:kr-1")])
        self.assertEqual(self.run_gate(), 1)

    def test_G4_a_vanished_fact_is_refused(self):
        write_facts(
            self.facts_dir,
            [kernel_reconstructed_fact("F:kr-1"), kernel_reconstructed_fact("F:kr-2")],
        )
        self.assertEqual(self.run_gate(["--update"]), 0)
        (self.facts_dir / "F-kr-1.json").unlink()
        self.assertEqual(self.run_gate(), 1)


if __name__ == "__main__":
    unittest.main()
