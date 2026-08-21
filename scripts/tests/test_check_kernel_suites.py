#!/usr/bin/env python3
"""Controls for ``scripts/check-kernel-suites.sh``.

CLAUDE.md: *a checker that cannot fail is worse than no checker.*  Every
scenario below drives ONE guard of the shipped script to failure on a synthetic
tree, plus the cases it must ACCEPT.  The script is never re-implemented here --
``AXEYUM_KERNEL_SUITES_ROOT`` points the real file at a throwaway tree and
``AXEYUM_CARGO`` at a stub whose transcript is whatever the scenario needs.

Each control is tied to exactly one guard, so deleting a guard must kill exactly
one of these.  Registered with ``scripts/tests/mutation_controls.py`` under
``kernel-suite-partition``; run::

    python3 -m unittest scripts.tests.test_check_kernel_suites
    python3 scripts/tests/mutation_controls.py kernel-suite-partition
"""

from __future__ import annotations

import os
import pathlib
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check-kernel-suites.sh"

PROBE = '#[path = "support/lean_probe.rs"]\nmod lean_probe;\n'
PLAIN = "#[test]\nfn t() {}\n"

# A stub `cargo` that prints a cargo-shaped transcript for the targets it is
# given, records its argv, and exits with whatever the scenario asked for.
STUB_CARGO = r"""#!/usr/bin/env bash
printf '%s\n' "$*" >> "$ARGV_LOG"
echo "   Running unittests src/lib.rs (/t/debug/deps/pkg-0)"
echo "running $LIB_TESTS tests"
prev=""
for arg in "$@"; do
  if [ "$prev" = "--test" ]; then
    echo "   Running tests/$arg.rs (/t/debug/deps/$arg-0)"
    if [ "$arg" = "$INERT_SUITE" ]; then
      echo "running 0 tests"
    else
      echo "running $SUITE_TESTS tests"
    fi
  fi
  prev="$arg"
done
exit ${CARGO_RC:-0}
"""


class KernelSuitePartitionControls(unittest.TestCase):
    """One scenario per guard in `scripts/check-kernel-suites.sh`."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory(dir="/data0/axeyum/scratch"
                                                if pathlib.Path("/data0/axeyum/scratch").is_dir()
                                                else None)
        self.addCleanup(self._tmp.cleanup)
        self.root = pathlib.Path(self._tmp.name)
        (self.root / "scripts").mkdir(parents=True)
        self.tests = self.root / "crates/axeyum-lean-kernel/tests"
        self.tests.mkdir(parents=True)
        self.argv_log = self.root / "argv.log"
        stub = self.root / "cargo-stub"
        stub.write_text(STUB_CARGO)
        stub.chmod(0o755)
        self.stub = stub

    # -- tree construction --------------------------------------------------

    def suite(self, name: str, *, lean: bool = False, body: str = "") -> None:
        self.tests.joinpath(f"{name}.rs").write_text((PROBE if lean else PLAIN) + body)

    def gate(self, *targets: str, package: str = "axeyum-lean-kernel") -> None:
        """Write a `check-lean-gate.sh` whose suite table names `targets`."""
        rows = "".join(f"{package}||{t}\n" for t in targets)
        self.root.joinpath("scripts/check-lean-gate.sh").write_text(
            "#!/usr/bin/env bash\nsuites=$(\n  cat <<'EOF'\n" + rows + "EOF\n)\n"
        )

    def run_gate(self, *args: str, lib_tests: int = 3, suite_tests: int = 2,
                 inert: str = "", cargo_rc: int = 0) -> subprocess.CompletedProcess:
        env = dict(os.environ)
        env.update(
            AXEYUM_KERNEL_SUITES_ROOT=str(self.root),
            AXEYUM_CARGO=str(self.stub),
            ARGV_LOG=str(self.argv_log),
            LIB_TESTS=str(lib_tests),
            SUITE_TESTS=str(suite_tests),
            INERT_SUITE=inert,
            CARGO_RC=str(cargo_rc),
        )
        return subprocess.run(
            ["bash", str(SCRIPT), *args],
            capture_output=True, text=True, env=env, cwd=str(ROOT),
        )

    def healthy(self) -> None:
        """Two push suites, one real-Lean suite, and a gate table that owns it."""
        self.suite("axiom_footprint")
        self.suite("structure_eta")
        self.suite("real_lean_kernel_replay", lean=True)
        self.gate("real_lean_kernel_replay")

    # -- the case it must ACCEPT -------------------------------------------

    def test_accepts_a_total_partition(self) -> None:
        self.healthy()
        got = self.run_gate()
        self.assertEqual(got.returncode, 0, got.stdout + got.stderr)
        self.assertIn("2 run here, 1 owned by", got.stdout)

    def test_runs_the_push_half_and_only_the_push_half(self) -> None:
        """The point of the split: the real-Lean suite must not be re-run here."""
        self.healthy()
        got = self.run_gate()
        self.assertEqual(got.returncode, 0, got.stdout + got.stderr)
        argv = self.argv_log.read_text()
        self.assertIn("--test axiom_footprint", argv)
        self.assertIn("--test structure_eta", argv)
        self.assertIn("--lib", argv)
        self.assertNotIn("real_lean_kernel_replay", argv)

    # -- one scenario per guard --------------------------------------------

    def test_rejects_a_real_lean_suite_no_gate_owns(self) -> None:
        """The defect this gate was written for, found live on 2026-08-19."""
        self.healthy()
        self.suite("real_lean_string_monoid_crosscheck", lean=True)
        got = self.run_gate()
        self.assertEqual(got.returncode, 1, got.stdout + got.stderr)
        self.assertIn("real_lean_string_monoid_crosscheck", got.stderr)
        self.assertIn("does not list it", got.stderr)

    def test_rejects_a_gate_entry_whose_suite_is_gone(self) -> None:
        self.healthy()
        self.gate("real_lean_kernel_replay", "real_lean_deleted_crosscheck")
        got = self.run_gate()
        self.assertEqual(got.returncode, 1, got.stdout + got.stderr)
        self.assertIn("does not exist", got.stderr)

    def test_rejects_a_gate_entry_that_needs_no_lean(self) -> None:
        """Listed there AND runnable here is the duplication being removed."""
        self.healthy()
        self.gate("real_lean_kernel_replay", "structure_eta")
        got = self.run_gate()
        self.assertEqual(got.returncode, 1, got.stdout + got.stderr)
        self.assertIn("does not use", got.stderr)
        self.assertIn("structure_eta", got.stderr)

    def test_rejects_a_hand_rolled_lean_resolver(self) -> None:
        """A suite that dodges the probe is outside BOTH halves' accounting."""
        self.healthy()
        self.suite(
            "sneaky_lean",
            body='fn bin() -> String { std::env::var("AXEYUM_LEAN_BIN").unwrap() }\n',
        )
        got = self.run_gate()
        self.assertEqual(got.returncode, 1, got.stdout + got.stderr)
        self.assertIn("sneaky_lean", got.stderr)
        self.assertIn("resolves a `lean` binary of its own", got.stderr)

    def test_rejects_a_hand_written_checked_marker(self) -> None:
        """The real-Lean gate parses one shape; anything else sums as zero."""
        self.healthy()
        self.suite(
            "real_lean_hand_counted",
            lean=True,
            body='fn r() { println!("{}|tag|1|done", lean_probe::CHECKED_MARKER); }\n',
        )
        self.gate("real_lean_kernel_replay", "real_lean_hand_counted")
        got = self.run_gate()
        self.assertEqual(got.returncode, 1, got.stdout + got.stderr)
        self.assertIn("real_lean_hand_counted", got.stderr)
        self.assertIn("report_checked", got.stderr)

    def test_rejects_a_tree_it_discovered_nothing_in(self) -> None:
        """A gate that discovers nothing must fail, not pass."""
        self.suite("axiom_footprint")
        self.gate()
        got = self.run_gate()
        self.assertEqual(got.returncode, 1, got.stdout + got.stderr)
        self.assertIn("discovered 1 suite", got.stderr)

    def test_rejects_an_unreadable_lean_gate_table(self) -> None:
        self.healthy()
        self.root.joinpath("scripts/check-lean-gate.sh").write_text(
            "#!/usr/bin/env bash\n# the table has been rewritten in some new format\n"
        )
        got = self.run_gate()
        self.assertEqual(got.returncode, 1, got.stdout + got.stderr)
        self.assertIn("read ZERO", got.stderr)

    def test_rejects_a_split_that_leaves_nothing_to_run(self) -> None:
        self.suite("real_lean_kernel_replay", lean=True)
        self.suite("real_lean_inductive_crosscheck", lean=True)
        self.gate("real_lean_kernel_replay", "real_lean_inductive_crosscheck")
        got = self.run_gate()
        self.assertEqual(got.returncode, 1, got.stdout + got.stderr)
        self.assertIn("run NOTHING at push time", got.stderr)
        # Named, and named VERBATIM. This message carried `axiom_footprint` in
        # unescaped backticks inside a double-quoted `echo`, so the shell ran it
        # as a command and substituted the empty output -- the CLAUDE.md
        # commit-message trap, in a gate's own explanation of itself. Asserting
        # the identifier is what notices; asserting the sentence around it does
        # not.
        self.assertIn("axiom_footprint", got.stderr)

    def test_rejects_an_inert_suite(self) -> None:
        """`cargo test` exits 0 on an empty binary; the count is the evidence."""
        self.healthy()
        got = self.run_gate(inert="structure_eta")
        self.assertEqual(got.returncode, 1, got.stdout + got.stderr)
        self.assertIn("ran ZERO tests", got.stderr)
        self.assertIn("INERT", got.stdout)

    def test_rejects_a_red_run(self) -> None:
        self.healthy()
        got = self.run_gate(cargo_rc=1)
        self.assertEqual(got.returncode, 1, got.stdout + got.stderr)
        self.assertIn("is red", got.stderr)

    def test_no_lib_leaves_the_unit_tests_to_the_workspace_sweep(self) -> None:
        """The hook's step above this one is `cargo test --workspace --lib`."""
        self.healthy()
        got = self.run_gate("--no-lib")
        self.assertEqual(got.returncode, 0, got.stdout + got.stderr)
        argv = self.argv_log.read_text()
        self.assertNotIn("--lib", argv)
        self.assertIn("--test axiom_footprint", argv)

    def test_rejects_an_argument_it_does_not_understand(self) -> None:
        self.healthy()
        got = self.run_gate("--run-everything")
        self.assertEqual(got.returncode, 2, got.stdout + got.stderr)

    # -- --list must not run cargo ----------------------------------------

    def test_list_mode_partitions_without_building(self) -> None:
        self.healthy()
        got = self.run_gate("--list")
        self.assertEqual(got.returncode, 0, got.stdout + got.stderr)
        self.assertIn("check-lean-gate.sh", got.stdout)
        self.assertFalse(self.argv_log.exists(), "--list must not invoke cargo")


if __name__ == "__main__":
    unittest.main()
