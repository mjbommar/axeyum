"""Control suite for `scripts/check-arith-boundary.sh`.

The gate exists because ADR-1710 measured eight private bignum paths growing
from eight private `use num_bigint::...` lines. A gate that could not fail
would be worse than no gate at all, so each test below plants a specific
violation in a **scratch copy** of the repository (never the shared worktree —
a mutant on disk is every other lane's build) and requires exit 1, plus one
test that requires exit 0 on the unmodified tree.

Mutation discipline: each guard in the script is covered by exactly one test
here, so deleting a guard kills exactly one of them.
"""

from __future__ import annotations

import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
SCRIPT = "scripts/check-arith-boundary.sh"
ALLOWLIST = "scripts/arith-boundary-allowlist.txt"


def _scratch_repo(tmp: Path) -> Path:
    """A minimal copy of the tree the gate reads: the script, the allowlist,
    and `crates/` — enough for the gate to run and nothing else."""
    root = tmp / "repo"
    (root / "scripts" / "tests").mkdir(parents=True)
    shutil.copy2(REPO / SCRIPT, root / SCRIPT)
    os.chmod(root / SCRIPT, 0o755)
    shutil.copy2(REPO / ALLOWLIST, root / ALLOWLIST)
    # Only the manifests and Rust sources matter; copying the whole of
    # `crates/` would drag in target dirs and corpora.
    for path in (REPO / "crates").rglob("*"):
        if path.is_dir():
            continue
        if path.suffix not in {".rs", ".toml"}:
            continue
        if "target" in path.parts:
            continue
        destination = root / path.relative_to(REPO)
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, destination)
    return root


def _run(root: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [str(root / SCRIPT)],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
    )


class ArithBoundaryGateControls(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.root = _scratch_repo(Path(self._tmp.name))

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def test_the_unmodified_tree_passes(self) -> None:
        """A positive control. Without this, every test below could be passing
        because the gate always fails."""
        result = _run(self.root)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("arith boundary holds", result.stdout)

    def test_a_planted_rust_import_fails_the_gate(self) -> None:
        """Guard 1: a Rust source outside `axeyum-arith` naming the upstream
        crate."""
        planted = self.root / "crates" / "axeyum-ir" / "src" / "planted_gate_probe.rs"
        planted.write_text("use num_bigint::BigInt;\n")
        result = _run(self.root)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("planted_gate_probe.rs", result.stdout)

    def test_a_planted_manifest_entry_fails_the_gate(self) -> None:
        """Guard 2: a manifest outside `axeyum-arith` declaring one of the
        four crates. Planted in a crate that has no source hit, so only the
        manifest guard can catch it."""
        manifest = self.root / "crates" / "axeyum-fp" / "Cargo.toml"
        text = manifest.read_text()
        manifest.write_text(text.replace("[dependencies]", "[dependencies]\nnum-rational.workspace = true", 1))
        result = _run(self.root)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("axeyum-fp/Cargo.toml", result.stdout)

    def test_a_stale_allowlist_entry_fails_the_gate(self) -> None:
        """Guard 3: an allowlist line naming a file that no longer has a hit.
        A stale exception is a hole nobody can see, so it must fail in the
        other direction."""
        allowlist = self.root / ALLOWLIST
        allowlist.write_text(
            allowlist.read_text() + "crates/axeyum-ir/src/lib.rs # stale probe\n"
        )
        result = _run(self.root)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("stale allowlist", result.stdout)

    def test_a_missing_allowlisted_path_fails_the_gate(self) -> None:
        """The other half of guard 3: an allowlist line naming a file that
        does not exist at all (a rename that did not update this file)."""
        allowlist = self.root / ALLOWLIST
        allowlist.write_text(
            allowlist.read_text() + "crates/axeyum-cas/src/does_not_exist.rs # probe\n"
        )
        result = _run(self.root)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("no such file", result.stdout)

    def test_axeyum_arith_itself_is_exempt(self) -> None:
        """The exemption is real, not accidental: `axeyum-arith` is the one
        crate allowed to name the upstream crates, and it does so on many
        lines. If this ever fails, the exemption path has broken and the gate
        is about to be disabled by whoever hits it."""
        planted = self.root / "crates" / "axeyum-arith" / "src" / "planted_exempt_probe.rs"
        planted.write_text("use num_bigint::BigInt;\nuse num_rational::BigRational;\n")
        result = _run(self.root)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_the_allowed_files_are_actually_allowed(self) -> None:
        """An allowlisted CAS file has real hits and is not reported. Without
        this the allowlist could be inert and the tree could be passing for
        the wrong reason."""
        allowlisted = self.root / "crates" / "axeyum-cas" / "src" / "ntheory.rs"
        self.assertIn("num_bigint", allowlisted.read_text())
        result = _run(self.root)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("ntheory.rs", result.stdout)


if __name__ == "__main__":
    unittest.main()
