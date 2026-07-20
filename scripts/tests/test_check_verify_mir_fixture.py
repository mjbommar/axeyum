import hashlib
import importlib.util
import json
import pathlib
import shutil
import stat
import subprocess
import tempfile
import unittest


SCRIPT = pathlib.Path(__file__).resolve().parents[1] / "check-verify-mir-fixture.py"
SPEC = importlib.util.spec_from_file_location("check_verify_mir_fixture", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def rewrite_checksum(root: pathlib.Path, name: str) -> None:
    checksum_path = root / MODULE.CHECKSUM_NAME
    lines = checksum_path.read_text(encoding="ascii").splitlines()
    digest = hashlib.sha256((root / name).read_bytes()).hexdigest()
    rewritten = [f"{digest}  {name}" if line.endswith(f"  {name}") else line for line in lines]
    checksum_path.write_text("\n".join(rewritten) + "\n", encoding="ascii")


def exact_identity_script(path: pathlib.Path, capture_body: str) -> None:
    vv = "\\n".join(MODULE.REGISTERED_COMPILER["verbose_version"]) + "\\n"
    path.write_text(
        "#!/bin/sh\n"
        "if [ \"$1\" = \"-vV\" ]; then\n"
        f"  printf '%b' '{vv}'\n"
        "  exit 0\n"
        "fi\n"
        f"{capture_body}"
    )
    path.chmod(path.stat().st_mode | stat.S_IXUSR)


class MirFixtureCheckerTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self.tmp.name) / "mir"
        shutil.copytree(MODULE.CANONICAL_ROOT, self.root)

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def run_checker(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["python3", str(SCRIPT), *args, "--fixture-root", str(self.root)],
            check=False,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )

    def test_source_output_and_provenance_tampering_have_one_stable_class(self) -> None:
        for name in MODULE.HASHED_FILES:
            with self.subTest(name=name):
                root = pathlib.Path(self.tmp.name) / f"copy-{name.replace('.', '-')}"
                shutil.copytree(MODULE.CANONICAL_ROOT, root)
                with (root / name).open("ab") as stream:
                    stream.write(b"x")
                run = subprocess.run(
                    [
                        "python3",
                        str(SCRIPT),
                        "--verify",
                        "--fixture-root",
                        str(root),
                        "--rustc",
                        "/definitely/missing/rustc",
                    ],
                    check=False,
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                )
                self.assertNotEqual(run.returncode, 0)
                self.assertEqual(json.loads(run.stderr)["error_class"], "checksum_mismatch")

    def test_malformed_schema_is_checked_after_authentic_content(self) -> None:
        provenance = json.loads((self.root / MODULE.PROVENANCE_NAME).read_text())
        provenance["schema"] = "wrong"
        (self.root / MODULE.PROVENANCE_NAME).write_text(
            json.dumps(provenance, indent=2, sort_keys=True) + "\n"
        )
        rewrite_checksum(self.root, MODULE.PROVENANCE_NAME)
        run = self.run_checker("--verify", "--rustc", "/definitely/missing/rustc")
        self.assertNotEqual(run.returncode, 0)
        self.assertEqual(json.loads(run.stderr)["error_class"], "manifest_schema")

    def test_duplicate_manifest_key_fails_closed(self) -> None:
        raw = (self.root / MODULE.PROVENANCE_NAME).read_text()
        duplicate = raw.replace(
            '  "schema": "axeyum.verify-mir-capture.v1",',
            '  "schema": "axeyum.verify-mir-capture.v1",\n'
            '  "schema": "axeyum.verify-mir-capture.v1",',
        )
        (self.root / MODULE.PROVENANCE_NAME).write_text(duplicate)
        rewrite_checksum(self.root, MODULE.PROVENANCE_NAME)
        run = self.run_checker("--verify", "--rustc", "/definitely/missing/rustc")
        self.assertNotEqual(run.returncode, 0)
        self.assertEqual(
            json.loads(run.stderr)["error_class"], "duplicate_manifest_key"
        )

    def test_escaping_source_path_is_rejected_without_compiler_credit(self) -> None:
        provenance = json.loads((self.root / MODULE.PROVENANCE_NAME).read_text())
        provenance["source"] = "../source.rs"
        (self.root / MODULE.PROVENANCE_NAME).write_text(
            json.dumps(provenance, indent=2, sort_keys=True) + "\n"
        )
        rewrite_checksum(self.root, MODULE.PROVENANCE_NAME)
        run = self.run_checker("--verify", "--rustc", "/definitely/missing/rustc")
        self.assertNotEqual(run.returncode, 0)
        self.assertEqual(json.loads(run.stderr)["error_class"], "unsafe_path")

    def test_wrong_compiler_is_explicitly_unavailable_or_required(self) -> None:
        fake = pathlib.Path(self.tmp.name) / "wrong-rustc"
        fake.write_text("#!/bin/sh\nprintf 'rustc 0.0.0\\n'\n")
        fake.chmod(fake.stat().st_mode | stat.S_IXUSR)

        ordinary = self.run_checker("--verify", "--rustc", str(fake))
        self.assertEqual(ordinary.returncode, 0, ordinary.stderr)
        self.assertEqual(json.loads(ordinary.stdout)["compiler_replay"], "unavailable")

        required = self.run_checker("--require-replay", "--rustc", str(fake))
        self.assertNotEqual(required.returncode, 0)
        self.assertEqual(
            json.loads(required.stderr)["error_class"], "compiler_identity_mismatch"
        )

        repeated = self.run_checker("--verify", "--rustc", str(fake))
        self.assertEqual(repeated.stdout, ordinary.stdout)

    def test_nondeterministic_regeneration_leaves_prior_files_intact(self) -> None:
        fake = pathlib.Path(self.tmp.name) / "changing-rustc"
        counter = pathlib.Path(self.tmp.name) / "counter"
        exact_identity_script(
            fake,
            f"n=$(cat '{counter}' 2>/dev/null || printf 0)\n"
            f"printf '%s' $((n + 1)) > '{counter}'\n"
            "printf 'capture-%s\\n' \"$n\"\n",
        )
        before_output = (self.root / MODULE.OUTPUT_NAME).read_bytes()
        before_checksums = (self.root / MODULE.CHECKSUM_NAME).read_bytes()

        with self.assertRaises(MODULE.FixtureError) as raised:
            MODULE.regenerate_fixture(self.root, str(fake), require_canonical=False)
        self.assertEqual(raised.exception.error_class, "nondeterministic_output")
        self.assertEqual((self.root / MODULE.OUTPUT_NAME).read_bytes(), before_output)
        self.assertEqual((self.root / MODULE.CHECKSUM_NAME).read_bytes(), before_checksums)

    def test_failed_regeneration_leaves_prior_files_intact(self) -> None:
        fake = pathlib.Path(self.tmp.name) / "failing-rustc"
        exact_identity_script(fake, "printf 'capture failed\\n' >&2\nexit 7\n")
        before_output = (self.root / MODULE.OUTPUT_NAME).read_bytes()
        before_checksums = (self.root / MODULE.CHECKSUM_NAME).read_bytes()

        with self.assertRaises(MODULE.FixtureError) as raised:
            MODULE.regenerate_fixture(self.root, str(fake), require_canonical=False)
        self.assertEqual(raised.exception.error_class, "compiler_execution")
        self.assertEqual((self.root / MODULE.OUTPUT_NAME).read_bytes(), before_output)
        self.assertEqual((self.root / MODULE.CHECKSUM_NAME).read_bytes(), before_checksums)

    def test_missing_and_extra_files_fail_closed(self) -> None:
        (self.root / MODULE.OUTPUT_NAME).unlink()
        missing = self.run_checker("--verify", "--rustc", "/definitely/missing/rustc")
        self.assertNotEqual(missing.returncode, 0)
        self.assertEqual(json.loads(missing.stderr)["error_class"], "unexpected_file")

        shutil.copyfile(
            MODULE.CANONICAL_ROOT / MODULE.OUTPUT_NAME,
            self.root / MODULE.OUTPUT_NAME,
        )
        (self.root / "extra").write_text("x")
        extra = self.run_checker("--verify", "--rustc", "/definitely/missing/rustc")
        self.assertNotEqual(extra.returncode, 0)
        self.assertEqual(json.loads(extra.stderr)["error_class"], "unexpected_file")


if __name__ == "__main__":
    unittest.main()
