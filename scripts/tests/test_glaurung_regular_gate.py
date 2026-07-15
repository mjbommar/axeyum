import json
import os
import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


ROOT = Path(__file__).parents[2]
SCRIPT = ROOT / "scripts" / "check-glaurung-qfbv-regular.sh"


class GlaurungRegularGateTests(unittest.TestCase):
    def run_gate(self, env: dict[str, str]) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [str(SCRIPT)],
            cwd=ROOT,
            env=env,
            check=False,
            capture_output=True,
            text=True,
        )

    def test_unavailable_data_skips_without_invoking_cargo(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            temp = Path(temporary)
            cargo = temp / "cargo"
            cargo.write_text("#!/bin/sh\nexit 99\n", encoding="utf-8")
            cargo.chmod(0o755)
            env = os.environ.copy()
            env.update(
                {
                    "AXEYUM_GLAURUNG_QFBV_AUTO_DISCOVER": "0",
                    "PATH": f"{temp}:{env['PATH']}",
                }
            )
            env.pop("AXEYUM_GLAURUNG_QFBV_REPRESENTATIVE_DIR", None)
            env.pop("AXEYUM_GLAURUNG_QFBV_REPRESENTATIVE_MANIFEST", None)

            completed = self.run_gate(env)

        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn("SKIP access-controlled representative corpus unavailable", completed.stdout)

    def test_explicit_missing_data_fails_closed(self) -> None:
        env = os.environ.copy()
        env["AXEYUM_GLAURUNG_QFBV_REPRESENTATIVE_DIR"] = "/definitely/missing/glaurung"

        completed = self.run_gate(env)

        self.assertEqual(completed.returncode, 2)
        self.assertIn("configured corpus directory does not exist", completed.stderr)

    def test_real_path_runs_raw_and_canonical_with_all_semantic_gates(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            temp = Path(temporary)
            corpus = temp / "corpus"
            corpus.mkdir()
            manifest = corpus / "manifest-v1.json"
            manifest.write_text("{}\n", encoding="utf-8")
            out_dir = temp / "out"
            log = temp / "cargo-args.jsonl"
            bin_dir = temp / "bin"
            bin_dir.mkdir()
            cargo = bin_dir / "cargo"
            cargo.write_text(
                textwrap.dedent(
                    """\
                    #!/usr/bin/env python3
                    import json
                    import os
                    import sys

                    args = sys.argv[1:]
                    with open(os.environ["FAKE_CARGO_LOG"], "a", encoding="utf-8") as handle:
                        handle.write(json.dumps(args) + "\\n")
                    out = args[args.index("--out") + 1]
                    files = 128
                    artifact = {
                        "version": 31,
                        "summary": {
                            "files": files,
                            "decided": files,
                            "errors": 0,
                            "disagree": 0,
                            "model_replay_failures": 0,
                            "manifest": {
                                "compared": files,
                                "agree": files,
                                "disagree": 0,
                            },
                            "oracle": {
                                "compared": files,
                                "agree": files,
                                "disagree": 0,
                                "skipped": 0,
                            },
                            "client_comparison": {
                                "axeyum_total_s": 0.2,
                                "z3_total_s": 0.1,
                                "axeyum_over_z3_ratio": 2.0,
                            },
                            "layer_attribution": {
                                "word_preprocess_s": 0.01,
                                "bit_blast_s": 0.06,
                                "cnf_encode_s": 0.07,
                                "solve_s": 0.05,
                            },
                        },
                    }
                    with open(out, "w", encoding="utf-8") as handle:
                        json.dump(artifact, handle)
                    """
                ),
                encoding="utf-8",
            )
            cargo.chmod(0o755)
            env = os.environ.copy()
            env.update(
                {
                    "AXEYUM_GLAURUNG_QFBV_REPRESENTATIVE_DIR": str(corpus),
                    "AXEYUM_GLAURUNG_QFBV_REGRESSION_OUT_DIR": str(out_dir),
                    "AXEYUM_GLAURUNG_QFBV_MEMORY_GB": "1",
                    "FAKE_CARGO_LOG": str(log),
                    "PATH": f"{bin_dir}:{env['PATH']}",
                }
            )

            completed = self.run_gate(env)
            invocations = [json.loads(line) for line in log.read_text().splitlines()]

        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(len(invocations), 2)
        combined = "\n".join(" ".join(args) for args in invocations)
        self.assertIn("--rewrite off", combined)
        self.assertIn("--rewrite default", combined)
        self.assertEqual(combined.count("--corpus-tier representative"), 2)
        self.assertEqual(combined.count("--compare-z3"), 2)
        self.assertEqual(combined.count("--require-in-process-z3"), 2)
        self.assertEqual(combined.count("--require-deterministic-resources"), 2)
        self.assertEqual(combined.count("--min-decided-percent 100"), 2)
        self.assertNotIn("--require-reproducible-run", combined)
        self.assertIn("PASS policy=raw files=128", completed.stdout)
        self.assertIn("PASS policy=canonical files=128", completed.stdout)


if __name__ == "__main__":
    unittest.main()
