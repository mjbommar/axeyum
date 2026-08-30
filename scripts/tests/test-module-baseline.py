#!/usr/bin/env python3
"""Self-contained test suite for scripts/lib/module_baseline.py,
scripts/gen-module-baseline.py, scripts/check-module-baseline.py (L1 phase
G0 -- see docs/plan/status/l1-g0-module-baseline.md).

Builds a small synthetic Mathlib-shaped fixture (never touches the shared
mathlib4 checkout) and asserts one property per guard in the parser and the
drift checker. Every test here corresponds to exactly one guard, deliberately,
so `scripts/tests/test-module-baseline-mutations.sh` can delete that guard and
require exactly this test to die.

Usage:
    python3 scripts/tests/test-module-baseline.py
    python3 scripts/tests/test-module-baseline.py \\
        --lib /path/to/mutated/module_baseline.py \\
        --gen /path/to/mutated/gen-module-baseline.py \\
        --check /path/to/mutated/check-module-baseline.py

Prints one `TEST|name=...|verdict=PASS|FAIL` line per test and a final
`TEST_SUMMARY|total=N|passed=N|failed=[...]` line. Exit 0 iff every test
passed.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO_SCRIPTS = HERE.parent


def import_module_baseline(lib_path: Path):
    spec = importlib.util.spec_from_file_location("module_baseline_under_test", lib_path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)  # type: ignore[union-attr]
    return mod


def write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def build_fixture(root: Path) -> None:
    """A fourteen-module synthetic corpus under root/Mathlib/Fix/*.lean.

    Each guard gets its OWN modules so mutating one guard cannot ripple into
    another guard's test (an earlier version reused AAA/BBB for both the
    decoy-stripping check and the tie-break check, and a single mutation
    killed two tests at once -- exactly the "one guard wearing two names"
    shape this suite exists to rule out).

    Deliberately exercises: decoy import-looking text inside a block comment,
    a line comment, and a string literal, all targeting `DecoyTarget` (so a
    parser that fails to strip them inflates ONLY that module's indegree);
    one edge to a target outside the fixture (external, via `AAA`); several
    no-importer sinks; and a three-way indegree-2 tie (`TieA` / `TieB` /
    `TieC`) constructed so file-processing order and lexicographic order
    DISAGREE, discriminating the sort-order tie-break.
    """
    m = root / "Mathlib" / "Fix"
    write(m / "AAA.lean", "module\n")
    write(m / "BBB.lean", "module\n")
    write(m / "DecoyTarget.lean", "module\n")
    write(
        m / "CDecoyImports.lean",
        # Two decoys land at LINE START inside a block comment -- the exact
        # shape that makes a naive line-oriented parser miscount (real
        # Mathlib module docs do this, e.g. Mathlib/Tactic/MinImports.lean's
        # illustrative "import A" / "import B" lines). A "--" line comment or
        # a string literal can never put the word `import` at column 0 of a
        # physical line, so they cannot trigger this specific regex-anchoring
        # hazard regardless of stripping; they are kept here only as
        # realistic corpus noise, not as discriminating cases.
        "/-! decoy doc comment, must not be counted:\n"
        "import Mathlib.Fix.DecoyTarget\n"
        "import Mathlib.Fix.DecoyTarget\n"
        "-/\n"
        "-- also decoy (never matches, comment/code, not line-start): import Mathlib.Fix.DecoyTarget\n"
        '#eval "not an import either: import Mathlib.Fix.DecoyTarget"\n'
        "public import Mathlib.Fix.DecoyTarget\n",
    )
    write(
        m / "DExternal.lean",
        "public import Mathlib.Fix.AAA\npublic meta import Lean.Elab.Command\n",
    )
    write(m / "ESink1.lean", "module\n")
    write(m / "FSink2.lean", "module\n")
    write(m / "TieA.lean", "module\n")
    write(m / "TieB.lean", "module\n")
    write(m / "TieC.lean", "module\n")
    write(m / "G1Importer.lean", "public import Mathlib.Fix.TieC\n")
    write(m / "G2Importer.lean", "public import Mathlib.Fix.TieB\n")
    write(m / "G3Importer.lean", "public import Mathlib.Fix.TieC\n")
    write(m / "G4Importer.lean", "public import Mathlib.Fix.TieB\n")
    write(m / "G5Importer.lean", "public import Mathlib.Fix.TieA\n")
    write(m / "G6Importer.lean", "public import Mathlib.Fix.TieA\n")


RESULTS: list[tuple[str, bool, str]] = []


def check(name: str, condition: bool, detail: str = "") -> None:
    RESULTS.append((name, condition, detail))


def run_lib_tests(mb) -> None:
    with tempfile.TemporaryDirectory(prefix="module-baseline-fixture-") as tmp:
        root = Path(tmp)
        build_fixture(root)
        receipt = mb.build_receipt(root, commit_override="FIXTURE0000")

        # G1: comment/string decoys must not be counted as edges. DecoyTarget
        # is really imported exactly once (one `public import` in
        # CDecoyImports); the same file also mentions it inside a block
        # comment, a line comment, and a string literal. If comment/string
        # stripping is skipped, those three decoys inflate the count to 4.
        # DecoyTarget is used NOWHERE else in the fixture, so this mutation
        # cannot ripple into the sink or tie-break assertions below.
        indeg = {row["module"]: row["indegree"] for row in receipt["top_indegree"]}
        check(
            "comment_and_string_decoys_not_counted",
            indeg.get("Mathlib.Fix.DecoyTarget") == 1,
            f"got DecoyTarget={indeg.get('Mathlib.Fix.DecoyTarget')}",
        )

        # G2: an import naming a target outside the fixture module set is
        # external, not internal.
        check(
            "external_target_not_counted_internal",
            receipt["totals"]["external_edges"] == 1
            and all(row["module"] != "Lean.Elab.Command" for row in receipt["top_indegree"]),
            f"external_edges={receipt['totals']['external_edges']}",
        )

        # G3: sink count. Only AAA, DecoyTarget, TieA, TieB, TieC have
        # indegree > 0 among the 16 fixture modules, so 11 are no-importer
        # sinks (BBB included -- nothing imports it in this fixture).
        check(
            "sink_count_is_no_importer_modules",
            receipt["totals"]["no_importer_sink_count"] == 11,
            f"got {receipt['totals']['no_importer_sink_count']}",
        )

        # G4: tie-break order. TieA, TieB, TieC all have indegree 2. TieC's
        # first edge (G1Importer) is processed before TieB's first edge
        # (G2Importer), which is processed before TieA's first edge
        # (G5Importer) -- so an order that drops the lexicographic tie-break
        # emits TieC, TieB, TieA (file-processing order); the correct order is
        # alphabetical: TieA, TieB, TieC.
        names_at_2 = [row["module"] for row in receipt["top_indegree"] if row["indegree"] == 2]
        check(
            "tie_break_is_lexicographic_not_insertion_order",
            names_at_2 == ["Mathlib.Fix.TieA", "Mathlib.Fix.TieB", "Mathlib.Fix.TieC"],
            f"got {names_at_2}",
        )

        # G5a: missing directory entirely. Distinguished from G5b by MESSAGE
        # CONTENT, not just exception type -- both raise SourceUnreachable, so
        # a test that only checks the exception type cannot tell "the guard
        # for this exact case was removed" from "the OTHER guard caught it
        # anyway", since `(missing_dir / "Mathlib").is_dir()` is also False
        # for a directory that does not exist at all. Removing the dedicated
        # top-level-existence guard degrades the message people actually read
        # ("no Mathlib/ subdirectory" would be misleading when the whole
        # directory is absent), which is exactly the kind of loss this
        # project treats as real.
        missing = root / "does-not-exist"
        try:
            mb.build_receipt(missing)
            check("absence_missing_directory", False, "did not raise")
        except mb.SourceUnreachable as e:
            check(
                "absence_missing_directory",
                "does not exist" in str(e),
                f"wrong message: {e}",
            )
        except Exception as e:  # noqa: BLE001
            check("absence_missing_directory", False, f"wrong exception {type(e)}: {e}")

        # G5b: directory exists but has no Mathlib/ subdirectory.
        no_mathlib = root / "no-mathlib-here"
        (no_mathlib).mkdir()
        (no_mathlib / "README.md").write_text("nothing here\n")
        try:
            mb.build_receipt(no_mathlib)
            check("absence_no_mathlib_subdir", False, "did not raise")
        except mb.SourceUnreachable:
            check("absence_no_mathlib_subdir", True)
        except Exception as e:  # noqa: BLE001
            check("absence_no_mathlib_subdir", False, f"wrong exception {type(e)}: {e}")

        # G5c: Mathlib/ subdirectory exists but is empty (zero .lean files).
        empty_root = root / "empty-mathlib"
        (empty_root / "Mathlib").mkdir(parents=True)
        try:
            mb.build_receipt(empty_root)
            check("absence_zero_modules_parsed", False, "did not raise")
        except mb.EmptySource:
            check("absence_zero_modules_parsed", True)
        except Exception as e:  # noqa: BLE001
            check("absence_zero_modules_parsed", False, f"wrong exception {type(e)}: {e}")

        # Reproducibility sanity: two in-process builds are byte-identical.
        receipt_2 = mb.build_receipt(root, commit_override="FIXTURE0000")
        check(
            "two_runs_byte_identical",
            mb.receipt_to_json(receipt) == mb.receipt_to_json(receipt_2),
        )


def run_cli_drift_tests(gen_path: Path, check_path: Path) -> None:
    with tempfile.TemporaryDirectory(prefix="module-baseline-cli-") as tmp:
        root = Path(tmp)
        fixture_v1 = root / "fixture_v1"
        build_fixture(fixture_v1)

        receipt_path = root / "committed.json"
        r = subprocess.run(
            [
                sys.executable,
                str(gen_path),
                "--mathlib-dir",
                str(fixture_v1),
                "--out",
                str(receipt_path),
                "--commit",
                "FIXTUREAAA",
            ],
            capture_output=True,
            text=True,
        )
        check("cli_gen_succeeds_on_fixture", r.returncode == 0, r.stderr)

        # Baseline: check against the unchanged fixture must pass.
        r = subprocess.run(
            [
                sys.executable,
                str(check_path),
                "--mathlib-dir",
                str(fixture_v1),
                "--receipt",
                str(receipt_path),
                "--commit",
                "FIXTUREAAA",
            ],
            capture_output=True,
            text=True,
        )
        check("cli_check_passes_on_unchanged_fixture", r.returncode == 0, r.stderr)

        # SOURCE DRIFT: change the source content (add a new file), keep the
        # SAME claimed commit -- this is exactly the dangerous case (a
        # checkout mutated without updating its recorded identity). Must fail
        # naming SOURCE_DRIFT and must NOT name PARSER_DRIFT.
        fixture_v2 = root / "fixture_v2"
        build_fixture(fixture_v2)
        write(fixture_v2 / "Mathlib" / "Fix" / "NewModule.lean", "module\npublic import Mathlib.Fix.AAA\n")
        r = subprocess.run(
            [
                sys.executable,
                str(check_path),
                "--mathlib-dir",
                str(fixture_v2),
                "--receipt",
                str(receipt_path),
                "--commit",
                "FIXTUREAAA",
            ],
            capture_output=True,
            text=True,
        )
        check(
            "source_drift_detected_independently",
            r.returncode != 0 and "SOURCE_DRIFT" in r.stderr and "PARSER_DRIFT" not in r.stderr,
            f"rc={r.returncode} stderr={r.stderr!r}",
        )

        # PARSER DRIFT: same fixture, same commit, but a parser whose source
        # text differs (behaviour-preserving change: an appended comment) so
        # only its sha256 changes. Must fail naming PARSER_DRIFT and must NOT
        # name SOURCE_DRIFT.
        mutated_scripts = root / "mutated_parser"
        lib_dir = mutated_scripts / "lib"
        lib_dir.mkdir(parents=True)
        original_lib = (REPO_SCRIPTS / "lib" / "module_baseline.py").read_text(encoding="utf-8")
        (lib_dir / "module_baseline.py").write_text(
            original_lib + "\n# harmless parser-identity-changing comment\n", encoding="utf-8"
        )
        mutated_check = mutated_scripts / "check-module-baseline.py"
        mutated_check.write_text(check_path.read_text(encoding="utf-8"), encoding="utf-8")
        r = subprocess.run(
            [
                sys.executable,
                str(mutated_check),
                "--mathlib-dir",
                str(fixture_v1),
                "--receipt",
                str(receipt_path),
                "--commit",
                "FIXTUREAAA",
            ],
            capture_output=True,
            text=True,
        )
        check(
            "parser_drift_detected_independently",
            r.returncode != 0 and "PARSER_DRIFT" in r.stderr and "SOURCE_DRIFT" not in r.stderr,
            f"rc={r.returncode} stderr={r.stderr!r}",
        )


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lib", default=str(REPO_SCRIPTS / "lib" / "module_baseline.py"))
    parser.add_argument("--gen", default=str(REPO_SCRIPTS / "gen-module-baseline.py"))
    parser.add_argument("--check", default=str(REPO_SCRIPTS / "check-module-baseline.py"))
    args = parser.parse_args(argv)

    try:
        mb = import_module_baseline(Path(args.lib))
        run_lib_tests(mb)
    except Exception as e:  # noqa: BLE001
        print(f"TEST_SUITE_DID_NOT_BUILD|error={type(e).__name__}: {e}", file=sys.stderr)
        return 2

    try:
        run_cli_drift_tests(Path(args.gen), Path(args.check))
    except Exception as e:  # noqa: BLE001
        print(f"TEST_SUITE_DID_NOT_BUILD|error={type(e).__name__}: {e}", file=sys.stderr)
        return 2

    failed = []
    for name, ok, detail in RESULTS:
        verdict = "PASS" if ok else "FAIL"
        suffix = f"|detail={detail}" if (detail and not ok) else ""
        print(f"TEST|name={name}|verdict={verdict}{suffix}")
        if not ok:
            failed.append(name)

    print(f"TEST_SUMMARY|total={len(RESULTS)}|passed={len(RESULTS) - len(failed)}|failed={failed}")
    return 0 if not failed else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
