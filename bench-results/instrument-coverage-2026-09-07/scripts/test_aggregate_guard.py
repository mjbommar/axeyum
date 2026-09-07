#!/usr/bin/env python3
"""Regression test for `aggregate.py`'s non-additivity guard.

Per CLAUDE.md's evidence-and-checker-discipline rule ("when you attach
evidence, make the exit status depend on the finding; when you touch a
checker, delete one guard and require that exactly one test dies"): this
constructs one synthetic TSV+log fixture that must PASS the guard (traced_ms
well under wall_ms) and one that must FAIL it (a `; bv-layer …` line whose
`total_ms` alone exceeds the file's own wall_ms — the exact shape of the
QF_UF `theory_assert_ms` double-count bug `bench-divisions-2026-09-07`
found, reproduced here for `bv-layer` so the guard this lane added is
mutation-checked rather than merely written).

Run: `python3 bench-results/instrument-coverage-2026-09-07/scripts/test_aggregate_guard.py`
Exits 0 if both cases behave as expected, 1 otherwise (with a message naming
which case failed).
"""
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
AGGREGATE = SCRIPT_DIR / "aggregate.py"


def write_case(tmp: Path, name: str, wall_ms: int, log_lines: list[str]) -> Path:
    log_path = tmp / f"{name}.log"
    log_path.write_text("\n".join(log_lines) + "\n", encoding="utf-8")
    tsv_path = tmp / f"{name}.tsv"
    tsv_path.write_text(
        "division\tfile\twall_ms\tverdict\tlog_path\n"
        f"TEST_DIV\t{name}.smt2\t{wall_ms}\tunsolved\t{log_path}\n",
        encoding="utf-8",
    )
    return tsv_path


def run_aggregate(tsv_path: Path) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, str(AGGREGATE), str(tsv_path)],
        capture_output=True,
        text=True,
        check=False,
    )


def main() -> int:
    failures = []
    with tempfile.TemporaryDirectory() as tmp_str:
        tmp = Path(tmp_str)

        # Case 1: honest, non-overlapping traced time well under wall_ms.
        # Must PASS (exit 0).
        pass_tsv = write_case(
            tmp,
            "honest",
            wall_ms=24000,
            log_lines=[
                "; front-door parse_ms=50",
                "; dl-online total_ms=10",
                "; bv-layer bit_blast_ms=100 cnf_encode_ms=200 cnf_inprocess_ms=0 "
                "solve_ms=5000 model_lift_ms=1 model_replay_ms=1 total_ms=5302 "
                "bit_demand_analysis_nested_in_bit_blast_ms=0 "
                "range_demand_admission_nested_in_bit_blast_ms=0 aig_nodes=1 "
                "cnf_variables=1 cnf_clauses=1",
                "unknown",
            ],
        )
        result = run_aggregate(pass_tsv)
        if result.returncode != 0:
            failures.append(
                f"Case 1 (honest, should PASS) exited {result.returncode}, "
                f"expected 0. stderr={result.stderr!r}"
            )

        # Case 2: a `bv-layer` line whose own `total_ms` alone exceeds
        # wall_ms -- the double-counting/impossible-sum shape the guard
        # exists to catch. Must FAIL (exit 1, and name the violation).
        fail_tsv = write_case(
            tmp,
            "impossible",
            wall_ms=1000,
            log_lines=[
                "; front-door parse_ms=5",
                "; dl-online total_ms=0",
                "; bv-layer bit_blast_ms=100 cnf_encode_ms=200 cnf_inprocess_ms=0 "
                "solve_ms=5000 model_lift_ms=1 model_replay_ms=1 total_ms=5302 "
                "bit_demand_analysis_nested_in_bit_blast_ms=0 "
                "range_demand_admission_nested_in_bit_blast_ms=0 aig_nodes=1 "
                "cnf_variables=1 cnf_clauses=1",
                "unknown",
            ],
        )
        result = run_aggregate(fail_tsv)
        if result.returncode != 1:
            failures.append(
                f"Case 2 (impossible sum, should FAIL) exited {result.returncode}, "
                f"expected 1. stdout={result.stdout!r} stderr={result.stderr!r}"
            )
        elif "NON-ADDITIVITY GUARD FAILED" not in result.stderr:
            failures.append(
                "Case 2 exited 1 but did not print the expected guard-failure "
                f"message. stderr={result.stderr!r}"
            )

    if failures:
        print("FAILED:", file=sys.stderr)
        for f in failures:
            print(f"  - {f}", file=sys.stderr)
        return 1
    print("OK: both cases behaved as expected (guard fires only on the impossible sum).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
