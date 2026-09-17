#!/usr/bin/env python3
"""The second reading of a cindergraph-defects sweep: does the evidence say PASS?

`python/examples/cindergraph_defects/check.py` lifts twelve C samples through
cindergraph into QF_BV, has the native solver find a witness per sink, and
replays each witness under a sanitizer. It exits 1 on its own failures — but a
driver's exit status is one reading of one process, and the rule this
repository keeps (CLAUDE.md, "Evidence, checkers, and blind populations") is
that a gate re-derives its finding from the artifact the subject wrote, so
that a driver which stopped counting, or started saying yes, is caught by a
reader that did not change with it.

So this script never runs the sweep. `scripts/check-cindergraph-defects.sh`
runs it and hands over three things: the driver's stdout (its provenance
header, its replay-control line and its `CINDERGRAPH_DEFECTS_RUN|...` counts),
the `results.tsv` it wrote, and the samples directory. From those it asserts,
each as its own failure CLASS so a mutation kills exactly the test that watches
it (`scripts/tests/test_check_cindergraph_defects.py`):

  expectation   every function cindergraph exported has a `// expect:` line in
                its sample, every such line is met, and the per-verdict counts
                (clean / finding / bounded / refused) equal the counts of those
                lines — derived from the samples, never from a literal here.
  replay        no `DID NOT REPLAY` row; every replayed row's report names the
                line it fired at, and it is the row's own line.
  control       the driver's control — the first replayed harness judged at the
                line AFTER its finding — came back `refused`.
  provenance    the cindergraph that ran is the commit `pyproject.toml` pins.
  inconsistent  the driver's own counts, or its exit status, disagree with what
                this reader derived from the table.

Exit status depends on the finding. The one summary line:

  CINDERGRAPH_DEFECTS|rows=N|replayed=N|dead=N|clean=N|bounded=N|no_oracle=N|failures=N|PASS

`failures` is the number of failure lines printed above it, so a reader who
sees `PASS` with `failures=0` and a reader who counts the `FAIL|` lines agree.
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import Counter
from pathlib import Path

RUN_LINE = "CINDERGRAPH_DEFECTS_RUN"
CONTROL_LINE = "CINDERGRAPH_DEFECTS_REPLAY_CONTROL"
FAIL = "CINDERGRAPH_DEFECTS_FAIL"
CLASSES = ("expectation", "replay", "control", "provenance", "inconsistent")
VERDICTS = ("finding", "clean", "refused", "bounded")
_EXPECT_RE = re.compile(r"//\s*expect:\s*(\w+)\s+(finding|clean|refused|bounded)")
_LINE_RE = re.compile(r"\(line (\d+)\)\s*$")
# Row kinds that are not a witness: the function's verdict, or a proof.
NOT_A_WITNESS = {"clean", "dead-branch", "bounded", "refused", "parse-error", "EXPECTATION-FAILED"}


def expectations(samples: Path) -> dict[str, str]:
    """``{function: verdict}`` from every ``// expect:`` line under ``samples``."""
    out: dict[str, str] = {}
    for sample in sorted(samples.rglob("*.c")):
        for m in _EXPECT_RE.finditer(sample.read_text(errors="replace")):
            out[m.group(1)] = m.group(2)
    return out


def read_rows(tsv: Path) -> list[tuple[str, ...]]:
    return [tuple(line.split("\t")) for line in tsv.read_text().splitlines() if line.strip()]


def fields(line: str) -> dict[str, str]:
    """``k=v`` pairs of a ``NAME|k=v|k=v`` line."""
    out: dict[str, str] = {}
    for part in line.split("|")[1:]:
        key, sep, value = part.partition("=")
        if sep:
            out[key] = value
    return out


def evaluate(
    rows: list[tuple[str, ...]], expect: dict[str, str], stdout: str, driver_status: int
) -> tuple[list[tuple[str, str]], dict[str, int]]:
    """``(failures, counts)``: every failure as ``(class, detail)``, and the summary counts."""
    failures: list[tuple[str, str]] = []
    counts = Counter(row[2] for row in rows if len(row) > 2)
    witnesses = [row for row in rows if len(row) > 5 and row[2] not in NOT_A_WITNESS]
    replayed = [row for row in witnesses if row[5].startswith("REPLAYED: ")]
    no_oracle = [row for row in witnesses if row[5].startswith("NO RUNTIME ORACLE: ")]

    # -- expectation ------------------------------------------------------
    seen: dict[str, set[str]] = {}
    for row in rows:
        if len(row) < 3 or row[1] == "-":
            continue
        seen.setdefault(row[1], set()).add(row[2])
    for function, kinds in sorted(seen.items()):
        if function not in expect:
            failures.append(("expectation", f"{function} has no `// expect:` line in its sample"))
        if "EXPECTATION-FAILED" in kinds:
            failures.append(("expectation", f"{function}: expected {expect.get(function)}"))
        if "refused" in kinds and expect.get(function) != "refused":
            failures.append(("expectation", f"{function} was refused"))
        if "parse-error" in kinds:
            failures.append(("expectation", f"{function}: cindergraph could not parse the file"))
    for function in sorted(set(expect) - set(seen)):
        failures.append(("expectation", f"{function} has an `// expect:` line but no row"))
    # Verdict counts, derived from the samples: a function is `clean` when its
    # only row is a clean row, `finding` when it has a witness or a dead
    # branch, `bounded` when it has a bounded row and no witness.
    derived = Counter()
    for function, kinds in seen.items():
        if kinds & {"refused", "parse-error"}:
            derived["refused"] += 1
        elif kinds - NOT_A_WITNESS or "dead-branch" in kinds:
            derived["finding"] += 1
        elif "bounded" in kinds:
            derived["bounded"] += 1
        elif "clean" in kinds:
            derived["clean"] += 1
    expected = Counter(expect.values())
    for verdict in VERDICTS:
        if derived[verdict] != expected[verdict]:
            detail = (
                f"{verdict}: {derived[verdict]} function(s) in the table, "
                f"{expected[verdict]} `// expect:` line(s)"
            )
            failures.append(("expectation", detail))

    # -- replay -------------------------------------------------------------
    for row in witnesses:
        where = row[3]
        report = row[5]
        if report.startswith("DID NOT REPLAY"):
            failures.append(("replay", f"{row[0]} {row[1]} {row[2]} {where}: {report[:120]}"))
            continue
        if report.startswith("REPLAYED: "):
            m = _LINE_RE.search(report)
            if m is None:
                failures.append(
                    ("replay", f"{row[0]} {row[1]} {where}: replay names no line: {report[:100]}")
                )
            elif f"line {m.group(1)}" != where:
                failures.append(
                    ("replay", f"{row[0]} {row[1]} {where}: replayed at line {m.group(1)}")
                )
        elif not report.startswith("NO RUNTIME ORACLE: "):
            failures.append(
                ("replay", f"{row[0]} {row[1]} {where}: unreadable status {report[:80]}")
            )

    # -- control ----------------------------------------------------------
    control = [line for line in stdout.splitlines() if line.startswith(CONTROL_LINE + "|")]
    if len(control) != 1:
        failures.append(("control", f"{len(control)} replay-control line(s) in the driver output"))
    else:
        parts = control[0].split("|")
        verdict = parts[3] if len(parts) > 3 else "?"
        if verdict != "refused":
            failures.append(
                ("control", f"the wrong-line replay control was {verdict}: {control[0]}")
            )

    # -- provenance ---------------------------------------------------------
    header = [line for line in stdout.splitlines() if line.startswith("cindergraph|")]
    if len(header) != 1:
        failures.append(("provenance", f"{len(header)} cindergraph header line(s)"))
    else:
        h = fields(header[0])
        commit, pinned = h.get("commit", "unknown"), h.get("pinned", "unknown")
        if commit == "unknown" or pinned == "unknown" or commit != pinned:
            failures.append(("provenance", f"ran cindergraph {commit}, pyproject pins {pinned}"))

    # -- inconsistent ------------------------------------------------------
    summary = {
        "rows": len(rows),
        "replayed": len(replayed),
        "dead": counts["dead-branch"],
        "clean": counts["clean"],
        "bounded": counts["bounded"],
        "no_oracle": len(no_oracle),
    }
    run = [line for line in stdout.splitlines() if line.startswith(RUN_LINE + "|")]
    if len(run) != 1:
        failures.append(("inconsistent", f"{len(run)} {RUN_LINE} line(s) in the driver output"))
    else:
        theirs = fields(run[0])
        for key, mine in summary.items():
            if theirs.get(key) != str(mine):
                failures.append(
                    (
                        "inconsistent",
                        f"{key}: the driver says {theirs.get(key)}, the table says {mine}",
                    )
                )
        driver_failures = theirs.get("failures", "?")
        if driver_failures != "0" and driver_status == 0:
            failures.append(("inconsistent", f"driver exit 0 with failures={driver_failures}"))
        if driver_failures == "0" and driver_status != 0:
            failures.append(("inconsistent", f"driver exit {driver_status} with failures=0"))
    if not rows:
        failures.append(("inconsistent", "the table is empty"))
    return failures, summary


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    ap.add_argument("--results", type=Path, required=True, help="the driver's results.tsv")
    ap.add_argument("--stdout", type=Path, required=True, help="the driver's captured stdout")
    ap.add_argument("--samples", type=Path, required=True, help="the samples directory")
    ap.add_argument("--driver-status", type=int, required=True, help="the driver's exit status")
    args = ap.parse_args()
    if not args.results.exists():
        print(f"{FAIL}|inconsistent|no results.tsv at {args.results}")
        print(
            "CINDERGRAPH_DEFECTS|rows=0|replayed=0|dead=0|clean=0|bounded=0|no_oracle=0|failures=1|FAIL"
        )
        return 1
    rows = read_rows(args.results)
    expect = expectations(args.samples)
    stdout = args.stdout.read_text() if args.stdout.exists() else ""
    failures, summary = evaluate(rows, expect, stdout, args.driver_status)
    for cls, detail in failures:
        print(f"{FAIL}|{cls}|{detail}")
    verdict = "PASS" if not failures else "FAIL"
    print(
        "CINDERGRAPH_DEFECTS|"
        + "|".join(f"{k}={v}" for k, v in summary.items())
        + f"|failures={len(failures)}|{verdict}"
    )
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
