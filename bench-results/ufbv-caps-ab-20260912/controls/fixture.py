#!/usr/bin/env python3
"""Controls for `summarize.py`: prove each guard can fire, and that a clean
fixture produces NOTHING alarming.

A checker that cannot fail is worse than no checker, so every abort path gets a
fixture that must trigger it, AND one clean fixture that must not.

Run: python3 controls/fixture.py
"""

import pathlib
import shutil
import subprocess
import sys
import tempfile

HDR = "file\tarm\tverdict\trc\twall_ms\tattempts\tdecided_by\tbound_by\tbound_ms\ttotal_ms\tgiveup\tlever_refused"
HERE = pathlib.Path(__file__).resolve().parent
SUMMARIZE = HERE.parent / "summarize.py"


def row(f, arm, verdict, wall=100, giveup="none", refused="no"):
    return f"{f}\t{arm}\t{verdict}\t0\t{wall}\t3\tqf-bv\tqf-bv\t{wall}\t{wall}\t{giveup}\t{refused}"


def clean_rows():
    out = []
    for f in ("A.smt2", "B.smt2", "C.smt2"):
        for arm in ("base", "a4096"):
            v = "sat" if f != "C.smt2" else ("unknown" if arm == "base" else "unsat")
            out.append(row(f, arm, v))
    return out


def run(rows, extra=()):
    d = tempfile.mkdtemp(prefix="ufbvcaps-ctl-")
    try:
        (pathlib.Path(d) / "shard0.tsv").write_text(HDR + "\n" + "\n".join(rows) + "\n")
        p = subprocess.run(
            [sys.executable, str(SUMMARIZE), d, *extra],
            capture_output=True,
            text=True,
        )
        return p.returncode, p.stdout + p.stderr
    finally:
        shutil.rmtree(d)


CASES = []


def case(name, rows, extra=(), must_abort=True, must_say=None):
    CASES.append((name, rows, extra, must_abort, must_say))


case(
    "a clean fixture reports and does not abort",
    clean_rows(),
    must_abort=False,
    must_say="a4096: 1 gained",
)
case(
    "a refused lever aborts",
    [r.replace("\tno", "\tyes") if "a4096" in r else r for r in clean_rows()],
    must_say="lever REFUSE",
)
case(
    "a missing matrix cell aborts",
    clean_rows()[:-1],
    must_say="missing cells",
)
case(
    "a sat/unsat disagreement between arms aborts",
    [r.replace("\tsat\t", "\tunsat\t") if r.startswith("A.smt2\ta4096") else r for r in clean_rows()],
    must_say="DISAGREE",
)
case(
    "a duplicate row aborts",
    clean_rows() + [row("A.smt2", "base", "sat")],
    must_say="duplicate row",
)
case(
    "a wrong file count aborts",
    clean_rows(),
    extra=("--expect-files", "200"),
    must_say="expected 200",
)
case(
    "a missing arm aborts",
    clean_rows(),
    extra=("--expect-arms", "base,a4096,n65536"),
    must_say="!= expected",
)
case(
    "an empty directory aborts",
    [],
    must_say="no rows",
)
case(
    "a fixture with NO baseline arm aborts",
    [r for r in clean_rows() if "\tbase\t" not in r],
    must_say="no `base` arm",
)


def main():
    failures = 0
    for name, rows, extra, must_abort, must_say in CASES:
        rc, out = run(rows, extra)
        aborted = rc != 0
        ok = aborted == must_abort and (must_say is None or must_say in out)
        print(f"{'PASS' if ok else 'FAIL'}  {name}")
        if not ok:
            failures += 1
            print(f"      rc={rc} must_abort={must_abort} looking for {must_say!r}")
            print("      " + out.replace("\n", "\n      ")[:900])
    print(f"\n{len(CASES) - failures} of {len(CASES)} controls passed")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
