#!/usr/bin/env python3
"""Read an ADR-2131 sizing sweep back out of its kept captures.

Exit criterion 1. The sweep runs each file once with ``--trace`` through
``scripts/ledger-run-one.sh``, which keeps the FULL stdout; this reads the
verdict and the ``nra-real-root`` attempt out of those captures, so "did we
decide it" and "why not" come from ONE run rather than two.

Reading the attempt has a trap this script is built around, and ADR-2126's
scanner hit it first: an attempt that DECIDED carries no ``detail`` field at
all, so treating a missing field as "no attempt in the trail" reports the three
files where the route worked as absences.  The attempt's PRESENCE and its
OUTCOME are separate reads here, and a missing detail on a present attempt is
recorded as the outcome alone.

Controls, each of which makes the exit status depend on the finding:

* every capture named on the command line must exist and be non-empty;
* the capture count must equal the file-list count;
* every undecided file must yield a cause, and an unrecognised cause is an
  error rather than an "other" bucket.

Usage:
    size-report.py --captures DIR --list FILE [--arm single-cell]
                   [--out TSV] [--expect-files N]
"""

from __future__ import annotations

import argparse
import collections
import pathlib
import re
import sys

VERDICT_RE = re.compile(r"^(sat|unsat|unknown)$", re.MULTILINE)
ATTEMPT_RE = re.compile(r'\{"route":"nra-real-root"[^}]*\}')
OUTCOME_RE = re.compile(r'"outcome":"([^"]*)"')
DETAIL_RE = re.compile(r'"detail":"([^"]*)"')
# The trace detail is a SENTENCE -- `exact real-polynomial decider declined:
# <cause> (cad-arm=<arm>)`. The bare `CadDecline::name` key is what the cause
# table is keyed on, so it is extracted rather than the whole string; a detail
# this does not match is reported verbatim and fails the control.
CAUSE_RE = re.compile(r"declined: ([a-z0-9-]+) \(cad-arm=")
REASON_RE = re.compile(r'"reason":"([^"]*)"')
CLAUSE_RE = re.compile(r'"clause_detail":"([^"]*)"')

# Every cause `CadDecline::name` can print, plus the two non-decline outcomes.
# Derived from the authority (the enum) rather than from memory: a cause this
# list does not name is an ERROR, not an "other" row, because an "other" bucket
# is how a new cause hides.
KNOWN = {
    "not-attempted",
    "non-conjunctive",
    "deadline",
    "cell-budget",
    "critical-count-cap",
    "coefficient-range",
    "root-isolation",
    "root-ordering",
    "projection",
    "projection-sylvester-dim",
    "projection-resultant-zero",
    "projection-derivative",
    "projection-arithmetic",
    "nullified-residual",
    "algebraic-coarsening",
    "indeterminate-sign",
    "slice-bounds",
    "certificate-rejected",
    "algebraic-witness",
    "unsat-withheld-by-arm",
    "clause-loop-shape",
    "clause-loop-budget",
    "clause-loop-unsat-uncertified",
    "clause-loop-certificate-rejected",
    # Not `CadDecline` causes: these are what the ROUTE TRACE says when the rung
    # never got far enough to attribute one. Named rather than bucketed, because
    # they mean different things and both are real answers to "why not":
    #   `declined/not-applicable` -- the rung refused the query's SHAPE before any
    #       CAD work, so no cause was recorded (the slot is `not-attempted`);
    #   `ABSENT` -- there is no `nra-real-root` attempt in the trail at all, which
    #       on this population means the watchdog killed the run before the ladder
    #       reached the rung.
    "declined/not-applicable",
    "ABSENT",
}


def slug(rel: str) -> str:
    return rel.replace("/", "_")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--captures", required=True)
    ap.add_argument("--list", required=True)
    ap.add_argument("--arm", default="single-cell")
    ap.add_argument("--out")
    ap.add_argument("--expect-files", type=int)
    args = ap.parse_args()

    root = pathlib.Path(args.captures)
    rels = [ln.strip() for ln in pathlib.Path(args.list).read_text().splitlines()]
    rels = [r for r in rels if r]

    failures: list[str] = []
    if args.expect_files is not None and len(rels) != args.expect_files:
        failures.append(
            f"CONTROL: list has {len(rels)} files, expected {args.expect_files}"
        )

    rows = []
    for rel in rels:
        # The capture may live under any shard directory; find it by name.
        name = f"{args.arm}__{slug(rel)}.out"
        hits = sorted(root.glob(f"**/{name}"))
        if not hits:
            failures.append(f"CONTROL: no capture for {rel}")
            continue
        text = hits[0].read_text(errors="replace")
        if not text.strip():
            failures.append(f"CONTROL: empty capture for {rel}")
            continue
        m = VERDICT_RE.search(text)
        verdict = m.group(1) if m else "none"
        attempt = ATTEMPT_RE.search(text)
        if attempt is None:
            cause = "ABSENT"
        else:
            blob = attempt.group(0)
            om = OUTCOME_RE.search(blob)
            dm = DETAIL_RE.search(blob)
            outcome = om.group(1) if om else "unknown-outcome"
            if dm:
                cm2 = CAUSE_RE.search(dm.group(1))
                cause = cm2.group(1) if cm2 else dm.group(1)
            else:
                # No `detail` means no cause was attributed. Keep the trace's own
                # `reason` rather than collapsing to the bare outcome -- the two
                # carry different information and a bare "declined" row would be
                # a shrug where the trail actually said something.
                rm = REASON_RE.search(blob)
                cause = f"{outcome}/{rm.group(1)}" if rm else outcome
        cm = CLAUSE_RE.search(text)
        clause = cm.group(1) if cm else ""
        rows.append((rel, verdict, cause, clause))

    decided = [r for r in rows if r[1] in ("sat", "unsat")]
    undecided = [r for r in rows if r[1] not in ("sat", "unsat")]

    for rel, _v, cause, _c in undecided:
        if cause not in KNOWN:
            failures.append(f"CONTROL: unrecognised cause {cause!r} for {rel}")

    hist = collections.Counter(c for _r, _v, c, _cl in undecided)
    clause_hist = collections.Counter(
        cl for _r, _v, c, cl in undecided if c == "non-conjunctive" and cl
    )

    out = []
    out.append(f"== {args.captures}: {len(rows)} files, arm={args.arm} ==")
    out.append("")
    out.append(f"decided   {len(decided):>4}   (sat "
               f"{sum(1 for r in decided if r[1] == 'sat')}, unsat "
               f"{sum(1 for r in decided if r[1] == 'unsat')})")
    out.append(f"undecided {len(undecided):>4}")
    out.append("")
    out.append("files  nra-real-root cause (undecided only)")
    out.append("-----  ------------------------------------")
    for cause, n in hist.most_common():
        out.append(f"{n:>5}  {cause}")
    out.append("-----")
    out.append(f"{len(undecided):>5}  TOTAL")
    if clause_hist:
        out.append("")
        out.append("files  clause-loop detail on the non-conjunctive files")
        out.append("-----  ----------------------------------------------")
        for cause, n in clause_hist.most_common():
            out.append(f"{n:>5}  {cause}")

    if args.out:
        with open(args.out, "w") as fh:
            fh.write("file\tverdict\tnra_real_root_cause\tclause_loop_detail\n")
            for rel, verdict, cause, clause in rows:
                fh.write(f"{rel}\t{verdict}\t{cause}\t{clause}\n")

    print("\n".join(out))
    if failures:
        print("")
        print("CONTROLS FAILED")
        for f in failures:
            print(f"  {f}")
        return 1
    print("")
    print("CONTROLS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
