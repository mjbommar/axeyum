#!/usr/bin/env python3
"""Derive every number in the QF_UFBV cap A/B from the shard TSVs.

Nothing here is transcribed. The script ABORTS rather than reporting on:

  * any row whose `lever_refused` is `yes` -- the lever panicked on a malformed
    value and the CLI turned that into `unknown`, which reads exactly like "the
    raised cap did not help";
  * an incomplete arm/file matrix -- a smaller denominator is a different
    experiment, not a partial one;
  * a SOUNDNESS disagreement between two arms (one says sat, the other unsat).

Usage: summarize.py <out-dir> [--expect-files N] [--expect-arms a,b,c]
"""

import sys
import pathlib
import collections

DECIDED = {"sat", "unsat"}


def load(outdir):
    rows = []
    for p in sorted(pathlib.Path(outdir).glob("shard*.tsv")):
        with open(p) as fh:
            header = fh.readline().rstrip("\n").split("\t")
            for line in fh:
                parts = line.rstrip("\n").split("\t")
                if len(parts) != len(header):
                    continue
                rows.append(dict(zip(header, parts)))
    return rows


def main():
    outdir = sys.argv[1]
    expect_files = None
    expect_arms = None
    args = sys.argv[2:]
    for i, a in enumerate(args):
        if a == "--expect-files":
            expect_files = int(args[i + 1])
        if a == "--expect-arms":
            expect_arms = args[i + 1].split(",")

    rows = load(outdir)
    if not rows:
        print(f"ABORT: no rows under {outdir}")
        return 2

    refused = [r for r in rows if r["lever_refused"] == "yes"]
    if refused:
        print(f"ABORT: {len(refused)} row(s) had the lever REFUSE its value.")
        for r in refused[:5]:
            print("   ", r["file"], r["arm"])
        return 2

    arms = sorted({r["arm"] for r in rows})
    files = sorted({r["file"] for r in rows})
    if expect_arms and sorted(expect_arms) != arms:
        print(f"ABORT: arms {arms} != expected {sorted(expect_arms)}")
        return 2
    if expect_files is not None and len(files) != expect_files:
        print(f"ABORT: {len(files)} files, expected {expect_files}")
        return 2

    by = {}
    for r in rows:
        key = (r["file"], r["arm"])
        if key in by:
            print(f"ABORT: duplicate row {key}")
            return 2
        by[key] = r
    missing = [(f, a) for f in files for a in arms if (f, a) not in by]
    if missing:
        print(f"ABORT: {len(missing)} missing cells in the {len(files)}x{len(arms)} matrix")
        for m in missing[:5]:
            print("   ", m)
        return 2

    # Soundness: no two arms may disagree sat/unsat on one file.
    conflicts = []
    for f in files:
        vs = {by[(f, a)]["verdict"] for a in arms} & DECIDED
        if len(vs) > 1:
            conflicts.append(f)
    if conflicts:
        print(f"ABORT: {len(conflicts)} file(s) where two arms DISAGREE sat/unsat:")
        for c in conflicts:
            print("   ", c, {a: by[(c, a)]["verdict"] for a in arms})
        return 2

    base = "base"
    if base not in arms:
        print(f"ABORT: no `{base}` arm to compare against")
        return 2

    print(f"# QF_UFBV cap A/B -- {len(files)} files x {len(arms)} arms = {len(rows)} runs")
    print(f"# soundness: 0 sat/unsat disagreements across {len(arms)} arms on {len(files)} files")
    print()
    base_dec = {f for f in files if by[(f, base)]["verdict"] in DECIDED}
    print(f"baseline decides {len(base_dec)} of {len(files)}")
    print()
    hdr = f"{'arm':<10} {'decided':>7} {'gain':>5} {'loss':>5} {'net':>5} {'wall_s':>9} {'dwall_s':>9}"
    print(hdr)
    print("-" * len(hdr))
    base_wall = sum(int(by[(f, base)]["wall_ms"]) for f in files) / 1000.0
    detail = {}
    for a in arms:
        dec = {f for f in files if by[(f, a)]["verdict"] in DECIDED}
        gain = sorted(dec - base_dec)
        loss = sorted(base_dec - dec)
        wall = sum(int(by[(f, a)]["wall_ms"]) for f in files) / 1000.0
        detail[a] = (gain, loss)
        print(
            f"{a:<10} {len(dec):>7} {len(gain):>5} {len(loss):>5} "
            f"{len(dec) - len(base_dec):>+5} {wall:>9.1f} {wall - base_wall:>+9.1f}"
        )
    print()
    for a in arms:
        gain, loss = detail[a]
        if a == base:
            continue
        if gain:
            print(f"## {a}: {len(gain)} gained")
            for f in gain:
                r = by[(f, a)]
                print(f"   + {r['verdict']:<6} {int(r['wall_ms']) / 1000.0:>6.1f}s  {f}")
        if loss:
            print(f"## {a}: {len(loss)} LOST")
            for f in loss:
                b, r = by[(f, base)], by[(f, a)]
                print(
                    f"   - was {b['verdict']} in {int(b['wall_ms']) / 1000.0:.1f}s; "
                    f"now {r['verdict']} in {int(r['wall_ms']) / 1000.0:.1f}s  {f}"
                )
                print(f"     {r['giveup'][:150]}")
        if gain or loss:
            print()

    # Why the non-gainers still fail, per arm: the give-up reason histogram
    # over files the baseline leaves undecided.
    print("# give-up reason on files the BASELINE leaves undecided")
    und = sorted(set(files) - base_dec)
    print(f"# denominator {len(und)}")
    for a in arms:
        hist = collections.Counter()
        for f in und:
            r = by[(f, a)]
            if r["verdict"] in DECIDED:
                hist["DECIDED"] += 1
                continue
            g = r["giveup"]
            if g == "none":
                hist["no give-up line"] += 1
            else:
                kind = g.split("kind=")[1].split(" ")[0] if "kind=" in g else "?"
                det = g.split("detail=")[1] if "detail=" in g else ""
                # collapse the varying measured N out of the detail
                det = " ".join(w for w in det.split() if not w.isdigit())
                hist[f"{kind}: {det[:90]}"] += 1
        print(f"-- {a}")
        for k, v in hist.most_common():
            print(f"   {v:>4}  {k}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
