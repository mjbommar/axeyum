#!/usr/bin/env python3
"""Compare sweep arms on one population, file by file.

Usage: compare.py <ref-solved.tsv> <baseline-dir>[,<dir>…] <arm-dir> [<arm-dir>…]

The baseline may be several directories (the base run was sharded across three
hosts); every arm after it is one directory holding the whole population.

EXIT STATUS 1 ON A DISAGREEMENT — either between two arms on a `sat`/`unsat`, or
between an arm and the committed reference verdict. A soundness break has to
fail the run, not appear in a table somebody skims.
"""

import collections
import hashlib
import json
import pathlib
import sys


def summary(d):
    rows = {}
    meta = []
    for line in open(pathlib.Path(d) / "summary.tsv"):
        if line.startswith("#"):
            meta.append(line.rstrip("\n"))
            continue
        p = line.rstrip("\n").split("\t")
        if p[0] == "file":
            continue
        rows[p[0]] = (int(p[1]), p[2])
    return rows, meta


def raw(d, path):
    key = hashlib.sha256(path.encode()).hexdigest()[:12]
    p = pathlib.Path(d) / "raw" / f"{key}.txt"
    return p.read_text() if p.exists() else ""


def last_attempt(text):
    trail = None
    for line in text.splitlines():
        for pre in ("; route-trail ", "; partial route-trail "):
            if line.startswith(pre):
                try:
                    trail = json.loads(line[len(pre) :])
                except json.JSONDecodeError:
                    trail = None
    att = [a for a in (trail or {}).get("attempts", []) if a["route"] != "probe"]
    if not att:
        return ("none", "no attempt recorded")
    a = att[-1]
    return (a["route"], (a.get("detail") or a.get("reason") or "")[:120])


def interface_line(text):
    for line in text.splitlines():
        if "uflia-interface " in line:
            return line
    return ""


def main(argv):
    ref = {}
    for line in open(argv[1]):
        f, v = line.rstrip("\n").split("\t")
        ref[f] = v

    base = {}
    for d in argv[2].split(","):
        rows, _ = summary(d)
        base.update(rows)

    bad = False
    for arm_dir in argv[3:]:
        rows, meta = summary(arm_dir)
        print(f"== {arm_dir}")
        for m in meta:
            print("   " + m)
        gained, lost, disagree = [], [], []
        for f, (ms, v) in rows.items():
            bv = base.get(f, (0, "unknown"))[1]
            if v in ("sat", "unsat") and f in ref and v != ref[f]:
                disagree.append((f, v, ref[f]))
            if v in ("sat", "unsat") and bv not in ("sat", "unsat"):
                gained.append((f, v, ms))
            if bv in ("sat", "unsat") and v not in ("sat", "unsat"):
                lost.append((f, bv, ms))
        decided = sum(1 for _, (_, v) in rows.items() if v in ("sat", "unsat"))
        print(f"   files {len(rows)}  decided {decided}  gained {len(gained)}  lost {len(lost)}")
        if disagree:
            bad = True
            print("   DISAGREEMENTS AGAINST THE REFERENCE:")
            for d in disagree:
                print("     ", d)
        for f, v, ms in sorted(gained, key=lambda x: x[0]):
            print(f"   + {v:5s} {ms:6d}ms  {pathlib.Path(f).name}")
        for f, v, ms in sorted(lost, key=lambda x: x[0]):
            print(f"   - was {v:5s} {ms:6d}ms  {pathlib.Path(f).name}")

        tail = collections.Counter()
        for f, (ms, v) in rows.items():
            if v in ("sat", "unsat"):
                continue
            tail[last_attempt(raw(arm_dir, f))] += 1
        print("   still lost, by last route and reason:")
        for (r, d), n in tail.most_common():
            print(f"     {n:3d}  {r:32s} {d}")
        print()

    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
