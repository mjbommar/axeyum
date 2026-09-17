#!/usr/bin/env python3
"""Collect every `run-summary.tsv` under <sweep-root>/<run>/<arm>/ into one
`sweep.tsv` (run, arm, core, verdict, decided_by, elapsed_ms, rc), so the
per-(core, arm, run) verdicts the README and ADR-2149 s6 quote are committed
beside the scripts that read them. A run directory without a `DONE` marker is
labelled `partial` in the `status` column rather than silently included as
complete.

    collect-sweep.py <sweep-root> > sweep.tsv
"""
import os
import sys


def main(argv):
    root = argv[1]
    print("\t".join(["run", "status", "arm", "core", "verdict", "decided_by", "elapsed_ms", "rc"]))
    for run in sorted(d for d in os.listdir(root) if d.startswith("r") and os.path.isdir(os.path.join(root, d))):
        for arm in sorted(os.listdir(os.path.join(root, run))):
            arm_dir = os.path.join(root, run, arm)
            summary = os.path.join(arm_dir, "run-summary.tsv")
            if not os.path.isfile(summary):
                continue
            status = "complete" if os.path.exists(os.path.join(arm_dir, "DONE")) else "partial"
            with open(summary, encoding="utf-8") as f:
                header = f.readline().rstrip("\n").split("\t")
                for line in f:
                    parts = line.rstrip("\n").split("\t")
                    if len(parts) != len(header):
                        continue
                    d = dict(zip(header, parts))
                    print("\t".join([run, status, arm, d["core"], d["verdict"], d["decided_by"], d["elapsed_ms"], d["rc"]]))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
