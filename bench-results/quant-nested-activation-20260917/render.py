#!/usr/bin/env python3
"""Render `split.tsv` (from `split.py`) as the per-core markdown table and the
pooled totals the README carries, so the README's numbers are derived from the
committed TSV rather than typed.

    render.py split.tsv            # per-core table + pooled totals
    render.py split.tsv --pooled   # pooled totals only
"""
import csv
import sys


def load(path):
    with open(path, encoding="utf-8") as f:
        return list(csv.DictReader(f, delimiter="\t"))


def short(core):
    return core.replace("UFLIA_", "").replace(".smt2.core.smt2", "")


def pooled(rows):
    arms = {}
    for r in rows:
        a = arms.setdefault(r["arm"], {"cores": 0, "unsat": 0, "table": 0, "regs_context": 0,
                                       "regs_crossed": 0, "regs_negative": 0, "regs_untracked": 0,
                                       "handoff": 0, "poscap": 0, "nocontext": 0,
                                       "nocontext_crossed": 0, "nocontext_negative": 0,
                                       "nocontext_untracked": 0, "cores_crossed": 0,
                                       "disc_registered": 0, "disc_rejected_checker": 0,
                                       "cap_regs": 0, "cap_rebuilds": 0, "cap_positive": 0})
        a["cores"] += 1
        a["unsat"] += r["verdict"] == "unsat"
        a["table"] += int(r["invocations"]) > 0
        for k in ("regs_context", "regs_crossed", "regs_negative", "regs_untracked", "handoff",
                  "poscap", "nocontext", "nocontext_crossed", "nocontext_negative",
                  "nocontext_untracked", "disc_registered", "disc_rejected_checker"):
            a[k] += int(r[k])
        a["cores_crossed"] += int(r["nocontext_crossed"]) > 0
        a["cap_regs"] += int(r["cap_registrations_hit"]) > 0
        a["cap_rebuilds"] += int(r["cap_rebuilds_hit"]) > 0
        a["cap_positive"] += int(r["cap_positive_hit"]) > 0
    return arms


def main(argv):
    rows = load(argv[1])
    arms = pooled(rows)
    if "--pooled" not in argv:
        by_core = {}
        for r in rows:
            by_core.setdefault(r["core"], {})[r["arm"]] = r
        arm_names = sorted(arms)
        print("| core | " + " | ".join(
            f"{a}: verdict | {a}: nocontext crossed / negative / untracked | {a}: handoff | {a}: caps hit (regs/rebuilds/positive)"
            for a in arm_names) + " |")
        print("|---|" + "|".join("---|---:|---:|---" for _ in arm_names) + "|")
        for core in sorted(by_core):
            cells = []
            for a in arm_names:
                r = by_core[core].get(a)
                if r is None:
                    cells.append("(no run) | | | ")
                    continue
                v = r["verdict"] if int(r["invocations"]) > 0 else f"{r['verdict']} (no table)"
                cells.append(
                    f"{v} | {r['nocontext_crossed']} / {r['nocontext_negative']} / {r['nocontext_untracked']} "
                    f"| {r['handoff']} | {r['cap_registrations_hit']}/{r['cap_rebuilds_hit']}/{r['cap_positive_hit']}")
            print(f"| `{short(core)}` | " + " | ".join(cells) + " |")
        print()
    print("| arm | cores | unsat | cores printing a table | regs context / crossed / negative / untracked | handoff | poscap | nocontext crossed / negative / untracked | cores with crossed drops | discovered | checker-refused | cores hitting cap regs / rebuilds / positive |")
    print("|---|---:|---:|---:|---|---:|---:|---|---:|---:|---:|---|")
    for a in sorted(arms):
        d = arms[a]
        print(f"| `{a}` | {d['cores']} | {d['unsat']} | {d['table']} | "
              f"{d['regs_context']:,} / {d['regs_crossed']} / {d['regs_negative']} / {d['regs_untracked']:,} | "
              f"{d['handoff']:,} | {d['poscap']:,} | "
              f"{d['nocontext_crossed']:,} / {d['nocontext_negative']:,} / {d['nocontext_untracked']:,} | "
              f"{d['cores_crossed']} | {d['disc_registered']:,} | {d['disc_rejected_checker']:,} | "
              f"{d['cap_regs']} / {d['cap_rebuilds']} / {d['cap_positive']} |")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
