#!/usr/bin/env python3
"""Read the sweep rows written by ``scripts/inprocess-cost-sweep.sh`` and print
the tables the cost decomposition is stated in.

Usage:
    python3 scripts/inprocess-cost-report.py <arm.jsonl> [<arm.jsonl> ...]

Every arm file must cover the same benchmark list, and this refuses when they do
not: an arm silently measured over a different (or shorter) population produces
a solved-count comparison that is not a comparison, and that failure looks
exactly like a real difference in the numbers.

WHAT THE BUDGET CURVE IS AND IS NOT

``solved_at(B)`` counts files whose recorded wall time is <= B. For a sweep run
AT budget B0 that is an observation at B0 and a DERIVED number below it, and the
derivation is only valid if the solver's behaviour does not depend on the budget
it was given. It does here: inprocessing is granted half the remaining solve
budget, so a smaller budget is a smaller slice. The derivation is therefore
reported together with the count of rows whose passes actually hit that
deadline (``*_deadline_expired``). Zero such rows is what licenses reading the
derived column; a nonzero count is printed loudly rather than folded in.
"""

import json
import sys
from collections import defaultdict


def load(path):
    rows = []
    with open(path, encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if line:
                rows.append(json.loads(line))
    return rows


def counter(row, key):
    """A counter's value, or None when the run did not record it.

    Absent is not zero. A pass that never ran records no timing, and a run with
    no deadline records no ``*_deadline_expired`` flag at all; defaulting either
    to 0 would turn "not measured" into "measured as none".
    """
    return row.get("counters", {}).get(key)


def main():
    paths = sys.argv[1:]
    if not paths:
        print(__doc__)
        return 2

    arms = {}
    for path in paths:
        rows = load(path)
        if not rows:
            print(f"FAIL: {path} has no rows — nothing was measured", file=sys.stderr)
            return 1
        arm = rows[0].get("arm", path)
        arms[arm] = {r["file"]: r for r in rows}
        print(f"# {arm}: {len(rows)} rows from {path}", file=sys.stderr)

    populations = {frozenset(v) for v in arms.values()}
    if len(populations) != 1:
        print(
            "FAIL: the arms do not cover the same files — a solved-count "
            "comparison over different populations is not a comparison",
            file=sys.stderr,
        )
        for arm, rows in arms.items():
            print(f"  {arm}: {len(rows)} files", file=sys.stderr)
        return 1
    files = sorted(next(iter(populations)))
    print(f"\npopulation: {len(files)} files, identical across {len(arms)} arms\n")

    # SOUNDNESS FIRST, BEFORE ANY PERFORMANCE TABLE.
    #
    # Inprocessing changes the formula the SAT core decides, and a `sat` model
    # comes back through a reconstruction stack. A performance report over
    # verdicts nobody cross-checked would be measuring how fast we get answers
    # of unknown correctness. Every benchmark that declares `(set-info :status
    # ...)` is ground truth; a disagreement is an immediate FAIL, not a
    # percentage, exactly as the parity protocol requires.
    #
    # A file with no declared status is NOT dropped — it is counted as
    # unverifiable and reported, so "we checked everything we could" and "we
    # checked everything" stay distinguishable.
    print("## declared-`:status` cross-check (a disagreement is a FAIL, not a footnote)")
    print("| arm | decided | agreed | DISAGREED | no declared status |")
    print("|---|---:|---:|---:|---:|")
    disagreements = []
    declared = {}
    for f in files:
        try:
            with open(f, encoding="utf-8", errors="replace") as handle:
                for line in handle:
                    if ":status" in line:
                        for word in ("unsat", "sat", "unknown"):
                            if word in line.split(":status", 1)[1]:
                                declared[f] = word
                                break
                        break
        except OSError:
            pass
    for arm, rows in arms.items():
        decided = agreed = disagreed = nostatus = 0
        for f in files:
            v = rows[f]["verdict"]
            if v not in ("sat", "unsat"):
                continue
            decided += 1
            want = declared.get(f)
            if want is None or want == "unknown":
                nostatus += 1
            elif want == v:
                agreed += 1
            else:
                disagreed += 1
                disagreements.append((arm, f, want, v))
        print(f"| {arm} | {decided} | {agreed} | {disagreed} | {nostatus} |")
    if disagreements:
        print("\n**FAIL — a verdict contradicts the benchmark's declared status:**")
        for arm, f, want, got in disagreements:
            print(f"  {arm}: {f} declared {want}, we answered {got}")

    # Cross-arm agreement is the second check, and it is independent of the
    # first: it catches a wrong verdict on a file that declares no status.
    if len(arms) > 1:
        cross = []
        arm_names = list(arms)
        for f in files:
            verdicts = {
                arms[a][f]["verdict"] for a in arm_names if arms[a][f]["verdict"] in ("sat", "unsat")
            }
            if len(verdicts) > 1:
                cross.append((f, {a: arms[a][f]["verdict"] for a in arm_names}))
        print(f"\ncross-arm verdict conflicts: {len(cross)}")
        for f, v in cross:
            print(f"  CONFLICT {f}: {v}")

    budgets = [1000, 3000, 6000, 12000, 24000, 60000, 120000]
    print("## solved count vs budget (ms). `at-budget` is the run's own budget.")
    header = "| arm | " + " | ".join(f"{b // 1000}s" for b in budgets) + " | run budget |"
    print(header)
    print("|" + "---|" * (len(budgets) + 2))
    for arm, rows in arms.items():
        cells = []
        for budget in budgets:
            n = sum(
                1
                for f in files
                if rows[f]["verdict"] in ("sat", "unsat")
                and rows[f]["wall_ms"] <= budget
            )
            cells.append(str(n))
        run_budget = rows[files[0]]["budget_ms"]
        print(f"| {arm} | " + " | ".join(cells) + f" | {run_budget} |")

    print("\n## deadline truncation: did a pass run out of its slice?")
    print("| arm | rows with inprocessing | subsume expired | bve expired | vivify expired |")
    print("|---|---:|---:|---:|---:|")
    for arm, rows in arms.items():
        ran = [r for r in rows.values() if counter(r, "cnf_inprocessing") == 1.0]
        def expired(key):
            return sum(1 for r in ran if counter(r, key) == 1.0)
        print(
            f"| {arm} | {len(ran)} | {expired('subsume_deadline_expired')} | "
            f"{expired('bve_deadline_expired')} | {expired('vivify_deadline_expired')} |"
        )

    print("\n## where the inprocessing time went (ms, summed over files that ran it)")
    stages = [
        "xor_propagate_ms",
        "subsume_ms",
        "vivify_ms",
        "bve_ms",
        "compact_ms",
    ]
    print("| arm | files | " + " | ".join(stages) + " | sum stages | inprocess_ms | residual |")
    print("|" + "---|" * (len(stages) + 5))
    for arm, rows in arms.items():
        ran = [r for r in rows.values() if counter(r, "cnf_inprocessing") == 1.0]
        if not ran:
            continue
        totals = {s: sum(counter(r, s) or 0.0 for r in ran) for s in stages}
        total_stage = sum(totals.values())
        total_inproc = sum(counter(r, "inprocess_ms") or 0.0 for r in ran)
        cells = " | ".join(f"{totals[s]:.0f}" for s in stages)
        print(
            f"| {arm} | {len(ran)} | {cells} | {total_stage:.0f} | "
            f"{total_inproc:.0f} | {total_inproc - total_stage:.0f} |"
        )

    print("\n## formula shrink (files where inprocessing ran)")
    print("| arm | files | clauses before | clauses after | ratio | literals before | literals after | ratio | vars before | vars after | ratio |")
    print("|" + "---|" * 11)
    for arm, rows in arms.items():
        ran = [r for r in rows.values() if counter(r, "cnf_inprocessing") == 1.0]
        if not ran:
            continue
        cb = sum(counter(r, "cnf_clauses") or 0.0 for r in ran)
        ca = sum(counter(r, "cnf_clauses_solved") or 0.0 for r in ran)
        lb = sum(counter(r, "inprocess_literals_before") or 0.0 for r in ran)
        la = sum(counter(r, "inprocess_literals_after") or 0.0 for r in ran)
        vb = sum(counter(r, "cnf_variables") or 0.0 for r in ran)
        va = sum(counter(r, "cnf_variables_solved") or 0.0 for r in ran)
        print(
            f"| {arm} | {len(ran)} | {cb:.0f} | {ca:.0f} | {ca / max(cb, 1):.3f} | "
            f"{lb:.0f} | {la:.0f} | {la / max(lb, 1):.3f} | "
            f"{vb:.0f} | {va:.0f} | {va / max(vb, 1):.3f} |"
        )

    base = "off" if "off" in arms else None
    if base:
        print("\n## per-file verdict changes vs `off`")
        for arm, rows in arms.items():
            if arm == base:
                continue
            gained = [
                f
                for f in files
                if rows[f]["verdict"] in ("sat", "unsat")
                and arms[base][f]["verdict"] not in ("sat", "unsat")
            ]
            lost = [
                f
                for f in files
                if arms[base][f]["verdict"] in ("sat", "unsat")
                and rows[f]["verdict"] not in ("sat", "unsat")
            ]
            print(f"\n### {arm}: gained {len(gained)}, lost {len(lost)}")
            for f in gained:
                print(f"  GAINED {f}  ({rows[f]['wall_ms']} ms)")
            for f in lost:
                print(f"  LOST   {f}  (off: {arms[base][f]['wall_ms']} ms)")

        print("\n## the ten files where inprocessing cost the most wall time vs `off`")
        for arm, rows in arms.items():
            if arm == base:
                continue
            deltas = []
            for f in files:
                if arms[base][f]["verdict"] in ("sat", "unsat") and rows[f]["verdict"] in (
                    "sat",
                    "unsat",
                ):
                    deltas.append((rows[f]["wall_ms"] - arms[base][f]["wall_ms"], f))
            deltas.sort(reverse=True)
            print(f"\n### {arm} (both arms decided; positive = slower with the pass on)")
            print("| delta ms | off ms | arm ms | inprocess_ms | bve_ms | file |")
            print("|---:|---:|---:|---:|---:|---|")
            for delta, f in deltas[:10]:
                r = rows[f]
                print(
                    f"| {delta} | {arms[base][f]['wall_ms']} | {r['wall_ms']} | "
                    f"{counter(r, 'inprocess_ms') or 0:.0f} | "
                    f"{counter(r, 'bve_ms') or 0:.0f} | {f.split('/')[-1]} |"
                )

        print("\n## boundary files: decided by one arm within 20% of the budget, or flipped")
        boundary = set()
        for arm, rows in arms.items():
            for f in files:
                budget = rows[f]["budget_ms"]
                v_base = arms[base][f]["verdict"] in ("sat", "unsat")
                v_arm = rows[f]["verdict"] in ("sat", "unsat")
                if v_base != v_arm:
                    boundary.add(f)
                elif v_arm and rows[f]["wall_ms"] > 0.8 * budget:
                    boundary.add(f)
        for f in sorted(boundary):
            cells = " ".join(
                f"{a}={arms[a][f]['verdict']}/{arms[a][f]['wall_ms']}ms" for a in arms
            )
            print(f"  {f}  {cells}")
        print(f"\nboundary files: {len(boundary)}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
