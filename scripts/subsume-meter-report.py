#!/usr/bin/env python3
"""Read the sweep rows written by ``scripts/subsume-meter-sweep.sh`` and print
the tables the subsumption work-meter measurement is stated in.

Usage:
    python3 scripts/subsume-meter-report.py <label>=<arm.jsonl> [...]

Labels are the arm labels the sweep script takes (``off``, ``base``,
``bve-free``, ``bve-free-compact``, ``subsume-gated``, ...). Every arm must
cover the same benchmark list, and this refuses when they do not: an arm
silently measured over a different population produces a comparison that is not
one, and that failure looks exactly like a real difference in the numbers.

THE EXIT STATUS DEPENDS ON THE FINDING
--------------------------------------

Exit 1 when a population is inconsistent, when a arm recorded no rows, or when
a table that the report is *about* would be computed over zero files. A report
that prints "the arms are identical" over an empty intersection is worse than
no report, because it reads as a result.
"""

import json
import statistics
import sys

PAR2_UNSOLVED_MULTIPLIER = 2


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

    Absent is not zero: a pass that never ran records no timing, and treating
    that as a measured zero is how a skipped stage becomes a fast one.
    """
    return row.get("counters", {}).get(key)


def num(row, key, default=0.0):
    v = counter(row, key)
    return default if v is None else v


def pct(values, q):
    if not values:
        return float("nan")
    values = sorted(values)
    idx = min(len(values) - 1, int(q * len(values)))
    return values[idx]


def par2(rows, budget_ms):
    total = 0.0
    for row in rows:
        if row["verdict"] in ("sat", "unsat"):
            total += row["wall_ms"] / 1000.0
        else:
            total += PAR2_UNSOLVED_MULTIPLIER * budget_ms / 1000.0
    return total


def decided(rows):
    return sum(1 for r in rows if r["verdict"] in ("sat", "unsat"))


def main():
    args = sys.argv[1:]
    if not args:
        print(__doc__)
        return 2

    arms = {}
    for arg in args:
        label, _, path = arg.partition("=")
        if not path:
            print(f"FAIL: expected <label>=<path>, got {arg!r}", file=sys.stderr)
            return 1
        rows = load(path)
        if not rows:
            print(f"FAIL: {path} has no rows — nothing was measured", file=sys.stderr)
            return 1
        arms[label] = {r["file"]: r for r in rows}

    populations = {label: frozenset(rows) for label, rows in arms.items()}
    if len(set(populations.values())) != 1:
        for label, pop in populations.items():
            print(f"  {label}: {len(pop)} files", file=sys.stderr)
        print("FAIL: the arms do not cover the same files", file=sys.stderr)
        return 1
    files = sorted(next(iter(populations.values())))
    budget_ms = next(iter(next(iter(arms.values())).values()))["budget_ms"]
    print(f"population: {len(files)} files, budget {budget_ms} ms\n")

    # ---- headline per arm -------------------------------------------------
    print("| arm | decided | PAR-2 | inproc s | subsume s | vivify s | bve s |"
          " subsume clock-cut | subsume work-cut | bve dead/spent |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for label, rows in arms.items():
        rs = [rows[f] for f in files]
        inproc = sum(num(r, "inprocess_ms") for r in rs) / 1000
        sub = sum(num(r, "subsume_ms") for r in rs) / 1000
        viv = sum(num(r, "vivify_ms") for r in rs) / 1000
        bve = sum(num(r, "bve_ms") for r in rs) / 1000
        sub_clock = sum(1 for r in rs if num(r, "subsume_deadline_expired") == 1)
        sub_work = sum(1 for r in rs if num(r, "subsume_work_exhausted") == 1)
        dead = sum(num(r, "bve_dead_occurrence_entries") for r in rs)
        spent = sum(num(r, "bve_work_spent") for r in rs)
        ratio = f"{dead / spent:.3f}" if spent else "—"
        print(f"| {label} | {decided(rs)} | {par2(rs, budget_ms):.1f} | {inproc:.1f} |"
              f" {sub:.1f} | {viv:.1f} | {bve:.1f} | {sub_clock} | {sub_work} | {ratio} |")
    print()

    # ---- verdict safety, before any timing is read ------------------------
    conflicts = []
    for f in files:
        verdicts = {rows[f]["verdict"] for rows in arms.values()}
        verdicts.discard("unknown")
        verdicts.discard("killed")
        if len(verdicts) > 1:
            conflicts.append((f, verdicts))
    print(f"cross-arm verdict conflicts: {len(conflicts)}")
    for f, v in conflicts[:10]:
        print(f"  CONFLICT {f}: {sorted(v)}")
    if conflicts:
        print("FAIL: arms disagree on a verdict", file=sys.stderr)
        return 1
    print()

    # ---- subsumption cost distribution, from a calibration arm ------------
    calib = arms.get("base") or arms.get("bve-free")
    if calib is None:
        print("no calibration arm (base / bve-free) given; skipping the "
              "distribution and pricing tables")
        return 0

    ran = []
    for f in files:
        r = calib[f]
        setup = counter(r, "subsume_setup_work")
        spent = counter(r, "subsume_work_spent")
        last = counter(r, "subsume_work_at_last_progress")
        ms = counter(r, "subsume_ms")
        if setup and spent and last is not None and ms is not None:
            ran.append((f, setup, spent, last, ms))
    if not ran:
        print("FAIL: no file recorded the subsumption counters — the report's "
              "subject was never measured", file=sys.stderr)
        return 1
    print(f"files that ran subsumption and recorded the counters: {len(ran)} "
          f"of {len(files)}")

    lastx = [last / setup for (_, setup, _, last, _) in ran]
    spendx = [spent / setup for (_, setup, spent, _, _) in ran]
    total_spent = sum(spent for (_, _, spent, _, _) in ran)
    total_waste = sum(spent - last for (_, _, spent, last, _) in ran)
    print(f"\nlast progress, in units of the pass's own setup cost:")
    print(f"  p50 {pct(lastx, 0.50):.0f}x  p75 {pct(lastx, 0.75):.0f}x  "
          f"p90 {pct(lastx, 0.90):.0f}x  p95 {pct(lastx, 0.95):.0f}x  "
          f"max {max(lastx):.0f}x")
    print(f"total spend, same units: p50 {pct(spendx, 0.50):.0f}x  "
          f"p90 {pct(spendx, 0.90):.0f}x  max {max(spendx):.0f}x")
    print(f"spend after the last useful action: {100 * total_waste / total_spent:.1f}%"
          f" of all subsumption work")

    rates = [spent / ms for (_, _, spent, _, ms) in ran if ms >= 20]
    if rates:
        print(f"throughput (steps/ms, {len(rates)} files >= 20 ms): "
              f"p10 {pct(rates, 0.10):,.0f}  median {statistics.median(rates):,.0f}  "
              f"p90 {pct(rates, 0.90):,.0f}")
    else:
        print("throughput: NOT MEASURED — no file spent 20 ms in subsumption")

    # ---- pricing every candidate budget from the one calibration sweep ----
    print("\n| K (x setup) | files cut | sec saved | files keeping 100% |")
    print("|---:|---:|---:|---:|")
    for k in (10, 25, 50, 100, 200, 500, 1000, 2000, 5000):
        cut = 0
        saved = 0.0
        whole = 0
        for (_, setup, spent, last, ms) in ran:
            limit = k * setup
            if limit >= spent:
                whole += 1
                continue
            cut += 1
            rate = spent / ms if ms > 0 else None
            if rate:
                saved += (spent - limit) / rate / 1000.0
            if limit >= last:
                whole += 1
        print(f"| {k} | {cut} | {saved:.1f} s | {whole} |")

    # ---- budgeting against compaction, the two fixes side by side ---------
    free = arms.get("bve-free")
    compact = arms.get("bve-free-compact")
    budgeted = arms.get("base")
    if free and compact:
        print("\n=== compaction against budgeting (BVE) ===")
        dead = sum(num(free[f], "bve_dead_occurrence_entries") for f in files)
        spent = sum(num(free[f], "bve_work_spent") for f in files)
        if spent == 0:
            print("FAIL: no BVE work was recorded in the unbudgeted arm — the "
                  "compaction comparison has no subject", file=sys.stderr)
            return 1
        print(f"dead occurrence entries, unbudgeted BVE: {dead:,.0f} of "
              f"{spent:,.0f} steps = {100 * dead / spent:.2f}% of the scan")
        per_file = sorted(
            (num(free[f], "bve_dead_occurrence_entries")
             / max(num(free[f], "bve_work_spent"), 1.0))
            for f in files
            if num(free[f], "bve_work_spent") > 0
        )
        if per_file:
            print(f"per file: p50 {100 * pct(per_file, 0.5):.2f}%  "
                  f"p90 {100 * pct(per_file, 0.9):.2f}%  "
                  f"max {100 * max(per_file):.2f}%  ({len(per_file)} files)")
        rows = [("bve-free (neither fix)", free)]
        if budgeted:
            rows.append(("base (budget only)", budgeted))
        rows.append(("bve-free-compact (compaction only)", compact))
        print("\n| arm | bve s | bve work steps | dead steps | vars eliminated |")
        print("|---|---:|---:|---:|---:|")
        for label, a in rows:
            ms = sum(num(a[f], "bve_ms") for f in files) / 1000
            w = sum(num(a[f], "bve_work_spent") for f in files)
            d = sum(num(a[f], "bve_dead_occurrence_entries") for f in files)
            v = sum(num(a[f], "bve_variables_eliminated") for f in files)
            print(f"| {label} | {ms:.1f} | {w:,.0f} | {d:,.0f} | {v:,.0f} |")

    # ---- the file this lane was handed ------------------------------------
    print("\nthe named file:")
    for f in files:
        if "div3.c.50" not in f:
            continue
        for label, rows in arms.items():
            r = rows[f]
            print(f"  {label:22s} {r['verdict']:8s} wall {r['wall_ms']:>7.0f} ms  "
                  f"subsume {num(r, 'subsume_ms'):>8.0f} ms  "
                  f"bve {num(r, 'bve_ms'):>8.0f} ms  "
                  f"subsume_work {num(r, 'subsume_work_spent'):>15,.0f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
