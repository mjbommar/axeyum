#!/usr/bin/env python3
"""QUANT-GROUND-INCREMENTAL (ADR-2124) -- read `cores-run.sh`'s capture into one
row per core per arm and compare the two arms.

    cores-summarize.py <outdir>

THE VERDICT AND THE TERMINAL REASON COME FROM `scripts/route_trace_reader.py`,
never from a grep over the CLI's prose -- three ADRs record a census that got a
bucket wrong by parsing the rendering instead of the artifact (ADR-2075, a prefix
nobody wrote the consumer half of; ADR-2020, a split on `;` inside a `why=`
field; ADR-2060, one give-up string standing for 28 program points).

THE GROUND-CHECK COST COMES FROM `[qtrace]`, and only from the ONE line the
loop's own call site emits:

    [qtrace] egraph-seg +<seconds> qf-check round=<N> ground=<M>

One such line per interleaved check.  `<seconds>` is the segment's own wall
clock, so summing them is the time the arm spent re-solving the accumulated
ground set -- the number ADR-2120 could not report, because it did not commit
its raw capture.

A CORE THAT PRINTS NO SUCH LINE PRINTS NOTHING, WHICH IS NOT A ZERO in general:
the loop may have exited before the first check was due.  Here it happens to be
readable as zero cost (no check ran, so no time was spent in one), and that is
the only claim made from it.  The `checks` column says which cores those are.
"""

import argparse
import os
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
sys.path.insert(0, str(REPO / "scripts"))

import route_trace_reader as rtr  # noqa: E402

QF_CHECK_RE = re.compile(
    r"^\[qtrace\]\s+egraph-seg\s+\+(?P<secs>[0-9.]+)s\s+qf-check\s+round=(?P<round>\d+)\s+ground=(?P<ground>\d+)"
)


def terminal(path):
    """`(verdict, route, reason, detail)` from the route trail, or a NAMED
    absence.  A missing trail is reported as such and never as a decline: the
    two are different facts and only one is about the solver.  Same definition
    as `bench-results/quant-activation-20260915/core-census.py:96`."""
    try:
        trail = rtr.read_file(path)
    except rtr.NoTrailLine:
        return ("none", "NO-TRAIL", "NO-TRAIL", None)
    except rtr.RouteTraceError as exc:
        return ("none", "TRAIL-ERROR", type(exc).__name__, str(exc)[:120])
    verdict = trail.verdict or "unknown"
    declines = trail.decline_reasons()
    if trail.decided_by:
        return (verdict, trail.decided_by, "decided", None)
    if not declines:
        return (verdict, trail.last or "NONE", "no-decline-recorded", None)
    route, reason, detail = declines[-1]
    return (verdict, route, reason, detail)


def qf_checks(path):
    """`(count, total_seconds, max_ground)` over the loop's own qf-check lines."""
    count, total, largest = 0, 0.0, 0
    if not os.path.exists(path):
        return (0, 0.0, 0)
    with open(path, errors="replace") as fh:
        for line in fh:
            m = QF_CHECK_RE.match(line)
            if not m:
                continue
            count += 1
            total += float(m.group("secs"))
            largest = max(largest, int(m.group("ground")))
    return (count, total, largest)


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("outdir")
    args = ap.parse_args(argv)
    raw = Path(args.outdir) / "raw"
    cores = sorted({p.name.rsplit(".", 2)[0] for p in raw.glob("*.out")})
    if not cores:
        print("no cores found -- did cores-run.sh run?")
        return 2

    rows = []
    for core in cores:
        row = {"core": core}
        for arm in ("off", "on"):
            v, r, reason, detail = terminal(raw / f"{core}.{arm}.out")
            c, secs, ground = qf_checks(raw / f"{core}.{arm}.err")
            row[arm] = {
                "verdict": v,
                "route": r,
                "reason": reason,
                "detail": detail,
                "checks": c,
                "secs": secs,
                "ground": ground,
            }
        rows.append(row)

    tsv = Path(args.outdir) / "cores.tsv"
    with open(tsv, "w") as fh:
        fh.write(
            "core\toff_verdict\toff_route\toff_reason\toff_checks\toff_qf_secs\toff_ground"
            "\ton_verdict\ton_route\ton_reason\ton_checks\ton_qf_secs\ton_ground\n"
        )
        for row in rows:
            o, n = row["off"], row["on"]
            fh.write(
                f"{row['core']}\t{o['verdict']}\t{o['route']}\t{o['reason']}\t{o['checks']}"
                f"\t{o['secs']:.3f}\t{o['ground']}"
                f"\t{n['verdict']}\t{n['route']}\t{n['reason']}\t{n['checks']}"
                f"\t{n['secs']:.3f}\t{n['ground']}\n"
            )

    def decided(a):
        return a["verdict"] in ("sat", "unsat")

    off_dec = sum(1 for r in rows if decided(r["off"]))
    on_dec = sum(1 for r in rows if decided(r["on"]))
    moved = [
        r for r in rows if r["off"]["verdict"] != r["on"]["verdict"]
    ]
    gains = [r for r in moved if decided(r["on"]) and not decided(r["off"])]
    losses = [r for r in moved if decided(r["off"]) and not decided(r["on"])]
    flips = [
        r
        for r in rows
        if decided(r["off"]) and decided(r["on"]) and r["off"]["verdict"] != r["on"]["verdict"]
    ]

    print(f"== {len(rows)} UFLIA CORES, GROUND-SESSION LEVER OFF vs ON (ADR-2124) ==")
    print()
    print(f"cores                          : {len(rows)}")
    print(f"OFF decided                    : {off_dec}")
    print(f"ON  decided                    : {on_dec}")
    print(f"verdict moved                  : {len(moved)}")
    print(f"  of which GAIN (unknown->dec) : {len(gains)}")
    print(f"  of which LOSS (dec->unknown) : {len(losses)}")
    print(f"  of which FLIP (sat<->unsat)  : {len(flips)}   <-- any nonzero here is a SOUNDNESS defect")
    print()
    print("-- the interleaved cold ground check, from the loop's own qtrace line --")
    for arm in ("off", "on"):
        ran = [r[arm] for r in rows if r[arm]["checks"] > 0]
        calls = sum(r[arm]["checks"] for r in rows)
        secs = sum(r[arm]["secs"] for r in rows)
        print(
            f"   {arm.upper():3s}  ran on {len(ran):2d} of {len(rows)}"
            f"   calls {calls:4d}   total {secs:8.1f}s"
            f"   max ground {max((r[arm]['ground'] for r in rows), default=0)}"
        )
    off_secs = sum(r["off"]["secs"] for r in rows)
    on_secs = sum(r["on"]["secs"] for r in rows)
    print()
    print(f"   seconds of ground re-solve REMOVED by the lever : {off_secs - on_secs:.1f}s")
    if off_secs > 0:
        print(f"   as a fraction of what OFF spent there           : {100.0 * (off_secs - on_secs) / off_secs:.1f}%")
    budget = len(rows) * 24.0
    print(f"   as a fraction of the whole 24s x {len(rows)} budget     : {100.0 * (off_secs - on_secs) / budget:.1f}%")

    print()
    print("-- the ON arm's TERMINAL typed reason, bucketed --")
    bucket = {}
    for r in rows:
        key = f"{r['on']['route']}={r['on']['reason']}"
        bucket[key] = bucket.get(key, 0) + 1
    for key, n in sorted(bucket.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"   {n:4d}  {key}")

    print()
    print("-- its details, VERBATIM and unbucketed (a bucket's LABEL hides four causes) --")
    det = {}
    for r in rows:
        d = (r["on"]["detail"] or "")[:118]
        if d:
            det[d] = det.get(d, 0) + 1
    for d, n in sorted(det.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"   {n:4d}  {d}")

    if moved:
        print()
        print("-- every core whose verdict MOVED --")
        for r in moved:
            print(
                f"   {r['off']['verdict']:>7s} -> {r['on']['verdict']:<7s}  "
                f"(off {r['off']['route']}={r['off']['reason']} / on {r['on']['route']}={r['on']['reason']})  "
                f"{r['core'][:60]}"
            )

    print()
    print(f"rows written to {tsv}")
    # THE EXIT STATUS DEPENDS ON THE FINDING. A flip is a soundness defect and
    # must not be reportable as a clean run.
    return 1 if flips else 0


if __name__ == "__main__":
    raise SystemExit(main())
