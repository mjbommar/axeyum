#!/usr/bin/env python3
"""QUANT-SESSION-ARITH (ADR-2130) -- read the 53-core probe's capture into one
row per core per arm and compare the two arms.

    cores-summarize.py <outdir>

THE VERDICT AND THE TERMINAL REASON COME FROM `scripts/route_trace_reader.py`,
never from a grep over the CLI's prose -- three ADRs record a census that got a
bucket wrong by parsing the rendering instead of the artifact.

TWO `[qtrace]` LINES ARE READ, and the second one is this lane's:

    [qtrace] egraph-seg   +<s> qf-check round=<N> ground=<M>
    [qtrace] ground-session +<s> built=<0|1> level=<L> round=<N> ground=<M> \\
             atoms=<A> hosted=<0|1> opaque=<O>

The first is ADR-2124's, one line per interleaved cold check, and summing its
seconds is what the arm spent re-solving the accumulated ground set. The second
is emitted UNCONDITIONALLY at the session-construction site, including on a
decline, because a core that prints no line printed an ABSENCE and an absence is
not a zero -- without it "the session declined" and "the session was never
attempted" are the same observation.

**THE EXIT STATUS DEPENDS ON THE FINDING, and on TWO findings, not one.**

  * A `sat`/`unsat` FLIP is a soundness defect -> exit 1.
  * A run in which the ON arm never actually HOSTED arithmetic on any core is a
    run that measured nothing -> exit 2. A lever that did not engage produces a
    clean-looking null that is indistinguishable from a lever that engaged and
    did not help, and this lane's whole question is which of those it is.
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
    r"^\[qtrace\]\s+egraph-seg\s+\+(?P<secs>[0-9.]+)s\s+qf-check\s+"
    r"round=(?P<round>\d+)\s+ground=(?P<ground>\d+)"
)
SESSION_RE = re.compile(
    r"^\[qtrace\]\s+ground-session\s+\+(?P<secs>[0-9.]+)s\s+built=(?P<built>\d+)\s+"
    r"level=(?P<level>\d+)\s+round=(?P<round>\d+)\s+ground=(?P<ground>\d+)\s+"
    r"atoms=(?P<atoms>\d+)\s+hosted=(?P<hosted>\d+)\s+abstracted=(?P<abstracted>\d+)\s+"
    r"gates=(?P<gates>\d+)\s+shapes=(?P<shapes>\S+)"
)


def terminal(path):
    """`(verdict, route, reason, detail)` from the route trail, or a NAMED
    absence. A missing trail is reported as such and never as a decline: the two
    are different facts and only one is about the solver."""
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


def qtrace(path):
    """`(checks, qf_secs, max_ground, session)` for one arm's stderr.

    `session` is `None` when the construction site was never reached at all --
    distinct from a site that was reached and declined, which reports
    `built=0`."""
    checks, total, largest = 0, 0.0, 0
    session = None
    if not os.path.exists(path):
        return (0, 0.0, 0, None)
    with open(path, errors="replace") as fh:
        for line in fh:
            m = QF_CHECK_RE.match(line)
            if m:
                checks += 1
                total += float(m.group("secs"))
                largest = max(largest, int(m.group("ground")))
                continue
            m = SESSION_RE.match(line)
            if m and session is None:
                session = {
                    "built": int(m.group("built")),
                    "level": int(m.group("level")),
                    "atoms": int(m.group("atoms")),
                    "hosted": int(m.group("hosted")),
                    "abstracted": int(m.group("abstracted")),
                    "gates": int(m.group("gates")),
                    "shapes": m.group("shapes"),
                    "ground": int(m.group("ground")),
                }
    return (checks, total, largest, session)


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("outdir")
    args = ap.parse_args(argv)
    raw = Path(args.outdir) / "raw"
    cores = sorted({p.name.rsplit(".", 2)[0] for p in raw.glob("*.out")})
    if not cores:
        print("no cores found -- did cores-launch.sh run?")
        return 2

    rows = []
    for core in cores:
        row = {"core": core}
        for arm in ("off", "on"):
            v, r, reason, detail = terminal(raw / f"{core}.{arm}.out")
            c, secs, ground, session = qtrace(raw / f"{core}.{arm}.err")
            row[arm] = {
                "verdict": v,
                "route": r,
                "reason": reason,
                "detail": detail,
                "checks": c,
                "secs": secs,
                "ground": ground,
                "session": session,
            }
        rows.append(row)

    tsv = Path(args.outdir) / "cores.tsv"
    with open(tsv, "w") as fh:
        fh.write(
            "core\toff_verdict\toff_route\toff_reason\toff_checks\toff_qf_secs\toff_ground"
            "\toff_built\toff_hosted\toff_abstracted"
            "\ton_verdict\ton_route\ton_reason\ton_checks\ton_qf_secs\ton_ground"
            "\ton_built\ton_hosted\ton_abstracted\n"
        )
        for row in rows:
            cells = [row["core"]]
            for arm in ("off", "on"):
                a = row[arm]
                sess = a["session"] or {}
                cells += [
                    a["verdict"],
                    a["route"],
                    a["reason"],
                    str(a["checks"]),
                    f"{a['secs']:.3f}",
                    str(a["ground"]),
                    str(sess.get("built", "-")),
                    str(sess.get("hosted", "-")),
                    str(sess.get("abstracted", "-")),
                ]
            fh.write("\t".join(cells) + "\n")

    def decided(a):
        return a["verdict"] in ("sat", "unsat")

    off_dec = sum(1 for r in rows if decided(r["off"]))
    on_dec = sum(1 for r in rows if decided(r["on"]))
    moved = [r for r in rows if r["off"]["verdict"] != r["on"]["verdict"]]
    gains = [r for r in moved if decided(r["on"]) and not decided(r["off"])]
    losses = [r for r in moved if decided(r["off"]) and not decided(r["on"])]
    flips = [
        r
        for r in rows
        if decided(r["off"])
        and decided(r["on"])
        and r["off"]["verdict"] != r["on"]["verdict"]
    ]

    print(f"== {len(rows)} UFLIA CORES, GROUND-SESSION OFF (shipped) vs ON (ADR-2130) ==")
    print()
    print(f"cores                          : {len(rows)}")
    print(f"OFF decided                    : {off_dec}")
    print(f"ON  decided                    : {on_dec}")
    print(f"verdict moved                  : {len(moved)}")
    print(f"  of which GAIN (unknown->dec) : {len(gains)}")
    print(f"  of which LOSS (dec->unknown) : {len(losses)}")
    print(
        f"  of which FLIP (sat<->unsat)  : {len(flips)}"
        "   <-- any nonzero here is a SOUNDNESS defect"
    )

    print()
    print("-- DID THE LEVER ENGAGE?  the session-construction site's own line --")
    engagement = {}
    for arm in ("off", "on"):
        reached = [r[arm] for r in rows if r[arm]["session"] is not None]
        built = [a for a in reached if a["session"]["built"] == 1]
        host = [a for a in built if a["session"]["hosted"] == 1]
        opaque = sum(a["session"]["abstracted"] for a in built)
        atoms = sum(a["session"]["atoms"] for a in built)
        engagement[arm] = len(host)
        print(
            f"   {arm.upper():3s}  site reached on {len(reached):2d} of {len(rows)}"
            f"   session BUILT {len(built):2d}   HOSTING arithmetic {len(host):2d}"
            f"   atoms {atoms:6d}   abstracted {opaque:5d}"
        )
    print(
        "   (a core whose site was never reached printed an ABSENCE, not a zero:"
        " the loop exited first)"
    )

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
        print(
            "   as a fraction of what OFF spent there           : "
            f"{100.0 * (off_secs - on_secs) / off_secs:.1f}%"
        )

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
                f"(off {r['off']['route']}={r['off']['reason']} / "
                f"on {r['on']['route']}={r['on']['reason']})  {r['core'][:60]}"
            )

    print()
    print(f"rows written to {tsv}")

    if flips:
        print()
        print("EXIT 1: a sat/unsat FLIP is a soundness defect.")
        return 1
    if engagement["on"] == 0:
        print()
        print(
            "EXIT 2: the ON arm HOSTED arithmetic on 0 of the cores, so this run\n"
            "        measured nothing about hosting. A lever that never engaged\n"
            "        produces a clean-looking null indistinguishable from a lever\n"
            "        that engaged and did not help. Do not read the deltas above\n"
            "        as a result."
        )
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
