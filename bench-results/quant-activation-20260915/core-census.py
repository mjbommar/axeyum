#!/usr/bin/env python3
"""QUANT-ACTIVATION -- read `core-census.sh`'s raw capture into one row per core
and bucket the ON arm's terminal reason (ADR-2120 §7).

    core-census.py <outdir> [--inst-dir DIR]

THE TERMINAL REASON COMES FROM `scripts/route_trace_reader.py`, never from a
grep over the CLI's prose. Three ADRs in this repository record a census that
got a bucket wrong by parsing the rendering instead of the artifact: a prefix
nobody wrote the consumer half of (ADR-2075), a split on `;` inside a `why=`
field (ADR-2020), and one give-up string standing for 28 program points
(ADR-2060). The reader is the contract.

THE INSTANCE AND GROUND COLUMNS COME FROM STDERR, and each is named for the
producer that emits it rather than inferred:

    admitted     sum of `admitted=` over the `QPROBE universal[...]` lines --
                 instances the loop ACCEPTED into the ground set.
    handoff      sum of `rej_handoff=`  -- tuples handed to the positive-
                 replacement driver because the universal HAS a context.
    nocontext    sum of `rej_nocontext=` -- tuples joined and then DISCARDED
                 because it has none. The bucket ADR-2113 measured at 100.0 %.
    ground       the `ground=` total on the `[qtrace] nested-quant` line: how
                 many replacement conclusions reached the ground set.
    qf_checks    how many `qf-check round=` lines appeared -- whether the
                 interleaved GROUND CLOSURE ran at all, and how often.
    qf_ground    the largest `ground=N` a `qf-check` line reported: the size of
                 the set the ground solver was actually handed.

`probed` is its own column and is not folded into `admitted`. A core whose loop
exits before the per-universal probe block prints NOTHING, which is
indistinguishable in the output from a core that admitted nothing -- and
collapsing the two is how a census reports a strong negative it never measured
(ADR-2113 had to make the same caveat about 34 of its 53 cores).

Z3 MEMBERSHIP is reported only where a ground dump exists, and PRESENT is the
strong direction: the dump holds whatever the run accumulated before its
deadline, so load can only move a row from PRESENT to ABSENT. An ABSENT column
is a lower bound and is labelled one.
"""

import argparse
import collections
import os
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
sys.path.insert(0, str(REPO / "scripts"))

import route_trace_reader as rtr  # noqa: E402

PROBE_RE = re.compile(r"^QPROBE\s+universal\[")
FIELD_RE = {
    "admitted": re.compile(r"\badmitted=(\d+)"),
    "handoff": re.compile(r"\brej_handoff=(\d+)"),
    "nocontext": re.compile(r"\brej_nocontext=(\d+)"),
}
NESTED_RE = re.compile(r"totals: positive=(\d+) ground=(\d+) regs=(\d+) rejected=(\d+)")
QFCHECK_RE = re.compile(r"qf-check round=(\d+) ground=(\d+)")
IDENT_RE = re.compile(r"[A-Za-z0-9_.$@!~^&*+\-/<>=%?:|]+")


def read_err(path):
    out = {
        "probed": 0,
        "admitted": 0,
        "handoff": 0,
        "nocontext": 0,
        "ground": 0,
        "qf_checks": 0,
        "qf_ground": 0,
    }
    if not os.path.exists(path):
        return out
    with open(path, errors="replace") as fh:
        for line in fh:
            if PROBE_RE.match(line):
                out["probed"] += 1
                for key, rx in FIELD_RE.items():
                    m = rx.search(line)
                    if m:
                        out[key] += int(m.group(1))
                continue
            m = NESTED_RE.search(line)
            if m:
                out["ground"] = max(out["ground"], int(m.group(2)))
                continue
            m = QFCHECK_RE.search(line)
            if m:
                out["qf_checks"] += 1
                out["qf_ground"] = max(out["qf_ground"], int(m.group(2)))
    return out


def terminal(path):
    """`(verdict, route, reason, detail)` from the route trail, or a NAMED
    absence. A missing trail is reported as such and never as a decline: the
    two are different facts and only one is about the solver."""
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


def ground_terms(dump):
    """Every identifier-ish token in the accumulated ground dump.

    Containment at IDENTIFIER BOUNDARIES, not substring: ADR-2113 records that a
    substring test over a multi-megabyte corpus drifts toward answering PRESENT
    for everything, and that the opposite error -- comparing a term against a
    whole asserted CONJUNCT -- returned ABSENT on 100 % of arguments including
    bare declared constants."""
    if not os.path.exists(dump):
        return None
    with open(dump, errors="replace") as fh:
        text = fh.read()
    return set(IDENT_RE.findall(text))


def z3_instance_args(inst_path):
    """The terms z3's own proof substitutes, one per tab-separated field."""
    if not os.path.exists(inst_path):
        return None
    args = []
    with open(inst_path, errors="replace") as fh:
        for line in fh:
            parts = line.rstrip("\n").split("\t")
            args.extend(p for p in parts[1:] if p)
    return args


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("outdir")
    ap.add_argument("--inst-dir", default=None)
    args = ap.parse_args()
    raw = Path(args.outdir) / "raw"
    dump = Path(args.outdir) / "dump"
    cores = sorted({p.name[: -len(".off.out")] for p in raw.glob("*.off.out")})
    if not cores:
        print("no cores found -- did core-census.sh run?")
        return 1

    cols = (
        "core", "off_verdict", "off_route", "off_reason",
        "on_verdict", "on_route", "on_reason",
        "on_probed", "on_admitted", "on_handoff", "on_nocontext",
        "on_ground", "on_qf_checks", "on_qf_ground",
        "off_handoff", "off_nocontext",
        "z3_args", "z3_present",
    )
    rows = []
    buckets = collections.Counter()
    details = collections.Counter()
    moved = []
    for core in cores:
        offv, offr, offreason, _ = terminal(raw / f"{core}.off.out")
        onv, onr, onreason, ondetail = terminal(raw / f"{core}.on.out")
        e_on = read_err(raw / f"{core}.on.err")
        e_off = read_err(raw / f"{core}.off.err")
        buckets[f"{onr}={onreason}"] += 1
        if ondetail:
            details[ondetail.strip()[:160]] += 1
        if offv != onv:
            moved.append((core, offv, onv))
        z3n = z3p = "NA"
        if args.inst_dir:
            terms = ground_terms(dump / f"{core}.on.ground")
            z3args = z3_instance_args(Path(args.inst_dir) / f"{core}.inst")
            if terms is not None and z3args is not None:
                present = 0
                for a in z3args:
                    toks = set(IDENT_RE.findall(a))
                    if toks and toks <= terms:
                        present += 1
                z3n, z3p = len(z3args), present
        rows.append(
            (core, offv, offr, offreason, onv, onr, onreason,
             e_on["probed"], e_on["admitted"], e_on["handoff"], e_on["nocontext"],
             e_on["ground"], e_on["qf_checks"], e_on["qf_ground"],
             e_off["handoff"], e_off["nocontext"], z3n, z3p)
        )

    with open(Path(args.outdir) / "cores.tsv", "w") as fh:
        fh.write("\t".join(cols) + "\n")
        for r in rows:
            fh.write("\t".join(str(x) for x in r) + "\n")

    print("== 53 UFLIA CORES, LEVER OFF vs ON ==")
    print("")
    print("cores                          : %d" % len(rows))
    print("OFF decided                    : %d" % sum(1 for r in rows if r[1] in ("sat", "unsat")))
    print("ON  decided                    : %d" % sum(1 for r in rows if r[4] in ("sat", "unsat")))
    print("verdict moved                  : %d" % len(moved))
    for core, a, b in moved:
        print("    MOVED %s  %s -> %s" % (core, a, b))
    print("")
    print("-- the ON arm REACHED its target on: --")
    reached = [r for r in rows if r[9] > 0]
    print("   handoff > 0                 : %d of %d" % (len(reached), len(rows)))
    print("   of those, OFF handoff was 0  : %d" % sum(1 for r in reached if r[14] == 0))
    probed_cores = sum(1 for r in rows if r[7] > 0)
    print("   probe printed on the ON arm  : %d of %d  (a core whose loop exits"
          % (probed_cores, len(rows)))
    print("                                   before the probe block prints NOTHING,")
    print("                                   which is NOT a zero)")
    if probed_cores == 0:
        # An empty grep is not a negative result. Verified 2026-09-15: the
        # pattern `^QPROBE\s+universal\[` matches the producer's own format
        # string (`qinst_egraph.rs`, "QPROBE   universal[{index}] vars=..."),
        # and `reach-probe.sh` counted 372 and 432 such lines on real files with
        # the SAME binary. So a zero here is a statement about these 53 cores,
        # not about the instrument -- but it is printed as a warning rather than
        # as a finding, because the two look identical in the output.
        print("")
        print("   !! ZERO cores printed a per-universal probe line. The pattern is")
        print("      verified against the producer's format string and against")
        print("      `reach-probe.sh`, which counted 372 and 432 such lines with this")
        print("      same binary -- so this is a fact about the 53 cores' loop exits")
        print("      and NOT an instrument pointed at nothing. Read the handoff and")
        print("      nocontext columns as UNMEASURED here, never as zero.")
    print("")
    print("-- the ON arm's TERMINAL typed reason, bucketed --")
    for k, n in buckets.most_common():
        print("   %4d  %s" % (n, k))
    print("")
    print("-- its details, VERBATIM and unbucketed (a bucket's LABEL hides four causes) --")
    for k, n in details.most_common(12):
        print("   %4d  %s" % (n, k))
    print("")
    ran = sum(1 for r in rows if r[12] > 0)
    print("-- did the GROUND CLOSURE run on the ON arm? --")
    print("   qf-check ran                : %d of %d" % (ran, len(rows)))
    print("   max ground set handed to it : %d" % max((r[13] for r in rows), default=0))
    if args.inst_dir:
        tot = sum(r[16] for r in rows if isinstance(r[16], int))
        pre = sum(r[17] for r in rows if isinstance(r[17], int))
        print("")
        print("-- are z3's own substituted terms in OUR ground set (ON arm)? --")
        print("   instance arguments          : %d" % tot)
        print("   PRESENT                     : %d" % pre)
        print("   PRESENT is the strong direction: the dump holds whatever the run")
        print("   accumulated before its deadline, so load can only move a row from")
        print("   PRESENT to ABSENT. The ABSENT column is a LOWER BOUND.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
