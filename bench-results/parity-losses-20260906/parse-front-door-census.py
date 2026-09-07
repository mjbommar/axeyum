"""Turn a run directory of <n>.{out,err,meta} into a front-door census TSV.

TIMING MODEL (read from crates/axeyum-solver/src/auto.rs and qinst_egraph.rs;
`qtrace` prints `since.elapsed()`, so what a line means depends entirely on
which `Instant` its caller passed):

  CUMULATIVE, one shared `t0` created at the top of `finish_quantified_solve`:
      forall-exists-witness, finite-expansion, uf-fmf-probe,
      egraph (t0 forwarded as `started`), mbqi, uf-fmf-full
    -> a stage's OWN cost is its printed value minus everything already
       accounted for.  Reading the printed number as the stage's cost
       overstates it by every stage above it.

  STAGE-LOCAL, own `Instant`:
      mbqi-quick, nat-induction

  SEGMENT-LOCAL, inside the e-graph instantiation loop (sub-stages of whichever
  top-level window they fall in):
      egraph-seg (except the first two, `closed-universal done` / `targeted
      done`, which are cumulative from that call's own trace_start),
      match-seg, nested-quant
    -> summed as a sub-profile, never added to the top-level accounting.
"""

import os
import re
import sys
from collections import Counter, defaultdict

CUMULATIVE = [
    "forall-exists-witness",
    "finite-expansion",
    "uf-fmf-probe",
    "egraph",
    "mbqi",
    "uf-fmf-full",
]
LOCAL = ["mbqi-quick", "nat-induction"]
SEG = ["egraph-seg", "match-seg", "nested-quant"]
QT = re.compile(r"^\[qtrace\] (\S+) \+([0-9.]+)s (.*)$")
ROUND = re.compile(r"round=(\d+)")
GROUND = re.compile(r"ground=(\d+)")


def parse_trace(errtext, wall):
    """Returns (top_stages, accounted_ms, subprofile)."""
    top = []
    accounted = 0.0
    pending = []  # seg lines not yet assigned to a top window
    sub = defaultdict(float)
    maxround = 0
    maxground = 0
    for line in errtext.splitlines():
        m = QT.match(line.strip())
        if not m:
            continue
        name, ms, note = m.group(1), float(m.group(2)) * 1000.0, m.group(3)
        if name in SEG:
            r = ROUND.search(note)
            g = GROUND.search(note)
            if r:
                maxround = max(maxround, int(r.group(1)))
            if g:
                maxground = max(maxground, int(g.group(1)))
            key = name + ":" + note.split()[0]
            if name == "egraph-seg" and note in (
                "closed-universal done",
                "targeted done",
            ):
                pending.append((key, 0.0))  # cumulative-in-call; not summed
            else:
                pending.append((key, ms))
            continue
        if name in CUMULATIVE:
            cost = ms - accounted
            accounted = ms
        elif name in LOCAL:
            cost = ms
            accounted += ms
        else:
            cost = ms
            accounted += ms
            name += "?UNKNOWN-STAGE"
        for key, v in pending:
            sub[name + " / " + key] += v
        pending = []
        top.append((name, cost, note, line.strip()))
    for key, v in pending:  # segs after the last checkpoint (killed mid-loop)
        sub["<no closing checkpoint> / " + key] += v
    return top, accounted, sub, maxround, maxground


def classify(verdict, detail):
    if verdict.startswith("sat") or verdict.startswith("unsat"):
        return "decided(" + verdict + ")"
    if "kind=Timeout" in verdict or "kind=ResourceLimit" in verdict:
        return "search-timeout"
    if "instantiation does not reach" in detail:
        return "route-decline(residual-quantifier)"
    if "instantiation is satisfiable" in detail:
        return "other(instantiation-satisfiable)"
    if "does not transfer back through skolemization" in detail:
        return "other(skolemized-sat-not-transferable)"
    if "no universal is asserted" in detail:
        return "other(no-universal-asserted)"
    return "other(" + detail[:70] + ")"


def main(rundir, listfile, out_tsv):
    paths = [l.strip() for l in open(listfile) if l.strip()]
    rows = []
    for i, p in enumerate(paths, 1):
        meta = dict(
            l.split("\t", 1)
            for l in open(os.path.join(rundir, "%d.meta" % i)).read().splitlines()
            if "\t" in l
        )
        assert meta["path"] == p, "row %d mismatch" % i
        wall = int(meta["wall_ms"])
        rc = int(meta["exit"])
        outtxt = (
            open(os.path.join(rundir, "%d.out" % i), errors="replace").read().splitlines()
        )
        errtxt = open(os.path.join(rundir, "%d.err" % i), errors="replace").read()
        verdict = outtxt[0] if outtxt else "<no output, rc=%d>" % rc
        detail = ""
        for l in outtxt[1:]:
            if l.startswith("detail: "):
                detail = l[len("detail: ") :].strip()
        top, accounted, sub, maxround, maxground = parse_trace(errtxt, wall)
        pre = wall - accounted
        allst = top + [("pre/post-ladder", pre, "parse+QF front door+skolemize", "")]
        dom = max(allst, key=lambda r: r[1])
        subtop = sorted(sub.items(), key=lambda kv: -kv[1])[:3]
        rows.append(
            dict(
                file=os.path.basename(p),
                path=p,
                verdict=verdict,
                detail=detail,
                klass=classify(verdict, detail),
                budget_stage=dom[0],
                budget_stage_ms="%.0f" % dom[1],
                budget_stage_share="%.0f%%" % (100.0 * dom[1] / max(wall, 1)),
                wall_ms=str(wall),
                rc=str(rc),
                rounds=str(maxround),
                ground=str(maxground),
                ladder="|".join("%s=%.0fms" % (n, c) for n, c, _, _ in top)
                + "|pre/post-ladder=%.0fms" % pre,
                sub="|".join("%s=%.0fms" % (k, v) for k, v in subtop),
                evidence=dom[3]
                or "wall %d ms minus %.0f ms of traced stages" % (wall, accounted),
            )
        )
    cols = [
        "file",
        "klass",
        "budget_stage",
        "budget_stage_ms",
        "budget_stage_share",
        "wall_ms",
        "rounds",
        "ground",
        "verdict",
        "detail",
        "ladder",
        "sub",
        "evidence",
        "rc",
        "path",
    ]
    header = [
        "file",
        "class",
        "budget_stage",
        "budget_stage_ms",
        "budget_stage_share",
        "wall_ms",
        "egraph_max_round",
        "egraph_max_ground",
        "verdict",
        "detail",
        "ladder_stage_costs",
        "dominant_substages",
        "evidence_line",
        "exit",
        "path",
    ]
    with open(out_tsv, "w") as f:
        f.write("\t".join(header) + "\n")
        for r in rows:
            f.write("\t".join(r[c] for c in cols) + "\n")
    print("wrote %s: %d rows" % (out_tsv, len(rows)))
    for label, key in (
        ("class", "klass"),
        ("budget_stage", "budget_stage"),
    ):
        print("\n== " + label)
        for k, v in Counter(r[key] for r in rows).most_common():
            print("  %3d  %s" % (v, k))
    print("\n== class x budget_stage")
    for k, v in Counter((r["klass"], r["budget_stage"]) for r in rows).most_common():
        print("  %3d  %s / %s" % (v, k[0], k[1]))
    walls = sorted(int(r["wall_ms"]) for r in rows)
    print(
        "\n== wall_ms: min=%d median=%d max=%d ; files under 20 s (budget left "
        "unspent) = %d"
        % (walls[0], walls[len(walls) // 2], walls[-1], sum(1 for w in walls if w < 20000))
    )


main(*sys.argv[1:])
