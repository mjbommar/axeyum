#!/usr/bin/env python3
"""Where the budget went, per file, from a `scripts/trace-sweep.sh` directory.

Written 2026-09-08 to answer that for the 22 `QF_LRA` files that print no
`; theory-layer` line and the 27 `QF_LIA` losses. The raw output of that
run is in `bench-results/watchdog-blind-files-20260908/`.

Reads a sweep directory produced by `.lane-sweep.sh` and answers, per file:

  path      did the run RETURN (soft stop inside the solve) or was it killed by
            the watchdog?  Only the second family could lose an instrument.
  bound_by  which route consumed the budget, and its share of the total.
  theory    did a `; theory-layer` line print at all -- complete, partial, or
            neither -- and if neither, which route was binding instead.
  lia       the integer-route group readings, kept distinct from zero.
  crossed   which configuration bound actually BIT.

Nothing here derives a rate from a partial reading: every `; partial` counter is
a lower bound, so they are reported as-is and never divided.
"""

import collections
import json
import os
import re
import sys


def parse_log(path):
    text = open(path, encoding="utf-8", errors="replace").read()
    rec = {
        "watchdog": "; partial at=watchdog-kill" in text,
        "verdict": None,
        "theory": "absent",
        "lia": "absent",
        "config": "absent",
        "crossed": [],
        "consulted": 0,
        "bound_by": None,
        "bound_ms": None,
        "total_ms": None,
        "decided_by": None,
        "attempts": None,
        "trail": [],
        "bv_stage": None,
        "give_up": None,
        "lia_groups": None,
        "lazy": None,
        "route_open": None,
    }
    for line in text.splitlines():
        if line in ("sat", "unsat", "unknown"):
            rec["verdict"] = line
        # The 'unavailable' test comes FIRST: '; theory-layer unavailable: ...'
        # also starts with '; theory-layer ', so testing the complete form first
        # counted an explicit ABSENCE as a complete reading. It did, on the one
        # watchdog file in the QF_LRA population, before this was fixed.
        elif line.startswith("; theory-layer unavailable"):
            rec["theory"] = "unavailable"
        elif line.startswith("; partial theory-layer "):
            rec["theory"] = "partial"
        elif line.startswith("; theory-layer "):
            rec["theory"] = "complete"
        elif line.startswith("; lia ") or line.startswith("; partial lia "):
            rec["lia"] = "partial" if line.startswith("; partial") else "complete"
            rec["lia_groups"] = {
                k: v
                for k, v in re.findall(r"\b(offline|theory|propagation)=(\S+)", line)
            }
            rec["lia_fields"] = dict(re.findall(r"\b(\w+)=(\d+)\b", line))
        elif line.startswith("; config ") or line.startswith("; partial config "):
            rec["config"] = "partial" if line.startswith("; partial") else "complete"
            m = re.search(r" consulted=(\d+)", line)
            rec["consulted"] = int(m.group(1)) if m else 0
            crossed = re.search(r" crossed=\d+ (.*)$", line)
            if crossed:
                rec["crossed"] = re.findall(r"(\S+?)=(\d+)/(\d+)", crossed.group(1))
        elif line.startswith("; route ") or line.startswith("; partial route "):
            for key in ("decided_by", "bound_by", "bound_ms", "total_ms", "attempts"):
                m = re.search(rf"\b{key}=(\S+)", line)
                if m:
                    rec[key] = m.group(1)
        elif "route-trail " in line:
            try:
                blob = json.loads(line.split("route-trail ", 1)[1])
                rec["trail"] = [
                    (a["route"], a.get("reason", a.get("outcome", "")),
                     a["elapsed_ns"] / 1e6)
                    for a in blob["attempts"]
                ]
            except (ValueError, KeyError):
                pass
        elif line.startswith("; lazy-smt ") or line.startswith("; partial lazy-smt "):
            rec["lazy"] = dict(re.findall(r"\b(\w+)=(\S+)", line))
            rec["lazy_partial"] = line.startswith("; partial")
        elif line.startswith("; partial route-open "):
            rec["route_open"] = dict(
                re.findall(r"\b(ms|after|attributed_ms)=(\S+)", line)
            )
        elif line.startswith("; partial bv-stage "):
            rec["bv_stage"] = line.split("in=", 1)[1].split()[0]
        elif line.startswith("; give-up "):
            rec["give_up"] = line
    return rec


def main(sweep_dir, label):
    index = os.path.join(sweep_dir, "index.tsv")
    rows = []
    with open(index, encoding="utf-8") as fh:
        next(fh)
        for line in fh:
            n, path, verdict, wall = line.rstrip("\n").split("\t")
            log = os.path.join(sweep_dir, f"{n}.log")
            rec = parse_log(log)
            rec["file"] = path
            rec["wall_ms"] = int(wall)
            rec["index_verdict"] = verdict
            rows.append(rec)

    print(f"\n{'=' * 78}\n{label}: {len(rows)} files\n{'=' * 78}")

    watchdog = [r for r in rows if r["watchdog"]]
    print(f"\ntook the WATCHDOG path (worker never returned): "
          f"{len(watchdog)} of {len(rows)}")
    print("returned normally (soft stop inside the solve): "
          f"{len(rows) - len(watchdog)}")

    print("\n-- instrument presence --")
    for field in ("theory", "lia", "config"):
        c = collections.Counter(r[field] for r in rows)
        print(f"  {field:8s} {dict(c)}")

    print("\n-- which route consumed the budget (bound_by) --")
    for route, n in collections.Counter(
        r["bound_by"] or "none" for r in rows
    ).most_common():
        share = []
        for r in rows:
            if (r["bound_by"] or "none") == route and r["bound_ms"] and r["total_ms"]:
                try:
                    share.append(int(r["bound_ms"]) / max(int(r["total_ms"]), 1))
                except ValueError:
                    pass
        avg = f"{sum(share) / len(share):.0%}" if share else "n/a"
        print(f"  {route:36s} {n:3d} files, mean share of total {avg}")

    print("\n-- theory-layer absent: what was binding instead --")
    blind = [r for r in rows if r["theory"] == "absent"]
    for route, n in collections.Counter(
        r["bound_by"] or "none" for r in blind
    ).most_common():
        print(f"  {route:36s} {n:3d} of {len(blind)} still-silent files")

    print("\n-- configuration bounds that actually CROSSED --")
    crossed = collections.Counter()
    for r in rows:
        for key, obs, bound in r["crossed"]:
            crossed[f"{key} (bound {bound})"] += 1
    if crossed:
        for key, n in crossed.most_common():
            print(f"  {key:70s} {n:3d} files")
    else:
        print("  none crossed on any file")

    print("\n-- per file --")
    hdr = (f"{'file':52s} {'wall':>6s} {'verdict':8s} {'path':9s} "
           f"{'theory':10s} {'bound_by':26s} {'share':>6s}")
    print(hdr)
    print("-" * len(hdr))
    for r in sorted(rows, key=lambda r: -r["wall_ms"]):
        share = ""
        if r["bound_ms"] and r["total_ms"]:
            try:
                share = f"{int(r['bound_ms']) / max(int(r['total_ms']), 1):.0%}"
            except ValueError:
                share = ""
        print(
            f"{os.path.basename(r['file'])[:52]:52s} "
            f"{r['wall_ms']:6d} {str(r['index_verdict'])[:8]:8s} "
            f"{'watchdog' if r['watchdog'] else 'returned':9s} "
            f"{r['theory']:10s} {str(r['bound_by'])[:26]:26s} {share:>6s}"
        )

    lazy = [r for r in rows if r["lazy"]]
    if lazy:
        print("\n-- the lazy-SMT refinement loop: where a round's time goes --")
        hdr2 = (
            f"{'file':38s} {'rounds':>6s} {'wall':>6s} {'skel_ms':>8s} "
            f"{'theory_ms':>9s} {'core_ms':>8s} {'acct%':>6s} "
            f"{'ms/round':>8s} {'clause':>6s} {'atoms':>6s}"
        )
        print(hdr2)
        print("-" * len(hdr2))
        for r in sorted(lazy, key=lambda r: -int(r["lazy"].get("theory_ms", 0))):
            g = r["lazy"]
            rounds = int(g.get("lra_rounds", 0)) + int(g.get("nra_rounds", 0))
            skel = int(g.get("skeleton_ms", 0))
            thy = int(g.get("theory_ms", 0))
            clauses = int(g.get("blocking_clauses", 0))
            lits = int(g.get("blocking_literals", 0))
            core_ms = int(g.get("core_ms", 0))
            acct = skel + thy + core_ms
            per = f"{acct / rounds:.0f}" if rounds else "-"
            # Share of the file's WALL CLOCK the three stages account for. The
            # point of the `core_ms` field is that this used to read ~50%, and
            # a diagnosis that cannot say where half the budget went is an
            # invitation for the next reader to guess.
            covered = f"{acct / max(r['wall_ms'], 1):.0%}"
            width = f"{lits / clauses:.1f}" if clauses else "-"
            print(
                f"{os.path.basename(r['file'])[:38]:38s} "
                f"{rounds:6d} {r['wall_ms']:6d} {skel:8d} {thy:9d} {core_ms:8d} "
                f"{covered:>6s} {per:>8s} {width:>6s} {g.get('atoms', '-'):>6s}"
            )
        rounds_all = sum(
            int(r["lazy"].get("lra_rounds", 0)) + int(r["lazy"].get("nra_rounds", 0))
            for r in lazy
        )
        skel_all = sum(int(r["lazy"].get("skeleton_ms", 0)) for r in lazy)
        thy_all = sum(int(r["lazy"].get("theory_ms", 0)) for r in lazy)
        core_all = sum(int(r["lazy"].get("core_ms", 0)) for r in lazy)
        wall_all = sum(r["wall_ms"] for r in lazy)
        acct_all = skel_all + thy_all + core_all
        print(
            f"\n  totals over {len(lazy)} files: rounds={rounds_all}, "
            f"wall {wall_all} ms, accounted {acct_all} ms "
            f"({acct_all / max(wall_all, 1):.0%} of wall)"
        )
        print(
            f"    skeleton (SAT)      {skel_all:8d} ms  "
            f"{skel_all / max(acct_all, 1):5.1%} of accounted"
        )
        print(
            f"    theory check        {thy_all:8d} ms  "
            f"{thy_all / max(acct_all, 1):5.1%} of accounted"
        )
        print(
            f"    Farkas core         {core_all:8d} ms  "
            f"{core_all / max(acct_all, 1):5.1%} of accounted"
        )

    open_seg = [r for r in rows if r["route_open"]]
    if open_seg:
        print("\n-- partial route readings: is `bound_by` the answer? --")
        wrong = [
            r
            for r in open_seg
            if int(r["route_open"]["ms"]) > int(r["route_open"]["attributed_ms"])
        ]
        print(
            f"  `bound_by` is NOT the answer on {len(wrong)} of {len(open_seg)} "
            f"partial route readings (the open segment exceeds everything every "
            f"recorded attempt accounts for)"
        )
        for r in open_seg:
            o = r["route_open"]
            print(
                f"    {os.path.basename(r['file'])[:44]:44s} "
                f"open={o['ms']:>7s} ms  attributed={o['attributed_ms']:>6s} ms  "
                f"after={o['after']}"
            )

    if label.startswith("QF_LIA"):
        print("\n-- integer-route group readings (never a bare zero) --")
        for r in sorted(rows, key=lambda r: -r["wall_ms"]):
            g = r["lia_groups"]
            if not g:
                print(f"{os.path.basename(r['file'])[:52]:52s}  no ';' lia line")
                continue
            f = r.get("lia_fields", {})
            print(
                f"{os.path.basename(r['file'])[:52]:52s}  "
                f"offline={g.get('offline'):12s} calls={f.get('offline_calls', '-'):>8s} "
                f"bnb_nodes={f.get('bnb_nodes', '-'):>8s} "
                f"simplex_pivots={f.get('simplex_pivots', '-'):>9s} "
                f"theory={g.get('theory'):12s} asserts={f.get('theory_asserts', '-'):>8s} "
                f"arena_clones={f.get('arena_clones', '-'):>8s}"
            )

    return rows


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
