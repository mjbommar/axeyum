#!/usr/bin/env python3
"""Classify a `scripts/trace-sweep.sh` output directory into the step-1 split.

Written 2026-09-09 for the 75 `QF_NRA` parity losses in
`bench-results/parity-losses-20260908/QF_NRA.txt`, the largest single division
gap after the 2026-09-08 re-cut.

The question it answers is the one every division lane has had to answer
separately, always by hand: of the files we lose, how many do we

  (a) DECLINE before trying (an admission refusal, a shape we do not accept),
  (b) TRY and time out (the watchdog, or a deadline inside a route),
  (c) refuse on a MEMORY / SIZE bound, or
  (d) return `unknown` for some other reason?

It reads the `; give-up kind=… detail=…` line and the `; route`/`; route-trail`
attribution the CLI prints under `--trace`, so the class is derived from the
branch that actually returned, not from the wall-clock shape of the run.

    scripts/cargo-serialized.sh build --release -p axeyum-bench --example smtcomp_cli
    scripts/trace-sweep.sh <list> <out-dir> 24
    scripts/nra-loss-classify.py <out-dir>

Nothing here divides a `; partial` counter: a watchdog-killed run's counters are
lower bounds, so they are reported as-is (the `watchdog` column) and never used
as a rate.
"""

import collections
import json
import os
import re
import sys

# Each entry is (substring of the give-up detail, class). Order matters: the
# first match wins, so the specific admission texts precede the generic ones.
# Every class name is prefixed with its step-1 letter so a sort groups them.
CLASSES = [
    ("past the consuming engine's capacity", "c_size-bound:atom-capacity"),
    ("exceed the hard admission count", "c_size-bound:hard-count"),
    ("coefficient cap", "c_size-bound:coefficient-cap"),
    ("wall-clock timeout reached", "b_timeout:deadline-in-route"),
    ("auto-dispatch timeout", "b_timeout:dispatch-boundary"),
    ("branch-and-bound depth budget", "d_other:bnb-depth-budget"),
    ("could not certify", "d_other:resultant-uncertified"),
    ("refinement", "d_other:refine-fixpoint"),
]


def classify(detail, watchdog):
    """The step-1 class for one file, from the branch that returned."""
    if watchdog:
        return "b_timeout:watchdog-kill"
    d = detail or ""
    for needle, name in CLASSES:
        if needle in d:
            return name
    if d:
        return "d_other:" + d[:56]
    return "d_other:no-give-up-line"


def parse_log(path):
    """One file's trace block: give-up detail, route attribution, trail."""
    text = open(path, encoding="utf-8", errors="replace").read()
    rec = {
        "watchdog": "; partial at=watchdog-kill" in text,
        "give_up": None,
        "bound_by": None,
        "bound_ms": None,
        "total_ms": None,
        "trail": [],
        "route_ms": {},
    }
    for line in text.splitlines():
        if line.startswith("; give-up "):
            m = re.search(r"detail=(.*)$", line)
            rec["give_up"] = m.group(1) if m else line
        elif line.startswith("; route ") or line.startswith("; partial route "):
            for key in ("bound_by", "bound_ms", "total_ms"):
                m = re.search(rf"\b{key}=(\S+)", line)
                if m:
                    rec[key] = m.group(1)
        elif "route-trail " in line:
            try:
                blob = json.loads(line.split("route-trail ", 1)[1])
            except ValueError:
                continue
            for a in blob.get("attempts", []):
                ms = a.get("elapsed_ns", 0) / 1e6
                rec["trail"].append(
                    (a.get("route"), a.get("outcome"), a.get("reason", ""),
                     a.get("detail", ""), ms)
                )
                rec["route_ms"][a.get("route")] = ms
    if not rec["give_up"]:
        # A watchdog-killed run prints no `; give-up`; the trail's last detail
        # is then the nearest thing to a reason and is labelled as such.
        #
        # Only NON-front-door routes are consulted. Every `fd:` attempt after a
        # theory route COPIES that route's decline text, and `fd:parse` carries a
        # probe string (`string_bound=12`) that is not a reason at all — reading
        # the trail's literal last entry classified one file by the parser's
        # probe note. The branch that returned is always a theory route here.
        for route, _outcome, _reason, detail, _ms in reversed(rec["trail"]):
            if detail and not str(route).startswith("fd:"):
                rec["give_up"] = detail
                break
    return rec


def main(sweep_dir):
    rows = []
    with open(os.path.join(sweep_dir, "index.tsv"), encoding="utf-8") as fh:
        next(fh)
        for line in fh:
            n, path, verdict, wall = line.rstrip("\n").split("\t")
            rec = parse_log(os.path.join(sweep_dir, f"{n}.log"))
            rec["file"] = path
            rec["verdict"] = verdict
            rec["wall"] = int(wall)
            rec["class"] = classify(rec["give_up"], rec["watchdog"])
            rows.append(rec)

    total_ms = sum(r["wall"] for r in rows)
    print(f"{len(rows)} files, {total_ms / 1000:.0f}s of wall clock\n")

    print("== verdicts ==")
    for v, c in collections.Counter(r["verdict"] for r in rows).most_common():
        print(f"  {v:10s} {c:3d}")

    print("\n== STEP-1 SPLIT (from the branch that returned) ==")
    by_class = collections.defaultdict(list)
    for r in rows:
        by_class[r["class"]].append(r["wall"])
    for name in sorted(by_class, key=lambda k: -len(by_class[k])):
        w = by_class[name]
        print(f"  {name:40s} {len(w):3d} files  {sum(w) / 1000:7.1f}s "
              f"({sum(w) / total_ms:5.1%} of budget)")

    print("\n== which route consumed the budget (bound_by) ==")
    for k, c in collections.Counter(str(r["bound_by"]) for r in rows).most_common():
        print(f"  {k:30s} {c:3d}")

    print("\n== last NON-front-door route in the trail ==")
    cnt = collections.Counter()
    for r in rows:
        real = [t for t in r["trail"] if not str(t[0]).startswith("fd:")]
        cnt[real[-1][0] if real else "none"] += 1
    for k, c in cnt.most_common():
        print(f"  {k:30s} {c:3d}")

    print("\n== time inside each named route (mean over files that entered it) ==")
    per = collections.defaultdict(list)
    for r in rows:
        for route, ms in r["route_ms"].items():
            if not str(route).startswith("fd:"):
                per[route].append(ms)
    for route in sorted(per, key=lambda k: -sum(per[k])):
        v = per[route]
        print(f"  {route:24s} {len(v):3d} files  total {sum(v) / 1000:7.1f}s  "
              f"mean {sum(v) / len(v):8.0f}ms  max {max(v):8.0f}ms")

    print("\n== per file ==")
    hdr = f"{'file':46s} {'wall':>6s} {'verdict':8s} {'class'}"
    print(hdr)
    print("-" * 100)
    for r in sorted(rows, key=lambda x: (x["class"], -x["wall"])):
        print(f"{os.path.basename(r['file'])[:46]:46s} {r['wall']:6d} "
              f"{r['verdict']:8s} {r['class']}")


if __name__ == "__main__":
    main(sys.argv[1])
