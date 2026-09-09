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
    ("no combination of the asserted equations", "d_other:cas-ideal-declined"),
]

# The `; give-up` line does NOT always name the branch that returned. When the
# preprocessing wrapper's own deadline has passed it REPLACES the inner reason
# with its own text, so a query the relaxation gave up on for a structural
# reason is reported as a wrapper timeout. These texts are wrapper markers:
# the real reason is the last non-front-door route's detail in the trail.
WRAPPER_TIMEOUTS = (
    "preprocessed dispatch timeout after reduced solve",
    "auto-dispatch timeout",
)


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
    return "d_other:no-reason-recorded"


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
        "lazy": {},
        "lazy_partial": False,
    }
    for line in text.splitlines():
        if line.startswith("; lazy-smt ") or line.startswith("; partial lazy-smt "):
            rec["lazy"] = dict(re.findall(r"\b(\w+)=(\S+)", line))
            rec["lazy_partial"] = line.startswith("; partial")
        elif line.startswith("; give-up "):
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
    # The reason of record is the last NON-front-door route's detail, not the
    # `; give-up` line. Two things make the give-up line unreliable here:
    #   * every `fd:` attempt after a theory route copies that route's text, and
    #     `fd:parse` carries a probe note (`string_bound=12`) that is not a
    #     reason at all — reading the trail's literal last entry classified one
    #     file by the parser's probe string; and
    #   * the preprocessing wrapper REPLACES the inner reason with its own
    #     timeout text once its deadline has passed, so four files reported a
    #     wrapper timeout for a relaxation that had given up structurally.
    # The give-up line is kept as a fallback for a run with no usable trail.
    rec["inner_reason"] = None
    for route, _outcome, _reason, detail, _ms in reversed(rec["trail"]):
        if detail and not str(route).startswith("fd:"):
            rec["inner_reason"] = detail
            break
    rec["wrapper_masked"] = bool(
        rec["give_up"]
        and any(w in rec["give_up"] for w in WRAPPER_TIMEOUTS)
        and rec["inner_reason"]
        and rec["inner_reason"] != rec["give_up"]
    )
    rec["reason"] = rec["inner_reason"] or rec["give_up"]
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
            rec["class"] = classify(rec["reason"], rec["watchdog"])
            rows.append(rec)

    total_ms = sum(r["wall"] for r in rows)
    print(f"{len(rows)} files, {total_ms / 1000:.0f}s of wall clock\n")

    print("== verdicts ==")
    for v, c in collections.Counter(r["verdict"] for r in rows).most_common():
        print(f"  {v:10s} {c:3d}")

    masked = [r for r in rows if r["wrapper_masked"]]
    print(f"\n== give-up line masked the inner reason on {len(masked)} of "
          f"{len(rows)} files ==")
    for r in masked[:6]:
        print(f"  {os.path.basename(r['file'])[:40]:40s} printed "
              f"{r['give_up'][:38]!r} -> really {r['reason'][:44]!r}")

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

    # The budget axis, kept SEPARATE from the reason axis. A file can give up
    # for a structural reason and still have consumed the whole clock, and the
    # two questions ("why did it stop" / "did it run out") have different fixes.
    print("\n== budget axis (24s protocol) ==")
    exhausted = [r for r in rows if r["watchdog"] or r["wall"] >= 23_000]
    half = [r for r in rows
            if r not in exhausted and 10_000 <= r["wall"] <= 15_000]
    early = [r for r in rows if r["wall"] < 1_000]
    print(f"  spent the whole 24s (watchdog or >=23s) : {len(exhausted):3d}")
    print(f"  returned near HALF the budget (10-15s)  : {len(half):3d}")
    print(f"  returned in under 1s                    : {len(early):3d}")
    print(f"  everything else                         : "
          f"{len(rows) - len(exhausted) - len(half) - len(early):3d}")

    # Inside the lazy-SMT loop the budget splits between the BOOLEAN SKELETON
    # solve (enumerating cubes) and the THEORY solve (deciding one cube). Which
    # of the two dominates decides what a fix would even be, and the two are not
    # visible from any wall-clock number. Reported per file, never averaged into
    # a rate: a `; partial` reading is a lower bound.
    def as_int(rec, key):
        try:
            return int(rec["lazy"].get(key, 0))
        except ValueError:
            return 0

    lazy_rows = [r for r in rows if r["lazy"]]
    print(f"\n== inside the lazy-SMT loop ({len(lazy_rows)} files report it) ==")
    print(f"{'file':40s} {'part':>5s} {'skel_ms':>8s} {'theory_ms':>9s} "
          f"{'skel%':>6s} {'nra_rnd':>8s} {'lra_rnd':>8s} {'atoms':>7s}")
    skel_dom = 0
    for r in sorted(lazy_rows, key=lambda x: -as_int(x, "skeleton_ms")):
        skel = as_int(r, "skeleton_ms")
        thy = as_int(r, "theory_ms")
        acct = as_int(r, "accounted_ms")
        pct = f"{skel / acct:.0%}" if acct else "n/a"
        if acct and skel / acct >= 0.5:
            skel_dom += 1
        print(f"{os.path.basename(r['file'])[:40]:40s} "
              f"{'yes' if r['lazy_partial'] else 'no':>5s} {skel:8d} {thy:9d} "
              f"{pct:>6s} {as_int(r, 'nra_rounds'):8d} "
              f"{as_int(r, 'lra_rounds'):8d} {as_int(r, 'atoms'):7d}")
    print(f"  -> the BOOLEAN SKELETON is >=50% of accounted time on "
          f"{skel_dom} of {len(lazy_rows)} files")

    print("\n== per file ==")
    hdr = (f"{'file':44s} {'wall':>6s} {'nra_ms':>7s} {'rroot_ms':>8s} "
           f"{'class'}")
    print(hdr)
    print("-" * 110)
    for r in sorted(rows, key=lambda x: (x["class"], -x["wall"])):
        print(f"{os.path.basename(r['file'])[:44]:44s} {r['wall']:6d} "
              f"{r['route_ms'].get('nra', 0):7.0f} "
              f"{r['route_ms'].get('nra-real-root', 0):8.0f} {r['class']}")


if __name__ == "__main__":
    main(sys.argv[1])
