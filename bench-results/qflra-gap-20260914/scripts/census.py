#!/usr/bin/env python3
"""Aggregate the QF_LRA census, splitting every give-up label BEFORE counting.

Rule R1: four cause channels exist and only the first is a give-up string.

  1. `; give-up kind=... detail=...`     (stdout, trace arm)
  2. the verdict line                    (sat/unsat/unknown)
  3. the process exit status             (134 = abort, 124 = wall kill)
  4. stderr                              (allocation failure prints ONLY here)

Channel 4 emits NO give-up line, so a census over channel 1 alone silently
loses it.  That is this division's largest bucket.

Two pre-committed splits, both because the label is known to cover more than
one site:

  * `kind=Timeout` is COMPOUND.  `auto.rs` relabels a reduced solve's own
    `Unknown` as "preprocessed dispatch timeout after reduced solve; the
    reduced solve's own reason was [{kind}] {detail}".  The detail CONTAINS
    `;` -- the ADR-2020 separator trap exactly.  We split on the bracketed
    inner kind and count THAT.  A row counts as a clock only when it has no
    inner reason.

  * `bound_by` comes from the route trail, never from the give-up text.  A
    give-up sentence names the route that produced the sentence; the trail
    names where the ladder actually stopped and how many rungs ran.
    `attempts=` is checked against ladder length before any bucket is called
    a blocker (a census can measure the ladder, not the solver).

Usage: census.py <logdir-glob-root> <census-tsv...>
"""

import hashlib
import json
import re
import statistics
import sys
from collections import Counter, defaultdict
from pathlib import Path

BUDGET_MS = 24_000

RELABEL = "preprocessed dispatch timeout after reduced solve; the reduced solve's own reason was "
INNER = re.compile(r"^\[(?P<kind>[A-Za-z]+)\]\s*(?P<detail>.*)$", re.S)
GIVEUP = re.compile(r"^; give-up kind=(?P<kind>\S+) detail=(?P<detail>.*)$", re.S)
ROUTE = re.compile(r"^; route (?P<body>.*)$")


def norm(detail: str) -> str:
    """Collapse the instance-specific numbers so a CAUSE is one bucket.

    Without this every refusal is its own bucket (each prints its own atom
    count / MiB figure) and the census degenerates into a list of files.
    """
    d = re.sub(r"\d+", "N", detail)
    return re.sub(r"\s+", " ", d).strip()[:160]


def split_giveup(raw: str):
    """-> (outer_kind, inner_kind, cause) applying the compound-label split."""
    m = GIVEUP.match(raw.strip())
    if not m:
        return None, None, None
    outer, detail = m.group("kind"), m.group("detail").strip()
    if detail.startswith(RELABEL):
        rest = detail[len(RELABEL):].strip()
        im = INNER.match(rest)
        if im:
            # The BINDING cause is the inner one; the outer `Timeout` is the
            # relabel, not the reason.
            return outer, im.group("kind"), norm(im.group("detail"))
        # Relabel present but carrying nothing: a genuine clock.
        return outer, "NO-INNER-REASON", "<relabel carried no inner reason>"
    return outer, None, norm(detail)


def main() -> int:
    logroot = Path(sys.argv[1])
    rows = []
    for tsv in sys.argv[2:]:
        with open(tsv) as fh:
            head = fh.readline().rstrip("\n").split("\t")
            for line in fh:
                rows.append(dict(zip(head, line.rstrip("\n").split("\t"))))

    for r in rows:
        key = hashlib.sha1(r["file"].encode()).hexdigest()[:12]
        r["key"] = key
        out = None
        for sh in logroot.glob(f"sh*/{key}.T.out"):
            out = sh.read_text(errors="replace")
            break
        r["trace"] = out or ""
        # Channel 1, split.
        gl = [ln for ln in r["trace"].splitlines() if ln.startswith("; give-up")]
        r["giveups"] = [split_giveup(ln) for ln in gl]
        # Route trail (authority for WHERE the ladder stopped).
        r["attempts"] = r["bound_by"] = r["decided_by"] = r["last"] = "NONE"
        for ln in r["trace"].splitlines():
            m = ROUTE.match(ln)
            if m:
                for kv in m.group("body").split():
                    k, _, v = kv.partition("=")
                    if k in ("attempts", "bound_by", "decided_by", "last"):
                        r[k] = v
        r["trail"] = []
        for ln in r["trace"].splitlines():
            if ln.startswith("; route-trail "):
                try:
                    r["trail"] = json.loads(ln[len("; route-trail "):])["attempts"]
                except Exception:
                    pass
        # `; lazy-smt ...` carries the theory-side shape: how many LRA atoms the
        # query actually has, and what the online CDCL(T) probe did with them.
        # This is what decides whether a file is refused by the ADMISSION screen
        # (a bound we set) or by the SEARCH (a capability we lack).
        r["atoms"] = r["online_probe"] = "NONE"
        for k in ("cube_matrices", "cube_simplex_calls", "cube_fm_ms",
                  "cube_simplex_ms", "cube_collect_ms", "cube_fm_declines"):
            r[k] = "NONE"
        for ln in r["trace"].splitlines():
            if ln.startswith("; lazy-smt "):
                for kv in ln.split():
                    k, _, v = kv.partition("=")
                    if k in r or k in ("atoms", "online_probe"):
                        r[k] = v

    print(f"rows={len(rows)}")

    # ---- the population of record is the PLAIN arm (competition-identical) ----
    dec = [r for r in rows if r["P"] in ("sat", "unsat")]
    und = [r for r in rows if r["P"] not in ("sat", "unsat")]
    print(f"\n== population, PLAIN arm (competition-identical) ==")
    print(f"decided={len(dec)}  undecided={len(und)}")
    print("  " + str(Counter(r["P"] for r in rows)))

    # Does --trace perturb the population?  Measured, not assumed.
    tdec = sum(1 for r in rows if r["T"] in ("sat", "unsat"))
    disagree = [r for r in rows if (r["T"] in ("sat", "unsat")) != (r["P"] in ("sat", "unsat"))]
    print(f"\n== --trace perturbation ==")
    print(f"trace-arm decided={tdec}  plain-arm decided={len(dec)}  rows differing={len(disagree)}")
    for r in disagree:
        print(f"    {r['P']}/{r['T']}  {r['file'].split('QF_LRA/')[-1]}")

    # ---- CHANNEL SPLIT over the undecided ----
    def bucket(r):
        # Channel 3+4 first: an abort emits NO give-up line, so a census that
        # asked channel 1 first would mislabel it.
        rc = r["P_rc"]
        if rc == "134" or "memory allocation of" in r["stderr1"]:
            return ("ABORT/oom", "process aborted: " + norm(r["stderr1"]))
        if rc == "124":
            return ("KILL/wall", "killed by the outer wall clock, no verdict")
        if rc not in ("0",):
            return (f"EXIT/{rc}", norm(r["stderr1"]))
        gs = [g for g in r["giveups"] if g[0]]
        if not gs:
            return ("SILENT", "verdict `unknown` with NO give-up line")
        outer, inner, cause = gs[-1]
        # SECOND SPLIT, forced by the first pass.
        #
        # "lra: Fourier-Motzkin elimination exceeded the wall-clock / size
        # budget" is ONE string at `lra.rs:159` standing for EVERY
        # `Decision::TimedOut` out of `decide_within` -- and `decide_within`
        # returns `TimedOut` for an i128 OVERFLOW, for the deadline in the
        # multiplier loop, for the simplex, AND for the elimination.  The
        # which-matrix probe measured `cube_matrices=0` with
        # `cube_simplex_ms=46356` on a file wearing this label, so the label is
        # NOT the binding engine and counting it as written would attribute a
        # simplex cost to Fourier-Motzkin.
        #
        # The engines' own counters are the discriminator: they are incremented
        # by the engines themselves, so they cannot agree with a wrong guess.
        if "Fourier" in cause:
            mats = r["cube_matrices"]
            calls = r["cube_simplex_calls"]
            if mats.isdigit() and int(mats) > 0:
                return (f"{outer}/{inner}", "FM elimination ran (cube_matrices>0) and spent the budget")
            if calls.isdigit() and int(calls) > 0:
                return (f"{outer}/{inner}",
                        "DENSE SIMPLEX spent the budget (cube_simplex_calls>0, cube_matrices=0) "
                        "-- the `Fourier-Motzkin` label is WRONG")
            return (f"{outer}/{inner}",
                    "neither engine ran (cube_matrices=0, cube_simplex_calls=0) "
                    "-- collection/overflow/deadline before either")
        return (f"{outer}/{inner or '-'}", cause)

    groups = defaultdict(list)
    for r in und:
        groups[bucket(r)].append(r)

    print(f"\n== R1 census of the {len(und)} undecided rows, causes split before counting ==")
    print(f"{'n':>4} {'med_ms':>7} {'>=90%budget':>11}  bucket / cause")
    for (b, cause), rs in sorted(groups.items(), key=lambda kv: -len(kv[1])):
        ms = sorted(int(r["P_ms"]) for r in rs)
        at_budget = sum(1 for m in ms if m >= 0.9 * BUDGET_MS)
        print(f"{len(rs):>4} {statistics.median(ms):>7.0f} {at_budget:>11}  [{b}] {cause}")

    # ---- R2: refusal vs exhausted clock ----
    print(f"\n== R2 refusals vs exhausted clocks, over the {len(und)} undecided ==")
    refus = [r for r in und if int(r["P_ms"]) < 0.9 * BUDGET_MS]
    clock = [r for r in und if int(r["P_ms"]) >= 0.9 * BUDGET_MS]
    for name, rs in (("REFUSAL (< 90% of budget)", refus), ("CLOCK (>= 90% of budget)", clock)):
        if not rs:
            print(f"  {name}: 0")
            continue
        ms = sorted(int(r["P_ms"]) for r in rs)
        print(f"  {name}: n={len(rs)} ({100*len(rs)/len(und):.1f}%) "
              f"min={ms[0]} p25={ms[len(ms)//4]} med={statistics.median(ms):.0f} "
              f"p75={ms[3*len(ms)//4]} max={ms[-1]}")

    # ---- ladder reach: a census can measure the ladder, not the solver ----
    print(f"\n== ladder reach over the undecided (attempts=, from the route trail) ==")
    print("  " + str(Counter(r["attempts"] for r in und)))
    print(f"  bound_by: {Counter(r['bound_by'] for r in und).most_common()}")

    # ---- the admission question, measured rather than modelled ----
    #
    # NOT bucketed by atom count.  It is tempting, because the constant the
    # default budget is calibrated to reproduce is an ATOM cap
    # (`MAX_ONLINE_LRA_ATOMS = 1_024`) and the doc quotes "13 107 atoms at
    # 8 GiB".  But `NormalizationLimits::for_budget` charges the budget in
    # COEFFICIENT WORK, not atoms -- that is the whole point of ADR-1752, since
    # 23 385 atoms over few variables cost less than 1 492 over 700.  An atom
    # bucket would therefore be a proxy for a gate that does not read atoms,
    # and a bucket built on a proxy is exactly the "do not build against the
    # label" failure.  `online_probe` is the screen's OWN report of what it did,
    # so it is counted instead, and atoms are reported descriptively only.
    print(f"\n== online-LRA admission, over the undecided ==")
    print(f"  online_probe (the screen's own report): "
          f"{Counter(r['online_probe'] for r in und).most_common()}")
    ats = sorted(int(r["atoms"]) for r in und if r["atoms"].isdigit())
    if ats:
        print(f"  atoms (DESCRIPTIVE -- the gate is coefficient work, not this): "
              f"n={len(ats)} min={ats[0]} med={statistics.median(ats):.0f} max={ats[-1]}")
    print(f"  rows with NO lazy-smt line at all (never reached the theory): "
          f"{sum(1 for r in und if r['atoms'] == 'NONE')}")

    # ---- per-row artifact, so the ADR cites rows rather than a summary ----
    out = Path(sys.argv[1]).parent / "out" / "census-rows.tsv"
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w") as fh:
        fh.write("file\tverdict\trc\tms\trss_kb\tstatus\tbucket\tcause\t"
                 "attempts\tbound_by\tatoms\tonline_probe\tcube_matrices\tcube_simplex_calls\n")
        for r in sorted(rows, key=lambda x: x["file"]):
            b, cause = bucket(r) if r in und else ("DECIDED", "-")
            fh.write("\t".join([
                r["file"].split("non-incremental/")[-1], r["P"], r["P_rc"], r["P_ms"],
                r["P_rss"], r["status"], b, cause, r["attempts"], r["bound_by"],
                r["atoms"], r["online_probe"], r["cube_matrices"], r["cube_simplex_calls"],
            ]) + "\n")
    print(f"\nper-row artifact: {out}")

    # ---- peak RSS ----
    print(f"\n== peak RSS (KB) over the undecided ==")
    rss = sorted(int(r["P_rss"]) for r in und if r["P_rss"].isdigit())
    if rss:
        print(f"  n={len(rss)} med={statistics.median(rss):.0f} p90={rss[int(.9*len(rss))]} max={rss[-1]}")
        print(f"  rows over 4 GiB: {sum(1 for v in rss if v > 4*1024*1024)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
