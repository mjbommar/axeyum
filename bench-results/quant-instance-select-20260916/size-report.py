#!/usr/bin/env python3
"""Sizing for lane QUANT-INSTANCE-SELECT (ADR-2133).

Reads the per-core captures of the instrumented sizing sweep (`AXEYUM_QPROBE`
plus `AXEYUM_QGROUNDDUMP`, release `smtcomp_cli --trace`, 24 s / 8 GiB, s6
pinned core pairs) over ADR-2113's 53 reference-minimal UFLIA cores, and joins
them with z3's own per-core `:max-generation` from `ref-cores.tsv`.

The question it answers, and the reason it runs BEFORE any code change: the
generation-ordered, per-round-capped, eager/lazy deferred admission this lane
was briefed to build ALREADY EXISTS in `qinst_egraph.rs` (`TermGenerations`,
`budget_flood_slice`, `FLOOD_ROUND_ADMISSION_CAP`, `FLOOD_EAGER_GENERATION_MAX`)
and is gated behind `FLOOD_THROTTLE_MIN_GROUND = 2048`. So the sizing has to
say whether that gate is even reached on this population, and what generation
z3's refutations actually need against the one generation ceiling we apply
(`FLOOD_FINAL_SUBSET_MAX_GENERATION = 1`).

Usage: size-report.py [SWEEP_DIR]
"""

import collections
import csv
import os
import re
import sys

BASE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(BASE))
LANE = "/nas3/data/axeyum/lanes/quant-instance-select"
# Arm 0: `AXEYUM_QPROBE` only -- the historical probe, byte for byte, and the
# arm that carries the ground DUMPS (generations).
SWEEP = sys.argv[1] if len(sys.argv) > 1 else os.path.join(LANE, "size0")
# Arm 1: `AXEYUM_QPROBE_CENSUS` as well. It exists because
# `census.flood_slices += usize::from(census.enabled)` -- EVERY `flood_*` and
# `rej_*` counter is hard-zero without that second variable, so arm 0 can only
# report their ABSENCE. Reading arm 0's zeros as "the throttle never engaged"
# was wrong by 14 cores; this is the arm that says what it did.
CENSUS = sys.argv[2] if len(sys.argv) > 2 else os.path.join(LANE, "size1")

VERDICT = re.compile(r"^(sat|unsat|unknown)$", re.M)
QPROBE = re.compile(
    r"QPROBE egraph-fixpoint round=(\d+) ground=(\d+) .*?"
    r"releases=(\d+) releases_at_throttle=(\d+) flood_slices=(\d+) "
    r"flood_eager_kept=(\d+) flood_deep_seen=(\d+)"
)
REJ = re.compile(r"rej_(\w+)=(\d+)")

# Filled by `collect_census()` before `collect()` runs.
CENSUS_ROWS: dict = {}


def read_ref():
    path = os.path.join(REPO, "bench-results/uflia-trace-20260915/ref/ref-cores.tsv")
    with open(path) as fh:
        return {r["core"]: r for r in csv.DictReader(fh, delimiter="\t")}


def read_dump(path):
    """Generation histogram of the LAST GROUNDDUMP block in `path`."""
    if not os.path.exists(path):
        return None, None, None
    blocks, cur = [], None
    with open(path, errors="replace") as fh:
        for line in fh:
            if line.startswith("GROUNDDUMP begin"):
                m = re.search(r"reason=(\S+) count=(\d+)", line)
                cur = {
                    "gens": collections.Counter(),
                    "n": int(m.group(2)) if m else 0,
                    "reason": m.group(1) if m else None,
                }
            elif line.startswith("GROUND ") and cur is not None:
                m = re.match(r"GROUND \d+ gen=(\d+) ", line)
                if m:
                    cur["gens"][int(m.group(1))] += 1
            elif line.startswith("GROUNDDUMP end") and cur is not None:
                blocks.append(cur)
                cur = None
    if not blocks:
        return None, None, None
    b = blocks[-1]
    return b["gens"], b["n"], b["reason"]


def collect_census():
    """Per-core `flood_*` and `rej_*` counters from the census arm."""
    out = {}
    if not os.path.isdir(CENSUS):
        return out
    for shard in sorted(os.listdir(CENSUS)):
        capdir = os.path.join(CENSUS, shard, "cap")
        if not os.path.isdir(capdir):
            continue
        for name in sorted(os.listdir(capdir)):
            with open(os.path.join(capdir, name), errors="replace") as fh:
                text = fh.read()
            qp = QPROBE.findall(text)
            rj = collections.Counter()
            for key, val in REJ.findall(text):
                rj[key] += int(val)
            base = name[:-4] if name.endswith(".txt") else name
            out[base] = dict(
                releases=int(qp[-1][2]) if qp else None,
                at_throttle=int(qp[-1][3]) if qp else None,
                flood_slices=int(qp[-1][4]) if qp else None,
                eager_kept=int(qp[-1][5]) if qp else None,
                deep_seen=int(qp[-1][6]) if qp else None,
                rej=rj,
            )
    return out


def collect(ref):
    rows = []
    for shard in sorted(os.listdir(SWEEP)):
        capdir = os.path.join(SWEEP, shard, "cap")
        if not os.path.isdir(capdir):
            continue
        for name in sorted(os.listdir(capdir)):
            with open(os.path.join(capdir, name), errors="replace") as fh:
                text = fh.read()
            verdicts = VERDICT.findall(text)
            qp = QPROBE.findall(text)
            # The sweep writes `cap/<core>.txt` and `dump/<core>.dump`, so the
            # capture's own `.txt` suffix has to come off first. Getting this
            # wrong silently reports every core as having no dump, because the
            # QPROBE fixpoint line is a fallback source for `ground`.
            base = name[:-4] if name.endswith(".txt") else name
            gens, ground_n, reason = read_dump(os.path.join(SWEEP, shard, "dump", base + ".dump"))
            gens = gens or collections.Counter()
            rj = collections.Counter()
            for key, val in REJ.findall(text):
                rj[key] += int(val)
            r = ref.get(base, {})
            cz = CENSUS_ROWS.get(base, {})
            rjc = cz.get("rej", collections.Counter())
            rows.append(
                dict(
                    core=name,
                    verdict=verdicts[-1] if verdicts else "NONE",
                    z3_maxgen=r.get("z3_maxgen", "?"),
                    z3_qinst=r.get("z3_qinst", "?"),
                    proof_qinst=r.get("proof_qinst", "?"),
                    ground=ground_n if ground_n is not None else (int(qp[-1][1]) if qp else None),
                    dump_reason=reason,
                    gens=gens,
                    admitted=sum(v for g, v in gens.items() if g >= 1),
                    gen0=gens.get(0, 0),
                    gen1=gens.get(1, 0),
                    gen2plus=sum(v for g, v in gens.items() if g >= 2),
                    maxgen_ours=max(gens) if gens else None,
                    # From the CENSUS arm: these counters do not exist in arm 0.
                    flood_slices=cz.get("flood_slices"),
                    eager_kept=cz.get("eager_kept"),
                    deep_seen=cz.get("deep_seen"),
                    at_throttle=cz.get("at_throttle"),
                    rej=rjc,
                    rej_flood=rjc.get("flood", 0),
                    rej_nocontext=rjc.get("nocontext", 0),
                    rej_ceiling=rjc.get("ceiling", 0),
                )
            )
    return rows


def report(rows):
    print(f"cores captured: {len(rows)}")
    print(f"verdicts: {dict(collections.Counter(r['verdict'] for r in rows))}")
    have = [r for r in rows if r["ground"] is not None]
    print(f"cores with a ground dump (give-up instrument fired): {len(have)} / {len(rows)}")
    print("  NOTE: the dump writes only at a give-up point, so a core our engine")
    print("  DECIDES leaves no dump. That is coverage, not a zero.")
    if have:
        gs = sorted(r["ground"] for r in have)
        print(f"ground set size: min {gs[0]} median {gs[len(gs) // 2]} max {gs[-1]}")
        ge = len([r for r in have if r["ground"] >= 2048])
        print(f"  cores reaching FLOOD_THROTTLE_MIN_GROUND=2048: {ge} / {len(have)}")
        # `flood_slices` is printed ONLY on the e-matching FIXPOINT exit, so a
        # core that exits on the clock reports no census at all. "Absent" and
        # "zero" are different findings and are counted separately here: a
        # denominator of 53 would be a measurement of the printing site, not of
        # whether the throttle engaged.
        censused = [r for r in rows if r["flood_slices"] is not None]
        eng = len([r for r in censused if r["flood_slices"]])
        thr = len([r for r in censused if r["at_throttle"]])
        print(
            f"  cores printing the admission census (fixpoint exit): {len(censused)} / {len(rows)}"
        )
        print(f"  of those, a release happened at ground >= 2048:         {thr} / {len(censused)}")
        print(f"  of those, budget_flood_slice engaged (flood_slices>0):  {eng} / {len(censused)}")
        ad = sorted(r["admitted"] for r in have)
        print(f"admitted (gen>=1) ground terms: min {ad[0]} median {ad[len(ad) // 2]} max {ad[-1]}")
        tot = collections.Counter()
        for r in have:
            tot.update(r["gens"])
        s = sum(tot.values())
        print("generation histogram, all dumped cores pooled (our ground set):")
        for g in sorted(tot):
            print(f"  gen={g}: {tot[g]} ({100 * tot[g] / s:.1f} %)")
        le1 = sum(v for g, v in tot.items() if g <= 1)
        print(
            f"  gen<=1 (all FLOOD_FINAL_SUBSET_MAX_GENERATION=1 admits to the "
            f"subset-first final check): {le1} / {s} ({100 * le1 / s:.1f} %)"
        )
        deep = [r for r in have if (r["maxgen_ours"] or 0) >= 2]
        print(f"  cores whose ground set reaches generation >= 2: {len(deep)} / {len(have)}")
    pooled = collections.Counter()
    for r in rows:
        pooled.update(r["rej"])
    total = sum(pooled.values())
    if total:
        print(f"pooled admission rejections, census arm, all {len(rows)} cores ({total}):")
        for kind, n in pooled.most_common():
            print(f"  rej_{kind}: {n} ({100 * n / total:.2f} %)")
        nonzero = len([k for k, v in pooled.items() if v])
        print(f"  nonzero reject kinds: {nonzero}  <- positive control that the census is LIVE")
        print(
            f"  ** the per-round cap's OWN share of rejected traffic is rej_flood = "
            f"{pooled['flood']} ({100 * pooled['flood'] / total:.2f} %) **"
        )
    zm = collections.Counter(r["z3_maxgen"] for r in rows)
    print("z3 :max-generation per core (authoritative, ref-cores.tsv):")
    for k in sorted(zm, key=lambda x: (not x.isdigit(), int(x) if x.isdigit() else 0)):
        print(f"  z3_maxgen={k}: {zm[k]} cores")
    n2 = sum(v for k, v in zm.items() if k.isdigit() and int(k) <= 2)
    n1 = sum(v for k, v in zm.items() if k.isdigit() and int(k) <= 1)
    print(f"  <=1: {n1}/{len(rows)}   <=2: {n2}/{len(rows)}   >=3: {len(rows) - n2}/{len(rows)}")


def write_tsv(rows):
    path = os.path.join(BASE, "sizing.tsv")
    with open(path, "w") as fh:
        w = csv.writer(fh, delimiter="\t", lineterminator="\n")
        w.writerow(
            [
                "core", "ours_verdict", "ground", "dump_reason", "admitted",
                "gen0", "gen1", "gen2plus", "ours_maxgen", "flood_slices",
                "eager_kept", "deep_seen", "rej_flood", "rej_nocontext",
                "rej_ceiling", "z3_maxgen", "z3_qinst", "proof_qinst",
            ]
        )
        for r in sorted(rows, key=lambda r: r["core"]):
            w.writerow(
                [
                    r["core"], r["verdict"],
                    "" if r["ground"] is None else r["ground"],
                    r["dump_reason"] or "", r["admitted"], r["gen0"], r["gen1"],
                    r["gen2plus"],
                    "" if r["maxgen_ours"] is None else r["maxgen_ours"],
                    "" if r["flood_slices"] is None else r["flood_slices"],
                    "" if r["eager_kept"] is None else r["eager_kept"],
                    "" if r["deep_seen"] is None else r["deep_seen"],
                    r["rej_flood"], r["rej_nocontext"], r["rej_ceiling"],
                    r["z3_maxgen"], r["z3_qinst"], r["proof_qinst"],
                ]
            )
    print(f"wrote {path}")


def main():
    global CENSUS_ROWS
    CENSUS_ROWS = collect_census()
    ref = read_ref()
    rows = collect(ref)
    if not rows:
        print(f"no captures under {SWEEP}", file=sys.stderr)
        return 2
    report(rows)
    write_tsv(rows)
    return 0


if __name__ == "__main__":
    sys.exit(main())
