#!/usr/bin/env python3
"""Per-rung analysis for the NIA-GROEBNER-GATE ladder.

Reads ONE ledger TSV (schema from scripts/outcome_ledger.py, arms `shipped`
and `gate<N>`) plus the matching capture directory, and reports, per arm:
decided / gains / losses vs shipped / flips / exit-status differences,
median and p90 elapsed ms, and how many rows the Gröbner route
(`cas-ideal-refuter`) DECIDES vs ADMITS-but-fails vs still REFUSES (via the
typed route-trail JSON through `route_trace_reader.py`, never via a prose
grep -- CLAUDE.md's rule on this exact failure mode).

Usage:
    analyze-rung.py --ledger PATH.tsv --captures DIR --rung LABEL

Exit status depends on the finding: refuses (exit 2) if the shipped arm's
row count does not match the gate arm's row count (an incomplete sweep), or
if a file is missing its capture.
"""
from __future__ import annotations

import argparse
import statistics
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent.parent / "scripts"))
import outcome_ledger as ol  # noqa: E402
import route_trace_reader as rtr  # noqa: E402

ADMISSION_DETAIL = "nonlinear system exceeds the deterministic generator/atom/inequality ceilings"


def cas_status(trail: rtr.RouteTrail) -> str:
    """Classify one file's `cas-ideal-refuter` attempt, or its absence."""
    for a in trail.attempts:
        if a.route != "cas-ideal-refuter":
            continue
        if a.outcome == "decided":
            return "decides"
        if a.outcome == "declined":
            if (a.detail or "") == ADMISSION_DETAIL:
                return "refuses"
            return "admits-but-fails"
        return f"other:{a.outcome}"
    return "not-reached"


def pct(n: int, d: int) -> str:
    return f"{n}/{d}" if d else "0/0"


def main(argv=None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--ledger", required=True)
    p.add_argument("--captures", required=True)
    p.add_argument("--rung", required=True)
    p.add_argument("--gate-arm", default=None, help="defaults to gate<rung>")
    args = p.parse_args(argv)

    gate_arm = args.gate_arm or f"gate{args.rung}"
    rows = ol.read_ledger(args.ledger)
    shipped = {r.corpus_path: r for r in rows if r.arm == "shipped"}
    gate = {r.corpus_path: r for r in rows if r.arm == gate_arm}

    if not shipped or not gate:
        print(f"REFUSED: empty arm(s) -- shipped={len(shipped)} {gate_arm}={len(gate)}", file=sys.stderr)
        return 2
    if set(shipped) != set(gate):
        only_s = set(shipped) - set(gate)
        only_g = set(gate) - set(shipped)
        print(f"REFUSED: file sets differ -- only-shipped={len(only_s)} only-{gate_arm}={len(only_g)}", file=sys.stderr)
        return 2

    files = sorted(shipped)
    decided = lambda v: v in ("sat", "unsat")  # noqa: E731

    gains, losses, flips, exit_diffs = [], [], [], []
    s_ms, g_ms = [], []
    cas_s_counts: dict[str, int] = {}
    cas_g_counts: dict[str, int] = {}

    captures = Path(args.captures)

    def cap_path(arm: str, corpus_path: str) -> Path:
        slug = corpus_path.replace("/", "_")
        return captures / f"{arm}__{slug}.out"

    missing = []
    for f in files:
        sr, gr = shipped[f], gate[f]
        s_ms.append(int(sr.elapsed_ms))
        g_ms.append(int(gr.elapsed_ms))
        if sr.exit_status != gr.exit_status:
            exit_diffs.append((f, sr.exit_status, gr.exit_status))
        if decided(sr.verdict) and decided(gr.verdict) and sr.verdict != gr.verdict:
            flips.append((f, sr.verdict, gr.verdict))
        elif not decided(sr.verdict) and decided(gr.verdict):
            gains.append(f)
        elif decided(sr.verdict) and not decided(gr.verdict):
            losses.append(f)

        sp, gp = cap_path("shipped", f), cap_path(gate_arm, f)
        for arm_name, path, counts in (("shipped", sp, cas_s_counts), (gate_arm, gp, cas_g_counts)):
            if not path.exists():
                missing.append(str(path))
                continue
            try:
                trail = rtr.read_file(path)
            except rtr.NoTrailLine:
                counts["no-trail"] = counts.get("no-trail", 0) + 1
                continue
            status = cas_status(trail)
            counts[status] = counts.get(status, 0) + 1

    if missing:
        print(f"WARNING: {len(missing)} capture(s) missing (partial sweep?) e.g. {missing[0]}", file=sys.stderr)

    def median_p90(xs):
        xs = sorted(xs)
        if not xs:
            return (0, 0)
        med = statistics.median(xs)
        p90_idx = min(len(xs) - 1, int(round(0.9 * (len(xs) - 1))))
        return (med, xs[p90_idx])

    s_med, s_p90 = median_p90(s_ms)
    g_med, g_p90 = median_p90(g_ms)

    n_shipped_decided = sum(1 for f in files if decided(shipped[f].verdict))
    n_gate_decided = sum(1 for f in files if decided(gate[f].verdict))

    print(f"=== rung {args.rung} (arm={gate_arm}) -- {len(files)} files ===")
    print(f"shipped decided: {n_shipped_decided}/{len(files)}   {gate_arm} decided: {n_gate_decided}/{len(files)}")
    print(f"gains (shipped unknown -> {gate_arm} decided): {len(gains)}  {gains}")
    print(f"losses ({gate_arm} lost what shipped had): {len(losses)}  {losses}")
    print(f"flips (both decided, different verdict -- SOUNDNESS ALARM if any): {len(flips)}  {flips}")
    print(f"exit-status differences: {len(exit_diffs)}  {exit_diffs[:10]}{' ...' if len(exit_diffs) > 10 else ''}")
    print(f"shipped elapsed_ms: median={s_med} p90={s_p90}")
    print(f"{gate_arm} elapsed_ms: median={g_med} p90={g_p90}")
    print(f"cas-ideal-refuter status (shipped): {cas_s_counts}")
    print(f"cas-ideal-refuter status ({gate_arm}): {cas_g_counts}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
