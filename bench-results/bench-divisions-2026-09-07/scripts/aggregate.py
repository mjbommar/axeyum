#!/usr/bin/env python3
"""Aggregate bench-divisions per-file TSVs into a per-division stage breakdown.

Reads one or more TSVs written by run_division.sh (columns: division, file,
wall_ms, verdict, trace_line) and prints, per division:
  - file count, total wall ms
  - whether each file emitted a `; theory-layer ...` line at all (front-door
    CDCL(T) instrument coverage)
  - sum of each traced duration field, grouped into boolean-search vs
    theory-work buckets
  - fraction of total wall the traced fields account for
  - untraced remainder (ms and %)
"""
import sys
import json

# NOTE (found empirically on QF_UF, then confirmed in source): `theory_assert_ms`
# is NOT disjoint from `boolean_propagate_ms`. `cdclt.rs` `assign()` (~line 993)
# times `theory.assert()` into `time_theory_assert`, and `assign()` is called
# from *inside* `unit_propagate()` (~line 1102), which `propagate()` (~line
# 2005-2010) wraps whole into `time_boolean_propagate`. So a chunk of
# `theory_assert_ms` is counted a second time inside `boolean_propagate_ms`.
# (`assign()` is also called from `theory_propagate()`'s queue-drain, which is
# NOT nested under `boolean_propagate_ms` -- so the overlap is partial, not
# total, and cannot be subtracted precisely from a distance.) Confirmed on
# QF_UF_rushhour: boolean_propagate_ms=17655 + theory_assert_ms=18630 alone
# is 36285ms against a 24224ms wall clock for that ONE file -- summing every
# field naively is not safe. See the diary for the full trace.
#
# BOOLEAN_FIELDS is the "gross" Boolean-search stage (already includes
# whatever theory-assert time happened during unit propagation).
# THEORY_FIELDS_CONSERVATIVE excludes theory_assert_ms so the two buckets are
# non-overlapping to the best of what the source lets us prove; theory_assert
# is reported separately, unioned into neither bucket by default.
BOOLEAN_FIELDS = ["boolean_propagate_ms", "conflict_analysis_ms"]
THEORY_FIELDS_CONSERVATIVE = [
    "theory_propagate_ms", "theory_push_pop_ms",
    "theory_final_check_ms", "theory_explain_ms",
]
THEORY_ASSERT_FIELD = "theory_assert_ms"
THEORY_FIELDS = THEORY_FIELDS_CONSERVATIVE + [THEORY_ASSERT_FIELD]
ALL_MS_FIELDS = BOOLEAN_FIELDS + THEORY_FIELDS


def parse_trace_line(line):
    if not line or not line.startswith("; theory-layer"):
        return None
    fields = {}
    for tok in line.split():
        if "=" in tok:
            k, v = tok.split("=", 1)
            fields[k] = v
    return fields


def main():
    rows = []
    for path in sys.argv[1:]:
        with open(path) as f:
            f.readline()  # header
            for line in f:
                line = line.rstrip("\n")
                if not line:
                    continue
                parts = line.split("\t")
                if len(parts) < 4:
                    continue
                division, file_, wall_ms, verdict = parts[0], parts[1], parts[2], parts[3]
                trace_line = parts[4] if len(parts) > 4 else ""
                rows.append({
                    "division": division, "file": file_,
                    "wall_ms": int(wall_ms), "verdict": verdict,
                    "trace_line": trace_line,
                })

    divisions = {}
    for r in rows:
        divisions.setdefault(r["division"], []).append(r)

    report = {}
    for div, items in sorted(divisions.items()):
        n = len(items)
        total_wall = sum(r["wall_ms"] for r in items)
        traced_files = 0
        unavailable_files = 0
        no_line_files = 0
        sums = {k: 0 for k in ALL_MS_FIELDS}
        per_file = []
        for r in items:
            tf = parse_trace_line(r["trace_line"])
            entry = {"file": r["file"], "wall_ms": r["wall_ms"], "verdict": r["verdict"]}
            if r["trace_line"].startswith("; theory-layer unavailable"):
                unavailable_files += 1
                entry["theory_layer"] = "unavailable"
            elif tf is None:
                no_line_files += 1
                entry["theory_layer"] = "no_line"
            else:
                traced_files += 1
                entry["theory_layer"] = "present"
                file_traced_ms = 0
                for k in ALL_MS_FIELDS:
                    v = tf.get(k)
                    if v is not None and v.lstrip("-").isdigit():
                        sums[k] += int(v)
                        file_traced_ms += int(v)
                entry["traced_ms"] = file_traced_ms
            per_file.append(entry)

        boolean_sum = sum(sums[k] for k in BOOLEAN_FIELDS)
        theory_sum_conservative = sum(sums[k] for k in THEORY_FIELDS_CONSERVATIVE)
        theory_assert_sum = sums[THEORY_ASSERT_FIELD]
        traced_total_conservative = boolean_sum + theory_sum_conservative
        traced_total_naive = traced_total_conservative + theory_assert_sum
        frac_cons = (traced_total_conservative / total_wall * 100) if total_wall else 0.0
        frac_naive = (traced_total_naive / total_wall * 100) if total_wall else 0.0

        report[div] = {
            "files": n,
            "total_wall_ms": total_wall,
            "files_with_theory_layer_line": traced_files,
            "files_watchdog_unavailable": unavailable_files,
            "files_no_line_at_all": no_line_files,
            "boolean_search_ms": boolean_sum,
            "theory_work_ms_conservative": theory_sum_conservative,
            "theory_assert_ms_excluded_overlap": theory_assert_sum,
            "traced_total_ms": traced_total_conservative,
            "untraced_ms": total_wall - traced_total_conservative,
            "traced_fraction_pct": round(frac_cons, 1),
            "naive_traced_total_ms_DO_NOT_TRUST": traced_total_naive,
            "naive_traced_fraction_pct_DO_NOT_TRUST": round(frac_naive, 1),
            "field_sums_ms": sums,
            "per_file": per_file,
        }

    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
