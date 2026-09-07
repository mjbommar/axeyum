#!/usr/bin/env python3
"""Render the aggregate.py JSON report as a markdown table + notes."""
import json
import sys

def main():
    with open(sys.argv[1]) as f:
        report = json.load(f)

    print("| Division | Files | Total wall | theory-layer present | watchdog-unavailable | no line at all | Boolean search (gross) | Theory work (conservative) | Traced total (conservative) | Untraced | Traced % (conservative) | naive % (DO NOT TRUST, includes double-counted assert) |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for div, r in report.items():
        print(
            f"| {div} | {r['files']} | {r['total_wall_ms']/1000:.1f}s "
            f"| {r['files_with_theory_layer_line']} | {r['files_watchdog_unavailable']} "
            f"| {r['files_no_line_at_all']} | {r['boolean_search_ms']/1000:.2f}s "
            f"| {r['theory_work_ms_conservative']/1000:.2f}s | {r['traced_total_ms']/1000:.2f}s "
            f"| {r['untraced_ms']/1000:.1f}s | {r['traced_fraction_pct']}% "
            f"| {r['naive_traced_fraction_pct_DO_NOT_TRUST']}% |"
        )

if __name__ == "__main__":
    main()
