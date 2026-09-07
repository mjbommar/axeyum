#!/usr/bin/env python3
"""Aggregate the instrument-coverage 2026-09-07 re-run's per-file logs into a
per-division stage-coverage report, extending
`bench-results/bench-divisions-2026-09-07/scripts/aggregate.py` to the four
`--trace` instruments now available (`; front-door …`, `; dl-online …`,
`; bv-layer …`, in addition to the pre-existing `; theory-layer …`).

Reads the TSVs `run_division.sh` writes (columns: division, file, wall_ms,
verdict, log_path) and, for each file, reads `log_path` and extracts every
`; front-door …` / `; dl-online …` / `; bv-layer …` / `; theory-layer …` line
present (a query prints AT MOST one of `; bv-layer …` / `; theory-layer …`,
since a `sat-bv` decide never runs the CDCL(T) driver and vice versa, but
`; front-door …` and `; dl-online …` are independent stages that can appear
alongside either — see the module docs in `crates/axeyum-bench/examples/
smtcomp_cli.rs`).

# The non-additivity guard this script enforces (the exit-criterion instrument)

`docs/research/12-performance/bench-divisions-2026-09-07.md`'s own
"Methodology correction" found that naively summing every `; theory-layer …`
duration field double-counts (`theory_assert_ms` is nested inside
`boolean_propagate_ms`), because a stage breakdown that exceeds its own wall
clock is impossible and therefore proof the sum is wrong. This script folds
that check in permanently: after computing each file's `traced_ms` from the
(documented, checked-non-overlapping) fields below, it asserts
`traced_ms <= wall_ms * ALLOWED_SLOP` for every file and exits 1 — not just
prints a warning — if any file violates it. `ALLOWED_SLOP` is slightly above
1.0 (not exactly 1.0) purely to absorb the process-vs-instrument clock skew
between the harness's wall-clock `date +%s%N` measurement and the binary's own
internal `Instant` timers (startup/exit overhead, scheduling jitter) — it is
NOT a license to double-count a nested field; every field summed below is
picked specifically to be non-overlapping (see `TRACED_MS` below and its
comment).
"""
import re
import sys
import json

ALLOWED_SLOP = 1.15  # 15% headroom for process-vs-instrument clock skew, not double-counting.

FRONT_DOOR_RE = re.compile(r"^; front-door parse_ms=(\d+)\s*$", re.MULTILINE)
DL_ONLINE_RE = re.compile(r"^; dl-online total_ms=(\d+)\s*$", re.MULTILINE)
BV_LAYER_RE = re.compile(r"^; bv-layer .*?\btotal_ms=(\d+)\b", re.MULTILINE)
# theory-layer's own non-double-counting decomposition, ported verbatim from
# bench-results/bench-divisions-2026-09-07/scripts/aggregate.py: gross
# boolean-search (already subsumes whatever theory-assert time happened during
# propagation) plus theory work EXCLUDING theory_assert_ms (nested inside
# boolean_propagate_ms for a portion of its total -- see that script's own
# long comment, which this one does not re-derive).
THEORY_LAYER_RE = re.compile(r"^; theory-layer (.+)$", re.MULTILINE)
BOOLEAN_FIELDS = ["boolean_propagate_ms", "conflict_analysis_ms"]
THEORY_FIELDS_CONSERVATIVE = [
    "theory_propagate_ms", "theory_push_pop_ms",
    "theory_final_check_ms", "theory_explain_ms",
]


def parse_theory_layer_fields(line: str) -> dict:
    fields = {}
    for tok in line.split():
        if "=" in tok:
            k, v = tok.split("=", 1)
            fields[k] = v
    return fields


def theory_layer_traced_ms(log_text: str) -> int:
    m = THEORY_LAYER_RE.search(log_text)
    if not m or m.group(1).startswith("unavailable:"):
        return 0
    fields = parse_theory_layer_fields(m.group(1))
    total = 0
    for key in BOOLEAN_FIELDS + THEORY_FIELDS_CONSERVATIVE:
        v = fields.get(key)
        if v is not None and v.lstrip("-").isdigit():
            total += int(v)
    return total


def bv_layer_traced_ms(log_text: str) -> int:
    m = BV_LAYER_RE.search(log_text)
    return int(m.group(1)) if m else 0


def front_door_traced_ms(log_text: str) -> int:
    m = FRONT_DOOR_RE.search(log_text)
    return int(m.group(1)) if m else 0


def dl_online_traced_ms(log_text: str) -> int:
    m = DL_ONLINE_RE.search(log_text)
    return int(m.group(1)) if m else 0


def main() -> int:
    rows = []
    for path in sys.argv[1:]:
        with open(path, encoding="utf-8") as f:
            f.readline()  # header
            for line in f:
                line = line.rstrip("\n")
                if not line:
                    continue
                parts = line.split("\t")
                if len(parts) < 5:
                    continue
                division, file_, wall_ms, verdict, log_path = parts[:5]
                rows.append({
                    "division": division, "file": file_,
                    "wall_ms": int(wall_ms), "verdict": verdict,
                    "log_path": log_path,
                })

    divisions = {}
    for r in rows:
        divisions.setdefault(r["division"], []).append(r)

    violations = []
    report = {}
    grand_wall = 0
    grand_traced = 0
    for div, items in sorted(divisions.items()):
        n = len(items)
        total_wall = sum(r["wall_ms"] for r in items)
        per_file = []
        div_front_door = div_dl_online = div_bv_layer = div_theory_layer = 0
        div_traced = 0
        for r in items:
            try:
                with open(r["log_path"], encoding="utf-8", errors="replace") as lf:
                    log_text = lf.read()
            except OSError:
                log_text = ""
            front_door_ms = front_door_traced_ms(log_text)
            dl_online_ms = dl_online_traced_ms(log_text)
            bv_ms = bv_layer_traced_ms(log_text)
            theory_ms = theory_layer_traced_ms(log_text)
            # Non-overlapping by construction: front-door (parse) runs BEFORE
            # dispatch; dl-online is a probe that runs and returns before the
            # decisive route (bv-layer XOR theory-layer, never both) starts.
            file_traced = front_door_ms + dl_online_ms + bv_ms + theory_ms
            div_front_door += front_door_ms
            div_dl_online += dl_online_ms
            div_bv_layer += bv_ms
            div_theory_layer += theory_ms
            div_traced += file_traced
            wall_ms = r["wall_ms"]
            if wall_ms > 0 and file_traced > wall_ms * ALLOWED_SLOP:
                violations.append({
                    "division": div, "file": r["file"],
                    "wall_ms": wall_ms, "traced_ms": file_traced,
                    "pct": round(file_traced / wall_ms * 100, 1),
                })
            per_file.append({
                "file": r["file"], "wall_ms": wall_ms, "verdict": r["verdict"],
                "front_door_ms": front_door_ms, "dl_online_ms": dl_online_ms,
                "bv_layer_ms": bv_ms, "theory_layer_ms": theory_ms,
                "traced_ms": file_traced,
            })
        frac = (div_traced / total_wall * 100) if total_wall else 0.0
        report[div] = {
            "files": n,
            "total_wall_ms": total_wall,
            "front_door_ms": div_front_door,
            "dl_online_ms": div_dl_online,
            "bv_layer_ms": div_bv_layer,
            "theory_layer_ms": div_theory_layer,
            "traced_total_ms": div_traced,
            "untraced_ms": total_wall - div_traced,
            "traced_fraction_pct": round(frac, 1),
            "per_file": per_file,
        }
        grand_wall += total_wall
        grand_traced += div_traced

    report["_overall"] = {
        "total_wall_ms": grand_wall,
        "traced_total_ms": grand_traced,
        "traced_fraction_pct": round(grand_traced / grand_wall * 100, 1) if grand_wall else 0.0,
        "non_additivity_guard_violations": violations,
    }

    print(json.dumps(report, indent=2))

    if violations:
        print(
            f"NON-ADDITIVITY GUARD FAILED: {len(violations)} file(s) report traced_ms "
            f"exceeding wall_ms * {ALLOWED_SLOP} -- a stage breakdown cannot exceed the "
            "wall clock it was measured inside. See bench-divisions-2026-09-07's "
            "'Methodology correction' for the class of bug this catches.",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
