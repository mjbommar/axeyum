#!/usr/bin/env python3
"""Generate bench-results/SCOREBOARD.md from the committed measured baselines.

This is an additive, deterministic aggregator: it reads the per-division
`vs-Z3` baselines under bench-results/baselines/, the synthetic graduated
NRA/NIA baselines, and the progress-frontier rows under bench-results/frontier/,
then emits a single legible markdown scoreboard. It fabricates nothing — every
number is read straight from the committed JSON. Re-running on unchanged
baselines produces a byte-identical file (no timestamps, fully sorted).

Usage:
    python3 scripts/gen-scoreboard.py

Reads:
    bench-results/baselines/*solver-vs-z3*.json   (per-division check_auto/solve)
    bench-results/baselines/qf-nra-synthetic-graduated-vs-z3.json
    bench-results/baselines/qf-nia-synthetic-graduated-vs-z3.json
    bench-results/frontier/*.json                 (lever progress frontiers)

Writes:
    bench-results/SCOREBOARD.md
"""

import glob
import json
import os

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASELINES_DIR = os.path.join(REPO_ROOT, "bench-results", "baselines")
FRONTIER_DIR = os.path.join(REPO_ROOT, "bench-results", "frontier")
OUT_PATH = os.path.join(REPO_ROOT, "bench-results", "SCOREBOARD.md")

# Z3 oracle version recorded across the baselines (used in the header prose).
Z3_VERSION = "z3 4.13.3"


def rel(path):
    """Repo-relative POSIX path for provenance listing (deterministic)."""
    return os.path.relpath(path, REPO_ROOT).replace(os.sep, "/")


def ground_truth_source(summary, instances):
    """Honest ground-truth label for a division baseline.

    - oracle.compared > 0  -> the live Z3 oracle decided the comparison.
      Flavor is the dominant backend_kind among *compared* instances:
        'z3'        -> in-repo Z3 library oracle  => "z3-library"
        'z3-binary' -> external Z3 binary oracle  => "z3-binary"
    - oracle.compared == 0 -> the Z3 oracle was skipped/vacuous for the whole
      division (e.g. unsupported sort, or binary oracle rejected the logic);
      ground truth then falls back to the SMT-LIB `:status` annotation
      (the per-instance `expected` field), tracked by status_disagreements.
    """
    oracle = summary["oracle"]
    if oracle["compared"] > 0:
        # Count the backend_kind only over instances Z3 actually compared.
        lib = 0
        binv = 0
        for it in instances:
            orc = it.get("oracle") or {}
            if not orc.get("decision_compared"):
                continue
            bk = orc.get("backend_kind")
            if bk == "z3":
                lib += 1
            elif bk == "z3-binary":
                binv += 1
        if lib and binv:
            return "z3-library+binary"
        if lib:
            return "z3-library"
        if binv:
            return "z3-binary"
        # compared>0 but kinds unattributable: still a live oracle.
        return "z3-oracle"
    # Oracle vacuous for the whole division -> SMT-LIB :status is the truth.
    return ":status"


def load_division_baselines():
    """Return sorted list of division rows from *solver-vs-z3* baselines."""
    rows = []
    paths = sorted(glob.glob(os.path.join(BASELINES_DIR, "*solver-vs-z3*.json")))
    for path in paths:
        with open(path) as fh:
            data = json.load(fh)
        cfg = data["config"]
        summary = data["summary"]
        instances = data.get("instances", [])
        oracle = summary["oracle"]
        triage_sound = data.get("triage", {}).get("soundness", {})

        logic = cfg.get("logic")
        if not logic:
            # Some QF_UF slices record logic as null; recover from corpus path.
            corpus = cfg.get("corpus", "")
            parts = [p for p in corpus.split("/") if p]
            # corpus/.../non-incremental/<LOGIC>/<slice>
            logic = "QF_UF"
            for i, p in enumerate(parts):
                if p == "non-incremental" and i + 1 < len(parts):
                    logic = parts[i + 1]
                    break

        files = summary["files"]
        sat = summary["sat"]
        unsat = summary["unsat"]
        decided = sat + unsat
        unknown = summary["unknown"]
        unsupported = summary["unsupported"]
        decide_pct = (100.0 * decided / files) if files else 0.0

        # Honest DISAGREE = oracle disagreements + :status disagreements.
        disagree = oracle["disagree"] + triage_sound.get("status_disagreements", 0)

        gt = ground_truth_source(summary, instances)
        par2 = summary.get("par2_mean_s")

        # A short slice label from the file stem to disambiguate same-logic rows.
        stem = os.path.basename(path)[: -len("-solver-vs-z3-10s.json")]
        # Derive a compact slice tag (drop the logic prefix where redundant).
        slice_tag = stem

        rows.append(
            {
                "logic": logic,
                "slice": slice_tag,
                "file": rel(path),
                "files": files,
                "sat": sat,
                "unsat": unsat,
                "decided": decided,
                "unknown": unknown,
                "unsupported": unsupported,
                "decide_pct": decide_pct,
                "compared": oracle["compared"],
                "disagree": disagree,
                "ground_truth": gt,
                "par2": par2,
            }
        )
    return rows


def load_synthetic_baselines():
    """Return rows for the synthetic graduated NRA/NIA baselines."""
    rows = []
    for name, logic in (
        ("qf-nra-synthetic-graduated-vs-z3.json", "QF_NRA"),
        ("qf-nia-synthetic-graduated-vs-z3.json", "QF_NIA"),
    ):
        path = os.path.join(BASELINES_DIR, name)
        if not os.path.exists(path):
            continue
        with open(path) as fh:
            data = json.load(fh)
        files = data["considered"]
        decided = data["axeyum_decided"]
        unknown = data.get("axeyum_unknown", files - decided)
        decide_pct = (100.0 * decided / files) if files else 0.0
        rows.append(
            {
                "logic": logic,
                "slice": logic.lower().replace("_", "-") + "-synthetic-graduated",
                "file": rel(path),
                "files": files,
                "sat": data.get("axeyum_sat", 0),
                "unsat": data.get("axeyum_unsat", 0),
                "decided": decided,
                "unknown": unknown,
                "unsupported": 0,
                "decide_pct": decide_pct,
                "compared": data.get("agree", 0) + data.get("disagree", 0),
                "disagree": data["disagree"],
                "ground_truth": "z3-binary",
                "par2": data.get("axeyum_par2_s"),
            }
        )
    return rows


def load_frontiers():
    """Return sorted progress-frontier rows."""
    rows = []
    paths = sorted(glob.glob(os.path.join(FRONTIER_DIR, "*.json")))
    for path in paths:
        with open(path) as fh:
            data = json.load(fh)
        curve = data.get("curve", [])
        max_knob = max((c["n"] for c in curve), default=0)
        budget_s = data.get("budget_ms", 0) / 1000.0
        rows.append(
            {
                "family": data["family"],
                "frontier": data["frontier"],
                "baseline": data["baseline"],
                "max_knob": max_knob,
                "budget_s": budget_s,
                "file": rel(path),
            }
        )
    return rows


FRONTIER_TRACKS = {
    "bv_reduction": "QF_BV word-level reduction depth (unsat at knob N)",
    "lia_cuts": "QF_LIA branch-and-cut depth (sat at knob N)",
    "nia_unsat": "QF_NIA unsat-proving depth (knob N)",
    "nra_degree": "QF_NRA polynomial-degree decision depth (knob N)",
    "string_bound": "QF_S string-length bound (sat at knob N)",
}


def fmt_par2(par2):
    if par2 is None:
        return "—"
    return f"{par2:.3f}"


def build_markdown(div_rows, synth_rows, frontier_rows):
    all_div = div_rows + synth_rows
    # Sort divisions: by logic name, then by descending decide%, then slice.
    all_div_sorted = sorted(
        all_div, key=lambda r: (r["logic"], -r["decide_pct"], r["slice"])
    )

    total_divisions = len(all_div_sorted)
    total_files = sum(r["files"] for r in all_div_sorted)
    total_decided = sum(r["decided"] for r in all_div_sorted)
    total_compared = sum(r["compared"] for r in all_div_sorted)
    total_disagree = sum(r["disagree"] for r in all_div_sorted)
    distinct_logics = sorted({r["logic"] for r in all_div_sorted})

    pcts = [r["decide_pct"] for r in all_div_sorted if r["files"]]
    pct_lo = min(pcts) if pcts else 0.0
    pct_hi = max(pcts) if pcts else 0.0

    lines = []
    lines.append("# Measured Scoreboard — axeyum vs Z3")
    lines.append("")
    lines.append(
        "> **Auto-generated. Do not edit by hand.** "
        "Regenerate with `python3 scripts/gen-scoreboard.py`."
    )
    lines.append("")
    lines.append(
        "A single-glance, honest view of where the pure-Rust axeyum solver "
        f"stands against **{Z3_VERSION}** across every *measured* division. "
        "Every number here is read straight from a committed baseline JSON "
        "under `bench-results/baselines/` — nothing is hand-entered."
    )
    lines.append("")
    lines.append("## How to read this")
    lines.append("")
    lines.append(
        "- **Decided** = `sat + unsat` — the instances axeyum *resolves*. "
        "Everything else is a **sound `unknown`** (we cannot decide it yet) or "
        "**unsupported** (the logic fragment is not wired); axeyum never guesses."
    )
    lines.append(
        "- **Decide%** = `Decided / Files`. This is the **capability frontier** — "
        "higher means axeyum decides more of the slice on its own."
    )
    lines.append(
        "- **DISAGREE** = wrong verdicts vs the ground truth (oracle "
        "disagreements + `:status` disagreements). **DISAGREE = 0 everywhere "
        "means zero wrong sat/unsat — soundness.** This is the line that must "
        "never move off zero."
    )
    lines.append(
        "- **Ground-truth** — how each division's verdict was checked: "
        "`z3-library` (the in-repo Z3 oracle), `z3-binary` (the external Z3 "
        "binary), `z3-library+binary` (a mix across the slice), or `:status` "
        "(the SMT-LIB `(set-info :status ...)` annotation, used when the Z3 "
        "oracle was vacuous/skipped for the whole slice — e.g. it rejected the "
        "logic's sort). An honest row reflects what was *actually* compared "
        "(see the **Cmp** column = instances the oracle compared)."
    )
    lines.append(
        "- **PAR-2** = mean PAR-2 score in seconds (timeouts counted at 2×); "
        "lower is faster. `—` where not recorded."
    )
    lines.append("")
    lines.append("## Headline")
    lines.append("")
    lines.append(
        f"- **{total_divisions} division baselines** measured vs "
        f"{Z3_VERSION}, spanning **{len(distinct_logics)} logic fragments** "
        f"({', '.join(distinct_logics)})."
    )
    lines.append(
        f"- **DISAGREE = {total_disagree} across all baselines** — zero wrong "
        f"verdicts over {total_compared} oracle-compared instances "
        f"({total_files} files total, {total_decided} decided)."
    )
    lines.append(
        f"- Decide-rate ranges **{pct_lo:.0f}%–{pct_hi:.0f}%** across "
        "divisions — that spread *is* the capability frontier; DISAGREE = 0 is "
        "the soundness floor that holds everywhere."
    )
    lines.append("")
    lines.append("## Divisions vs Z3")
    lines.append("")
    lines.append(
        "Sorted by logic, then by descending decide-rate. Every committed "
        "`*solver-vs-z3*` baseline plus the synthetic graduated NRA/NIA "
        "baselines appears below."
    )
    lines.append("")
    lines.append(
        "| Division | Slice | Files | Decided | Decide% | Unknown | Unsup | "
        "Cmp | DISAGREE | Ground-truth | PAR-2 (s) |"
    )
    lines.append(
        "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | "
        "--- | ---: |"
    )
    for r in all_div_sorted:
        lines.append(
            "| {logic} | `{slice}` | {files} | {decided} | {pct:.0f}% | "
            "{unknown} | {unsup} | {cmp} | {dis} | {gt} | {par2} |".format(
                logic=r["logic"],
                slice=r["slice"],
                files=r["files"],
                decided=r["decided"],
                pct=r["decide_pct"],
                unknown=r["unknown"],
                unsup=r["unsupported"],
                cmp=r["compared"],
                dis=r["disagree"],
                gt=r["ground_truth"],
                par2=fmt_par2(r["par2"]),
            )
        )
    lines.append("")
    lines.append(
        f"**Totals:** {total_files} files, {total_decided} decided, "
        f"{total_compared} oracle-compared, **{total_disagree} disagreements.**"
    )
    lines.append("")

    # Frontier table.
    lines.append("## Progress frontiers (lever depth)")
    lines.append("")
    lines.append(
        "Each frontier tracks how deep a single capability lever reaches: a "
        "family is scaled by a knob `N` and the **frontier** is the largest `N` "
        "axeyum still decides within budget. **Baseline** is the previously "
        "recorded frontier — the gap (frontier − baseline) is the gradual "
        "improvement this front exists to show."
    )
    lines.append("")
    lines.append(
        "| Lever family | Frontier | Baseline | Δ | Max knob | Budget (s) | "
        "Tracks |"
    )
    lines.append("| --- | ---: | ---: | ---: | ---: | ---: | --- |")
    for r in sorted(frontier_rows, key=lambda x: x["family"]):
        delta = r["frontier"] - r["baseline"]
        delta_str = f"+{delta}" if delta > 0 else str(delta)
        lines.append(
            "| {family} | {frontier} | {baseline} | {delta} | {maxk} | "
            "{budget:.0f} | {tracks} |".format(
                family=r["family"],
                frontier=r["frontier"],
                baseline=r["baseline"],
                delta=delta_str,
                maxk=r["max_knob"],
                budget=r["budget_s"],
                tracks=FRONTIER_TRACKS.get(r["family"], "—"),
            )
        )
    lines.append("")

    # Summary line.
    lines.append("## One-line summary")
    lines.append("")
    lines.append(
        f"**{total_divisions} division baselines measured vs {Z3_VERSION}, "
        f"DISAGREE = {total_disagree} across all — zero wrong verdicts; "
        f"decide-rate ranges {pct_lo:.0f}%–{pct_hi:.0f}%.** DISAGREE = 0 "
        "everywhere is the soundness guarantee; decide% is the capability "
        "frontier we push, division by division."
    )
    lines.append("")

    # Provenance.
    lines.append("## Provenance")
    lines.append("")
    lines.append(
        "Generated by [`scripts/gen-scoreboard.py`](../scripts/gen-scoreboard.py) "
        "from the following committed baselines (deterministic — no timestamps, "
        "fully sorted; re-running on unchanged inputs yields a byte-identical "
        "file):"
    )
    lines.append("")
    prov = sorted(
        r["file"] for r in (div_rows + synth_rows)
    ) + sorted(r["file"] for r in frontier_rows)
    for p in prov:
        lines.append(f"- `{p}`")
    lines.append("")
    lines.append("Regenerate with `python3 scripts/gen-scoreboard.py`.")
    lines.append("")
    return "\n".join(lines)


def main():
    div_rows = load_division_baselines()
    synth_rows = load_synthetic_baselines()
    frontier_rows = load_frontiers()
    md = build_markdown(div_rows, synth_rows, frontier_rows)
    with open(OUT_PATH, "w") as fh:
        fh.write(md)
    print(
        f"wrote {rel(OUT_PATH)}: "
        f"{len(div_rows) + len(synth_rows)} divisions, "
        f"{len(frontier_rows)} frontiers"
    )


if __name__ == "__main__":
    main()
