#!/usr/bin/env python3
"""Aggregate the gate (b) re-run sweeps into the decided/PAR-2 table and the
boundary decomposition Phase D's entry condition needs.

Reads the per-engine TSVs this directory holds and prints:

  1. the decided-count + PAR-2 table, one row per engine, per family;
  2. cross-engine verdict disagreements (a P0 if any) and unchecked models;
  3. for every file a reference decides and the native core does not, the
     reference's wall time -- bucketed near/far from the budget boundary,
     because "the reference decides it in 0.2 s of 20 s" and "the reference
     decides it in 19 s of 20 s" are different claims about how much a core
     improvement would have to buy.

PAR-2 scores an undecided instance at 2x the budget, which is the standard
SAT-competition convention and the one the 2026-09-05 artifact used.
"""

import os
import sys

BUDGET_S = 20.0
NATIVE_HEADER_COLS = [
    "file",
    "variables",
    "clauses",
    "native_verdict",
    "native_ms",
    "native_timed_out",
    "native_model_valid",
]


def read_tsv(path):
    if not os.path.exists(path):
        return None
    with open(path, encoding="utf-8") as handle:
        lines = handle.read().splitlines()
    if not lines:
        return None
    header = lines[0].split("\t")
    rows = []
    for line in lines[1:]:
        if not line.strip():
            continue
        rows.append(dict(zip(header, line.split("\t"), strict=False)))
    return rows


def load_family(art, family):
    """Returns {engine: {file: (verdict, wall_s, model_check)}}."""
    engines = {}
    native = read_tsv(os.path.join(art, f"native-{family}.tsv"))
    if native is not None:
        engines["native"] = {
            row["file"]: (
                row["native_verdict"],
                float(row["native_ms"]) / 1000.0,
                row.get("native_model_valid", ""),
            )
            for row in native
        }
    for engine in ("cadical", "kissat"):
        rows = read_tsv(os.path.join(art, f"{engine}-{family}.tsv"))
        if rows is not None:
            engines[engine] = {
                row["file"]: (
                    row["verdict"],
                    float(row["wall_ms"]) / 1000.0,
                    row.get("model_check", ""),
                )
                for row in rows
            }
    return engines


def par2(records, universe):
    total = 0.0
    for name in universe:
        entry = records.get(name)
        if entry is None or entry[0] not in ("sat", "unsat"):
            total += 2.0 * BUDGET_S
        else:
            total += min(entry[1], BUDGET_S)
    return total / len(universe) if universe else float("nan")


def report(art, family):
    engines = load_family(art, family)
    if not engines:
        print(f"\n## {family}: no data\n")
        return
    universe = sorted(set().union(*(set(rows) for rows in engines.values())))
    print(f"\n## {family} -- {len(universe)} files, {BUDGET_S:.0f} s budget\n")
    for engine, rows in engines.items():
        missing = [name for name in universe if name not in rows]
        if missing:
            print(
                f"INCOMPLETE: {engine} has {len(rows)}/{len(universe)} rows "
                f"(missing {len(missing)}); its numbers are NOT comparable."
            )
    print("| Engine | Decided / {} | sat | unsat | PAR-2 mean (s) |".format(len(universe)))
    print("|---|---:|---:|---:|---:|")
    for engine in ("native", "cadical", "kissat"):
        rows = engines.get(engine)
        if rows is None:
            continue
        sat = sum(1 for name in universe if rows.get(name, ("", 0, ""))[0] == "sat")
        unsat = sum(1 for name in universe if rows.get(name, ("", 0, ""))[0] == "unsat")
        print(
            f"| {engine} | {sat + unsat} | {sat} | {unsat} | {par2(rows, universe):.3f} |"
        )

    # Soundness: cross-engine disagreement and unchecked models.
    disagreements = []
    for name in universe:
        verdicts = {
            engine: rows[name][0]
            for engine, rows in engines.items()
            if name in rows and rows[name][0] in ("sat", "unsat")
        }
        if len(set(verdicts.values())) > 1:
            disagreements.append((name, verdicts))
    unchecked = [
        (engine, name)
        for engine, rows in engines.items()
        for name in rows
        if rows[name][0] == "sat" and rows[name][2] not in ("ok", "true")
    ]
    print(f"\ncross-engine verdict disagreements: {len(disagreements)}")
    for name, verdicts in disagreements:
        print(f"  DISAGREEMENT {name}: {verdicts}")
    print(f"sat verdicts not confirmed by CnfFormula::evaluate: {len(unchecked)}")
    for engine, name in unchecked[:10]:
        print(f"  UNCHECKED {engine} {name}")

    # Boundary decomposition.
    native = engines.get("native")
    if native is None:
        return
    for engine in ("cadical", "kissat"):
        rows = engines.get(engine)
        if rows is None:
            continue
        extra = [
            (name, rows[name][1])
            for name in universe
            if rows.get(name, ("", 0, ""))[0] in ("sat", "unsat")
            and native.get(name, ("", 0, ""))[0] not in ("sat", "unsat")
        ]
        lost = [
            name
            for name in universe
            if native.get(name, ("", 0, ""))[0] in ("sat", "unsat")
            and rows.get(name, ("", 0, ""))[0] not in ("sat", "unsat")
        ]
        extra.sort(key=lambda pair: pair[1])
        print(
            f"\n### {engine} decides and native does not: {len(extra)} "
            f"(native decides and {engine} does not: {len(lost)})"
        )
        if lost:
            print("  native-only: " + ", ".join(lost))
        far = [pair for pair in extra if pair[1] <= 0.25 * BUDGET_S]
        mid = [pair for pair in extra if 0.25 * BUDGET_S < pair[1] <= 0.75 * BUDGET_S]
        near = [pair for pair in extra if pair[1] > 0.75 * BUDGET_S]
        print(
            f"  far from the boundary (<= {0.25 * BUDGET_S:.0f} s, "
            f">= 4x headroom): {len(far)}"
        )
        print(f"  mid ({0.25 * BUDGET_S:.0f}-{0.75 * BUDGET_S:.0f} s): {len(mid)}")
        print(f"  near the boundary (> {0.75 * BUDGET_S:.0f} s): {len(near)}")
        for name, wall in extra:
            print(f"    {wall:8.2f}s  {name}")


def main():
    art = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))
    for family in ("p4dfa", "noetzli"):
        report(art, family)


if __name__ == "__main__":
    main()
