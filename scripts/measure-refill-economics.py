#!/usr/bin/env python3
"""Measure the refill economics of the autogenesis nursery draw.

ADR-1475. The dispatchable frontier fell below its floor of 10 within about an
hour of draw 18 taking it to 21, and authoring that draw cost four lanes. This
script measures the ratio behind that observation, so that the answer to "what
would raise the throughput ceiling" is arithmetic rather than instinct.

It is READ-ONLY. Nothing under `artifacts/` is written, and the numbers come
from `gen-autogenesis-nursery-refill.py`'s own screens -- `read_vocabulary`,
`admissible`, `blockers_for`, `HYGIENE`, `CONST_RE`, `PER_FAMILY`,
`FAMILY_MODULES` -- imported rather than reimplemented.
`propose-nursery-refill.py` is deliberately NOT consulted: four independent
blind spots were found in it on 2026-09-01, each overstating readiness.

Every count printed is paired with the population it was taken from, because a
total that has not moved is not the same as a total that is right.

Usage:
    python3 scripts/measure-refill-economics.py            # full report
    python3 scripts/measure-refill-economics.py --json     # machine-readable

Exit status: 0 ok, 2 an input could not be read.
"""

from __future__ import annotations

import argparse
import collections
import importlib.util
import json
import pathlib
import re
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
REFILL_SRC = ROOT / "scripts/gen-autogenesis-nursery-refill.py"

DRAW_RE = re.compile(r"^\s*#\s*---\s*draw\s+(\d+),\s*(\S+)")
FAMILY_KEY_RE = re.compile(r'^\s{4}"([a-z0-9-]+)":\s*\(')


def load_refill():
    spec = importlib.util.spec_from_file_location("refill_mod", REFILL_SRC)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def draw_blocks() -> list[dict[str, Any]]:
    """Which families each draw added, read from FAMILY_MODULES' own source.

    The manifest records no draw number, so the source comment markers are the
    only record of draw boundaries. They are load-bearing enough to parse: a
    family key appearing before the first `--- draw N` marker belongs to draw 1,
    which has no marker of its own.
    """
    text = REFILL_SRC.read_text().splitlines()
    start = next(i for i, line in enumerate(text)
                 if line.startswith("FAMILY_MODULES:"))
    end = next(i for i in range(start + 1, len(text))
               if text[i].startswith("}"))
    current = {"draw": 1, "date": "2026-08-29", "families": []}
    blocks = [current]
    for line in text[start + 1:end]:
        marker = DRAW_RE.match(line)
        if marker:
            current = {"draw": int(marker.group(1)),
                       "date": marker.group(2).rstrip(","),
                       "families": []}
            blocks.append(current)
            continue
        key = FAMILY_KEY_RE.match(line)
        if key:
            current["families"].append(key.group(1))
    return [b for b in blocks if b["families"]]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    R = load_refill()
    out: dict[str, Any] = {}

    try:
        snapshot = R.load_json(R.ENV_SNAPSHOT)
        env = set(snapshot["declarations"])
        inventory = R.read_inventory()
        catalog = R.load_json(R.CATALOG)
        registry = R.load_json(R.REGISTRY)["constructions"]
    except R.RefillError as exc:
        print(f"measure-refill-economics: {exc}", file=sys.stderr)
        return 2

    facts = {}
    for path in sorted(R.FACTS.glob("*.json")):
        fact = json.loads(path.read_text())
        facts[fact["id"]] = fact
    vocabulary = R.read_vocabulary(env, inventory, catalog, facts)
    adm = R.admissible(env, vocabulary)
    catalogued = {row["source_name"] for row in catalog["facts"]
                  if row["kind"] == "external-source"}

    module_family = {m: f for f, ms in R.FAMILY_MODULES.items() for m in ms}
    drawn_modules = set(module_family)

    # ---- the screen, applied to the WHOLE inventory ------------------------
    per_module: dict[str, list[str]] = collections.defaultdict(list)
    reasons: collections.Counter = collections.Counter()
    # For `not-statable-here`, how far away is the row? A row missing one
    # constant is a different economic proposition from one missing nine.
    missing_hist: collections.Counter = collections.Counter()
    blocking_const: collections.Counter = collections.Counter()
    near_miss_modules: dict[str, list[str]] = collections.defaultdict(list)

    for name in sorted(inventory):
        record = inventory[name]
        if name in catalogued:
            reasons["already-catalogued"] += 1
            continue
        if R.HYGIENE.search(name):
            reasons["hygienic-or-generated"] += 1
            continue
        constants = set(R.CONST_RE.findall(record["type_repr"]))
        missing = constants - adm
        if missing:
            reasons["not-statable-here"] += 1
            missing_hist[min(len(missing), 10)] += 1
            for const in missing:
                blocking_const[const] += 1
            if len(missing) == 1:
                near_miss_modules[record["module"]].append(name)
            continue
        if constants & R.HELD_OUT_CONSTRUCTIONS:
            reasons["held-out-construction"] += 1
            continue
        if R.blockers_for(record["type"], registry):
            reasons["divergence-registry"] += 1
            continue
        reasons["screened-ok"] += 1
        per_module[record["module"]].append(name)

    undrawn = {m: v for m, v in per_module.items() if m not in drawn_modules}
    residual = {m: v for m, v in per_module.items() if m in drawn_modules}
    out["screen"] = dict(reasons)
    out["inventory_records"] = len(inventory)
    out["env_declarations"] = len(env)
    out["admissible_constants"] = len(adm)
    out["screened_ok_total"] = sum(len(v) for v in per_module.values())
    out["screened_ok_modules"] = len(per_module)
    out["undrawn_modules"] = {m: len(v) for m, v in sorted(undrawn.items())}
    out["undrawn_rows"] = sum(len(v) for v in undrawn.values())
    out["drawn_module_residual_rows"] = sum(len(v) for v in residual.values())
    out["drawn_module_residual_modules"] = len(residual)
    out["undrawn_modules_anchoring_alone"] = sorted(
        m for m, v in undrawn.items() if len(v) >= R.PER_FAMILY)
    out["per_family"] = R.PER_FAMILY
    out["families_drawn"] = len(R.FAMILY_MODULES)
    out["modules_drawn"] = len(drawn_modules)

    # How many families could the undrawn supply form at various family sizes,
    # if arbitrary bundling of undrawn modules were permitted? This is an UPPER
    # bound: it ignores the mathematical-coherence and adjacency screens, which
    # only ever remove options.
    for size in (10, 8, 6, 5, 4, 3):
        out.setdefault("bundling_upper_bound", {})[size] = \
            out["undrawn_rows"] // size

    out["not_statable_missing_count_histogram"] = {
        str(k): v for k, v in sorted(missing_hist.items())}
    out["top_blocking_constants"] = blocking_const.most_common(25)
    out["near_miss_modules"] = {
        m: len(v) for m, v in sorted(near_miss_modules.items(),
                                     key=lambda kv: -len(kv[1]))[:25]}
    out["near_miss_rows"] = missing_hist.get(1, 0)

    # ---- per-draw economics -------------------------------------------------
    partitions = R.assign_partitions()
    blocks = draw_blocks()
    unknown = [f for b in blocks for f in b["families"]
               if f not in R.FAMILY_MODULES]
    out["draw_parse_unknown_families"] = unknown
    parsed = sum(len(b["families"]) for b in blocks)
    out["draw_parse_families"] = parsed
    out["draw_parse_covers_all_families"] = (parsed == len(R.FAMILY_MODULES)
                                             and not unknown)
    draws = []
    for block in blocks:
        counts: collections.Counter = collections.Counter(
            partitions[f] for f in block["families"] if f in R.FAMILY_MODULES)
        rows = len(block["families"]) * R.PER_FAMILY
        dispatchable = (counts["development"] + counts["train"]) * R.PER_FAMILY
        draws.append({
            "draw": block["draw"],
            "date": block["date"],
            "families": len(block["families"]),
            "rows": rows,
            "held_out_families": counts["held-out"],
            "held_out_rows": counts["held-out"] * R.PER_FAMILY,
            "dispatchable_rows": dispatchable,
        })
    out["draws"] = draws
    total_rows = sum(d["rows"] for d in draws)
    total_disp = sum(d["dispatchable_rows"] for d in draws)
    out["draw_totals"] = {
        "draws": len(draws),
        "families": sum(d["families"] for d in draws),
        "rows": total_rows,
        "dispatchable_rows": total_disp,
        "held_out_rows": total_rows - total_disp,
        "dispatchable_fraction": round(total_disp / total_rows, 4)
        if total_rows else None,
        "mean_families_per_draw": round(
            sum(d["families"] for d in draws) / len(draws), 2) if draws else None,
        "mean_dispatchable_per_draw": round(total_disp / len(draws), 2)
        if draws else None,
    }

    # ---- what the partition cycle costs at each family count ---------------
    cycle = R.PARTITION_CYCLE
    table = {}
    for n in range(3, 13):
        held = sum(1 for i in range(n) if cycle[i % len(cycle)] == "held-out")
        table[n] = {
            "held_out_families": held,
            "dispatchable_families": n - held,
            "dispatchable_rows": (n - held) * R.PER_FAMILY,
            "held_out_fraction": round(held / n, 4),
            "satisfies_R5": held >= 2,
        }
    out["cycle_table"] = table

    if args.json:
        print(json.dumps(out, indent=1, sort_keys=True))
        return 0

    print(f"INVENTORY|records={out['inventory_records']}"
          f"|env={out['env_declarations']}|admissible={out['admissible_constants']}"
          f"|families_drawn={out['families_drawn']}|modules_drawn={out['modules_drawn']}")
    print("SCREEN|" + "|".join(f"{k}={v}" for k, v in sorted(reasons.items())))
    print(f"SUPPLY|screened_ok={out['screened_ok_total']}"
          f"|modules={out['screened_ok_modules']}"
          f"|undrawn_rows={out['undrawn_rows']}"
          f"|undrawn_modules={len(undrawn)}"
          f"|residual_in_drawn_modules={out['drawn_module_residual_rows']}"
          f"|anchor_alone={len(out['undrawn_modules_anchoring_alone'])}")
    for module, count in sorted(out["undrawn_modules"].items(),
                                key=lambda kv: (-kv[1], kv[0])):
        print(f"  UNDRAWN|{count:4d}|{module}")
    print(f"BUNDLING_UPPER_BOUND|" + "|".join(
        f"size{k}={v}" for k, v in sorted(out["bundling_upper_bound"].items())))
    print(f"NEAR_MISS|rows_missing_exactly_one_constant={out['near_miss_rows']}"
          f"|of_not_statable={reasons['not-statable-here']}")
    print("MISSING_HIST|" + "|".join(
        f"{k}={v}" for k, v in sorted(out["not_statable_missing_count_histogram"].items(),
                                      key=lambda kv: int(kv[0]))))
    for const, count in out["top_blocking_constants"][:15]:
        print(f"  BLOCKER|{count:5d}|{const}")
    print(f"DRAW_PARSE|families={parsed}|covers_all="
          f"{out['draw_parse_covers_all_families']}|unknown={unknown}")
    for draw in draws:
        print(f"  DRAW|{draw['draw']:3d}|{draw['date']}|families={draw['families']}"
              f"|rows={draw['rows']}|held_out={draw['held_out_rows']}"
              f"|dispatchable={draw['dispatchable_rows']}")
    t = out["draw_totals"]
    print(f"DRAW_TOTALS|draws={t['draws']}|families={t['families']}"
          f"|rows={t['rows']}|dispatchable={t['dispatchable_rows']}"
          f"|held_out={t['held_out_rows']}"
          f"|dispatchable_fraction={t['dispatchable_fraction']}"
          f"|mean_families_per_draw={t['mean_families_per_draw']}"
          f"|mean_dispatchable_per_draw={t['mean_dispatchable_per_draw']}")
    for n, row in sorted(table.items()):
        print(f"  CYCLE|n={n:2d}|held_out_families={row['held_out_families']}"
              f"|dispatchable_rows={row['dispatchable_rows']}"
              f"|held_out_fraction={row['held_out_fraction']}"
              f"|R5={'ok' if row['satisfies_R5'] else 'FAILS'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
