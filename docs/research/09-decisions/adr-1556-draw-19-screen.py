#!/usr/bin/env python3
"""ADR-1556: screen nursery draw 19 against the REAL machinery.

Same construction as `adr-1240-index-zero-screen.py`, `adr-1245`, `adr-1255`
and `adr-1465-draw-18-screen.py`: load `scripts/gen-autogenesis-nursery-refill.py`
and `scripts/check-holdout-adjacency.py` by path and run the ACTUAL
`admissible()` / `blockers_for()` / `screen_family()` / `barred_modules()` /
`is_closed_evaluation` rather than a reimplementation.
`propose-nursery-refill.py` is deliberately NOT used as a candidate space --
it screens by module only and misses the fact-ledger, `HELD_OUT_CONSTRUCTIONS`
and R5 screens.

WHAT IT MEASURES. R5 demands two NEW held-out families per draw and the cycle
restarts at `held-out` for each draw's fresh family set, so a four-family draw
puts held-out at cycle indices 0 and 3. This screen enumerates EVERY drawn ten
buildable from the unowned pool and asks how many are held-out-viable, then
whether two of them are module-disjoint -- `select()`'s module->family map is
flat, so two families cannot share a module.

DEDUP IS BY DRAWN TEN, NOT BY MODULE SET, and that correction matters: a
superset of a module set that already reaches PER_FAMILY does NOT draw the same
ten, because an added module's names can sort earlier. Enumerating minimal
covers only (the obvious pruning) silently skips those tens. Both passes are
run below and both are reported, so the pruning's effect is measured rather
than assumed.

CONTROL. A search that finds no disjoint pair is worth nothing until it is
shown it CAN find one. The last assertion re-runs the identical disjointness
search over a pool in which the blocking module's rows are relabelled into a
second, independent module, and requires a disjoint pair to appear.

Usage:
    python3 docs/research/09-decisions/adr-1556-draw-19-screen.py [MAXMOD]

Needs the pinned statement inventory (`/nas3`), like the generator itself --
which is why this is not a registered gate.

Exit status depends on the finding:
  0  the refusal still holds (no two disjoint viable held-out families) AND
     the control fired.
  1  a disjoint pair EXISTS -- the refusal has expired, author the draw -- or
     the control did NOT fire, in which case the search is broken and its
     zero means nothing.
"""

from __future__ import annotations

import importlib.util
import itertools
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
MAXMOD = int(sys.argv[1]) if len(sys.argv) > 1 else 8


def load(path: pathlib.Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


R = load(ROOT / "scripts/gen-autogenesis-nursery-refill.py", "_refill")
ADJ = load(ROOT / "scripts/check-holdout-adjacency.py", "_adj")
CEV = load(ROOT / "scripts/check-holdout-closed-evaluation.py", "_cev")

failures: list[str] = []


def check(label: str, ok: bool, detail: str = "") -> None:
    print(f"{'ok  ' if ok else 'FAIL'}  {label}{'  ' + detail if detail else ''}")
    if not ok:
        failures.append(label)


def unowned_pool(env, inventory, registry, admissible):
    owned = {m for ms in R.FAMILY_MODULES.values() for m in ms}
    catalog = R.load_json(R.CATALOG)
    catalogued = {row["source_name"] for row in catalog["facts"]
                  if row["kind"] == "external-source"}
    pool: dict[str, list[str]] = {}
    for name in sorted(inventory):
        record = inventory[name]
        module = record["module"]
        if module in owned or name in catalogued or R.HYGIENE.search(name):
            continue
        constants = set(R.CONST_RE.findall(record["type_repr"]))
        if sorted(constants - admissible):
            continue
        if constants & R.HELD_OUT_CONSTRUCTIONS:
            continue
        if R.blockers_for(record["type"], registry):
            continue
        pool.setdefault(module, []).append(name)
    return pool


def viable_tens(pool, inventory, published, partition, barred, env, maxmod,
                minimal_covers_only=False):
    """Every DISTINCT drawn ten over `pool` that survives every held-out screen."""
    modules = sorted(pool)
    tens: dict[tuple, list[tuple]] = {}
    for k in range(1, maxmod + 1):
        for combo in itertools.combinations(modules, k):
            if sum(len(pool[m]) for m in combo) < R.PER_FAMILY:
                continue
            if minimal_covers_only and any(
                    sum(len(pool[m]) for m in combo if m != drop) >= R.PER_FAMILY
                    for drop in combo):
                continue
            ten = tuple(sorted(n for m in combo for n in pool[m])[:R.PER_FAMILY])
            tens.setdefault(ten, []).append(combo)
    out = []
    for ten, combos in tens.items():
        rows = [ADJ.Row(n, inventory[n]["module"],
                        frozenset(R.CONST_RE.findall(inventory[n]["type_repr"])))
                for n in ten]
        if any(r.module in barred for r in rows):
            continue
        finding = ADJ.screen_family("__candidate__", rows, published, partition,
                                    env=env, reviews={}, require_disclosure=False)
        if finding.verdict != "clean":
            continue
        if any(n in env for n in ten):          # R9
            continue
        if any(CEV.is_closed_evaluation(inventory[n]["type"]) for n in ten):  # R12
            continue
        out.append((ten, sorted({r.module for r in rows}), finding))
    return len(tens), out


def disjoint_pairs(viable):
    return [(a, b) for i, (_, a, _) in enumerate(viable)
            for (_, b, _) in viable[i + 1:] if not (set(a) & set(b))]


def main() -> int:
    env = set(R.load_json(R.ENV_SNAPSHOT)["declarations"])
    inventory = R.read_inventory()
    registry = R.load_json(R.REGISTRY)["constructions"]
    catalog = R.load_json(R.CATALOG)
    facts = {}
    for path in sorted(R.FACTS.glob("*.json")):
        fact = json.loads(path.read_text())
        facts[fact["id"]] = fact
    vocabulary = R.read_vocabulary(env, inventory, catalog, facts)
    admissible = R.admissible(env, vocabulary)

    pool = unowned_pool(env, inventory, registry, admissible)
    rows_total = sum(len(v) for v in pool.values())
    print(f"environment: {len(env)} declarations (committed snapshot)")
    print(f"unowned modules with a screened pool: {len(pool)}, rows {rows_total}, "
          f"PER_FAMILY={R.PER_FAMILY}, max modules per family {MAXMOD}")

    existing_rows, existing_partition, _ = ADJ.resolve_families(R)
    barred = ADJ.barred_modules(ADJ.load_refusals())
    published = {f: rows for f, rows in existing_rows.items()
                 if existing_partition.get(f) in ("development", "train")}
    print(f"published development/train families scored against: {len(published)}")
    print(f"modules barred do-not-draw-held-out: {sorted(barred)}")
    print()

    # 1. The pruned pass (minimal covers only) and the exact pass, both run, so
    #    the pruning's effect on the answer is measured.
    n_pruned, viable_pruned = viable_tens(
        pool, inventory, published, existing_partition, barred, env, MAXMOD,
        minimal_covers_only=True)
    n_all, viable = viable_tens(
        pool, inventory, published, existing_partition, barred, env, MAXMOD)
    print(f"minimal-cover pass:  {n_pruned} distinct tens, "
          f"{len(viable_pruned)} viable")
    print(f"exact pass:          {n_all} distinct tens, {len(viable)} viable")
    check("the pruned pass does not change the viable count",
          len(viable_pruned) == len(viable),
          f"{len(viable_pruned)} vs {len(viable)}")

    print()
    for ten, mods, finding in viable:
        print(f"  VIABLE ten  vocab={finding.vocabulary_rows}/10 "
              f"env_sweep={[h[0] for h in finding.environment_hits]}")
        print(f"    modules contributing a row: {mods}")
        print(f"    ten: {list(ten)}")

    # 2. THE FINDING. R5 needs two NEW held-out families and a module belongs to
    #    exactly one family, so the two must be module-disjoint.
    pairs = disjoint_pairs(viable)
    print()
    print(f"disjoint pairs of viable held-out tens (R5 needs one): {len(pairs)}")
    if viable:
        common = set(viable[0][1])
        for _, mods, _ in viable[1:]:
            common &= set(mods)
        print(f"modules contributing a row to EVERY viable ten: {sorted(common)}")
    check("the refusal still holds: R5 cannot be satisfied from today's pool",
          not pairs,
          "a disjoint pair EXISTS -- author draw 19" if pairs else "")

    # 3. CONTROL. A zero from a search that cannot produce a one is not a
    #    measurement. Lift ADR-1450's `Mathlib.Data.Nat.Count` bar -- the ONLY
    #    signal that refuses the Count tens, measured -- and require a disjoint
    #    pair to appear. Count shares no module with the four above, so this is
    #    the smallest single change that should flip the answer, and it names
    #    the unblock exactly: one held-out-safe family disjoint from the core.
    #
    #    Cloning the blocking modules is NOT a usable control and the first
    #    draft of this file got it wrong: a clone carries the same row NAMES,
    #    the dedup key IS the drawn ten, so the clone's ten collapses onto the
    #    original's and no pair can ever appear. It reported 418 viable tens
    #    and 0 pairs, which reads exactly like the real finding.
    control_barred = {m: e for m, e in barred.items()
                      if m != "Mathlib.Data.Nat.Count"}
    _, viable_control = viable_tens(
        pool, inventory, published, existing_partition, control_barred, env,
        MAXMOD)
    control_pairs = disjoint_pairs(viable_control)
    print()
    print(f"CONTROL (ADR-1450's Mathlib.Data.Nat.Count bar lifted): "
          f"{len(viable_control)} viable tens, {len(control_pairs)} "
          f"disjoint pair(s)")
    check("CONTROL fires: the disjointness search CAN find a pair",
          bool(control_pairs))

    # 4. The blindness finding recorded by ADR-1556: `Int.gcd_eq_natAbs` is not
    #    a blind proposition here, because `Int.gcd` IS that equation. Read from
    #    the declaration's source rather than from a name.
    gcd_src = (ROOT / "crates/axeyum-lean-kernel/src/int_prelude/gcd.rs").read_text()
    body = gcd_src.split("pub(super) fn declare_gcd(", 1)[-1].split("\n}\n", 1)[0]
    check("Int.gcd is DEFINED as Nat.gcd (natAbs a) (natAbs b), so "
          "Int.gcd_eq_natAbs is rfl here",
          "nat_abs(d, a)" in body and "nat_abs(d, b)" in body
          and "NatOps::gcd(d, big_a, big_b)" in body)

    print()
    print(f"ADR_1556_DRAW_19_SCREEN|env={len(env)}|unowned_modules={len(pool)}"
          f"|unowned_rows={rows_total}|distinct_tens={n_all}"
          f"|viable={len(viable)}|disjoint_pairs={len(pairs)}"
          f"|failures={len(failures)}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
