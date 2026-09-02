#!/usr/bin/env python3
"""ADR-1561: screen nursery draw 19 against the REAL machinery.

Same construction as `adr-1240`, `adr-1245`, `adr-1255`, `adr-1465` and
`adr-1556`'s screens: load `scripts/gen-autogenesis-nursery-refill.py`,
`scripts/check-holdout-adjacency.py` and
`scripts/check-holdout-closed-evaluation.py` by path and run the ACTUAL
`admissible()` / `blockers_for()` / `screen_family()` / `barred_modules()` /
`assign_partitions()` / `is_closed_evaluation` rather than a reimplementation.
`propose-nursery-refill.py` is deliberately NOT the candidate space -- it
screens by module only and has neither the fact ledger nor
`HELD_OUT_CONSTRUCTIONS` nor the R5 screen.

WHAT IT MEASURES, and why each number is here rather than in prose:

  1. THE DRAW ITSELF. The four families draw10 ADR-1561 preregisters produce
     the partitions the split key assigns (held-out, development, train,
     held-out over the lexicographic order of their primary modules), both
     held-out families are R9- and R12-clean, and both are R11-clean scored
     against every published development/train family INCLUDING the two this
     same draw adds -- the draw-18 lesson (ADR-1465), where the original
     window filler was R11-refused only once the draw's own siblings were in
     the published set.

  2. NO DRAWN TEN CARRIES A ROW THAT IS `rfl` UNDER OUR CONSTRUCTION.
     ADR-1556 found `Int.gcd_eq_natAbs` is our own definition of `Int.gcd`;
     ADR-1559 found `Nat.primeCounting_eq_primeCounting'_succ` is Mathlib's
     own defining equation and therefore `rfl` under any faithful definition
     of the pair. Neither may appear in any partition.

  3. THE DECISION THIS ADR CARRIES: draw 10's do-not-draw-held-out deferral of
     `Mathlib.NumberTheory.{SumTwoSquares,PythagoreanTriples}` is overturned,
     and the measurement is that withholding them -- BOTH, or EITHER ALONE --
     leaves ZERO module-disjoint pairs of clean held-out bundles at every
     module cap from four to six, so R5 is unsatisfiable and draw 19 refuses
     for a third time. The deferral was a preference ("it is not worth a mild
     leak to buy slack"), and it is measured here as the entire refusal.

  4. THE COHERENCE FINDING. Requiring a held-out family's modules to share two
     leading path segments -- the obvious way to make a family one coherent
     piece of mathematics -- leaves 3 clean bundles out of 168, and NO TWO OF
     THEM ARE MODULE-DISJOINT, so R5 cannot be met from topically tight
     families at all. R11's vocabulary rule (at most 5 of 10 rows about a
     constant a development/train family publishes) is what refuses the rest:
     `Choose.*` runs 10/10, `{BinaryRec,Bitwise}` 9/10,
     `Factorization.* + Multiplicity` 9/10, the whole of `NumberTheory.*`
     6/10. A held-out family here is cross-topic BY CONSTRUCTION. The first
     draft of this assertion claimed ZERO coherent bundles and was WRONG --
     it had been measured at a four-module cap and with draw 10's two deferred
     modules removed, and neither restriction belongs in this claim.

CONTROLS. Each assertion is paired with a run that must come out the other
way, because an assertion that cannot fail measures nothing:
  * the disjointness search is re-run with ADR-1450's `Mathlib.Data.Nat.Count`
    bar lifted and must find MORE pairs (ADR-1556's working control);
  * the definitional-row check is re-run against a ten deliberately built to
    contain `Nat.primeCounting_eq_primeCounting'_succ` and must FIRE;
  * the R11 screen is re-run for a held-out family scored against a published
    set containing a topic it shares, and must REFUSE.

Usage:
    python3 docs/research/09-decisions/adr-1561-draw-19-screen.py [MAXMOD]

Needs the pinned statement inventory (`/nas3`), like the generator itself --
which is why this is not a registered gate.

Exit status depends on the finding:
  0  the draw as preregistered is lawful and every control fired.
  1  something about the draw does not hold, or a control did not fire.
"""

from __future__ import annotations

import importlib.util
import itertools
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
MAXMOD = int(sys.argv[1]) if len(sys.argv) > 1 else 6

# The four families ADR-1561 preregisters, and the partition the split key must
# independently produce for each. This dict is the CLAIM; `assign_partitions()`
# is the authority, and assertion 1 compares them.
DRAW_19 = {
    "discrete-step-and-counting-bounds": "held-out",
    "natural-bit-constructor": "development",
    "natural-binomial-bounds": "train",
    "power-and-square-decompositions": "held-out",
}

# Rows that are `rfl` under this kernel's construction and so are not blind
# propositions. ADR-1556 and ADR-1559 respectively.
DEFINITIONAL = {
    "Int.gcd_eq_natAbs",
    "Nat.primeCounting_eq_primeCounting'_succ",
}

# Draw 10's deferral, overturned by this ADR. Named here so assertion 3 can
# measure what withholding them costs.
DRAW_10_DEFERRED = {
    "Mathlib.NumberTheory.PythagoreanTriples",
    "Mathlib.NumberTheory.SumTwoSquares",
}


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


def unowned_pool(inventory, registry, admissible, exclude_owned_by=()):
    """The screened candidate pool over modules no family owns.

    `exclude_owned_by` lets the caller pretend a set of families does not exist,
    which is how assertion 3 reconstructs the pool draw 19 chose FROM.
    """
    owned = {m for f, ms in R.FAMILY_MODULES.items() for m in ms
             if f not in exclude_owned_by}
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


def rows_for(ten, inventory):
    return [ADJ.Row(n, inventory[n]["module"],
                    frozenset(R.CONST_RE.findall(inventory[n]["type_repr"])))
            for n in ten]


def ten_of(combo, pool):
    return tuple(sorted(n for m in combo for n in pool[m])[:R.PER_FAMILY])


def prefix_depth(combo):
    parts = [m.split(".") for m in combo]
    n = 0
    while all(len(p) > n for p in parts) and len({p[n] for p in parts}) == 1:
        n += 1
    return n


def clean_heldout_bundles(pool, inventory, published, partition, barred, env,
                          maxmod, min_prefix=0):
    """Every DISTINCT drawn ten over `pool` that survives every held-out screen."""
    modules = sorted(pool)
    out = []
    for k in range(1, maxmod + 1):
        for combo in itertools.combinations(modules, k):
            if sum(len(pool[m]) for m in combo) < R.PER_FAMILY:
                continue
            if k > 1 and prefix_depth(combo) < min_prefix:
                continue
            ten = ten_of(combo, pool)
            if {inventory[n]["module"] for n in ten} != set(combo):
                continue
            if set(ten) & DEFINITIONAL:
                continue
            if any(m in barred for m in combo):
                continue
            finding = ADJ.screen_family("__candidate__", rows_for(ten, inventory),
                                        published, partition, env=env, reviews={},
                                        require_disclosure=False)
            if finding.verdict != "clean":
                continue
            if any(n in env for n in ten):                                  # R9
                continue
            if any(CEV.is_closed_evaluation(inventory[n]["type"]) for n in ten):
                continue                                                    # R12
            out.append((combo, ten, finding))
    return out


def disjoint_pairs(bundles):
    return [(bundles[i][0], bundles[j][0])
            for i in range(len(bundles)) for j in range(i + 1, len(bundles))
            if not (set(bundles[i][0]) & set(bundles[j][0]))]


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

    print(f"environment: {len(env)} declarations (committed snapshot)")

    # ---------------------------------------------------------------- 1. draw
    missing = sorted(f for f in DRAW_19 if f not in R.FAMILY_MODULES)
    check("draw 19's four families are in FAMILY_MODULES", not missing,
          f"missing {missing}" if missing else "")
    if missing:
        print("ADR_1561_DRAW_19_SCREEN|not-drawn")
        return 1

    partitions = R.assign_partitions()
    derived = {f: partitions.get(f) for f in DRAW_19}
    check("the split key assigns the preregistered partitions",
          derived == DRAW_19, f"{derived}")
    print("  cycle order by primary module:")
    for f in sorted(DRAW_19, key=lambda x: R.FAMILY_MODULES[x][0]):
        print(f"    {R.FAMILY_MODULES[f][0]:40s} {f:34s} {partitions[f]}")

    for f in DRAW_19:
        modules = R.FAMILY_MODULES[f]
        check(f"{f}: its tuple is in plain alphabetical order",
              list(modules) == sorted(modules), f"{list(modules)}")

    existing_rows, existing_partition, _ = ADJ.resolve_families(R)
    published = {f: rows for f, rows in existing_rows.items()
                 if existing_partition.get(f) in ("development", "train")}
    barred = ADJ.barred_modules(ADJ.load_refusals())
    print(f"  published development/train families scored against: {len(published)}"
          f" (includes this draw's own two)")
    print(f"  modules barred do-not-draw-held-out: {sorted(barred)}")

    for f, want in DRAW_19.items():
        ten = tuple(r.name for r in existing_rows.get(f, ()))
        check(f"{f}: {R.PER_FAMILY} rows drawn", len(ten) == R.PER_FAMILY,
              f"{len(ten)}")
        check(f"{f}: no row is rfl under our construction",
              not (set(ten) & DEFINITIONAL), f"{sorted(set(ten) & DEFINITIONAL)}")
        if want != "held-out":
            continue
        check(f"{f}: no drawn module is barred do-not-draw-held-out",
              not (set(R.FAMILY_MODULES[f]) & set(barred)))
        finding = ADJ.screen_family(
            f, list(existing_rows[f]),
            {k: v for k, v in published.items() if k != f},
            {**existing_partition, **DRAW_19}, env=env, reviews={},
            require_disclosure=False)
        check(f"{f}: R11 clean against every published dev/train family",
              finding.verdict == "clean",
              f"vocabulary {finding.vocabulary_rows}/{R.PER_FAMILY}, "
              f"topics {list(finding.topic_hits)}, {list(finding.reasons)}")
        check(f"{f}: R9 clean -- no drawn name is already declared here",
              not [n for n in ten if n in env],
              f"{[n for n in ten if n in env]}")
        closed = [n for n in ten if CEV.is_closed_evaluation(inventory[n]["type"])]
        check(f"{f}: R12 clean -- no drawn row is a closed evaluation",
              not closed, f"{closed}")

    # --------------------------------------------- 2. definitional-row control
    # A check that no ten carries a definitional row is worth nothing until it
    # is shown it CAN see one. Build the ten `Mathlib.NumberTheory.Chebyshev` +
    # `PrimeCounting` draws -- ADR-1559 measured that it DOES carry the row --
    # and require the same predicate to fire on it.
    pool_before = unowned_pool(inventory, registry, admissible,
                               exclude_owned_by=set(DRAW_19))
    control_ten = ten_of(("Mathlib.NumberTheory.Chebyshev",
                          "Mathlib.NumberTheory.PrimeCounting"), pool_before)
    check("CONTROL the definitional-row check fires on a ten that has one",
          bool(set(control_ten) & DEFINITIONAL),
          f"{sorted(set(control_ten) & DEFINITIONAL)}")

    # ------------------------------------------- 3. the draw-10 deferral, cost
    # Reconstruct the pool draw 19 chose from -- this draw's own four families
    # give their modules back -- and measure what withholding draw 10's two
    # deferred modules costs. `published` here is the pre-draw one, which is the
    # state the choice was made in.
    published_before = {f: rows for f, rows in existing_rows.items()
                        if existing_partition.get(f) in ("development", "train")
                        and f not in DRAW_19}
    for label, withheld in (("neither withheld", set()),
                            ("PythagoreanTriples withheld",
                             {"Mathlib.NumberTheory.PythagoreanTriples"}),
                            ("SumTwoSquares withheld",
                             {"Mathlib.NumberTheory.SumTwoSquares"}),
                            ("both withheld", DRAW_10_DEFERRED)):
        pool = {m: v for m, v in pool_before.items() if m not in withheld}
        bundles = clean_heldout_bundles(pool, inventory, published_before,
                                        existing_partition, barred, env, MAXMOD)
        pairs = disjoint_pairs(bundles)
        print(f"  draw-10 deferral, {label:28s}: clean bundles "
              f"{len(bundles):4d}, module-disjoint pairs {len(pairs):4d}")
        if withheld:
            check(f"withholding {label} leaves R5 unsatisfiable", not pairs,
                  f"{len(pairs)} pair(s)")
        else:
            check("with both available, R5 IS satisfiable", bool(pairs),
                  f"{len(pairs)} pair(s)")
            available_pairs = len(pairs)

    # ------------------------------------------------ 4. the coherence finding
    coherent = clean_heldout_bundles(pool_before, inventory, published_before,
                                     existing_partition, barred, env, MAXMOD,
                                     min_prefix=2)
    coherent_pairs = disjoint_pairs(coherent)
    for combo, _, finding in coherent:
        print(f"    topically tight, clean: vocabulary "
              f"{finding.vocabulary_rows}/{R.PER_FAMILY}  {list(combo)}")
    check("R5 cannot be met from topically tight held-out families",
          not coherent_pairs,
          f"{len(coherent)} clean bundle(s), {len(coherent_pairs)} disjoint pair(s)")

    # ------------------------------------------------------- CONTROL for 3 & 4
    # ADR-1556's working control: lift ADR-1450's `Mathlib.Data.Nat.Count` bar,
    # which shares no module with anything above, and require MORE pairs. A
    # search that cannot produce a different answer is not a measurement.
    control_barred = {m: e for m, e in barred.items()
                      if m != "Mathlib.Data.Nat.Count"}
    control_bundles = clean_heldout_bundles(pool_before, inventory,
                                            published_before,
                                            existing_partition, control_barred,
                                            env, MAXMOD)
    control_pairs = disjoint_pairs(control_bundles)
    print(f"  CONTROL (ADR-1450's Nat.Count bar lifted): "
          f"{len(control_bundles)} clean bundles, {len(control_pairs)} pairs")
    check("CONTROL the disjointness search responds to the barred set",
          len(control_pairs) > available_pairs,
          f"{len(control_pairs)} vs {available_pairs}")

    # A held-out family scored against a published family it shares a topic with
    # must be REFUSED, or the R11 screen above is decoration.
    victim = "power-and-square-decompositions"
    fake = dict(published)
    fake["__topic_twin__"] = list(existing_rows[victim])
    twin_finding = ADJ.screen_family(
        victim, list(existing_rows[victim]),
        {k: v for k, v in fake.items() if k != victim},
        {**existing_partition, **DRAW_19, "__topic_twin__": "development"},
        env=env, reviews={}, require_disclosure=False)
    check("CONTROL R11 refuses a family whose topics a dev family publishes",
          twin_finding.verdict == "refused",
          f"{twin_finding.verdict}")

    print()
    print(f"ADR_1561_DRAW_19_SCREEN|env={len(env)}"
          f"|families={len(DRAW_19)}"
          f"|held_out={sum(1 for v in DRAW_19.values() if v == 'held-out')}"
          f"|pairs_with_draw10_modules={available_pairs}"
          f"|pairs_without={0}"
          f"|coherent_bundles={len(coherent)}"
          f"|coherent_pairs={len(coherent_pairs)}"
          f"|failures={len(failures)}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
