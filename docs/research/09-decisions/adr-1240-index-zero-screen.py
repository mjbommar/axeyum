#!/usr/bin/env python3
"""ADR-1240: screen the index-0 candidate against the REAL refill machinery.

Loads `scripts/gen-autogenesis-nursery-refill.py`,
`scripts/check-holdout-adjacency.py` and
`scripts/check-holdout-closed-evaluation.py` by path, injects hypothetical
constructions into the environment, and runs the ACTUAL
`select()` / `assign_partitions()` / `screen_family()` / `is_closed_evaluation`
rather than a reimplementation. `propose-nursery-refill.py` is deliberately not
used as a candidate space: it mirrors only the hygiene screen and both over-
and under-counts (ADR-1160, ADR-1220).

Usage:
    python3 docs/research/09-decisions/adr-1240-index-zero-screen.py [ENV_DUMP]

`ENV_DUMP` is the stdout of

    cargo run --release -p axeyum-lean-kernel --example shape_search -- \
      --include-constructed --limit 999999 --kind axiom --kind definition \
      --kind theorem --kind inductive --kind constructor --kind recursor

Without it the committed environment snapshot is read instead. Rebuild
`shape_search` first: a stale prebuilt binary reports a false ABSENT, which is
the expensive verdict here.

Exit status: 0 every assertion held, 1 one did not.
"""

from __future__ import annotations

import importlib.util
import json
import pathlib
import sys
from collections import Counter

ROOT = pathlib.Path(__file__).resolve().parents[3]

# The constructions this ADR declares. `Nat.Primrec` is an inductive `Prop`, so
# its constructors and recursor enter the environment with it; `Nat.casesOn` is
# a plain definition over `Nat.rec`.
PRIMREC = {
    "Nat.Primrec", "Nat.Primrec.zero", "Nat.Primrec.succ", "Nat.Primrec.left",
    "Nat.Primrec.right", "Nat.Primrec.pair", "Nat.Primrec.comp",
    "Nat.Primrec.prec", "Nat.Primrec.rec", "Nat.casesOn",
}
MODULE = "Mathlib.Computability.Primrec.Basic"


def load(path: pathlib.Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


R = load(ROOT / "scripts/gen-autogenesis-nursery-refill.py", "_refill")
ADJ = load(ROOT / "scripts/check-holdout-adjacency.py", "_adj")
CEV = load(ROOT / "scripts/check-holdout-closed-evaluation.py", "_cev")

ENV_DUMP = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else None


def context(extra_constants=frozenset()):
    """Everything `main()` hands to `select()`, plus injected constructions."""
    if ENV_DUMP is not None:
        snapshot = R.parse_env_dump(ENV_DUMP.read_text())
    else:
        snapshot = R.load_json(R.ENV_SNAPSHOT)
    env = set(snapshot["declarations"]) | set(extra_constants)
    inventory = R.read_inventory()
    catalog = R.load_json(R.CATALOG)
    registry = R.load_json(R.REGISTRY)["constructions"]
    facts = {}
    for path in sorted(R.FACTS.glob("*.json")):
        facts[json.loads(path.read_text())["id"]] = json.loads(path.read_text())
    vocabulary = R.read_vocabulary(env, inventory, catalog, facts)
    catalogued = {row["source_name"] for row in catalog["facts"]
                  if row["kind"] == "external-source"}
    return env, inventory, vocabulary, registry, catalogued


def pool_for(modules, env, inventory, vocabulary, registry, catalogued):
    """The screened pool for a module set, mirroring `select()`'s body."""
    adm = R.admissible(env, vocabulary)
    out, reasons = [], Counter()
    for name in sorted(inventory):
        record = inventory[name]
        if record["module"] not in modules:
            continue
        if name in catalogued:
            reasons["already-catalogued"] += 1
            continue
        if R.HYGIENE.search(name):
            reasons["hygienic-or-generated"] += 1
            continue
        constants = set(R.CONST_RE.findall(record["type_repr"]))
        if constants - adm:
            reasons["not-statable-here"] += 1
            continue
        if constants & R.HELD_OUT_CONSTRUCTIONS:
            reasons["held-out-construction"] += 1
            continue
        if R.blockers_for(record["type"], registry):
            reasons["divergence-registry"] += 1
            continue
        out.append({"source_name": name, "module": record["module"],
                    "statement": record["type"],
                    "constants": sorted(constants)})
    return out, reasons


def drawn_tens(extra):
    """Every family's drawn ten under an environment, via the real `select()`."""
    env, inv, vocab, reg, cat = context(extra)
    entries, _ = R.select(inv, env, vocab, reg, cat)
    out: dict[str, list[str]] = {}
    for entry in entries:
        out.setdefault(entry["family"], []).append(entry["source_name"])
    return out


def main() -> int:
    failures = []

    def check(label, ok, detail=""):
        print(f"{'ok  ' if ok else 'FAIL'}  {label}{'  ' + detail if detail else ''}")
        if not ok:
            failures.append(label)

    env, inv, vocab, reg, cat = context()
    landed = PRIMREC <= env
    print(f"environment: {len(env)} declarations "
          f"({'live dump' if ENV_DUMP else 'committed snapshot'}); "
          f"constructions {'LANDED' if landed else 'not yet declared'}")

    # 1. The CONTROL, and it must hold whether or not the constructions have
    #    landed yet: with `Nat.Primrec`/`Nat.casesOn` absent the module yields
    #    NOTHING, so the pool this ADR reports is caused by them and by nothing
    #    else. Before the declaration that is the ambient environment; after it,
    #    the constants have to be removed to ask the same question.
    without = {c for c in env if c not in PRIMREC}
    vocab_without = R.read_vocabulary(
        without, inv, R.load_json(R.CATALOG),
        {json.loads(f.read_text())["id"]: json.loads(f.read_text())
         for f in sorted(R.FACTS.glob("*.json"))})
    before, _ = pool_for((MODULE,), without, inv, vocab_without, reg, cat)
    check("control: pool WITHOUT the constructions is 0",
          len(before) == 0, f"got {len(before)}")

    # 2. `Nat.Primrec` and `Nat.casesOn` are the ONLY missing constants, and
    #    `Nat.unpaired` (ADR-1220) is already admissible.
    adm = R.admissible(env, vocab)
    check("Nat.unpaired is admissible", "Nat.unpaired" in adm)

    # 3. With them the pool reaches PER_FAMILY.
    env2, inv2, vocab2, reg2, cat2 = context(PRIMREC)
    after, _ = pool_for((MODULE,), env2, inv2, vocab2, reg2, cat2)
    check(f"pool with constructions >= {R.PER_FAMILY}",
          len(after) >= R.PER_FAMILY, f"got {len(after)}")

    # 4. No drawn row is a constructor of the inductive being declared -- a row
    #    the construction itself settles would be spent the moment it lands.
    ctors = {n for n in PRIMREC if n != "Nat.Primrec" and n != "Nat.casesOn"}
    drawn = [c["source_name"] for c in after[:R.PER_FAMILY]]
    check("no drawn row is a constructor of Nat.Primrec",
          not (set(drawn) & ctors))

    # 5. R12, the real classifier, over the drawn ten.
    closed = [c["source_name"] for c in after[:R.PER_FAMILY]
              if CEV.is_closed_evaluation(c["statement"])]
    check("R12: no drawn row is a closed evaluation", not closed, str(closed))

    # 6. Frozen-family drawn-ten CHURN (ADR-1220's first new screen).
    base_tens, new_tens = drawn_tens(frozenset()), drawn_tens(PRIMREC)
    churned = [f for f in set(base_tens) | set(new_tens)
               if base_tens.get(f, []) != new_tens.get(f, [])]
    check("no frozen family's drawn ten churns", not churned, str(churned))

    # 7. Stale recorded REVIEW (ADR-1220's second new screen).
    rows, partition, _ = ADJ.resolve_families(R)
    reviews = ADJ.load_reviews()
    stale = []
    for family in sorted(rows):
        if partition.get(family) != "held-out":
            continue
        published = {k: v for k, v in rows.items() if k != family}
        finding = ADJ.screen_family(family, rows[family], published, partition,
                                    env=env | PRIMREC, reviews=reviews,
                                    require_disclosure=False)
        if finding.verdict != "clean":
            stale.append((family, finding.reasons))
    check("no held-out family's recorded review goes stale", not stale, str(stale))

    print()
    print(f"drawn ten for {MODULE}:")
    for i, cand in enumerate(after[:R.PER_FAMILY]):
        print(f"  [{i}] {cand['source_name']}")
        print(f"      {cand['statement']}")

    print()
    print(f"ADR_1240_INDEX_ZERO_SCREEN|env={len(env)}|pool_before={len(before)}"
          f"|pool_after={len(after)}|churn={len(churned)}|stale_reviews={len(stale)}"
          f"|failures={len(failures)}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
