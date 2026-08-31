#!/usr/bin/env python3
"""ADR-1245: screen the index-3 candidate against the REAL refill machinery.

Same construction as `adr-1240-index-zero-screen.py`: load
`scripts/gen-autogenesis-nursery-refill.py`,
`scripts/check-holdout-adjacency.py` and
`scripts/check-holdout-closed-evaluation.py` by path and run the ACTUAL
`select()` / `assign_partitions()` / `screen_family()` / `is_closed_evaluation`
rather than a reimplementation. `propose-nursery-refill.py` is deliberately not
used as a candidate space (ADR-1160, ADR-1220).

Usage:
    python3 docs/research/09-decisions/adr-1245-index-three-screen.py [ENV_DUMP]

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

# The two constructions this ADR declares. Both are plain `Definition`s, so
# nothing else enters the environment with them -- unlike ADR-1240's inductive.
ROOTS = {"Nat.ceilRoot", "Nat.floorRoot"}
MODULE = "Mathlib.Data.Nat.Factorization.Root"

# ADR-1240's index-0 constructions, so the four-family layout can be screened
# whether or not they have landed in the environment being read.
PRIMREC = {
    "Nat.Primrec", "Nat.Primrec.zero", "Nat.Primrec.succ", "Nat.Primrec.left",
    "Nat.Primrec.right", "Nat.Primrec.pair", "Nat.Primrec.comp",
    "Nat.Primrec.prec", "Nat.Primrec.rec", "Nat.casesOn",
}


def load(path: pathlib.Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


R = load(ROOT / "scripts/gen-autogenesis-nursery-refill.py", "_refill")
ADJ = load(ROOT / "scripts/check-holdout-adjacency.py", "_adj")
CEV = load(ROOT / "scripts/check-holdout-closed-evaluation.py", "_cev")

ENV_DUMP = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else None
_FACTS = None


def facts():
    global _FACTS
    if _FACTS is None:
        _FACTS = {}
        for path in sorted(R.FACTS.glob("*.json")):
            row = json.loads(path.read_text())
            _FACTS[row["id"]] = row
    return _FACTS


def context(extra_constants=frozenset(), without=frozenset()):
    """Everything `main()` hands to `select()`, plus/minus injected constants."""
    if ENV_DUMP is not None:
        snapshot = R.parse_env_dump(ENV_DUMP.read_text())
    else:
        snapshot = R.load_json(R.ENV_SNAPSHOT)
    env = (set(snapshot["declarations"]) | set(extra_constants)) - set(without)
    inventory = R.read_inventory()
    catalog = R.load_json(R.CATALOG)
    registry = R.load_json(R.REGISTRY)["constructions"]
    vocabulary = R.read_vocabulary(env, inventory, catalog, facts())
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


def drawn_tens(extra, without=frozenset()):
    """Every family's drawn ten under an environment, via the real `select()`."""
    env, inv, vocab, reg, cat = context(extra, without)
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
    landed = ROOTS <= env
    print(f"environment: {len(env)} declarations "
          f"({'live dump' if ENV_DUMP else 'committed snapshot'}); "
          f"constructions {'LANDED' if landed else 'not yet declared'}; "
          f"ADR-1240 primrec {'LANDED' if PRIMREC <= env else 'ABSENT'}")

    # 1. CONTROL. Without the two constructions the module must yield NOTHING,
    #    so the pool reported below is caused by them and by nothing else.
    env0, inv0, vocab0, reg0, cat0 = context(without=ROOTS)
    before, _ = pool_for((MODULE,), env0, inv0, vocab0, reg0, cat0)
    check("control: pool WITHOUT the constructions is 0",
          len(before) == 0, f"got {len(before)}")

    # 2. With them the pool reaches PER_FAMILY.
    env2, inv2, vocab2, reg2, cat2 = context(ROOTS)
    after, _ = pool_for((MODULE,), env2, inv2, vocab2, reg2, cat2)
    check(f"pool with constructions >= {R.PER_FAMILY}",
          len(after) >= R.PER_FAMILY, f"got {len(after)}")

    # 3. R12, the real classifier, over the drawn ten. This is NOT the boundary
    #    reading -- `is_closed_evaluation` is binder-free by construction, so a
    #    quantified defining equation is invisible to it (ADR-1160). The reading
    #    is in the ADR and is definition-relative.
    drawn = after[:R.PER_FAMILY]
    closed = [c["source_name"] for c in drawn
              if CEV.is_closed_evaluation(c["statement"])]
    check("R12: no drawn row is a closed evaluation", not closed, str(closed))

    # 4. Frozen-family drawn-ten CHURN (ADR-1220's first new screen).
    base_tens = drawn_tens(frozenset(), without=ROOTS)
    new_tens = drawn_tens(ROOTS)
    churned = [f for f in sorted(set(base_tens) | set(new_tens))
               if base_tens.get(f, []) != new_tens.get(f, [])]
    check("no frozen family's drawn ten churns", not churned, str(churned))

    # 5. Stale recorded REVIEW (ADR-1220's second new screen). This one is
    #    EXPECTED to fire before the review is redone and to be clean after --
    #    `ceilRoot`/`floorRoot` move `natural-nth-root`'s `root` sweep.
    rows, partition, _ = ADJ.resolve_families(R)
    reviews = ADJ.load_reviews()
    stale = []
    for family in sorted(rows):
        if partition.get(family) != "held-out":
            continue
        published = {k: v for k, v in rows.items() if k != family}
        finding = ADJ.screen_family(family, rows[family], published, partition,
                                    env=env | ROOTS, reviews=reviews,
                                    require_disclosure=False)
        if finding.verdict != "clean":
            stale.append((family, finding.reasons))
    check("no held-out family's recorded review goes stale", not stale, str(stale))

    # 6. The live sweep for `natural-nth-root` under the new constants, printed
    #    so the redone review can record it VERBATIM rather than by hand.
    if "natural-nth-root" in rows:
        subjects = ADJ.subject_constants(
            rows["natural-nth-root"], ADJ.plumbing(rows))
        print()
        print("natural-nth-root live sweep, with the constructions:")
        print("  ", json.dumps([list(h) for h in ADJ.environment_sweep(
            subjects, env | ROOTS)]))
        print("  subjects:", sorted(subjects))

    print()
    print(f"drawn ten for {MODULE} (pool {len(after)}):")
    for i, cand in enumerate(drawn):
        print(f"  [{i}] {cand['source_name']}")
        print(f"      {cand['statement']}")
    print(f"  --- the {len(after) - len(drawn)} rows below the cut ---")
    for cand in after[R.PER_FAMILY:]:
        print(f"      {cand['source_name']}: {cand['statement']}")

    print()
    print(f"ADR_1245_INDEX_THREE_SCREEN|env={len(env)}|pool_before={len(before)}"
          f"|pool_after={len(after)}|churn={len(churned)}"
          f"|stale_reviews={len(stale)}|failures={len(failures)}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
