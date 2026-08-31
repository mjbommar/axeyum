#!/usr/bin/env python3
"""ADR-1255: screen nursery draw 16 (layout RP) against the REAL machinery.

Same construction as `adr-1240-index-zero-screen.py` and
`adr-1245-index-three-screen.py`: load
`scripts/gen-autogenesis-nursery-refill.py`,
`scripts/check-holdout-adjacency.py` and
`scripts/check-holdout-closed-evaluation.py` by path and run the ACTUAL
`select()` / `assign_partitions()` / `screen_family()` / `guard()` /
`is_closed_evaluation` rather than a reimplementation.
`propose-nursery-refill.py` is deliberately NOT used as a candidate space: it
mirrors only the hygiene screen and OVERCOUNTS (ADR-1160 measured 21 against a
real 6).

The four candidate families are injected into `FAMILY_MODULES` /
`FAMILY_ROUTES` in memory, so this screen can be run BEFORE the generator is
edited and can be re-run afterwards to confirm the edit reproduces it.

Usage:
    python3 docs/research/09-decisions/adr-1255-draw-16-screen.py [ENV_DUMP]

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

ROOT = pathlib.Path(__file__).resolve().parents[3]

# Layout RP (ADR-1220), with the two held-out slots filled by ADR-1240 and
# ADR-1245. The cycle is mechanical over the primary module sorted
# lexicographically, so these four sort 0..3 in exactly this order and the
# held-out slots land at 0 and 3 by sort order rather than by arrangement.
NEW_MODULES = {
    "natural-primitive-recursion": ("Mathlib.Computability.Primrec.Basic",),
    "natural-fibonacci-basic": (
        "Mathlib.Data.Int.Fib.Basic", "Mathlib.Data.Nat.Fib.Basic"),
    "natural-prime-divisibility": (
        "Mathlib.Data.Int.NatPrime", "Mathlib.Data.Nat.GCD.Prime",
        "Mathlib.Data.Nat.Prime.Factorial", "Mathlib.Data.Nat.Prime.Int",
        "Mathlib.RingTheory.Int.Basic"),
    "natural-integer-root": ("Mathlib.Data.Nat.Factorization.Root",),
}
NEW_ROUTES = {
    "natural-primitive-recursion": (
        "kernel-induction", "recursive-function-reconstruction"),
    "natural-fibonacci-basic": (
        "kernel-induction", "recursive-function-reconstruction"),
    "natural-prime-divisibility": (
        "divisibility-library-application", "kernel-library-application"),
    "natural-integer-root": (
        "divisibility-library-application", "kernel-induction"),
}
EXPECTED_PARTITIONS = {
    "natural-primitive-recursion": "held-out",
    "natural-fibonacci-basic": "development",
    "natural-prime-divisibility": "train",
    "natural-integer-root": "held-out",
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

BASE_MODULES = dict(R.FAMILY_MODULES)
BASE_ROUTES = dict(R.FAMILY_ROUTES)


def install(new_modules, new_routes):
    R.FAMILY_MODULES.clear()
    R.FAMILY_MODULES.update(BASE_MODULES)
    R.FAMILY_MODULES.update(new_modules)
    R.FAMILY_ROUTES.clear()
    R.FAMILY_ROUTES.update(BASE_ROUTES)
    R.FAMILY_ROUTES.update(new_routes)


def env_set():
    if ENV_DUMP is not None:
        snapshot = R.parse_env_dump(ENV_DUMP.read_text())
    else:
        snapshot = R.load_json(R.ENV_SNAPSHOT)
    return set(snapshot["declarations"])


def context(env):
    inventory = R.read_inventory()
    catalog = R.load_json(R.CATALOG)
    registry = R.load_json(R.REGISTRY)["constructions"]
    facts = {}
    for path in sorted(R.FACTS.glob("*.json")):
        fact = json.loads(path.read_text())
        facts[fact["id"]] = fact
    vocabulary = R.read_vocabulary(env, inventory, catalog, facts)
    catalogued = {row["source_name"] for row in catalog["facts"]
                  if row["kind"] == "external-source"}
    return inventory, vocabulary, registry, catalogued


def main() -> int:
    failures = []

    def check(label, ok, detail=""):
        print(f"{'ok  ' if ok else 'FAIL'}  {label}{'  ' + detail if detail else ''}")
        if not ok:
            failures.append(label)

    env = env_set()
    print(f"environment: {len(env)} declarations "
          f"({'live dump' if ENV_DUMP else 'committed snapshot'})")
    for name in ("Nat.Primrec", "Nat.casesOn", "Nat.floorRoot", "Nat.ceilRoot"):
        check(f"construction {name} is in the environment", name in env)

    install(NEW_MODULES, NEW_ROUTES)
    inventory, vocabulary, registry, catalogued = context(env)

    # 1. The cycle assigns exactly layout RP -- re-derived from the module
    #    paths, never chosen.
    partitions = R.assign_partitions()
    fresh = sorted(NEW_MODULES, key=lambda f: NEW_MODULES[f][0])
    print()
    print("cycle assignment over the four fresh families, in sort order:")
    for i, fam in enumerate(fresh):
        print(f"  [{i}] {fam:34s} {partitions[fam]:12s} {NEW_MODULES[fam][0]}")
    check("cycle reproduces layout RP",
          all(partitions[f] == EXPECTED_PARTITIONS[f] for f in NEW_MODULES),
          str({f: partitions[f] for f in NEW_MODULES}))

    # 2. select() over the whole nursery, with the four families added.
    entries, reasons = R.select(inventory, env, vocabulary, registry, catalogued)
    new_entries = [e for e in entries if e["family"] in NEW_MODULES]
    check(f"the draw adds {R.PER_FAMILY * len(NEW_MODULES)} entries",
          len(new_entries) == R.PER_FAMILY * len(NEW_MODULES),
          f"got {len(new_entries)}")

    # 3. CONTROL: without ADR-1240/ADR-1245's constructions the two held-out
    #    families must yield NOTHING, so the pools reported here are caused by
    #    them and by nothing else.
    for family, constructions in (
            ("natural-primitive-recursion", {"Nat.Primrec", "Nat.casesOn"}),
            ("natural-integer-root", {"Nat.floorRoot", "Nat.ceilRoot"})):
        env0 = env - constructions
        inv0, vocab0, reg0, cat0 = context(env0)
        try:
            e0, _ = R.select(inv0, env0, vocab0, reg0, cat0)
            got = len([e for e in e0 if e["family"] == family])
            check(f"control: {family} yields 0 without its constructions",
                  got == 0, f"got {got}")
        except R.RefillError as exc:
            check(f"control: {family} yields 0 without its constructions",
                  "yields 0 screened candidates" in str(exc)
                  or f"'{family}'" in str(exc), str(exc)[:160])

    # 4. R12, the real classifier, over every new HELD-OUT row.
    closed = [e["source_name"] for e in new_entries
              if e["partition"] == "held-out"
              and CEV.is_closed_evaluation(e["statement"])]
    check("R12: no new held-out row is a closed evaluation", not closed, str(closed))

    # 5. R11's hard signals, with the disclosure demand OFF, so topic and
    #    vocabulary are read separately from the review question.
    existing_rows, existing_partition, _ = ADJ.resolve_families(R)
    new_rows: dict[str, list] = {}
    new_partition: dict[str, str] = {}
    for e in new_entries:
        new_partition[e["family"]] = e["partition"]
        new_rows.setdefault(e["family"], []).append(
            ADJ.Row(e["source_name"], e["module"], frozenset(e["constants"])))
    for fam in new_rows:
        existing_rows.pop(fam, None)
    findings = ADJ.screen_draw(new_rows, new_partition, existing_rows,
                               existing_partition, env=env,
                               reviews=ADJ.load_reviews(),
                               require_disclosure=False)
    print()
    for f in findings:
        print(f"R11 {f.family:34s} {f.verdict:8s} topic={len(f.topic_hits)} "
              f"vocab={f.vocabulary_rows}/10 env={[h[0] for h in f.environment_hits]}")
        for reason in f.reasons:
            print(f"      {reason}")
    check("R11 hard signals clean (disclosure off)",
          all(f.verdict == "clean" for f in findings))

    # 6. Frozen-family drawn-ten CHURN (ADR-1220's first screen): adding four
    #    families must not move any EXISTING family's drawn ten.
    install(BASE_MODULES, BASE_ROUTES)
    base_entries, _ = R.select(inventory, env, vocabulary, registry, catalogued)
    install(NEW_MODULES, NEW_ROUTES)
    def tens(rows):
        out: dict[str, list[str]] = {}
        for e in rows:
            out.setdefault(e["family"], []).append(e["source_name"])
        return out
    before_t, after_t = tens(base_entries), tens(entries)
    churned = [f for f in sorted(before_t)
               if before_t[f] != after_t.get(f, [])]
    check("no existing family's drawn ten churns", not churned, str(churned))

    # 7. Stale recorded REVIEW over every standing held-out family.
    rows_all, partition_all, _ = ADJ.resolve_families(R)
    reviews = ADJ.load_reviews()
    stale = []
    for family in sorted(rows_all):
        if partition_all.get(family) != "held-out":
            continue
        published = {k: v for k, v in rows_all.items() if k != family}
        finding = ADJ.screen_family(family, rows_all[family], published,
                                    partition_all, env=env, reviews=reviews,
                                    require_disclosure=False)
        if finding.verdict != "clean":
            stale.append((family, finding.reasons))
    check("no standing held-out family's recorded review goes stale",
          not stale, str(stale))

    # 7b. THE REVERSE DIRECTION, which no gate asks for. `cmd_check` scores a
    #     held-out family only against families drawn NO LATER than itself, so
    #     a NEW development/train family cannot make a STANDING held-out family
    #     go red however adjacent it is. That is deliberate (a later draw must
    #     not retroactively refuse the standing population) and it is not a
    #     licence to publish a subject an existing held-out family owns. Scored
    #     here with the draw-membership filter REMOVED.
    print()
    print("reverse adjacency: every STANDING held-out family scored against "
          "this draw's development/train families (no gate asks this):")
    reverse = []
    publishing = {f: new_rows[f] for f in new_rows
                  if new_partition[f] in ("development", "train")}
    pub_part = {f: new_partition[f] for f in publishing}
    for family in sorted(rows_all):
        if partition_all.get(family) != "held-out":
            continue
        others = {k: v for k, v in rows_all.items() if k != family}
        others.update(publishing)
        part = dict(partition_all)
        part.update(pub_part)
        base = ADJ.screen_family(family, rows_all[family],
                                 {k: v for k, v in rows_all.items() if k != family},
                                 partition_all, env=env, reviews=reviews,
                                 require_disclosure=False)
        with_new = ADJ.screen_family(family, rows_all[family], others, part,
                                     env=env, reviews=reviews,
                                     require_disclosure=False)
        moved = (len(base.topic_hits), base.vocabulary_rows) != \
                (len(with_new.topic_hits), with_new.vocabulary_rows)
        if moved:
            reverse.append((family, len(base.topic_hits), base.vocabulary_rows,
                            len(with_new.topic_hits), with_new.vocabulary_rows,
                            with_new.verdict))
        print(f"  {family:36s} topic {len(base.topic_hits)}->"
              f"{len(with_new.topic_hits)}  vocab {base.vocabulary_rows}->"
              f"{with_new.vocabulary_rows}  {with_new.verdict}"
              + ("   <- MOVED" if moved else ""))
    check("no standing held-out family's signals move under this draw's "
          "development/train families", not reverse, str(reverse))

    # 8. The live sweep for the two NEW held-out families, printed verbatim so
    #    the disclosure review records what was measured rather than what was
    #    remembered.
    print()
    for fam in ("natural-primitive-recursion", "natural-integer-root"):
        subjects = ADJ.subject_constants(new_rows[fam], ADJ.plumbing(
            {**existing_rows, **new_rows}))
        sweep = ADJ.environment_sweep(subjects, env)
        print(f"{fam} live sweep:")
        print("  ", json.dumps([list(h) for h in sweep]))
        print("  subjects:", sorted(subjects))

    # 9. The drawn ten for each new family, verbatim, for the ADR-1160 READING.
    print()
    for fam in fresh:
        rows = [e for e in new_entries if e["family"] == fam]
        print(f"{fam} ({partitions[fam]}, {NEW_MODULES[fam][0]}):")
        for i, e in enumerate(rows):
            print(f"  [{i}] {e['source_name']}")
            print(f"      {e['statement']}")
        print()

    install(BASE_MODULES, BASE_ROUTES)
    print(f"ADR_1255_DRAW_16_SCREEN|env={len(env)}|new_entries={len(new_entries)}"
          f"|churn={len(churned)}|stale_reviews={len(stale)}"
          f"|r12_violations={len(closed)}|failures={len(failures)}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
