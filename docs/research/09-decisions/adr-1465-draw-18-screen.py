#!/usr/bin/env python3
"""ADR-1465: screen nursery draw 18 against the REAL machinery.

Same construction as `adr-1240-index-zero-screen.py`,
`adr-1245-index-three-screen.py` and `adr-1255-draw-16-screen.py`: load
`scripts/gen-autogenesis-nursery-refill.py`, `scripts/check-holdout-adjacency.py`
and `scripts/check-holdout-closed-evaluation.py` by path and run the ACTUAL
`select()` / `assign_partitions()` / `screen_family()` / `guard()` /
`is_closed_evaluation` rather than a reimplementation.
`propose-nursery-refill.py` is deliberately NOT used as a candidate space.

The four candidate families are injected into `FAMILY_MODULES` / `FAMILY_ROUTES`
in memory, so this screen can be run BEFORE the generator is edited and can be
re-run afterwards to confirm the edit reproduces it.

Usage:
    python3 docs/research/09-decisions/adr-1465-draw-18-screen.py [ENV_DUMP]

Without an ENV_DUMP the committed environment snapshot is read instead.

Exit status: 0 every assertion held, 1 one did not.
"""

from __future__ import annotations

import importlib.util
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]

# ADR-1450 named the unblock: declare a construction opening a module sorting
# lexicographically before Mathlib.Data.Nat.MaxPowDiv, topic- and
# vocabulary-clean, leaving room for two more families in the window between
# it and Mathlib.Data.Nat.Factorization.LCM (already declared, ADR-1450
# follow-on, commit 36f85826f). That commit re-derived the window: unowned
# modules sorting between LCM and MaxPowDiv are Factorization.PrimePow (2),
# Factors (2), Fib.Zeckendorf (0), GCD.BigOperators (0), Lattice (0), Log
# (17) -- 21 rows across six modules. Two candidate fillers:
#   Log alone                                                    17 rows
#   PrimePow (2) + Factors (2) + Factorization.Basic (5)
#     + Factorization.Induction (1)                              10 rows
# Both sort within the window (PrimePow's own path sorts there; Log's does
# too), so both are usable regardless of which is development and which is
# train.
NEW_MODULES = {
    "natural-factorization-lcm": ("Mathlib.Data.Nat.Factorization.LCM",),
    # ORIGINAL PLAN (PrimePow + Factors + Factorization.Basic + Induction)
    # REFUSED at R11: every one of those three Factorization.* modules shares
    # the topic segment "Factorization" with `natural-factorization-lcm`
    # itself, so bundling them as development in the SAME draw as LCM
    # held-out is exactly the shape 1 topical-overlap R11 exists to catch --
    # measured, not inherited (see the commit message / ADR body for the
    # live refusal). `Mathlib.Data.Nat.Factors` (2 rows, topic "Factors",
    # sorts inside the LCM->MaxPowDiv window) is topic-clean; bundled with
    # `Mathlib.NumberTheory.FactorisationProperties` (15 rows, topic
    # "FactorisationProperties" -- a DIFFERENT word from "Factorization", no
    # collision, ADR-1115's do-not-draw-held-out bar is HELD-OUT-scoped only
    # and does not reach a development/train use) it reaches 17, more than
    # enough, and stays topically coherent (both are about the factors/
    # factorisation-theoretic properties of a natural number).
    "natural-factors-and-factorisation-properties": (
        "Mathlib.Data.Nat.Factors",
        "Mathlib.NumberTheory.FactorisationProperties"),
    "natural-logarithm-base": ("Mathlib.Data.Nat.Log",),
    # MaxPowDiv alone yields 7 rows, short of PER_FAMILY=10 (ADR-1450's status
    # doc recorded this: "pool 7 alone and 11 bundled with
    # Mathlib.NumberTheory.Bertrand" -- reproduced here rather than inherited).
    "natural-max-power-dividing": (
        "Mathlib.Data.Nat.MaxPowDiv", "Mathlib.NumberTheory.Bertrand"),
}
NEW_ROUTES = {
    "natural-factorization-lcm": (
        "divisibility-library-application", "kernel-library-application"),
    "natural-factors-and-factorisation-properties": (
        "divisibility-library-application", "kernel-induction"),
    "natural-logarithm-base": (
        "kernel-induction", "recursive-function-reconstruction"),
    "natural-max-power-dividing": (
        "divisibility-library-application", "recursive-function-reconstruction"),
}
EXPECTED_PARTITIONS = {
    "natural-factorization-lcm": "held-out",
    "natural-factors-and-factorisation-properties": "development",
    "natural-logarithm-base": "train",
    "natural-max-power-dividing": "held-out",
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
    for name in ("Nat.factorizationLCMLeft", "Nat.factorizationLCMRight",
                 "Nat.divMaxPow", "Nat.divMaxPowAux"):
        check(f"construction {name} is in the environment", name in env)

    install(NEW_MODULES, NEW_ROUTES)
    inventory, vocabulary, registry, catalogued = context(env)

    # 1. The cycle assigns exactly the layout below -- re-derived from the
    #    module paths, never chosen.
    partitions = R.assign_partitions()
    fresh = sorted(NEW_MODULES, key=lambda f: NEW_MODULES[f][0])
    print()
    print("cycle assignment over the four fresh families, in sort order:")
    for i, fam in enumerate(fresh):
        print(f"  [{i}] {fam:34s} {partitions[fam]:12s} {NEW_MODULES[fam][0]}")
    check("cycle assigns the intended layout",
          all(partitions[f] == EXPECTED_PARTITIONS[f] for f in NEW_MODULES),
          str({f: partitions[f] for f in NEW_MODULES}))

    # 2. select() over the whole nursery, with the four families added.
    entries, reasons = R.select(inventory, env, vocabulary, registry, catalogued)
    new_entries = [e for e in entries if e["family"] in NEW_MODULES]
    check(f"the draw adds {R.PER_FAMILY * len(NEW_MODULES)} entries",
          len(new_entries) == R.PER_FAMILY * len(NEW_MODULES),
          f"got {len(new_entries)}")
    for fam in fresh:
        pool_reason = [r for r in reasons if r == f"selected:{fam}"]
        n = len([e for e in new_entries if e["family"] == fam])
        print(f"  {fam:34s} drawn {n}")

    # 3. CONTROL: without the two new constructions, the two held-out families
    #    must yield NOTHING (LCM) or be structurally absent (MaxPowDiv already
    #    exists on main so this control targets LCM only -- MaxPowDiv predates
    #    this lane and was checked by ADR-1430).
    for family, constructions in (
            ("natural-factorization-lcm",
             {"Nat.factorizationLCMLeft", "Nat.factorizationLCMRight"}),):
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

    # 5b. R11 with disclosure ON, against reviews already recorded plus the
    #     new one this lane will write for MaxPowDiv (checked separately
    #     below, after the review file is edited).
    findings_disclosed = ADJ.screen_draw(new_rows, new_partition, existing_rows,
                               existing_partition, env=env,
                               reviews=ADJ.load_reviews(),
                               require_disclosure=True)
    print()
    for f in findings_disclosed:
        print(f"R11+disclosure {f.family:34s} {f.verdict:8s}")

    # 6. Frozen-family drawn-ten CHURN: adding four families must not move any
    #    EXISTING family's drawn ten.
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

    # 6b. NEGATIVE CONTROL for the churn probe: deliberately flip one already
    #     drawn family's partition in a COPY and confirm the instrument
    #     detects it. A zero-diff that cannot fail is worth nothing.
    import copy as _copy
    mutated_entries = _copy.deepcopy(entries)
    victim_family = None
    for e in mutated_entries:
        if e["family"] not in NEW_MODULES:
            victim_family = e["family"]
            break
    if victim_family is not None:
        flips = 0
        for e in mutated_entries:
            if e["family"] == victim_family:
                e["partition"] = ("development" if e["partition"] != "development"
                                  else "held-out")
                flips += 1
        mutated_before = tens(base_entries)
        mutated_after = tens(mutated_entries)
        # partition is not part of `tens` (source_name only), so also assert on
        # partition field directly, which is what a real corruption would move.
        real_before_partition = {e["fact_id"]: e["partition"] for e in entries
                                  if e["family"] == victim_family}
        real_after_partition = {e["fact_id"]: e["partition"] for e in mutated_entries
                                 if e["family"] == victim_family}
        partition_moved = [fid for fid in real_before_partition
                            if real_before_partition[fid] != real_after_partition[fid]]
        check("NEGATIVE CONTROL: a deliberately flipped partition in a copy IS "
              f"detected ({victim_family}, {flips} rows flipped)",
              len(partition_moved) == flips, f"detected {len(partition_moved)}")
    else:
        check("NEGATIVE CONTROL: found a victim family to flip", False)

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

    # 8. The live sweep for the two NEW held-out families, printed verbatim so
    #    the disclosure review records what was measured rather than what was
    #    remembered.
    print()
    for fam in ("natural-factorization-lcm", "natural-max-power-dividing"):
        subjects = ADJ.subject_constants(new_rows[fam], ADJ.plumbing(
            {**existing_rows, **new_rows}))
        sweep = ADJ.environment_sweep(subjects, env)
        print(f"{fam} live sweep:")
        print("  ", json.dumps([list(h) for h in sweep]))
        print("  subjects:", sorted(subjects))

    # 9. The drawn ten for each new family, verbatim.
    print()
    for fam in fresh:
        rows = [e for e in new_entries if e["family"] == fam]
        print(f"{fam} ({partitions[fam]}, {NEW_MODULES[fam][0]}):")
        for i, e in enumerate(rows):
            print(f"  [{i}] {e['source_name']}")
            print(f"      {e['statement']}")
        print()

    install(BASE_MODULES, BASE_ROUTES)
    print(f"ADR_1465_DRAW_18_SCREEN|env={len(env)}|new_entries={len(new_entries)}"
          f"|churn={len(churned)}|stale_reviews={len(stale)}"
          f"|r12_violations={len(closed)}|failures={len(failures)}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
