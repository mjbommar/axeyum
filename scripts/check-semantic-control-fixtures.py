#!/usr/bin/env python3
"""Execute the retained semantic-control fixture pack and gate on the result
(roadmap phase S3).

S3's exit, verbatim: *the known false/vacuous fixture pack is rejected and
known valid controls remain accepted; zero executed cases is always failure.*

This script is that sentence, executable:

* every `false` fixture must produce at least one counterexample;
* every `vacuous` fixture must produce ZERO discriminating instances -- the
  fixture asserts the zero rather than the fixture's own greenness;
* every `valid` fixture must produce no counterexamples, at least one
  discriminating instance, and at least one KILLED mutation, which is what
  makes its control load-bearing rather than merely green;
* **any fixture that executed zero cases fails, whatever its class**, and so
  does a run whose total executed count is zero.

A mutation that is NOT falsified is classified `also-true` and reported for
review.  It is not a failure.  The roadmap says so explicitly, and a gate that
reds on a true mutation is a gate somebody turns off -- which is the same
outcome as not having one.

The pack's verdicts are pinned in `artifacts/semantic-controls/fixture-pack.json`
so a silent change in a model is drift, not a fresh baseline.  `--write`
regenerates that pin and the summary; `--check` (the default) compares.

Usage:

    python3 scripts/check-semantic-control-fixtures.py            # gate
    python3 scripts/check-semantic-control-fixtures.py --write    # re-pin
    python3 scripts/check-semantic-control-fixtures.py --json     # for agents
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys
import time

# How an in-tree numerics script spells its own negative control.  The first
# version of this pattern was the literal string `NEGATIVE CONTROL`, and it
# reported TWO scripts as having none while each carries several spelled
# `GENUINELY FAILS` -- a gate manufacturing a finding about its own subject,
# which is the exact defect this pack exists to catch.  Both spellings, case
# insensitive, and `scripts/tests/test-semantic-control-fixtures.sh` pins that
# a script with genuinely no control still fails.
NEG_CONTROL = re.compile(r"negative control|genuinely fail", re.IGNORECASE)

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

from semantic_control_fixtures import (  # noqa: E402
    FIXTURES,
    NUMERICS_SCRIPTS,
    Fixture,
    Mutation,
    Outcome,
)

__all__ = ["Fixture", "Mutation", "Outcome"]

ROOT = pathlib.Path(__file__).resolve().parent.parent
PIN = ROOT / "artifacts" / "semantic-controls" / "fixture-pack.json"
SUMMARY = ROOT / "artifacts" / "semantic-controls" / "semantic-controls-summary.md"
MATRIX = ROOT / "artifacts" / "safety-matrix" / "safety-matrix.tsv"
NURSERY = ROOT / "artifacts" / "autogenesis" / "nursery-v1.json"
FACTS = ROOT / "artifacts" / "facts"

PACK_VERSION = 1


# ---------------------------------------------------------------------------
# execution
# ---------------------------------------------------------------------------


def run_fixture(fx: Fixture) -> dict:
    t0 = time.time()
    out = fx.run()
    mutations = []
    for mut in fx.mutations:
        mo = mut.run()
        killed = bool(mo.counterexamples)
        if killed:
            status = "killed"
        elif mut.also_true:
            status = "also-true"
        else:
            status = "survived"
        mutations.append(
            {
                "id": mut.id,
                "kind": mut.kind,
                "status": status,
                "executed": mo.executed,
                "counterexamples": len(mo.counterexamples),
                "first": mo.counterexamples[0] if mo.counterexamples else "",
            }
        )
    return {
        "id": fx.id,
        "family": fx.family,
        "expect": fx.expect,
        "fact_ids": list(fx.fact_ids),
        "executed": out.executed,
        "discriminating": out.discriminating,
        "counterexamples": len(out.counterexamples),
        "first_counterexample": out.counterexamples[0] if out.counterexamples else "",
        "note": out.note,
        "mutations": mutations,
        "killed": sum(1 for m in mutations if m["status"] == "killed"),
        "also_true": sum(1 for m in mutations if m["status"] == "also-true"),
        "survived": sum(1 for m in mutations if m["status"] == "survived"),
        "seconds": round(time.time() - t0, 3),
    }


def run_numerics() -> list[dict]:
    """Execute the pre-existing in-tree numerics scripts.

    They are the pattern this pack extends, not replaces.  Each one asserts
    that its OWN negative controls genuinely fail; a script with no negative
    control is not a load-bearing control and is recorded as such.
    """
    rows = []
    for rel, _ in NUMERICS_SCRIPTS:
        path = ROOT / rel
        n_neg = 0
        if path.exists():
            n_neg = sum(
                1 for line in path.read_text().splitlines() if NEG_CONTROL.search(line)
            )
        t0 = time.time()
        proc = subprocess.run(
            [sys.executable, str(path)], capture_output=True, text=True, cwd=ROOT
        )
        rows.append(
            {
                "script": rel,
                "exit": proc.returncode,
                "negative_controls": n_neg,
                "stdout_lines": len(proc.stdout.splitlines()),
                "seconds": round(time.time() - t0, 3),
            }
        )
    return rows


# ---------------------------------------------------------------------------
# guards.  Each is separately deletable; `scripts/tests/
# test-semantic-control-fixtures.sh` kills each with exactly one case.
# ---------------------------------------------------------------------------


def guard_zero_executed(results: list[dict]) -> list[str]:
    """ZERO EXECUTED CASES IS ALWAYS FAILURE -- per fixture and in total."""
    bad = [f"{r['id']}: executed 0 cases" for r in results if r["executed"] == 0]
    if results and sum(r["executed"] for r in results) == 0:
        bad.append("the whole pack executed 0 cases")
    if not results:
        bad.append("the pack is empty: 0 fixtures executed")
    return bad


def guard_false_rejected(results: list[dict]) -> list[str]:
    """A known-FALSE statement must be refuted by its control."""
    return [
        f"{r['id']}: expect=false but the control found no counterexample"
        for r in results
        if r["expect"] == "false" and r["counterexamples"] == 0
    ]


def guard_valid_accepted(results: list[dict]) -> list[str]:
    """A known-VALID control must remain accepted."""
    return [
        f"{r['id']}: expect=valid but the control found "
        f"{r['counterexamples']} counterexample(s): {r['first_counterexample']}"
        for r in results
        if r["expect"] == "valid" and r["counterexamples"] > 0
    ]


def guard_valid_discriminates(results: list[dict]) -> list[str]:
    """A VALID control with zero discriminating instances is vacuous."""
    return [
        f"{r['id']}: expect=valid but 0 discriminating instances -- vacuous"
        for r in results
        if r["expect"] == "valid" and r["discriminating"] == 0
    ]


def guard_valid_load_bearing(results: list[dict]) -> list[str]:
    """A VALID control needs at least one KILLED mutation.  Without one, nothing
    demonstrates it would fail if the property failed."""
    return [
        f"{r['id']}: expect=valid but no mutation was killed -- not load-bearing"
        for r in results
        if r["expect"] == "valid" and r["killed"] == 0
    ]


def guard_vacuous_is_vacuous(results: list[dict]) -> list[str]:
    """A fixture pinned VACUOUS must really discriminate nothing, and must not
    be false either -- otherwise the pin is wrong about it."""
    bad = []
    for r in results:
        if r["expect"] != "vacuous":
            continue
        if r["discriminating"] != 0:
            bad.append(
                f"{r['id']}: expect=vacuous but {r['discriminating']} discriminating "
                "instances -- it is not vacuous"
            )
        if r["counterexamples"] != 0:
            bad.append(
                f"{r['id']}: expect=vacuous but the statement is FALSE at "
                f"{r['counterexamples']} instance(s)"
            )
    return bad


def guard_pin_drift(results: list[dict], pin: dict | None) -> list[str]:
    """The executed shape of every fixture is pinned; a silent model change is
    drift, not a new baseline."""
    if pin is None:
        return ["no pinned fixture pack: run with --write"]
    pinned = {p["id"]: p for p in pin.get("fixtures", [])}
    bad = []
    for r in results:
        p = pinned.get(r["id"])
        if p is None:
            continue
        for field in ("expect", "executed", "discriminating", "counterexamples", "killed"):
            if p.get(field) != r[field]:
                bad.append(
                    f"{r['id']}: pinned {field}={p.get(field)} but observed {r[field]}"
                )
    return bad


def guard_pin_coverage(results: list[dict], pin: dict | None) -> list[str]:
    """Deleting a fixture, or pinning one that no longer runs, must fail."""
    if pin is None:
        return []
    pinned = {p["id"] for p in pin.get("fixtures", [])}
    seen = {r["id"] for r in results}
    bad = []
    for missing in sorted(pinned - seen):
        bad.append(f"pinned fixture {missing} did not run -- deleted or renamed")
    for extra in sorted(seen - pinned):
        bad.append(f"fixture {extra} ran but is not pinned -- run with --write")
    return bad


def guard_numerics(numerics: list[dict]) -> list[str]:
    """The in-tree numerics scripts must pass AND must carry a negative
    control; a numerics script with none proves nothing about itself."""
    bad = []
    for n in numerics:
        if n["exit"] != 0:
            bad.append(f"{n['script']}: exit {n['exit']}")
        if n["negative_controls"] == 0:
            bad.append(f"{n['script']}: no NEGATIVE CONTROL -- not load-bearing")
    return bad


def guard_no_holdout(results: list[dict]) -> list[str]:
    """No fixture may name a held-out nursery row.  A control aimed at a blind
    evaluation population spends the family it was measuring."""
    if not NURSERY.exists():
        return []
    entries = json.loads(NURSERY.read_text()).get("entries", [])
    held = {e["fact_id"] for e in entries if e.get("partition") == "held-out"}
    bad = []
    for r in results:
        for fid in r["fact_ids"]:
            if fid in held:
                bad.append(f"{r['id']} names HELD-OUT fact {fid}")
    return bad


def guard_fact_ids_exist(results: list[dict]) -> list[str]:
    """A fixture claiming to control a fact must name a fact that exists and is
    `proved`; otherwise the census counts a control over nothing."""
    bad = []
    for r in results:
        for fid in r["fact_ids"]:
            path = FACTS / (fid.replace(":", "-") + ".json")
            if not path.exists():
                bad.append(f"{r['id']} names fact {fid}, which does not exist")
                continue
            status = json.loads(path.read_text()).get("epistemic_status")
            if status != "proved":
                bad.append(f"{r['id']} names fact {fid}, whose status is {status!r}")
    return bad


# ---------------------------------------------------------------------------
# the load-bearing census
# ---------------------------------------------------------------------------


def load_matrix_semantic() -> tuple[set[str], int]:
    """S0's `semantic_falsification` column, read from S0's generated artifact.

    This lane does NOT recompute it: `gen-safety-matrix.py` is S0's writer and
    owns that key.  Reading the column is also how the `kind` inflation is kept
    out -- S0 classifies from `supports`, so the 1,901 rows that declare
    `exhaustive-enumeration` / `instance-pin` while recording an axiom
    footprint are already excluded, and the count stays 91 rather than 1,992.
    """
    if not MATRIX.exists():
        return set(), 0
    lines = MATRIX.read_text().splitlines()
    header = lines[0].split("\t")
    i_id = header.index("fact_id")
    i_sem = header.index("semantic_falsification")
    sem = set()
    total = 0
    for line in lines[1:]:
        cells = line.split("\t")
        if len(cells) <= i_sem:
            continue
        total += 1
        if cells[i_sem] == "yes":
            sem.add(cells[i_id])
    return sem, total


def numerics_covered_facts() -> dict[str, list[str]]:
    """Which proved facts cite each numerics script in a `checker_command`.

    Derived from the ledger, never asserted: a fixture does not get to declare
    what it covers.
    """
    cover: dict[str, list[str]] = {rel: [] for rel, _ in NUMERICS_SCRIPTS}
    for path in sorted(FACTS.glob("*.json")):
        try:
            fact = json.loads(path.read_text())
        except json.JSONDecodeError:
            continue
        if fact.get("epistemic_status") != "proved":
            continue
        blob = json.dumps(fact.get("evidence", []))
        for rel in cover:
            if rel in blob:
                cover[rel].append(fact["id"])
    return cover


def census(results: list[dict], numerics: list[dict]) -> dict:
    sem_facts, proved_total = load_matrix_semantic()
    numeric_ok = {
        n["script"] for n in numerics if n["exit"] == 0 and n["negative_controls"] > 0
    }
    cover = numerics_covered_facts()

    load_bearing: dict[str, list[str]] = {}

    # source 1: a valid fixture with at least one KILLED mutation is a control
    # independently demonstrated to fail when the property fails.
    for r in results:
        if r["expect"] != "valid" or r["killed"] == 0:
            continue
        for fid in r["fact_ids"]:
            load_bearing.setdefault(fid, []).append(f"fixture:{r['id']}")

    # source 2: an in-tree numerics script that passes AND asserts its own
    # negative controls genuinely fail, for the facts that cite it.
    for rel, fids in cover.items():
        if rel not in numeric_ok:
            continue
        for fid in fids:
            load_bearing.setdefault(fid, []).append(f"numerics:{rel}")

    return {
        "proved_facts": proved_total,
        "semantic_falsification_facts": len(sem_facts),
        "load_bearing_facts": len(load_bearing),
        "load_bearing": {k: sorted(set(v)) for k, v in sorted(load_bearing.items())},
        "semantic_but_not_load_bearing": sorted(sem_facts - set(load_bearing)),
    }


# ---------------------------------------------------------------------------
# reporting
# ---------------------------------------------------------------------------


def build_pin(results: list[dict], numerics: list[dict], cen: dict) -> dict:
    return {
        "pack_version": PACK_VERSION,
        "generator": "scripts/check-semantic-control-fixtures.py",
        "note": "Generated. Do not hand-edit; run the generator with --write.",
        "fixtures": [
            {
                "id": r["id"],
                "family": r["family"],
                "expect": r["expect"],
                "fact_ids": r["fact_ids"],
                "executed": r["executed"],
                "discriminating": r["discriminating"],
                "counterexamples": r["counterexamples"],
                "killed": r["killed"],
                "also_true": r["also_true"],
                "survived": r["survived"],
                "mutations": [
                    {"id": m["id"], "kind": m["kind"], "status": m["status"]}
                    for m in r["mutations"]
                ],
            }
            for r in results
        ],
        "numerics": [
            {"script": n["script"], "exit": n["exit"], "negative_controls": n["negative_controls"]}
            for n in numerics
        ],
        "census": {
            "proved_facts": cen["proved_facts"],
            "semantic_falsification_facts": cen["semantic_falsification_facts"],
            "load_bearing_facts": cen["load_bearing_facts"],
        },
    }


def write_summary(results: list[dict], numerics: list[dict], cen: dict) -> None:
    w = []
    a = w.append
    a("# Semantic controls (S3)")
    a("")
    a("Generated by `scripts/check-semantic-control-fixtures.py`. Do not hand-edit.")
    a("")
    total_exec = sum(r["executed"] for r in results)
    total_exec += sum(m["executed"] for r in results for m in r["mutations"])
    a(
        f"{len(results)} fixtures, {total_exec} executed cases, "
        f"{sum(len(r['mutations']) for r in results)} mutations."
    )
    a("")
    a("## Fixture pack")
    a("")
    a("| fixture | class | executed | discriminating | counterexamples | mutations killed / also-true / survived |")
    a("|---|---|---:|---:|---:|---|")
    for r in results:
        a(
            f"| `{r['id']}` | {r['expect']} | {r['executed']} | {r['discriminating']} | "
            f"{r['counterexamples']} | {r['killed']} / {r['also_true']} / {r['survived']} |"
        )
    a("")
    a("`false` fixtures must be refuted; `vacuous` fixtures must discriminate")
    a("NOTHING (the fixture asserts the zero); `valid` fixtures must be accepted,")
    a("must discriminate, and must kill at least one mutation.")
    a("")
    a("## Mutations classified `also-true`")
    a("")
    a("These were not falsified because the mutated statement is itself true.")
    a("Per the roadmap this is a REVIEW result, not a theorem failure.")
    a("")
    rows = [
        (r["id"], m)
        for r in results
        for m in r["mutations"]
        if m["status"] == "also-true"
    ]
    if rows:
        a("| fixture | mutation | kind |")
        a("|---|---|---|")
        for fid, m in rows:
            a(f"| `{fid}` | `{m['id']}` | {m['kind']} |")
    else:
        a("(none)")
    a("")
    surv = [(r["id"], m) for r in results for m in r["mutations"] if m["status"] == "survived"]
    a("## Mutations that survived and are NOT declared also-true")
    a("")
    if surv:
        a("Each of these needs review: either the mutation is true (declare it)")
        a("or the control does not reach it.")
        a("")
        for fid, m in surv:
            a(f"- `{fid}` / `{m['id']}` ({m['kind']})")
    else:
        a("(none)")
    a("")
    a("## In-tree numerics scripts")
    a("")
    a("| script | exit | negative controls |")
    a("|---|---:|---:|")
    for n in numerics:
        a(f"| `{n['script']}` | {n['exit']} | {n['negative_controls']} |")
    a("")
    a("## Load-bearing control census")
    a("")
    a(
        f"**{cen['load_bearing_facts']} / {cen['proved_facts']}** proved facts have a "
        "control this gate independently demonstrated would fail if the property"
    )
    a("failed -- a killed mutation, or a numerics script whose own negative")
    a("controls were asserted to genuinely fail.")
    a("")
    a(
        f"S0's `semantic_falsification` column reports {cen['semantic_falsification_facts']} "
        f"/ {cen['proved_facts']}. That is the upper bound: it counts facts carrying"
    )
    a("a semantic evidence row, not facts whose control was shown to discriminate.")
    a("")
    a("The `kind` enum is NOT used anywhere in this census. 1,901 evidence rows")
    a("declare `exhaustive-enumeration` or `instance-pin` while their `supports`")
    a("records an axiom footprint; read at face value that turns 91 into 1,992.")
    a("This census reads S0's generated column, which classifies from `supports`.")
    a("")
    a("| facts with a load-bearing control | source |")
    a("|---|---|")
    for fid, srcs in cen["load_bearing"].items():
        a(f"| `{fid}` | {', '.join(f'`{s}`' for s in srcs)} |")
    a("")
    n_gap = len(cen["semantic_but_not_load_bearing"])
    a(
        f"{n_gap} facts carry a semantic-falsification evidence row with no "
        "demonstrated load-bearing control."
    )
    SUMMARY.parent.mkdir(parents=True, exist_ok=True)
    SUMMARY.write_text("\n".join(w) + "\n")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true", help="regenerate the pin and summary")
    ap.add_argument(
        "--check",
        action="store_true",
        help="explicit form of the default: execute the pack and gate, writing nothing",
    )
    ap.add_argument("--json", action="store_true", help="emit the full run as JSON")
    args = ap.parse_args()

    results = [run_fixture(fx) for fx in FIXTURES]
    numerics = run_numerics()
    cen = census(results, numerics)

    pin = json.loads(PIN.read_text()) if PIN.exists() else None

    failures: list[str] = []
    failures += guard_zero_executed(results)
    failures += guard_false_rejected(results)
    failures += guard_valid_accepted(results)
    failures += guard_valid_discriminates(results)
    failures += guard_valid_load_bearing(results)
    failures += guard_vacuous_is_vacuous(results)
    failures += guard_numerics(numerics)
    failures += guard_no_holdout(results)
    failures += guard_fact_ids_exist(results)
    if not args.write:
        failures += guard_pin_drift(results, pin)
        failures += guard_pin_coverage(results, pin)

    if args.json:
        print(json.dumps({"fixtures": results, "numerics": numerics, "census": cen,
                          "failures": failures}, indent=2))
    else:
        for r in results:
            verdict = {
                "false": "REJECTED " if r["counterexamples"] else "not-refuted",
                "vacuous": "VACUOUS  " if r["discriminating"] == 0 else "discriminates",
                "valid": "ACCEPTED " if not r["counterexamples"] else "REFUTED",
            }[r["expect"]]
            print(
                f"{verdict}  {r['id']:52s} class={r['expect']:8s} "
                f"executed={r['executed']:6d} disc={r['discriminating']:6d} "
                f"ce={r['counterexamples']:4d} "
                f"mut killed={r['killed']} also-true={r['also_true']} survived={r['survived']}"
            )
        for n in numerics:
            print(
                f"{'ok       ' if n['exit'] == 0 else 'FAIL     '}  {n['script']:52s} "
                f"exit={n['exit']} negative_controls={n['negative_controls']}"
            )
        total_exec = sum(r["executed"] for r in results) + sum(
            m["executed"] for r in results for m in r["mutations"]
        )
        print(
            f"fixtures={len(results)}|executed={total_exec}|"
            f"mutations={sum(len(r['mutations']) for r in results)}|"
            f"killed={sum(r['killed'] for r in results)}|"
            f"also_true={sum(r['also_true'] for r in results)}|"
            f"survived={sum(r['survived'] for r in results)}"
        )
        print(
            f"load_bearing={cen['load_bearing_facts']}|"
            f"semantic_falsification={cen['semantic_falsification_facts']}|"
            f"proved={cen['proved_facts']}"
        )

    if args.write:
        PIN.parent.mkdir(parents=True, exist_ok=True)
        PIN.write_text(json.dumps(build_pin(results, numerics, cen), indent=2) + "\n")
        write_summary(results, numerics, cen)
        print(f"wrote {PIN.relative_to(ROOT)} and {SUMMARY.relative_to(ROOT)}")

    if failures:
        print("")
        for f in failures:
            print(f"FAIL  {f}")
        print(f"{len(failures)} failure(s)")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
