#!/usr/bin/env python3
"""D4 gate: does the obstruction-producer compiler's output still mean what
it claims to mean?

This is the CHECKER half of the compiler pair
(`scripts/gen-obstruction-producers.py` is the generator). It exists because
a compiler that classifies obstructions and emits producer contracts can
fail exactly the way the operation registry failed before ADR-0602: every
contract naming one target, an empty applicability set, or a `proved` field
smuggled back in. Each of those must make THIS gate's exit status nonzero,
by name.

Guards, each with a distinct failure line so a mutation test can attribute a
kill to exactly one:

  G1  freshness   -- `gen-obstruction-producers.py --check` must pass. A
                      committed artifact that no longer matches its own
                      generator is unreviewable drift.
  G2  nonempty     -- at least one obstruction must be classified. A
                      compiler that classified nothing did not run.
  G3  live-producer -- at least one obstruction must be classified
                      `removability: producer` AND have a compiled
                      contract. Classifying without ever compiling is a
                      dead half of this phase.
  G4  no-proved    -- no producer contract JSON may contain a `proved` key
                      anywhere (recursive scan). ADR-0602's structural
                      guarantee: the false-assertion failure mode must be
                      UNREPRESENTABLE, not merely avoided by convention.
  G5  applicability-nonempty -- every contract's applicability.fact_ids
                      must be non-empty.
  G6  plurality    -- a contract with kind=="producer" must name >= 2
                      applicability targets, or it must be relabeled
                      kind=="capsule". This is D4's exit criterion made
                      mechanical: "a single-target producer is labeled a
                      capsule and cannot justify generality."
  G7  targets-exist -- every applicability fact_id must exist in the fact
                      ledger and must currently be `open` (a producer
                      whose targets are already settled is retrospective,
                      not prospective).
  G8  negative-controls -- every contract must name at least one negative
                      control, and every named control fact_id must exist
                      in the ledger.
  G9  obstruction-schema -- every obstruction's `removability` is one of
                      the three registered values, and every
                      `not-removable` obstruction cites at least one
                      evidence path that exists in this tree (a file) or
                      names the divergence registry (a live, re-checked
                      construction).
  G10 classification-covers-blocked -- every registered producer's
                      `obstruction_ids` must resolve to a real obstruction
                      record, and that obstruction's `blocked_fact_ids`
                      must be a SUPERSET of what actually ends up in the
                      contract's applicability (a producer may correctly
                      decline some of the obstruction's population as
                      negative controls, but it may not claim to cover a
                      fact its own obstruction record never named).

Exit status:
    0  every guard passed
    1  a guard fired (see FAIL lines)
    2  a required input could not be read (including: gen script missing,
       classification artifacts missing entirely)
"""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS_DIR = ROOT / "artifacts" / "facts"
OUT_DIR = ROOT / "artifacts" / "obstruction-producers"
OBSTRUCTIONS_PATH = OUT_DIR / "obstructions.json"
PRODUCERS_DIR = OUT_DIR / "producers"
GEN_SCRIPT = ROOT / "scripts" / "gen-obstruction-producers.py"

REMOVABILITY = {"producer", "new-construction", "not-removable"}


def die(message: str, code: int = 2) -> None:
    print(f"ERROR: {message}", file=sys.stderr)
    raise SystemExit(code)


def contains_key(doc: Any, key: str) -> bool:
    if isinstance(doc, dict):
        if key in doc:
            return True
        return any(contains_key(v, key) for v in doc.values())
    if isinstance(doc, list):
        return any(contains_key(v, key) for v in doc)
    return False


def load_facts() -> dict[str, dict[str, Any]]:
    if not FACTS_DIR.is_dir():
        die(f"no fact directory at {FACTS_DIR}")
    out: dict[str, dict[str, Any]] = {}
    for path in sorted(FACTS_DIR.glob("*.json")):
        fact = json.loads(path.read_text())
        ident = fact.get("id")
        if isinstance(ident, str):
            out[ident] = fact
    return out


def main() -> int:
    fails: list[str] = []

    # --- absence checks (exit 2: the gate cannot even evaluate) ----------
    if not GEN_SCRIPT.is_file():
        die(f"no generator at {GEN_SCRIPT} -- this gate has nothing to "
            f"re-verify freshness against")
    if not OBSTRUCTIONS_PATH.is_file():
        die(f"no {OBSTRUCTIONS_PATH} -- classification did not run "
            f"(python3 scripts/gen-obstruction-producers.py)")
    if not PRODUCERS_DIR.is_dir() or not list(PRODUCERS_DIR.glob("*.json")):
        die(f"no producer contracts under {PRODUCERS_DIR} -- the compiler "
            f"has never compiled anything")

    facts = load_facts()
    if not facts:
        die("fact ledger is empty; nothing to check contracts against")

    # G1 -- freshness.
    proc = subprocess.run(
        [sys.executable, str(GEN_SCRIPT), "--check"],
        cwd=ROOT, capture_output=True, text=True, timeout=120,
    )
    if proc.returncode != 0:
        fails.append(
            f"G1 stale-classification: `gen-obstruction-producers.py --check` "
            f"exited {proc.returncode}:\n{proc.stdout}{proc.stderr}")

    obstructions_doc = json.loads(OBSTRUCTIONS_PATH.read_text())
    obstructions = obstructions_doc.get("obstructions")
    if not isinstance(obstructions, list):
        die(f"{OBSTRUCTIONS_PATH}: no `obstructions` list")

    # G2 -- nonempty classification.
    if not obstructions:
        fails.append("G2 empty-classification: obstructions.json classifies "
                     "nothing; the compiler produced no findings")

    obstruction_by_id: dict[str, dict[str, Any]] = {}
    for o in obstructions:
        oid = o.get("id")
        if not isinstance(oid, str) or not oid:
            fails.append(f"G9 malformed-obstruction: an entry has no string id: {o}")
            continue
        obstruction_by_id[oid] = o

        # G9 -- schema + evidence for not-removable claims.
        removability = o.get("removability")
        if removability not in REMOVABILITY:
            fails.append(
                f"G9 bad-removability: {oid} has removability={removability!r}, "
                f"expected one of {sorted(REMOVABILITY)}")
        if removability == "not-removable":
            evidence = o.get("evidence")
            if not isinstance(evidence, list) or not evidence:
                fails.append(
                    f"G9 unbacked-not-removable: {oid} is classified "
                    f"not-removable but carries no evidence")
            else:
                backed = False
                for e in evidence:
                    if not isinstance(e, str):
                        continue
                    path_part = e.split("#", 1)[0].strip()
                    if path_part and (ROOT / path_part).exists():
                        backed = True
                if not backed:
                    fails.append(
                        f"G9 unbacked-not-removable: {oid}'s evidence names no "
                        f"file that exists in this tree: {evidence}")
        if not o.get("blocked_fact_ids"):
            fails.append(f"G9 no-population: {oid} names no blocked_fact_ids "
                         f"-- an obstruction with no population is not measured "
                         f"against anything")

    # --- producer contracts -------------------------------------------
    live_producer_found = False
    for path in sorted(PRODUCERS_DIR.glob("*.json")):
        doc = json.loads(path.read_text())
        pid = doc.get("id", path.stem)

        # G4 -- structural ADR-0602 compliance.
        if contains_key(doc, "proved"):
            fails.append(f"G4 proved-field-present: {path.name} contains a "
                         f"'proved' key -- ADR-0602 forbids this structurally")

        applicability = doc.get("applicability", {})
        fact_ids = applicability.get("fact_ids") if isinstance(applicability, dict) else None

        # G5 -- applicability nonempty.
        if not fact_ids:
            fails.append(f"G5 empty-applicability: {path.name} has an empty "
                         f"applicability.fact_ids")
            fact_ids = []

        # G6 -- plurality.
        kind = doc.get("kind")
        if kind == "producer" and len(fact_ids) < 2:
            fails.append(
                f"G6 single-target-producer: {path.name} claims kind=producer "
                f"with {len(fact_ids)} target(s); must be kind=capsule")
        elif kind == "producer" and len(fact_ids) >= 2:
            live_producer_found = True
        elif kind not in ("producer", "capsule"):
            fails.append(f"G6 bad-kind: {path.name} has kind={kind!r}, "
                         f"expected 'producer' or 'capsule'")

        # G7 -- targets exist and are open.
        for fid in fact_ids:
            if fid not in facts:
                fails.append(f"G7 unknown-target: {path.name} names {fid}, "
                             f"which is not in the fact ledger")
            elif facts[fid].get("epistemic_status") != "open":
                fails.append(
                    f"G7 non-open-target: {path.name} names {fid} with "
                    f"epistemic_status={facts[fid].get('epistemic_status')!r} "
                    f"-- a producer's targets must be genuinely open work")

        # G8 -- negative controls present and real.
        controls = doc.get("negative_controls")
        if not controls:
            fails.append(f"G8 no-negative-controls: {path.name} names zero "
                         f"negative controls")
        else:
            for c in controls:
                cid = c.get("fact_id") if isinstance(c, dict) else None
                if cid and cid not in facts:
                    fails.append(
                        f"G8 unknown-control: {path.name}'s negative control "
                        f"{cid} is not in the fact ledger")

        # G10 -- obstruction linkage and coverage bound.
        obstruction_ids = doc.get("obstruction_ids")
        if not obstruction_ids:
            fails.append(f"G10 no-obstruction-link: {path.name} names no "
                         f"obstruction_ids")
        else:
            for oid in obstruction_ids:
                obs = obstruction_by_id.get(oid)
                if obs is None:
                    fails.append(
                        f"G10 dangling-obstruction-link: {path.name} names "
                        f"obstruction {oid!r}, which is not in obstructions.json")
                    continue
                population = set(obs.get("blocked_fact_ids") or [])
                overreach = set(fact_ids) - population
                if overreach:
                    fails.append(
                        f"G10 coverage-overreach: {path.name} claims applicability "
                        f"{sorted(overreach)}, outside its own obstruction "
                        f"{oid}'s blocked_fact_ids population {sorted(population)}")

    # G3 -- at least one live producer.
    if not live_producer_found:
        fails.append("G3 no-live-producer: no compiled contract has "
                     "kind=producer with >= 2 applicability targets -- "
                     "classification ran but nothing was actually compiled")

    # Report the applicability-set-size distribution honestly, always --
    # this is not a guard, it is the headline number D4 asks this phase to
    # report without spin.
    sizes = []
    for path in sorted(PRODUCERS_DIR.glob("*.json")):
        doc = json.loads(path.read_text())
        if doc.get("kind") == "producer":
            sizes.append(len(doc.get("applicability", {}).get("fact_ids") or []))
    if sizes:
        mean = sum(sizes) / len(sizes)
        print(f"applicability-set sizes (kind=producer): {sizes}, mean={mean:.2f}")
        if mean == 1.0:
            print("FAILED PHASE: mean applicability-set size is 1.0 -- this "
                  "phase rebuilt the dispatch-table failure mode ADR-0602 "
                  "exists to prevent, reported honestly rather than hidden.")
            fails.append("mean-applicability-is-one: see FAILED PHASE line above")
    else:
        print("applicability-set sizes (kind=producer): none compiled")

    if fails:
        print("FAIL:")
        for f in fails:
            print(f"  - {f}")
        return 1
    print(f"OK -- {len(obstructions)} obstruction(s) classified, "
          f"{len(list(PRODUCERS_DIR.glob('*.json')))} producer contract(s) "
          f"compiled, all guards passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
