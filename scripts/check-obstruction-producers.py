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
  G3  live-producer -- the compiler must have produced SOMETHING: a
                      contract with kind=producer and >= 2 live targets,
                      or -- once every population it was sized against has
                      closed -- a kind=fulfilled retirement record.
                      Classifying without ever compiling is a dead half of
                      this phase; retiring an exhausted contract is not
                      (ADR-1510: a claim over an empty population must
                      RETIRE, not error). A tree in which every contract is
                      retired passes, loudly: the EXHAUSTED line below says
                      so, because a gate that failed on it would report
                      success as a defect, which is the exact bug this
                      guard's own generator shipped on 2026-09-02.
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
  G11 spent-bookkeeping -- a contract's `spent` list (the targets that
                      closed underneath it) must name real facts, none of
                      them still `open`, each with the `settled_commit`
                      that closed it, and must be DISJOINT from
                      `applicability.fact_ids`. Without the disjointness
                      half a settled target could be recorded as closed and
                      still claimed as prospective work; without the
                      still-open half, `spent` would be a way to park live
                      work where G7 cannot see it.

Exit status:
    0  every guard passed
    1  a guard fired (see FAIL lines)
    2  a required input could not be read (including: gen script missing,
       classification artifacts missing entirely)
"""

from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]

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


def load_facts(facts_dir: pathlib.Path) -> dict[str, dict[str, Any]]:
    if not facts_dir.is_dir():
        die(f"no fact directory at {facts_dir}")
    out: dict[str, dict[str, Any]] = {}
    for path in sorted(facts_dir.glob("*.json")):
        fact = json.loads(path.read_text())
        ident = fact.get("id")
        if isinstance(ident, str):
            out[ident] = fact
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                      formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=pathlib.Path, default=ROOT,
                        help="repository root to check (testing only; production "
                             "runs use the real tree)")
    parser.add_argument("--skip-freshness", action="store_true",
                        help="skip G1 (testing only: exercises G2-G10 against a "
                             "synthetic fixture that has no real gen script to "
                             "re-derive from)")
    args = parser.parse_args()

    root = args.root
    facts_dir = root / "artifacts" / "facts"
    out_dir = root / "artifacts" / "obstruction-producers"
    obstructions_path = out_dir / "obstructions.json"
    producers_dir = out_dir / "producers"
    gen_script = root / "scripts" / "gen-obstruction-producers.py"

    fails: list[str] = []

    # --- absence checks (exit 2: the gate cannot even evaluate) ----------
    if not args.skip_freshness and not gen_script.is_file():
        die(f"no generator at {gen_script} -- this gate has nothing to "
            f"re-verify freshness against")
    if not obstructions_path.is_file():
        die(f"no {obstructions_path} -- classification did not run "
            f"(python3 scripts/gen-obstruction-producers.py)")
    if not producers_dir.is_dir() or not list(producers_dir.glob("*.json")):
        die(f"no producer contracts under {producers_dir} -- the compiler "
            f"has never compiled anything")

    facts = load_facts(facts_dir)
    if not facts:
        die("fact ledger is empty; nothing to check contracts against")

    # G1 -- freshness.
    if args.skip_freshness:
        print("G1 SKIPPED (--skip-freshness; testing only)")
    else:
        proc = subprocess.run(
            [sys.executable, str(gen_script), "--check"],
            cwd=root, capture_output=True, text=True, timeout=120,
        )
        if proc.returncode != 0:
            fails.append(
                f"G1 stale-classification: `gen-obstruction-producers.py --check` "
                f"exited {proc.returncode}:\n{proc.stdout}{proc.stderr}")

    obstructions_doc = json.loads(obstructions_path.read_text())
    obstructions = obstructions_doc.get("obstructions")
    if not isinstance(obstructions, list):
        die(f"{obstructions_path}: no `obstructions` list")

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
                    if path_part and (root / path_part).exists():
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
    fulfilled_found = False
    for path in sorted(producers_dir.glob("*.json")):
        doc = json.loads(path.read_text())
        pid = doc.get("id", path.stem)

        # G4 -- structural ADR-0602 compliance.
        if contains_key(doc, "proved"):
            fails.append(f"G4 proved-field-present: {path.name} contains a "
                         f"'proved' key -- ADR-0602 forbids this structurally")

        kind = doc.get("kind")
        applicability = doc.get("applicability", {})
        fact_ids = applicability.get("fact_ids") if isinstance(applicability, dict) else None

        # G11 -- partial-settle bookkeeping, for EVERY kind.
        #
        # A population can close underneath a contract while it is still live
        # (some targets settle, some do not). The settled ones leave
        # `applicability` and land in `spent`; this guard is what makes that
        # readable rather than a silent drop, and what stops `spent` becoming a
        # place to hide live work from G7.
        spent_ids: set[str] = set()
        for entry in doc.get("spent") or []:
            sid = entry.get("fact_id") if isinstance(entry, dict) else None
            if not sid:
                fails.append(f"G11 malformed-spent: {path.name} has a spent "
                             f"entry with no fact_id")
                continue
            spent_ids.add(sid)
            if sid not in facts:
                fails.append(f"G11 unknown-spent-target: {path.name} records "
                             f"{sid} as spent, but it is not in the fact ledger")
                continue
            if facts[sid].get("epistemic_status") == "open":
                fails.append(
                    f"G11 spent-target-still-open: {path.name} records {sid} as "
                    f"spent, but it is still open -- a contract may not retire "
                    f"live work")
            if not entry.get("settled_commit"):
                fails.append(
                    f"G11 spent-without-provenance: {path.name} records {sid} as "
                    f"spent but names no settled_commit -- a retirement that "
                    f"cannot say WHAT closed the target is unauditable")
        both = spent_ids & set(fact_ids or [])
        if both:
            fails.append(
                f"G11 spent-and-live: {path.name} lists {sorted(both)} as both "
                f"live applicability and spent")

        # A FULFILLED record is a retired producer whose whole population
        # closed. It has no open targets by definition, so G5's non-empty rule,
        # G6's plurality and G7's open-target rule do not apply -- but it must
        # name what closed and what it achieved, which G6F enforces instead.
        if kind == "fulfilled":
            if not doc.get("spent"):
                fails.append(f"G6F fulfilled-without-spent: {path.name} is "
                             f"kind=fulfilled but names no spent hypotheses")
            if not doc.get("outcome"):
                fails.append(f"G6F fulfilled-without-outcome: {path.name} is "
                             f"kind=fulfilled but records no outcome")
            fulfilled_found = True
            continue

        # G5 -- applicability nonempty.
        if not fact_ids:
            fails.append(f"G5 empty-applicability: {path.name} has an empty "
                         f"applicability.fact_ids")
            fact_ids = []


        # G6 -- plurality.
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

    # G3 -- the compiler produced something: a live producer, or a retirement.
    if not live_producer_found and not fulfilled_found:
        fails.append("G3 no-live-producer: no compiled contract has "
                     "kind=producer with >= 2 applicability targets, and none "
                     "is a kind=fulfilled retirement -- classification ran but "
                     "nothing was actually compiled")
    elif not live_producer_found:
        print("EXHAUSTED: every compiled contract is kind=fulfilled -- each "
              "population this compiler was sized against has closed, so there "
              "is no live producer to dispatch. That is a true state, not a "
              "defect (ADR-1510), and it is the OPEN POLICY QUESTION this gate "
              "cannot answer: the next contract must be sized against the "
              "current frontier before it is written, not against what a "
              "producer already did.")

    # Report the applicability-set-size distribution honestly, always --
    # this is not a guard, it is the headline number D4 asks this phase to
    # report without spin.
    sizes = []
    for path in sorted(producers_dir.glob("*.json")):
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
          f"{len(list(producers_dir.glob('*.json')))} producer contract(s) "
          f"compiled, all guards passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
