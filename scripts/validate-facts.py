#!/usr/bin/env python3
"""Validate `artifacts/facts/*.json` against fact.schema.json and its semantics.

Structural validation is deliberately local (no `jsonschema` dependency), matching
`validate-claims.py` and `validate-smt-fragment-atlas.py`.

The semantic rules are the point. A schema can say a fact HAS a status and HAS an
evidence array; only these rules say the two must agree:

  * `proved` / `computed` / `refuted` require evidence that was actually checked.
    A status asserting something was established, with nothing establishing it, is
    the defect this whole repository is built to prevent.
  * `proved` requires an `axiom_footprint`. An EMPTY array means axiom-free and is
    a strictly stronger claim than an absent field, so the absence must not read as
    the strong case.
  * `open` requires an EMPTY evidence array. An open fact carrying evidence is a
    contradiction, and the empty array is a statement rather than an omission.
  * `depends_on` must resolve to facts that exist. A dependency DAG with dangling
    edges is not a build order.
  * `claim-ref` evidence must point at a claim file that exists, since that is how
    a computed value becomes evidence for a proposition.
  * `external_status` of `proved` or `refuted` requires a `provenance.prior_art`
    citation. Asserting that mathematics has settled something, without saying who
    settled it, is an unverifiable claim about the literature -- and this project
    has already published one round of Zenodo self-deposits as though they were
    refereed results.

It also REPORTS, without failing, any fact we have established that the wider
literature has not. That combination is not an error; it is the output this
project exists to produce, and a gate that stays silent about it is measuring
the wrong thing.

Like the claims checker, this prints what it examined and names what it could not
check rather than passing it silently.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FACTS = ROOT / "artifacts" / "facts"
SCHEMA = ROOT / "artifacts" / "ontology" / "fact.schema.json"

ID_RE = re.compile(r"^F:[a-z0-9]+(-[a-z0-9]+)*$")

REQUIRED = {"schema_version", "id", "title", "statement", "formal",
            "epistemic_status", "depends_on", "evidence", "provenance"}
STATUSES = {"axiom", "proved", "computed", "empirical", "conjectured", "open", "refuted"}
EXTERNAL_STATUSES = {"proved", "refuted", "conjectured", "open", "unknown"}
# What the wider literature has settled. Asserting one of these means asserting
# something about the world, so it has to name a source.
EXTERNAL_SETTLED = {"proved", "refuted"}
# What WE established. Paired with an unsettled external status, this is novelty.
OURS_SETTLED = {"proved", "computed", "refuted"}
LANGUAGES = {"smtlib2", "lean4", "axeyum-ir"}
EVIDENCE_KINDS = {"kernel-term", "witness-replay", "unsat-certificate", "cube-cover",
                  "cube-tree-cover", "exhaustive-enumeration", "published-value-replication",
                  "bound-citation", "instance-pin", "claim-ref"}
CHECK_STATUSES = {"checked", "replay-only", "not-checked"}

# A status that asserts the statement was settled must be backed by something.
ESTABLISHED = {"proved", "computed", "refuted"}


def fail(errors: list[str], msg: str) -> None:
    errors.append(msg)


def validate_one(path: Path, fact: dict, known_ids: set[str]) -> list[str]:
    errors: list[str] = []
    fid = fact.get("id", f"<{path.name}>")

    missing = REQUIRED - set(fact)
    if missing:
        fail(errors, f"{fid}: missing required field(s): {sorted(missing)}")
        return errors

    if not ID_RE.match(fact["id"]):
        fail(errors, f"{fid}: id must match ^F:[a-z0-9-]+$")

    expected_name = fact["id"].replace("F:", "F-") + ".json"
    if path.name != expected_name:
        fail(errors, f"{fid}: lives in {path.name} but its id implies {expected_name}")

    status = fact["epistemic_status"]
    if status not in STATUSES:
        fail(errors, f"{fid}: epistemic_status {status!r} is not one of {sorted(STATUSES)}")

    formal = fact["formal"]
    for key in ("language", "statement", "fragment"):
        if not formal.get(key):
            fail(errors, f"{fid}: formal.{key} is required and must be non-empty")
    if formal.get("language") not in LANGUAGES:
        fail(errors, f"{fid}: formal.language {formal.get('language')!r} not in {sorted(LANGUAGES)}")

    for dep in fact["depends_on"]:
        if not ID_RE.match(dep):
            fail(errors, f"{fid}: depends_on entry {dep!r} is not a fact id")
        elif dep not in known_ids:
            fail(errors, f"{fid}: depends_on {dep} does not exist -- a dependency DAG "
                         f"with dangling edges is not a build order")

    checked = 0
    for ev in fact["evidence"]:
        for key in ("id", "kind", "supports", "check_status"):
            if key not in ev:
                fail(errors, f"{fid}: evidence row missing {key!r}")
        if ev.get("kind") not in EVIDENCE_KINDS:
            fail(errors, f"{fid}: evidence kind {ev.get('kind')!r} not in {sorted(EVIDENCE_KINDS)}")
        if ev.get("check_status") not in CHECK_STATUSES:
            fail(errors, f"{fid}: evidence check_status {ev.get('check_status')!r} is unknown")
        if ev.get("check_status") == "checked":
            checked += 1
        if ev.get("kind") == "claim-ref":
            art = ev.get("artifact")
            if not art:
                fail(errors, f"{fid}: claim-ref evidence must name the claim in `artifact`")
            elif not (ROOT / art).is_file():
                fail(errors, f"{fid}: claim-ref points at {art}, which does not exist")

    # --- the semantic rules ---
    if status in ESTABLISHED and checked == 0:
        fail(errors, f"{fid}: status {status!r} asserts the statement was settled, but no "
                     f"evidence row is `checked`. A status with nothing establishing it is "
                     f"the defect this ledger exists to prevent.")

    if status == "proved" and "axiom_footprint" not in fact:
        fail(errors, f"{fid}: status `proved` requires axiom_footprint. An EMPTY array means "
                     f"axiom-free and is a stronger claim than an absent field, so absence "
                     f"must not read as the strong case.")

    if status == "open" and fact["evidence"]:
        fail(errors, f"{fid}: status `open` must carry an empty evidence array -- an open fact "
                     f"with evidence is a contradiction, and the empty array is a statement.")

    external = fact.get("external_status")
    if external is not None:
        if external not in EXTERNAL_STATUSES:
            fail(errors, f"{fid}: external_status {external!r} is not one of "
                         f"{sorted(EXTERNAL_STATUSES)}")
        elif (
            external in EXTERNAL_SETTLED
            and status not in OURS_SETTLED
            and not fact["provenance"].get("prior_art")
        ):
            fail(errors, f"{fid}: this fact is {status!r} to us but external_status "
                         f"{external!r}, so the LITERATURE is the only thing holding it up "
                         f"-- provenance.prior_art must name who settled it. (When we have "
                         f"established a fact ourselves, external_status is corroborative "
                         f"and needs no citation; the risk is relying on an unverified "
                         f"claim about the literature, which is how this project came to "
                         f"cite Zenodo self-deposits as refereed results.)")

    return errors


def main() -> int:
    if not SCHEMA.is_file():
        print(f"validate-facts: missing {SCHEMA}", file=sys.stderr)
        return 2
    if not FACTS.is_dir():
        print("validate-facts: no artifacts/facts/ directory; nothing to check")
        return 0

    paths = sorted(FACTS.glob("*.json"))
    facts: dict[Path, dict] = {}
    errors: list[str] = []

    for p in paths:
        try:
            facts[p] = json.loads(p.read_text())
        except json.JSONDecodeError as exc:
            fail(errors, f"{p.name}: not valid JSON: {exc}")

    ids: dict[str, Path] = {}
    for p, f in facts.items():
        fid = f.get("id")
        if fid in ids:
            fail(errors, f"{fid}: duplicate id, also in {ids[fid].name}")
        elif fid:
            ids[fid] = p

    for p, f in facts.items():
        errors.extend(validate_one(p, f, set(ids)))

    by_status: dict[str, int] = {}
    for f in facts.values():
        by_status[f.get("epistemic_status", "?")] = by_status.get(f.get("epistemic_status", "?"), 0) + 1

    if errors:
        print(f"\nvalidate-facts: {len(facts)} facts, {len(errors)} errors", file=sys.stderr)
        for e in errors:
            print(f"  ERROR {e}", file=sys.stderr)
        return 1

    # Established here, not settled in the literature -- i.e. new. Reported, never
    # failed: this is the output the project exists to produce, and a gate silent
    # about it is measuring the wrong thing.
    novel = sorted(
        f["id"]
        for f in facts.values()
        if f.get("epistemic_status") in OURS_SETTLED
        and f.get("external_status") in {"open", "conjectured"}
    )
    # Known to mathematics, not to us -- the import backlog. Distinct from `open`,
    # and the self-extension loop must not treat these as problems to solve.
    backlog = sum(
        1
        for f in facts.values()
        if f.get("epistemic_status") == "open" and f.get("external_status") == "proved"
    )
    unclassified = sum(1 for f in facts.values() if "external_status" not in f)

    spread = " ".join(f"{k}={v}" for k, v in sorted(by_status.items()))
    print(f"{len(facts)} facts checked, 0 errors  ({spread})")
    print(f"  external: {backlog} settled elsewhere but not here (import backlog), "
          f"{unclassified} unclassified")
    if novel:
        print(f"  NOVEL -- established here, not settled in the literature: {', '.join(novel)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
