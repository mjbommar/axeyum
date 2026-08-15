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
  * A settled fact must name its `proof_route`, and `axiom_footprint: []` is
    rejected on any route that cannot deliver axiom-freedom. Two incompatible
    footprint vocabularies were already coexisting -- 17 facts with `[]` from the
    kernel and 14 with `["axeyum-ir.bool-evaluator", ...]` from the SMT route,
    strings a lane invented because the schema offered none. Read side by side
    the first group looks like it rests on less. It does not; the two are
    different trust bases, and the routes are not even equally strong (the logic
    prelude is intuitionistic, so excluded middle is provable on the SMT route
    and unreachable in the kernel without a new axiom). Reporting one total
    across routes would restate exactly that error, so axiom-freedom is counted
    only where it is measurable.

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
LANGUAGES_ALL = {"smtlib2", "lean4", "lean4-surface", "axeyum-ir", "cas-term"}
# `cas-certificate` is the computer-algebra route: an identity in Q(vars) re-derived
# by exact polynomial arithmetic that shares no code with the search that found it.
# It is deliberately NOT `search-certificate`: a replayed witness settles one finite
# instance, while a polynomial identity settles every instance at once, and their
# footprints differ in kind rather than in size.
# `imported-kernel-lean` passes through the SAME trusted gate as `kernel-lean`
# (`Kernel::add_declaration` re-derives the type from the proof term), and is a
# separate route anyway, for two reasons. (1) Authorship: a `kernel-lean` fact is
# one this project constructed a proof of, which is the number the self-extension
# loop exists to raise; an import raises no such number, and one shared label
# would let the headline count be inflated by ingestion. (2) Trust base: an
# import additionally assumes the exporter rendered the source environment
# faithfully, that our wire translation preserves meaning, and that the delivered
# bytes are the producer's intended export -- format 3.1 has no footer, so
# completion is relative to the bytes handed over. So `[]` is unavailable here.
ROUTES = {"kernel-lean", "imported-kernel-lean", "smt-term-level", "smt-clausal",
          "search-certificate", "cas-certificate", "none"}
# Only this route can deliver axiom-freedom, because only there does an empty
# footprint correspond to a measurable fact about a kernel environment.
AXIOM_FREE_CAPABLE = {"kernel-lean"}
# Routes on which the proof term was NOT authored here. Reported separately from
# the constructed count for exactly the reason above.
IMPORTED_ROUTES = {"imported-kernel-lean"}

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
    if formal.get("language") not in LANGUAGES_ALL:
        fail(errors, f"{fid}: formal.language {formal.get('language')!r} not in "
                     f"{sorted(LANGUAGES_ALL)}")

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
        for c in ev.get("checkers", []):
            if not isinstance(c, str) or not c.strip():
                fail(errors, f"{fid}: evidence.checkers entries must be non-empty names")
        # A checker is only worth its exit status. `smtcomp_cli --evidence` exits
        # 0 on ANY decided verdict -- sat and unsat alike -- so a bare invocation
        # proves the binary ran, not that the recorded verdict still holds. The
        # replay gate ran 16 such commands and reported them as re-derived; a
        # solver flipping `unsat` to `sat` would have passed silently, which is
        # the exact regression the gate exists to catch.
        cmd = ev.get("checker_command") or ""
        if "smtcomp_cli" in cmd and not re.search(r"\btest\b|\bgrep\b|\[\[?", cmd):
            fail(errors, f"{fid}: checker_command invokes smtcomp_cli without asserting a "
                         f"verdict. It exits 0 on sat AND unsat, so as written it checks "
                         f"that the binary ran. Wrap it, e.g. "
                         f'test "$(... | tail -1)" = unsat')
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

    route = fact.get("proof_route")
    if route is not None and route not in ROUTES:
        fail(errors, f"{fid}: proof_route {route!r} is not one of {sorted(ROUTES)}")
    if status in ESTABLISHED and route is None:
        fail(errors, f"{fid}: status {status!r} requires a proof_route. axiom_footprint is "
                     f"only comparable WITHIN a route, so a settled fact that does not say "
                     f"which machine settled it makes its own footprint unreadable.")
    # The rule this whole field exists for.
    # Scoped to KNOWN routes: an unrecognised route is already reported above, and
    # we cannot say what a route we do not know cannot deliver. Without this guard
    # one bad value produced two errors, which makes a control ambiguous about
    # which rule it exercised.
    if (
        route in ROUTES
        and route not in AXIOM_FREE_CAPABLE
        and fact.get("axiom_footprint") == []
    ):
        fail(errors, f"{fid}: axiom_footprint [] on proof_route {route!r}. An empty footprint "
                     f"asserts axiom-freedom, which only {sorted(AXIOM_FREE_CAPABLE)} can "
                     f"deliver -- there it means a kernel environment admits no Axiom, Opaque "
                     f"or Quotient. On any other route it names semantic assumptions that are "
                     f"real and cannot be empty, so [] would read as the strongest claim the "
                     f"project makes on evidence that cannot support it.")

    # An imported proof term has an author, and it is not us. Requiring the
    # citation structurally is what stops an import from reading as a local
    # result: without it the only thing separating "we proved this" from "Lean
    # proved this and we re-checked the term" is a route string a reader has to
    # already understand.
    if route in IMPORTED_ROUTES and not fact["provenance"].get("prior_art"):
        fail(errors, f"{fid}: proof_route {route!r} means the proof term was authored "
                     f"elsewhere, so provenance.prior_art must name who authored it. "
                     f"An import that reads as a local proof is the failure this route "
                     f"exists to prevent.")

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

    # Route spread, and axiom-freedom reported ONLY where it means something.
    # A single "N axiom-free" number across routes is the exact conflation
    # proof_route exists to prevent, so it is scoped rather than totalled.
    routes: dict[str, int] = {}
    axiom_free = 0
    for f in facts.values():
        r = f.get("proof_route")
        if r:
            routes[r] = routes.get(r, 0) + 1
        if r in AXIOM_FREE_CAPABLE and f.get("axiom_footprint") == []:
            axiom_free += 1
    # Independent re-derivations. Cross-oracle agreement is the strongest signal
    # here, and it was invisible while every row said `checked` and nothing else.
    multi = sum(
        1
        for f in facts.values()
        for e in f.get("evidence", [])
        if len(e.get("checkers", [])) >= 2
    )

    spread = " ".join(f"{k}={v}" for k, v in sorted(by_status.items()))
    print(f"{len(facts)} facts checked, 0 errors  ({spread})")
    if routes:
        print("  routes: " + " ".join(f"{k}={v}" for k, v in sorted(routes.items()))
              + f"; {axiom_free} axiom-free on {sorted(AXIOM_FREE_CAPABLE)[0]}"
              + " (not comparable across routes)")
    # Constructed here vs. checked here but authored elsewhere. Reported apart
    # because the project's headline claim is about the first number, and an
    # ingestion pipeline can move the second one arbitrarily far.
    imported = sum(1 for f in facts.values() if f.get("proof_route") in IMPORTED_ROUTES)
    if imported:
        print(f"  {imported} fact(s) on an IMPORTED route -- proof term checked here, "
              f"authored elsewhere; not evidence of construction")
    print(f"  {multi} evidence row(s) re-derived by 2+ independent checkers")
    print(f"  external: {backlog} settled elsewhere but not here (import backlog), "
          f"{unclassified} unclassified")
    if novel:
        print(f"  NOVEL -- established here, not settled in the literature: {', '.join(novel)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
